import Freigen.Reflect.Resolve
import Freigen.Reflect.Source
import Lean.Meta.RecursorInfo
import Lean.Meta.Match.MatcherApp.Basic

namespace Freigen
namespace Ast
namespace Reflector

open Lean Meta Elab Term
/-! ## Supported recursion recognition -/

structure NatBRecShape where
  functional : Lean.Expr
  deriving Inhabited

private def analyzeNatBRec (name : Name) : MetaM (Option NatBRecShape) := do
  let some (.defnInfo info) := (← getEnv).find? name | return none
  lambdaTelescope info.value fun xs body => do
    unless xs.size == 1 do return none
    let body := body.consumeMData
    let some recursorName := body.getAppFn.constName? | return none
    let env ← getEnv
    unless isBRecOnRecursor env recursorName do return none
    let recursor ← try mkRecursorInfo recursorName catch _ => return none
    unless recursor.typeName == ``Nat && recursor.recursive && recursor.numMinors == 1 do
      return none
    let args := body.getAppArgs
    unless recursor.majorPos < args.size do return none
    unless ← isDefEq args[recursor.majorPos]! xs[0]! do return none
    let some minorPos := (Array.range args.size).find? recursor.isMinor | return none
    return some { functional := args[minorPos]! }

/-! ## Plan schema -/

structure ValueParam where
  type : Lean.Expr
  repr : Lean.Expr
  deriving Inhabited

inductive HelperBoundary where
  | unary (before : Array Lean.Expr) (arg : ValueParam) (after : Array Lean.Expr)
  | pair (before : Array Lean.Expr) (left : ValueParam) (between : Array Lean.Expr)
      (right : ValueParam) (after : Array Lean.Expr)
  | natBRec (arg : ValueParam) (shape : NatBRecShape)
  deriving Inhabited

def HelperBoundary.valueParams : HelperBoundary → Array ValueParam
  | .unary _ arg _ | .natBRec arg _ => #[arg]
  | .pair _ left _ right _ => #[left, right]

def HelperBoundary.staticArgs : HelperBoundary → Array Lean.Expr
  | .unary before _ after => before ++ after
  | .pair before _ between _ after => before ++ between ++ after
  | .natBRec .. => #[]

def HelperBoundary.valueEntries : HelperBoundary → Array (Nat × ValueParam)
  | .unary before arg _ => #[(before.size, arg)]
  | .pair before left between right _ =>
      #[(before.size, left), (before.size + between.size + 1, right)]
  | .natBRec arg _ => #[(0, arg)]

def HelperBoundary.staticEntries : HelperBoundary → Array (Nat × Lean.Expr)
  | .unary before _ after =>
      before.mapIdx (fun i value => (i, value)) ++
      after.mapIdx (fun i value => (before.size + i + 1, value))
  | .pair before _ between _ after =>
      before.mapIdx (fun i value => (i, value)) ++
      between.mapIdx (fun i value => (before.size + i + 1, value)) ++
      after.mapIdx (fun i value => (before.size + between.size + i + 2, value))
  | .natBRec .. => #[]

def HelperBoundary.isRecursive : HelperBoundary → Bool
  | .natBRec .. => true
  | _ => false

structure Specialization where
  name : Name
  resultType : Lean.Expr
  resultRepr : Lean.Expr
  sourceRange? : Option Lean.Expr := none
  boundary : HelperBoundary
  deriving Inhabited

def Specialization.staticArgs (spec : Specialization) : Array Lean.Expr :=
  spec.boundary.staticArgs

structure SpecializationKey where
  name : Name
  staticArgs : Array Lean.Expr
  deriving Inhabited

def Specialization.key (spec : Specialization) : SpecializationKey :=
  { name := spec.name, staticArgs := spec.staticArgs }

def Specialization.valueParams (spec : Specialization) : Array ValueParam :=
  spec.boundary.valueParams

/-- Reconstruct a source call from the complete boundary layout. The layout constructors encode
    every static segment, so a discovered plan cannot contain a missing argument slot. -/
def Specialization.reconstructArgs (spec : Specialization) (values : Array Lean.Expr) :
    MetaM (Array Lean.Expr) := do
  match spec.boundary, values with
  | .unary before _ after, #[value] => pure (before ++ #[value] ++ after)
  | .pair before _ between _ after, #[left, right] =>
      pure (before ++ #[left] ++ between ++ #[right] ++ after)
  | .natBRec .., #[value] => pure #[value]
  | _, _ => throwError "reflect%: internal: helper `{spec.name}` received the wrong boundary arity"

def Specialization.callStaticArgs (spec : Specialization) (args : Array Lean.Expr) :
    Array Lean.Expr :=
  spec.boundary.staticEntries.map fun entry => args[entry.1]!

structure Plan where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  compat : Lean.Expr
  resultType : Lean.Expr
  resultRepr : Lean.Expr
  specializations : Array Specialization

private def freekType? (ty : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let ty ← whnf ty
  if ty.isAppOfArity ``Free 2 then
    return some (ty.getArg! 0, ty.getArg! 1)
  return none

def isReflectorCore (n : Name) : Bool :=
  n == ``Free.pure || n == ``Free.op || n == ``Free.bind ||
  n == ``Pure.pure || n == ``Bind.bind

def sameArgs (xs ys : Array Lean.Expr) : MetaM Bool := do
  if xs.size != ys.size then return false
  let saved ← get
  for i in [0:xs.size] do
    unless ← isDefEq xs[i]! ys[i]! do
      set saved
      return false
  set saved
  return true

def sameKey (left right : SpecializationKey) : MetaM Bool := do
  unless left.name == right.name do return false
  sameArgs left.staticArgs right.staticArgs

def Specialization.matchesCall (spec : Specialization) (call : Lean.Expr) : MetaM Bool := do
  unless call.getAppFn.constName? == some spec.name do return false
  sameArgs spec.staticArgs (spec.callStaticArgs call.getAppArgs)

/-! ## Plan construction -/

private inductive ClassifiedParam where
  | value (param : ValueParam)
  | fixed (value : Lean.Expr)
  | unsupported
  deriving Inhabited

private structure DiscoveryState where
  completed : Array Specialization := #[]
  active : Array SpecializationKey := #[]
  recursive : Array SpecializationKey := #[]

private def ClassifiedParam.staticArgs (params : Array ClassifiedParam) : Array Lean.Expr :=
  params.foldl (init := #[]) fun args param => match param with
    | ClassifiedParam.fixed fixedValue => args.push fixedValue
    | _ => args

private def staticSegment (params : Array ClassifiedParam) (start stop : Nat) :
    MetaM (Array Lean.Expr) := do
  let mut result := #[]
  for offset in [0:stop - start] do
    match params[start + offset]! with
    | .fixed fixedValue => result := result.push fixedValue
    | _ => throwError "reflect%: internal: non-static argument in a static helper segment"
  pure result

private def ordinaryBoundary (name : Name) (params : Array ClassifiedParam)
    (values : Array (Nat × ValueParam)) : MetaM HelperBoundary := do
  unless params.all fun param => match param with | .unsupported => false | _ => true do
    throwError "reflect%: helper `{name}` has an unsupported dynamic argument"
  match values with
  | #[(position, arg)] => do
      pure (.unary (← staticSegment params 0 position) arg
        (← staticSegment params (position + 1) params.size))
  | #[(leftPosition, left), (rightPosition, right)] => do
      pure (.pair (← staticSegment params 0 leftPosition) left
        (← staticSegment params (leftPosition + 1) rightPosition) right
        (← staticSegment params (rightPosition + 1) params.size))
  | _ => throwError
      "reflect%: nonrecursive helper `{name}` must have one argument or one pair, plus static specialization arguments"

/-- Pass 1: discover all monomorphized `Free` helpers in dependency order.  No AST or proof terms
    are emitted in this pass. -/
partial def discover (root : Lean.Expr) : TermElabM Plan := do
  let some (S, α) ← freekType? (← inferType root)
    | throwError "reflect%: expected a `Free` program{indentExpr root}"
  let ⟨H, C⟩ ← resolveCompat S
  let reprCache ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
  let rec getRepr (type : Lean.Expr) : MetaM Lean.Expr := do
    for entry in ← reprCache.get do
      if ← isDefEq entry.1 type then return entry.2
    let repr ← resolveRepr type
    reprCache.modify (·.push (type, repr))
    return repr
  let rec hasRepr (type : Lean.Expr) : MetaM Bool := do
    let saved ← get
    try
      discard <| getRepr type
      return true
    catch _ =>
      set saved
      return false
  let rootRepr ← getRepr α
  let state ← IO.mkRef ({} : DiscoveryState)
  let rec keyMember (key : SpecializationKey) (keys : Array SpecializationKey) : MetaM Bool := do
    for candidate in keys do
      if ← sameKey key candidate then return true
    return false
  let rec completed (key : SpecializationKey) : MetaM Bool := do
    for spec in (← state.get).completed do
      if ← sameKey key spec.key then return true
    return false
  let rec visit (e : Lean.Expr) : MetaM Unit := do
    let e ← instantiateMVars e
    let fn := e.getAppFn
    if let some n := fn.constName? then
      -- Matchers organize source syntax; they are not user helpers.  Only their alternatives can
      -- contain computations, so inspecting motives, discriminants, and generated plumbing is
      -- both unnecessary and catastrophically expensive for `brecOn` functionals.
      if let some matcher ← matchMatcherApp? e (alsoCasesOn := true) then
        for alt in matcher.alts do visit alt
        return
      -- Other auxiliary recursors are likewise compiler structure.  Recognized recursive helpers
      -- are entered through their functional below, so there is no useful call hidden here.
      if isAuxRecursor (← getEnv) n then
        return
      if !isReflectorCore n then
        let resultType ← inferType e
        if let some (_, result) ← freekType? resultType then
          -- Argument classification is meaningful only for spillable helpers.  Doing it before
          -- this check makes discovery inspect every application inside values and proof terms.
          let mut params : Array ClassifiedParam := #[]
          let mut valueEntries : Array (Nat × ValueParam) := #[]
          let callArgs := e.getAppArgs
          let callArgTypes ← callArgs.mapM inferType
          for i in [0:callArgs.size] do
            let arg := callArgs[i]!
            let argType := callArgTypes[i]!
            let dependentLiteral ← match (← getNatValue? arg) with
              | none => pure false
              | some _ =>
                  let occursInLater := (List.range (callArgs.size - i - 1)).any fun offset =>
                    (callArgTypes[i + offset + 1]!.find? (· == arg)).isSome
                  pure (occursInLater || (resultType.find? (· == arg)).isSome)
            if dependentLiteral then
              params := params.push (.fixed arg)
            else if ← hasRepr argType then
              let valueParam : ValueParam := {
                type := argType
                repr := ← getRepr argType
              }
              params := params.push (.value valueParam)
              valueEntries := valueEntries.push (i, valueParam)
            else if !arg.hasFVar then
              params := params.push (.fixed arg)
            else
              params := params.push .unsupported
          let key : SpecializationKey := {
            name := n, staticArgs := ClassifiedParam.staticArgs params
          }
          if astInlineAttr.hasTag (← getEnv) n then
            if let some body ← unfoldDefinition? e then visit body
            return
          if ← keyMember key (← state.get).active then
            state.modify fun current => { current with recursive := current.recursive.push key }
            return
          if ← completed key then return
          state.modify fun current => { current with active := current.active.push key }
          -- A generated recursive definition already exposes precisely the syntax we care about
          -- through its `brecOn` functional.  Walking the unfolded recursor instead duplicates and
          -- normalizes compiler-generated recursion plumbing.
          let analyzedShape ← analyzeNatBRec n
          match analyzedShape with
          | some shape =>
              -- The generated functional is normally a reducible auxiliary constant (`foo._f`).
              -- Open that one definition so dependency calls in its zero/successor branches are
              -- visible, while leaving the surrounding recursor itself closed.
              if let some functionalBody ← unfoldDefinition? shape.functional then
                visit functionalBody
              else
                visit shape.functional
          | none => if let some body ← unfoldDefinition? e then visit body
          state.modify fun current => { current with active := current.active.pop }
          let discoveredRec ← keyMember key (← state.get).recursive
          let isRec := discoveredRec || analyzedShape.isSome
          let repr ← getRepr result
          let boundary ← if isRec then
            match analyzedShape with
            | some shape => do
                unless params.size == 1 do
                  throwError "reflect%: recursive helper `{n}` currently requires one Nat argument"
                let .value arg := params[0]!
                  | throwError "reflect%: recursive helper `{n}` currently requires one Nat argument"
                let argCode ← mkAppM ``ReprSpec.code #[arg.repr]
                unless ← isDefEq argCode (mkConst ``Tp.nat) do
                  throwError "reflect%: recursive helper `{n}` must use the Nat representation"
                pure (.natBRec arg shape)
            | none => throwError
                "reflect%: recursive helper `{n}` is not compiled through `Nat.brecOn`"
          else ordinaryBoundary n params valueEntries
          let sourceRange? ← declarationSourceRange? n
          state.modify fun current => { current with completed := current.completed.push {
            name := n
            resultType := result
            resultRepr := repr
            sourceRange? := sourceRange?
            boundary := boundary
          } }
          return
    match e with
    | .app f a => visit f; visit a
    | .lam n d b bi =>
        visit d
        withLocalDecl n bi d fun x => visit (b.instantiate1 x)
    | .forallE _ d _ _ => visit d
    | .letE _ t value body _ =>
        visit t
        visit value
        visit (body.instantiate1 value)
    | .mdata _ b | .proj _ _ b => visit b
    | _ => pure ()
  let visitRoot (root : Lean.Expr) : MetaM Unit := do
    let root ← instantiateMVars root
    if let some name := root.getAppFn.constName? then
      if !isReflectorCore name then
        if let some _ ← freekType? (← inferType root) then
          if (← analyzeNatBRec name).isSome then
            return ← visit root
          if let some body ← unfoldDefinition? root then
            return ← visit body
          return
    visit root
  visitRoot root
  let specializations := (← state.get).completed
  pure {
    sourceSig := S
    targetSig := H
    compat := C
    resultType := α
    resultRepr := rootRepr
    specializations := specializations
  }

end Reflector
end Ast
end Freigen
