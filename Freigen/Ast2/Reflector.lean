import Freigen.Ast2.Registry
import Lean.Elab.Command
import Lean.Elab.SyntheticMVars
import Lean.DeclarationRange

namespace Freigen
namespace Ast2
namespace Reflector

open Lean Meta Elab Term

private def quoteSourceRange (module : Name) (startPos endPos : Position) : Lean.Expr :=
  mkAppN (mkConst ``SourceRange.mk) #[toExpr module,
    mkNatLit startPos.line, mkNatLit startPos.column,
    mkNatLit endPos.line, mkNatLit endPos.column]

private def declarationSourceRange? (decl : Name) : MetaM (Option Lean.Expr) := do
  let some ranges ← findDeclarationRanges? decl | return none
  let env ← getEnv
  let module := match env.getModuleIdxFor? decl with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  return some (quoteSourceRange module ranges.range.pos ranges.range.endPos)

private def syntaxSourceRange? (stx : Syntax) : TermElabM (Option Lean.Expr) := do
  let some range := stx.getRange? | return none
  let fileMap ← getFileMap
  return some (quoteSourceRange (← getMainModule)
    (fileMap.toPosition range.start) (fileMap.toPosition range.stop))

private def registryEntries (attr : TagAttribute) : CoreM (Array Name) := do
  let env ← getEnv
  return env.constants.toList.foldl (init := #[]) fun entries entry =>
    if attr.hasTag env entry.1 then entries.push entry.1 else entries

private partial def instantiateRegistered (decl : Name)
    (expected : Lean.Expr) : MetaM Lean.Expr := do
  let c ← mkConstWithFreshMVarLevels decl
  let ⟨xs, _, body⟩ ← forallMetaTelescope (← inferType c)
  unless ← isDefEq body expected do
    throwError "result type does not match"
  for x in xs do
    let m := x.mvarId!
    unless (← m.isAssigned) do
      let ty ← instantiateMVars (← m.getType)
      if ty.isAppOfArity ``ReprSpec 1 then
        let α := ty.getArg! 0
        m.assign (← resolve ast2ReprAttr ty α)
      else
        throwError "unresolved registry parameter{indentExpr ty}"
  pure (← instantiateMVars (mkAppN c xs))
where
  resolve (attr : TagAttribute) (expected : Lean.Expr) (_index : Lean.Expr) : MetaM Lean.Expr := do
    let saved ← get
    for candidate in ← registryEntries attr do
      try
        return ← instantiateRegistered candidate expected
      catch _ =>
        set saved
    throwError "reflect%: no registered declaration produces{indentExpr expected}"

/-- Resolve an explicit representation declaration for a host type. -/
def resolveRepr (α : Lean.Expr) : MetaM Lean.Expr := do
  let expected ← mkAppM ``ReprSpec #[α]
  let saved ← get
  let candidates ← registryEntries ast2ReprAttr
  for candidate in candidates do
    try
      return ← instantiateRegistered candidate expected
    catch _ =>
      set saved
  throwError "reflect%: type has no registered AST2 representation{indentExpr α}\nregistered: {candidates}"

/-- Resolve the source/target signature compatibility selected for `S`. -/
def resolveCompat (S : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let H ← mkFreshExprMVar (mkConst ``Signature)
  let expected ← mkAppM ``Signature.Compat #[S, H]
  let saved ← get
  for candidate in ← registryEntries ast2CompatAttr do
    try
      let compat ← instantiateRegistered candidate expected
      return (← instantiateMVars H, compat)
    catch _ =>
      set saved
  throwError "reflect%: source signature has no registered AST2 compatibility{indentExpr S}"

/-- Resolve the exact target operation and compatibility witness for one source operation. -/
def resolveOp (C e : Lean.Expr) : MetaM Lean.Expr := do
  let expected ← mkAppM ``OpSpec #[C, e]
  let saved ← get
  for candidate in ← registryEntries ast2OpAttr do
    try
      return ← instantiateRegistered candidate expected
    catch _ =>
      set saved
  throwError "reflect%: source operation is not representable by the target signature{indentExpr e}"

structure NatRecShape where
  recPos : Nat
  baseEqn : Name
  stepEqn : Name
  deriving Inhabited

private def withEqn {α} (eqn : Name)
    (k : Array Lean.Expr → Lean.Expr → MetaM α) : MetaM α := do
  let some ci := (← getEnv).find? eqn
    | throwError "reflect%: missing equation theorem `{eqn}`"
  forallTelescope ci.type fun _ body => do
    let_expr Eq _ lhs rhs := body
      | throwError "reflect%: unexpected equation theorem shape for `{eqn}`"
    k lhs.getAppArgs rhs

private def succVariable? (e : Lean.Expr) : Option Lean.Expr :=
  match_expr e with
  | Nat.succ n => if n.isFVar then some n else none
  | HAdd.hAdd _ _ _ _ n one =>
      match_expr one with
      | OfNat.ofNat _ lit _ =>
          if n.isFVar && lit.isRawNatLit && lit.rawNatLit? == some 1 then some n else none
      | _ => none
  | _ => none

private def unaryEquationRhs (eqn : Name) (stepArg : Option Lean.Expr) : MetaM Lean.Expr :=
  withEqn eqn fun lhs rhs => do
    unless lhs.size == 1 do
      throwError "reflect%: recursive equation `{eqn}` is not unary"
    match stepArg with
    | none => pure rhs
    | some value =>
        let some predVar := succVariable? lhs[0]!
          | throwError "reflect%: recursive step equation `{eqn}` has no predecessor"
        pure (rhs.replaceFVarId predVar.fvarId! value)

private def analyzeNatRec (name : Name) : MetaM (Option NatRecShape) := do
  let some eqns ← (try getEqnsFor? name catch _ => pure none) | return none
  unless eqns.size == 2 do return none
  let inspect (eqn : Name) : MetaM (Option (Nat × Bool × Bool)) :=
    withEqn eqn fun lhs rhs => do
      let mut patterned : Option (Nat × Bool) := none
      for i in [0:lhs.size] do
        unless lhs[i]!.isFVar do
          if patterned.isSome then return none
          let isStep := (succVariable? lhs[i]!).isSome
          let isZero ← isDefEq lhs[i]! (mkNatLit 0)
          unless isStep || isZero do return none
          patterned := some (i, isStep)
      let some (pos, isStep) := patterned | return none
      return some (pos, isStep, (rhs.find? (·.isConstOf name)).isSome)
  let some (p₁, step₁, rec₁) ← inspect eqns[0]! | return none
  let some (p₂, step₂, rec₂) ← inspect eqns[1]! | return none
  unless p₁ == p₂ && step₁ != step₂ do return none
  if step₁ && rec₁ && !rec₂ then
    return some { recPos := p₁, baseEqn := eqns[1]!, stepEqn := eqns[0]! }
  if step₂ && rec₂ && !rec₁ then
    return some { recPos := p₂, baseEqn := eqns[0]!, stepEqn := eqns[1]! }
  return none

structure Specialization where
  name : Name
  args : Array Lean.Expr
  arity : Nat
  valuePos : Array Nat
  staticPos : Array Nat
  argTypes : Array Lean.Expr
  argReprs : Array Lean.Expr
  sourceSig : Lean.Expr
  resultType : Lean.Expr
  resultRepr : Lean.Expr
  sourceRange? : Option Lean.Expr := none
  recursive : Bool := false
  recShape : Option NatRecShape := none
  deriving Inhabited

structure Discovery where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  compat : Lean.Expr
  resultType : Lean.Expr
  resultRepr : Lean.Expr
  specializations : Array Specialization

/-- A paired atom used by pass 2.  `source` may occur only in generated proof terms, `target` may
    occur only in generated PHOAS code, and `related` is the bridge used by smart constructors. -/
structure Atom where
  source : Lean.Expr
  code : Lean.Expr
  target : Lean.Expr
  related : Lean.Expr

structure Emission where
  code : Lean.Expr
  /-- One application of a `Reflection.*` smart constructor.  Its first projection is the AST and
      its second projection is the relational soundness witness, so emission cannot drift. -/
  reflection : Lean.Expr

structure Helper where
  spec : Specialization
  target : Lean.Expr
  adequate : Lean.Expr

private def checkedEmission (code reflection : Lean.Expr) : MetaM Emission := do
  let reflectedCode ← whnf (← mkAppM ``Sigma.fst #[reflection])
  unless ← isDefEq reflectedCode code do
    throwError "reflect%: internal: generated AST drifted from its smart-constructor proof\nAST:{indentExpr code}\nproof AST:{indentExpr reflectedCode}"
  pure { code, reflection }

private def annotateEmission (range : Lean.Expr) (emission : Emission) : MetaM Emission := do
  let reflection ← mkAppM ``Reflection.source #[range, emission.reflection]
  let code ← mkAppM ``Expr.source #[range, emission.code]
  checkedEmission code reflection

private def annotateRecEmission (range : Lean.Expr) (emission : Emission) : MetaM Emission := do
  let reflection ← mkAppM ``RecReflection.source #[range, emission.reflection]
  let code ← mkAppM ``Expr.source #[range, emission.code]
  checkedEmission code reflection

private def freekType? (ty : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let ty ← whnf ty
  if ty.isAppOfArity ``Freek 2 then
    return some (ty.getArg! 0, ty.getArg! 1)
  return none

private def isReflectorCore (n : Name) : Bool :=
  n == ``Freek.pure || n == ``Freek.op || n == ``Freek.bind ||
  n == ``Pure.pure || n == ``Bind.bind

private def sameArgs (xs ys : Array Lean.Expr) : MetaM Bool := do
  if xs.size != ys.size then return false
  let saved ← get
  for i in [0:xs.size] do
    unless ← isDefEq xs[i]! ys[i]! do
      set saved
      return false
  set saved
  return true

/-- Pass 1: discover all monomorphized `Freek` helpers in dependency order.  No AST or proof terms
    are emitted in this pass. -/
partial def discover (root : Lean.Expr) : TermElabM Discovery := do
  let some (S, α) ← freekType? (← inferType root)
    | throwError "reflect%: expected a `Freek` program{indentExpr root}"
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
  let done ← IO.mkRef (#[] : Array Specialization)
  let active ← IO.mkRef (#[] : Array (Name × Array Lean.Expr))
  let recursive ← IO.mkRef (#[] : Array (Name × Array Lean.Expr))
  let rec find? (n : Name) (args : Array Lean.Expr) : MetaM (Option Nat) := do
    let specs ← done.get
    for i in [0:specs.size] do
      if specs[i]!.name == n && (← sameArgs specs[i]!.args args) then return some i
    return none
  let rec active? (n : Name) (args : Array Lean.Expr) : MetaM Bool := do
    for entry in ← active.get do
      if entry.1 == n && (← sameArgs entry.2 args) then return true
    return false
  let rec isRecursive (n : Name) (args : Array Lean.Expr) : MetaM Bool := do
    for entry in ← recursive.get do
      if entry.1 == n && (← sameArgs entry.2 args) then return true
    return false
  let rec visit (e : Lean.Expr) : MetaM Unit := do
    let e ← instantiateMVars e
    let fn := e.getAppFn
    if let some n := fn.constName? then
      -- Representable arguments become parameters of the spilled helper.  Only static arguments
      -- such as types, dictionaries, and proof-erased configuration enter its specialization key.
      let mut args := #[]
      let mut valuePos := #[]
      let mut staticPos := #[]
      let mut argTypes := #[]
      let mut argReprs := #[]
      let callArgs := e.getAppArgs
      for i in [0:callArgs.size] do
        let arg := callArgs[i]!
        let argType ← inferType arg
        if ← hasRepr argType then
          valuePos := valuePos.push i
          argTypes := argTypes.push argType
          argReprs := argReprs.push (← getRepr argType)
        else if !arg.hasFVar then
          args := args.push arg
          staticPos := staticPos.push i
      if !isReflectorCore n then
        if let some (sig, result) ← freekType? (← inferType e) then
          if ast2InlineAttr.hasTag (← getEnv) n then
            if let some body ← unfoldDefinition? e then visit body
            return
          if (← active? n args) then
            recursive.modify (·.push (n, args))
            return
          if (← find? n args).isSome then return
          active.modify (·.push (n, args))
          if let some body ← unfoldDefinition? e then visit body
          active.modify (·.pop)
          let repr ← getRepr result
          let discoveredRec ← isRecursive n args
          let analyzedShape ← analyzeNatRec n
          let isRec := discoveredRec || analyzedShape.isSome
          let recShape ← if isRec then
            match analyzedShape with
            | some shape => pure (some shape)
            | none => analyzeNatRec n
          else pure none
          if isRec && recShape.isNone then
            throwError "reflect%: recursive helper `{n}` is not structural `Nat` recursion"
          let sourceRange? ← declarationSourceRange? n
          done.modify fun specs => specs.push {
            name := n
            args := args
            arity := callArgs.size
            valuePos := valuePos
            staticPos := staticPos
            argTypes := argTypes
            argReprs := argReprs
            sourceSig := sig
            resultType := result
            resultRepr := repr
            sourceRange? := sourceRange?
            recursive := isRec
            recShape := recShape
          }
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
  visit root
  let mut specializations ← done.get
  if let some rootName := root.getAppFn.constName? then
    if let some last := specializations.back? then
      if last.name == rootName && !last.recursive then
        specializations := specializations.pop
  pure {
    sourceSig := S
    targetSig := H
    compat := C
    resultType := α
    resultRepr := rootRepr
    specializations := specializations
  }

/-- Debugging surface for the first pass.  Kept intentionally small so specialization tests can
    pin discovery independently of AST emission. -/
elab "#reflect_plan " t:term : command => Command.liftTermElabM do
  let root ← elabTermAndSynthesize t none
  let plan ← discover (← instantiateMVars root)
  logInfo m!"AST2 reflection plan: {plan.specializations.map (·.name)}"

structure EmitGoal where
  sourceType : Lean.Expr
  targetTp : Lean.Expr
  relates : Lean.Expr

private def lookupAtom? (atoms : Array Atom) (source : Lean.Expr) : Option Atom :=
  atoms.find? fun atom => atom.source == source

private def emitValue (Φ repr source : Lean.Expr) (atoms : Array Atom) : MetaM Atom := do
  if let some atom := lookupAtom? atoms source then return atom
  if source.hasFVar then
    return ← withLocalDeclD `hΦ Φ fun hΦ => do
      let mut target := source
      let mut equality ← mkAppM ``Eq.refl #[source]
      for atom in atoms do
        if atom.source.isFVar && target.containsFVar atom.source.fvarId! then
          let next := target.replaceFVarId atom.source.fvarId! atom.target
          let atomEqType ← mkAppM ``Eq #[atom.source, atom.target]
          let atomEq ← mkExpectedTypeHint (mkApp atom.related hΦ) atomEqType
          let context ← mkLambdaFVars #[atom.source] target
          let step ← mkAppM ``congrArg #[context, atomEq]
          equality ← mkAppM ``Eq.trans #[equality, step]
          target := next
      let relation ← mkAppM ``ReprSpec.relates #[repr, source, target]
      let related ← mkLambdaFVars #[hΦ] (← mkExpectedTypeHint equality relation)
      return { source, code := target, target, related }
  let target ← mkAppM ``ReprSpec.encode #[repr, source]
  let relatedProof ← mkAppM ``ReprSpec.encode_related #[repr, source]
  let related := mkLambda `h .default Φ relatedProof
  pure { source, code := target, target, related }

structure RecEnv where
  spec : Specialization
  body : Lean.Expr
  ih : Lean.Expr
  currentSource : Lean.Expr
  order : Lean.Expr
  argRel : Lean.Expr
  currentRel : Lean.Expr
  nonzero : Lean.Expr

private partial def emitRecComp (plan : Discovery) (goal : EmitGoal)
    (env : RecEnv) (Φ source : Lean.Expr) (atoms : Array Atom := #[])
    (helpers : Array Helper := #[]) : MetaM Emission := do
  let initialSource ← instantiateMVars source
  let initialName := initialSource.getAppFn.constName?
  let initiallyNamed := helpers.any fun helper =>
    initialName == some helper.spec.name
  let rawSource ← if initiallyNamed then pure initialSource else whnf initialSource
  let callArgs := rawSource.getAppArgs
  let recursiveCall? (candidate : Lean.Expr) : MetaM Bool := do
    unless candidate.getAppFn.constName? == some env.spec.name do return false
    let args := candidate.getAppArgs
    let staticArgs := env.spec.staticPos.map (args[·]!)
    sameArgs env.spec.args staticArgs
  let emitCall (sourceCall sourceK : Lean.Expr) : MetaM Emission := do
    unless env.spec.valuePos.size == 1 do
      throwError "reflect%: recursive helper currently requires one represented argument"
    let smaller := sourceCall.getAppArgs[env.spec.valuePos[0]!]!
    let argRepr := env.spec.argReprs[0]!
    let targetArg ← emitValue Φ argRepr smaller atoms
    let ihAt ← withLocalDeclD `hΦ Φ fun hΦ => do
      let hrel := mkApp targetArg.related hΦ
      let hlt ← mkAppM ``natPred_lt_of_rel
        #[env.currentRel, hrel, mkApp env.nonzero hΦ]
      let callAdequate := mkAppN env.ih #[smaller, targetArg.target, hrel, hlt]
      mkLambdaFVars #[hΦ] callAdequate
    let resultRel ← mkAppM ``ReprSpec.relates #[env.spec.resultRepr]
    let targetResultTp ← mkAppM ``Tp.base
      #[← mkAppM ``ReprSpec.code #[env.spec.resultRepr]]
    let targetSpec ← mkAppM ``Signature.spec #[plan.targetSig]
    let semanticM := mkApp (Lean.mkConst ``ITree2.CompE [Level.zero, Level.zero]) targetSpec
    let targetResultType ← mkAppM ``Tp.denote #[semanticM, targetResultTp]
    let ⟨kCode, kSound⟩ ← withLocalDeclD `target targetResultType fun target =>
      withLocalDeclD `source env.spec.resultType fun sourceResult => do
        let relatedType ← mkAppM' resultRel #[sourceResult, target]
        withLocalDeclD `hrel relatedType fun hrel => do
          let nextSource := mkApp sourceK sourceResult
          let emitted ← emitRecComp plan goal env Φ nextSource
            (atoms.push {
              source := sourceResult
              code := target
              target := target
              related := mkLambda `h .default Φ hrel }) helpers
          let witness ← mkAppM ``Sigma.snd #[emitted.reflection]
          pure (← mkLambdaFVars #[target] emitted.code,
            ← mkLambdaFVars #[target, sourceResult, hrel] witness)
    let reflection ← mkAppOptM ``RecReflection.selfCall
      #[some plan.sourceSig, some plan.targetSig, some (Lean.mkConst ``Tp.nat),
        some targetResultTp, some goal.targetTp, some plan.compat,
        some env.body, some Φ, none, none, some resultRel, some goal.relates,
        some sourceCall, some targetArg.target, some ihAt, some sourceK,
        some kCode, some kSound]
    let code ← whnf (← mkAppM ``Sigma.fst #[reflection])
    checkedEmission code reflection
  if rawSource.getAppFn.constName? == some ``Freek.bind ||
      rawSource.getAppFn.constName? == some ``Bind.bind then
    let head := callArgs[callArgs.size - 2]!
    let sourceK := callArgs[callArgs.size - 1]!
    if ← recursiveCall? head then return ← emitCall head sourceK
  if ← recursiveCall? rawSource then
    let sourceResultType := env.spec.resultType
    let sourceK ← withLocalDeclD `source sourceResultType fun sourceResult => do
      mkLambdaFVars #[sourceResult]
        (← mkAppM ``Freek.pure #[sourceResult])
    return ← emitCall rawSource sourceK
  let source ← whnf rawSource
  if source.getAppFn.constName? == some ``Freek.pure ||
      source.getAppFn.constName? == some ``Pure.pure then
    let value := source.getAppArgs.back!
    let repr ← resolveRepr (← inferType value)
    let atom ← emitValue Φ repr value atoms
    let reflection ← mkAppOptM ``RecReflection.ret
      #[some plan.sourceSig, some plan.targetSig, none, none, some goal.targetTp,
        some plan.compat, some env.body, some Φ, some goal.sourceType,
        some goal.relates, some atom.target, some value, some atom.related]
    let code ← whnf (← mkAppM ``Sigma.fst #[reflection])
    return ← checkedEmission code reflection
  if source.getAppFn.constName? == some ``Freek.op then
    let args := source.getAppArgs
    let e := args[2]!
    let sourceInput := args[3]!
    let sourceBlocks := args[4]!
    let sourceK := args[5]!
    let opSpec ← resolveOp plan.compat e
    let targetOp ← mkAppM ``OpSpec.target #[opSpec]
    let witness ← mkAppM ``OpSpec.witness #[opSpec]
    let sourceBranchType ← mkAppM ``ITree2.HSig.branch #[plan.sourceSig, e]
    let targetBranchType ← mkAppM ``Signature.branch #[plan.targetSig, targetOp]
    unless (← isDefEq sourceBranchType (mkConst ``Empty)) &&
        (← isDefEq targetBranchType (mkConst ``Empty)) do
      throwError "reflect%: recursive dynamic blocks require the scoped interpreter bridge"
    let sourceEmpty ← withLocalDeclD `branch sourceBranchType fun branch => do
      let falseType := Lean.mkConst ``False
      mkLambdaFVars #[branch] (← mkAppOptM ``Empty.elim #[some falseType, some branch])
    let targetEmpty ← withLocalDeclD `branch targetBranchType fun branch => do
      let falseType := Lean.mkConst ``False
      mkLambdaFVars #[branch] (← mkAppOptM ``Empty.elim #[some falseType, some branch])
    let inputRepr ← resolveRepr (← inferType sourceInput)
    let input ← emitValue Φ inputRepr sourceInput atoms
    let hi := input.related
    let targetOutputCode ← mkAppM ``Signature.output #[plan.targetSig, targetOp]
    let targetOutputType ← mkAppM ``Tp0.denote #[targetOutputCode]
    let sourceOutputType ← mkAppM ``ITree2.HSig.output #[plan.sourceSig, e]
    let ⟨kCode, kSound⟩ ← withLocalDeclD `target targetOutputType fun target => do
      withLocalDeclD `sourceOutput sourceOutputType fun sourceOutput => do
          let outputRel ← mkAppM ``ITree2.HSig.Compat.output
            #[plan.compat, witness, sourceOutput, target]
          withLocalDeclD `hrel outputRel fun hrel => do
            let nextSource := mkApp sourceK sourceOutput
            let emitted ← emitRecComp plan goal env Φ nextSource
              (atoms.push {
                source := sourceOutput
                code := target
                target := target
                related := mkLambda `h .default Φ hrel }) helpers
            let proof ← mkAppM ``Sigma.snd #[emitted.reflection]
            pure (← mkLambdaFVars #[target] emitted.code,
              ← mkLambdaFVars #[target, sourceOutput, hrel] proof)
    let reflection ← mkAppOptM ``RecReflection.opNoBranches
      #[some plan.sourceSig, some plan.targetSig, some (Lean.mkConst ``Tp.nat),
        some (← mkAppM ``Tp.base #[← mkAppM ``ReprSpec.code #[env.spec.resultRepr]]),
        some goal.targetTp, some plan.compat, some env.body, some Φ,
        some goal.sourceType, some goal.relates, some e, some targetOp, some witness,
        some sourceEmpty, some targetEmpty, some input.target, some sourceInput,
        some hi, some sourceBlocks, some sourceK, some kCode, some kSound]
    let code ← whnf (← mkAppM ``Sigma.fst #[reflection])
    return ← checkedEmission code reflection
  if let some name := rawSource.getAppFn.constName? then
    if name != env.spec.name then
      if let some unfolded ← unfoldDefinition? rawSource then
        return ← emitRecComp plan goal env Φ unfolded atoms helpers
  throwError "reflect%: recursive pass does not recognize computation{indentExpr source}"

private partial def emitComp (plan : Discovery) (goal : EmitGoal)
    (Φ source : Lean.Expr) (atoms : Array Atom := #[])
    (helpers : Array Helper := #[]) : MetaM Emission := do
  let initialSource ← instantiateMVars source
  let initialName := initialSource.getAppFn.constName?
  let initiallyNamed := helpers.any fun helper => initialName == some helper.spec.name
  let rawSource ← if initiallyNamed then pure initialSource else whnf initialSource
  if let some name := rawSource.getAppFn.constName? then
    let callArgs := rawSource.getAppArgs
    let recursiveHelper? := helpers.find? fun helper =>
      helper.spec.recursive && helper.spec.name == name
    let helper? ← match recursiveHelper? with
      | some helper => pure (some helper)
      | none => helpers.findM? fun helper => do
          unless helper.spec.name == name do return false
          let staticArgs := helper.spec.staticPos.map (callArgs[·]!)
          sameArgs helper.spec.args staticArgs
    if let some helper := helper? then
      unless helper.spec.valuePos.size == 1 || helper.spec.valuePos.size == 2 do
        throwError "reflect%: helper spilling supports one argument or a tuple of two arguments"
      let sourceArg₁ := rawSource.getAppArgs[helper.spec.valuePos[0]!]!
      let arg₁ ← emitValue Φ helper.spec.argReprs[0]! sourceArg₁ atoms
      let ⟨sourceArg, targetArg, related⟩ ← if helper.spec.valuePos.size == 1 then
        pure (sourceArg₁, arg₁.target, arg₁.related)
      else
        let sourceArg₂ := rawSource.getAppArgs[helper.spec.valuePos[1]!]!
        let arg₂ ← emitValue Φ helper.spec.argReprs[1]! sourceArg₂ atoms
        let sourcePair ← mkAppM ``Prod.mk #[sourceArg₁, sourceArg₂]
        let targetPair ← mkAppM ``Prod.mk #[arg₁.target, arg₂.target]
        let related ← withLocalDeclD `hΦ Φ fun hΦ => do
          let proof ← mkAppM ``And.intro #[mkApp arg₁.related hΦ, mkApp arg₂.related hΦ]
          mkLambdaFVars #[hΦ] proof
        pure (sourcePair, targetPair, related)
      let hEutt ← withLocalDeclD `hΦ Φ fun hΦ =>
        mkLambdaFVars #[hΦ]
          (mkAppN helper.adequate #[sourceArg, targetArg, mkApp related hΦ])
      let reflection ← mkAppOptM ``Reflection.call
        #[some plan.sourceSig, some plan.targetSig, some plan.compat, some Φ,
          none, some goal.targetTp, some goal.sourceType, some goal.relates,
          some helper.target, some targetArg, some rawSource, some hEutt]
      let code ← whnf (← mkAppM ``Sigma.fst #[reflection])
      return ← checkedEmission code reflection
  let source ← whnf source
  let recursionSlotType ← mkAppM ``Prod #[mkConst ``Tp, mkConst ``Tp]
  let noRecursion ← mkAppOptM ``Option.none #[some recursionSlotType]
  let targetSpec ← mkAppM ``Signature.spec #[plan.targetSig]
  let compE := Lean.mkConst ``ITree2.CompE [Level.zero, Level.zero]
  let semanticM := mkApp compE targetSpec
  let semanticV ← mkAppM ``Tp.denote #[semanticM]
  if source.getAppFn.constName? == some ``Freek.pure then
    let value := source.getAppArgs.back!
    let repr ← resolveRepr (← inferType value)
    let atom ← emitValue Φ repr value atoms
    let reflection ← mkAppOptM ``Reflection.ret
      #[some plan.sourceSig, some plan.targetSig, some noRecursion, some plan.compat, some Φ,
        some goal.targetTp, some goal.sourceType, some goal.relates,
        some atom.target, some value, some atom.related]
    let code ← mkAppOptM ``Expr.ret
      #[some plan.targetSig, some semanticV, some noRecursion, some goal.targetTp,
        some atom.target]
    return ← checkedEmission code reflection
  if source.getAppFn.constName? == some ``Freek.op then
    let args := source.getAppArgs
    let e := args[2]!
    let sourceInput := args[3]!
    let sourceBlocks := args[4]!
    let sourceK := args[5]!
    let opSpec ← resolveOp plan.compat e
    let targetOp ← mkAppM ``OpSpec.target #[opSpec]
    let witness ← mkAppM ``OpSpec.witness #[opSpec]
    let inputRepr ← resolveRepr (← inferType sourceInput)
    let input ← emitValue Φ inputRepr sourceInput atoms
    let opHead ← mkAppOptM ``Reflection.op
      #[some plan.sourceSig, some plan.targetSig, some plan.compat, some Φ,
        some goal.targetTp, some goal.sourceType, some goal.relates, some e, some targetOp,
        some witness, some input.target, some sourceInput, some input.related, some sourceBlocks]
    let .forallE _ blocksType _ _ ← whnf (← inferType opHead)
      | throwError "reflect%: internal: malformed `Reflection.op` block argument"
    let targetBranchType ← mkAppM ``Signature.branch #[plan.targetSig, targetOp]
    let emptyBranches ← isDefEq targetBranchType (mkConst ``Empty)
    let ⟨blocksCode, blockSound⟩ ← if emptyBranches then
      let .forallE _ btType btBody _ := blocksType
        | throwError "reflect%: internal: block argument is not a function"
      withLocalDeclD `bt btType fun bt => do
        let .forallE _ xtType xtBody _ := btBody.instantiate1 bt
          | throwError "reflect%: internal: block binder argument is not a function"
        withLocalDeclD `xt xtType fun xt => do
          let codeType := xtBody.instantiate1 xt
          let impossibleCode ← mkAppOptM ``Empty.elim #[some codeType, some bt]
          let blocksCode ← mkLambdaFVars #[bt, xt] impossibleCode
          let withBlocks := mkApp opHead blocksCode
          let .forallE _ blockSoundType _ _ ← whnf (← inferType withBlocks)
            | throwError "reflect%: internal: malformed block-soundness argument"
          forallTelescope blockSoundType fun binders body => do
            let some soundBt := binders[0]?
              | throwError "reflect%: internal: empty block soundness has no branch binder"
            let impossibleSound ← mkAppOptM ``Empty.elim #[some body, some soundBt]
            pure (blocksCode, ← mkLambdaFVars binders impossibleSound)
    else withLocalDeclD `bt targetBranchType fun bt => do
      let targetInputCode ← mkAppM ``Signature.branchInput #[plan.targetSig, targetOp, bt]
      let targetInputType ← mkAppM ``Tp0.denote #[targetInputCode]
      withLocalDeclD `xt targetInputType fun xt => do
        let sourceBranchType ← mkAppM ``ITree2.HSig.branch #[plan.sourceSig, e]
        withLocalDeclD `bs sourceBranchType fun bs => do
          let branchRelType ← mkAppM ``ITree2.HSig.Compat.branch
            #[plan.compat, witness, bs, bt]
          withLocalDeclD `hbr branchRelType fun hbr => do
            let sourceInputType ← mkAppM ``ITree2.HSig.branchInput #[plan.sourceSig, e, bs]
            withLocalDeclD `xs sourceInputType fun xs => do
              let inputRelType ← mkAppM ``ITree2.HSig.Compat.branchInput
                #[plan.compat, witness, hbr, xs, xt]
              withLocalDeclD `hx inputRelType fun hx => do
                let blockSource ← mkAppM' sourceBlocks #[bs, xs]
                let blockSourceType ← inferType blockSource
                let blockTargetCode ← mkAppM ``Signature.branchOutput #[plan.targetSig, targetOp, bt]
                let blockTargetTp ← mkAppM ``Tp.base #[blockTargetCode]
                let blockRel ← mkAppM ``ITree2.HSig.Compat.branchOutput
                  #[plan.compat, witness, hbr]
                let emitted ← emitComp plan {
                  sourceType := blockSourceType.getArg! 1
                  targetTp := blockTargetTp
                  relates := blockRel
                } Φ blockSource (atoms.push {
                  source := bs
                  code := bt
                  target := bt
                  related := mkLambda `h .default Φ hbr } |>.push
                  { source := xs
                    code := xt
                    target := xt
                    related := mkLambda `h .default Φ hx }) helpers
                let code := emitted.code
                if code.containsFVar bs.fvarId! || code.containsFVar hbr.fvarId! ||
                    code.containsFVar xs.fvarId! || code.containsFVar hx.fvarId! then
                  throwError "reflect%: block AST depends on source-only relational binders"
                let proof ← whnf (← mkAppM ``Sigma.snd #[emitted.reflection])
                let proof ← mkLambdaFVars #[bs, hbr, xs, hx] proof
                pure (← mkLambdaFVars #[bt, xt] emitted.code,
                  ← mkLambdaFVars #[bt, xt] proof)
    let targetOutputCode ← mkAppM ``Signature.output #[plan.targetSig, targetOp]
    let targetOutputType ← mkAppM ``Tp0.denote #[targetOutputCode]
    let ⟨kCode, kSound⟩ ← withLocalDeclD `ot targetOutputType fun ot => do
      let sourceOutputType ← mkAppM ``ITree2.HSig.output #[plan.sourceSig, e]
      withLocalDeclD `os sourceOutputType fun os => do
        let outputRelType ← mkAppM ``ITree2.HSig.Compat.output
          #[plan.compat, witness, os, ot]
        withLocalDeclD `ho outputRelType fun ho => do
          let nextSource := mkApp sourceK os
          let emitted ← emitComp plan goal Φ nextSource
            (atoms.push {
              source := os
              code := ot
              target := ot
              related := mkLambda `h .default Φ ho
            }) helpers
          let code := emitted.code
          if code.containsFVar os.fvarId! || code.containsFVar ho.fvarId! then
            throwError "reflect%: continuation AST depends on source-only relational binders\nAST:{indentExpr code}\nsource output: {code.containsFVar os.fvarId!}\nrelation proof: {code.containsFVar ho.fvarId!}"
          let proof ← whnf (← mkAppM ``Sigma.snd #[emitted.reflection])
          let proof ← mkLambdaFVars #[os, ho] proof
          pure (← mkLambdaFVars #[ot] emitted.code,
            ← mkLambdaFVars #[ot] proof)
    let reflection ← mkAppM' opHead #[blocksCode, blockSound, kCode, kSound]
    let code ← mkAppOptM ``Expr.op
      #[some plan.targetSig, some semanticV, some noRecursion, some goal.targetTp,
        some targetOp, some input.target, some blocksCode, some kCode]
    return ← checkedEmission code reflection
  throwError "reflect%: pass 2 does not recognize computation{indentExpr source}"

private partial def emitProgram (plan : Discovery) (goal : EmitGoal)
    (source : Lean.Expr) (specs : List Specialization := plan.specializations.toList)
    (helpers : Array Helper := #[]) : MetaM Emission := do
  match specs with
  | [] => emitComp plan goal (mkConst ``True) source #[] helpers
  | spec :: rest =>
      if spec.recursive then
        unless spec.arity == 1 && spec.valuePos == #[0] do
          throwError "reflect%: recursive helper `{spec.name}` currently requires one Nat argument"
        let some shape := spec.recShape
          | throwError "reflect%: recursive helper `{spec.name}` lost its equation shape"
        let argRepr := spec.argReprs[0]!
        let argCode ← mkAppM ``ReprSpec.code #[argRepr]
        unless ← isDefEq argCode (mkConst ``Tp0.nat) do
          throwError "reflect%: recursive helper `{spec.name}` must use the Nat representation"
        let argRel ← whnf (← mkAppM ``ReprSpec.relates #[argRepr])
        let argTp := Lean.mkConst ``Tp.nat
        let resultTp ← mkAppM ``Tp.base #[← mkAppM ``ReprSpec.code #[spec.resultRepr]]
        let resultRel ← mkAppM ``ReprSpec.relates #[spec.resultRepr]
        let targetSpec ← mkAppM ``Signature.spec #[plan.targetSig]
        let semanticM := mkApp (Lean.mkConst ``ITree2.CompE [Level.zero, Level.zero]) targetSpec
        let semanticV ← mkAppM ``Tp.denote #[semanticM]
        let targetArgType ← mkAppM ``Tp.denote #[semanticM, argTp]
        let recursionPair ← mkAppM ``Prod.mk #[argTp, resultTp]
        let recursionSlot ← mkAppM ``Option.some #[recursionPair]
        let bodyResultType ← mkAppM ``Expr
          #[plan.targetSig, semanticV, recursionSlot, resultTp]
        let bodyType ← mkArrow targetArgType bodyResultType
        let bodyMVar ← mkFreshExprMVar bodyType
        let sourceFn ← mkConstWithFreshMVarLevels spec.name
        let order ← withLocalDeclD `smaller (Lean.mkConst ``Nat) fun smaller => do
          withLocalDeclD `current (Lean.mkConst ``Nat) fun current => do
            mkLambdaFVars #[smaller, current]
              (← mkAppM ``LT.lt #[smaller, current])
        let bodySound ← withLocalDeclD `sourceArg (Lean.mkConst ``Nat) fun sourceArg => do
          withLocalDeclD `targetArg targetArgType fun targetArg => do
            let hrelType ← mkAppM' argRel #[sourceArg, targetArg]
            withLocalDeclD `hrel hrelType fun hrel => do
              let smallerType ← withLocalDeclD `smaller (Lean.mkConst ``Nat) fun smaller =>
                withLocalDeclD `targetSmaller targetArgType fun targetSmaller => do
                  let hsType ← mkAppM' argRel #[smaller, targetSmaller]
                  withLocalDeclD `hs hsType fun hs => do
                    let hltType ← mkAppM' order #[smaller, sourceArg]
                    withLocalDeclD `hlt hltType fun hlt => do
                      let conclusion ← mkAppOptM ``RecCallAdequate
                        #[some plan.sourceSig, some plan.targetSig, some argTp, some resultTp,
                          some plan.compat, some bodyMVar, some (Lean.mkConst ``True),
                          some spec.resultType, some resultRel,
                          some (mkApp sourceFn smaller), some targetSmaller]
                      mkForallFVars #[smaller, targetSmaller, hs, hlt] conclusion
              withLocalDeclD `ih smallerType fun ih => do
                let zero := mkNatLit 0
                let one := mkNatLit 1
                let condition ← mkAppM ``BEq.beq #[targetArg, zero]
                let predecessor ← mkAppM ``Nat.sub #[targetArg, one]
                let baseSource ← unaryEquationRhs shape.baseEqn none
                let stepSource ← unaryEquationRhs shape.stepEqn (some predecessor)
                let baseΦ ← mkAppM ``And #[Lean.mkConst ``True,
                  ← mkAppM ``Eq #[condition, Lean.mkConst ``true]]
                let stepΦ ← mkAppM ``And #[Lean.mkConst ``True,
                  ← mkAppM ``Eq #[condition, Lean.mkConst ``false]]
                let nonzero ← withLocalDeclD `hΦ stepΦ fun hΦ => do
                  mkLambdaFVars #[hΦ] (← mkAppM ``And.right #[hΦ])
                let currentRel ← mkExpectedTypeHint hrel
                  (← mkAppM ``Eq #[sourceArg, targetArg])
                let atoms : Array Atom := #[{
                  source := sourceArg, code := targetArg, target := targetArg,
                  related := mkLambda `h .default (Lean.mkConst ``True) hrel }]
                let recEnv : RecEnv := {
                  spec := spec
                  body := bodyMVar
                  ih := ih
                  currentSource := sourceArg
                  order := order
                  argRel := argRel
                  currentRel := currentRel
                  nonzero := nonzero }
                let base ← emitRecComp plan {
                  sourceType := spec.resultType, targetTp := resultTp, relates := resultRel
                } recEnv baseΦ baseSource atoms helpers
                let step ← emitRecComp plan {
                  sourceType := spec.resultType, targetTp := resultTp, relates := resultRel
                } recEnv stepΦ stepSource atoms helpers
                let resultTargetType ← mkAppM ``Tp.denote #[semanticM, resultTp]
                let kCode ← withLocalDeclD `value resultTargetType fun value => do
                  let ret ← mkAppOptM ``Expr.ret
                    #[some plan.targetSig, some semanticV, some recursionSlot,
                      some resultTp, some value]
                  mkLambdaFVars #[value] ret
                let kSound ← withLocalDeclD `target resultTargetType fun target => do
                  withLocalDeclD `sourceResult spec.resultType fun sourceResult => do
                    withLocalDeclD `hr (← mkAppM' resultRel #[sourceResult, target]) fun hr => do
                      let related := mkLambda `h .default (mkConst ``True) hr
                      let ret ← mkAppOptM ``RecReflection.ret
                        #[some plan.sourceSig, some plan.targetSig, some argTp, some resultTp,
                          some resultTp, some plan.compat, some bodyMVar, some (mkConst ``True),
                          some spec.resultType, some resultRel, some target,
                          some sourceResult, some related]
                      let witness ← mkAppM ``Sigma.snd #[ret]
                      mkLambdaFVars #[target, sourceResult, hr] witness
                let iteReflection ← mkAppOptM ``RecReflection.ite
                  #[some plan.sourceSig, some plan.targetSig, some argTp, some resultTp,
                    some resultTp, some resultTp, some plan.compat, some bodyMVar,
                    some (mkConst ``True), some spec.resultType, some spec.resultType,
                    some condition, some resultRel, some resultRel,
                    some baseSource, some stepSource, some base.reflection,
                    some step.reflection, none, some kCode, some kSound]
                let bodyCode ← mkAppOptM ``Expr.ite
                  #[some plan.targetSig, some semanticV, some recursionSlot, some resultTp,
                    some resultTp, some condition, some base.code, some step.code, some kCode]
                let bodyEmission ← checkedEmission bodyCode iteReflection
                let bodyEmission ← match spec.sourceRange? with
                  | some range => annotateRecEmission range bodyEmission
                  | none => pure bodyEmission
                bodyMVar.mvarId!.assign (← mkLambdaFVars #[targetArg] bodyEmission.code)
                let stepFn ← withLocalDeclD `n (mkConst ``Nat) fun n => do
                  mkLambdaFVars #[n] (← unaryEquationRhs shape.stepEqn (some n))
                let hcases ← mkAppM ``natCases_eq
                  #[sourceFn, baseSource, stepFn, mkConst shape.baseEqn,
                    mkConst shape.stepEqn, targetArg]
                let harg ← mkAppM ``congrArg #[sourceFn, hrel]
                let choiceEq ← mkAppM ``Eq.trans #[hcases, ← mkAppM ``Eq.symm #[harg]]
                let choiceCondition ← mkAppM ``Eq #[condition, Lean.mkConst ``true]
                let choice ← mkAppM ``ite #[choiceCondition, baseSource, stepSource]
                let bindPure ← mkAppM ``Freek.bind_pure #[choice]
                let sourceEq ← mkAppM ``Eq.trans #[bindPure, choiceEq]
                let transported ← mkAppM ``RecReflection.congrSource
                  #[sourceEq, bodyEmission.reflection]
                let witness ← mkAppM ``Sigma.snd #[transported]
                mkLambdaFVars #[sourceArg, targetArg, hrel, ih] witness
        let body ← instantiateMVars bodyMVar
        let wf ← mkAppOptM ``WellFoundedRelation.wf
          #[some (Lean.mkConst ``Nat), some (Lean.mkConst ``Nat.lt_wfRel)]
        let adequate ← mkAppOptM ``RecReflection.adequate
          #[some plan.sourceSig, some plan.targetSig, some argTp, some resultTp,
            some plan.compat, some (Lean.mkConst ``Nat), some spec.resultType,
            some argRel, some resultRel, some sourceFn, some body,
            some order, some wf, some bodySound]
        let targetFn ← mkAppM ``ITree2.CompE.mrec
          #[← withLocalDeclD `x targetArgType fun x => do
            mkLambdaFVars #[x] (← mkAppM ``Expr.denote #[mkApp body x])]
        let helper : Helper := { spec, target := targetFn, adequate }
        let inner ← emitProgram plan goal source rest (helpers.push helper)
        let fnType ← inferType targetFn
        let kCode ← withLocalDeclD `helper fnType fun bound =>
          mkLambdaFVars #[bound] (inner.code.replace fun e =>
            if e == targetFn then some bound else none)
        let innerWitness ← mkAppM ``Sigma.snd #[inner.reflection]
        let reflection ← mkAppOptM ``Reflection.letrec
          #[some plan.sourceSig, some plan.targetSig, some plan.compat, some (mkConst ``True),
            some argTp, some resultTp, some goal.targetTp, some goal.sourceType,
            some goal.relates, some source, some body, some kCode, some innerWitness]
        let code ← mkAppOptM ``Expr.letrec
          #[some plan.targetSig, none, none, some goal.targetTp, some argTp,
            some resultTp, some body, some kCode]
        checkedEmission code reflection
      else
        if spec.valuePos.size == 2 && spec.staticPos.size + 2 == spec.arity then
          let repr₁ := spec.argReprs[0]!
          let repr₂ := spec.argReprs[1]!
          let code₁ ← mkAppM ``ReprSpec.code #[repr₁]
          let code₂ ← mkAppM ``ReprSpec.code #[repr₂]
          let pairCode ← mkAppM ``Tp0.prod #[code₁, code₂]
          let argTp ← mkAppM ``Tp.base #[pairCode]
          let sourcePairType ← mkAppM ``Prod #[spec.argTypes[0]!, spec.argTypes[1]!]
          let targetSpec ← mkAppM ``Signature.spec #[plan.targetSig]
          let semanticM := mkApp (Lean.mkConst ``ITree2.CompE [Level.zero, Level.zero]) targetSpec
          let targetPairType ← mkAppM ``Tp.denote #[semanticM, argTp]
          let resultTp ← mkAppM ``Tp.base #[← mkAppM ``ReprSpec.code #[spec.resultRepr]]
          let resultRel ← mkAppM ``ReprSpec.relates #[spec.resultRepr]
          let rel₁ ← mkAppM ``ReprSpec.relates #[repr₁]
          let rel₂ ← mkAppM ``ReprSpec.relates #[repr₂]
          let pairRel ← withLocalDeclD `source sourcePairType fun sourcePair =>
            withLocalDeclD `target targetPairType fun targetPair => do
              let left ← mkAppM ``Prod.fst #[sourcePair]
              let right ← mkAppM ``Prod.snd #[sourcePair]
              let targetLeft ← mkAppM ``Prod.fst #[targetPair]
              let targetRight ← mkAppM ``Prod.snd #[targetPair]
              mkLambdaFVars #[sourcePair, targetPair]
                (← mkAppM ``And #[← mkAppM' rel₁ #[left, targetLeft],
                  ← mkAppM' rel₂ #[right, targetRight]])
          let ⟨bodyCode, targetFn, adequateCurried⟩ ←
            withLocalDeclD `source₁ spec.argTypes[0]! fun source₁ =>
            withLocalDeclD `source₂ spec.argTypes[1]! fun source₂ =>
            withLocalDeclD `target targetPairType fun targetPair => do
              let target₁ ← mkAppM ``Prod.fst #[targetPair]
              let target₂ ← mkAppM ``Prod.snd #[targetPair]
              let Φ ← mkAppM ``And #[← mkAppM' rel₁ #[source₁, target₁],
                ← mkAppM' rel₂ #[source₂, target₂]]
              let mut fullArgs := Array.replicate spec.arity source₁
              fullArgs := fullArgs.set! spec.valuePos[0]! source₁
              fullArgs := fullArgs.set! spec.valuePos[1]! source₂
              for i in [0:spec.staticPos.size] do
                fullArgs := fullArgs.set! spec.staticPos[i]! spec.args[i]!
              let sourceCall := mkAppN (← mkConstWithFreshMVarLevels spec.name) fullArgs
              let some bodySource ← unfoldDefinition? sourceCall
                | throwError "reflect%: cannot unfold tupled helper `{spec.name}`"
              let leftRelated ← withLocalDeclD `hΦ Φ fun hΦ => do
                mkLambdaFVars #[hΦ] (← mkAppM ``And.left #[hΦ])
              let rightRelated ← withLocalDeclD `hΦ Φ fun hΦ => do
                mkLambdaFVars #[hΦ] (← mkAppM ``And.right #[hΦ])
              let body ← emitComp plan {
                sourceType := spec.resultType, targetTp := resultTp, relates := resultRel
              } Φ bodySource #[
                { source := source₁, code := target₁, target := target₁,
                  related := leftRelated },
                { source := source₂, code := target₂, target := target₂,
                  related := rightRelated }
              ] helpers
              let body ← match spec.sourceRange? with
                | some range => annotateEmission range body
                | none => pure body
              let bodyCode ← mkLambdaFVars #[targetPair] body.code
              let targetFn ← mkLambdaFVars #[targetPair] (← mkAppM ``Expr.denote #[body.code])
              let witness ← mkAppM ``Sigma.snd #[body.reflection]
              let adequateCurried ← withLocalDeclD `hrel Φ fun hrel => do
                let sound ← mkAppM ``ReflectionWitnessAt.sound #[witness, hrel]
                mkLambdaFVars #[source₁, source₂, targetPair, hrel] sound
              pure (bodyCode, targetFn, adequateCurried)
          let adequate ← withLocalDeclD `source sourcePairType fun sourcePair =>
            withLocalDeclD `target targetPairType fun targetPair => do
              let source₁ ← mkAppM ``Prod.fst #[sourcePair]
              let source₂ ← mkAppM ``Prod.snd #[sourcePair]
              let Φ ← mkAppM' pairRel #[sourcePair, targetPair]
              withLocalDeclD `hrel Φ fun hrel => do
                mkLambdaFVars #[sourcePair, targetPair, hrel]
                  (mkAppN adequateCurried #[source₁, source₂, targetPair, hrel])
          let helper : Helper := { spec, target := targetFn, adequate }
          let inner ← emitProgram plan goal source rest (helpers.push helper)
          let fnType ← inferType targetFn
          let kCode ← withLocalDeclD `helper fnType fun bound =>
            mkLambdaFVars #[bound] (inner.code.replace fun e =>
              if e == targetFn then some bound else none)
          let innerWitness ← mkAppM ``Sigma.snd #[inner.reflection]
          let reflection ← mkAppOptM ``Reflection.lam
            #[some plan.sourceSig, some plan.targetSig, some plan.compat,
              some (Lean.mkConst ``True), some argTp, some resultTp,
              some goal.targetTp, some goal.sourceType, some goal.relates,
              some source, some bodyCode, some kCode, some innerWitness]
          let code ← mkAppOptM ``Expr.lam
            #[some plan.targetSig, none, none, some goal.targetTp, some argTp,
              some resultTp, some bodyCode, some kCode]
          return ← checkedEmission code reflection
        unless spec.valuePos.size == 1 && spec.staticPos.size + 1 == spec.arity do
          throwError "reflect%: nonrecursive helper spilling currently supports one represented argument plus static specialization arguments; `{spec.name}` has positions {spec.valuePos}"
        let argRepr := spec.argReprs[0]!
        let argTp ← mkAppM ``Tp.base #[← mkAppM ``ReprSpec.code #[argRepr]]
        let targetSpec ← mkAppM ``Signature.spec #[plan.targetSig]
        let semanticM := mkApp (Lean.mkConst ``ITree2.CompE [Level.zero, Level.zero]) targetSpec
        let targetArgType ← mkAppM ``Tp.denote #[semanticM, argTp]
        let resultTp ← mkAppM ``Tp.base #[← mkAppM ``ReprSpec.code #[spec.resultRepr]]
        let resultRel ← mkAppM ``ReprSpec.relates #[spec.resultRepr]
        withLocalDeclD `sourceArg spec.argTypes[0]! fun sourceArg =>
          withLocalDeclD `targetArg targetArgType fun targetArg => do
            let argRel ← mkAppM ``ReprSpec.relates #[argRepr]
            let Φ ← mkAppM' argRel #[sourceArg, targetArg]
            let mut fullArgs := Array.replicate spec.arity sourceArg
            fullArgs := fullArgs.set! spec.valuePos[0]! sourceArg
            for i in [0:spec.staticPos.size] do
              fullArgs := fullArgs.set! spec.staticPos[i]! spec.args[i]!
            let sourceCall := mkAppN (← mkConstWithFreshMVarLevels spec.name) fullArgs
            let some bodySource ← unfoldDefinition? sourceCall
              | throwError "reflect%: cannot unfold helper `{spec.name}`"
            let related := mkLambda `h .default Φ (.bvar 0)
            let body ← emitComp plan {
              sourceType := spec.resultType
              targetTp := resultTp
              relates := resultRel
            } Φ bodySource #[{
              source := sourceArg
              code := targetArg
              target := targetArg
              related := related
            }] helpers
            let body ← match spec.sourceRange? with
              | some range => annotateEmission range body
              | none => pure body
            let bodyCode ← mkLambdaFVars #[targetArg] body.code
            let targetFn ← mkLambdaFVars #[targetArg] (← mkAppM ``Expr.denote #[body.code])
            let witness ← mkAppM ``Sigma.snd #[body.reflection]
            let adequate ← withLocalDeclD `hrel Φ fun hrel => do
              let sound ← mkAppM ``ReflectionWitnessAt.sound #[witness, hrel]
              mkLambdaFVars #[sourceArg, targetArg, hrel] sound
            let helper : Helper := { spec, target := targetFn, adequate }
            let inner ← emitProgram plan goal source rest (helpers.push helper)
            let fnType ← inferType targetFn
            let kCode ← withLocalDeclD `helper fnType fun bound =>
              mkLambdaFVars #[bound] (inner.code.replace fun e =>
                if e == targetFn then some bound else none)
            let innerWitness ← mkAppM ``Sigma.snd #[inner.reflection]
            let reflection ← mkAppOptM ``Reflection.lam
              #[some plan.sourceSig, some plan.targetSig, some plan.compat, some (mkConst ``True),
                some argTp, some resultTp, some goal.targetTp, some goal.sourceType,
                some goal.relates, some source, some bodyCode, some kCode, some innerWitness]
            let code ← mkAppOptM ``Expr.lam
              #[some plan.targetSig, none, none, some goal.targetTp, some argTp,
                some resultTp, some bodyCode, some kCode]
            checkedEmission code reflection

structure GenericAtom where
  semantic : Lean.Expr
  code : Lean.Expr

private def genericAtom? (atoms : Array GenericAtom) (semantic : Lean.Expr) : Option Lean.Expr :=
  (atoms.find? (·.semantic == semantic)).map (·.code)

private def boolValue? (e : Lean.Expr) : MetaM (Option Bool) := do
  let saved ← get
  if ← isDefEq e (mkConst ``true) then
    set saved
    return some true
  set saved
  if ← isDefEq e (mkConst ``false) then
    set saved
    return some false
  set saved
  return none

private partial def reifyGenericValue (H V r tp value : Lean.Expr)
    (atoms : Array GenericAtom) (k : Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr := do
  if let some code := genericAtom? atoms value then return ← k code
  let reduced ← whnf value
  if let some code := genericAtom? atoms reduced then return ← k code
  if ← isDefEq tp (mkConst ``Tp0.nat) then
    if let some n ← getNatValue? reduced then
      let codeType := mkApp V (mkConst ``Tp.nat)
      return ← withLocalDeclD `n codeType fun code => do
        let tail ← k code
        let cont ← mkLambdaFVars #[code] tail
        mkAppOptM ``Expr.natLit #[some H, some V, some r, none, some (mkNatLit n), some cont]
  if ← isDefEq tp (mkConst ``Tp0.bool) then
    if let some b ← boolValue? reduced then
      let codeType := mkApp V (mkConst ``Tp.bool)
      return ← withLocalDeclD `b codeType fun code => do
        let tail ← k code
        let cont ← mkLambdaFVars #[code] tail
        mkAppOptM ``Expr.boolLit #[some H, some V, some r, none,
          some (mkConst (if b then ``true else ``false)), some cont]
  if ← isDefEq tp (mkConst ``Tp0.unit) then
    let codeType := mkApp V (mkConst ``Tp.unit)
    return ← withLocalDeclD `unit codeType fun code => do
      let tail ← k code
      let cont ← mkLambdaFVars #[code] tail
      mkAppOptM ``Expr.unitLit #[some H, some V, some r, none, some cont]
  let fn := value.getAppFn.constName?
  let args := value.getAppArgs
  if fn == some ``Prod.fst || fn == some ``Prod.snd then
    let pair := args[args.size - 1]!
    let pairType ← whnf (← inferType pair)
    let .app (.app (.const ``Prod _) leftType) rightType := pairType
      | throwError "reflect%: malformed product projection"
    let leftRepr ← resolveRepr leftType
    let rightRepr ← resolveRepr rightType
    let leftCode ← mkAppM ``ReprSpec.code #[leftRepr]
    let rightCode ← mkAppM ``ReprSpec.code #[rightRepr]
    let pairTp ← mkAppM ``Tp0.prod #[leftCode, rightCode]
    return ← reifyGenericValue H V r pairTp pair atoms fun pairCode => do
      let resultCodeType := mkApp V (← mkAppM ``Tp.base #[tp])
      withLocalDeclD `result resultCodeType fun resultCode => do
        let tail ← k resultCode
        let cont ← mkLambdaFVars #[resultCode] tail
        let op ← mkAppOptM (if fn == some ``Prod.fst then ``Un.fst else ``Un.snd)
          #[some leftCode, some rightCode]
        mkAppOptM ``Expr.un #[some H, some V, some r, none, none, none,
          some op, some pairCode, some cont]
  if fn == some ``Prod.mk then
    let .app (.app (.const ``Tp0.prod _) leftTp) rightTp := tp
      | throwError "reflect%: product constructor used at a non-product object type"
    let left := args[args.size - 2]!
    let right := args[args.size - 1]!
    return ← reifyGenericValue H V r leftTp left atoms fun leftCode =>
      reifyGenericValue H V r rightTp right atoms fun rightCode => do
        let resultCodeType := mkApp V (← mkAppM ``Tp.base #[tp])
        withLocalDeclD `result resultCodeType fun resultCode => do
          let tail ← k resultCode
          let cont ← mkLambdaFVars #[resultCode] tail
          mkAppOptM ``Expr.bin #[some H, some V, some r, none, none, none, none,
            some (mkConst ``Bin.pair), some leftCode, some rightCode, some cont]
  let bin? : Option (Name × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) :=
    if fn == some ``Nat.mul then some (``Bin.mul, mkConst ``Tp0.nat, mkConst ``Tp0.nat,
      mkConst ``Tp0.nat, args[args.size - 2]!, args[args.size - 1]!)
    else if fn == some ``Nat.add then some (``Bin.add, mkConst ``Tp0.nat, mkConst ``Tp0.nat,
      mkConst ``Tp0.nat, args[args.size - 2]!, args[args.size - 1]!)
    else if fn == some ``Nat.sub then some (``Bin.sub, mkConst ``Tp0.nat, mkConst ``Tp0.nat,
      mkConst ``Tp0.nat, args[args.size - 2]!, args[args.size - 1]!)
    else if fn == some ``HMul.hMul then some (``Bin.mul, mkConst ``Tp0.nat, mkConst ``Tp0.nat,
      mkConst ``Tp0.nat, args[args.size - 2]!, args[args.size - 1]!)
    else if fn == some ``HAdd.hAdd then some (``Bin.add, mkConst ``Tp0.nat, mkConst ``Tp0.nat,
      mkConst ``Tp0.nat, args[args.size - 2]!, args[args.size - 1]!)
    else if fn == some ``HSub.hSub then some (``Bin.sub, mkConst ``Tp0.nat, mkConst ``Tp0.nat,
      mkConst ``Tp0.nat, args[args.size - 2]!, args[args.size - 1]!)
    else if fn == some ``BEq.beq then some (``Bin.eq, mkConst ``Tp0.nat, mkConst ``Tp0.nat,
      mkConst ``Tp0.bool, args[args.size - 2]!, args[args.size - 1]!)
    else none
  if let some (opName, leftTp, rightTp, _, left, right) := bin? then
    return ← reifyGenericValue H V r leftTp left atoms fun leftCode =>
      reifyGenericValue H V r rightTp right atoms fun rightCode => do
        let resultCodeType := mkApp V (← mkAppM ``Tp.base #[tp])
        withLocalDeclD `result resultCodeType fun resultCode => do
          let tail ← k resultCode
          let cont ← mkLambdaFVars #[resultCode] tail
          mkAppOptM ``Expr.bin #[some H, some V, some r, none, none, none, none,
            some (mkConst opName), some leftCode, some rightCode, some cont]
  if fn == some ``Decidable.decide then
    let proposition := args[args.size - 2]!
    let pfn := proposition.getAppFn.constName?
    let pargs := proposition.getAppArgs
    let opName? := if pfn == some ``LE.le then some ``Bin.le
      else if pfn == some ``LT.lt then some ``Bin.lt else none
    if let some opName := opName? then
      let left := pargs[pargs.size - 2]!
      let right := pargs[pargs.size - 1]!
      return ← reifyGenericValue H V r (mkConst ``Tp0.nat) left atoms fun leftCode =>
        reifyGenericValue H V r (mkConst ``Tp0.nat) right atoms fun rightCode => do
          let resultCodeType := mkApp V (mkConst ``Tp.bool)
          withLocalDeclD `result resultCodeType fun resultCode => do
            let tail ← k resultCode
            let cont ← mkLambdaFVars #[resultCode] tail
            mkAppOptM ``Expr.bin #[some H, some V, some r, none, none, none, none,
              some (mkConst opName), some leftCode, some rightCode, some cont]
  throwError "reflect%: cannot reify semantic value into generic PHOAS{indentExpr value}"

private partial def genericExpr (H V : Lean.Expr) (semantic : Lean.Expr)
    (atoms : Array GenericAtom := #[]) : MetaM Lean.Expr := do
  let semantic ← whnf semantic
  let fn := semantic.getAppFn.constName?
  let args := semantic.getAppArgs
  if fn == some ``Expr.source then
    let r := args[2]!
    let α := args[3]!
    let range := args[4]!
    let body ← genericExpr H V args[5]! atoms
    return ← mkAppOptM ``Expr.source
      #[some H, some V, some r, some α, some range, some body]
  if fn == some ``Expr.ret then
    let r := args[2]!
    let α := args[3]!
    let value := args[4]!
    let .app (.const ``Tp.base _) tp := α
      | if let some code := genericAtom? atoms value then
          return ← mkAppOptM ``Expr.ret #[some H, some V, some r, some α, some code]
        else throwError "reflect%: generic return at a function type is not an atom"
    return ← reifyGenericValue H V r tp value atoms fun code =>
      mkAppOptM ``Expr.ret #[some H, some V, some r, some α, some code]
  if fn == some ``Expr.op then
    let r := args[2]!
    let α := args[3]!
    let op := args[4]!
    let input := args[5]!
    let blocks := args[6]!
    let cont := args[7]!
    let inputTp ← mkAppM ``Signature.input #[H, op]
    return ← reifyGenericValue H V r inputTp input atoms fun inputCode => do
      let branchType ← mkAppM ``Signature.branch #[H, op]
      let genericBlocks ← if ← isDefEq branchType (Lean.mkConst ``Empty) then
        withLocalDeclD `branch branchType fun branch => do
          let branchInputCode ← mkAppM ``Signature.branchInput #[H, op, branch]
          let genericInputTp := mkApp V (← mkAppM ``Tp.base #[branchInputCode])
          withLocalDeclD `input genericInputTp fun genericInput => do
            let resultCode ← mkAppM ``Signature.branchOutput #[H, op, branch]
            let resultType ← mkAppM ``Expr
              #[H, V, r, ← mkAppM ``Tp.base #[resultCode]]
            let impossible ← mkAppOptM ``Empty.elim #[some resultType, some branch]
            mkLambdaFVars #[branch, genericInput] impossible
      else withLocalDeclD `branch branchType fun branch => do
          let semanticInputTp ← mkAppM ``Tp0.denote
            #[← mkAppM ``Signature.branchInput #[H, op, branch]]
          let genericInputTp := mkApp V
            (← mkAppM ``Tp.base #[← mkAppM ``Signature.branchInput #[H, op, branch]])
          withLocalDeclD `semanticInput semanticInputTp fun semanticInput =>
            withLocalDeclD `input genericInputTp fun genericInput => do
              let body ← genericExpr H V (mkAppN blocks #[branch, semanticInput])
                (atoms.push { semantic := semanticInput, code := genericInput })
              mkLambdaFVars #[branch, genericInput] body
      let semanticOutputTp ← mkAppM ``Tp0.denote #[← mkAppM ``Signature.output #[H, op]]
      let genericOutputTp := mkApp V
        (← mkAppM ``Tp.base #[← mkAppM ``Signature.output #[H, op]])
      let genericCont ← withLocalDeclD `semanticOutput semanticOutputTp fun semanticOutput =>
        withLocalDeclD `output genericOutputTp fun output => do
          let body ← genericExpr H V (mkApp cont semanticOutput)
            (atoms.push { semantic := semanticOutput, code := output })
          mkLambdaFVars #[output] body
      return ← mkAppOptM ``Expr.op #[some H, some V, some r, some α, some op,
        some inputCode, some genericBlocks, some genericCont]
  if fn == some ``Expr.lam then
    let r := args[2]!
    let α := args[3]!
    let a := args[4]!
    let b := args[5]!
    let body := args[6]!
    let cont := args[7]!
    let semanticArgTp ← mkAppM ``Tp.denote
      #[mkApp (Lean.mkConst ``ITree2.CompE [Level.zero, Level.zero])
        (← mkAppM ``Signature.spec #[H]), a]
    let genericArgTp := mkApp V a
    let genericBody ← withLocalDeclD `semanticArg semanticArgTp fun semanticArg =>
      withLocalDeclD `arg genericArgTp fun arg => do
        let code ← genericExpr H V (mkApp body semanticArg)
          (atoms.push { semantic := semanticArg, code := arg })
        mkLambdaFVars #[arg] code
    let semanticFnTp ← inferType (← withLocalDeclD `x semanticArgTp fun x => do
      mkLambdaFVars #[x] (← mkAppM ``Expr.denote #[mkApp body x]))
    let genericFnTp := mkApp V (← mkAppM ``Tp.fn #[a, b])
    let genericCont ← withLocalDeclD `semanticFn semanticFnTp fun semanticFn =>
      withLocalDeclD `fn genericFnTp fun genericFn => do
        let code ← genericExpr H V (mkApp cont semanticFn)
          (atoms.push { semantic := semanticFn, code := genericFn })
        mkLambdaFVars #[genericFn] code
    return ← mkAppOptM ``Expr.lam #[some H, some V, some r, some α, some a, some b,
      some genericBody, some genericCont]
  if fn == some ``Expr.app then
    let r := args[2]!
    let α := args[3]!
    let a := args[4]!
    let b := args[5]!
    let f := args[6]!
    let x := args[7]!
    let cont := args[8]!
    let some genericF := genericAtom? atoms f
      | throwError "reflect%: generic function application has an unbound function"
    let aReduced ← whnf a
    let .app (.const ``Tp.base _) inputTp := aReduced
      | throwError "reflect%: generic application currently requires a first-order argument"
    return ← reifyGenericValue H V r inputTp x atoms fun genericX => do
      let semanticResultTp ← mkAppM ``Tp.denote
        #[mkApp (Lean.mkConst ``ITree2.CompE [Level.zero, Level.zero])
          (← mkAppM ``Signature.spec #[H]), b]
      let genericResultTp := mkApp V b
      let genericCont ← withLocalDeclD `semanticResult semanticResultTp fun semanticResult =>
        withLocalDeclD `result genericResultTp fun result => do
          let code ← genericExpr H V (mkApp cont semanticResult)
            (atoms.push { semantic := semanticResult, code := result })
          mkLambdaFVars #[result] code
      mkAppOptM ``Expr.app #[some H, some V, some r, some α, some a, some b,
        some genericF, some genericX, some genericCont]
  if fn == some ``Expr.ite then
    let r := args[2]!
    let α := args[3]!
    let β := args[4]!
    let condition := args[5]!
    let thenBranch := args[6]!
    let elseBranch := args[7]!
    let cont := args[8]!
    return ← reifyGenericValue H V r (mkConst ``Tp0.bool) condition atoms
      fun conditionCode => do
        let thenCode ← genericExpr H V thenBranch atoms
        let elseCode ← genericExpr H V elseBranch atoms
        let semanticResultTp ← mkAppM ``Tp.denote
          #[mkApp (Lean.mkConst ``ITree2.CompE [Level.zero, Level.zero])
            (← mkAppM ``Signature.spec #[H]), β]
        let genericResultTp := mkApp V β
        let genericCont ← withLocalDeclD `semanticResult semanticResultTp fun semanticResult =>
          withLocalDeclD `result genericResultTp fun result => do
            let code ← genericExpr H V (mkApp cont semanticResult)
              (atoms.push { semantic := semanticResult, code := result })
            mkLambdaFVars #[result] code
        mkAppOptM ``Expr.ite #[some H, some V, some r, some α, some β,
          some conditionCode, some thenCode, some elseCode, some genericCont]
  if fn == some ``Expr.letrec then
    let r := args[2]!
    let α := args[3]!
    let a := args[4]!
    let b := args[5]!
    let body := args[6]!
    let cont := args[7]!
    let semanticArgTp ← mkAppM ``Tp.denote
      #[mkApp (Lean.mkConst ``ITree2.CompE [Level.zero, Level.zero])
        (← mkAppM ``Signature.spec #[H]), a]
    let genericArgTp := mkApp V a
    let genericBody ← withLocalDeclD `semanticArg semanticArgTp fun semanticArg =>
      withLocalDeclD `arg genericArgTp fun arg => do
        let code ← genericExpr H V (mkApp body semanticArg)
          (atoms.push { semantic := semanticArg, code := arg })
        mkLambdaFVars #[arg] code
    let semanticBody ← withLocalDeclD `y semanticArgTp fun y => do
      mkLambdaFVars #[y] (← mkAppM ``Expr.denote #[mkApp body y])
    let semanticFn ← mkAppM ``ITree2.CompE.mrec #[semanticBody]
    let semanticFnTp ← inferType semanticFn
    let genericFnTp := mkApp V (← mkAppM ``Tp.fn #[a, b])
    let genericCont ← withLocalDeclD `semanticFn semanticFnTp fun semanticFn =>
      withLocalDeclD `fn genericFnTp fun genericFn => do
        let code ← genericExpr H V (mkApp cont semanticFn)
          (atoms.push { semantic := semanticFn, code := genericFn })
        mkLambdaFVars #[genericFn] code
    return ← mkAppOptM ``Expr.letrec #[some H, some V, some r, some α, some a, some b,
      some genericBody, some genericCont]
  if fn == some ``Expr.selfCall then
    let α := args[2]!
    let a := args[3]!
    let b := args[4]!
    let input := args[5]!
    let cont := args[6]!
    let aReduced ← whnf a
    let .app (.const ``Tp.base _) inputTp := aReduced
      | throwError "reflect%: recursive helper argument is not first-order"
    let pairTp ← mkAppM ``Prod #[mkConst ``Tp, mkConst ``Tp]
    let pair ← mkAppM ``Prod.mk #[a, b]
    let recursionSlot ← mkAppOptM ``Option.some #[some pairTp, some pair]
    return ← reifyGenericValue H V recursionSlot
      inputTp input atoms fun genericInput => do
        let semanticResultTp ← mkAppM ``Tp.denote
          #[mkApp (Lean.mkConst ``ITree2.CompE [Level.zero, Level.zero])
            (← mkAppM ``Signature.spec #[H]), b]
        let genericResultTp := mkApp V b
        let genericCont ← withLocalDeclD `semanticResult semanticResultTp fun semanticResult =>
          withLocalDeclD `result genericResultTp fun result => do
            let code ← genericExpr H V (mkApp cont semanticResult)
              (atoms.push { semantic := semanticResult, code := result })
            mkLambdaFVars #[result] code
        mkAppOptM ``Expr.selfCall #[some H, some V, some α, some a, some b,
          some genericInput, some genericCont]
  if fn == some ``Empty.rec || fn == some ``Empty.elim then
    let branch := args[args.size - 1]!
    let type ← whnf (← inferType semantic)
    unless type.isAppOfArity ``Expr 4 do
      throwError "reflect%: malformed empty AST branch{indentExpr type}"
    let r := type.getArg! 2
    let α := type.getArg! 3
    let genericType ← mkAppM ``Expr #[H, V, r, α]
    return ← mkAppOptM ``Empty.elim #[some genericType, some branch]
  throwError "reflect%: cannot translate semantic AST node to generic PHOAS{indentExpr semantic}"

private def closeEmission (plan : Discovery) (goal : EmitGoal) (source : Lean.Expr)
    (emission : Emission) : MetaM Lean.Expr := do
  let VType := .forallE `t (mkConst ``Tp) (mkSort 1) .default
  let closed ← withLocalDeclD `V VType fun V => do
    mkLambdaFVars #[V] (← genericExpr plan.targetSig V emission.code)
  let targetSpec ← mkAppM ``Signature.spec #[plan.targetSig]
  let semanticM := mkApp (Lean.mkConst ``ITree2.CompE [Level.zero, Level.zero]) targetSpec
  let semanticV ← mkAppM ``Tp.denote #[semanticM]
  let genericSemantic := mkApp closed semanticV
  let witness ← mkAppM ``Sigma.snd #[emission.reflection]
  let sound ← mkAppM ``ReflectionWitnessAt.sound #[witness, mkConst ``True.intro]
  let wanted ← mkAppM ``ITree2.CompE.Eutt #[plan.compat, goal.relates,
    ← mkAppM ``Freek.toITree #[source], ← mkAppM ``Expr.denote #[genericSemantic]]
  let sound ← mkExpectedTypeHint sound wanted
  let reflectedType ← mkAppOptM ``Reflected
    #[some plan.sourceSig, some plan.targetSig, some plan.compat, some goal.targetTp,
      some goal.sourceType, some goal.relates, some source]
  let reflectedType ← whnf reflectedType
  unless reflectedType.isAppOfArity ``Subtype 2 do
    throwError "reflect%: internal: malformed closed reflection type"
  mkAppOptM ``Subtype.mk #[some (reflectedType.getArg! 0), some (reflectedType.getArg! 1),
    some closed, some sound]

private def reflectTerm (source : Lean.Expr) (range? : Option Lean.Expr := none) : TermElabM Lean.Expr := do
  let plan ← discover source
  let targetTp ← mkAppM ``Tp.base #[← mkAppM ``ReprSpec.code #[plan.resultRepr]]
  let relates ← mkAppM ``ReprSpec.relates #[plan.resultRepr]
  let emission ← emitProgram plan {
    sourceType := plan.resultType
    targetTp := targetTp
    relates := relates
  } source
  let emission ← match source.getAppFn.constName? with
    | some decl => match ← declarationSourceRange? decl with
      | some range => annotateEmission range emission
      | none => pure emission
    | none => pure emission
  let emission ← match range? with
    | some range => annotateEmission range emission
    | none => pure emission
  return emission.reflection

private def reflectClosedTerm (source : Lean.Expr) (range? : Option Lean.Expr := none) : TermElabM Lean.Expr := do
  let plan ← discover source
  let targetTp ← mkAppM ``Tp.base #[← mkAppM ``ReprSpec.code #[plan.resultRepr]]
  let relates ← mkAppM ``ReprSpec.relates #[plan.resultRepr]
  let goal : EmitGoal := {
    sourceType := plan.resultType
    targetTp := targetTp
    relates := relates
  }
  let emission ← emitProgram plan goal source
  let emission ← match source.getAppFn.constName? with
    | some decl => match ← declarationSourceRange? decl with
      | some range => annotateEmission range emission
      | none => pure emission
    | none => pure emission
  let emission ← match range? with
    | some range => annotateEmission range emission
    | none => pure emission
  closeEmission plan goal source emission

/-- Concrete semantic reflection, retained as a debugging surface for smart constructors. -/
elab "reflect_semantic% " t:term : term => do
  let source ← elabTermAndSynthesize t none
  reflectTerm (← instantiateMVars source) (← syntaxSourceRange? t)

/-- AST2 `reflect%`: closed PHOAS code bundled with its relational soundness theorem. -/
elab "reflect% " t:term : term => do
  let source ← elabTermAndSynthesize t none
  reflectClosedTerm (← instantiateMVars source) (← syntaxSourceRange? t)

elab doc:(Lean.Parser.Command.docComment)? "reflect_def " nm:ident " := " t:term : command =>
  Command.liftTermElabM do
    let source ← elabTermAndSynthesize t none
    let reflected ← reflectClosedTerm (← instantiateMVars source) (← syntaxSourceRange? t)
    synthesizeSyntheticMVarsNoPostponing
    let reflected ← instantiateMVars reflected
    let code ← whnf (← mkAppM ``Subtype.val #[reflected])
    let sound ← whnf (← mkAppM ``Subtype.property #[reflected])
    let codeName := (← getCurrNamespace) ++ nm.getId
    let soundName := codeName.appendAfter "_sound"
    addAndCompile (.defnDecl {
      name := codeName
      levelParams := []
      type := ← inferType code
      value := code
      hints := .abbrev
      safety := .safe
    })
    let soundType := (← inferType sound).replace fun e =>
      if e == code then some (mkConst codeName) else none
    addDecl (.thmDecl {
      name := soundName
      levelParams := []
      type := soundType
      value := ← mkExpectedTypeHint sound soundType
    })
    if let some d := doc then
      addDocStringCore codeName (← Lean.getDocStringText d)
    Term.addTermInfo' nm (mkConst codeName) (isBinder := true)

end Reflector
end Ast2
end Freigen
