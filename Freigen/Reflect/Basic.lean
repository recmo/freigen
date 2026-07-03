import Freigen.Ast.Basic
import Freigen.Free
import Freigen.ITree.Eutt
import Freigen.Reflect.Sound
/-! ## The `reflect%` reflector

Reflects a `Free Op SOp α` program (which may call top-level helper functions, recursive or not)
into a `Prog`: pure computation is A-normalised into `un`/`bin`/`lit`; effects/scoped blocks pass
through; **calls to helper functions — `Free`-valued *or pure* — become `call` nodes,
monomorphised and spilled as `def_`s** (definitions are *kept folded*; helper bodies may call
other helpers, spilled in dependency order — a two-pass discovery/build).  A reifiable pure `let`
keeps its sharing.

**Recursion is not special.**  A structural `0`/`succ` recursion (at any `Nat` argument) spills
as a `Prog.rec_` at the tupled state of its value arguments — hypothesis arguments erased,
function/type arguments monomorphised — with `mrec` adequacy (`recSound`, at the measure = the
recursion component) proved per monomorphisation in the `elabRecKits` stage between discovery and
build.  A *recursive program* is just the degenerate case: its definition is kept folded and
`main` becomes the call.  Closed values containing a (user-module) recursion bypass
`Code.lit`-folding — a recursion reflects structurally, never evaluates.

**One walk, two modes.**  A single walk (`Env.walk`/`Env.atom`) serves both jobs, selected by
`Env.pf`:

* **Abstract mode** (`pf := false`): build the `Code` against opaque `F`/`V` — the parametric `g`
  and (in `tryCall`) the spilled helper bodies.  A closed value must be bound via `Code.lit` (a host
  value is not a `V α`).  No proofs are produced.
* **Proof mode** (`pf := true`, at `V := Tp.denote`, `F := KC Op`): re-walk the source and *also*
  return, at every node, the equation of the invariant

  ```
  denote code = bind (ofFree e) Kf        -- (★)   Kf = the reflected continuation's denotation
  ```

  assembled from the sub-terms' equations by that node's congruence lemma (`sc_op`, `sc_bind`, …).
  Every non-`get`/`set` atom step is *definitional* (`denote (Code.bin …) = denote (k …)` is `rfl`),
  so a proof-erased get/set/cast contributes the only real step: `sc_vget … h` = `dif_pos h`, the
  **source's own** in-bounds proof taken straight from the term — no `simp`, no decidability, sound
  for a symbolic index at any depth.  A closed value is fed *directly* (no `Code.lit` node —
  denotationally identical, and a literal index/collection keeps the source proof fitting).  The
  proof-mode code is definitionally the concrete specialisation of the abstract `g`, so the
  top-level (★) (`k = ret`, `Kf = ret`) *is* `denoteProg (g KC Tp.denote) ⟨args⟩ = ofFree (foo args)`.

  Past a recursive call the invariant weakens to `≈` — `mrec` adequacy inserts `tau`s — and the
  proof continues in eutt mode (`Pf.isEq`, the `sc_*E` twins): equality where possible, weak
  bisimulation where recursion forces it.

Supporting a new source form is therefore **one** arm in `Env.atom` (or `Env.walk`) calling **one**
emitter — both modes share the code path, so they cannot drift apart. -/

namespace Freigen
open Lean Lean.Meta Lean.Elab.Term

/-- Reify a Lean type into a `Tp` (matching the head *before* `whnf`, so `ZMod n` stays `ZMod n`). -/
partial def reifyTp (T : Expr) : MetaM (Option Expr) := do
  match_expr T with
  | Tp.denote _ t => return some t
  | Bool     => return some (.const ``Tp.bool [])
  | Nat      => return some (.const ``Tp.nat [])
  | ZMod n   => return some (mkApp (.const ``Tp.zmod []) n)
  | PUnit    => return some (.const ``Tp.unit [])
  | Unit     => return some (.const ``Tp.unit [])
  | Prod A B =>
      let some a ← reifyTp A | return none
      let some b ← reifyTp B | return none
      return some (mkApp2 (.const ``Tp.prod []) a b)
  | Vector A n =>
      let some a ← reifyTp A | return none
      return some (mkApp2 (.const ``Tp.vec []) a n)
  | Array A =>
      let some a ← reifyTp A | return none
      return some (mkApp (.const ``Tp.array []) a)
  | Sum A B =>
      let some a ← reifyTp A | return none
      let some b ← reifyTp B | return none
      return some (mkApp2 (.const ``Tp.sum []) a b)
  | Fin n => return some (mkApp (.const ``Tp.fin []) n)
  | _ =>
      if let .forallE _ A B _ := T then
        if B.hasLooseBVars then return none
        let some a ← reifyTp A | return none
        -- a Kleisli arrow (the denotation of `.fn`) reifies through its result type
        match_expr B with
        | ITree.CompE _ _ R =>
            let some b ← reifyTp R | return none
            return some (mkApp2 (.const ``Tp.fn []) a b)
        | _ =>
          let some b ← reifyTp B | return none
          return some (mkApp2 (.const ``Tp.fn []) a b)
      else match ← unfoldDefinition? T with
        | some T' => reifyTp T'
        | none    => return none

/-- Reify a Lean type into a `Tp`, aborting if unsupported. -/
def reifyTpOrThrow (T : Expr) : MetaM Expr := do
  match ← reifyTp T with
  | some tp => return tp
  | none    => throwError "reflect%: type not expressible as a `Tp`:{indentExpr T}"

/-- `Bin.add`/`Bin.addZ` picking on the (reified) arithmetic result type. -/
def arithOp (natC zmodC : Name) (resTy : Expr) : MetaM (Expr × Expr) := do
  let cTp ← reifyTpOrThrow resTy
  match_expr cTp with
  | Tp.nat    => return (.const natC [], cTp)
  | Tp.zmod n => return (mkApp (.const zmodC []) n, cTp)
  | _         => throwError "reflect%: unsupported arithmetic result type{indentExpr cTp}"

/-- `Un.fst`/`Un.snd` for a value of product type. -/
def prodUn (ctor : Name) (p : Expr) : MetaM Expr := do
  match_expr ← reifyTpOrThrow (← inferType p) with
  | Tp.prod a b => return mkApp2 (.const ctor []) a b
  | _           => throwError "reflect%: projection applied to a non-product{indentExpr p}"

/-- Project the `j`-th element out of an `HList` atom (`head ∘ tailʲ`). -/
def projHList (hargs : Expr) (j : Nat) : MetaM Expr := do
  let mut h := hargs
  for _ in [0:j] do h ← mkAppM ``HList.tail #[h]
  mkAppM ``HList.head #[h]

/-- The site-independent synthesis of one **monomorphised recursive pure helper** — a structural
    `0`/`succ` recursion at some `Nat` argument, spilled as a `Prog.rec_` at the tupled state
    `σ := (value args)` with hypothesis arguments *erased* (their occurrences are eliminated:
    self-calls drop them, remaining proof subterms are re-synthesized at the monomorphised
    bounds) and function/type arguments *baked in* (monomorphisation — closures cannot spill:
    the `def_`/`rec_` telescope is closed). -/
structure RecData where
  /-- Positions (in the full argument telescope) of the state components (source order). -/
  statePos : Array Nat
  /-- Positions of the erased hypothesis arguments (source order). -/
  hypPos   : Array Nat
  /-- Index of the structural-recursion component *among the state components*. -/
  recIdx   : Nat
  /-- The first `fnStateCount` state components are function-valued — **invariant** through the
      recursion (every self-call passes them unchanged); the adequacy is relativized to states
      where they are embeddings of fixed pure functions. -/
  fnStateCount : Nat := 0
  /-- Host (pure-function) types of the fn state components. -/
  fnHostTys : Array Expr := #[]
  /-- Host types / reified `Tp`s of the state components. -/
  stateTys : Array Expr
  stateTps : Array Expr
  /-- The tupled state: host type and reified `Tp`. -/
  σTy : Expr
  σTp : Expr
  /-- The helper's full host result type (`Free Op SOp X` for an effectful recursion, the value
      type for a pure one). -/
  ρTy : Expr
  /-- The result *value* host type (`X` above; `= ρTy` for a pure helper) — the `ρ` of
      `CallOp Op σ ρ` and of the `rec_`'s result. -/
  ρValTy : Expr
  /-- The CallOp-lifted **totalized** body `cb : σ → Free (CallOp Op σ ρ) SOp ρ`
      (`bif i == 0 then pure base else …call…`). -/
  cb : Expr
  /-- The totalized `Nat.rec` twin `goT : σ → ρ` (agrees with the source wherever the source's
      hypotheses hold — the `bridge`). -/
  goT : Expr
  /-- The measure `μ : σ → Nat` (the recursion component's projection). -/
  μ : Expr
  deriving Inhabited

/-- A call-site analysis of a **spillable helper** — a `Free`-valued function or a *pure* function
    of reifiable signature (definitions are **kept folded**: both spill as `def_`s).  Carries
    everything needed to *rebuild* the helper's body at fresh binders (bodies are rebuilt on the
    resolution pass, since they may themselves call earlier-spilled helpers). -/
structure CallSig where
  cName     : Name
  cValInst  : Expr
  fArgs     : Array Expr
  valuePos  : Array Nat
  valueArgs : List Expr
  /-- Host types of the value arguments (fresh-binder types for body rebuilds). -/
  argTys    : Array Expr
  argTps    : Array Expr
  asList    : Expr
  retTp     : Expr
  /-- A pure helper (result reifies to a `Tp` directly) vs a `Free` computation. -/
  isPure    : Bool
  /-- The **monomorphisation key**: the non-value arguments baked into the spilled body (types,
      instances, demoted function values).  Two sites share a spill only if these are defeq. -/
  monoArgs  : Array Expr := #[]
  /-- Indices *into the value-argument list* that are function-typed — genuine first-class
      parameters of the spilled definition. -/
  fnArgPos  : Array Nat := #[]
  /-- This signature's function arguments were **demoted** to monomorphisation (the body reaches
      a recursion that must specialize over them); a nullary spill is then still allowed. -/
  fnDemoted : Bool := false
  /-- A recursive helper's synthesis (`none` for plain helpers). -/
  rec?      : Option RecData := none
  deriving Inhabited

/-- The proof-mode helper cache entry: a helper's concrete subroutine `cf` and its parametric
    equation `bodyProof : ∀ hargs, cf hargs = ofFree …` (Free) / `… = ret …` (pure), built **once**
    per monomorphised signature and reused at every call site. -/
structure PfDefEntry where
  name      : Name
  asList    : Expr
  retTp     : Expr
  cf        : Expr
  bodyProof : Expr
  /-- `bodyProof`'s mode: `∀ args, cf args = …` (`true`) vs `∀ …, cf args ≈ …` (`false` — a
      recursive helper, whose adequacy is only up to taus). -/
  bodyProofEq : Bool := true
  /-- The monomorphisation key (mirrors `CallSig.monoArgs`). -/
  key : Array Expr := #[]
  deriving Inhabited

/-- The reflection environment: the `Op`/`SOp`/`F`/`V` we build against, a substitution from
    continuation-bound host placeholders to object atoms, the running spill cache (in dependency
    post-order — callees precede callers, as `Prog.def_` scoping requires), the in-flight set (for
    cycle detection), on the build pass the resolved `F`-names, and the walk **mode** (`pf`). -/
structure Env where
  /-- The DSL signature `X : TpF → TpF → Type`. -/
  Op : Expr
  /-- The code-level op vocabulary (`OpT X` for ordinary code; `CallOp (OpT X) σ ρ` inside a
      `rec_` body). -/
  Opc : Expr
  /-- Wrap a lifted DSL op (`OpT.mk o : OpT X I.tp R.tp`, given the `Tp` exprs) into the
      vocabulary — identity normally, `CallOp.base` inside a `rec_` body. -/
  opWrap : Expr → Expr → Expr → Expr
  /-- Inside a `rec_` body: proof steps use the `sc_*C` lemma set (`scn`), which carries two
      extra implicit `Tp` arguments (`scx`). -/
  recMode : Bool := false
  /-- Inside a `rec_` body: the recursion's state/result `Tp` exprs. -/
  recTps : Option (Expr × Expr) := none
  SOp : Expr
  F : Expr
  V : Expr
  subst : List (FVarId × Expr)
  defs : IO.Ref (Array CallSig)
  /-- Proof-mode helper cache (`cf` + body equation per monomorphised signature). -/
  pfDefs : IO.Ref (Array PfDefEntry)
  /-- Helpers whose bodies are currently being walked — a name re-entering is a recursive helper,
      which cannot spill (no `μ`); reported as an error. -/
  inFlight : IO.Ref (Array Name)
  /-- No `def_` telescope is available (the recursion arm): helper calls inline instead of
      spilling. -/
  noSpill : Bool := false
  resolved : Option (Array (CallSig × Expr)) := none
  /-- **Proof mode**: the walk runs at the concrete representation (`V := Tp.denote`, `F := KC Op`)
      and every step also returns its (★)-equation. -/
  pf : Bool := false
  /-- Pending arithmetic obligations from totalizing recursive helpers (fresh mvars, discharged
      by tactic in a `TermElabM` stage after the discovery pass — the walk is `MetaM`). -/
  pending : IO.Ref (Array MVarId)
  /-- Name-level "spillable structural recursion" verdicts, cached per run. -/
  recVerdicts : IO.Ref (List (Name × Bool))
  /-- Reflected `rec_` bodies, one per monomorphised recursive helper — shared between the
      abstract build and proof mode, so the two are *definitionally* the same term. -/
  recBodies : IO.Ref (Array (CallSig × Expr))

/-- The (★)-lemma name for the current walk mode (`sc_*` vs the rec-body `sc_*C` set). -/
def Env.scn (env : Env) (n : Name) : Name :=
  if env.recMode then n.appendAfter "C" else n

/-- The extra arguments of the rec-body lemma set (the recursion's `σT ρT`). -/
def Env.scx (env : Env) : Array (Option Expr) :=
  match env.recMode, env.recTps with
  | true, some (σTp, ρTp) => #[some σTp, some ρTp]
  | _, _ => #[]

/-- Apply a (★)-step lemma in the current mode: base `sc_*` set or the rec-body `sc_*C` set
    (which carries two extra inferable implicits). -/
def Env.mkSc (env : Env) (n : Name) (rest : Array (Option Expr)) : MetaM Expr :=
  mkAppOptM (env.scn n) (#[some env.Op, some env.SOp] ++ env.scx ++ rest)

/-- A proof-mode step: the proof term, tagged with its **mode** — `isEq = true` is the equality
    invariant (★); `false` is the weakened eutt invariant (★≈), entered when the step passed
    through a recursive helper call (`mrec` adequacy is `≈`, not `=`) and infectious upward. -/
structure Pf where
  e : Expr
  isEq : Bool
  deriving Inhabited

/-- One step of the walk: the built `Code`, and — in proof mode — its (★)/(★≈)-step. -/
abbrev CodePf := Expr × Option Pf

/-- Lift to the eutt invariant (`Eutt.of_eq` for an `Eq`-mode proof). -/
def Pf.toEutt (p : Pf) : MetaM Expr :=
  if p.isEq then mkAppM ``ITree.Eutt.of_eq #[p.e] else pure p.e

/-- Lift a ∀/λ-abstracted pointwise proof to pointwise eutt (`fun r … => Eutt.of_eq (h r …)`). -/
def Pf.toEuttPointwise (p : Pf) : MetaM Expr := do
  if !p.isEq then return p.e
  forallTelescope (← inferType p.e) fun rs _ => do
    mkLambdaFVars rs (← mkAppM ``ITree.Eutt.of_eq #[mkAppN p.e rs])

/-- Bind a host literal `a : αTp.denote` as an atom (abstract mode only — proof mode feeds closed
    values directly). -/
def Env.mkLitBind (env : Env) (a αTp : Expr) (k : Expr → MetaM CodePf) : MetaM CodePf := do
  withLocalDeclD `v (mkApp env.V αTp) fun vx => do
    let (kcode, _) ← k vx
    let lam ← mkLambdaFVars #[vx] kcode
    return (← mkAppOptM ``Code.lit #[env.Op, env.Opc, env.SOp, env.F, env.V, none, αTp, a, lam], none)

/-- Build the argument tuple `HList V [tps]` from already-reflected atoms. -/
def Env.mkArgHList (env : Env) (atoms : List Expr) : MetaM Expr := do
  let mut h ← mkAppOptM ``HList.nil #[none, env.V]
  for a in atoms.reverse do h ← mkAppM ``HList.cons #[a, h]
  pure h

/-- Extract the elements of a `List` literal (`e₀ :: … :: []`). -/
partial def listLitElems : Expr → Option (List Expr)
  | e => match e.getAppFnArgs with
    | (``List.nil, _)            => some []
    | (``List.cons, #[_, x, xs]) => (listLitElems xs).map (x :: ·)
    | _                          => none

/-- Extract elements of a `List`/`Array` literal (`#[…]` = `List.toArray […]`). -/
def seqLitElems (e : Expr) : Option (List Expr) :=
  match e.getAppFnArgs with
  | (``List.toArray, #[_, lst]) => listLitElems lst
  | _                           => listLitElems e

/-- Build a `Vector (V a) n` atom-vector from element atoms (`⟨#[atoms], rfl⟩`). -/
def mkVecOfAtoms (V aTp nExpr : Expr) (atoms : List Expr) : MetaM Expr := do
  let elemTy := mkApp V aTp
  let arrExpr ← mkAppM ``List.toArray #[← mkListLit elemTy atoms]
  let proof ← mkExpectedTypeHint (← mkEqRefl nExpr) (← mkEq (← mkAppM ``Array.size #[arrExpr]) nExpr)
  mkAppOptM ``Vector.mk #[elemTy, nExpr, arrExpr, proof]

/-- Normalise a collection index to `(Nat-index, optional in-bounds proof)`: a `Fin n` index becomes
    `i.val` with `i.isLt`; a `Nat` index passes through unchanged. -/
def finIndexToNat (i : Expr) : MetaM (Expr × Option Expr) := do
  match_expr ← whnf (← inferType i) with
  | Fin _ => return (← mkAppM ``Fin.val #[i], some (← mkAppM ``Fin.isLt #[i]))
  | _     => return (i, none)

/-- Emit a `call cf args k`, binding the result atom for the continuation. -/
def Env.emitCall (env : Env) (cf asList retTp hl : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  let contLam ← withLocalDeclD `r (mkApp env.V retTp) fun vr => do mkLambdaFVars #[vr] (← k vr)
  mkAppOptM ``Code.call #[env.Op, env.Opc, env.SOp, env.F, env.V, none, asList, retTp, cf, hl, contLam]

/-- `denote code` as an `Expr`. -/
private def denoteE (c : Expr) : MetaM Expr := mkAppM ``denote #[c]

/-- `denote code` in the current walk mode: the base `denote`, or `denoteC` at the call-extended
    events inside a `rec_` body. -/
def Env.denE (env : Env) (c : Expr) : MetaM Expr := do
  if env.recMode then
    let some (σTp, ρTp) := env.recTps
      | throwError "reflect%: internal: rec walk without state types"
    let denoteV := mkApp (Lean.mkConst ``Tp.denote []) env.Op
    mkAppOptM ``denoteC
      #[env.Op, env.Opc, env.SOp, mkApp denoteV σTp, mkApp denoteV ρTp,
        ← mkAppM ``Inj.withCall #[← mkAppM ``injD #[env.Op], σTp, ρTp], none, c]
  else
    mkAppM ``denote #[c]

/-- A `ret` continuation with the result `Tp` given **explicitly** — needed at `V := Tp.denote`,
    where `α` cannot be recovered from a raw-typed atom by unifying `Tp.denote ?α`. -/
def Env.mkRetT (env : Env) (resTp : Expr) : Expr → MetaM Expr := fun atom =>
  mkAppOptM ``Code.ret #[env.Op, env.Opc, env.SOp, env.F, env.V, resTp, atom]

/-- `Kf := fun (r : X) => denote (k r)` — the reflected continuation's denotation. -/
private def mkKf (env : Env) (X : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `r X fun r => do mkLambdaFVars #[r] (← env.denE (← k r))

/-- Lift a code-only continuation to a `CodePf` one; in proof mode its step is `rfl`
    (`denote (k atom) = denote (k atom)`). -/
def Env.liftK (env : Env) (k : Expr → MetaM Expr) : Expr → MetaM CodePf := fun atom => do
  let c ← k atom
  if env.pf then return (c, some ⟨← mkEqRefl (← env.denE c), true⟩)
  else return (c, none)

/-- Bind the host-side placeholder for a continuation result: in proof mode the atom variable *is*
    the host value (`V := Tp.denote`), so it is reused; in abstract mode `V` is opaque, so a separate
    host placeholder of type `hostTy` is bound (to be mapped to the atom via `subst`). -/
def Env.withHostVar {α} (env : Env) (hostTy vx : Expr) (f : Expr → MetaM α) : MetaM α :=
  if env.pf then f vx else withLocalDeclD `h hostTy fun hx => f hx

/-- Build `HList V [tps]` from atoms with the `Tp` indices given **explicitly** — at `V := Tp.denote`
    the index can't be recovered from a raw-typed atom. -/
private def mkArgHListT (V : Expr) : List Expr → List Expr → MetaM Expr
  | [],      []      => mkAppOptM ``HList.nil #[none, V]
  | a :: as, t :: ts => do
      let tail ← mkArgHListT V as ts
      mkAppOptM ``HList.cons #[none, V, t, ← mkListLit (.const ``Tp []) ts, a, tail]
  | _, _ => throwError "reflect%: argument/type length mismatch"

/-- The result Lean type `X` of a source `e : Free Op SOp X`. -/
private def freeResult (e : Expr) : MetaM Expr := do
  let_expr FreeE _ _ _ X := (← whnf (← inferType e)) | throwError "reflect%: not a `Free`{indentExpr e}"
  pure X

/-- `Eq.trans` tolerant of a *definitional* mismatch at the shared point: the `denote`-of-a-node steps
    are only defeq (a `Code.bin`/`vget` node reduces to its continuation), so coerce `h2`'s LHS to
    `h1`'s RHS before chaining. -/
private def eqTransD (h1 h2 : Expr) : MetaM Expr := do
  let_expr Eq _ _ b := (← inferType h1) | throwError "reflect%: eqTransD h1 not an Eq"
  let_expr Eq _ _ c := (← inferType h2) | throwError "reflect%: eqTransD h2 not an Eq"
  mkAppM ``Eq.trans #[h1, ← mkExpectedTypeHint h2 (← mkEq b c)]

/-- The RHS of an `Eq`- or `Eutt`-typed proof (`≈` notation included). -/
private def pfRhs (h : Expr) : MetaM Expr := do
  match_expr ← inferType h with
  | Eq _ _ b => pure b
  | ITree.Eutt _ _ _ _ b => pure b
  | HasEquiv.Equiv _ _ _ b => pure b
  | _ => throwError "reflect%: not an Eq/Eutt proof{indentExpr h}"

/-- The LHS, ditto. -/
private def pfLhs (h : Expr) : MetaM Expr := do
  match_expr ← inferType h with
  | Eq _ a _ => pure a
  | ITree.Eutt _ _ _ a _ => pure a
  | HasEquiv.Equiv _ _ a _ => pure a
  | _ => throwError "reflect%: not an Eq/Eutt proof{indentExpr h}"

/-- Mode-dispatching `eqTransD`: two `Eq` steps chain as equalities; any eutt step lifts the
    other (`Eutt.of_eq`) and chains by `Eutt.trans` — with the same defeq coercion at the joint. -/
def pfTransD (h1 h2 : Pf) : MetaM Pf := do
  if h1.isEq && h2.isEq then return ⟨← eqTransD h1.e h2.e, true⟩
  let e1 ← h1.toEutt
  let e2 ← h2.toEutt
  let b ← pfRhs e1
  let c ← pfRhs e2
  let e2' ← mkExpectedTypeHint e2 (← mkAppM ``ITree.Eutt #[b, c])
  return ⟨← mkAppM ``ITree.Eutt.trans #[e1, e2'], false⟩

/-- Classify `e` as a call to a spillable top-level helper: a constant with a value, whose result
    is a `Free` computation (but not an effect/scoped smart-constructor — those inline) **or** a
    plain reifiable `Tp` (a pure helper), with at least one value argument, all value arguments
    reifying to `Tp`s.  `none` means "not a call — keep unfolding". -/
def analyzeCall (e : Expr) : MetaM (Option CallSig) := do
  let fn := e.getAppFn
  let some cName := fn.constName? | return none
  let some ci := (← getEnv).find? cName | return none
  let some cVal := ci.value? | return none
  let fArgs := e.getAppArgs
  let cValInst := cVal.instantiateLevelParams ci.levelParams fn.constLevels!
  let resTy ← inferType e
  let (retTp?, isPure) ← do
    match_expr ← whnf resTy with
    | FreeE _ _ _ R => pure (← reifyTp R, false)
    | _ => pure (← reifyTp resTy, true)     -- reify *before* whnf, so `ZMod n` stays `ZMod n`
  let some retTp := retTp? | return none
  unless isPure do
    match_expr ← whnf (cValInst.beta fArgs) with
    | FreeE.op _ _ _ _ _ _ => return none         -- effect smart-constructors (→ `op`) inline
    | FreeE.hop _ _ _ _ _ _ _ _ => return none    -- scoped constructs (→ `scope`) inline
    | _ => pure ()
  let valuePos ← forallTelescope (← inferType fn) fun xs cod => do
    let mut vps : Array Nat := #[]
    for i in [0:xs.size] do
      let mut dep := cod.containsFVar xs[i]!.fvarId!
      for j in [i+1:xs.size] do
        if (← inferType xs[j]!).containsFVar xs[i]!.fvarId! then dep := true
      unless dep do vps := vps.push i
    pure vps
  if valuePos.size == 0 then return none
  -- a *function-typed* argument is a genuine first-class parameter (a `(fn …)`-typed slot);
  -- if the body turns out to reach a recursion over it, discovery **demotes** it to
  -- monomorphisation (`CallSig.demoteFnArgs`)
  let mut vPos : Array Nat := #[]
  let mut fnArgPos : Array Nat := #[]
  let mut argTys : Array Expr := #[]
  let mut argTps : Array Expr := #[]
  for p in valuePos do
    let ty ← inferType fArgs[p]!
    let some t ← reifyTp ty | return none
    if t.isAppOf ``Tp.fn then fnArgPos := fnArgPos.push vPos.size
    vPos := vPos.push p
    argTys := argTys.push ty
    argTps := argTps.push t
  if vPos.size == 0 then return none
  let valueArgs := vPos.toList.map (fArgs[·]!)
  let monoArgs := (Array.range fArgs.size).filterMap fun j =>
    if vPos.contains j then none else some fArgs[j]!
  let asList ← mkListLit (.const ``Tp []) argTps.toList
  return some { cName, cValInst, fArgs, valuePos := vPos, valueArgs, argTys, argTps, asList,
                retTp, isPure, monoArgs, fnArgPos }

/-- Demote a signature's function-typed value arguments to monomorphisation (bake them into the
    body): used when the helper's body reaches a recursion that must specialize over them.  The
    baked values must then be program-independent. -/
def CallSig.demoteFnArgs (sig : CallSig) (env : Env) : MetaM CallSig := do
  let mut vPos : Array Nat := #[]
  let mut argTys : Array Expr := #[]
  let mut argTps : Array Expr := #[]
  let mut valueArgs : List Expr := []
  for h : i in [0:sig.valuePos.size] do
    if sig.fnArgPos.contains i then
      let v := sig.fArgs[sig.valuePos[i]!]!
      if v.hasAnyFVar (fun fid => (env.subst.lookup fid).isSome) then
        throwError "reflect%: `{sig.cName}`'s function argument reaches a recursion (which must \
                    specialize over it), but the value captures program variables{indentExpr v}"
    else
      vPos := vPos.push sig.valuePos[i]!
      argTys := argTys.push sig.argTys[i]!
      argTps := argTps.push sig.argTps[i]!
      valueArgs := valueArgs ++ [sig.fArgs[sig.valuePos[i]!]!]
  let monoArgs := (Array.range sig.fArgs.size).filterMap fun j =>
    if vPos.contains j then none else some sig.fArgs[j]!
  let asList ← mkListLit (.const ``Tp []) argTps.toList
  return { sig with valuePos := vPos, valueArgs, argTys, argTps, asList, monoArgs,
                    fnArgPos := #[], fnDemoted := true }

/-- Two spill signatures match: same helper, defeq (monomorphised) argument/result `Tp`s, and
    defeq monomorphisation keys (baked-in types/instances/function values). -/
def sigsMatch (d sig : CallSig) : MetaM Bool := do
  unless d.cName == sig.cName && d.monoArgs.size == sig.monoArgs.size do return false
  unless (← isDefEq d.asList sig.asList) && (← isDefEq d.retTp sig.retTp) do return false
  for (a, b) in d.monoArgs.zip sig.monoArgs do
    unless ← isDefEq a b do return false
  return true

/-! ## Recursive pure helpers

A **structural-recursive pure helper** (two equations, `0`/`succ` patterns on a `Nat` argument
at any position) spills as a `Prog.rec_` at the tupled state of its value arguments.  Hypothesis
arguments are *erased* (self-calls drop them; remaining proof subterms are re-synthesized at the
monomorphised bounds — obligations queued as mvars and discharged by `omega` after discovery),
and function/type arguments *monomorphise*.  Soundness is `recSound` (`mrec` adequacy at the
measure = the recursion component) against the **totalized** `Nat.rec` twin `goT`, bridged back
to the partial source by a generated induction — so a call site gets
`cf ⟨state⟩ ≈ ret (source state hyps)`, an *eutt* step (`sc_callPureE`). -/

/-- Right-nested host product type `A₀ × (A₁ × …)` (singleton = the type itself). -/
def mkProdTy : List Expr → Expr
  | [t]     => t
  | t :: ts => mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) t (mkProdTy ts)
  | []      => Lean.mkConst ``Unit []

/-- Right-nested reified product `Tp` (`t₀ ×ₚ (t₁ ×ₚ …)`; singleton = the `Tp` itself). -/
def prodTpOf : List Expr → Expr
  | [t]     => t
  | t :: ts => mkApp2 (Lean.mkConst ``Tp.prod []) t (prodTpOf ts)
  | []      => Lean.mkConst ``Tp.unit []

/-- Host projections of `s : A₀ × (A₁ × …)` — one per component, with explicit type arguments
    (pure, so usable on open terms). -/
def mkTupleProjs (tps : List Expr) (s : Expr) : List Expr :=
  match tps with
  | []  => []
  | [_] => [s]
  | t :: ts =>
      let tailTy := mkProdTy ts
      mkApp3 (Lean.mkConst ``Prod.fst [.zero, .zero]) t tailTy s ::
        mkTupleProjs ts (mkApp3 (Lean.mkConst ``Prod.snd [.zero, .zero]) t tailTy s)

/-- Right-nested host tuple `⟨a₀, ⟨a₁, …⟩⟩` with explicit type arguments (pure, so usable on open
    terms). -/
def mkTupleE (tps args : List Expr) : Expr :=
  match tps, args with
  | [_], [a] => a
  | t :: ts, a :: as =>
      mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) t (mkProdTy ts) a (mkTupleE ts as)
  | _, _ => Lean.mkConst ``Unit []   -- unreachable: arity ≥ 1 throughout

/-- The site-independent **shape** of a structural-recursive pure definition: the `0`/`succ`
    pattern position, the argument classification, and the two equations. -/
structure RecShape where
  arity    : Nat
  recPos   : Nat
  statePos : Array Nat
  hypPos   : Array Nat
  monoPos  : Array Nat
  baseEqn  : Name
  stepEqn  : Name
  deriving Inhabited

/-- Run `k lhsArgs rhs` under an equation's binders. -/
private def withEqn {α} (eqn : Name) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let some ci := (← getEnv).find? eqn | throwError "reflect%: internal: missing equation {eqn}"
  forallTelescope ci.type fun _ body => do
    let_expr Eq _ lhs rhs := body
      | throwError "reflect%: internal: unexpected equation shape for {eqn}"
    k lhs.getAppArgs rhs

/-- The `succ` pattern's variable (`Nat.succ m` / `m + 1`), if any. -/
private def succPatVar? (e : Expr) : Option Expr :=
  match_expr e with
  | Nat.succ m => if m.isFVar then some m else none
  | HAdd.hAdd _ _ _ _ m one =>
      match_expr one with
      | OfNat.ofNat _ o _ => if m.isFVar && o.isRawNatLit && o.rawNatLit? == some 1
                             then some m else none
      | _ => none
  | _ => none

/-- The signature actually spilled for this call site: discovery may have **demoted** the
    function arguments (a body that reaches a recursion); later passes must follow suit. -/
def Env.resolveVariant (env : Env) (sig : CallSig) (sigEq : CallSig → CallSig → MetaM Bool) :
    MetaM CallSig := do
  if (← (← env.defs.get).findM? (sigEq · sig)).isSome then return sig
  if sig.fnArgPos.isEmpty then return sig
  let some sig' ← (try some <$> sig.demoteFnArgs env catch _ => pure none) | return sig
  if (← (← env.defs.get).findM? (sigEq · sig')).isSome then return sig'
  return sig

/-- Recognise `cName` as a **spillable structural recursion**: a definition with exactly two
    equations whose left-hand sides differ from plain variables at exactly one (shared) `Nat`
    position — one `0`, one `succ m` — the `succ` side self-referential, the base not, and a pure
    reifiable result.  Arguments classify as hypotheses (`Prop`-typed, erased), monomorphisation
    parameters (function-typed, dependency carriers, unreifiable), or state. -/
def analyzeRecShape (cName : Name) : MetaM (Option RecShape) := do
  let some eqns ← (try getEqnsFor? cName catch _ => pure none) | return none
  unless eqns.size == 2 do return none
  let some ci := (← getEnv).find? cName | return none
  unless ci.hasValue do return none
  forallTelescope ci.type fun xs cod => do
    let arity := xs.size
    if arity == 0 then return none
    -- classification is *structural* (reifiability is a per-monomorphisation property, checked
    -- at the call site): hypotheses are `Prop`-typed; monomorphisation parameters are
    -- dependency carriers (the result type or another non-hypothesis argument's type mentions
    -- them: type indices like `n`, type parameters like `α`) and function-typed arguments
    let mut hypPos : Array Nat := #[]
    for i in [0:arity] do
      if ← Meta.isProp (← inferType xs[i]!) then hypPos := hypPos.push i
    let mut statePos : Array Nat := #[]
    let mut monoPos : Array Nat := #[]
    for i in [0:arity] do
      if hypPos.contains i then continue
      let ty ← inferType xs[i]!
      let mut mono := cod.containsFVar xs[i]!.fvarId! || ty.isSort
      for j in [0:arity] do
        if j != i && !hypPos.contains j then
          if (← inferType xs[j]!).containsFVar xs[i]!.fvarId! then mono := true
      if mono then monoPos := monoPos.push i else statePos := statePos.push i
    if statePos.isEmpty then return none
    -- the pattern position, from the two equations
    let inspect (eqn : Name) : MetaM (Option (Nat × Option Expr × Bool)) :=
      withEqn eqn fun lhsArgs rhs => do
        if lhsArgs.size != arity then return none
        let mut p? : Option (Nat × Option Expr) := none
        for j in [0:arity] do
          unless lhsArgs[j]!.isFVar do
            if p?.isSome then return none
            p? := some (j, succPatVar? lhsArgs[j]!)
        let some (p, mv) := p? | return none
        return some (p, mv, (rhs.find? (·.isConstOf cName)).isSome)
    let some (p1, mv1, r1) ← inspect eqns[0]! | return none
    let some (p2, mv2, r2) ← inspect eqns[1]! | return none
    unless p1 == p2 do return none
    let (baseEqn, stepEqn, stepRec, baseRec) ←
      match mv1, mv2 with
      | some _, none => pure (eqns[1]!, eqns[0]!, r1, r2)
      | none, some _ => pure (eqns[0]!, eqns[1]!, r2, r1)
      | _, _ => return none
    unless stepRec && !baseRec do return none
    unless statePos.contains p1 do return none
    unless ← isDefEq (← inferType xs[p1]!) (.const ``Nat []) do return none
    return some { arity, recPos := p1, statePos, hypPos, monoPos, baseEqn, stepEqn }

/-- Cached name-level verdict for `analyzeRecShape`. -/
def Env.isRecName (env : Env) (c : Name) : MetaM Bool := do
  if let some v := (← env.recVerdicts.get).lookup c then return v
  let v ← (do try pure (← analyzeRecShape c).isSome catch _ => pure false)
  env.recVerdicts.modify ((c, v) :: ·)
  return v

private def coreRoots : List Name :=
  [`Init, `Lean, `Std, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible,
   `ImportGraph, `LeanSearchClient]

/-- Does `e` reach — transitively through (non-core) definition values — a spillable structural
    recursion?  Bounded and cached; exempts a *closed* value from `Code.lit`-binding, since a
    recursion must reflect structurally, not evaluate.  Core/Mathlib definitions are not
    descended into (closed library values keep folding to literals). -/
def Env.reachesRec (env : Env) (e : Expr) : MetaM Bool := do
  let lenv ← getEnv
  let isCore (c : Name) : Bool :=
    match lenv.getModuleIdxFor? c with
    | none => false
    | some idx =>
        match lenv.header.moduleNames[idx.toNat]? with
        | some m => coreRoots.contains m.getRoot
        | none => true
  let mut visited : NameSet := {}
  let mut work : Array Name := e.getUsedConstants
  let mut budget := 64
  while budget > 0 do
    let some c := work.back? | return false
    work := work.pop
    if visited.contains c then continue
    visited := visited.insert c
    if isCore c then continue
    budget := budget - 1
    if ← env.isRecName c then return true
    let some ci := lenv.find? c | continue
    unless ci.hasValue do continue
    if ← Meta.isProp ci.type then continue
    work := work ++ ci.value!.getUsedConstants
  return false

/-- Eliminate erased-hypothesis occurrences from a totalized body: every **proof subterm**
    mentioning one is replaced by a fresh obligation mvar (queued on `env.pending`, discharged by
    `omega`/`decide` after the discovery pass) — sound by proof irrelevance.  A proof whose *type*
    still mentions a hypothesis (or a local binder) cannot be eliminated: reported. -/
partial def Env.elimHyps (env : Env) (hyps : Array FVarId) (e0 : Expr) : MetaM Expr := do
  if hyps.isEmpty then return e0
  let rec go (x : Expr) : MetaM Expr := do
    unless x.hasAnyFVar (fun fid => hyps.contains fid) do return x
    if ← Meta.isProof x then
      let ty ← inferType x
      if ty.hasAnyFVar (fun fid => hyps.contains fid) then
        throwError "reflect%: cannot totalize the recursive helper: a proof obligation's type \
                    mentions an erased hypothesis{indentExpr ty}"
      -- ∀-close the obligation over its free locals (the state binder, loop binders, …), so
      -- the queued mvar is context-free and dischargeable from the top level
      let fvIds := (collectFVars {} ty).fvarIds
      let fvars := (← Meta.sortFVarIds fvIds).map Expr.fvar
      -- declare the (closed) obligation in an *empty* local context, so no later
      -- `mkLambdaFVars` abstraction rewrites it into a delayed assignment
      let m ← mkFreshExprMVarAt {} {} (← mkForallFVars fvars ty)
      env.pending.modify (·.push m.mvarId!)
      return mkAppN m fvars
    match x with
    | .app .. => x.withApp fun f as => do
        return mkAppN (← go f) (← as.mapM go)
    | .lam nm t b bi =>
        withLocalDecl nm bi (← go t) fun v => do
          mkLambdaFVars #[v] (← go (b.instantiate1 v))
    | .forallE nm t b bi =>
        withLocalDecl nm bi (← go t) fun v => do
          mkForallFVars #[v] (← go (b.instantiate1 v))
    | .letE _ _ v b _ => go (b.instantiate1 v)
    | .mdata _ b => go b
    | .proj t i s => return .proj t i (← go s)
    | _ => throwError "reflect%: cannot eliminate an erased-hypothesis occurrence{indentExpr x}"
  go e0

/-- Under `eqn`'s binders, the rhs with: monomorphisation positions ↦ the site's values, state
    positions ↦ `stateVals` (by state index), the `succ` pattern variable ↦ `patVal`; hypothesis
    binders stay bound — `k hypFVars rhs` runs *inside* the telescope (they are eliminated
    there). -/
def withInstEqn {α} (shape : RecShape) (eqn : Name) (fArgs : Array Expr)
    (stateVals : Array Expr) (patVal : Option Expr) (k : Array FVarId → Expr → MetaM α) :
    MetaM α := do
  withEqn eqn fun lhsArgs rhs => do
    let mut fvars : Array Expr := #[]
    let mut vals : Array Expr := #[]
    let mut hypFVars : Array FVarId := #[]
    for j in [0:shape.arity] do
      let a := lhsArgs[j]!
      if shape.hypPos.contains j then
        if a.isFVar then hypFVars := hypFVars.push a.fvarId!
      else if j == shape.recPos then
        if let some m := succPatVar? a then
          fvars := fvars.push m
          vals := vals.push patVal.get!
      else if let some si := shape.statePos.findIdx? (· == j) then
        fvars := fvars.push a
        vals := vals.push stateVals[si]!
      else
        fvars := fvars.push a
        vals := vals.push fArgs[j]!
    k hypFVars (rhs.replaceFVars fvars vals)

/-- Rewrite a **pure body with self-calls** into a `FreeC` computation: the innermost self-call
    becomes the call event (`Sum.inr`) at the re-tupled state (dropping mono and hypothesis
    arguments); a non-tail context binds the result. -/
partial def Env.liftPureBody (env : Env) (shape : RecShape) (cName : Name)
    (εExt brExt σTy ρTy : Expr) (stateTys : List Expr) (statePos : Array Nat)
    (fnPairs : Array (Expr × Expr)) (t : Expr) : MetaM Expr := do
  let εE := mkApp (Lean.mkConst ``Effect []) env.Op
  let isSelf (x : Expr) : Bool :=
    x.getAppFn.isConstOf cName && x.getAppArgs.size == shape.arity
  let rec innermost (x : Expr) : Option Expr :=
    match x.find? isSelf with
    | none => none
    | some c =>
        match c.getAppArgs.findSome? innermost with
        | some deeper => some deeper
        | none => some c
  match innermost t with
  | none => mkAppOptM ``FreeE.pure #[εExt, brExt, env.SOp, ρTy, t]
  | some c =>
      let cArgs := c.getAppArgs
      let mut slots : List Expr := []
      for i in [0:statePos.size] do
        let arg := cArgs[statePos[i]!]!
        if h : i < fnPairs.size then
          -- **invariance**: a function-valued state component must pass through unchanged
          unless arg == fnPairs[i].1 do
            throwError "reflect%: recursive helper `{cName}` modifies its function-valued \
                        state — only invariant function state is supported{indentExpr c}"
          slots := slots ++ [fnPairs[i].2]
        else
          slots := slots ++ [arg]
      let tuple := mkTupleE stateTys slots
      let inrEv := mkApp3 (Lean.mkConst ``Sum.inr [.zero, .zero]) εE σTy tuple
      let pureC ← mkAppOptM ``FreeE.pure #[εExt, brExt, env.SOp, ρTy]
      let callE ← mkAppOptM ``FreeE.op #[εExt, brExt, env.SOp, ρTy, inrEv, pureC]
      if t == c then return callE
      withLocalDeclD `r ρTy fun r => do
        let t' := t.replace (fun x => if x == c then some r else none)
        let rest ← env.liftPureBody shape cName εExt brExt σTy ρTy stateTys statePos fnPairs t'
        mkAppM ``FreeE.bind #[callE, ← mkLambdaFVars #[r] rest]

/-- Rewrite a **`Free`-valued body with self-calls** over the call-extended events: self-calls
    become the call event at the re-tupled state (dropping mono/hypothesis arguments), DSL
    events relabel along `Sum.inl`, `pure`/`bind`/`bif`/`hop` rebuild structurally. -/
partial def Env.liftFreeBody (env : Env) (shape : RecShape) (cName : Name)
    (εExt brExt σTy ρTy : Expr) (stateTys : List Expr) (statePos : Array Nat)
    (fnPairs : Array (Expr × Expr)) (t0 : Expr) : MetaM Expr := do
  let εE := mkApp (Lean.mkConst ``Effect []) env.Op
  let rec go (t : Expr) : MetaM Expr := do
    let t := t.consumeMData.headBeta
    if let .letE _ _ v b _ := t then return ← go (b.instantiate1 v)
    if t.getAppFn.isConstOf cName && t.getAppArgs.size == shape.arity then
      let cArgs := t.getAppArgs
      let mut slots : List Expr := []
      for i in [0:statePos.size] do
        let arg := cArgs[statePos[i]!]!
        if h : i < fnPairs.size then
          unless arg == fnPairs[i].1 do
            throwError "reflect%: recursive helper `{cName}` modifies its function-valued \
                        state — only invariant function state is supported{indentExpr t}"
          slots := slots ++ [fnPairs[i].2]
        else
          slots := slots ++ [arg]
      let tuple := mkTupleE stateTys slots
      let inrEv := mkApp3 (Lean.mkConst ``Sum.inr [.zero, .zero]) εE σTy tuple
      let pureC ← mkAppOptM ``FreeE.pure #[εExt, brExt, env.SOp, ρTy]
      return ← mkAppOptM ``FreeE.op #[εExt, brExt, env.SOp, ρTy, inrEv, pureC]
    let doBind (x f : Expr) : MetaM Expr := do
      let .forallE _ A _ _ := (← whnf (← inferType f))
        | throwError "reflect%: bind cont not a function{indentExpr f}"
      let xC ← go x
      let fC ← withLocalDeclD `a A fun ha => do mkLambdaFVars #[ha] (← go (f.beta #[ha]))
      mkAppM ``FreeE.bind #[xC, fC]
    let relabel (e cont : Expr) : MetaM Expr := do
      let inlEv := mkApp3 (Lean.mkConst ``Sum.inl [.zero, .zero]) εE σTy e
      let R ← do
        let .forallE _ R _ _ := (← whnf (← inferType cont))
          | throwError "reflect%: op cont not a function{indentExpr cont}"
        pure R
      let kC ← withLocalDeclD `x R fun hx => do mkLambdaFVars #[hx] (← go (cont.beta #[hx]))
      mkAppOptM ``FreeE.op #[εExt, brExt, env.SOp, none, inlEv, kC]
    match_expr t with
    | FreeE.pure _ _ _ _ r => mkAppOptM ``FreeE.pure #[εExt, brExt, env.SOp, none, r]
    | Pure.pure _ _ _ r => mkAppOptM ``FreeE.pure #[εExt, brExt, env.SOp, none, r]
    | Bind.bind _ _ _ _ x f => doBind x f
    | FreeE.bind _ _ _ _ _ x f => doBind x f
    | cond _ c m1 m2 => do mkAppM ``cond #[c, ← go m1, ← go m2]
    | Free.op _ _ _ I R o i k => do
        relabel (← mkAppOptM ``Effect.mk #[env.Op, I, R, o, i]) k
    | FreeE.op _ _ _ _ e k => relabel e k
    | FreeE.hop _ _ _ _ β s b k => do
        let bC ← go b
        let kC ← withLocalDeclD `x β fun hx => do mkLambdaFVars #[hx] (← go (k.beta #[hx]))
        mkAppM ``FreeE.hop #[s, bC, kC]
    | _ =>
        match ← unfoldDefinition? t with
        | some t' => go t'
        | none => throwError "reflect%: cannot lift recursion body{indentExpr t}"
  go t0

/-- The **embedding** of a pure host function into the Kleisli slot: `fun x => ret (h x)`.
    Only unary function state is supported (`ofFn`-shaped). -/
def mkEmbOf (εE arityE : Expr) (host : Expr) : MetaM Expr := do
  let .forallE _ dom cod _ ← whnf (← inferType host)
    | throwError "reflect%: not a function-typed state component{indentExpr host}"
  if cod.hasLooseBVars || (← whnf cod).isForall then
    throwError "reflect%: curried function-valued recursion state is not supported{indentExpr host}"
  withLocalDeclD `x dom fun x => do
    mkLambdaFVars #[x] (← mkAppOptM ``ITree.ret #[εE, arityE, cod, mkApp host x])

/-- The lifted totalized body
    `cb := fun s => bif sᵣ == 0 then base[s] else step[s]` — the reflectable mirror of the
    source recursion over the tupled state (`isPure`: a pure body wraps in `pure` / extracts
    self-calls; a `Free` body relabels structurally). -/
def Env.buildCb (env : Env) (shape : RecShape) (cName : Name) (fArgs : Array Expr)
    (stateTys : Array Expr) (statePos : Array Nat) (fnHostTys : Array Expr)
    (σTy ρValTy : Expr) (recIdx : Nat) (isPure : Bool) : MetaM Expr := do
  let εE := mkApp (Lean.mkConst ``Effect []) env.Op
  let εExt := mkApp2 (Lean.mkConst ``Sum [.zero, .zero]) εE σTy
  let arityE := mkApp (Lean.mkConst ``Effect.arity []) env.Op
  let brExt ← mkAppOptM ``ITree.callBr #[εE, σTy, arityE, ρValTy]
  -- the invariant fn components enter as **pure host binders** (`cb` computes with them
  -- directly — the tree never applies a Kleisli value); self-call tuples carry their embeddings
  let hostDecls : Array (Name × (Array Expr → MetaM Expr)) :=
    (Array.range fnHostTys.size).map fun i =>
      (Name.mkSimple s!"f{i}", fun _ => pure fnHostTys[i]!)
  let kfDecls : Array (Name × (Array Expr → MetaM Expr)) :=
    (Array.range fnHostTys.size).map fun i =>
      (Name.mkSimple s!"kf{i}", fun _ => pure stateTys[i]!)
  withLocalDeclsD hostDecls fun hosts => do
  withLocalDeclsD kfDecls fun kfs => do
  let fnPairs := hosts.zip kfs
  let lift (rhs : Expr) : MetaM Expr :=
    if isPure then
      env.liftPureBody shape cName εExt brExt σTy ρValTy stateTys.toList statePos fnPairs rhs
    else
      env.liftFreeBody shape cName εExt brExt σTy ρValTy stateTys.toList statePos fnPairs rhs
  withLocalDeclD `s σTy fun s => do
    let projs := (mkTupleProjs stateTys.toList s).toArray
    let recProj := projs[recIdx]!
    let stateVals := (Array.range stateTys.size).map fun i =>
      if h : i < hosts.size then hosts[i] else projs[i]!
    let baseE ← withInstEqn shape shape.baseEqn fArgs stateVals none fun hyps rhs => do
      env.elimHyps hyps (← lift rhs)
    let km1 ← mkAppM ``HSub.hSub #[recProj, mkNatLit 1]
    let stepE ← withInstEqn shape shape.stepEqn fArgs stateVals (some km1) fun hyps rhs => do
      env.elimHyps hyps (← lift rhs)
    let condE ← mkAppM ``BEq.beq #[recProj, mkNatLit 0]
    mkLambdaFVars (hosts ++ kfs ++ #[s]) (← mkAppM ``cond #[condE, baseE, stepE])

/-- The totalized `Nat.rec` twin `goT : σ → ρ`: recursion on the `Nat` component, the other
    state components threading through the motive.  Definitionally reduces on `0`/`succ` — that
    (plus proof irrelevance) is what makes the `bridge` induction close by `rfl`. -/
partial def Env.buildGoT (env : Env) (shape : RecShape) (cName : Name) (fArgs : Array Expr)
    (stateTys : Array Expr) (statePos : Array Nat) (fnHostTys : Array Expr)
    (σTy ρTy : Expr) (recIdx : Nat) : MetaM Expr := do
  let fnCount := fnHostTys.size
  let restTys := (stateTys.toList.zipIdx.filterMap fun (t, i) =>
    if i == recIdx || i < fnCount then none else some t)
  let natTy : Expr := .const ``Nat []
  -- state-order values from (hosts, m?, rest-projections)
  let stateValsOf (hosts : Array Expr) (m : Expr) (restVals : List Expr) : Array Expr := Id.run do
    let mut vals : Array Expr := #[]
    let mut rest := restVals
    for i in [0:stateTys.size] do
      if h : i < fnCount then vals := vals.push hosts[i]!
      else if i == recIdx then vals := vals.push m
      else
        vals := vals.push rest.head!
        rest := rest.tail
    return vals
  -- rewrite self-calls `go args ↦ ih ⟨rest-of-args⟩` (innermost-first; the recursion argument
  -- must be *exactly* the pattern variable — structural recursion)
  let rewriteSelf (hosts : Array Expr) (m ih : Expr) (t0 : Expr) : MetaM Expr := do
    let isSelf (x : Expr) : Bool :=
      x.getAppFn.isConstOf cName && x.getAppArgs.size == shape.arity
    let rec loop (t : Expr) (fuel : Nat) : MetaM Expr := do
      if fuel == 0 then throwError "reflect%: internal: self-call rewrite did not terminate"
      let rec innermost (x : Expr) : Option Expr :=
        match x.find? isSelf with
        | none => none
        | some c => match c.getAppArgs.findSome? innermost with
          | some deeper => some deeper
          | none => some c
      match innermost t with
      | none => return t
      | some c =>
          let cArgs := c.getAppArgs
          unless cArgs[shape.recPos]! == m do
            throwError "reflect%: recursive helper `{cName}`: a self-call's recursion argument \
                        is not the structural predecessor{indentExpr c}"
          for i in [0:fnCount] do
            unless cArgs[statePos[i]!]! == hosts[i]! do
              throwError "reflect%: recursive helper `{cName}` modifies its function-valued \
                          state — only invariant function state is supported{indentExpr c}"
          let restArgs := statePos.toList.zipIdx.filterMap fun (j, i) =>
            if j == shape.recPos || i < fnCount then none else some cArgs[j]!
          let repl := if restTys.isEmpty then ih else mkApp ih (mkTupleE restTys restArgs)
          loop (t.replace (fun x => if x == c then some repl else none)) (fuel - 1)
    loop t0 32
  let hostDecls : Array (Name × (Array Expr → MetaM Expr)) :=
    (Array.range fnHostTys.size).map fun i =>
      (Name.mkSimple s!"f{i}", fun _ => pure fnHostTys[i]!)
  withLocalDeclsD hostDecls fun hosts => do
  withLocalDeclD `s σTy fun s => do
    let projs := (mkTupleProjs stateTys.toList s).toArray
    let recProj := projs[recIdx]!
    let restProjs := projs.toList.zipIdx.filterMap fun (p, i) =>
      if i == recIdx || i < fnCount then none else some p
    if restTys.isEmpty then
      let motive ← withLocalDeclD `n natTy fun n => mkLambdaFVars #[n] ρTy
      let base ← withInstEqn shape shape.baseEqn fArgs (stateValsOf hosts (mkNatLit 0) []) none
        fun hyps rhs => env.elimHyps hyps rhs
      let step ← withLocalDeclD `m natTy fun m =>
        withLocalDeclD `ih ρTy fun ih => do
          withInstEqn shape shape.stepEqn fArgs (stateValsOf hosts m []) (some m)
            fun hyps rhs => do
              let rhs ← rewriteSelf hosts m ih rhs
              mkLambdaFVars #[m, ih] (← env.elimHyps hyps rhs)
      let recApp ← mkAppOptM ``Nat.rec #[motive, base, step, recProj]
      mkLambdaFVars (hosts ++ #[s]) recApp
    else
      let restTy := mkProdTy restTys
      let motTy ← mkArrow restTy ρTy
      let motive ← withLocalDeclD `n natTy fun n => mkLambdaFVars #[n] motTy
      let base ← withLocalDeclD `rest restTy fun rest => do
        let rps := (mkTupleProjs restTys rest).toArray
        withInstEqn shape shape.baseEqn fArgs (stateValsOf hosts (mkNatLit 0) rps.toList) none
          fun hyps rhs => do mkLambdaFVars #[rest] (← env.elimHyps hyps rhs)
      let step ← withLocalDeclD `m natTy fun m =>
        withLocalDeclD `ih motTy fun ih =>
        withLocalDeclD `rest restTy fun rest => do
          let rps := (mkTupleProjs restTys rest).toArray
          withInstEqn shape shape.stepEqn fArgs (stateValsOf hosts m rps.toList) (some m)
            fun hyps rhs => do
              let rhs ← rewriteSelf hosts m ih rhs
              mkLambdaFVars #[m, ih, rest] (← env.elimHyps hyps rhs)
      let recApp ← mkAppOptM ``Nat.rec #[motive, base, step, recProj]
      mkLambdaFVars (hosts ++ #[s]) (mkApp recApp (mkTupleE restTys restProjs))

/-- Analyze a call to a **recursive pure helper** at this site: recognise the shape, require the
    monomorphisation arguments closed, and produce the spill signature — reusing an existing
    monomorphisation's synthesis (`RecData`) or building it (discovery only). -/
def Env.analyzeRecCall (env : Env) (e : Expr) : MetaM (Option CallSig) := do
  if env.noSpill then return none
  let fn := e.getAppFn
  let some cName := fn.constName? | return none
  unless ← env.isRecName cName do return none
  let some shape ← analyzeRecShape cName | return none
  let fArgs := e.getAppArgs
  if fArgs.size != shape.arity then return none
  for j in shape.monoPos do
    if fArgs[j]!.hasAnyFVar (fun fid => (env.subst.lookup fid).isSome) then
      throwError "reflect%: recursive helper `{cName}`: a function/type argument captures \
                  program variables — a spilled recursive definition is closed, so it must be \
                  program-independent{indentExpr fArgs[j]!}"
  let monoArgs := shape.monoPos.map (fArgs[·]!)
  -- reorder the state **function components first** (the adequacy invariant pins them as
  -- embeddings, and the repackaging peels the tuple from the front)
  let mut fnState : Array Nat := #[]
  let mut foState : Array Nat := #[]
  for j in shape.statePos do
    if (← whnf (← inferType fArgs[j]!)).isForall then fnState := fnState.push j
    else foState := foState.push j
  let statePos := fnState ++ foState
  let stateArgs := statePos.map (fArgs[·]!)
  let fnHostTys ← fnState.mapM (fun j => inferType fArgs[j]!)
  let mut stateTys : Array Expr := #[]
  let mut stateTps : Array Expr := #[]
  for i in [0:stateArgs.size] do
    let hostTy ← inferType stateArgs[i]!
    let tp ← reifyTpOrThrow hostTy
    stateTps := stateTps.push tp
    -- a function component's σ-slot is the *object* (Kleisli) type, not the host type
    if i < fnState.size then
      stateTys := stateTys.push (mkApp2 (Lean.mkConst ``Tp.denote []) env.Op tp)
    else
      stateTys := stateTys.push hostTy
  let σTy := mkProdTy stateTys.toList
  let σTp := prodTpOf stateTps.toList
  let ρTy ← inferType e
  let (ρValTy, isPure) ←
    match_expr ← whnf ρTy with
    | FreeE _ _ _ R => pure (R, false)
    | _ => pure (ρTy, true)
  let some ρTp ← reifyTp ρValTy | return none
  let some recIdx := statePos.findIdx? (· == shape.recPos)
    | throwError "reflect%: internal: recursion position not in state"
  let asList ← mkListLit (.const ``Tp []) [σTp]
  let sig0 : CallSig := {
    cName, cValInst := fn, fArgs, valuePos := statePos,
    valueArgs := stateArgs.toList, argTys := stateTys, argTps := stateTps,
    asList, retTp := ρTp, isPure, monoArgs }
  if let some hit ← (← env.defs.get).findM? (sigsMatch · sig0) then
    return some { sig0 with rec? := hit.rec? }
  if env.resolved.isSome || env.pf then
    throwError "reflect%: internal: recursive helper `{cName}` was not discovered"
  if fnState.size > 1 then
    throwError "reflect%: recursive helper `{cName}`: more than one function-valued state \
                component is not yet supported"
  let cb ← env.buildCb shape cName fArgs stateTys statePos fnHostTys σTy ρValTy recIdx isPure
  -- the `Nat.rec` twin (and its bridge) exist only to *totalize* — hypothesis-free sources are
  -- total over the state already and stand in for themselves
  let goT ←
    if shape.hypPos.isEmpty then pure (Expr.const ``Unit.unit [])
    else env.buildGoT shape cName fArgs stateTys statePos fnHostTys σTy ρTy recIdx
  let μ ← withLocalDeclD `s σTy fun s =>
    mkLambdaFVars #[s] (mkTupleProjs stateTys.toList s).toArray[recIdx]!
  let rd : RecData := { statePos, hypPos := shape.hypPos,
                        recIdx, stateTys, stateTps, σTy, σTp, ρTy, ρValTy, cb, goT, μ,
                        fnStateCount := fnState.size, fnHostTys }
  return some { sig0 with rec? := some rd }

mutual
  /-- Reflect a *pure* host value into a `Code` atom, A-normalising into `un`/`bin`/`lit`/collection
      node chains, then feed the atom to `k`.  In proof mode the continuation also returns the step's
      equation, so proofs thread through in one pass; every non-`get`/`set` step is definitional, and
      a get/set/cast inserts exactly `sc_*` (= `dif_pos h`, the source's own proof).  `resTp` is the
      overall result `Tp` (the sc-lemmas' `α`, unrecoverable through `Tp.denote`). -/
  partial def Env.atom (env : Env) (resTp a : Expr) (k : Expr → MetaM CodePf) : MetaM CodePf := do
    let a := (← instantiateMVars a).headBeta
    if let .letE _ ty v b _ := a then
      -- a reifiable pure `let` keeps its **sharing**: the bound value walks once, the body sees
      -- its atom (a non-reifiable let — a proof, a function — zeta-inlines instead)
      if (← reifyTp ty).isSome then
        return ← env.atom resTp v fun av => do
          if env.pf then
            let env' := if let .fvar fid := av
              then { env with subst := (fid, av) :: env.subst } else env
            env'.atom resTp (b.instantiate1 av) k
          else
            withLocalDeclD `h ty fun hx =>
              { env with subst := (hx.fvarId!, av) :: env.subst }.atom resTp (b.instantiate1 hx) k
      else
        return ← env.atom resTp (b.instantiate1 v) k
    if let .fvar fid := a then
      if let some atom := env.subst.lookup fid then return ← k atom
    if a.isLambda then return ← env.emitLam resTp a k
    if !(a.hasAnyFVar fun fid => (env.subst.lookup fid).isSome) then
      -- …except when the closed value contains a recursive helper: a recursion must reflect
      -- structurally (a `rec_` spill), not evaluate into a literal — fall through to the arms
      if env.noSpill || !(← env.reachesRec a) then
        if env.pf then
          -- a closed value, proof mode: feed it *directly* (no `Code.lit` node — denotationally
          -- identical, and a literal index/collection keeps a get/set's source proof `h` fitting)
          return ← k a
        else
          return ← env.mkLitBind a (← reifyTpOrThrow (← inferType a)) k
    match_expr a with
    | HMul.hMul _ _ _ _ x y => let (o,c) ← arithOp ``Bin.mul ``Bin.mulZ (← inferType a); env.emitBin resTp o c x y k
    | HAdd.hAdd _ _ _ _ x y => let (o,c) ← arithOp ``Bin.add ``Bin.addZ (← inferType a); env.emitBin resTp o c x y k
    | HSub.hSub _ _ _ _ x y => let (o,c) ← arithOp ``Bin.sub ``Bin.subZ (← inferType a); env.emitBin resTp o c x y k
    | HPow.hPow _ _ _ _ x y =>
        match_expr ← reifyTpOrThrow (← inferType a) with
        | Tp.nat    => env.emitBin resTp (.const ``Bin.pow []) (.const ``Tp.nat []) x y k
        | Tp.zmod n => env.emitBin resTp (mkApp (.const ``Bin.powZ []) n)
                         (mkApp (.const ``Tp.zmod []) n) x y k
        | _ => throwError "reflect%: `^` is only supported at `Nat` and `ZMod`:{indentExpr a}"
    | BEq.beq _ _ x y       => env.emitBin resTp (.const ``Bin.eq []) (.const ``Tp.bool []) x y k
    | Bool.and x y          => env.emitBin resTp (.const ``Bin.and []) (.const ``Tp.bool []) x y k
    | Bool.or  x y          => env.emitBin resTp (.const ``Bin.or []) (.const ``Tp.bool []) x y k
    | Bool.not x            => env.emitUn resTp (.const ``Un.not []) (.const ``Tp.bool []) x k
    | Prod.mk _ _ x y =>
        let aTp ← reifyTpOrThrow (← inferType x); let bTp ← reifyTpOrThrow (← inferType y)
        env.emitBin resTp (mkApp2 (.const ``Bin.pair []) aTp bTp) (mkApp2 (.const ``Tp.prod []) aTp bTp) x y k
    | Array.push _ xs x =>
        match_expr ← reifyTpOrThrow (← inferType a) with
        | Tp.array aTp =>
            env.emitBin resTp (mkApp (.const ``Bin.push []) aTp)
              (mkApp (.const ``Tp.array []) aTp) xs x k
        | _ => throwError "reflect%: `Array.push` at a non-array type{indentExpr a}"
    | Prod.fst _ _ p => env.emitUn resTp (← prodUn ``Un.fst p) (← reifyTpOrThrow (← inferType a)) p k
    | Prod.snd _ _ p => env.emitUn resTp (← prodUn ``Un.snd p) (← reifyTpOrThrow (← inferType a)) p k
    | Sum.inl A B x =>
        let aTp ← reifyTpOrThrow A; let bTp ← reifyTpOrThrow B
        env.emitUn resTp (mkApp2 (.const ``Un.inl []) aTp bTp) (mkApp2 (.const ``Tp.sum []) aTp bTp) x k
    | Sum.inr A B x =>
        let aTp ← reifyTpOrThrow A; let bTp ← reifyTpOrThrow B
        env.emitUn resTp (mkApp2 (.const ``Un.inr []) aTp bTp) (mkApp2 (.const ``Tp.sum []) aTp bTp) x k
    | GetElem.getElem _ _ _ _ _ coll i h =>
        -- `coll[i]`: the erased node drops the in-bounds proof; in proof mode the *source's* proof
        -- closes the node's `fail` branch (`sc_vget`/`sc_aget`)
        let (natIdx, finPf) ← finIndexToNat i        -- a `Fin` index becomes `i.val` with `i.isLt`
        let hSrc := finPf.getD h
        let natT : Expr := .const ``Tp.nat []
        match_expr ← reifyTpOrThrow (← inferType coll) with
        | Tp.vec aTp nExpr =>
            env.emitPop resTp a (mkApp2 (.const ``POp.vget []) aTp nExpr) aTp
              [mkApp2 (.const ``Tp.vec []) aTp nExpr, natT] [coll, natIdx]
              (fun klam => env.mkSc ``sc_vget #[resTp, aTp, none, coll, natIdx, klam, hSrc]) k
        | Tp.array aTp =>
            env.emitPop resTp a (mkApp (.const ``POp.aget []) aTp) aTp
              [mkApp (.const ``Tp.array []) aTp, natT] [coll, natIdx]
              (fun klam => env.mkSc ``sc_aget #[resTp, aTp, coll, natIdx, klam, hSrc]) k
        | _ => throwError "reflect%: get on a non-collection value{indentExpr coll}"
    | Vector.ofFn nExpr elemTy f =>
        -- the lane dimension is a **kept loop** (a `vgen` node), not unrolled
        let aTp ← reifyTpOrThrow elemTy
        env.emitVgen resTp a aTp nExpr f k
    | Vector.set _ _ coll i x h =>
        match_expr ← reifyTpOrThrow (← inferType coll) with
        | Tp.vec aTp nExpr =>
            let vecT := mkApp2 (.const ``Tp.vec []) aTp nExpr
            env.emitPop resTp a (mkApp2 (.const ``POp.vset []) aTp nExpr) vecT
              [vecT, .const ``Tp.nat [], aTp] [coll, i, x]
              (fun klam => env.mkSc ``sc_vset #[resTp, aTp, none, coll, i, x, klam, h]) k
        | _ => throwError "reflect%: `Vector.set` on a non-vector{indentExpr coll}"
    | Array.set _ coll i x h =>
        match_expr ← reifyTpOrThrow (← inferType coll) with
        | Tp.array aTp =>
            let arrT := mkApp (.const ``Tp.array []) aTp
            env.emitPop resTp a (mkApp (.const ``POp.aset []) aTp) arrT
              [arrT, .const ``Tp.nat [], aTp] [coll, i, x]
              (fun klam => env.mkSc ``sc_aset #[resTp, aTp, coll, i, x, klam, h]) k
        | _ => throwError "reflect%: `Array.set` on a non-array{indentExpr coll}"
    | Vector.mk _ nExpr arr h =>
        match_expr ← reifyTpOrThrow (← inferType a) with
        -- a list literal is a construction; a runtime `arr` is an `array → vec` *cast* (`⟨arr, h⟩`)
        | Tp.vec aTp _ =>
            match seqLitElems arr with
            | some elems => env.emitVec resTp aTp nExpr elems k
            | none       =>
                env.emitPop resTp a (mkApp2 (.const ``POp.arrToVec []) aTp nExpr)
                  (mkApp2 (.const ``Tp.vec []) aTp nExpr) [mkApp (.const ``Tp.array []) aTp] [arr]
                  (fun klam => env.mkSc ``sc_arrToVec #[resTp, aTp, nExpr, arr, klam, h]) k
        | _ => throwError "reflect%: `Vector.mk` at a non-vector type{indentExpr a}"
    | List.toArray _ lst =>
        let some elems := seqLitElems lst
          | throwError "reflect%: array not built from a list literal{indentExpr a}"
        match_expr ← reifyTpOrThrow (← inferType a) with
        | Tp.array aTp => env.emitArr resTp aTp elems k
        | _ => throwError "reflect%: array literal at a non-array type{indentExpr a}"
    | Fin.mk nExpr m h =>
        env.emitPop resTp a (mkApp (.const ``POp.natToFin []) nExpr)
          (mkApp (.const ``Tp.fin []) nExpr) [.const ``Tp.nat []] [m]
          (fun klam => env.mkSc ``sc_natToFin #[resTp, nExpr, m, klam, h]) k
    | Vector.toArray A nExpr v =>                                            -- total downcast `v.toArray`
        let aTp ← reifyTpOrThrow A
        env.emitUn resTp (mkApp2 (.const ``Un.toArray []) aTp nExpr) (mkApp (.const ``Tp.array []) aTp) v k
    | Fin.val nExpr i =>                                                     -- total downcast `i.val`
        env.emitUn resTp (mkApp (.const ``Un.finVal []) nExpr) (.const ``Tp.nat []) i k
    | Fin.foldl elemTy nExpr f init =>
        -- a bounded loop — reflected as a first-class `fold` node, NOT unrolled
        let aTp ← reifyTpOrThrow elemTy
        env.emitFold resTp a aTp nExpr f init k
    | ite _ c inst t e =>
        -- a pure decidable `if` — both branches evaluate, a strict `select` picks
        env.emitIte resTp a c inst t e k
    | Decidable.decide p _ =>
        -- a coerced comparison used as a `Bool` value (e.g. inside `… || …`); `Bin.denote` of the
        -- ordering ops is `decide`-shaped, so the step stays definitional
        let natCmp (op : Expr) (x y : Expr) : MetaM CodePf := do
          match_expr ← reifyTpOrThrow (← inferType x) with
          | Tp.nat => env.emitBin resTp op (.const ``Tp.bool []) x y k
          | _ => throwError "reflect%: `decide` only supported on `Nat` comparisons{indentExpr a}"
        match_expr p with
        | LT.lt _ _ x y => natCmp (.const ``Bin.lt []) x y
        | LE.le _ _ x y => natCmp (.const ``Bin.ble []) x y
        | GE.ge _ _ x y => natCmp (.const ``Bin.ble []) y x
        | GT.gt _ _ x y => natCmp (.const ``Bin.lt []) y x
        | _ => throwError "reflect%: `decide` only supported on `Nat` comparisons{indentExpr a}"
    | _ => do
        -- a *pure helper application*: spill it as a `def_` — definitions are **kept folded**;
        -- a *recursive* one spills as a `rec_`; anything unspillable unfolds and retries
        if a.isApp then
          let hd := a.getAppFn
          if hd.isFVar && (env.subst.lookup hd.fvarId!).isSome then
            if let some t ← reifyTp (← inferType hd) then
              if t.isAppOf ``Tp.fn then
                return ← env.emitApps resTp hd a.getAppArgs k
        if !env.noSpill then
          if let some sig ← env.analyzeRecCall a then
            return ← env.emitCallPure resTp sig k
          if let some sig ← analyzeCall a then
            if sig.isPure then
              let sig ← env.resolveVariant sig sigsMatch
              return ← env.emitCallPure resTp sig k
        match ← unfoldDefinition? a with
        | some a' => env.atom resTp a' k
        | none => throwError "reflect%: cannot reflect operand (not an atom or supported \
                              primitive):{indentExpr a}"

  /-- Binary primitive: reflect both operands, bind the result as a fresh var `vc`, emit the `bin`
      node; in proof mode instantiate `vc ↦ Bin.denote o x y` in the continuation's proof (the `bin`
      step is definitional). -/
  partial def Env.emitBin (env : Env) (resTp binOp cTp x y : Expr) (k : Expr → MetaM CodePf) : MetaM CodePf :=
    env.atom resTp x fun ax =>
    env.atom resTp y fun ay =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let (kcode, kpf?) ← k vc
      let node ← mkAppOptM ``Code.bin
        #[env.Op, env.Opc, env.SOp, env.F, env.V, none, none, none, none, binOp, ax, ay, ← mkLambdaFVars #[vc] kcode]
      let pf? ← kpf?.mapM fun kp =>
        return { kp with e := kp.e.replaceFVar vc (← mkAppOptM ``Bin.denote #[env.Op, none, none, none, binOp, ax, ay]) }
      return (node, pf?)

  /-- Unary primitive: as `emitBin`, with `vc ↦ Un.denote o x`. -/
  partial def Env.emitUn (env : Env) (resTp unOp cTp x : Expr) (k : Expr → MetaM CodePf) : MetaM CodePf :=
    env.atom resTp x fun ax =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let (kcode, kpf?) ← k vc
      let node ← mkAppOptM ``Code.un
        #[env.Op, env.Opc, env.SOp, env.F, env.V, none, none, none, unOp, ax, ← mkLambdaFVars #[vc] kcode]
      let pf? ← kpf?.mapM fun kp =>
        return { kp with e := kp.e.replaceFVar vc (← mkAppOptM ``Un.denote #[env.Op, none, none, unOp, ax]) }
      return (node, pf?)

  /-- A **partial primitive** (`Code.pop`): reflect the arguments, bind the result as a fresh var,
      emit the node.  In proof mode, close the erased `fail` branch via the per-op `sc_*` bridging
      lemma — built by `mkScStep` from the *source* arguments and the source's own proof (not the
      reflected atoms, which for compound arguments are fresh binders; the enclosing nodes tie each
      binder to its source value) — instantiating the result var with the source value `src`. -/
  partial def Env.emitPop (env : Env) (resTp src popOp retTp : Expr) (argTps argVals : List Expr)
      (mkScStep : Expr → MetaM Expr) (k : Expr → MetaM CodePf) : MetaM CodePf :=
    env.atoms resTp argVals fun atoms => do
      let argsHL ← mkArgHListT env.V atoms argTps
      let asList ← mkListLit (.const ``Tp []) argTps
      withLocalDeclD `v (mkApp env.V retTp) fun vc => do
        let (kcode, kpf?) ← k vc
        let klam ← mkLambdaFVars #[vc] kcode
        let node ← mkAppOptM ``Code.pop
          #[env.Op, env.Opc, env.SOp, env.F, env.V, none, asList, retTp, popOp, argsHL, klam]
        let pf? ← kpf?.mapM fun kp => do
          pfTransD ⟨← mkScStep klam, true⟩ { kp with e := kp.e.replaceFVar vc src }
        return (node, pf?)

  /-- A **bounded fold** (`Fin.foldl n f init`): reflect the initial accumulator, reflect the loop
      body **once** at fresh index/accumulator binders (ending in its own `ret`), and emit the
      `fold` node — the loop is *kept as control flow*, never unrolled.  In proof mode `sc_fold`
      consumes the body's pointwise equations (∀-abstracted over the binders); the `Fin`-typed index
      binder also supplies in-bounds facts (`i.isLt`) to gets inside the body. -/
  partial def Env.emitFold (env : Env) (resTp src aTp nExpr f init : Expr)
      (k : Expr → MetaM CodePf) : MetaM CodePf := do
    let finTp := mkApp (.const ``Tp.fin []) nExpr
    let finHostTy := mkApp (.const ``Fin []) nExpr
    let elemHostTy ← whnf (← inferType init)
    -- the body, walked once; in proof mode also its pointwise equation, ∀-abstracted
    let (bodyLam, hb?) ←
      withLocalDeclD `i (mkApp env.V finTp) fun vi =>
      env.withHostVar finHostTy vi fun hi =>
      withLocalDeclD `acc (mkApp env.V aTp) fun vacc =>
      env.withHostVar elemHostTy vacc fun hacc => do
        let env' := { env with
          subst := (hi.fvarId!, vi) :: (hacc.fvarId!, vacc) :: env.subst }
        let (bcode, bpf?) ← env'.atom aTp (f.beta #[hacc, hi]) (env'.liftK (env'.mkRetT aTp))
        pure (← mkLambdaFVars #[vi, vacc] bcode,
              ← bpf?.mapM (fun p => do pure { p with e := ← mkLambdaFVars #[vi, vacc] p.e }))
    env.atom resTp init fun ainit =>
    withLocalDeclD `v (mkApp env.V aTp) fun vc => do
      let (kcode, kpf?) ← k vc
      let klam ← mkLambdaFVars #[vc] kcode
      let node ← mkAppOptM ``Code.fold
        #[env.Op, env.Opc, env.SOp, env.F, env.V, none, aTp, nExpr, ainit, bodyLam, klam]
      let pf? ← kpf?.mapM fun kp => do
        let some hb := hb? | throwError "reflect%: internal: missing fold body proof"
        let scStep : Pf ←
          if hb.isEq then
            pure ⟨← env.mkSc ``sc_fold
              #[resTp, aTp, nExpr, init, f, bodyLam, klam, hb.e], true⟩
          else
            pure ⟨← mkAppOptM ``sc_foldE
              #[env.Op, env.SOp, resTp, aTp, nExpr, init, f, bodyLam, klam, hb.e], false⟩
        pfTransD scStep { kp with e := kp.e.replaceFVar vc src }
      return (node, pf?)

  /-- A **bounded generator** (`Vector.ofFn f`): reflect the lane body **once** at a fresh `Fin`
      index binder (ending in its own `ret`) and emit the `vgen` node — the lane dimension is kept
      as a loop.  In proof mode `sc_vgen` consumes the body's pointwise equations. -/
  partial def Env.emitVgen (env : Env) (resTp src aTp nExpr f : Expr)
      (k : Expr → MetaM CodePf) : MetaM CodePf := do
    let finTp := mkApp (.const ``Tp.fin []) nExpr
    let finHostTy := mkApp (.const ``Fin []) nExpr
    let (bodyLam, hb?) ←
      withLocalDeclD `i (mkApp env.V finTp) fun vi =>
      env.withHostVar finHostTy vi fun hi => do
        let env' := { env with subst := (hi.fvarId!, vi) :: env.subst }
        let (bcode, bpf?) ← env'.atom aTp (f.beta #[hi]) (env'.liftK (env'.mkRetT aTp))
        pure (← mkLambdaFVars #[vi] bcode,
              ← bpf?.mapM (fun p => do pure { p with e := ← mkLambdaFVars #[vi] p.e }))
    withLocalDeclD `v (mkApp env.V (mkApp2 (.const ``Tp.vec []) aTp nExpr)) fun vc => do
      let (kcode, kpf?) ← k vc
      let klam ← mkLambdaFVars #[vc] kcode
      let node ← mkAppOptM ``Code.vgen
        #[env.Op, env.Opc, env.SOp, env.F, env.V, none, aTp, nExpr, bodyLam, klam]
      let pf? ← kpf?.mapM fun kp => do
        let some hb := hb? | throwError "reflect%: internal: missing vgen body proof"
        let scStep : Pf ←
          if hb.isEq then
            pure ⟨← env.mkSc ``sc_vgen
              #[resTp, aTp, nExpr, f, bodyLam, klam, hb.e], true⟩
          else
            pure ⟨← mkAppOptM ``sc_vgenE
              #[env.Op, env.SOp, resTp, aTp, nExpr, f, bodyLam, klam, hb.e], false⟩
        pfTransD scStep { kp with e := kp.e.replaceFVar vc src }
      return (node, pf?)

  /-- A **pure decidable `if`**: both branches reflect (strict — a circuit-style `select`), the
      condition becomes a `Bool` atom, and one bridging lemma (`ite_decide`/`ite_nat_eq`/`ite_bool`)
      aligns the source `ite` with the selected `bif`. -/
  partial def Env.emitIte (env : Env) (resTp src c inst t e : Expr) (k : Expr → MetaM CodePf) :
      MetaM CodePf := do
    let aTp ← reifyTpOrThrow (← inferType t)
    let natBin (op : Expr) (x y : Expr) : (Expr → MetaM CodePf) → MetaM CodePf := fun kc => do
      match_expr ← reifyTpOrThrow (← inferType x) with
      | Tp.nat => env.emitBin resTp op (.const ``Tp.bool []) x y kc
      | _ => throwError "reflect%: `if` comparison only supported at `Nat`{indentExpr c}"
    -- (condition-atom emitter, source-side condition `Bool`, `ite → bif` bridging equation)
    let (emitCond, cBoolSrc, bridge) ← show MetaM (((Expr → MetaM CodePf) → MetaM CodePf) × Expr × Expr) from do
      match_expr c with
      | Eq ty x y =>
          match_expr ty with
          | Bool => do
              unless y.isConstOf ``Bool.true do
                throwError "reflect%: unsupported `if` condition{indentExpr c}"
              pure ((fun kc => env.atom resTp x kc), x, ← mkAppM ``ite_bool #[x, t, e])
          | Nat => do
              pure (natBin (.const ``Bin.eq []) x y, ← mkAppM ``BEq.beq #[x, y],
                    ← mkAppM ``ite_nat_eq #[x, y, t, e])
          | _ => throwError "reflect%: unsupported `if` condition{indentExpr c}"
      | LT.lt _ _ x y => do
          pure (natBin (.const ``Bin.lt []) x y, ← mkAppOptM ``Decidable.decide #[c, inst],
                ← mkAppOptM ``ite_decide #[c, inst, none, t, e])
      | LE.le _ _ x y => do
          pure (natBin (.const ``Bin.ble []) x y, ← mkAppOptM ``Decidable.decide #[c, inst],
                ← mkAppOptM ``ite_decide #[c, inst, none, t, e])
      | GE.ge _ _ x y => do
          pure (natBin (.const ``Bin.ble []) y x, ← mkAppOptM ``Decidable.decide #[c, inst],
                ← mkAppOptM ``ite_decide #[c, inst, none, t, e])
      | GT.gt _ _ x y => do
          pure (natBin (.const ``Bin.lt []) y x, ← mkAppOptM ``Decidable.decide #[c, inst],
                ← mkAppOptM ``ite_decide #[c, inst, none, t, e])
      | _ => throwError "reflect%: unsupported `if` condition{indentExpr c}"
    emitCond fun cb =>
    env.atom resTp t fun ta =>
    env.atom resTp e fun ea =>
    withLocalDeclD `v (mkApp env.V aTp) fun vc => do
      let (kcode, kpf?) ← k vc
      let klam ← mkLambdaFVars #[vc] kcode
      let boolT : Expr := .const ``Tp.bool []
      let argsHL ← mkArgHListT env.V [cb, ta, ea] [boolT, aTp, aTp]
      let asList ← mkListLit (.const ``Tp []) [boolT, aTp, aTp]
      let node ← mkAppOptM ``Code.pop
        #[env.Op, env.Opc, env.SOp, env.F, env.V, none, asList, aTp, mkApp (.const ``POp.select []) aTp,
          argsHL, klam]
      let pf? ← kpf?.mapM fun kp => do
        let scStep ← env.mkSc ``sc_select #[resTp, aTp, cBoolSrc, t, e, klam]
        -- `bif ⟦c⟧ then t else e = ite c t e` under `denote ∘ klam`
        let congrFn ← withLocalDeclD `z (mkApp env.V aTp) fun z => do
          mkLambdaFVars #[z] (← env.denE (mkApp klam z))
        let congrStep ← mkAppM ``congrArg #[congrFn, ← mkAppM ``Eq.symm #[bridge]]
        pfTransD ⟨scStep, true⟩
          (← pfTransD ⟨congrStep, true⟩ { kp with e := kp.e.replaceFVar vc src })
      return (node, pf?)

  /-- **Vector construction** `#v[e₀,…]`: reflect the elements, bind the result vector as a fresh
      var, emit the `vec` node; the step is definitional (`vc ↦` the atom-vector). -/
  partial def Env.emitVec (env : Env) (resTp aTp nExpr : Expr) (elems : List Expr)
      (k : Expr → MetaM CodePf) : MetaM CodePf :=
    env.atoms resTp elems fun atoms => do
      let vecVal ← mkVecOfAtoms env.V aTp nExpr atoms
      withLocalDeclD `v (mkApp env.V (mkApp2 (.const ``Tp.vec []) aTp nExpr)) fun vc => do
        let (kcode, kpf?) ← k vc
        let node ← mkAppOptM ``Code.vec
          #[env.Op, env.Opc, env.SOp, env.F, env.V, none, aTp, nExpr, vecVal, ← mkLambdaFVars #[vc] kcode]
        return (node, kpf?.map (fun kp => { kp with e := kp.e.replaceFVar vc vecVal }))

  /-- **Array construction** `#[e₀,…]`: as `emitVec`, instantiating with `(#[atoms])`. -/
  partial def Env.emitArr (env : Env) (resTp aTp : Expr) (elems : List Expr)
      (k : Expr → MetaM CodePf) : MetaM CodePf :=
    env.atoms resTp elems fun atoms => do
      let lst ← mkListLit (mkApp env.V aTp) atoms
      withLocalDeclD `v (mkApp env.V (mkApp (.const ``Tp.array []) aTp)) fun vc => do
        let (kcode, kpf?) ← k vc
        let node ← mkAppOptM ``Code.arr
          #[env.Op, env.Opc, env.SOp, env.F, env.V, none, aTp, lst, ← mkLambdaFVars #[vc] kcode]
        let pf? ← kpf?.mapM fun kp =>
          return { kp with e := kp.e.replaceFVar vc (← mkAppM ``List.toArray #[lst]) }
        return (node, pf?)

  /-- Reflect a list of pure argument values into their atoms. -/
  partial def Env.atoms (env : Env) (resTp : Expr) : List Expr → (List Expr → MetaM CodePf) → MetaM CodePf
    | [],      k => k []
    | v :: vs, k => env.atom resTp v fun av => env.atoms resTp vs (fun atoms => k (av :: atoms))

  /-- Reflect a `Free Op SOp _` computation into a `Code`; `k` consumes the result atom.  In proof
      mode, also return `proof : denote code = bind (ofFree e) Kf` — the invariant (★). -/
  partial def Env.walk (env : Env) (resTp e : Expr) (k : Expr → MetaM Expr) : MetaM CodePf := do
    let e := e.consumeMData.headBeta
    if let .letE _ _ v b _ := e then return ← env.walk resTp (b.instantiate1 v) k
    match_expr e with
    | FreeE.pure _ _ _ _ a    => env.walkPure resTp a k
    | Pure.pure _ _ _ a       => env.walkPure resTp a k
    | Bind.bind _ _ _ _ x f   => env.walkBind resTp x f k
    | FreeE.bind _ _ _ _ _ x f => env.walkBind resTp x f k
    | cond _ c t el           => env.walkIte resTp c t el k
    | Free.op _ _ _ I R o i cont => env.walkOp resTp I R o i cont k
    | FreeE.op _ _ _ _ ev cont => env.walkOpE resTp ev cont k
    | FreeE.hop _ _ _ _ β s b cont => env.walkScope resTp β s b cont k
    | Fin.foldlM _ elemTy _ nExpr f init =>
        -- a bounded loop with an *effectful* (`Free`-valued) body — the same body-agnostic node
        env.walkFold resTp elemTy nExpr f init k
    | _ =>
        match ← env.tryCall resTp e k with
        | some r => pure r
        | none => match ← unfoldDefinition? e with
          | some e' => env.walk resTp e' k
          | none    => throwError "reflect%: don't know how to reflect computation{indentExpr e}"

  /-- `pure a`: reflect the atom; in proof mode wrap its step with `sc_pure`. -/
  partial def Env.walkPure (env : Env) (resTp a : Expr) (k : Expr → MetaM Expr) : MetaM CodePf := do
    let (code, pA?) ← env.atom resTp a (env.liftK k)
    if !env.pf then return (code, none)
    let some pA := pA? | throwError "reflect%: internal: missing pure-atom proof"
    let Kf ← mkKf env (← inferType a) k
    if pA.isEq then
      return (code, some ⟨← env.mkSc ``sc_pure
        #[none, resTp, a, ← env.denE code, Kf, pA.e], true⟩)
    else
      return (code, some ⟨← mkAppOptM ``sc_pureE
        #[env.Op, env.SOp, none, resTp, a, ← denoteE code, Kf, pA.e], false⟩)

  /-- `bind x f`: a pure `x` is inlined via left-identity; else walk `x` with `f` reflected at each
      return point; in proof mode compose `x`'s and `f`'s equations via `sc_bind`. -/
  partial def Env.walkBind (env : Env) (resTp x f : Expr) (k : Expr → MetaM Expr) : MetaM CodePf := do
    match_expr x.consumeMData.headBeta with
    | FreeE.pure _ _ _ _ a => env.walk resTp (f.beta #[a]) k
    | Pure.pure _ _ _ a => env.walk resTp (f.beta #[a]) k
    | _ =>
      -- the code continuation at each return point of `x`: walk `f` at the bound atom (in proof
      -- mode the atom is the host value; in abstract mode a host placeholder maps to it)
      let kInner : Expr → MetaM Expr := fun xa => do
        if env.pf then
          let env' := if let .fvar fid := xa then { env with subst := (fid, xa) :: env.subst } else env
          return (← env'.walk resTp (f.beta #[xa]) k).1
        else
          let .forallE _ X _ _ := (← whnf (← inferType f))
            | throwError "reflect%: expected a continuation function{indentExpr f}"
          withLocalDeclD `h X fun hx =>
            return (← { env with subst := (hx.fvarId!, xa) :: env.subst }.walk resTp (f.beta #[hx]) k).1
      let (xcode, xpf?) ← env.walk resTp x kInner
      if !env.pf then return (xcode, none)
      let some xproof := xpf? | throwError "reflect%: internal: missing bind proof"
      let Y ← freeResult x
      let X ← forallTelescope (← inferType f) fun _ cod => do
        let_expr FreeE _ _ _ X := (← whnf cod) | throwError "reflect%: bind cont"
        pure X
      let Kf ← mkKf env X k
      let (fproofLam, fpEq) ← withLocalDeclD `r Y fun vr => do
        let env' := { env with subst := (vr.fvarId!, vr) :: env.subst }
        let (_, fp?) ← env'.walk resTp (f.beta #[vr]) k
        let some fp := fp? | throwError "reflect%: internal: missing bind-continuation proof"
        return (← mkLambdaFVars #[vr] fp.e, fp.isEq)
      if xproof.isEq && fpEq then
        -- xproof : denote xcode = bind (ofFree x) (fun r => denote (kInner r))
        let ofx ← mkAppM ``ofFree #[x]
        let hEq ← mkAppM ``funext #[fproofLam]      -- (fun r => denote (kInner r)) = (fun r => bind (ofFree (f r)) Kf)
        let compTy ← inferType (← env.denE xcode)
        let fFun ← withLocalDeclD `kk (← mkArrow Y compTy) fun kk => do
          mkLambdaFVars #[kk] (← mkAppM ``ITree.bind #[ofx, kk])
        let congrStep ← mkAppM ``congrArg #[fFun, hEq]
        let hC ← eqTransD xproof.e congrStep
        return (xcode, some ⟨← env.mkSc ``sc_bind
          #[none, none, resTp, x, f, Kf, ← env.denE xcode, hC], true⟩)
      else
        -- (★≈): the walked computation's step and the continuation's pointwise steps compose
        -- via `sc_bindE` (no `funext` fusion up to taus)
        let K1 ← mkKf env Y kInner
        let hC ← xproof.toEutt
        let ofx ← mkAppM ``ofFree #[x]
        let hC ← mkExpectedTypeHint hC
          (← mkAppM ``ITree.Eutt #[← env.denE xcode, ← mkAppM ``ITree.bind #[ofx, K1]])
        let hK ← Pf.toEuttPointwise ⟨fproofLam, fpEq⟩
        return (xcode, some ⟨← mkAppOptM ``sc_bindE
          #[env.Op, env.SOp, none, none, resTp, x, f, K1, Kf, ← env.denE xcode, hC, hK], false⟩)

  /-- `Free.op o i cont` (a DSL effect, first-order signature indices `I R : TpF`): reflect the
      continuation (binding the result atom), then the input atom wrapping the `op` node; in
      proof mode `sc_op`/`sc_opBaseC` with the continuation's IH. -/
  partial def Env.walkOp (env : Env) (resTp I R o i cont : Expr) (k : Expr → MetaM Expr) :
      MetaM CodePf := do
    let ITp := mkApp (Lean.mkConst ``TpF.tp []) I
    let RTp := mkApp (Lean.mkConst ``TpF.tp []) R
    let Rt := mkApp (Lean.mkConst ``TpF.denote []) R
    let oLift := mkApp4 (Lean.mkConst ``OpT.mk []) env.Op I R o
    let (kbody, ih?) ← withLocalDeclD `v (mkApp env.V RTp) fun vx =>
      env.withHostVar Rt vx fun hx => do
        let env' := { env with subst := (hx.fvarId!, vx) :: env.subst }
        let (rcode, rpf?) ← env'.walk resTp (cont.beta #[hx]) k
        return (← mkLambdaFVars #[vx] rcode,
                ← rpf?.mapM (fun p => do pure { p with e := ← mkLambdaFVars #[vx] p.e }))
    let (code, pI?) ← env.atom resTp i (env.liftK fun ia =>
      mkAppOptM ``Code.op #[env.Op, env.Opc, env.SOp, env.F, env.V, none, ITp, RTp,
                            env.opWrap ITp RTp oLift, ia, kbody])
    if !env.pf then return (code, none)
    let some pI := pI? | throwError "reflect%: internal: missing op-input proof"
    let some ih := ih? | throwError "reflect%: internal: missing op IH"
    let Xr ← forallTelescope (← inferType cont) fun _ cod => do
      let_expr FreeE _ _ _ X := (← whnf cod) | throwError "reflect%: op cont"
      pure X
    let Kf ← mkKf env Xr k
    let scStep : Pf ←
      if ih.isEq then
        pure ⟨← mkAppOptM (if env.recMode then ``sc_opBaseC else ``sc_op) (#[some env.Op, some env.SOp] ++ env.scx ++
          #[some I, some R, some resTp, none, some o, some i, some cont, some kbody,
            some Kf, some ih.e]), true⟩
      else do
        if env.recMode then throwError "reflect%: internal: eutt step inside a rec body"
        pure ⟨← mkAppOptM ``sc_opE
          #[env.Op, env.SOp, I, R, resTp, none, o, i, cont, kbody, Kf, ih.e], false⟩
    return (code, some (← pfTransD pI scStep))

  /-- A raw event node `FreeE.op ev cont` — the shape of a `rec_` body's lifted intermediary:
      `Sum.inl` a packaged DSL event, `Sum.inr` the self-call at the state. -/
  partial def Env.walkOpE (env : Env) (resTp ev cont : Expr) (k : Expr → MetaM Expr) :
      MetaM CodePf := do
    match_expr ev with
    | Sum.inl _ _ e => do
        let_expr Effect.mk _ I R o i := e
          | throwError "reflect%: unsupported event{indentExpr ev}"
        env.walkOp resTp I R o i cont k
    | Sum.inr _ _ st => do
        unless env.recMode do throwError "reflect%: self-call outside a rec body"
        let some (σTp, ρTp) := env.recTps
          | throwError "reflect%: internal: rec walk without state types"
        let callE := mkApp3 (Lean.mkConst ``CallOp.call [])
          (mkApp (Lean.mkConst ``OpT []) env.Op) σTp ρTp
        let hostTy := mkApp2 (Lean.mkConst ``Tp.denote []) env.Op ρTp
        let (kbody, ih?) ← withLocalDeclD `v (mkApp env.V ρTp) fun vx =>
          env.withHostVar hostTy vx fun hx => do
            let env' := { env with subst := (hx.fvarId!, vx) :: env.subst }
            let (rcode, rpf?) ← env'.walk resTp (cont.beta #[hx]) k
            return (← mkLambdaFVars #[vx] rcode,
                    ← rpf?.mapM (fun p => do pure { p with e := ← mkLambdaFVars #[vx] p.e }))
        let (code, pS?) ← env.atom resTp st (env.liftK fun sa =>
          mkAppOptM ``Code.op #[env.Op, env.Opc, env.SOp, env.F, env.V, none, σTp, ρTp,
                                callE, sa, kbody])
        if !env.pf then return (code, none)
        let some pS := pS? | throwError "reflect%: internal: missing call-input proof"
        let some ih := ih? | throwError "reflect%: internal: missing call IH"
        let Xr ← forallTelescope (← inferType cont) fun _ cod => do
          let_expr FreeE _ _ _ X := (← whnf cod) | throwError "reflect%: call cont"
          pure X
        let Kf ← mkKf env Xr k
        unless ih.isEq do throwError "reflect%: internal: eutt step inside a rec body"
        let scStep : Pf := ⟨← mkAppOptM ``sc_opCallC
          #[env.Op, env.SOp, σTp, ρTp, resTp, none, st, cont, kbody, Kf, ih.e], true⟩
        return (code, some (← pfTransD pS scStep))
    | _ => throwError "reflect%: unsupported event{indentExpr ev}"

  /-- `hop s b cont`: reflect the block (ending in `ret`), then the tail; in proof mode `sc_scope`
      composes the block's equation (`walkTop`'s `denote B = ofFree b`) with the tail's IH. -/
  partial def Env.walkScope (env : Env) (resTp β s b cont : Expr) (k : Expr → MetaM Expr) : MetaM CodePf := do
    let βTp ← reifyTpOrThrow β
    let (blockCode, blockPf?) ← env.walkTop βTp b
    let .forallE _ Xt _ _ := (← whnf (← inferType cont))
      | throwError "reflect%: expected a scope continuation{indentExpr cont}"
    let (kbody, ih?) ← withLocalDeclD `v (mkApp env.V βTp) fun vx =>
      env.withHostVar Xt vx fun hx => do
        let env' := { env with subst := (hx.fvarId!, vx) :: env.subst }
        let (rcode, rpf?) ← env'.walk resTp (cont.beta #[hx]) k
        return (← mkLambdaFVars #[vx] rcode,
                ← rpf?.mapM (fun p => do pure { p with e := ← mkLambdaFVars #[vx] p.e }))
    let code ← mkAppOptM ``Code.scope #[env.Op, env.Opc, env.SOp, env.F, env.V, none, βTp, s, blockCode, kbody]
    if !env.pf then return (code, none)
    let some hB := blockPf? | throwError "reflect%: internal: missing scope-block proof"
    let some ih := ih? | throwError "reflect%: internal: missing scope IH"
    let X ← forallTelescope (← inferType cont) fun _ cod => do
      let_expr FreeE _ _ _ X := (← whnf cod) | throwError "reflect%: scope cont"
      pure X
    let Kf ← mkKf env X k
    if hB.isEq && ih.isEq then
      return (code, some ⟨← env.mkSc ``sc_scope
        #[βTp, resTp, none, s, b, cont, blockCode, kbody, Kf, hB.e, ih.e], true⟩)
    else
      return (code, some ⟨← mkAppOptM ``sc_scopeE
        #[env.Op, env.SOp, βTp, resTp, none, s, b, cont, blockCode, kbody, Kf,
          ← hB.toEutt, ← ih.toEuttPointwise], false⟩)

  /-- `cond c t e`: reflect both arms with the same continuation, then the scrutinee atom wrapping
      the `ite` node; in proof mode `sc_cond` with both arms' IHs. -/
  partial def Env.walkIte (env : Env) (resTp c t el : Expr) (k : Expr → MetaM Expr) : MetaM CodePf := do
    let (tcode, tpf?) ← env.walk resTp t k
    let (ecode, epf?) ← env.walk resTp el k
    let (code, pC?) ← env.atom resTp c (env.liftK fun ca =>
      mkAppOptM ``Code.ite #[env.Op, env.Opc, env.SOp, env.F, env.V, none, ca, tcode, ecode])
    if !env.pf then return (code, none)
    let (some pC, some tproof, some eproof) := (pC?, tpf?, epf?)
      | throwError "reflect%: internal: missing ite proof"
    let X ← freeResult t
    let Kf ← mkKf env X k
    let scStep : Pf ←
      if tproof.isEq && eproof.isEq then
        pure ⟨← env.mkSc ``sc_cond
          #[none, resTp, c, t, el, tcode, ecode, Kf, tproof.e, eproof.e], true⟩
      else
        pure ⟨← mkAppOptM ``sc_condE
          #[env.Op, env.SOp, none, resTp, c, t, el, tcode, ecode, Kf,
            ← tproof.toEutt, ← eproof.toEutt], false⟩
    return (code, some (← pfTransD pC scStep))

  /-- A **bounded fold with an effectful body** (`Fin.foldlM n f init` over `Free`): the same
      `fold` node — the loop construct is body-agnostic — with the body reflected as a full block
      (`walkTop`: effects, scopes, anything); `sc_foldM` is its (★) step, consuming the blocks'
      pointwise `ofFree`-equations. -/
  partial def Env.walkFold (env : Env) (resTp elemTy nExpr f init : Expr) (k : Expr → MetaM Expr) :
      MetaM CodePf := do
    let aTp ← reifyTpOrThrow elemTy
    let finTp := mkApp (.const ``Tp.fin []) nExpr
    let finHostTy := mkApp (.const ``Fin []) nExpr
    let (bodyLam, hb?) ←
      withLocalDeclD `i (mkApp env.V finTp) fun vi =>
      env.withHostVar finHostTy vi fun hi =>
      withLocalDeclD `acc (mkApp env.V aTp) fun vacc =>
      env.withHostVar elemTy vacc fun hacc => do
        let env' := { env with
          subst := (hi.fvarId!, vi) :: (hacc.fvarId!, vacc) :: env.subst }
        let (bcode, bpf?) ← env'.walkTop aTp (f.beta #[hacc, hi])
        pure (← mkLambdaFVars #[vi, vacc] bcode,
              ← bpf?.mapM (fun p => do pure { p with e := ← mkLambdaFVars #[vi, vacc] p.e }))
    let kbody ← withLocalDeclD `v (mkApp env.V aTp) fun vc => do
      mkLambdaFVars #[vc] (← k vc)
    let (code, pI?) ← env.atom resTp init (env.liftK fun ainit =>
      mkAppOptM ``Code.fold #[env.Op, env.Opc, env.SOp, env.F, env.V, none, aTp, nExpr, ainit, bodyLam, kbody])
    if !env.pf then return (code, none)
    let some pI := pI? | throwError "reflect%: internal: missing fold-init proof"
    let some hb := hb? | throwError "reflect%: internal: missing fold body proof"
    let scStep : Pf ←
      if hb.isEq then
        pure ⟨← env.mkSc ``sc_foldM
          #[resTp, aTp, nExpr, init, f, bodyLam, kbody, hb.e], true⟩
      else
        pure ⟨← mkAppOptM ``sc_foldME
          #[env.Op, env.SOp, resTp, aTp, nExpr, init, f, bodyLam, kbody, hb.e], false⟩
    return (code, some (← pfTransD pI scStep))

  /-- Top-level walk (continuation `ret`, so `Kf = ret`); in proof mode close (★) with
      `bind_ret_right`, giving `denote code = ofFree e`.  `resTp` is `e`'s result `Tp`. -/
  partial def Env.walkTop (env : Env) (resTp e : Expr) : MetaM CodePf := do
    let (code, pf?) ← env.walk resTp e (env.mkRetT resTp)
    let pf? ← pf?.mapM fun proof =>
      do pfTransD proof ⟨← mkAppM ``ITree.bind_ret_right #[← mkAppM ``ofFree #[e]], true⟩
    return (code, pf?)

  /-- Try to reflect `e` (walk position, a `Free` computation) as a **call** to a top-level helper
      (`analyzeCall`), dispatching on the mode: abstract mode monomorphises and spills/resolves;
      proof mode builds the concrete subroutine with its own (★)-proof. -/
  partial def Env.tryCall (env : Env) (resTp e : Expr) (k : Expr → MetaM Expr) : MetaM (Option CodePf) := do
    if env.noSpill then return none
    if let some sig ← env.analyzeRecCall e then
      return some (← env.callRecWalk resTp sig k)
    let some sig ← analyzeCall e | return none
    let sig ← env.resolveVariant sig sigsMatch
    if env.pf then return some (← env.callWithProof resTp sig k)
    else env.callAbstract resTp sig k

  /-- A **recursive `Free` helper call** in walk position (this is also how a *recursive
      program* reflects: its `main` is exactly this call).  The state atoms tuple up and a
      single-argument `call` targets the spilled `rec_`; in proof mode the seeded `mrec`
      adequacy closes the node via `sc_callE` — an eutt step, (★≈) from here up. -/
  partial def Env.callRecWalk (env : Env) (resTp : Expr) (sig : CallSig)
      (k : Expr → MetaM Expr) : MetaM CodePf := do
    let some rd := sig.rec? | throwError "reflect%: internal: missing rec data"
    let (cf, bodyProofLam?) ←
      if env.pf then
        let (cf, bp) ← env.resolveCalleeProof sig
        pure (cf, some bp)
      else
        pure (← env.resolveCallee sig, none)
    let kcont ← withLocalDeclD `r (mkApp env.V sig.retTp) fun vr => do
      mkLambdaFVars #[vr] (← k vr)
    env.atoms resTp sig.valueArgs fun atoms => do
      env.emitTuple rd.stateTps.toList atoms fun tupAtom => do
        let argHL ← mkArgHListT env.V [tupAtom] [rd.σTp]
        let callCode ← env.emitCall cf sig.asList sig.retTp argHL k
        if !env.pf then return (callCode, none)
        let some bp := bodyProofLam?
          | throwError "reflect%: internal: missing rec-call body proof"
        let hypArgs := rd.hypPos.map (sig.fArgs[·]!)
        let hcf := bp.e.beta (#[argHL] ++ hypArgs)
        -- the source at the tuple atom's projections (tied to the source values by the
        -- enclosing pair nodes)
        let projs := (mkTupleProjs rd.stateTys.toList tupAtom).toArray
        let mut fullArgs := sig.fArgs
        for j in [0:sig.valuePos.size] do
          fullArgs := fullArgs.set! (sig.valuePos[j]!) projs[j]!
        let m ← mkAppM ``ofFree #[mkAppN sig.cValInst fullArgs]
        let scStep ← mkAppOptM ``sc_callE
          #[env.Op, env.SOp, sig.asList, sig.retTp, resTp, cf, argHL, kcont, m, hcf]
        pure (callCode, some ⟨scStep, false⟩)

  /-- Build a helper's `def_` body `fun hargs => code`: fresh value binders substituted by the
      `hargs` projections, the body walked at its result `Tp` ending in `ret` — a `Free` helper via
      `walk`, a **pure** helper via `atom`.  Bodies may themselves call (earlier-spilled) helpers. -/
  partial def Env.rebuildBody (env : Env) (sig : CallSig) : MetaM Expr := do
    let hlistTy ← mkAppM ``HList #[env.V, sig.asList]
    withLocalDeclD `args hlistTy fun hargs => do
      let decls : Array (Name × (Array Expr → MetaM Expr)) :=
        sig.argTys.map (fun ty => (`x, fun _ => pure ty))
      withLocalDeclsD decls fun hxs => do
        let mut subst := env.subst
        for j in [0:hxs.size] do
          subst := (hxs[j]!.fvarId!, ← projHList hargs j) :: subst
        let mut fullArgs := sig.fArgs
        for j in [0:sig.valuePos.size] do
          fullArgs := fullArgs.set! (sig.valuePos[j]!) hxs[j]!
        let env' := { env with subst }
        let body := sig.cValInst.beta fullArgs
        let bcode ←
          if sig.isPure then
            Prod.fst <$> env'.atom sig.retTp body (env'.liftK (env'.mkRetT sig.retTp))
          else
            Prod.fst <$> env'.walk sig.retTp body (env'.mkRetT sig.retTp)
        mkLambdaFVars #[hargs] bcode

  /-- Resolve a call's `F`-name.  Build pass: look it up among the bound `def_` binders (bodies see
      only *earlier* binders — guaranteed by discovery post-order).  Discovery pass: walk the callee
      body once (discarded — its own callees spill first, giving the dependency order), record the
      signature, and emit a fresh mvar (the discovery code is thrown away). -/
  partial def Env.resolveCallee (env : Env) (sig : CallSig) : MetaM Expr := do
    match env.resolved with
    | some resolved =>
        let some (_, cf) ← resolved.findM? (fun d => sigsMatch d.1 sig)
          | throwError "reflect%: internal: unresolved helper `{sig.cName}` (dependency order)"
        return cf
    | none =>
        unless (← (← env.defs.get).findM? (sigsMatch · sig)).isSome do
          if sig.rec?.isSome then
            -- a recursive helper's body inlines its own callees (`noSpill`): nothing to discover
            env.defs.modify (·.push sig)
          else
            if (← env.inFlight.get).contains sig.cName then
              throwError "reflect%: recursive helper `{sig.cName}` cannot be spilled — only \
                          structural `0`/`succ` recursion at a `Nat` argument is supported"
            env.inFlight.modify (·.push sig.cName)
            let sig ←
              try
                let _ ← env.rebuildBody sig       -- discovery: callees push first (post-order)
                pure sig
              catch e =>
                -- a body that reaches a recursion must *specialize* over its function
                -- arguments: demote them to monomorphisation and retry
                if sig.fnArgPos.isEmpty then
                  env.inFlight.modify (·.filter (· != sig.cName))
                  throw e
                let some sig' ← (try some <$> sig.demoteFnArgs env catch _ => pure none)
                  | env.inFlight.modify (·.filter (· != sig.cName)); throw e
                try
                  let _ ← env.rebuildBody sig'
                  pure sig'
                catch _ =>
                  env.inFlight.modify (·.filter (· != sig.cName))
                  throw e
            env.inFlight.modify (·.filter (· != sig.cName))
            env.defs.modify (·.push sig)
        mkFreshExprMVar (mkApp2 env.F sig.asList sig.retTp)

  /-- Abstract-mode `Free`-helper call: resolve the `F`-name, reflect the arguments, emit `call`. -/
  partial def Env.callAbstract (env : Env) (resTp : Expr) (sig : CallSig) (k : Expr → MetaM Expr) :
      MetaM (Option CodePf) := do
    let cf ← env.resolveCallee sig
    let r ← env.atoms resTp sig.valueArgs (fun atoms => do
      pure (← env.emitCall cf sig.asList sig.retTp (← env.mkArgHList atoms) k, none))
    return some r

  /-- Proof-mode resolution: the helper's concrete subroutine `cf` and its parametric equation
      (`∀ hargs, cf hargs = ofFree …` for a `Free` helper, `… = ret …` for a pure one) — built
      **once** per monomorphised signature (`pfDefs`), reused at every call site.  Bodies are walked
      with fresh *identity*-mapped value vars `pvs` (so `atom`'s `atom = value`), then substituted
      by `projHList hargs` — matching `g`'s spilled `def_` body. -/
  partial def Env.resolveCalleeProof (env : Env) (sig : CallSig) : MetaM (Expr × Pf) := do
    let entryMatches (d : PfDefEntry) : MetaM Bool := do
      unless d.name == sig.cName && d.key.size == sig.monoArgs.size do return false
      unless (← isDefEq d.asList sig.asList) && (← isDefEq d.retTp sig.retTp) do return false
      for (a, b) in d.key.zip sig.monoArgs do
        unless ← isDefEq a b do return false
      return true
    if let some d ← (← env.pfDefs.get).findM? entryMatches then
      return (d.cf, ⟨d.bodyProof, d.bodyProofEq⟩)
    if sig.rec?.isSome then
      throwError "reflect%: internal: recursive helper `{sig.cName}`'s adequacy was not seeded"
    if (← env.inFlight.get).contains sig.cName then
      throwError "reflect%: recursive helper `{sig.cName}` cannot be spilled — only top-level \
                  structural recursion is supported"
    env.inFlight.modify (·.push sig.cName)
    try
      let hlistTy ← mkAppM ``HList #[env.V, sig.asList]
      let (cf, bodyProofLam) ← withLocalDeclD `args hlistTy fun hargs => do
        let decls : Array (Name × (Array Expr → MetaM Expr)) :=
          sig.argTys.map (fun ty => (`x, fun _ => pure ty))
        withLocalDeclsD decls fun pvs => do
          -- a *function-typed* value argument gets a separate object-level atom (a Kleisli
          -- binder): the host `pv` carries the source side of the equation, the atom `pa` the
          -- code side; app-steps relate them by *deferred* hints, so both stay abstract until a
          -- call site instantiates them consistently
          let fnAtomDecls : Array (Name × (Array Expr → MetaM Expr)) :=
            sig.fnArgPos.map (fun i => (`fa, fun _ => pure (mkApp env.V sig.argTps[i]!)))
          withLocalDeclsD fnAtomDecls fun pas => do
          let mut subst := env.subst
          let mut atomOf : Array Expr := #[]
          for i in [0:pvs.size] do
            if let some fi := sig.fnArgPos.findIdx? (· == i) then
              subst := (pvs[i]!.fvarId!, pas[fi]!) :: subst
              atomOf := atomOf.push pas[fi]!
            else
              subst := (pvs[i]!.fvarId!, pvs[i]!) :: subst
              atomOf := atomOf.push pvs[i]!
          let mut fullArgs := sig.fArgs
          for j in [0:sig.valuePos.size] do fullArgs := fullArgs.set! (sig.valuePos[j]!) pvs[j]!
          let env' := { env with subst }
          let body := sig.cValInst.beta fullArgs
          let (bcode, bpf?) ←
            if sig.isPure then
              env'.atom sig.retTp body (env'.liftK (env'.mkRetT sig.retTp))
            else
              env'.walkTop sig.retTp body
          let some bproof := bpf? | throwError "reflect%: internal: missing call-body proof"
          let mut projs : Array Expr := #[]
          for j in [0:pvs.size] do projs := projs.push (← projHList hargs j)
          let bcode' := bcode.replaceFVars atomOf projs
          let bproof' := bproof.e.replaceFVars atomOf projs
          -- the fn *hosts* stay abstracted (trailing binders): a call site betas them with its
          -- actual source lambdas
          let fnHosts := sig.fnArgPos.map (pvs[·]!)
          pure (← mkLambdaFVars #[hargs] (← denoteE bcode'),
                Pf.mk (← mkLambdaFVars (#[hargs] ++ fnHosts) bproof') bproof.isEq)
      env.pfDefs.modify (·.push { name := sig.cName, asList := sig.asList, retTp := sig.retTp,
                                  cf, bodyProof := bodyProofLam.e, bodyProofEq := bodyProofLam.isEq,
                                  key := sig.monoArgs })
      return (cf, bodyProofLam)
    finally
      env.inFlight.modify (·.filter (· != sig.cName))

  /-- Proof-mode `Free`-helper call: reflect the arguments, then `sc_call` — the helper's soundness
      `hcf : cf args = ofFree (helper args)` composes with the caller's continuation. -/
  partial def Env.callWithProof (env : Env) (resTp : Expr) (sig : CallSig) (k : Expr → MetaM Expr) :
      MetaM CodePf := do
    let (cf, bodyProofLam) ← env.resolveCalleeProof sig
    let kcont ← withLocalDeclD `r (mkApp env.V sig.retTp) fun vr => do mkLambdaFVars #[vr] (← k vr)
    env.atoms resTp sig.valueArgs fun atoms => do
      let argHList ← mkArgHListT env.V atoms sig.argTps.toList
      let callCode ← env.emitCall cf sig.asList sig.retTp argHList k
      let fnSrcs := sig.fnArgPos.map (fun i => sig.valueArgs.toArray[i]!)
      let hcf := bodyProofLam.e.beta (#[argHList] ++ fnSrcs)
      -- `m = ofFree (helper applied to *these* atoms)` — matches `hcf`'s RHS; a bin/get argument's
      -- atom is a bound var here, later instantiated to the source value (so `m` becomes `ofFree e`);
      -- function arguments use the *source* lambda (matching the body proof's host side)
      let mut fullArgs := sig.fArgs
      for j in [0:sig.valuePos.size] do
        unless sig.fnArgPos.contains j do
          fullArgs := fullArgs.set! (sig.valuePos[j]!) atoms.toArray[j]!
      let m ← mkAppM ``ofFree #[sig.cValInst.beta fullArgs]
      if bodyProofLam.isEq then
        let scStep ← mkAppOptM ``sc_call
          #[env.Op, env.SOp, sig.asList, sig.retTp, resTp, cf, argHList, kcont, m, hcf]
        pure (callCode, some ⟨scStep, true⟩)
      else
        let scStep ← mkAppOptM ``sc_callE
          #[env.Op, env.SOp, sig.asList, sig.retTp, resTp, cf, argHList, kcont, m, hcf]
        pure (callCode, some ⟨scStep, false⟩)

  /-- Chain of `bin .pair` nodes assembling the right-nested tuple of already-reflected atoms;
      the tuple atom feeds `k` (proof-mode steps are definitional — `Bin.denote .pair`). -/
  partial def Env.emitTuple (env : Env) (tps : List Expr) (atoms : List Expr)
      (k : Expr → MetaM CodePf) : MetaM CodePf :=
    match tps, atoms with
    | [_], [a] => k a
    | t :: ts, a :: as =>
        env.emitTuple ts as fun tailAtom => do
          let bTp := prodTpOf ts
          let cTp := mkApp2 (.const ``Tp.prod []) t bTp
          let pairOp := mkApp2 (.const ``Bin.pair []) t bTp
          withLocalDeclD `p (mkApp env.V cTp) fun vp => do
            let (kcode, kpf?) ← k vp
            let node ← mkAppOptM ``Code.bin
              #[env.Op, env.Opc, env.SOp, env.F, env.V, none, none, none, none, pairOp, a, tailAtom,
                ← mkLambdaFVars #[vp] kcode]
            let pf? ← kpf?.mapM fun kp =>
              return { kp with
                e := kp.e.replaceFVar vp (← mkAppOptM ``Bin.denote #[env.Op, none, none, none, pairOp, a, tailAtom]) }
            return (node, pf?)
    | _, _ => throwError "reflect%: internal: tuple arity mismatch"

  /-- A **function value**: reflect the lambda's body as a suspended block (`Code.lam`).  The
      body is walked as ordinary code (a pure body wraps in `pure`); in proof mode `sc_lam`
      identifies the suspended Kleisli arrow with the source's embedding `ofFree ∘ f`, and the
      continuation is instantiated at that embedding. -/
  partial def Env.emitLam (env : Env) (resTp a : Expr) (k : Expr → MetaM CodePf) :
      MetaM CodePf := do
    if env.recMode then
      throwError "reflect%: a function value inside a recursive body is not supported{indentExpr a}"
    let fnTp ← reifyTpOrThrow (← inferType a)
    let (aTp, bTp) ← do
      match_expr fnTp with
      | Tp.fn x y => pure (x, y)
      | _ => throwError "reflect%: not a function type{indentExpr fnTp}"
    let .lam _ dom _ _ := a | throwError "reflect%: expected a lambda{indentExpr a}"
    -- the Free-valued source: the lambda itself, or its pure body wrapped in `pure`
    let bodyIsFree ← withLocalDeclD `x dom fun x => do
      pure ((← whnf (← inferType (a.beta #[x]))).isAppOf ``FreeE)
    let fW ←
      if bodyIsFree then pure a
      else withLocalDeclD `x dom fun x => do
        mkLambdaFVars #[x] (← mkAppOptM ``FreeE.pure
          #[mkApp (Lean.mkConst ``Effect []) env.Op,
            mkApp (Lean.mkConst ``Effect.arity []) env.Op, env.SOp, none, a.beta #[x]])
    let (bodyLam, hb?) ←
      withLocalDeclD `x (mkApp env.V aTp) fun vx =>
      env.withHostVar dom vx fun hx => do
        let env' := { env with subst := (hx.fvarId!, vx) :: env.subst }
        let (bcode, bpf?) ← env'.walkTop bTp (fW.beta #[hx])
        pure (← mkLambdaFVars #[vx] bcode,
              ← bpf?.mapM (fun p => do pure { p with e := ← mkLambdaFVars #[vx] p.e }))
    withLocalDeclD `v (mkApp env.V fnTp) fun vc => do
      let (kcode, kpf?) ← k vc
      let klam ← mkLambdaFVars #[vc] kcode
      let node ← mkAppOptM ``Code.lam
        #[env.Op, env.Opc, env.SOp, env.F, env.V, none, aTp, bTp, bodyLam, klam]
      let pf? ← kpf?.mapM fun kp => do
        let some hb := hb? | throwError "reflect%: internal: missing lambda body proof"
        unless hb.isEq do
          throwError "reflect%: a function value's body may not call a recursive helper"
        let scStep ← env.mkSc ``sc_lam #[aTp, bTp, resTp, fW, bodyLam, klam, hb.e]
        let emb ← withLocalDeclD `x dom fun x => do
          mkLambdaFVars #[x] (← mkAppM ``ofFree #[fW.beta #[x]])
        pfTransD ⟨scStep, true⟩ { kp with e := kp.e.replaceFVar vc emb }
      return (node, pf?)

  /-- First-class **application** `f x …` (an atom-mapped function head): one `Code.app` node
      per (curried) argument.  In proof mode the arrow's return equation is **deferred**: an
      `id`-hinted `rfl` whose type becomes definitional only once the enclosing nodes
      instantiate the function atom with its source embedding — the kernel checks the spliced,
      fully-instantiated proof. -/
  partial def Env.emitApps (env : Env) (resTp head : Expr) (args : Array Expr)
      (k : Expr → MetaM CodePf) : MetaM CodePf := do
    let εE := mkApp (Lean.mkConst ``Effect []) env.Op
    let arityE := mkApp (Lean.mkConst ``Effect.arity []) env.Op
    let rec go (fa src : Expr) (i : Nat) : MetaM CodePf := do
      if i >= args.size then k fa
      else do
        let x := args[i]!
        let fnTp ← reifyTpOrThrow (← inferType src)
        let (aTp, bTp) ← do
          match_expr fnTp with
          | Tp.fn u v => pure (u, v)
          | _ => throwError "reflect%: over-application of a function value{indentExpr src}"
        let _ := aTp
        env.atom resTp x fun xa => do
          let src' := mkApp src x
          withLocalDeclD `v (mkApp env.V bTp) fun vc => do
            let (kcode, kpf?) ← go vc src' (i+1)
            let klam ← mkLambdaFVars #[vc] kcode
            let node ← mkAppOptM ``Code.app
              #[env.Op, env.Opc, env.SOp, env.F, env.V, none, aTp, bTp, fa, xa, klam]
            let pf? ← kpf?.mapM fun kp => do
              let bden := mkApp2 (Lean.mkConst ``Tp.denote []) env.Op bTp
              let retV ← mkAppOptM ``ITree.ret #[εE, arityE, bden, src']
              let hfTy ← mkEq (mkApp fa xa) retV
              -- **deferred**: the hint's type becomes definitional once the enclosing nodes
              -- instantiate the atoms (the fn atom with its embedding) — the kernel checks the
              -- spliced, fully-instantiated proof
              let hf ← mkExpectedTypeHint (← mkEqRefl (mkApp fa xa)) hfTy
              let scStep ← env.mkSc ``sc_app #[aTp, bTp, resTp, fa, xa, none, klam, hf]
              pfTransD ⟨scStep, true⟩ { kp with e := kp.e.replaceFVar vc src' }
            return (node, pf?)
    env.atom resTp head fun fa => go fa head 0

  /-- A **recursive pure helper call** in atom position: the state atoms tuple up (`bin .pair`
      nodes) and a single-argument `call` targets the spilled `rec_`.  In proof mode the helper's
      seeded adequacy (`mrec … ≈ ret (source …)`) closes the node via `sc_callPureE` — an *eutt*
      step, weakening the invariant to (★≈) from here up. -/
  partial def Env.emitCallRec (env : Env) (resTp : Expr) (sig : CallSig) (rd : RecData)
      (k : Expr → MetaM CodePf) : MetaM CodePf := do
    let (cf, bodyProofLam?) ←
      if env.pf then
        let (cf, bp) ← env.resolveCalleeProof sig
        pure (cf, some bp)
      else
        pure (← env.resolveCallee sig, none)
    env.atoms resTp sig.valueArgs fun atoms => do
      env.emitTuple rd.stateTps.toList atoms fun tupAtom => do
        let argHL ← mkArgHListT env.V [tupAtom] [rd.σTp]
        withLocalDeclD `v (mkApp env.V sig.retTp) fun vc => do
          let (kcode, kpf?) ← k vc
          let klam ← mkLambdaFVars #[vc] kcode
          let node ← mkAppOptM ``Code.call
            #[env.Op, env.Opc, env.SOp, env.F, env.V, none, sig.asList, sig.retTp, cf, argHL, klam]
          let pf? ← kpf?.mapM fun kp => do
            let some bp := bodyProofLam?
              | throwError "reflect%: internal: missing rec-call body proof"
            let hypArgs := rd.hypPos.map (sig.fArgs[·]!)
            -- invariant fn components: the equation's host binders take the *source* functions
            let fnSrcs := (sig.valueArgs.take rd.fnStateCount).toArray
            let hcf := bp.e.beta (fnSrcs ++ #[argHL] ++ hypArgs)
            let scStep ← mkAppOptM ``sc_callPureE
              #[env.Op, env.SOp, sig.asList, sig.retTp, resTp, cf, argHL, none, klam, hcf]
            -- the source at the tuple atom's projections (the atom is a bound var, tied to the
            -- source values by the enclosing pair nodes); fn components use the source function
            let projs := (mkTupleProjs rd.stateTys.toList tupAtom).toArray
            let mut fullArgs := sig.fArgs
            for j in [0:sig.valuePos.size] do
              unless j < rd.fnStateCount do
                fullArgs := fullArgs.set! (sig.valuePos[j]!) projs[j]!
            pfTransD ⟨scStep, false⟩
              { kp with e := kp.e.replaceFVar vc (mkAppN sig.cValInst fullArgs) }
          return (node, pf?)

  /-- A **pure helper call** in atom position — definitions are *kept folded*: the helper spills as
      a `def_` and a `call` node binds its result atom.  In proof mode the helper's own memoized
      equation closes the step via `sc_callPure`. -/
  partial def Env.emitCallPure (env : Env) (resTp : Expr) (sig : CallSig)
      (k : Expr → MetaM CodePf) : MetaM CodePf := do
    if let some rd := sig.rec? then
      return ← env.emitCallRec resTp sig rd k
    let (cf, bodyProofLam?) ←
      if env.pf then
        let (cf, bp) ← env.resolveCalleeProof sig
        pure (cf, some bp)
      else
        pure (← env.resolveCallee sig, none)
    env.atoms resTp sig.valueArgs fun atoms => do
      let argHList ← mkArgHListT env.V atoms sig.argTps.toList
      withLocalDeclD `v (mkApp env.V sig.retTp) fun vc => do
        let (kcode, kpf?) ← k vc
        let klam ← mkLambdaFVars #[vc] kcode
        let node ← mkAppOptM ``Code.call
          #[env.Op, env.Opc, env.SOp, env.F, env.V, none, sig.asList, sig.retTp, cf, argHList, klam]
        let pf? ← kpf?.mapM fun kp => do
          let some bodyProofLam := bodyProofLam?
            | throwError "reflect%: internal: missing pure-call body proof"
          let fnSrcs := sig.fnArgPos.map (fun i => sig.valueArgs.toArray[i]!)
          let hcf := bodyProofLam.e.beta (#[argHList] ++ fnSrcs)
          let scStep : Pf ←
            if bodyProofLam.isEq then
              pure ⟨← mkAppOptM ``sc_callPure
                #[env.Op, env.SOp, sig.asList, sig.retTp, resTp, cf, argHList, none, klam, hcf],
                true⟩
            else
              pure ⟨← mkAppOptM ``sc_callPureE
                #[env.Op, env.SOp, sig.asList, sig.retTp, resTp, cf, argHList, none, klam, hcf],
                false⟩
          -- the value at *these* atoms (bound vars tied to sources by the enclosing nodes);
          -- function arguments use the *source* lambda (matching the body proof's host side)
          let mut fullArgs := sig.fArgs
          for j in [0:sig.valuePos.size] do
            unless sig.fnArgPos.contains j do
              fullArgs := fullArgs.set! (sig.valuePos[j]!) atoms.toArray[j]!
          pfTransD scStep { kp with e := kp.e.replaceFVar vc (sig.cValInst.beta fullArgs) }
        return (node, pf?)
end

/-- Walk the helper's telescope with: monomorphisation positions ↦ their baked values, state
    positions ↦ `stateVals` (by state index), hypotheses ↦ fresh binders — `k hypBinders
    fullValues` runs inside. -/
partial def withRecTelescope {α} (shape : RecShape) (cName : Name) (fnConst : Expr)
    (fArgs : Array Expr) (stateVals : Array Expr)
    (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  let some ci := (← getEnv).find? cName
    | throwError "reflect%: internal: missing definition {cName}"
  let ty := ci.type.instantiateLevelParams ci.levelParams fnConst.constLevels!
  let rec go (j : Nat) (curTy : Expr) (hypBs vals : Array Expr) : MetaM α := do
    if j == shape.arity then k hypBs vals
    else
      let .forallE nm dom body bi := (← whnf curTy)
        | throwError "reflect%: internal: telescope mismatch for {cName}"
      if shape.hypPos.contains j then
        withLocalDecl nm bi dom fun h =>
          go (j+1) (body.instantiate1 h) (hypBs.push h) (vals.push h)
      else
        let v := if let some si := shape.statePos.findIdx? (· == j) then stateVals[si]!
                 else fArgs[j]!
        go (j+1) (body.instantiate1 v) hypBs (vals.push v)
  go 0 ty #[] #[]

open Lean.Elab.Term in
/-- After the discovery pass: ❶ discharge the queued totalization obligations (`omega`/`decide`),
    then ❷ for every discovered **recursive helper** build its reflected `rec_` body (shared by
    the abstract build and proof mode — their definitional equality relies on it), its `mrec`
    adequacy (`recSound`: `hspec` by a proof-mode walk of the lifted body, `hrun`/`hcl` by
    generated case tactics), the totalization `bridge` (generated induction, closing by `rfl`
    thanks to `Nat.rec` iota + proof irrelevance), and seed the proof-mode cache with the
    call-site equation `∀ args hyps, cf args ≈ ret (source … hyps)`. -/
def elabRecKits (Op SOp : Expr) (defs : IO.Ref (Array CallSig))
    (pfDefs : IO.Ref (Array PfDefEntry)) (inFlight : IO.Ref (Array Name))
    (pending : IO.Ref (Array MVarId)) (recVerdicts : IO.Ref (List (Name × Bool)))
    (recBodies : IO.Ref (Array (CallSig × Expr))) : TermElabM Unit := do
  -- ❶ totalization obligations
  for m in (← pending.get) do
    unless ← m.isAssigned do
      let ty ← instantiateMVars (← m.getType)
      let prf ← elabTermEnsuringType (← `(by intros; first | omega | decide | trivial)) (some ty)
      m.assign prf
  pending.set #[]
  let denoteV := mkApp (Lean.mkConst ``Tp.denote []) Op
  let tpTy := (.const ``Tp [] : Expr)
  let fTy ← mkArrow (← mkAppM ``List #[tpTy]) (← mkArrow tpTy (mkSort (.succ .zero)))
  let vTy ← mkArrow tpTy (mkSort (.succ .zero))
  for sig in (← defs.get) do
    let some rd := sig.rec? | continue
    let some shape ← analyzeRecShape sig.cName
      | throwError "reflect%: internal: lost recursion shape for {sig.cName}"
    let cb ← instantiateMVars rd.cb
    let goT ← instantiateMVars rd.goT
    let μE ← instantiateMVars rd.μ
    let σTy := rd.σTy
    let ρTy := rd.ρTy
    let ρTp := sig.retTp
    let hasHyps := !rd.hypPos.isEmpty
    -- the call-extended vocabulary/events of this monomorphisation
    let opcBase := mkApp (Lean.mkConst ``OpT []) Op
    let opcExt := mkApp3 (Lean.mkConst ``CallOp []) opcBase rd.σTp ρTp
    let wrapBase := fun (iT rT o : Expr) =>
      mkApp6 (Lean.mkConst ``CallOp.base []) opcBase rd.σTp ρTp iT rT o
    let kcExt ← mkAppM ``KCC #[Op, rd.σTp, ρTp]
    let denC ← mkAppOptM ``denoteC
      #[Op, opcExt, SOp, mkApp denoteV rd.σTp, mkApp denoteV ρTp,
        ← mkAppM ``Inj.withCall #[← mkAppM ``injD #[Op], rd.σTp, ρTp]]
    -- **invariant fn state**: everything below is built under pure-host binders (abstracted
    -- into the stored equation at the end); the adequacy is relativized to states whose fn
    -- component is the host's embedding
    let fnCount := rd.fnStateCount
    let εEK := mkApp (Lean.mkConst ``Effect []) Op
    let arityEK := mkApp (Lean.mkConst ``Effect.arity []) Op
    let hostDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
      (Array.range fnCount).map fun i =>
        (Name.mkSimple s!"f{i}", fun _ => pure rd.fnHostTys[i]!)
    let _ : Unit ← withLocalDeclsD hostDecls fun hosts => do
      let embs ← hosts.mapM (fun h => (mkEmbOf εEK arityEK h : MetaM Expr))
      let cbH := (cb.beta (hosts ++ embs)).headBeta
      let goTH := (goT.beta hosts).headBeta
      let Papp ← withLocalDeclD `sv σTy fun sv => do
        if fnCount == 0 then mkLambdaFVars #[sv] (Lean.mkConst ``True)
        else mkLambdaFVars #[sv] (← mkEq (← mkAppM ``Prod.fst #[sv]) embs[0]!)
      -- the shared `rec_` body, parametric in the value/function representations; the fn state
      -- component is projected to an atom up front, the host bound to it
      let recBody ← withLocalDeclD `V0 vTy fun Vp0 => withLocalDeclD `F' fTy fun F' =>
        withLocalDeclD `arg (mkApp Vp0 rd.σTp) fun argAtom => do
          let codeT ← withLocalDeclD `s σTy fun s => do
            let envB : Env := { Op, Opc := opcExt, opWrap := wrapBase, SOp, F := F', V := Vp0,
                                subst := [(s.fvarId!, argAtom)], defs, pfDefs, inFlight,
                                pending, recVerdicts, recBodies, noSpill := true,
                                recMode := true, recTps := some (rd.σTp, ρTp) }
            if fnCount == 0 then
              Prod.fst <$> envB.walk ρTp (cbH.beta #[s]) (envB.mkRetT ρTp)
            else
              -- `kf` stands in for the embedding in self-call tuples (a lambda cannot be an
              -- atom inside a rec body); both it and the host route to the projected atom
              withLocalDeclD `kf rd.stateTys[0]! fun kf => do
              let src := ((cb.beta (hosts ++ #[kf])).headBeta).beta #[s]
              Prod.fst <$> envB.atom ρTp (← mkAppM ``Prod.fst #[s]) (fun fa => do
                let envB2 := { envB with
                  subst := (hosts[0]!.fvarId!, fa) :: (kf.fvarId!, fa) :: envB.subst }
                envB2.walk ρTp src (envB2.mkRetT ρTp))
          mkLambdaFVars #[Vp0, F', argAtom] codeT
      recBodies.modify (·.push (sig, recBody))
      let bodyCode := recBody.beta #[denoteV, kcExt]
      -- (hspec is built below, after the component-form machinery)
      -- the total source over the tupled state: `goT` when the source is hypothesis-guarded,
      -- else the source itself; fn components enter as the pure hosts (the σ-slot is ignored);
      -- a pure result wraps in `pure`
      let fW ← withLocalDeclD `s σTy fun s => do
        let projs := (mkTupleProjs rd.stateTys.toList s).toArray
        let src ←
          if hasHyps then pure (mkApp goTH s)
          else do
            let mut fullArgs := sig.fArgs
            for j in [0:sig.valuePos.size] do
              fullArgs := fullArgs.set! (sig.valuePos[j]!)
                (if j < fnCount then hosts[j]! else projs[j]!)
            pure (mkAppN sig.cValInst fullArgs)
        if sig.isPure then
          mkLambdaFVars #[s] (← mkAppOptM ``FreeE.pure
            #[mkApp (Lean.mkConst ``Effect []) Op, mkApp (Lean.mkConst ``Effect.arity []) Op,
              SOp, rd.ρValTy, src])
        else
          mkLambdaFVars #[s] src
      -- hrun/hcl: proved in *component* form (plain `intro`s, no tuple patterns; fn slots are
      -- the hosts' embeddings, literally), repackaged over the tupled `N` under the invariant
      -- (`fst_eq_tuple` pins the fn component; surjective pairing is definitional for the rest)
      let kSt := rd.stateTps.size
      let compIds := ((Array.range kSt).filter (· ≥ fnCount)).map fun i =>
        mkIdent (Name.mkSimple s!"c{i}")
      let recId := mkIdent (Name.mkSimple s!"c{rd.recIdx}")
      let stateDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
        ((Array.range kSt).filter (· ≥ fnCount)).map fun i =>
          (Name.mkSimple s!"c{i}", fun _ => pure rd.stateTys[i]!)
      let repackage (component : Expr) (want : Expr → MetaM Expr) : MetaM Expr :=
        withLocalDeclD `N σTy fun N =>
        withLocalDeclD `hP (mkApp Papp N) fun hP => do
          if fnCount == 0 then
            let projs := (mkTupleProjs rd.stateTys.toList N).toArray
            mkLambdaFVars #[N, hP] (← mkExpectedTypeHint (mkAppN component projs) (← want N))
          else do
            -- `N = (emb f₀, N.2)` by the invariant; the component instance is at the
            -- projections of `N.2` (η-definitional)
            let tupleEq ← mkAppM ``fst_eq_tuple #[hP]
            let sndN ← mkAppM ``Prod.snd #[N]
            let restProjs := (mkTupleProjs rd.stateTys.toList.tail sndN).toArray
            let stmtOf ← withLocalDeclD `sv σTy fun sv => do
              mkLambdaFVars #[sv] (← want sv)
            let congr ← mkAppM ``congrArg #[stmtOf, tupleEq]
            mkLambdaFVars #[N, hP] (← mkAppM ``Eq.mpr #[congr, mkAppN component restProjs])
      -- hspec: compositional (proof-mode walk of `cb`) at the **literal invariant state**
      -- `⟨emb f₀, cs⟩` — projection/application steps reduce definitionally there — then
      -- repackaged under `P`
      let hspecPrf ← do
        let comp ← withLocalDeclsD stateDecls fun cs => do
          let tup := mkTupleE rd.stateTys.toList (embs.toList ++ cs.toList)
          let penv : Env := { Op, Opc := opcExt, opWrap := wrapBase, SOp, F := kcExt,
                              V := denoteV, subst := [], defs, pfDefs, inFlight,
                              pending, recVerdicts, recBodies, noSpill := true, pf := true,
                              recMode := true, recTps := some (rd.σTp, ρTp) }
          let (_, pf?) ←
            if fnCount == 0 then penv.walkTop ρTp (cbH.beta #[tup])
            else
              -- walk at the **kf-tuple** (the embedding stand-in is an unmapped fvar, so
              -- projections stay closed and feed through directly); the kernel reconciles the
              -- shape difference against `bodyCode` by beta/iota at the literal state
              withLocalDeclD `kf rd.stateTys[0]! fun kf => do
              let tupK := mkTupleE rd.stateTys.toList (#[kf] ++ cs).toList
              let src := ((cb.beta (hosts ++ #[kf])).headBeta).beta #[tupK]
              -- the components self-map so the walk makes the *same* reification choices as
              -- the abstract walk at a symbolic state (partial ops must line up)
              let csSelf := cs.toList.map fun c => (c.fvarId!, c)
              let penv2 := { penv with subst :=
                (hosts[0]!.fvarId!, kf) :: (csSelf ++ penv.subst) }
              let r ← penv2.walkTop ρTp src
              -- restore the embedding for the walking device in the built proof
              pure (r.1, r.2.map fun pf =>
                { pf with e := pf.e.replaceFVar kf embs[0]! })
          let some proof := pf? | throwError "reflect%: internal: rec hspec produced no proof"
          unless proof.isEq do throwError "reflect%: internal: rec hspec must be an equality"
          let want ← mkEq (mkApp2 denC ρTp (mkApp bodyCode tup))
            (← mkAppM ``ofFree #[mkApp cbH tup])
          mkLambdaFVars cs (← mkExpectedTypeHint proof.e want)
        repackage comp fun N => do
          mkEq (mkApp2 denC ρTp (mkApp bodyCode N)) (← mkAppM ``ofFree #[mkApp cbH N])
      let hrunPrf ← do
        let stmt ← withLocalDeclsD stateDecls fun cs => do
          let tup := mkTupleE rd.stateTys.toList (embs.toList ++ cs.toList)
          mkForallFVars cs (← mkEq (← mkAppM ``runSrc #[fW, mkApp cbH tup]) (mkApp fW tup))
        let tac ← `(by intro $[$compIds]*
                       rcases $recId:ident with _ | m <;>
                         first | rfl | exact Freigen.Free.bind_pure _)
        let comp ← elabTermEnsuringType tac (some stmt)
        repackage comp fun N => do
          mkEq (← mkAppM ``runSrc #[fW, mkApp cbH N]) (mkApp fW N)
      let hclPrf ← do
        let stmt ← withLocalDeclsD stateDecls fun cs => do
          let tup := mkTupleE rd.stateTys.toList (embs.toList ++ cs.toList)
          mkForallFVars cs
            (← mkAppM ``callsLtP #[μE, Papp, mkApp μE tup, mkApp cbH tup])
        let tac ← `(by intro $[$compIds]*
                       rcases $recId:ident with _ | m <;>
                         (repeat' first | apply And.intro | intro _) <;>
                         (try simp only []) <;> (first | omega | rfl | trivial))
        let comp ← elabTermEnsuringType tac (some stmt)
        repackage comp fun N => mkAppM ``callsLtP #[μE, Papp, mkApp μE N, mkApp cbH N]
      -- the totalization bridge: `goT ⟨states⟩ = source states hyps` (induction on the recursion
      -- component; each case is `rfl`-strength — `Nat.rec` iota + the source's own equation +
      -- proof irrelevance across the differing `Fin.mk` proofs).  Only needed when hypotheses
      -- exist (else `fW` *is* the source).
      let bridgePrf ← if !hasHyps then pure (Expr.const ``Unit.unit []) else do
        let stmt ← withLocalDeclsD stateDecls fun cs => do
          withRecTelescope shape sig.cName sig.cValInst sig.fArgs (hosts ++ cs) fun hs vals => do
            let tup := mkTupleE rd.stateTys.toList (embs.toList ++ cs.toList)
            mkForallFVars (cs ++ hs) (← mkEq (mkApp goTH tup) (mkAppN sig.cValInst vals))
        let cId := mkIdent sig.cName
        let hypIds := (Array.range rd.hypPos.size).map fun i => mkIdent (Name.mkSimple s!"h{i}")
        let otherIds := ((Array.range kSt).filter (· ≥ fnCount)).filterMap fun i =>
          if i == rd.recIdx then none else some (mkIdent (Name.mkSimple s!"c{i}"))
        let introHyps : Array (TSyntax `tactic) ←
          if hypIds.isEmpty then pure #[] else pure #[← `(tactic| intro $[$hypIds]*)]
        let zeroSeq ← `(Lean.Parser.Tactic.tacticSeq|
          $[$introHyps]*
          first | rfl | rw [$cId:ident])
        let succSeq ← `(Lean.Parser.Tactic.tacticSeq|
          $[$introHyps]*
          rw [$cId:ident]
          first | apply ih | rfl)
        let tac ←
          if otherIds.isEmpty then
            `(by intro $[$compIds]*
                 induction $recId:ident with
                 | zero => $zeroSeq
                 | succ m ih => $succSeq)
          else
            `(by intro $[$compIds]*
                 induction $recId:ident generalizing $[$otherIds]* with
                 | zero => $zeroSeq
                 | succ m ih => $succSeq)
        elabTermEnsuringType tac (some stmt)
      -- `mrec` adequacy at this monomorphisation, and the call-site subroutine + equation
      let recSoundApp ← mkAppOptM ``recSoundP
        #[Op, SOp, rd.σTp, ρTp, μE, Papp, bodyCode, cbH, fW, hspecPrf, hrunPrf, hclPrf]
      let hlistTy ← mkAppM ``HList #[denoteV, sig.asList]
      let cf ← withLocalDeclD `args hlistTy fun hargs => do
        let bodyFn ← withLocalDeclD `s (mkApp denoteV rd.σTp) fun s => do
          mkLambdaFVars #[s] (mkApp2 denC ρTp (mkApp bodyCode s))
        mkLambdaFVars #[hargs]
          (← mkAppM ``ITree.mrec #[bodyFn, ← mkAppM ``HList.head #[hargs]])
      -- the call-site equation `cf args ≈ ret v` (pure) / `≈ ofFree (go …)` (`Free`)
      let εE := mkApp (Lean.mkConst ``Effect []) Op
      let arityE := mkApp (Lean.mkConst ``Effect.arity []) Op
      let endpointOf (v : Expr) : MetaM Expr :=
        if sig.isPure then mkAppOptM ``ITree.ret #[εE, arityE, rd.ρValTy, v]
        else mkAppM ``ofFree #[v]
      let bodyProofLam ← withLocalDeclD `args hlistTy fun hargs => do
        let sE ← mkAppM ``HList.head #[hargs]
        let projs := (mkTupleProjs rd.stateTys.toList sE).toArray
        let stateVals := (Array.range kSt).map fun i =>
          if i < fnCount then hosts[i]! else projs[i]!
        withRecTelescope shape sig.cName sig.cValInst sig.fArgs stateVals fun hs vals => do
          let goApp := mkAppN sig.cValInst vals
          -- the invariant at the call site: the tuple's fn atom *is* the embedding once the
          -- enclosing `lam` node instantiates it — a deferred hint
          let hPsite ←
            if fnCount == 0 then pure (Lean.mkConst ``True.intro)
            else do
              let proj0 ← mkAppM ``Prod.fst #[sE]
              mkExpectedTypeHint (← mkEqRefl proj0) (← mkEq proj0 embs[0]!)
          let a1 := mkApp2 recSoundApp sE hPsite
          let endTy ← mkAppM ``ITree.Eutt #[← pfLhs a1, ← endpointOf goApp]
          if hasHyps then
            let bridgeApp := mkAppN bridgePrf (projs.extract fnCount projs.size ++ hs)
            let congrFn ← withLocalDeclD `v ρTy fun v => do
              if sig.isPure then
                mkLambdaFVars #[v] (← mkAppOptM ``ITree.ret #[εE, arityE, rd.ρValTy, v])
              else
                mkLambdaFVars #[v] (← mkAppM ``ofFree #[v])
            let e2 ← mkAppM ``ITree.Eutt.of_eq #[← mkAppM ``congrArg #[congrFn, bridgeApp]]
            let e2' ← mkExpectedTypeHint e2
              (← mkAppM ``ITree.Eutt #[← pfRhs a1, ← endpointOf goApp])
            let prf ← mkAppM ``ITree.Eutt.trans #[a1, e2']
            mkLambdaFVars (#[hargs] ++ hs) prf
          else
            -- `fW` is the source itself: the adequacy *is* the equation (endpoint by defeq)
            mkLambdaFVars (#[hargs] ++ hs) (← mkExpectedTypeHint a1 endTy)
      pfDefs.modify (·.push { name := sig.cName, asList := sig.asList, retTp := ρTp, cf,
                              bodyProof := ← mkLambdaFVars hosts bodyProofLam,
                              bodyProofEq := false, key := sig.monoArgs })

/-- Reflect a program `foo : A₁ → … → Aₙ → Free Op SOp X` (`n ≥ 0`) into
    `{ g : Closed // ∀ args, denoteProg (g KC Tp.denote) ⟨value-args⟩ ≈ ofFree (foo args) }` — the
    `Prog` whose `main` is a function of the program's inputs (delivered as an `HList`), with a `def_`
    per monomorphised helper.  Each `Aᵢ` that reifies to a `Tp` is a program input; any that does not
    (e.g. an in-bounds proof `j < n` for a symbolic index) is **erased from the AST** and instead
    left quantifying the soundness statement, where it discharges the erased get/set's `fail` branch.
    The non-recursive arm of `reflect%`. -/
partial def reflectMain (foo : Expr) : TermElabM Expr := do
  -- like `forallTelescope`, with anonymous binders renamed `a0`, `a1`, … — they show in the
  -- soundness statement
  let rec namedTelescope {α} (i : Nat) (ty : Expr) (acc : Array Expr)
      (k : Array Expr → Expr → TermElabM α) : TermElabM α := do
    match ty with
    | .forallE nm dom body bi =>
        let nm := if nm.isAnonymous || nm.hasMacroScopes then Name.mkSimple s!"a{i}" else nm
        withLocalDecl nm bi dom fun x =>
          namedTelescope (i+1) (body.instantiate1 x) (acc.push x) k
    | _ => k acc ty
  namedTelescope 0 (← inferType foo) #[] fun args codom => do
    let_expr FreeE εE _ SOp X := (← whnf codom)
      | throwError "reflect%: the body must have type `Free Op SOp _`, got{indentExpr codom}"
    let_expr Effect Op := εE
      | throwError "reflect%: the program's events are not a DSL signature's{indentExpr εE}"
    let XTp ← reifyTpOrThrow X
    -- Classify each argument: those whose type reifies to a `Tp` are **program inputs**; the rest
    -- (e.g. an in-bounds proof `j < n` accompanying a symbolic index) are **erased** from the AST but
    -- kept as hypotheses scoping the soundness statement — that is how a proof-erased `vget`/`vset`'s
    -- `fail` branch is ruled out when the index is symbolic: the source still carries the proof.
    let argTpOpt ← args.mapM (fun a => do reifyTp (← inferType a))
    let mut mainArgTps : Array Expr := #[]
    let mut valueArgs : Array Expr := #[]
    for i in [0:args.size] do
      if let some t := argTpOpt[i]! then
        if t.isAppOf ``Tp.fn then
          throwError "reflect%: `main` may not take a function-typed input (function values \
                      arise from lambdas inside the program)"
        mainArgTps := mainArgTps.push t; valueArgs := valueArgs.push args[i]!
    -- program inputs must be monomorphic and non-dependent (no type-parameter arguments); a *hypothesis*
    -- argument may freely depend on earlier value arguments (it is a proof *about* them).
    for i in [0:args.size] do
      if X.containsFVar args[i]!.fvarId! then
        throwError "reflect%: `main`'s result type may not depend on its arguments"
      for j in [i+1:args.size] do
        if argTpOpt[j]!.isSome && (← inferType args[j]!).containsFVar args[i]!.fvarId! then
          throwError "reflect%: `main` may not take a type-parameter argument\
                      {indentExpr (← inferType args[i]!)}"
    let tpTy := (.const ``Tp [] : Expr)
    let mainArgsList ← mkListLit tpTy mainArgTps.toList
    let fTy ← mkArrow (← mkAppM ``List #[tpTy]) (← mkArrow tpTy (mkSort (.succ .zero)))
    let vTy ← mkArrow tpTy (mkSort (.succ .zero))
    let defs ← IO.mkRef (#[] : Array CallSig)
    let pfDefs ← IO.mkRef (#[] : Array PfDefEntry)
    let inFlight ← IO.mkRef (#[] : Array Name)
    let pending ← IO.mkRef (#[] : Array MVarId)
    let recVerdicts ← IO.mkRef ([] : List (Name × Bool))
    let recBodies ← IO.mkRef (#[] : Array (CallSig × Expr))
    let denoteV := mkApp (Lean.mkConst ``Tp.denote []) Op
    -- a *recursive* program keeps its definition folded — the walk spills it as a `rec_` and
    -- `main` becomes the call; anything else unfolds to expose the `Free` structure
    let topApp := foo.beta args
    let keepFolded ←
      match topApp.getAppFn.constName? with
      | some n => do pure (← analyzeRecShape n).isSome
      | none => pure false
    let topBody ←
      if keepFolded then pure topApp
      else pure ((← unfoldDefinition? topApp).getD topApp)
    let g ← withLocalDeclD `F fTy fun F => withLocalDeclD `V vTy fun V => do
      let hlistTy ← mkAppM ``HList #[V, mainArgsList]
      let mkEnv (resolved : Option (Array (CallSig × Expr))) (subst : List (FVarId × Expr)) : Env :=
        { Op, Opc := mkApp (Lean.mkConst ``OpT []) Op, opWrap := fun _ _ o => o, SOp, F, V,
          subst, defs, pfDefs, inFlight, pending, recVerdicts, recBodies, resolved }
      -- walk `main` under an argument tuple `hargs`, substituting each host argument for its atom
      let walkMain (resolved : Option (Array (CallSig × Expr))) (hargs : Expr) : MetaM Expr := do
        let mut subst : List (FVarId × Expr) := []
        for i in [0:valueArgs.size] do subst := (valueArgs[i]!.fvarId!, ← projHList hargs i) :: subst
        let env := mkEnv resolved subst
        Prod.fst <$> env.walk XTp topBody (env.mkRetT XTp)
      let _ ← withLocalDeclD `args hlistTy fun h => walkMain none h    -- pass 1: discovery
      -- pass 1½: discharge totalization obligations and synthesize each recursive helper's
      -- `rec_` body + `mrec` adequacy (seeding the proof-mode cache)
      elabRecKits Op SOp defs pfDefs inFlight pending recVerdicts recBodies
      let entries ← defs.get
      -- display names: the source definition's name, uniquified across monomorphisations
      let mut bases : Array String := #[]
      let mut dispNames : Array String := #[]
      for sig in entries do
        let base := match sig.cName with
          | .str _ s => s
          | n        => n.toString
        let dups := (bases.filter (· == base)).size
        bases := bases.push base
        dispNames := dispNames.push (if dups == 0 then base else s!"{base}_{dups + 1}")
      let names := dispNames
      -- pass 2: rebuild each helper body under only the *earlier* `def_` binders (discovery is
      -- post-order, so callees precede callers), then `main` under all of them
      let rec buildTele (i : Nat) (resolved : Array (CallSig × Expr)) : MetaM Expr := do
        if _h : i < entries.size then
          let sig := entries[i]!
          if let some rd := sig.rec? then
            -- a recursive helper: its (shared) reflected body ties the knot via `Prog.rec_`
            let some (_, recBody) ← (← recBodies.get).findM? (fun p => sigsMatch p.1 sig)
              | throwError "reflect%: internal: missing rec body for `{sig.cName}`"
            withLocalDeclD `f (mkApp2 F sig.asList sig.retTp) fun cf => do
              let rest ← buildTele (i + 1) (resolved.push (sig, cf))
              mkAppOptM ``Prog.rec_ #[Op, SOp, F, V, mainArgsList, none, rd.σTp, sig.retTp,
                                      Lean.mkStrLit names[i]!, recBody.beta #[V],
                                      ← mkLambdaFVars #[cf] rest]
          else
          let bodyLam ← (mkEnv (some resolved) []).rebuildBody sig
          withLocalDeclD `f (mkApp2 F sig.asList sig.retTp) fun cf => do
            let rest ← buildTele (i + 1) (resolved.push (sig, cf))
            mkAppOptM ``Prog.def_ #[Op, SOp, F, V, mainArgsList, none, sig.asList, sig.retTp,
                                    Lean.mkStrLit names[i]!, bodyLam, ← mkLambdaFVars #[cf] rest]
        else
          let mainLam ← withLocalDeclD `args hlistTy fun h => do
            mkLambdaFVars #[h] (← walkMain (some resolved) h)
          mkAppOptM ``Prog.main #[Op, SOp, F, V, mainArgsList, none, mainLam]
      let prog ← buildTele 0 #[]
      mkLambdaFVars #[F, V] prog
    let gTy ← inferType g
    let kc ← mkAppM ``KC #[Op]
    -- the actual (value) arguments as an `HList Tp.denote mainArgs`, for the soundness statement
    let mut argHList ← mkAppOptM ``HList.nil #[none, denoteV]
    for (a, t) in (valueArgs.zip mainArgTps).reverse do
      argHList ← mkAppOptM ``HList.cons #[none, denoteV, t, none, a, argHList]
    let ofFreeFn ← mkAppOptM ``ofFree
      #[mkApp (Lean.mkConst ``Effect []) Op, mkApp (Lean.mkConst ``Effect.arity []) Op, SOp, X]
    -- soundness  fun g => ∀ args, denoteProg (g KC Tp.denote) ⟨args⟩ ≈ ofFree (foo args)
    -- — `denoteProg` lands in `Comp` *directly*; `ofFree` only embeds the source `Free`.
    let pred ← withLocalDeclD `g gTy fun gv => do
      let lhs ← mkAppOptM ``denoteProg #[Op, SOp, none, none, mkAppN gv #[kc, denoteV], argHList]
      let eutt ← mkAppM ``ITree.Eutt #[lhs, mkApp ofFreeFn (foo.beta args)]
      mkLambdaFVars #[gv] (← mkForallFVars args eutt)
    -- proof: `denoteProg (g KC ⟨args⟩) = ofFree (foo args)` directly — `denote`/`denoteProg` and
    -- `ofFree` unfold to the same tree, the `call`-binds fusing via `bind_ret`/`bind_vis`.
    let dpC ← mkAppOptM ``denoteProg #[Op, SOp, none, none, mkAppN g #[kc, denoteV], argHList]
    let eqTy ← mkEq dpC (mkApp ofFreeFn (foo.beta args))
    -- **The compositional soundness proof**: re-walk the source in proof mode and assemble the
    -- `sc_*` congruence lemmas — the source's own in-bounds proofs discharge each erased get/set
    -- `fail` branch (`dif_pos`), and helper calls compose via each helper's own (★)-proof.
    -- No `simp`: the proof term mirrors the source structure.
    let mut psubst : List (FVarId × Expr) := []
    for va in valueArgs do psubst := (va.fvarId!, va) :: psubst
    let penv : Env := { Op, Opc := mkApp (Lean.mkConst ``OpT []) Op, opWrap := fun _ _ o => o,
                        SOp, F := kc, V := denoteV, subst := psubst, defs, pfDefs, inFlight,
                        pending, recVerdicts, recBodies, pf := true }
    let (_, pf?) ← penv.walkTop XTp topBody
    let some proof := pf? | throwError "reflect%: internal: proof mode produced no proof"
    let prfBody ←
      if proof.isEq then do
        let eqPrf ← mkExpectedTypeHint proof.e eqTy
        mkAppM ``ITree.Eutt.of_eq #[eqPrf]
      else
        -- a recursive helper was called: the walk's invariant is already (★≈)
        mkExpectedTypeHint proof.e
          (← mkAppM ``ITree.Eutt #[dpC, mkApp ofFreeFn (foo.beta args)])
    let prf ← mkLambdaFVars args prfBody
    mkAppOptM ``Subtype.mk #[gTy, pred, g, prf]

/-- **`reflect%`** — the unified entry point.  One walk handles everything:

* a `Free Op SOp α` **program value** → a `Prog` with a nullary `main`;
* a program `A₁ → … → Aₙ → Free Op SOp α` (of `Tp`-typed inputs) → a `Prog` whose `main` is a
  function of those inputs;
* a structural-recursive `def` → kept folded, spilled as a `rec_` (like any recursive helper),
  with `main` the call.

Each returns a `{ · // · }` bundling the AST with its `≈`-soundness against the source. -/
elab "reflect% " t:term : term => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  reflectMain (← instantiateMVars e)

/-- **`reflect_def C := src`** — reflect `src` (as `reflect%`) and introduce **two named
    definitions**:

* `C` — the closed `Prog`;
* `C_sound` — its `≈`-soundness against `ofFree src`,

so use sites read `C` / `C_sound` instead of projecting `.1`/`.2` out of the bundled `Subtype`
(and goals display the named constants). -/
elab doc:(Lean.Parser.Command.docComment)? "reflect_def " nm:ident " := " t:term : command =>
  Lean.Elab.Command.liftTermElabM do
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let packed ← reflectMain (← instantiateMVars e)
    synthesizeSyntheticMVarsNoPostponing
    let packed ← instantiateMVars packed
    let_expr Subtype.mk _ pred g prf := packed
      | throwError "reflect_def: internal: reflection did not produce a `Subtype.mk`"
    let progName := (← getCurrNamespace) ++ nm.getId
    let soundName := progName.appendAfter "_sound"
    addAndCompile (.defnDecl {
      name := progName, levelParams := [], type := ← inferType g, value := g,
      hints := .abbrev, safety := .safe })
    -- `C := g` definitionally, so the bundled proof also proves the statement *about `C`*
    addDecl (.thmDecl {
      name := soundName, levelParams := [],
      type := pred.beta #[Lean.mkConst progName], value := prf })
    if let some d := doc then
      addDocStringCore progName (← Lean.getDocStringText d)
    Lean.Elab.Term.addTermInfo' nm (Lean.mkConst progName) (isBinder := true)

end Freigen
