import Freigen.F2Z.Defs
import Lean.Elab.Tactic

namespace Freigen.F2Z

open Context

variable [ctx : Context]

abbrev Assertion := Valuation Wℤ → Valuation WBool → Prop

namespace Cert

/-- Certify a pointwise-valid assertion without using any certificate premises. -/
def pure {Q : Assertion}
    (h : ∀ ρℤ ρBool, Q ρℤ ρBool) : Cert Q :=
  ctx.cert.derive (ι := PEmpty)
    (P := fun _ _ _ => True)
    (fun ρℤ ρBool _ => h ρℤ ρBool)
    nofun

/-- Transport a certificate along pointwise implication. -/
def map {P Q : Assertion}
    (hp : Cert P)
    (h : ∀ ρℤ ρBool, P ρℤ ρBool → Q ρℤ ρBool) : Cert Q :=
  ctx.cert.derive (ι := PUnit)
    (fun ρℤ ρBool hs => h ρℤ ρBool (hs .unit))
    (fun _ => hp)

/-- Combine two certificates using a pointwise binary rule. -/
def map₂ {P Q R : Assertion}
    (hp : Cert P) (hq : Cert Q)
    (h : ∀ ρℤ ρBool, P ρℤ ρBool → Q ρℤ ρBool → R ρℤ ρBool) : Cert R :=
  ctx.cert.derive (ι := Sum PUnit PUnit)
    (P := fun
      | .inl _ => P
      | .inr _ => Q)
    (fun ρℤ ρBool hs => h ρℤ ρBool (hs (.inl .unit)) (hs (.inr .unit)))
    (fun
      | .inl _ => hp
      | .inr _ => hq)

/-- Certify the pointwise conjunction of two certified assertions. -/
def and {P Q : Assertion} (hp : Cert P) (hq : Cert Q) :
    Cert (fun ρℤ ρBool => P ρℤ ρBool ∧ Q ρℤ ρBool) :=
  map₂ hp hq fun _ _ hp hq => ⟨hp, hq⟩

/-- Combine a `Type`-indexed family of certificates into a certified pointwise universal. -/
def all {ι : Type} {P : ι → Assertion}
    (hs : (i : ι) → Cert (P i)) :
    Cert (fun ρℤ ρBool => ∀ i, P i ρℤ ρBool) :=
  ctx.cert.derive
    (fun _ _ h i => h i)
    hs

/-- Combine a proposition-indexed family of certificates into a certified pointwise universal. -/
def allProp {ι : Prop} {P : ι → Assertion}
    (hs : (i : ι) → Cert (P i)) :
    Cert (fun ρℤ ρBool => ∀ i, P i ρℤ ρBool) :=
  ctx.cert.derive (ι := PLift ι)
    (P := fun i => P i.down)
    (fun _ _ h i => h ⟨i⟩)
    (fun i => hs i.down)

end Cert

@[simp]
theorem Valuation.one_apply (ρ : Valuation Wℤ) : ρ (1 : Wℤ) = 1 :=
  ρ.one_map

@[simp]
theorem Valuation.add_apply (ρ : Valuation Wℤ) (x y : Wℤ) :
    ρ (x + y) = ρ x + ρ y :=
  ρ.toFun.map_add x y

@[simp]
theorem Valuation.smul_apply (ρ : Valuation Wℤ) (a : ℤ) (x : Wℤ) :
    ρ (a • x) = a * ρ x :=
  ρ.toFun.map_smul a x

end Freigen.F2Z

namespace Freigen.F2Z.CertTactic

open Lean Meta Elab Tactic

structure LiftedCert where
  sourceId : FVarId
  sourceName : Name
  cert : Expr
  assertion : Expr
  deriving Inhabited

private def certView? (expectedCtx type : Expr) : MetaM (Option Expr) := do
  let type ← instantiateMVars type
  unless type.getAppFn.isConstOf ``Context.Cert do
    return none
  let args := type.getAppArgs
  unless args.size == 2 do
    return none
  unless ← isDefEq expectedCtx args[0]! do
    return none
  return some args[1]!

private partial def liftCertFamily (expectedCtx : Expr) (sourceId : FVarId) (sourceName : Name)
    (value type : Expr) : MetaM (Option LiftedCert) := do
  if let some assertion ← certView? expectedCtx type then
    return some { sourceId, sourceName, cert := value, assertion }
  let type ← whnf type
  let .forallE binderName domain body binderInfo := type
    | return none
  withLocalDecl binderName binderInfo domain fun x => do
    let some lifted ←
        liftCertFamily expectedCtx sourceId sourceName (mkApp value x) (body.instantiate1 x)
      | return none
    let family ← mkLambdaFVars #[x] lifted.cert
    let liftedCert ←
      if ← isProp domain then
        mkAppM ``Cert.allProp #[family]
      else
        let domainSort ← whnf (← inferType domain)
        unless ← isDefEq domainSort (mkSort (.succ .zero)) do
          throwError "`cert` found `{sourceName}` ending in a certificate, but binder `{binderName}` has domain{indentExpr domain}\nOnly propositions and `Type`-valued binders are supported by the current universe-dumb `CertLogic.derive`."
        mkAppM ``Cert.all #[family]
    let liftedType ← inferType liftedCert
    let some assertion ← certView? expectedCtx liftedType
      | throwError "internal `cert` error: lifting `{sourceName}` did not produce a certificate"
    return some { sourceId, sourceName, cert := liftedCert, assertion }

private def collectCerts (goal : MVarId) (expectedCtx : Expr) : MetaM (Array LiftedCert) :=
  goal.withContext do
    let mut certs := #[]
    for localDecl in (← getLCtx) do
      if localDecl.isImplementationDetail then
        continue
      let value := mkFVar localDecl.fvarId
      if let some cert ←
          liftCertFamily expectedCtx localDecl.fvarId localDecl.userName value localDecl.type then
        certs := certs.push cert
    return certs

private def combineCerts (certs : Array LiftedCert) : MetaM Expr := do
  let some last := certs.back? | throwError "`cert` found no local certificates"
  let mut result := last.cert
  for i in (List.range (certs.size - 1)).reverse do
    result ← mkAppM ``Cert.and #[certs[i]!.cert, result]
  return result

private def openCerts (goal : MVarId) (certs : Array LiftedCert) : MetaM MVarId :=
  goal.withContext do
    let mut goal := goal
    for cert in certs.reverse do
      goal ← goal.clear cert.sourceId
    let rhoZName := (← getLCtx).getUnusedName `ρℤ
    let (_, goal') ← goal.intro rhoZName
    goal := goal'
    let rhoBoolName := (← goal.getDecl).lctx.getUnusedName `ρBool
    let (_, goal') ← goal.intro rhoBoolName
    goal := goal'
    let (allFactsId, goal') ← goal.intro1P
    goal := goal'
    let mut remaining := mkFVar allFactsId
    for i in [0 : certs.size] do
      let (proof, remaining') ← goal.withContext do
        if i + 1 == certs.size then
          pure (remaining, remaining)
        else
          return (← mkAppM ``And.left #[remaining], ← mkAppM ``And.right #[remaining])
      remaining := remaining'
      let (_, nextGoal) ← goal.withContext do
        let factName := certs[i]!.sourceName
        goal.note factName proof
      goal := nextGoal
    return ← goal.clear allFactsId

private def openPure (goal : MVarId) : MetaM MVarId :=
  goal.withContext do
    let rhoZName := (← getLCtx).getUnusedName `ρℤ
    let (_, goal) ← goal.intro rhoZName
    let rhoBoolName := (← goal.getDecl).lctx.getUnusedName `ρBool
    let (_, goal) ← goal.intro rhoBoolName
    return goal

private def certCore (goal : MVarId) : MetaM MVarId :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    unless target.getAppFn.isConstOf ``Context.Cert do
      throwError "`cert` requires a goal of the form `Cert Q`, but the target is{indentExpr target}"
    let args := target.getAppArgs
    unless args.size == 2 do
      throwError "internal `cert` error: unexpected `Cert` target{indentExpr target}"
    let expectedCtx := args[0]!
    let certs ← collectCerts goal expectedCtx
    if certs.isEmpty then
      let targetAssertion := args[1]!
      let ruleType ← forallTelescopeReducing (← inferType targetAssertion) (whnfType := true) fun rhos _ => do
        unless rhos.size == 2 do
          throwError "internal `cert` error: an assertion did not take two valuations"
        mkForallFVars rhos (mkAppN targetAssertion rhos)
      let rule ← mkFreshExprSyntheticOpaqueMVar ruleType (← goal.getTag)
      let result ← mkAppOptM ``Cert.pure
        #[some expectedCtx, some targetAssertion, some rule]
      goal.assign result
      return ← openPure rule.mvarId!
    let combined ← combineCerts certs
    let combinedType ← inferType combined
    let some combinedAssertion ← certView? expectedCtx combinedType
      | throwError "internal `cert` error: combined premises are not a certificate"
    let targetAssertion := args[1]!
    let ruleType ← forallTelescopeReducing (← inferType combinedAssertion) (whnfType := true) fun rhos _ => do
      unless rhos.size == 2 do
        throwError "internal `cert` error: an assertion did not take two valuations"
      let premise := mkAppN combinedAssertion rhos
      let conclusion := mkAppN targetAssertion rhos
      mkForallFVars rhos (mkForall `h .default premise conclusion)
    let rule ← mkFreshExprSyntheticOpaqueMVar ruleType (← goal.getTag)
    let result ← mkAppOptM ``Cert.map
      #[some expectedCtx, some combinedAssertion, some targetAssertion, some combined, some rule]
    goal.assign result
    openCerts rule.mvarId! certs

/--
Find every local hypothesis whose telescope ends in `Cert`, combine them, and reduce a `Cert Q`
goal to the corresponding pointwise logical implication. Each source certificate is removed and
its name is reused for its pointwise body: direct certificate `h : Cert P` becomes
`h : P ρℤ ρBool`, and a family `h : ∀ x, Cert (P x)` becomes
`h : ∀ x, P x ρℤ ρBool`. Inaccessible source names remain inaccessible.
When there are no local certificates, reduce the goal using `Cert.pure` instead.
-/
syntax (name := certTac) "cert" : tactic

elab_rules : tactic
  | `(tactic| cert) =>
      liftMetaTactic1 fun goal => some <$> certCore goal

end Freigen.F2Z.CertTactic
