import Freigen.Reflect.Comp
import Freigen.Reflect.NatConstruct
import Freigen.Reflect.Source

namespace Freigen
namespace Ast
namespace Reflector

open Lean Meta Elab Term

/-! ## Helper construction and plan execution -/

structure BuiltHelper extends HelperSemantics where
  argTp : Lean.Expr
  resultTp : Lean.Expr
  body : Lean.Expr
  genericBody : Lean.Expr

/-! ### Recursive helper construction -/

private def buildRecursiveHelper (plan : Plan) (target : TargetEnv) (V : Lean.Expr)
    (helpers : Array Helper) (spec : Specialization) (arg : ValueParam)
    (shape : NatBRecShape) :
    MetaM BuiltHelper := do
  let argRepr := arg.repr
  let argTp := Lean.mkConst ``Tp.nat
  let resultTp ← reprTp spec.resultRepr
  let resultRel ← mkAppM ``ReprSpec.relates #[spec.resultRepr]
  let targetArgType ← mkAppM ``Tp.denote #[target.monad, argTp]
  let slot ← recursionSlot argTp resultTp
  let bodyResultType ← mkAppM ``Expr
    #[plan.targetSig, target.values, slot, resultTp]
  let baseMVar ← mkFreshExprMVar bodyResultType
  let stepMVar ← mkFreshExprMVar (← mkArrow (mkConst ``Nat) bodyResultType)
  let range? ← match spec.sourceRange? with
    | some range => mkAppM ``Option.some #[range]
    | none => pure (mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``SourceRange))
  let body ← mkAppM ``Expr.natBrecBody #[range?, baseMVar, stepMVar]
  let baseFn := mkApp shape.functional (mkNatLit 0)
  let .forallE _ belowZero _ _ ← whnf (← inferType baseFn)
    | throwError "reflect%: malformed zero argument of `Nat.brecOn` functional"
  let .const ``PUnit [belowLevel] ← whnf belowZero
    | throwError "reflect%: zero argument of `Nat.brecOn` functional is not `PUnit`"
  let baseSource := mkApp baseFn (mkConst ``PUnit.unit [belowLevel])
  let base ← emitComp {
    plan, target
    goal := { sourceType := spec.resultType, targetTp := resultTp, relates := resultRel }
    mode := .recursive { spec, body }
    V, Φ := mkConst ``True
    helpers
  } baseSource
  baseMVar.mvarId!.assign base.code
  let baseWitness := base.sound
  let ⟨stepCode, stepGeneric, stepSound⟩ ←
    withLocalDeclD `genericPred (mkApp V argTp) fun genericPred =>
    withLocalDeclD `pred (mkConst ``Nat) fun pred => do
    let sourceCall ← mkAppM ``Nat.brecOn #[pred, shape.functional]
    let go ← mkAppM ``Nat.brecOn.go #[pred, shape.functional]
    let tail ← mkAppM ``PProd.snd #[go]
    let below ← mkAppM ``PProd.mk #[sourceCall, tail]
    let succ ← mkAppM ``Nat.succ #[pred]
    let stepSource ← mkAppM' shape.functional #[succ, below]
    let callType ← Construct.recCallType {
      sourceSig := plan.sourceSig, targetSig := plan.targetSig, argumentTp := argTp
      resultTp, compat := plan.compat, body, assumption := mkConst ``True
      sourceType := spec.resultType, relates := resultRel, sourceCall, sourceArgument := pred
    }
    withLocalDeclD `ih callType fun ih => do
      let predRel ← mkAppM ``ReprSpec.relates #[argRepr, pred, pred]
      let predRelated ← mkExpectedTypeHint (← mkAppM ``Eq.refl #[pred]) predRel
      let atoms : Array RelatedAtom := #[{
        source := pred, target := pred,
        related := mkLambda `h .default (mkConst ``True) predRelated }]
      let emitted ← emitComp {
        plan, target
        goal := { sourceType := spec.resultType, targetTp := resultTp, relates := resultRel }
        mode := .recursive { spec, body, call? := some {
          sourceCall, sourceArg := pred, targetArg := pred, adequate := ih } }
        V, Φ := mkConst ``True
        atoms
        genericAtoms := #[{ semantic := pred, code := genericPred }]
        helpers
      } stepSource
      let witness := emitted.sound
      pure (← mkLambdaFVars #[pred] emitted.code,
        ← mkLambdaFVars #[genericPred] emitted.generic,
        ← mkLambdaFVars #[pred, ih] witness)
  stepMVar.mvarId!.assign stepCode
  let body ← instantiateMVars body
  let sourceFn ← mkConstWithFreshMVarLevels spec.name
  let brecFn ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    mkLambdaFVars #[n] (← mkAppM ``Nat.brecOn #[n, shape.functional])
  let sourceEqType ← mkAppM ``Eq #[sourceFn, brecFn]
  let sourceEq ← mkExpectedTypeHint (← mkAppM ``Eq.refl #[sourceFn]) sourceEqType
  let semanticAdequate ← Construct.natBrecAdequate {
    sourceSig := plan.sourceSig, targetSig := plan.targetSig, compat := plan.compat
    sourceType := spec.resultType, resultTp, relates := resultRel, sourceFunction := sourceFn
    functional := shape.functional, sourceEquality := sourceEq, range := range?
    base := base.code, step := stepCode, baseSound := baseWitness, stepSound
  }
  let semanticTarget ← mkAppM ``ITree.CompE.mrec
    #[← withLocalDeclD `x targetArgType fun x => do
      mkLambdaFVars #[x] (← mkAppM ``Expr.denote #[mkApp body x])]
  let genericBody ← withLocalDeclD `genericN (mkApp V argTp) fun genericN => do
    mkLambdaFVars #[genericN]
      (← mkAppM ``Expr.natBrecCode #[range?, base.generic, stepGeneric, genericN])
  let semanticBody ← withLocalDeclD `n targetArgType fun n => do
    mkLambdaFVars #[n]
      (← mkAppM ``Expr.natBrecCode #[range?, base.code, stepCode, n])
  let targetFn ← mkAppM ``ITree.CompE.mrec
    #[← withLocalDeclD `x targetArgType fun x => do
      mkLambdaFVars #[x] (← mkAppM ``Expr.denote #[mkApp semanticBody x])]
  let targetEq ← mkExpectedTypeHint
    (← mkAppM ``Expr.mrec_natBrecBody_eq_code #[range?, base.code, stepCode])
    (← mkAppM ``Eq #[semanticTarget, targetFn])
  let adequate ← mkAppM ``Adequate.congrTarget #[targetEq, semanticAdequate]
  pure ({
    spec := spec
    target := targetFn
    adequate := adequate
    argTp := argTp
    resultTp := resultTp
    body := semanticBody
    genericBody := genericBody
  } : BuiltHelper)

/-! ### Ordinary helper construction -/

private def buildOrdinaryHelper (plan : Plan) (target : TargetEnv) (V : Lean.Expr)
    (helpers : Array Helper) (spec : Specialization) (first : ValueParam)
    (second? : Option ValueParam) :
    MetaM BuiltHelper := do
  let valueParams := match second? with
    | none => #[first]
    | some second => #[first, second]
  let arity := valueParams.size
  let argCodes ← valueParams.mapM fun param => mkAppM ``ReprSpec.code #[param.repr]
  let argCode ← if arity == 1 then pure argCodes[0]! else
    mkAppM ``Tp0.prod #[argCodes[0]!, argCodes[1]!]
  let argTp ← mkAppM ``Tp.base #[argCode]
  let targetArgType ← mkAppM ``Tp.denote #[target.monad, argTp]
  let sourceArgType ← if arity == 1 then pure valueParams[0]!.type else
    mkAppM ``Prod #[valueParams[0]!.type, valueParams[1]!.type]
  let resultTp ← reprTp spec.resultRepr
  let resultRel ← mkAppM ``ReprSpec.relates #[spec.resultRepr]
  let argRels ← valueParams.mapM fun param => mkAppM ``ReprSpec.relates #[param.repr]
  let sourceDecls := valueParams.map fun param => (`sourceArg, fun _ => pure param.type)
  let ⟨bodyCode, genericBody, targetFn, adequateCurried⟩ ←
    withLocalDeclsD sourceDecls fun sourceArgs =>
    withLocalDeclD `genericArg (mkApp V argTp) fun genericArg =>
    withLocalDeclD `targetArg targetArgType fun targetArg => do
      let targetArgs ← if arity == 1 then pure #[targetArg] else
        pure #[← mkAppM ``Prod.fst #[targetArg], ← mkAppM ``Prod.snd #[targetArg]]
      let relations ← sourceArgs.mapIdxM fun i sourceArg =>
        mkAppM' argRels[i]! #[sourceArg, targetArgs[i]!]
      let Φ ← if arity == 1 then pure relations[0]! else
        mkAppM ``And #[relations[0]!, relations[1]!]
      let fullArgs ← spec.reconstructArgs sourceArgs
      let sourceCall := mkAppN (← mkConstWithFreshMVarLevels spec.name) fullArgs
      let some bodySource ← unfoldDefinition? sourceCall
        | throwError "reflect%: cannot unfold helper `{spec.name}`"
      let atoms : Array RelatedAtom ← sourceArgs.mapIdxM fun i sourceArg => do
        let related ← withLocalDeclD `hΦ Φ fun hΦ => do
          let proof ← if arity == 1 then pure hΦ else
            mkAppM (if i == 0 then ``And.left else ``And.right) #[hΦ]
          mkLambdaFVars #[hΦ] proof
        let target := targetArgs[i]!
        pure {
          source := sourceArg
          target := target
          related := related
        }
      let body ← emitComp {
        plan, target
        goal := { sourceType := spec.resultType, targetTp := resultTp, relates := resultRel }
        mode := .ordinary
        V, Φ, atoms
        genericAtoms := #[{ semantic := targetArg, code := genericArg }]
        helpers
      } bodySource
      let body ← match spec.sourceRange? with
        | some range => annotateEmission range body
        | none => pure body
      let bodyCode ← mkLambdaFVars #[targetArg] body.code
      let genericBody ← mkLambdaFVars #[genericArg] body.generic
      let targetFn ← mkLambdaFVars #[targetArg] (← mkAppM ``Expr.denote #[body.code])
      let witness := body.sound
      let adequateCurried ← withLocalDeclD `hrel Φ fun hrel => do
        let sound ← mkAppM ``ReflectionWitnessAt.sound #[witness, hrel]
        mkLambdaFVars (sourceArgs ++ #[targetArg, hrel]) sound
      pure (bodyCode, genericBody, targetFn, adequateCurried)
  let adequate ← if arity == 1 then pure adequateCurried else
    withLocalDeclD `sourceArg sourceArgType fun sourceArg =>
    withLocalDeclD `targetArg targetArgType fun targetArg => do
      let sources := #[← mkAppM ``Prod.fst #[sourceArg], ← mkAppM ``Prod.snd #[sourceArg]]
      let Φ ← mkAppM ``And #[← mkAppM' argRels[0]! #[sources[0]!, ← mkAppM ``Prod.fst #[targetArg]],
        ← mkAppM' argRels[1]! #[sources[1]!, ← mkAppM ``Prod.snd #[targetArg]]]
      withLocalDeclD `hrel Φ fun hrel =>
        mkLambdaFVars #[sourceArg, targetArg, hrel]
          (mkAppN adequateCurried (sources ++ #[targetArg, hrel]))
  pure ({
    spec := spec
    target := targetFn
    adequate := adequate
    argTp := argTp
    resultTp := resultTp
    body := bodyCode
    genericBody := genericBody
  } : BuiltHelper)

private def buildHelper (plan : Plan) (target : TargetEnv) (V : Lean.Expr)
    (helpers : Array Helper) (spec : Specialization) : MetaM BuiltHelper :=
  match spec.boundary with
  | .unary _ arg _ => buildOrdinaryHelper plan target V helpers spec arg none
  | .pair _ left _ right _ => buildOrdinaryHelper plan target V helpers spec left (some right)
  | .natBRec arg shape => buildRecursiveHelper plan target V helpers spec arg shape

/-! ### Plan-ordered helper installation -/

private partial def emitProgram (plan : Plan) (target : TargetEnv) (goal : EmitGoal)
    (V source : Lean.Expr) (specs : List Specialization := plan.specializations.toList)
    (helpers : Array Helper := #[]) : MetaM Emission := do
  match specs with
  | [] => emitComp ({
      plan, target, goal, mode := .ordinary, V, Φ := mkConst ``True, helpers
    } : EmitContext) source
  | spec :: rest =>
      let built ← buildHelper plan target V helpers spec
      /- Installing a helper is identical after its body and adequacy theorem have been built. -/
      let genericFnTp ← mkAppM ``Tp.fn #[built.argTp, built.resultTp]
      withLocalDeclD `genericHelper (mkApp V genericFnTp) fun genericHelper => do
        let installed : Helper := {
          spec := built.spec
          target := built.target
          generic := genericHelper
          adequate := built.adequate
        }
        let inner ← emitProgram plan target goal V source rest (helpers.push installed)
        let targetFn := built.target
        let kCode ← withLocalDeclD `helper (← inferType targetFn) fun bound =>
          mkLambdaFVars #[bound] (inner.code.replace fun e =>
            if e == targetFn then some bound else none)
        let kGeneric ← mkLambdaFVars #[genericHelper] inner.generic
        let innerWitness := inner.sound
        let proofArgs : Construct.HelperScopeProof := {
          sourceSig := plan.sourceSig, targetSig := plan.targetSig, compat := plan.compat
          assumption := mkConst ``True, argumentTp := built.argTp
          helperResultTp := built.resultTp, targetTp := goal.targetTp
          sourceType := goal.sourceType, relates := goal.relates, source, body := built.body
          continuation := kCode, innerSound := innerWitness
        }
        let codeArgs : Construct.HelperScope := {
          targetSig := plan.targetSig, carrier := target.values, targetTp := goal.targetTp
          argumentTp := built.argTp, helperResultTp := built.resultTp, body := built.body
          continuation := kCode
        }
        let genericArgs : Construct.HelperScope := {
          targetSig := plan.targetSig, carrier := V, targetTp := goal.targetTp
          argumentTp := built.argTp, helperResultTp := built.resultTp
          body := built.genericBody, continuation := kGeneric
        }
        let ⟨reflection, code, generic⟩ ← if built.spec.boundary.isRecursive then do
          pure (← Construct.letrecProof proofArgs, ← Construct.letrec codeArgs,
            ← Construct.letrec genericArgs)
        else do
          pure (← Construct.lambdaProof proofArgs, ← Construct.lambda codeArgs,
            ← Construct.lambda genericArgs)
        pure { code, generic, sound := reflection }

/-! ## Public plan execution -/

structure Execution where
  plan : Plan
  goal : EmitGoal
  emission : Emission
  program : Lean.Expr

def execute (plan : Plan) (source : Lean.Expr) (range? : Option Lean.Expr) :
    TermElabM Execution := do
  let targetTp ← mkAppM ``Tp.base #[← mkAppM ``ReprSpec.code #[plan.resultRepr]]
  let relates ← mkAppM ``ReprSpec.relates #[plan.resultRepr]
  let goal : EmitGoal := {
    sourceType := plan.resultType
    targetTp := targetTp
    relates := relates
  }
  let target ← mkTargetEnv plan.targetSig
  let VType := .forallE `t (mkConst ``Tp) (mkSort 1) .default
  let ⟨emission, program⟩ ← withLocalDeclD `V VType fun V => do
    let emission ← emitProgram plan target goal V source
    let emission ← match source.getAppFn.constName? with
      | some decl => match ← declarationSourceRange? decl with
        | some range => annotateEmission range emission
        | none => pure emission
      | none => pure emission
    let emission ← match range? with
      | some range => annotateEmission range emission
      | none => pure emission
    if emission.code.containsFVar V.fvarId! || emission.sound.containsFVar V.fvarId! then
      throwError "reflect%: semantic emission retained the generic PHOAS carrier"
    pure (emission, ← mkLambdaFVars #[V] emission.generic)
  pure { plan, goal, emission, program }

/-! ## Final result packaging -/

/-- Package emitted PHOAS and its soundness theorem without reducing the `Reflected` subtype. -/
private def packReflection (plan : Plan) (goal : EmitGoal) (source semanticV
    program sound : Lean.Expr) : MetaM Lean.Expr := do
  let codeType ← inferType program
  let predicate ← withLocalDeclD `code codeType fun code => do
    let denoted ← mkAppM ``Expr.denote #[mkApp code semanticV]
    let property ← mkAppM ``ITree.CompE.Eutt #[plan.compat, goal.relates,
      ← mkAppM ``Free.toITree #[source], denoted]
    mkLambdaFVars #[code] property
  mkAppOptM ``Subtype.mk
    #[some codeType, some predicate, some program, some sound]

/-- Give the large generated proof a name so reflected definitions and the compiler retain sharing. -/
private def shareSoundProof (sound : Lean.Expr) : TermElabM Lean.Expr := do
  synthesizeSyntheticMVarsNoPostponing
  let sound ← instantiateMVars sound
  let soundType ← inferType sound
  let name ← mkAuxName `reflectSound
  addDecl (.defnDecl {
    name
    levelParams := []
    type := soundType
    value := sound
    hints := .regular (getMaxHeight (← getEnv) sound + 1)
    safety := .safe
  })
  pure (mkConst name)

/-- Emit the program and package the soundness proof attached to that same emission. -/
def reflectProgram (source : Lean.Expr) (range? : Option Lean.Expr := none) :
    TermElabM Lean.Expr := do
  let plan ← discover source
  let execution ← execute plan source range?
  let targetSpec ← mkAppM ``Signature.spec #[execution.plan.targetSig]
  let semanticM := mkApp (Lean.mkConst ``ITree.CompE [Level.zero, Level.zero]) targetSpec
  let semanticV ← mkAppM ``Tp.denote #[semanticM]
  let genericSemantic := mkApp execution.program semanticV
  let witness := execution.emission.sound
  let noRecursion ← mkAppOptM ``Option.none
    #[some (← mkAppM ``Prod #[mkConst ``Tp, mkConst ``Tp])]
  let semanticSound ← Construct.witnessSound {
    sourceSig := execution.plan.sourceSig, targetSig := execution.plan.targetSig
    slot := noRecursion, compat := execution.plan.compat, assumption := mkConst ``True
    targetTp := execution.goal.targetTp, sourceType := execution.goal.sourceType
    relates := execution.goal.relates, source, code := execution.emission.code, witness
    assumptionProof := mkConst ``True.intro
  }
  let wanted ← mkAppM ``ITree.CompE.Eutt
    #[execution.plan.compat, execution.goal.relates, ← mkAppM ``Free.toITree #[source],
      ← mkAppM ``Expr.denote #[genericSemantic]]
  let sound ← mkExpectedTypeHint semanticSound wanted
  let sound ← shareSoundProof sound
  packReflection execution.plan execution.goal source semanticV execution.program sound

def reflectTerm (source : Lean.Expr) (range? : Option Lean.Expr := none) : TermElabM Lean.Expr := do
  let plan ← discover source
  let execution ← execute plan source range?
  mkAppM ``Sigma.mk #[execution.emission.code, execution.emission.sound]

end Reflector
end Ast
end Freigen
