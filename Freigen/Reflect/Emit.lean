import Freigen.Reflect.Comp
import Freigen.Reflect.NatConstruct
import Freigen.Reflect.Source

namespace Freigen
namespace Ast
namespace Reflector

open Lean Meta Elab Term

/-! ## Definition-table construction

Pass one has already fixed every specialization.  Execution can therefore compute the complete
`DefCtx` before emitting a body, use typed de Bruijn references while emitting, and build the
`Defs` telescope once in dependency order.  There is no nested program continuation and no
second denotation traversal.
-/

structure BuiltHelper extends HelperSemantics where
  semanticBody : Lean.Expr
  genericBody : Lean.Expr
  dispatch : MVarId

structure TableState where
  scope : Lean.Expr
  extension : Lean.Expr
  semanticDefs : Lean.Expr
  genericDefs : Lean.Expr
  helpers : Array Helper := #[]
  dispatches : Array MVarId := #[]

private def mkDefSig (input output : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``DefSig.mk #[Lean.mkConst ``Tp.unit, input, output]

private def specializationTypes (spec : Specialization) : MetaM (Lean.Expr × Lean.Expr) := do
  let params := spec.valueParams
  let codes ← params.mapM fun param => mkAppM ``ReprSpec.code #[param.repr]
  let input ← match codes with
    | #[input] => pure input
    | #[left, right] => mkAppM ``Tp.prod #[left, right]
    | _ => throwError "reflect%: internal: helper boundary has unsupported value arity"
  pure (input, ← reprTp spec.resultRepr)

private def fullContext (specs : Array Specialization) : MetaM Lean.Expr := do
  let mut ctx ← mkAppOptM ``List.nil #[some (Lean.mkConst ``DefSig)]
  for spec in specs do
    let (input, output) ← specializationTypes spec
    ctx ← mkAppM ``List.cons #[← mkDefSig input output, ctx]
  pure ctx

private def extensionFor (small : Lean.Expr) (future : Array Specialization) : MetaM Lean.Expr := do
  let mut extension ← mkAppOptM ``Extension.refl #[some small]
  for spec in future do
    let (input, output) ← specializationTypes spec
    let decl ← mkDefSig input output
    extension ← mkAppOptM ``Extension.step #[none, none, some decl, some extension]
  pure extension

private def semanticClosure (fullCtx extension ref : Lean.Expr) : MetaM Lean.Expr := do
  let lifted ← mkAppM ``DefRef.lift #[extension, ref]
  let packed ← mkAppOptM ``Packed.pack
    #[some fullCtx, some (Lean.mkConst ``Tp.unit), some (Lean.mkConst ``Unit.unit)]
  mkAppM ``Closure.mk #[lifted, packed]

private def weakenHelper (decl : Lean.Expr) (helper : Helper) : MetaM Helper := do
  pure { helper with ref := ← mkAppM ``DefRef.weaken #[decl, helper.ref] }

private def sourceArgumentType (params : Array ValueParam) : MetaM Lean.Expr :=
  match params with
  | #[param] => pure param.type
  | #[left, right] => mkAppM ``Prod #[left.type, right.type]
  | _ => throwError "reflect%: internal: helper boundary has unsupported value arity"

private def splitTargetArgument (params : Array ValueParam) (argument : Lean.Expr) :
    MetaM (Array Lean.Expr) :=
  match params with
  | #[_] => pure #[argument]
  | #[_, _] => do
      pure #[← mkAppM ``Prod.fst #[argument], ← mkAppM ``Prod.snd #[argument]]
  | _ => throwError "reflect%: internal: helper boundary has unsupported value arity"

private def splitSourceArgument (params : Array ValueParam) (argument : Lean.Expr) :
    MetaM (Array Lean.Expr) :=
  splitTargetArgument params argument

private def argumentRelation (ctx : Lean.Expr) (params : Array ValueParam)
    (sourceType targetType : Lean.Expr) :
    MetaM Lean.Expr := do
  let relations ← params.mapM fun param =>
    mkAppOptM ``ReprSpec.relates #[none, some param.repr, some ctx]
  match params with
  | #[_] => pure relations[0]!
  | #[_, _] =>
      withLocalDeclD `source sourceType fun source => do
      withLocalDeclD `target targetType fun target => do
        let relation ← mkAppM ``And #[
          ← mkAppM' relations[0]! #[← mkAppM ``Prod.fst #[source], ← mkAppM ``Prod.fst #[target]],
          ← mkAppM' relations[1]! #[← mkAppM ``Prod.snd #[source], ← mkAppM ``Prod.snd #[target]]]
        mkLambdaFVars #[source, target] relation
  | _ => throwError "reflect%: internal: helper boundary has unsupported value arity"

private def buildOrdinaryHelper (plan : Plan) (target : TargetEnv)
    (V scope extension selfRef : Lean.Expr) (helpers : Array Helper)
    (spec : Specialization) : MetaM BuiltHelper := do
  let params := spec.valueParams
  let (argTp, resultTp) ← specializationTypes spec
  let targetArgType := mkApp target.values argTp
  let sourceArgType ← sourceArgumentType params
  let resultRel ← mkAppOptM ``ReprSpec.relates
    #[none, some spec.resultRepr, some target.ctx]
  let argRel ← argumentRelation target.ctx params sourceArgType targetArgType
  let self ← semanticClosure target.ctx extension selfRef
  let sourceDecls := params.map fun param => (`sourceArg, fun _ => pure param.type)
  let ⟨semanticBody, genericBody, curriedSound⟩ ←
    withLocalDeclsD sourceDecls fun sourceArgs =>
    withLocalDeclD `genericCaptured (mkApp V (Lean.mkConst ``Tp.unit)) fun genericCaptured =>
    withLocalDeclD `genericArg (mkApp V argTp) fun genericArg =>
    withLocalDeclD `captured (mkApp target.values (Lean.mkConst ``Tp.unit)) fun captured =>
    withLocalDeclD `targetArg targetArgType fun targetArg => do
      let targetArgs ← splitTargetArgument params targetArg
      let relations ← params.mapIdxM fun index param => do
        mkAppM' (← mkAppOptM ``ReprSpec.relates
          #[none, some param.repr, some target.ctx])
          #[sourceArgs[index]!, targetArgs[index]!]
      let Φ ← match relations with
        | #[relation] => pure relation
        | #[left, right] => mkAppM ``And #[left, right]
        | _ => throwError "reflect%: internal: malformed helper relation"
      let fullArgs ← spec.reconstructArgs sourceArgs
      let sourceCall := mkAppN (← mkConstWithFreshMVarLevels spec.name) fullArgs
      let some sourceBody ← unfoldDefinition? sourceCall
        | throwError "reflect%: cannot unfold helper `{spec.name}`"
      let atoms : Array RelatedAtom ← sourceArgs.mapIdxM fun index sourceArg => do
        let related ← withLocalDeclD `hΦ Φ fun hΦ => do
          let proof ← match sourceArgs.size with
            | 1 => pure hΦ
            | _ => mkAppM (if index == 0 then ``And.left else ``And.right) #[hΦ]
          mkLambdaFVars #[hΦ] proof
        pure { source := sourceArg, target := targetArgs[index]!, related }
      let emitted ← emitComp {
        plan, target, scope, extension
        goal := { sourceType := spec.resultType, targetTp := resultTp, relates := resultRel }
        mode := .recursive { spec, argumentTp := argTp, self, selfRef }
        V, Φ, atoms
        genericAtoms := #[{ semantic := targetArg, code := genericArg }]
        helpers
      } sourceBody
      let emitted ← match spec.sourceRange? with
        | some range => annotateEmission range emitted
        | none => pure emitted
      let semanticBody ← mkLambdaFVars #[captured, targetArg] emitted.code
      let genericBody ← mkLambdaFVars #[genericCaptured, genericArg] emitted.generic
      let curriedSound ← withLocalDeclD `hrel Φ fun hrel => do
        mkLambdaFVars (sourceArgs ++ #[targetArg, hrel])
          (← Construct.discharge hrel emitted.sound)
      pure (semanticBody, genericBody, curriedSound)
  let bodySound ← withLocalDeclD `sourceArg sourceArgType fun sourceArg =>
    withLocalDeclD `targetArg targetArgType fun targetArg => do
      let sources ← splitSourceArgument params sourceArg
      let relation ← mkAppM' argRel #[sourceArg, targetArg]
      withLocalDeclD `hrel relation fun hrel => do
        let witness := mkAppN curriedSound (sources ++ #[targetArg, hrel])
        mkLambdaFVars #[sourceArg, targetArg, hrel] witness
  let sourceFn ← withLocalDeclD `sourceArg sourceArgType fun sourceArg => do
    let sources ← splitSourceArgument params sourceArg
    let fullArgs ← spec.reconstructArgs sources
    mkLambdaFVars #[sourceArg] (mkAppN (← mkConstWithFreshMVarLevels spec.name) fullArgs)
  let dispatchType ← withLocalDeclD `argument targetArgType fun argument => do
    let lhs ← mkAppM ``Defs.denote #[target.defs, mkApp (Lean.mkConst ``Extension.refl) target.ctx,
      ← mkAppM ``DefRef.lift #[extension, selfRef], Lean.mkConst ``Unit.unit, argument]
    let rhsExpr := mkAppN semanticBody #[Lean.mkConst ``Unit.unit, argument]
    let rhs ← mkAppM ``Expr.denote #[extension, rhsExpr]
    mkForallFVars #[argument] (← mkAppM ``Eq #[lhs, rhs])
  let dispatch ← mkFreshExprMVar dispatchType
  let adequate ← mkAppM ``RecReflection.nonrecursiveAdequate
    #[target.defs, extension, selfRef, Lean.mkConst ``Unit.unit, argRel, resultRel,
      sourceFn, semanticBody, dispatch, bodySound]
  pure {
    spec, argTp, resultTp, target := self, adequate,
    semanticBody, genericBody, dispatch := dispatch.mvarId!
  }

/-! ## `Nat.brecOn` backend -/

private def buildRecursiveHelper (plan : Plan) (target : TargetEnv)
    (V scope extension selfRef : Lean.Expr) (helpers : Array Helper)
    (spec : Specialization) (arg : ValueParam) (shape : NatBRecShape) :
    MetaM BuiltHelper := do
  let argTp := Lean.mkConst ``Tp.nat
  let resultTp ← reprTp spec.resultRepr
  let resultRel ← mkAppOptM ``ReprSpec.relates
    #[none, some spec.resultRepr, some target.ctx]
  let targetArgType := mkApp target.values argTp
  let self ← semanticClosure target.ctx extension selfRef
  let range? ← match spec.sourceRange? with
    | some range => mkAppM ``Option.some #[range]
    | none => pure (mkApp (Lean.mkConst ``Option.none [Level.zero]) (Lean.mkConst ``SourceRange))
  let semanticResult ← mkAppM ``Expr #[plan.targetSig, scope, target.values, resultTp]
  let baseMVar ← mkFreshExprMVar semanticResult
  let stepMVar ← mkFreshExprMVar (← mkArrow (Lean.mkConst ``Nat) semanticResult)
  let semanticCore ← mkAppM ``Expr.natBrecSemantic #[range?, baseMVar, stepMVar]
  let baseSourceFn := mkApp shape.functional (mkNatLit 0)
  let .forallE _ belowZero _ _ ← whnf (← inferType baseSourceFn)
    | throwError "reflect%: malformed zero argument of `Nat.brecOn` functional"
  let .const ``PUnit [belowLevel] ← whnf belowZero
    | throwError "reflect%: zero argument of `Nat.brecOn` functional is not `PUnit`"
  let baseSource := mkApp baseSourceFn (Lean.mkConst ``PUnit.unit [belowLevel])
  let base ← emitComp {
    plan, target, scope, extension
    goal := { sourceType := spec.resultType, targetTp := resultTp, relates := resultRel }
    mode := .recursive { spec, argumentTp := argTp, self, selfRef }
    V, Φ := Lean.mkConst ``True, helpers
  } baseSource
  baseMVar.mvarId!.assign base.code
  let ⟨stepCode, stepGenericFn, stepSound⟩ ←
    withLocalDeclD `genericPred (mkApp V argTp) fun genericPred =>
    withLocalDeclD `pred (Lean.mkConst ``Nat) fun pred => do
      let sourceCall ← mkAppM ``Nat.brecOn #[pred, shape.functional]
      let go ← mkAppM ``Nat.brecOn.go #[pred, shape.functional]
      let below ← mkAppM ``PProd.mk #[sourceCall, ← mkAppM ``PProd.snd #[go]]
      let stepSource ← mkAppM' shape.functional #[← mkAppM ``Nat.succ #[pred], below]
      let callType ← Construct.recCallType {
        compat := target.compat, defs := target.defs, relates := resultRel,
        sourceCall, targetClosure := self, targetArgument := pred
      }
      withLocalDeclD `ih callType fun ih => do
        let predRel ← mkAppOptM ``ReprSpec.relates
          #[none, some arg.repr, some target.ctx, some pred, some pred]
        let predRelated ← mkExpectedTypeHint (← mkAppM ``Eq.refl #[pred]) predRel
        let recursive : RecEnv := {
          spec := spec
          argumentTp := argTp
          self := self
          selfRef := selfRef
          call? := some {
            sourceCall := sourceCall
            sourceArg := pred
            targetArg := pred
            adequate := ih
          }
        }
        let predAtom : RelatedAtom := {
          source := pred
          target := pred
          related := mkLambda `h .default (Lean.mkConst ``True) predRelated
        }
        let genericPredAtom : ReifiedAtom := { semantic := pred, code := genericPred }
        let emitted ← emitComp {
          plan := plan, target := target, scope := scope, extension := extension,
          goal := { sourceType := spec.resultType, targetTp := resultTp, relates := resultRel },
          mode := .recursive recursive,
          V := V, Φ := Lean.mkConst ``True,
          atoms := #[predAtom],
          genericAtoms := #[genericPredAtom],
          helpers := helpers
        } stepSource
        pure (← mkLambdaFVars #[pred] emitted.code,
          ← mkLambdaFVars #[genericPred] emitted.generic,
          ← mkLambdaFVars #[pred, ih] emitted.sound)
  stepMVar.mvarId!.assign stepCode
  let semanticCore ← instantiateMVars semanticCore
  let semanticBody ← withLocalDeclD `captured (mkApp target.values (Lean.mkConst ``Tp.unit)) fun captured =>
    withLocalDeclD `n targetArgType fun n =>
      mkLambdaFVars #[captured, n] (mkApp semanticCore n)
  let genericBody ← withLocalDeclD `captured (mkApp V (Lean.mkConst ``Tp.unit)) fun captured =>
    withLocalDeclD `n (mkApp V argTp) fun n => do
      let body ← mkAppM ``Expr.natBrecBody #[range?, base.generic, stepGenericFn, n]
      mkLambdaFVars #[captured, n] body
  let sourceFn ← mkConstWithFreshMVarLevels spec.name
  let brecFn ← withLocalDeclD `n (Lean.mkConst ``Nat) fun n => do
    mkLambdaFVars #[n] (← mkAppM ``Nat.brecOn #[n, shape.functional])
  let sourceEq ← mkExpectedTypeHint (← mkAppM ``Eq.refl #[sourceFn])
    (← mkAppM ``Eq #[sourceFn, brecFn])
  let dispatchType ← withLocalDeclD `argument targetArgType fun argument => do
    let lhs ← mkAppM ``Defs.denote #[target.defs, mkApp (Lean.mkConst ``Extension.refl) target.ctx,
      ← mkAppM ``DefRef.lift #[extension, selfRef], Lean.mkConst ``Unit.unit, argument]
    let rhs ← mkAppM ``Expr.denote #[extension, mkApp semanticCore argument]
    mkForallFVars #[argument] (← mkAppM ``Eq #[lhs, rhs])
  let dispatch ← mkFreshExprMVar dispatchType
  let adequate ← Construct.natBrecAdequate {
    compat := target.compat, defs := target.defs, extension, self := selfRef,
    captured := Lean.mkConst ``Unit.unit, relates := resultRel, sourceFunction := sourceFn,
    functional := shape.functional, sourceEquality := sourceEq, range := range?,
    base := base.code, step := stepCode, dispatch,
    baseSound := base.sound, stepSound
  }
  pure {
    spec, argTp, resultTp, target := self, adequate,
    semanticBody, genericBody, dispatch := dispatch.mvarId!
  }

private def buildHelper (plan : Plan) (target : TargetEnv)
    (V scope extension selfRef : Lean.Expr) (helpers : Array Helper)
    (spec : Specialization) : MetaM BuiltHelper :=
  match spec.boundary with
  | .natBRec arg shape => buildRecursiveHelper plan target V scope extension selfRef helpers spec arg shape
  | _ => buildOrdinaryHelper plan target V scope extension selfRef helpers spec

/-! ## Plan execution -/

structure Execution where
  plan : Plan
  goal : EmitGoal
  program : Lean.Expr
  semanticProgram : Lean.Expr
  sound : Lean.Expr

private def installDefinitions (plan : Plan) (target : TargetEnv) (V : Lean.Expr) :
    MetaM TableState := do
  let emptyScope ← mkAppOptM ``List.nil #[some (Lean.mkConst ``DefSig)]
  let semanticNil ← mkAppOptM ``Defs.nil #[some plan.targetSig, some target.values]
  let genericNil ← mkAppOptM ``Defs.nil #[some plan.targetSig, some V]
  let mut state : TableState := {
    scope := emptyScope,
    extension := ← extensionFor emptyScope plan.specializations,
    semanticDefs := semanticNil,
    genericDefs := genericNil
  }
  for index in [0:plan.specializations.size] do
    let spec := plan.specializations[index]!
    let (input, output) ← specializationTypes spec
    let decl ← mkDefSig input output
    let scope ← mkAppM ``List.cons #[decl, state.scope]
    let extension ← extensionFor scope
      (plan.specializations.extract (index + 1) plan.specializations.size)
    let selfRef ← mkAppOptM ``DefRef.here #[some decl, some state.scope]
    let helpers ← state.helpers.mapM (weakenHelper decl)
    let built ← buildHelper plan target V scope extension selfRef helpers spec
    let semanticDefs ← mkAppOptM ``Defs.add
      #[some plan.targetSig, some target.values, some state.scope, some decl,
        some state.semanticDefs, some built.semanticBody]
    let genericDefs ← mkAppOptM ``Defs.add
      #[some plan.targetSig, some V, some state.scope, some decl,
        some state.genericDefs, some built.genericBody]
    let installed : Helper := {
      built.toHelperSemantics with ref := selfRef
    }
    state := {
      scope, extension, semanticDefs, genericDefs,
      helpers := helpers.push installed,
      dispatches := state.dispatches.push built.dispatch
    }
  pure state

def execute (plan : Plan) (source : Lean.Expr) (range? : Option Lean.Expr) :
    TermElabM Execution := do
  let ctx ← fullContext plan.specializations
  let values ← withLocalDeclD `tp (Lean.mkConst ``Tp) fun tp => do
    mkLambdaFVars #[tp] (← mkAppM ``Tp.denote #[ctx, tp])
  let defsType ← mkAppM ``Defs #[plan.targetSig, values, ctx]
  let defsMVar ← mkFreshExprMVar defsType
  let target ← mkTargetEnv plan.targetSig plan.compat ctx defsMVar
  let targetTp ← reprTp plan.resultRepr
  let relates ← mkAppOptM ``ReprSpec.relates
    #[none, some plan.resultRepr, some ctx]
  let goal : EmitGoal := { sourceType := plan.resultType, targetTp, relates }
  let VType := .forallE `tp (Lean.mkConst ``Tp) (mkSort 1) .default
  withLocalDeclD `V VType fun V => do
    let table ← installDefinitions plan target V
    defsMVar.mvarId!.assign table.semanticDefs
    for dispatch in table.dispatches do
      let type ← instantiateMVars (← dispatch.getType)
      let proof ← forallTelescope type fun binders body => do
        unless body.isAppOfArity ``Eq 3 do
          throwError "reflect%: internal: definition dispatch is not an equality"
        let lhs := body.getArg! 1
        let refl ← mkExpectedTypeHint (← mkAppM ``Eq.refl #[lhs]) body
        mkLambdaFVars binders refl
      dispatch.assign proof
    let root ← emitComp {
      plan, target := { target with defs := table.semanticDefs },
      scope := ctx, extension := mkApp (Lean.mkConst ``Extension.refl) ctx,
      goal, mode := .ordinary, V, Φ := Lean.mkConst ``True, helpers := table.helpers
    } source
    let mut root := root
    if let some decl := source.getAppFn.constName? then
      if let some range ← declarationSourceRange? decl then
        root ← annotateEmission range root
    if let some range := range? then root ← annotateEmission range root
    let noArgs ← mkAppOptM ``List.nil #[some (Lean.mkConst ``Tp)]
    let semanticArgsType ← mkAppM ``MainArgs #[values, noArgs]
    let genericArgsType ← mkAppM ``MainArgs #[V, noArgs]
    let semanticMain ← withLocalDeclD `args semanticArgsType fun args =>
      mkLambdaFVars #[args] root.code
    let genericMain ← withLocalDeclD `args genericArgsType fun args =>
      mkLambdaFVars #[args] root.generic
    let semanticProgram ← mkAppM ``Program.mk #[table.semanticDefs, semanticMain]
    let genericProgram ← mkAppM ``Program.mk #[table.genericDefs, genericMain]
    let program ← mkAppM ``Code.mk #[ctx, ← mkLambdaFVars #[V] genericProgram]
    let sound ← mkAppM ``ReflectionWitness.close #[root.sound]
    pure { plan, goal, program, semanticProgram, sound }

/-! ## Public packaging -/

private def packReflection (execution : Execution) (source : Lean.Expr) : MetaM Lean.Expr := do
  let codeType ← inferType execution.program
  let predicate ← withLocalDeclD `code codeType fun code => do
    let denoted ← mkAppM ``Closed.denote #[code]
    let codeCtx ← mkAppM ``Code.ctx #[code]
    let property ← mkAppM ``ITree.CompE.Eutt #[mkApp execution.plan.compat codeCtx,
      execution.goal.relates,
      ← mkAppM ``Free.toITree #[source], denoted]
    mkLambdaFVars #[code] property
  let property := mkApp predicate execution.program
  let sound ← mkExpectedTypeHint execution.sound property
  mkAppOptM ``Subtype.mk #[some codeType, some predicate, some execution.program, some sound]

def reflectProgram (source : Lean.Expr) (range? : Option Lean.Expr := none) :
    TermElabM Lean.Expr := do
  let plan ← discover source
  let execution ← execute plan source range?
  packReflection execution source

def reflectTerm (source : Lean.Expr) (range? : Option Lean.Expr := none) : TermElabM Lean.Expr := do
  let plan ← discover source
  let execution ← execute plan source range?
  mkAppM ``Sigma.mk #[execution.semanticProgram, execution.sound]

end Reflector
end Ast
end Freigen
