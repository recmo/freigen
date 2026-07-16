import Freigen.Reflect.Plan
import Freigen.Reflect.Value
import Freigen.Reflect.Construct
import Lean.Elab.SyntheticMVars

namespace Freigen
namespace Ast
namespace Reflector

open Lean Meta Elab Term

/-! ## Execution state -/

/-- A source/semantic-target relation available while constructing proofs and semantic code.
    Generic PHOAS reification is intentionally a separate environment because source-only branch
    binders have no generic counterpart. -/
structure RelatedAtom where
  source : Lean.Expr
  target : Lean.Expr
  related : Lean.Expr

structure Emission where
  code : Lean.Expr
  generic : Lean.Expr
  sound : Lean.Expr

structure HelperSemantics where
  spec : Specialization
  argTp : Lean.Expr
  resultTp : Lean.Expr
  target : Lean.Expr
  adequate : Lean.Expr

structure Helper extends HelperSemantics where
  ref : Lean.Expr

def annotateEmission (range : Lean.Expr) (emission : Emission) : MetaM Emission := do
  pure {
    code := ← mkAppM ``Expr.source #[range, emission.code]
    generic := ← mkAppM ``Expr.source #[range, emission.generic]
    sound := ← Construct.source emission.code range emission.sound
  }

private def helperForCall? (helpers : Array Helper) (call : Lean.Expr) : MetaM (Option Helper) := do
  helpers.findM? fun helper => helper.spec.matchesCall call

/-- Expose the next source node while preserving helper calls selected by the plan. -/
private partial def exposeComp (source : Lean.Expr) (helpers : Array Helper) : MetaM Lean.Expr := do
  let source ← whnfCore (← instantiateMVars source)
  if (← helperForCall? helpers source).isSome then return source
  if let some name := source.getAppFn.constName? then
    if isReflectorCore name then return source
    if let some unfolded ← unfoldDefinition? source then
      return ← exposeComp unfolded helpers
  return source

/-! ## Source matching

The emitter recognizes only the computation spine. Everything else is either a planned helper
call (handled before this classifier) or an implementation detail that may be unfolded once.
-/
private inductive SourceNode where
  | bind (head k : Lean.Expr)
  | ret (value : Lean.Expr)
  | op (source : Lean.Expr)
  | other (source : Lean.Expr)

private def matchSource (source : Lean.Expr) : SourceNode :=
  let fn := source.getAppFn.constName?
  let args := source.getAppArgs
  if fn == some ``Free.bind || fn == some ``Bind.bind then
    .bind args[args.size - 2]! args[args.size - 1]!
  else if fn == some ``Free.pure || fn == some ``Pure.pure then
    .ret args.back!
  else if fn == some ``Free.op then .op source
  else .other source

/-! ## Shared construction machinery -/

structure EmitGoal where
  sourceType : Lean.Expr
  targetTp : Lean.Expr
  relates : Lean.Expr

/-- Target interpretation shared by every node in one emission run. -/
structure TargetEnv where
  ctx : Lean.Expr
  compat : Lean.Expr
  monad : Lean.Expr
  values : Lean.Expr
  defs : Lean.Expr

def mkTargetEnv (H compatFn ctx defs : Lean.Expr) : MetaM TargetEnv := do
  let spec ← mkAppM ``Signature.spec #[H, ctx]
  let monad := mkApp (Lean.mkConst ``ITree.CompE [Level.zero, Level.zero]) spec
  let values ← withLocalDeclD `tp (mkConst ``Tp) fun tp => do
    mkLambdaFVars #[tp] (← mkAppM ``Tp.denote #[ctx, tp])
  pure { ctx, compat := mkApp compatFn ctx, monad, values, defs }

def reprTp (repr : Lean.Expr) : MetaM Lean.Expr := do
  mkAppM ``ReprSpec.code #[repr]

private def pureSourceK (sourceSig type : Lean.Expr) : MetaM Lean.Expr :=
  withLocalDeclD `result type fun result => do
    mkLambdaFVars #[result] (← mkAppOptM ``Free.pure
      #[some sourceSig, some type, some result])

private def lookupAtom? (atoms : Array RelatedAtom) (source : Lean.Expr) : Option RelatedAtom :=
  atoms.find? fun atom => atom.source == source

private def emitValue (ctx Φ repr source : Lean.Expr) (atoms : Array RelatedAtom) : MetaM RelatedAtom := do
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
      let relation ← mkAppOptM ``ReprSpec.relates
        #[none, some repr, some ctx, some source, some target]
      let related ← mkLambdaFVars #[hΦ] (← mkExpectedTypeHint equality relation)
      return { source, target, related }
  let target ← mkAppOptM ``ReprSpec.encode #[none, some repr, some ctx, some source]
  let relatedProof ← mkAppOptM ``ReprSpec.encode_related
    #[none, some repr, some ctx, some source]
  let related := mkLambda `h .default Φ relatedProof
  pure { source, target, related }

structure EncodedCall where
  input : RelatedAtom
  inputTp : Lean.Expr

/-- Encode the one represented argument, or the supported pair of represented arguments, of a
    spilled helper.  Both ordinary and recursive emission use exactly this calling convention. -/
private def encodeCall (ctx Φ : Lean.Expr) (spec : Specialization) (call : Lean.Expr)
    (atoms : Array RelatedAtom) : MetaM EncodedCall := do
  let args := call.getAppArgs
  let (position₁, param₁, param₂?) := match spec.boundary with
    | .unary before param _ => (before.size, param, none)
    | .natBRec param _ => (0, param, none)
    | .pair before left between right _ =>
        (before.size, left, some (before.size + between.size + 1, right))
  let source₁ := args[position₁]!
  let encoded₁ ← emitValue ctx Φ param₁.repr source₁ atoms
  let some (position₂, param₂) := param₂? | return {
      input := encoded₁
      inputTp := ← mkAppM ``ReprSpec.code #[param₁.repr]
    }
  let source₂ := args[position₂]!
  let encoded₂ ← emitValue ctx Φ param₂.repr source₂ atoms
  let code₁ ← mkAppM ``ReprSpec.code #[param₁.repr]
  let code₂ ← mkAppM ``ReprSpec.code #[param₂.repr]
  let related ← withLocalDeclD `hΦ Φ fun hΦ => do
    let proof ← mkAppM ``And.intro #[mkApp encoded₁.related hΦ, mkApp encoded₂.related hΦ]
    mkLambdaFVars #[hΦ] proof
  return {
    input := {
      source := ← mkAppM ``Prod.mk #[source₁, source₂]
      target := ← mkAppM ``Prod.mk #[encoded₁.target, encoded₂.target]
      related
    }
    inputTp := ← mkAppM ``Tp.prod #[code₁, code₂]
  }

structure EncodedOp where
  sourceOp : Lean.Expr
  sourceInput : Lean.Expr
  sourceBlocks : Lean.Expr
  sourceK : Lean.Expr
  targetOp : Lean.Expr
  witness : Lean.Expr
  input : RelatedAtom

/-- The ordinary and recursive proof rules use the same operation lookup and input encoding. -/
private def encodeOp (plan : Plan) (targetCtx compat Φ source : Lean.Expr)
    (atoms : Array RelatedAtom) : MetaM EncodedOp := do
  let args := source.getAppArgs
  let sourceOp := args[2]!
  let sourceInput := args[3]!
  let sourceBlocks := args[4]!
  let sourceK := args[5]!
  let spec ← resolveOp compat sourceOp
  let targetOp ← mkAppM ``OpSpec.target #[spec]
  let witness ← mkAppM ``OpSpec.witness #[spec]
  let inputTp ← mkAppM ``Signature.input #[plan.targetSig, targetOp]
  let inputRel ← mkAppM ``ITree.HSig.Compat.input #[compat, witness]
  let inputRepr ← resolveReprFor targetCtx (← inferType sourceInput) inputTp inputRel
  let input ← emitValue targetCtx Φ inputRepr sourceInput atoms
  pure { sourceOp, sourceInput, sourceBlocks, sourceK, targetOp, witness, input }

/-- Build the target continuation and its relational witness.  Operation continuations, helper
    continuations, and recursive-call continuations differ only in how their next source term is
    emitted. -/
private def emitContinuation (V Φ targetTp sourceType targetType sourceK : Lean.Expr)
    (atoms : Array RelatedAtom) (genericAtoms : Array ReifiedAtom)
    (relate : Lean.Expr → Lean.Expr → MetaM Lean.Expr)
    (emitNext : Lean.Expr → Array RelatedAtom → Array ReifiedAtom → MetaM Emission) :
    MetaM Emission := do
  withLocalDeclD `genericTarget (mkApp V targetTp) fun genericTarget =>
  withLocalDeclD `target targetType fun target =>
  withLocalDeclD `source sourceType fun source => do
    let relation ← relate source target
    withLocalDeclD `hrel relation fun hrel => do
      let related := mkLambda `h .default Φ hrel
      let emitted ← emitNext (mkApp sourceK source) (atoms.push {
        source := source, target := target, related := related })
        (genericAtoms.push { semantic := target, code := genericTarget })
      if emitted.code.containsFVar source.fvarId! || emitted.code.containsFVar hrel.fvarId! then
        throwError "reflect%: target continuation depends on source-only relational binders"
      let witness := emitted.sound
      pure {
        code := ← mkLambdaFVars #[target] emitted.code
        generic := ← mkLambdaFVars #[genericTarget] emitted.generic
        sound := ← mkLambdaFVars #[target, source, hrel] witness
      }

structure RecCallEnv where
  sourceCall : Lean.Expr
  sourceArg : Lean.Expr
  targetArg : Lean.Expr
  adequate : Lean.Expr

structure RecEnv where
  spec : Specialization
  argumentTp : Lean.Expr
  self : Lean.Expr
  selfRef : Lean.Expr
  call? : Option RecCallEnv := none

/-! ## Unified computation execution

`matchSource` above is the classifier. `emitComp` below consumes that classification and constructs
the semantic AST, generic AST, and proof at the same case site. `EmitMode` supplies only the extra
environment available inside a recursive body; it does not select a second traversal.
-/

inductive EmitMode where
  | ordinary
  | recursive (env : RecEnv)

structure EmitContext where
  plan : Plan
  target : TargetEnv
  scope : Lean.Expr
  extension : Lean.Expr
  goal : EmitGoal
  mode : EmitMode
  V : Lean.Expr
  Φ : Lean.Expr
  atoms : Array RelatedAtom := #[]
  genericAtoms : Array ReifiedAtom := #[]
  helpers : Array Helper := #[]

/-! ### Operation construction -/

private structure BlockEmission where
  code : Lean.Expr
  generic : Lean.Expr
  sound : Lean.Expr

private def emitEmptyBlocks (ctx : EmitContext) (op : EncodedOp) : MetaM BlockEmission := do
  let targetBranchType ← mkAppM ``Signature.branch #[ctx.plan.targetSig, op.targetOp]
  withLocalDeclD `bt targetBranchType fun bt => do
    let inputTp ← mkAppM ``Signature.branchInput #[ctx.plan.targetSig, op.targetOp, bt]
    let outputTp ← mkAppM ``Signature.branchOutput #[ctx.plan.targetSig, op.targetOp, bt]
    withLocalDeclD `xt (mkApp ctx.target.values inputTp) fun xt => do
      let semanticResult ← mkAppM ``Expr
        #[ctx.plan.targetSig, ctx.scope, ctx.target.values, outputTp]
      let code ← mkLambdaFVars #[bt, xt]
        (← mkAppOptM ``Empty.elim #[some semanticResult, some bt])
      let generic ← withLocalDeclD `genericInput (mkApp ctx.V inputTp) fun genericInput => do
        let genericResult ← mkAppM ``Expr
          #[ctx.plan.targetSig, ctx.scope, ctx.V, outputTp]
        mkLambdaFVars #[bt, genericInput]
          (← mkAppOptM ``Empty.elim #[some genericResult, some bt])
      let sourceBranchType ← mkAppM ``ITree.HSig.branch
        #[ctx.plan.sourceSig, op.sourceOp]
      let sound ← withLocalDeclD `bs sourceBranchType fun bs => do
        let branchRel ← mkAppM ``ITree.HSig.Compat.branch
          #[ctx.target.compat, op.witness, bs, bt]
        withLocalDeclD `hbr branchRel fun hbr => do
          let sourceInputType ← mkAppM ``ITree.HSig.branchInput
            #[ctx.plan.sourceSig, op.sourceOp, bs]
          withLocalDeclD `xs sourceInputType fun xs => do
            let inputRel ← mkAppM ``ITree.HSig.Compat.branchInput
              #[ctx.target.compat, op.witness, hbr, xs, xt]
            withLocalDeclD `hx inputRel fun hx => do
              let blockRel ← mkAppM ``ITree.HSig.Compat.branchOutput
                #[ctx.target.compat, op.witness, hbr]
              let sourceBlock ← mkAppM' op.sourceBlocks #[bs, xs]
              let targetBlock := mkAppN code #[bt, xt]
              let witnessType ← mkAppM ``ReflectionWitness #[ctx.target.compat,
                ctx.target.defs, ctx.extension, ctx.Φ, outputTp, blockRel,
                sourceBlock, targetBlock]
              mkLambdaFVars #[bt, xt, bs, hbr, xs, hx]
                (← mkAppOptM ``Empty.elim #[some witnessType, some bt])
      pure { code, generic, sound }

private def emitOrdinaryDynamicBlocks (ctx : EmitContext) (op : EncodedOp)
    (targetBranchType : Lean.Expr)
    (recur : EmitContext → Lean.Expr → MetaM Emission) : MetaM BlockEmission := do
  let plan := ctx.plan
  withLocalDeclD `bt targetBranchType fun bt => do
    let inputCode ← mkAppM ``Signature.branchInput #[plan.targetSig, op.targetOp, bt]
    withLocalDeclD `genericInput (mkApp ctx.V inputCode) fun genericInput =>
    withLocalDeclD `xt (mkApp ctx.target.values inputCode) fun xt => do
      let sourceBranchType ← mkAppM ``ITree.HSig.branch #[plan.sourceSig, op.sourceOp]
      withLocalDeclD `bs sourceBranchType fun bs => do
        let branchRel ← mkAppM ``ITree.HSig.Compat.branch
          #[ctx.target.compat, op.witness, bs, bt]
        withLocalDeclD `hbr branchRel fun hbr => do
          let sourceInputType ← mkAppM ``ITree.HSig.branchInput
            #[plan.sourceSig, op.sourceOp, bs]
          withLocalDeclD `xs sourceInputType fun xs => do
            let inputRel ← mkAppM ``ITree.HSig.Compat.branchInput
              #[ctx.target.compat, op.witness, hbr, xs, xt]
            withLocalDeclD `hx inputRel fun hx => do
              let blockSource ← mkAppM' op.sourceBlocks #[bs, xs]
              let blockSourceType ← inferType blockSource
              let blockTargetTp ←
                mkAppM ``Signature.branchOutput #[plan.targetSig, op.targetOp, bt]
              let blockRel ← mkAppM ``ITree.HSig.Compat.branchOutput
                #[ctx.target.compat, op.witness, hbr]
              let emitted ← recur { ctx with
                goal := {
                  sourceType := blockSourceType.getArg! 1
                  targetTp := blockTargetTp
                  relates := blockRel
                }
                mode := .ordinary
                atoms := ctx.atoms.push {
                  source := bs, target := bt,
                  related := mkLambda `h .default ctx.Φ hbr } |>.push {
                  source := xs, target := xt,
                  related := mkLambda `h .default ctx.Φ hx }
                genericAtoms := ctx.genericAtoms.push {
                  semantic := xt, code := genericInput }
              } blockSource
              if emitted.code.containsFVar bs.fvarId! ||
                  emitted.code.containsFVar hbr.fvarId! ||
                  emitted.code.containsFVar xs.fvarId! ||
                  emitted.code.containsFVar hx.fvarId! then
                throwError "reflect%: block AST depends on source-only relational binders"
              pure {
                code := ← mkLambdaFVars #[bt, xt] emitted.code
                generic := ← mkLambdaFVars #[bt, genericInput] emitted.generic
                sound := ← mkLambdaFVars #[bt, xt]
                  (← mkLambdaFVars #[bs, hbr, xs, hx] emitted.sound)
              }

private def emitBlocks (ctx : EmitContext) (op : EncodedOp)
    (kCode kSound targetBranchType : Lean.Expr)
    (recur : EmitContext → Lean.Expr → MetaM Emission) : MetaM BlockEmission := do
  let blocks ← if ← isDefEq targetBranchType (mkConst ``Empty) then
    emitEmptyBlocks ctx op
  else
    emitOrdinaryDynamicBlocks ctx op targetBranchType recur
  let sound ← Construct.opSound {
    compat := ctx.target.compat, sourceOp := op.sourceOp, targetOp := op.targetOp
    witness := op.witness, targetInput := op.input.target,
    inputRelated := op.input.related, sourceBlocks := op.sourceBlocks,
    targetBlocks := blocks.code, blockSound := blocks.sound,
    sourceContinuation := op.sourceK, targetContinuation := kCode,
    continuationSound := kSound
  }
  pure { blocks with sound }

private def emitOperation (ctx : EmitContext) (source : Lean.Expr)
    (recur : EmitContext → Lean.Expr → MetaM Emission) : MetaM Emission := do
  let plan := ctx.plan
  let target := ctx.target
  let op ← encodeOp plan target.ctx target.compat ctx.Φ source ctx.atoms
  let targetOutputCode ← mkAppM ``Signature.output #[plan.targetSig, op.targetOp]
  let targetOutputTp := targetOutputCode
  let targetOutputType := mkApp target.values targetOutputCode
  let sourceOutputType ← mkAppM ``ITree.HSig.output #[plan.sourceSig, op.sourceOp]
  let ⟨kCode, kGeneric, kSound⟩ ← emitContinuation ctx.V ctx.Φ targetOutputTp
    sourceOutputType targetOutputType op.sourceK ctx.atoms ctx.genericAtoms
    (fun source target => mkAppM ``ITree.HSig.Compat.output
      #[ctx.target.compat, op.witness, source, target])
    (fun next atoms genericAtoms => recur { ctx with atoms, genericAtoms } next)
  let targetBranchType ← mkAppM ``Signature.branch #[plan.targetSig, op.targetOp]
  let blocks ← emitBlocks ctx op kCode kSound targetBranchType recur
  let code ← Construct.op plan.targetSig ctx.scope ctx.target.values
    op.targetOp op.input.target blocks.code kCode
  let inputCode ← mkAppM ``Signature.input #[plan.targetSig, op.targetOp]
  let generic ← emitGenericValue plan.targetSig ctx.scope ctx.V inputCode op.input.target
    ctx.genericAtoms fun input => Construct.op plan.targetSig ctx.scope ctx.V
      op.targetOp input blocks.generic kGeneric
  pure { code, generic, sound := blocks.sound }

/-! ### Definition-call construction -/

private def isRecursiveCall (ctx : EmitContext) (candidate : Lean.Expr) : MetaM Bool := do
  let .recursive env := ctx.mode | return false
  if let some call := env.call? then
    if ← isDefEq candidate call.sourceCall then return true
  env.spec.matchesCall candidate

private def emitRecursiveCall (ctx : EmitContext) (sourceCall sourceK : Lean.Expr)
    (recur : EmitContext → Lean.Expr → MetaM Emission) : MetaM Emission := do
  let plan := ctx.plan
  let target := ctx.target
  let mode := ctx.mode
  let V := ctx.V
  let Φ := ctx.Φ
  let atoms := ctx.atoms
  let genericAtoms := ctx.genericAtoms
  let .recursive env := mode
    | throwError "reflect%: internal: recursive call outside a recursive definition"
  let some call := env.call?
    | throwError "reflect%: `Nat.brecOn` zero functional unexpectedly contains a recursive call"
  unless ← isDefEq sourceCall call.sourceCall do
    throwError "reflect%: recursive `Nat.brecOn` functional does not call its immediate induction hypothesis{indentExpr sourceCall}"
  let .natBRec argParam _ := env.spec.boundary
    | throwError "reflect%: internal: recursive emission used a nonrecursive helper boundary"
  let argRepr := argParam.repr
  let targetArg ← emitValue target.ctx Φ argRepr call.sourceArg atoms
  unless ← isDefEq targetArg.target call.targetArg do
    throwError "reflect%: recursive `Nat.brecOn` functional changed its induction-hypothesis argument{indentExpr targetArg.target}"
  let ihAt ← withLocalDeclD `hΦ Φ fun hΦ => mkLambdaFVars #[hΦ] call.adequate
  let resultRel ← mkAppOptM ``ReprSpec.relates
    #[none, some env.spec.resultRepr, some target.ctx]
  let resultTp ← reprTp env.spec.resultRepr
  let targetResultType := mkApp target.values resultTp
  let ⟨kCode, kGeneric, kSound⟩ ← emitContinuation V Φ resultTp
    env.spec.resultType targetResultType sourceK atoms genericAtoms
    (fun source target => mkAppM' resultRel #[source, target])
    (fun next atoms genericAtoms =>
      recur { ctx with atoms, genericAtoms } next)
  let sound ← Construct.recursiveCall call.sourceCall env.self targetArg.target ihAt
    kCode kSound
  let code ← Construct.app plan.targetSig ctx.scope target.values env.argumentTp resultTp
    env.self targetArg.target kCode
  let generic ← emitGenericValue plan.targetSig ctx.scope V (mkConst ``Tp.nat)
    targetArg.target genericAtoms fun input => do
      withLocalDeclD `unit (mkApp V (mkConst ``Tp.unit)) fun unit => do
        withLocalDeclD `selfFn (mkApp V (← mkAppM ``Tp.fn #[env.argumentTp, resultTp]))
            fun selfFn => do
          let applied ← Construct.app plan.targetSig ctx.scope V env.argumentTp resultTp
            selfFn input kGeneric
          let closed ← Construct.closure env.selfRef unit
            (← mkLambdaFVars #[selfFn] applied)
          mkAppM ``Expr.unitLit #[← mkLambdaFVars #[unit] closed]
  pure { code, generic, sound }

private def emitHelperCall (ctx : EmitContext) (helper : Helper) (sourceCall : Lean.Expr)
    (sourceK? : Option Lean.Expr)
    (recur : EmitContext → Lean.Expr → MetaM Emission) : MetaM Emission := do
  let plan := ctx.plan
  let target := ctx.target
  let mode := ctx.mode
  let V := ctx.V
  let Φ := ctx.Φ
  let atoms := ctx.atoms
  let genericAtoms := ctx.genericAtoms
  let encoded ← encodeCall target.ctx Φ helper.spec sourceCall atoms
  let hEutt ← withLocalDeclD `hΦ Φ fun hΦ =>
    mkLambdaFVars #[hΦ]
      (mkAppN helper.adequate
        #[encoded.input.source, encoded.input.target, mkApp encoded.input.related hΦ])
  let resultTp ← reprTp helper.spec.resultRepr
  let inputCode := encoded.inputTp
  match sourceK? with
  | none =>
      let .ordinary := mode
        | throwError "reflect%: internal: direct recursive helper call lacks a continuation"
      let sound ← Construct.directCall target.compat target.defs ctx.extension Φ
        helper.target encoded.input.target hEutt
      let targetResultType := mkApp target.values resultTp
      let returnCode ← withLocalDeclD `result targetResultType fun result => do
        mkLambdaFVars #[result]
          (← Construct.ret plan.targetSig ctx.scope target.values resultTp result)
      let genericReturn ← withLocalDeclD `result (mkApp V resultTp) fun result => do
        mkLambdaFVars #[result]
          (← Construct.ret plan.targetSig ctx.scope V resultTp result)
      let code ← Construct.app plan.targetSig ctx.scope target.values encoded.inputTp resultTp
        helper.target encoded.input.target returnCode
      let generic ← emitGenericValue plan.targetSig ctx.scope V inputCode
        encoded.input.target genericAtoms fun input => do
          withLocalDeclD `unit (mkApp V (mkConst ``Tp.unit)) fun unit => do
            withLocalDeclD `fn (mkApp V (← mkAppM ``Tp.fn #[encoded.inputTp, resultTp])) fun fn => do
              let applied ← Construct.app plan.targetSig ctx.scope V encoded.inputTp resultTp
                fn input genericReturn
              let closed ← Construct.closure helper.ref unit
                (← mkLambdaFVars #[fn] applied)
              mkAppM ``Expr.unitLit #[← mkLambdaFVars #[unit] closed]
      pure { code, generic, sound }
  | some sourceK =>
      let resultRel ← mkAppOptM ``ReprSpec.relates
        #[none, some helper.spec.resultRepr, some target.ctx]
      let targetResultType := mkApp target.values resultTp
      let ⟨kCode, kGeneric, kSound⟩ ← emitContinuation V Φ resultTp
        helper.spec.resultType targetResultType sourceK atoms genericAtoms
        (fun source target => mkAppM' resultRel #[source, target])
        (fun next atoms genericAtoms =>
          recur { ctx with atoms, genericAtoms } next)
      let sound ← Construct.bindCall target.compat target.defs ctx.extension Φ
        helper.target encoded.input.target hEutt kCode kSound
      let code ← Construct.app plan.targetSig ctx.scope target.values encoded.inputTp resultTp
        helper.target encoded.input.target kCode
      let generic ← emitGenericValue plan.targetSig ctx.scope V inputCode encoded.input.target
        genericAtoms fun input => do
          withLocalDeclD `unit (mkApp V (mkConst ``Tp.unit)) fun unit => do
            withLocalDeclD `fn (mkApp V (← mkAppM ``Tp.fn #[encoded.inputTp, resultTp])) fun fn => do
              let applied ← Construct.app plan.targetSig ctx.scope V encoded.inputTp resultTp
                fn input kGeneric
              let closed ← Construct.closure helper.ref unit
                (← mkLambdaFVars #[fn] applied)
              mkAppM ``Expr.unitLit #[← mkLambdaFVars #[unit] closed]
      pure { code, generic, sound }

/-! ### Return construction -/

private def emitReturn (ctx : EmitContext) (value : Lean.Expr) : MetaM Emission := do
  let plan := ctx.plan
  let target := ctx.target
  let goal := ctx.goal
  let V := ctx.V
  let Φ := ctx.Φ
  let atoms := ctx.atoms
  let genericAtoms := ctx.genericAtoms
  let repr ← resolveReprFor target.ctx (← inferType value) goal.targetTp goal.relates
  let atom ← emitValue target.ctx Φ repr value atoms
  let sound ← Construct.retSound target.compat target.defs ctx.extension goal.targetTp
    atom.target atom.related
  let code ← Construct.ret plan.targetSig ctx.scope target.values goal.targetTp atom.target
  let valueCode ← mkAppM ``ReprSpec.code #[repr]
  let generic ← emitGenericValue plan.targetSig ctx.scope V valueCode atom.target
    genericAtoms fun value => Construct.ret plan.targetSig ctx.scope V goal.targetTp value
  pure { code, generic, sound }

/-! ### Computation dispatcher -/

partial def emitComp (ctx : EmitContext) (source : Lean.Expr) : MetaM Emission := do
  let mode := ctx.mode
  let helpers := ctx.helpers
  let initialSource ← instantiateMVars source
  let rawSource ← match mode with
    | .ordinary => exposeComp initialSource helpers
    | .recursive env =>
        let initialName := initialSource.getAppFn.constName?
        let named := helpers.any fun helper =>
          initialName == some helper.spec.name || initialName == some env.spec.name
        if named then pure initialSource else exposeComp initialSource helpers
  if let .ordinary := mode then
    if let some helper ← helperForCall? helpers rawSource then
      return ← emitHelperCall ctx helper rawSource none emitComp
  match matchSource rawSource with
  | .bind head sourceK =>
      if ← isRecursiveCall ctx head then return ← emitRecursiveCall ctx head sourceK emitComp
      let coreHead ← exposeComp head helpers
      if let some helper ← helperForCall? helpers coreHead then
        return ← emitHelperCall ctx helper coreHead (some sourceK) emitComp
      let coreBind ← mkAppM ``Free.bind #[coreHead, sourceK]
      let some reduced ← unfoldDefinition? coreBind
        | throwError "reflect%: cannot reduce core `Free.bind` plumbing"
      emitComp ctx reduced
  | .ret value =>
      emitReturn ctx value
  | .op source =>
      emitOperation ctx source emitComp
  | .other source =>
      match mode with
      | .ordinary => throwError "reflect%: pass 2 does not recognize computation{indentExpr source}"
      | .recursive env =>
          if ← isRecursiveCall ctx source then
            return ← emitRecursiveCall ctx source
              (← pureSourceK ctx.plan.sourceSig env.spec.resultType) emitComp
          if let some helper ← helperForCall? helpers source then
            return ← emitHelperCall ctx helper source
              (some (← pureSourceK ctx.plan.sourceSig helper.spec.resultType)) emitComp
          if let some name := source.getAppFn.constName? then
            if name != env.spec.name then
              if let some unfolded ← unfoldDefinition? source then
                return ← emitComp ctx unfolded
          throwError "reflect%: recursive pass does not recognize computation{indentExpr source}"


end Reflector
end Ast
end Freigen
