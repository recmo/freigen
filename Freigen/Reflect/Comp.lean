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
  target : Lean.Expr
  adequate : Lean.Expr

structure Helper extends HelperSemantics where
  generic : Lean.Expr

def annotateEmission (range : Lean.Expr) (emission : Emission) : MetaM Emission := do
  pure {
    code := ← mkAppM ``Expr.source #[range, emission.code]
    generic := ← mkAppM ``Expr.source #[range, emission.generic]
    sound := ← mkAppM ``Reflection.source #[emission.code, range, emission.sound]
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
  monad : Lean.Expr
  values : Lean.Expr
  noRecursion : Lean.Expr

def mkTargetEnv (H : Lean.Expr) : MetaM TargetEnv := do
  let spec ← mkAppM ``Signature.spec #[H]
  let monad := mkApp (Lean.mkConst ``ITree.CompE [Level.zero, Level.zero]) spec
  let values ← mkAppM ``Tp.denote #[monad]
  let slotType ← mkAppM ``Prod #[mkConst ``Tp, mkConst ``Tp]
  let noRecursion ← mkAppOptM ``Option.none #[some slotType]
  pure { monad, values, noRecursion }

def reprTp (repr : Lean.Expr) : MetaM Lean.Expr := do
  mkAppM ``Tp.base #[← mkAppM ``ReprSpec.code #[repr]]

def recursionSlot (a b : Lean.Expr) : MetaM Lean.Expr := do
  mkAppM ``Option.some #[← mkAppM ``Prod.mk #[a, b]]

private def pureSourceK (type : Lean.Expr) : MetaM Lean.Expr :=
  withLocalDeclD `result type fun result => do
    mkLambdaFVars #[result] (← mkAppM ``Free.pure #[result])

private def lookupAtom? (atoms : Array RelatedAtom) (source : Lean.Expr) : Option RelatedAtom :=
  atoms.find? fun atom => atom.source == source

private def emitValue (Φ repr source : Lean.Expr) (atoms : Array RelatedAtom) : MetaM RelatedAtom := do
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
      return { source, target, related }
  let target ← mkAppM ``ReprSpec.encode #[repr, source]
  let relatedProof ← mkAppM ``ReprSpec.encode_related #[repr, source]
  let related := mkLambda `h .default Φ relatedProof
  pure { source, target, related }

structure EncodedCall where
  input : RelatedAtom
  inputTp : Lean.Expr

/-- Encode the one represented argument, or the supported pair of represented arguments, of a
    spilled helper.  Both ordinary and recursive emission use exactly this calling convention. -/
private def encodeCall (Φ : Lean.Expr) (spec : Specialization) (call : Lean.Expr)
    (atoms : Array RelatedAtom) : MetaM EncodedCall := do
  let args := call.getAppArgs
  let (position₁, param₁, param₂?) := match spec.boundary with
    | .unary before param _ => (before.size, param, none)
    | .natBRec param _ => (0, param, none)
    | .pair before left between right _ =>
        (before.size, left, some (before.size + between.size + 1, right))
  let source₁ := args[position₁]!
  let encoded₁ ← emitValue Φ param₁.repr source₁ atoms
  let some (position₂, param₂) := param₂? | return {
      input := encoded₁
      inputTp := ← mkAppM ``Tp.base #[← mkAppM ``ReprSpec.code #[param₁.repr]]
    }
  let source₂ := args[position₂]!
  let encoded₂ ← emitValue Φ param₂.repr source₂ atoms
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
    inputTp := ← mkAppM ``Tp.base #[← mkAppM ``Tp0.prod #[code₁, code₂]]
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
private def encodeOp (plan : Plan) (Φ source : Lean.Expr)
    (atoms : Array RelatedAtom) : MetaM EncodedOp := do
  let args := source.getAppArgs
  let sourceOp := args[2]!
  let sourceInput := args[3]!
  let sourceBlocks := args[4]!
  let sourceK := args[5]!
  let spec ← resolveOp plan.compat sourceOp
  let targetOp ← mkAppM ``OpSpec.target #[spec]
  let witness ← mkAppM ``OpSpec.witness #[spec]
  let inputTp ← mkAppM ``Tp.base #[← mkAppM ``Signature.input #[plan.targetSig, targetOp]]
  let inputRel ← mkAppM ``ITree.HSig.Compat.input #[plan.compat, witness]
  let inputRepr ← resolveReprFor (← inferType sourceInput) inputTp inputRel
  let input ← emitValue Φ inputRepr sourceInput atoms
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
  body : Lean.Expr
  call? : Option RecCallEnv := none

/-! ## Unified computation execution

`matchSource` above is the classifier. `emitComp` below consumes that classification and constructs
the semantic AST, generic AST, and proof at the same case site. `EmitMode` supplies only the extra
environment available inside a recursive body; it does not select a second traversal.
-/

inductive EmitMode where
  | ordinary
  | recursive (env : RecEnv)

private def EmitMode.slot (mode : EmitMode) (target : TargetEnv) : MetaM Lean.Expr := do
  match mode with
  | .ordinary => pure target.noRecursion
  | .recursive env => recursionSlot (mkConst ``Tp.nat) (← reprTp env.spec.resultRepr)

structure EmitContext where
  plan : Plan
  target : TargetEnv
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

private def emitRecursiveEmptyBlocks (ctx : EmitContext) (env : RecEnv) (op : EncodedOp)
    (slot kCode kSound targetBranchType : Lean.Expr) : MetaM BlockEmission := do
  let plan := ctx.plan
  let target := ctx.target
  let goal := ctx.goal
  let V := ctx.V
  let Φ := ctx.Φ
  let sourceBranchType ← mkAppM ``ITree.HSig.branch #[plan.sourceSig, op.sourceOp]
  unless (← isDefEq sourceBranchType (mkConst ``Empty)) &&
      (← isDefEq targetBranchType (mkConst ``Empty)) do
    throwError "reflect%: recursive dynamic blocks require the scoped interpreter bridge"
  let sourceEmpty ← withLocalDeclD `branch sourceBranchType fun branch => do
    mkLambdaFVars #[branch] (← mkAppOptM ``Empty.elim
      #[some (mkConst ``False), some branch])
  let targetEmpty ← withLocalDeclD `branch targetBranchType fun branch => do
    mkLambdaFVars #[branch] (← mkAppOptM ``Empty.elim
      #[some (mkConst ``False), some branch])
  let blocksCode ← withLocalDeclD `bt targetBranchType fun bt => do
    let inputCode ← mkAppM ``Signature.branchInput #[plan.targetSig, op.targetOp, bt]
    let inputType ← mkAppM ``Tp0.denote #[inputCode]
    let blockTp ← mkAppM ``Tp.base
      #[← mkAppM ``Signature.branchOutput #[plan.targetSig, op.targetOp, bt]]
    let blockType ← mkAppM ``Expr #[plan.targetSig, target.values, slot, blockTp]
    let impossible ← mkAppOptM ``False.elim
      #[some (← mkArrow inputType blockType), some (mkApp targetEmpty bt)]
    mkLambdaFVars #[bt] impossible
  let blocksGeneric ← withLocalDeclD `bt targetBranchType fun bt => do
    let inputTp ← mkAppM ``Tp.base
      #[← mkAppM ``Signature.branchInput #[plan.targetSig, op.targetOp, bt]]
    withLocalDeclD `input (mkApp V inputTp) fun input => do
      let blockTp ← mkAppM ``Tp.base
        #[← mkAppM ``Signature.branchOutput #[plan.targetSig, op.targetOp, bt]]
      let blockType ← mkAppM ``Expr #[plan.targetSig, V, slot, blockTp]
      mkLambdaFVars #[bt, input] (← mkAppOptM ``Empty.elim
        #[some blockType, some bt])
  let sound ← Construct.recursiveOpNoBranches {
    sourceSig := plan.sourceSig, targetSig := plan.targetSig
    argumentTp := mkConst ``Tp.nat
    recursiveResultTp := ← reprTp env.spec.resultRepr
    targetTp := goal.targetTp, compat := plan.compat, body := env.body, assumption := Φ
    sourceType := goal.sourceType, relates := goal.relates
    sourceOp := op.sourceOp, targetOp := op.targetOp, witness := op.witness
    sourceEmpty, targetEmpty, targetInput := op.input.target, sourceInput := op.sourceInput
    inputRelated := op.input.related, sourceBlocks := op.sourceBlocks
    sourceContinuation := op.sourceK, continuation := kCode, continuationSound := kSound
  }
  pure { code := blocksCode, generic := blocksGeneric, sound }

private def ordinaryOpHead (ctx : EmitContext) (op : EncodedOp) : MetaM Lean.Expr :=
  Construct.ordinaryOp {
    sourceSig := ctx.plan.sourceSig, targetSig := ctx.plan.targetSig
    compat := ctx.plan.compat, assumption := ctx.Φ, targetTp := ctx.goal.targetTp
    sourceType := ctx.goal.sourceType, relates := ctx.goal.relates
    sourceOp := op.sourceOp, targetOp := op.targetOp, witness := op.witness
    targetInput := op.input.target, sourceInput := op.sourceInput
    inputRelated := op.input.related, sourceBlocks := op.sourceBlocks
  }

private def emitOrdinaryEmptyBlocks (ctx : EmitContext) (op : EncodedOp)
    (slot opHead blocksType : Lean.Expr) : MetaM BlockEmission := do
  let .forallE _ btType btBody _ := blocksType
    | throwError "reflect%: internal: block argument is not a function"
  withLocalDeclD `bt btType fun bt => do
    let .forallE _ xtType xtBody _ := btBody.instantiate1 bt
      | throwError "reflect%: internal: block binder argument is not a function"
    withLocalDeclD `xt xtType fun xt => do
      let blocksCode ← mkLambdaFVars #[bt, xt]
        (← mkAppOptM ``Empty.elim #[some (xtBody.instantiate1 xt), some bt])
      let .forallE _ soundType _ _ ← whnf (← inferType (mkApp opHead blocksCode))
        | throwError "reflect%: internal: malformed block-soundness argument"
      forallTelescope soundType fun binders body => do
        let some soundBt := binders[0]?
          | throwError "reflect%: internal: empty block soundness has no branch binder"
        let inputTp ← mkAppM ``Tp.base
          #[← mkAppM ``Signature.branchInput #[ctx.plan.targetSig, op.targetOp, bt]]
        let blocksGeneric ← withLocalDeclD `input (mkApp ctx.V inputTp) fun input => do
          let blockTp ← mkAppM ``Tp.base
            #[← mkAppM ``Signature.branchOutput #[ctx.plan.targetSig, op.targetOp, bt]]
          let blockType ← mkAppM ``Expr #[ctx.plan.targetSig, ctx.V, slot, blockTp]
          mkLambdaFVars #[bt, input] (← mkAppOptM ``Empty.elim
            #[some blockType, some bt])
        pure {
          code := blocksCode
          generic := blocksGeneric
          sound := ← mkLambdaFVars binders (← mkAppOptM ``Empty.elim
            #[some body, some soundBt])
        }

private def emitOrdinaryDynamicBlocks (ctx : EmitContext) (op : EncodedOp)
    (targetBranchType : Lean.Expr)
    (recur : EmitContext → Lean.Expr → MetaM Emission) : MetaM BlockEmission := do
  let plan := ctx.plan
  withLocalDeclD `bt targetBranchType fun bt => do
    let inputCode ← mkAppM ``Signature.branchInput #[plan.targetSig, op.targetOp, bt]
    let inputType ← mkAppM ``Tp0.denote #[inputCode]
    let inputTp ← mkAppM ``Tp.base #[inputCode]
    withLocalDeclD `genericInput (mkApp ctx.V inputTp) fun genericInput =>
    withLocalDeclD `xt inputType fun xt => do
      let sourceBranchType ← mkAppM ``ITree.HSig.branch #[plan.sourceSig, op.sourceOp]
      withLocalDeclD `bs sourceBranchType fun bs => do
        let branchRel ← mkAppM ``ITree.HSig.Compat.branch
          #[plan.compat, op.witness, bs, bt]
        withLocalDeclD `hbr branchRel fun hbr => do
          let sourceInputType ← mkAppM ``ITree.HSig.branchInput
            #[plan.sourceSig, op.sourceOp, bs]
          withLocalDeclD `xs sourceInputType fun xs => do
            let inputRel ← mkAppM ``ITree.HSig.Compat.branchInput
              #[plan.compat, op.witness, hbr, xs, xt]
            withLocalDeclD `hx inputRel fun hx => do
              let blockSource ← mkAppM' op.sourceBlocks #[bs, xs]
              let blockSourceType ← inferType blockSource
              let blockTargetTp ← mkAppM ``Tp.base
                #[← mkAppM ``Signature.branchOutput #[plan.targetSig, op.targetOp, bt]]
              let blockRel ← mkAppM ``ITree.HSig.Compat.branchOutput
                #[plan.compat, op.witness, hbr]
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

private def emitOrdinaryBlocks (ctx : EmitContext) (op : EncodedOp)
    (slot kCode kSound targetBranchType : Lean.Expr)
    (recur : EmitContext → Lean.Expr → MetaM Emission) : MetaM BlockEmission := do
  let opHead ← ordinaryOpHead ctx op
  let .forallE _ blocksType _ _ ← whnf (← inferType opHead)
    | throwError "reflect%: internal: malformed `Reflection.op` block argument"
  let blocks ← if ← isDefEq targetBranchType (mkConst ``Empty) then
    emitOrdinaryEmptyBlocks ctx op slot opHead blocksType
  else
    emitOrdinaryDynamicBlocks ctx op targetBranchType recur
  pure { blocks with sound := ← mkAppM' opHead #[blocks.code, blocks.sound, kCode, kSound] }

private def emitOperation (ctx : EmitContext) (source : Lean.Expr)
    (recur : EmitContext → Lean.Expr → MetaM Emission) : MetaM Emission := do
  let plan := ctx.plan
  let target := ctx.target
  let goal := ctx.goal
  let op ← encodeOp plan ctx.Φ source ctx.atoms
  let targetOutputCode ← mkAppM ``Signature.output #[plan.targetSig, op.targetOp]
  let targetOutputTp ← mkAppM ``Tp.base #[targetOutputCode]
  let targetOutputType ← mkAppM ``Tp0.denote #[targetOutputCode]
  let sourceOutputType ← mkAppM ``ITree.HSig.output #[plan.sourceSig, op.sourceOp]
  let ⟨kCode, kGeneric, kSound⟩ ← emitContinuation ctx.V ctx.Φ targetOutputTp
    sourceOutputType targetOutputType op.sourceK ctx.atoms ctx.genericAtoms
    (fun source target => mkAppM ``ITree.HSig.Compat.output
      #[plan.compat, op.witness, source, target])
    (fun next atoms genericAtoms => recur { ctx with atoms, genericAtoms } next)
  let slot ← ctx.mode.slot target
  let targetBranchType ← mkAppM ``Signature.branch #[plan.targetSig, op.targetOp]
  let blocks ← match ctx.mode with
    | .ordinary => emitOrdinaryBlocks ctx op slot kCode kSound targetBranchType recur
    | .recursive env =>
        emitRecursiveEmptyBlocks ctx env op slot kCode kSound targetBranchType
  let code ← Construct.op {
    targetSig := plan.targetSig, carrier := target.values, slot, resultTp := goal.targetTp
    operation := op.targetOp, input := op.input.target, blocks := blocks.code
    continuation := kCode
  }
  let inputCode ← mkAppM ``Signature.input #[plan.targetSig, op.targetOp]
  let generic ← emitGenericValue plan.targetSig ctx.V slot inputCode op.input.target
    ctx.genericAtoms fun input => Construct.op {
      targetSig := plan.targetSig, carrier := ctx.V, slot, resultTp := goal.targetTp
      operation := op.targetOp, input, blocks := blocks.generic, continuation := kGeneric
    }
  pure { code, generic, sound := blocks.sound }

/-! ### Helper and self-call construction -/

private def isRecursiveCall (ctx : EmitContext) (candidate : Lean.Expr) : MetaM Bool := do
  let .recursive env := ctx.mode | return false
  if let some call := env.call? then
    if ← isDefEq candidate call.sourceCall then return true
  env.spec.matchesCall candidate

private def emitSelfCall (ctx : EmitContext) (sourceCall sourceK : Lean.Expr)
    (recur : EmitContext → Lean.Expr → MetaM Emission) : MetaM Emission := do
  let plan := ctx.plan
  let target := ctx.target
  let goal := ctx.goal
  let mode := ctx.mode
  let V := ctx.V
  let Φ := ctx.Φ
  let atoms := ctx.atoms
  let genericAtoms := ctx.genericAtoms
  let .recursive env := mode
    | throwError "reflect%: internal: self call outside a recursive body"
  let some call := env.call?
    | throwError "reflect%: `Nat.brecOn` zero functional unexpectedly contains a recursive call"
  unless ← isDefEq sourceCall call.sourceCall do
    throwError "reflect%: recursive `Nat.brecOn` functional does not call its immediate induction hypothesis{indentExpr sourceCall}"
  let .natBRec argParam _ := env.spec.boundary
    | throwError "reflect%: internal: recursive emission used a nonrecursive helper boundary"
  let argRepr := argParam.repr
  let targetArg ← emitValue Φ argRepr call.sourceArg atoms
  unless ← isDefEq targetArg.target call.targetArg do
    throwError "reflect%: recursive `Nat.brecOn` functional changed its induction-hypothesis argument{indentExpr targetArg.target}"
  let ihAt ← withLocalDeclD `hΦ Φ fun hΦ => mkLambdaFVars #[hΦ] call.adequate
  let resultRel ← mkAppM ``ReprSpec.relates #[env.spec.resultRepr]
  let resultTp ← reprTp env.spec.resultRepr
  let targetResultType ← mkAppM ``Tp.denote #[target.monad, resultTp]
  let ⟨kCode, kGeneric, kSound⟩ ← emitContinuation V Φ resultTp
    env.spec.resultType targetResultType sourceK atoms genericAtoms
    (fun source target => mkAppM' resultRel #[source, target])
    (fun next atoms genericAtoms =>
      recur { ctx with atoms, genericAtoms } next)
  let sound ← Construct.recursiveSelfCall {
    sourceSig := plan.sourceSig, targetSig := plan.targetSig, argumentTp := mkConst ``Tp.nat
    recursiveResultTp := resultTp, targetTp := goal.targetTp, compat := plan.compat
    body := env.body, assumption := Φ, recursiveRelates := resultRel
    relates := goal.relates, sourceCall := call.sourceCall, argument := targetArg.target
    inductionHypothesis := ihAt, sourceContinuation := sourceK, continuation := kCode
    continuationSound := kSound
  }
  let code ← Construct.selfCall {
    targetSig := plan.targetSig, carrier := target.values, outputTp := goal.targetTp
    argumentTp := mkConst ``Tp.nat, recursiveResultTp := resultTp
    argument := targetArg.target, continuation := kCode
  }
  let slot ← mode.slot target
  let generic ← emitGenericValue plan.targetSig V slot (mkConst ``Tp0.nat)
    targetArg.target genericAtoms fun input => Construct.selfCall {
      targetSig := plan.targetSig, carrier := V, outputTp := goal.targetTp
      argumentTp := mkConst ``Tp.nat, recursiveResultTp := resultTp
      argument := input, continuation := kGeneric
    }
  pure { code, generic, sound }

private def emitHelperCall (ctx : EmitContext) (helper : Helper) (sourceCall : Lean.Expr)
    (sourceK? : Option Lean.Expr)
    (recur : EmitContext → Lean.Expr → MetaM Emission) : MetaM Emission := do
  let plan := ctx.plan
  let target := ctx.target
  let goal := ctx.goal
  let mode := ctx.mode
  let V := ctx.V
  let Φ := ctx.Φ
  let atoms := ctx.atoms
  let genericAtoms := ctx.genericAtoms
  let encoded ← encodeCall Φ helper.spec sourceCall atoms
  let hEutt ← withLocalDeclD `hΦ Φ fun hΦ =>
    mkLambdaFVars #[hΦ]
      (mkAppN helper.adequate
        #[encoded.input.source, encoded.input.target, mkApp encoded.input.related hΦ])
  let resultTp ← reprTp helper.spec.resultRepr
  let .app (.const ``Tp.base _) inputCode ← whnf encoded.inputTp
    | throwError "reflect%: helper argument is not first-order"
  match sourceK? with
  | none =>
      let .ordinary := mode
        | throwError "reflect%: internal: direct recursive helper call lacks a continuation"
      let sound ← Construct.directCall {
        sourceSig := plan.sourceSig, targetSig := plan.targetSig, compat := plan.compat
        assumption := Φ, targetTp := goal.targetTp, sourceType := goal.sourceType
        relates := goal.relates, function := helper.target, argument := encoded.input.target
        sourceCall, adequate := hEutt
      }
      let targetResultType ← mkAppM ``Tp.denote #[target.monad, resultTp]
      let returnCode ← withLocalDeclD `result targetResultType fun result => do
        mkLambdaFVars #[result] (← Construct.ret {
          targetSig := plan.targetSig, carrier := target.values, slot := target.noRecursion
          resultTp, value := result
        })
      let genericReturn ← withLocalDeclD `result (mkApp V resultTp) fun result => do
        mkLambdaFVars #[result] (← Construct.ret {
          targetSig := plan.targetSig, carrier := V, slot := target.noRecursion
          resultTp, value := result
        })
      let code ← Construct.app {
        targetSig := plan.targetSig, carrier := target.values, slot := target.noRecursion
        outputTp := resultTp, inputTp := encoded.inputTp, helperResultTp := resultTp
        function := helper.target, input := encoded.input.target, continuation := returnCode
      }
      let generic ← emitGenericValue plan.targetSig V target.noRecursion inputCode
        encoded.input.target genericAtoms fun input => Construct.app {
          targetSig := plan.targetSig, carrier := V, slot := target.noRecursion
          outputTp := resultTp, inputTp := encoded.inputTp, helperResultTp := resultTp
          function := helper.generic, input, continuation := genericReturn
        }
      pure { code, generic, sound }
  | some sourceK =>
      let resultRel ← mkAppM ``ReprSpec.relates #[helper.spec.resultRepr]
      let targetResultType ← mkAppM ``Tp.denote #[target.monad, resultTp]
      let ⟨kCode, kGeneric, kSound⟩ ← emitContinuation V Φ resultTp
        helper.spec.resultType targetResultType sourceK atoms genericAtoms
        (fun source target => mkAppM' resultRel #[source, target])
        (fun next atoms genericAtoms =>
          recur { ctx with atoms, genericAtoms } next)
      let slot ← mode.slot target
      let sound ← match mode with
        | .ordinary => Construct.ordinaryBindCall {
            sourceSig := plan.sourceSig, targetSig := plan.targetSig, compat := plan.compat
            assumption := Φ, helperResultTp := resultTp, targetTp := goal.targetTp
            helperSourceType := helper.spec.resultType, sourceType := goal.sourceType
            helperRelates := resultRel, relates := goal.relates, function := helper.target
            argument := encoded.input.target, sourceCall, adequate := hEutt
            sourceContinuation := sourceK, continuation := kCode, continuationSound := kSound
          }
        | .recursive env => Construct.recursiveBindCall {
            sourceSig := plan.sourceSig, targetSig := plan.targetSig
            recursiveArgumentTp := mkConst ``Tp.nat
            recursiveResultTp := ← reprTp env.spec.resultRepr
            helperArgumentTp := encoded.inputTp, helperResultTp := resultTp
            targetTp := goal.targetTp, compat := plan.compat, body := env.body, assumption := Φ
            helperSourceType := helper.spec.resultType, sourceType := goal.sourceType
            helperRelates := resultRel, relates := goal.relates, function := helper.target
            argument := encoded.input.target, sourceCall, adequate := hEutt
            sourceContinuation := sourceK, continuation := kCode, continuationSound := kSound
          }
      let code ← Construct.app {
        targetSig := plan.targetSig, carrier := target.values, slot, outputTp := goal.targetTp
        inputTp := encoded.inputTp, helperResultTp := resultTp, function := helper.target
        input := encoded.input.target, continuation := kCode
      }
      let generic ← emitGenericValue plan.targetSig V slot inputCode encoded.input.target
        genericAtoms fun input => Construct.app {
          targetSig := plan.targetSig, carrier := V, slot, outputTp := goal.targetTp
          inputTp := encoded.inputTp, helperResultTp := resultTp, function := helper.generic
          input, continuation := kGeneric
        }
      pure { code, generic, sound }

/-! ### Return construction -/

private def emitReturn (ctx : EmitContext) (value : Lean.Expr) : MetaM Emission := do
  let plan := ctx.plan
  let target := ctx.target
  let goal := ctx.goal
  let mode := ctx.mode
  let V := ctx.V
  let Φ := ctx.Φ
  let atoms := ctx.atoms
  let genericAtoms := ctx.genericAtoms
  let repr ← resolveReprFor (← inferType value) goal.targetTp goal.relates
  let atom ← emitValue Φ repr value atoms
  let slot ← mode.slot target
  let sound ← match mode with
    | .ordinary => Construct.ordinaryRet {
        sourceSig := plan.sourceSig, targetSig := plan.targetSig, slot, compat := plan.compat
        assumption := Φ, targetTp := goal.targetTp, sourceType := goal.sourceType
        relates := goal.relates, targetValue := atom.target, sourceValue := value
        related := atom.related
      }
    | .recursive env => Construct.recursiveRet {
        sourceSig := plan.sourceSig, targetSig := plan.targetSig
        argumentTp := mkConst ``Tp.nat, recursiveResultTp := ← reprTp env.spec.resultRepr
        targetTp := goal.targetTp, compat := plan.compat, body := env.body, assumption := Φ
        sourceType := goal.sourceType, relates := goal.relates, targetValue := atom.target
        sourceValue := value, related := atom.related
      }
  let code ← Construct.ret {
    targetSig := plan.targetSig, carrier := target.values, slot, resultTp := goal.targetTp
    value := atom.target
  }
  let valueCode ← mkAppM ``ReprSpec.code #[repr]
  let generic ← emitGenericValue plan.targetSig V slot valueCode atom.target
    genericAtoms fun value => Construct.ret {
      targetSig := plan.targetSig, carrier := V, slot, resultTp := goal.targetTp, value
    }
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
      if ← isRecursiveCall ctx head then return ← emitSelfCall ctx head sourceK emitComp
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
            return ← emitSelfCall ctx source (← pureSourceK env.spec.resultType) emitComp
          if let some helper ← helperForCall? helpers source then
            return ← emitHelperCall ctx helper source
              (some (← pureSourceK helper.spec.resultType)) emitComp
          if let some name := source.getAppFn.constName? then
            if name != env.spec.name then
              if let some unfolded ← unfoldDefinition? source then
                return ← emitComp ctx unfolded
          throwError "reflect%: recursive pass does not recognize computation{indentExpr source}"


end Reflector
end Ast
end Freigen
