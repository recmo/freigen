import Freigen.Reflect.Sound
import Lean.Elab.Term

namespace Freigen
namespace Ast
namespace Reflector
namespace Construct

open Lean Meta

/-! ## Named metaprogram constructors

Coupling to the positional signatures of computation AST nodes and soundness declarations lives
here. Execution code supplies named records; a declaration-signature change therefore has one
audited failure point instead of many anonymous `Array (Option Expr)` call sites. The smaller value
syntax is intentionally constructed beside value matching in `Value.lean`.
-/

structure Ret where
  targetSig : Lean.Expr
  carrier : Lean.Expr
  slot : Lean.Expr
  resultTp : Lean.Expr
  value : Lean.Expr

def ret (a : Ret) : MetaM Lean.Expr :=
  mkAppOptM ``Expr.ret
    #[some a.targetSig, some a.carrier, some a.slot, some a.resultTp, some a.value]

structure App where
  targetSig : Lean.Expr
  carrier : Lean.Expr
  slot : Lean.Expr
  outputTp : Lean.Expr
  inputTp : Lean.Expr
  helperResultTp : Lean.Expr
  function : Lean.Expr
  input : Lean.Expr
  continuation : Lean.Expr

def app (a : App) : MetaM Lean.Expr :=
  mkAppOptM ``Expr.app
    #[some a.targetSig, some a.carrier, some a.slot, some a.outputTp, some a.inputTp,
      some a.helperResultTp, some a.function, some a.input, some a.continuation]

structure Op where
  targetSig : Lean.Expr
  carrier : Lean.Expr
  slot : Lean.Expr
  resultTp : Lean.Expr
  operation : Lean.Expr
  input : Lean.Expr
  blocks : Lean.Expr
  continuation : Lean.Expr

def op (a : Op) : MetaM Lean.Expr :=
  mkAppOptM ``Expr.op
    #[some a.targetSig, some a.carrier, some a.slot, some a.resultTp, some a.operation,
      some a.input, some a.blocks, some a.continuation]

structure SelfCall where
  targetSig : Lean.Expr
  carrier : Lean.Expr
  outputTp : Lean.Expr
  argumentTp : Lean.Expr
  recursiveResultTp : Lean.Expr
  argument : Lean.Expr
  continuation : Lean.Expr

def selfCall (a : SelfCall) : MetaM Lean.Expr :=
  mkAppOptM ``Expr.selfCall
    #[some a.targetSig, some a.carrier, some a.outputTp, some a.argumentTp,
      some a.recursiveResultTp, some a.argument, some a.continuation]

structure OrdinaryRet where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  slot : Lean.Expr
  compat : Lean.Expr
  assumption : Lean.Expr
  targetTp : Lean.Expr
  sourceType : Lean.Expr
  relates : Lean.Expr
  targetValue : Lean.Expr
  sourceValue : Lean.Expr
  related : Lean.Expr

def ordinaryRet (a : OrdinaryRet) : MetaM Lean.Expr :=
  mkAppOptM ``Reflection.ret
    #[some a.sourceSig, some a.targetSig, some a.slot, some a.compat, some a.assumption,
      some a.targetTp, some a.sourceType, some a.relates, some a.targetValue,
      some a.sourceValue, some a.related]

structure RecursiveRet where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  argumentTp : Lean.Expr
  recursiveResultTp : Lean.Expr
  targetTp : Lean.Expr
  compat : Lean.Expr
  body : Lean.Expr
  assumption : Lean.Expr
  sourceType : Lean.Expr
  relates : Lean.Expr
  targetValue : Lean.Expr
  sourceValue : Lean.Expr
  related : Lean.Expr

def recursiveRet (a : RecursiveRet) : MetaM Lean.Expr :=
  mkAppOptM ``RecReflection.ret
    #[some a.sourceSig, some a.targetSig, some a.argumentTp, some a.recursiveResultTp,
      some a.targetTp, some a.compat, some a.body, some a.assumption, some a.sourceType,
      some a.relates, some a.targetValue, some a.sourceValue, some a.related]

structure DirectCall where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  compat : Lean.Expr
  assumption : Lean.Expr
  slot? : Option Lean.Expr := none
  targetTp : Lean.Expr
  sourceType : Lean.Expr
  relates : Lean.Expr
  function : Lean.Expr
  argument : Lean.Expr
  sourceCall : Lean.Expr
  adequate : Lean.Expr

def directCall (a : DirectCall) : MetaM Lean.Expr :=
  mkAppOptM ``Reflection.call
    #[some a.sourceSig, some a.targetSig, some a.compat, some a.assumption, a.slot?,
      some a.targetTp, some a.sourceType, some a.relates, some a.function,
      some a.argument, some a.sourceCall, some a.adequate]

structure OrdinaryBindCall where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  compat : Lean.Expr
  assumption : Lean.Expr
  slot? : Option Lean.Expr := none
  helperResultTp : Lean.Expr
  targetTp : Lean.Expr
  helperSourceType : Lean.Expr
  sourceType : Lean.Expr
  helperRelates : Lean.Expr
  relates : Lean.Expr
  function : Lean.Expr
  argument : Lean.Expr
  sourceCall : Lean.Expr
  adequate : Lean.Expr
  sourceContinuation : Lean.Expr
  continuation : Lean.Expr
  continuationSound : Lean.Expr

def ordinaryBindCall (a : OrdinaryBindCall) : MetaM Lean.Expr :=
  mkAppOptM ``Reflection.bindCall
    #[some a.sourceSig, some a.targetSig, some a.compat, some a.assumption, a.slot?,
      some a.helperResultTp, some a.targetTp, some a.helperSourceType, some a.sourceType,
      some a.helperRelates, some a.relates, some a.function, some a.argument,
      some a.sourceCall, some a.adequate, some a.sourceContinuation, some a.continuation,
      some a.continuationSound]

structure RecursiveBindCall where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  recursiveArgumentTp : Lean.Expr
  recursiveResultTp : Lean.Expr
  helperArgumentTp : Lean.Expr
  helperResultTp : Lean.Expr
  targetTp : Lean.Expr
  compat : Lean.Expr
  body : Lean.Expr
  assumption : Lean.Expr
  helperSourceType : Lean.Expr
  sourceType : Lean.Expr
  helperRelates : Lean.Expr
  relates : Lean.Expr
  function : Lean.Expr
  argument : Lean.Expr
  sourceCall : Lean.Expr
  adequate : Lean.Expr
  sourceContinuation : Lean.Expr
  continuation : Lean.Expr
  continuationSound : Lean.Expr

def recursiveBindCall (a : RecursiveBindCall) : MetaM Lean.Expr :=
  mkAppOptM ``RecReflection.bindCall
    #[some a.sourceSig, some a.targetSig, some a.recursiveArgumentTp,
      some a.recursiveResultTp, some a.helperArgumentTp, some a.helperResultTp,
      some a.targetTp, some a.compat, some a.body, some a.assumption,
      some a.helperSourceType, some a.sourceType, some a.helperRelates, some a.relates,
      some a.function, some a.argument, some a.sourceCall, some a.adequate,
      some a.sourceContinuation, some a.continuation, some a.continuationSound]

structure RecursiveSelfCall where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  argumentTp : Lean.Expr
  recursiveResultTp : Lean.Expr
  targetTp : Lean.Expr
  compat : Lean.Expr
  body : Lean.Expr
  assumption : Lean.Expr
  sourceType? : Option Lean.Expr := none
  sourceArgumentType? : Option Lean.Expr := none
  recursiveRelates : Lean.Expr
  relates : Lean.Expr
  sourceCall : Lean.Expr
  argument : Lean.Expr
  inductionHypothesis : Lean.Expr
  sourceContinuation : Lean.Expr
  continuation : Lean.Expr
  continuationSound : Lean.Expr

def recursiveSelfCall (a : RecursiveSelfCall) : MetaM Lean.Expr :=
  mkAppOptM ``RecReflection.selfCall
    #[some a.sourceSig, some a.targetSig, some a.argumentTp, some a.recursiveResultTp,
      some a.targetTp, some a.compat, some a.body, some a.assumption, a.sourceType?,
      a.sourceArgumentType?, some a.recursiveRelates, some a.relates, some a.sourceCall,
      some a.argument, some a.inductionHypothesis, some a.sourceContinuation,
      some a.continuation, some a.continuationSound]

structure OrdinaryOp where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  compat : Lean.Expr
  assumption : Lean.Expr
  targetTp : Lean.Expr
  sourceType : Lean.Expr
  relates : Lean.Expr
  sourceOp : Lean.Expr
  targetOp : Lean.Expr
  witness : Lean.Expr
  targetInput : Lean.Expr
  sourceInput : Lean.Expr
  inputRelated : Lean.Expr
  sourceBlocks : Lean.Expr

def ordinaryOp (a : OrdinaryOp) : MetaM Lean.Expr :=
  mkAppOptM ``Reflection.op
    #[some a.sourceSig, some a.targetSig, some a.compat, some a.assumption,
      some a.targetTp, some a.sourceType, some a.relates, some a.sourceOp,
      some a.targetOp, some a.witness, some a.targetInput, some a.sourceInput,
      some a.inputRelated, some a.sourceBlocks]

structure RecursiveOpNoBranches where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  argumentTp : Lean.Expr
  recursiveResultTp : Lean.Expr
  targetTp : Lean.Expr
  compat : Lean.Expr
  body : Lean.Expr
  assumption : Lean.Expr
  sourceType : Lean.Expr
  relates : Lean.Expr
  sourceOp : Lean.Expr
  targetOp : Lean.Expr
  witness : Lean.Expr
  sourceEmpty : Lean.Expr
  targetEmpty : Lean.Expr
  targetInput : Lean.Expr
  sourceInput : Lean.Expr
  inputRelated : Lean.Expr
  sourceBlocks : Lean.Expr
  sourceContinuation : Lean.Expr
  continuation : Lean.Expr
  continuationSound : Lean.Expr

def recursiveOpNoBranches (a : RecursiveOpNoBranches) : MetaM Lean.Expr :=
  mkAppOptM ``RecReflection.opNoBranches
    #[some a.sourceSig, some a.targetSig, some a.argumentTp, some a.recursiveResultTp,
      some a.targetTp, some a.compat, some a.body, some a.assumption, some a.sourceType,
      some a.relates, some a.sourceOp, some a.targetOp, some a.witness, some a.sourceEmpty,
      some a.targetEmpty, some a.targetInput, some a.sourceInput, some a.inputRelated,
      some a.sourceBlocks, some a.sourceContinuation, some a.continuation,
      some a.continuationSound]

structure HelperScopeProof where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  compat : Lean.Expr
  assumption : Lean.Expr
  argumentTp : Lean.Expr
  helperResultTp : Lean.Expr
  targetTp : Lean.Expr
  sourceType : Lean.Expr
  relates : Lean.Expr
  source : Lean.Expr
  body : Lean.Expr
  continuation : Lean.Expr
  innerSound : Lean.Expr

private def helperScopeProof (constructor : Name) (a : HelperScopeProof) : MetaM Lean.Expr :=
  mkAppOptM constructor
    #[some a.sourceSig, some a.targetSig, some a.compat, some a.assumption,
      some a.argumentTp, some a.helperResultTp, some a.targetTp, some a.sourceType,
      some a.relates, some a.source, some a.body, some a.continuation, some a.innerSound]

def lambdaProof (a : HelperScopeProof) : MetaM Lean.Expr :=
  helperScopeProof ``Reflection.lam a

def letrecProof (a : HelperScopeProof) : MetaM Lean.Expr :=
  helperScopeProof ``Reflection.letrec a

structure HelperScope where
  targetSig : Lean.Expr
  carrier : Lean.Expr
  slot? : Option Lean.Expr := none
  targetTp : Lean.Expr
  argumentTp : Lean.Expr
  helperResultTp : Lean.Expr
  body : Lean.Expr
  continuation : Lean.Expr

private def helperScope (constructor : Name) (a : HelperScope) : MetaM Lean.Expr :=
  mkAppOptM constructor
    #[some a.targetSig, some a.carrier, a.slot?, some a.targetTp, some a.argumentTp,
      some a.helperResultTp, some a.body, some a.continuation]

def lambda (a : HelperScope) : MetaM Lean.Expr := helperScope ``Expr.lam a
def letrec (a : HelperScope) : MetaM Lean.Expr := helperScope ``Expr.letrec a

structure WitnessSound where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  slot : Lean.Expr
  compat : Lean.Expr
  assumption : Lean.Expr
  targetTp : Lean.Expr
  sourceType : Lean.Expr
  relates : Lean.Expr
  source : Lean.Expr
  code : Lean.Expr
  witness : Lean.Expr
  assumptionProof : Lean.Expr

def witnessSound (a : WitnessSound) : MetaM Lean.Expr :=
  mkAppOptM ``ReflectionWitnessAt.sound
    #[some a.sourceSig, some a.targetSig, some a.slot, some a.compat, some a.assumption,
      some a.targetTp, some a.sourceType, some a.relates, some a.source, some a.code,
      some a.witness, some a.assumptionProof]

end Construct
end Reflector
end Ast
end Freigen
