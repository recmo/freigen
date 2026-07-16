import Freigen.Reflect.Sound
import Lean.Elab.Term

namespace Freigen
namespace Ast
namespace Reflector
namespace Construct

open Lean Meta

/-! ## Expression construction

This module is the only place where the metaprogram names object-language and soundness
constructors.  The executor passes semantic arguments, not positional declaration signatures;
Lean infers the ambient definition context, carrier, and result indices from those arguments.
-/

def ret (targetSig scope carrier resultTp value : Lean.Expr) : MetaM Lean.Expr :=
  mkAppOptM ``Expr.ret
    #[some targetSig, some scope, some carrier, some resultTp, some value]

def app (targetSig scope carrier inputTp outputTp fn input continuation : Lean.Expr) :
    MetaM Lean.Expr :=
  mkAppOptM ``Expr.app
    #[some targetSig, some scope, some carrier, none, some inputTp, some outputTp,
      some fn, some input, some continuation]

def closure (ref captured continuation : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``Expr.closure #[ref, captured, continuation]

def op (targetSig scope carrier operation input blocks continuation : Lean.Expr) :
    MetaM Lean.Expr :=
  mkAppOptM ``Expr.op
    #[some targetSig, some scope, some carrier, none, some operation,
      some input, some blocks, some continuation]

/-! ## Expression soundness construction -/

def source (target range sound : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``Reflection.source #[target, range, sound]

def retSound (compat defs extension resultTp targetValue related : Lean.Expr) : MetaM Lean.Expr :=
  mkAppOptM ``Reflection.ret
    #[none, none, none, none, some compat, some defs, some extension,
      none, some resultTp, none, none, some targetValue, none, some related]

def discharge (assumption sound : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``Reflection.discharge #[assumption, sound]

def directCall (compat defs extension Φ fn argument adequate : Lean.Expr) : MetaM Lean.Expr :=
  mkAppOptM ``Reflection.call
    #[none, none, none, none, some compat, some defs, some extension, some Φ,
      none, none, none, none, some fn, some argument, none, some adequate]

def bindCall (compat defs extension Φ fn argument adequate continuation
    continuationSound : Lean.Expr) : MetaM Lean.Expr :=
  mkAppOptM ``Reflection.bindCall
    #[none, none, none, none, some compat, some defs, some extension, some Φ,
      none, none, none, none, none, none, none, some fn, some argument, none,
      some adequate, none, some continuation, some continuationSound]

def recursiveCall (sourceCall fn argument inductionHypothesis continuation
    continuationSound : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``Reflection.recursiveCall
    #[sourceCall, fn, argument, inductionHypothesis, continuation, continuationSound]

structure OpSound where
  compat : Lean.Expr
  sourceOp : Lean.Expr
  targetOp : Lean.Expr
  witness : Lean.Expr
  targetInput : Lean.Expr
  inputRelated : Lean.Expr
  sourceBlocks : Lean.Expr
  targetBlocks : Lean.Expr
  blockSound : Lean.Expr
  sourceContinuation : Lean.Expr
  targetContinuation : Lean.Expr
  continuationSound : Lean.Expr

def opSound (a : OpSound) : MetaM Lean.Expr :=
  mkAppM ``Reflection.op
    #[a.compat, a.sourceOp, a.targetOp, a.witness, a.targetInput,
      a.inputRelated, a.targetBlocks, a.blockSound,
      a.targetContinuation, a.continuationSound]

/-! ## Recursion construction -/

structure RecCallType where
  compat : Lean.Expr
  defs : Lean.Expr
  relates : Lean.Expr
  sourceCall : Lean.Expr
  targetClosure : Lean.Expr
  targetArgument : Lean.Expr

def recCallType (a : RecCallType) : MetaM Lean.Expr :=
  mkAppM ``RecCallAdequate
    #[a.compat, a.defs, a.relates, a.sourceCall, a.targetClosure, a.targetArgument]

end Construct
end Reflector
end Ast
end Freigen
