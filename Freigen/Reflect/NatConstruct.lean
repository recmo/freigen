import Freigen.Reflect.Construct
import Freigen.Reflect.NatRec

namespace Freigen
namespace Ast
namespace Reflector
namespace Construct

open Lean Meta

/-! Named construction adapters for the one supported recursion backend. Keeping them here
prevents the generic computation emitter from depending on `Nat.brecOn`. -/

structure RecCallType where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  argumentTp : Lean.Expr
  resultTp : Lean.Expr
  compat : Lean.Expr
  body : Lean.Expr
  assumption : Lean.Expr
  sourceType : Lean.Expr
  relates : Lean.Expr
  sourceCall : Lean.Expr
  sourceArgument : Lean.Expr

def recCallType (a : RecCallType) : MetaM Lean.Expr :=
  mkAppOptM ``RecCallAdequate
    #[some a.sourceSig, some a.targetSig, some a.argumentTp, some a.resultTp,
      some a.compat, some a.body, some a.assumption, some a.sourceType, some a.relates,
      some a.sourceCall, some a.sourceArgument]

structure NatBrecAdequate where
  sourceSig : Lean.Expr
  targetSig : Lean.Expr
  compat : Lean.Expr
  sourceType : Lean.Expr
  resultTp : Lean.Expr
  relates : Lean.Expr
  sourceFunction : Lean.Expr
  functional : Lean.Expr
  sourceEquality : Lean.Expr
  range : Lean.Expr
  base : Lean.Expr
  step : Lean.Expr
  baseSound : Lean.Expr
  stepSound : Lean.Expr

def natBrecAdequate (a : NatBrecAdequate) : MetaM Lean.Expr :=
  mkAppOptM ``RecReflection.natBrecOnAdequate
    #[some a.sourceSig, some a.targetSig, some a.compat, some a.sourceType,
      some a.resultTp, some a.relates, some a.sourceFunction, some a.functional,
      some a.sourceEquality, some a.range, some a.base, some a.step,
      some a.baseSound, some a.stepSound]

end Construct
end Reflector
end Ast
end Freigen
