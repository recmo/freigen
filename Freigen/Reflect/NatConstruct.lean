import Freigen.Reflect.Construct
import Freigen.Reflect.NatRec

namespace Freigen.Ast.Reflector.Construct

open Lean Meta

structure NatBrecAdequate where
  compat : Lean.Expr
  defs : Lean.Expr
  extension : Lean.Expr
  self : Lean.Expr
  captured : Lean.Expr
  relates : Lean.Expr
  sourceFunction : Lean.Expr
  functional : Lean.Expr
  sourceEquality : Lean.Expr
  range : Lean.Expr
  base : Lean.Expr
  step : Lean.Expr
  dispatch : Lean.Expr
  baseSound : Lean.Expr
  stepSound : Lean.Expr

def natBrecAdequate (a : NatBrecAdequate) : MetaM Lean.Expr :=
  mkAppM ``RecReflection.natBrecOnAdequate
    #[a.compat, a.defs, a.extension, a.self, a.captured, a.relates,
      a.sourceFunction, a.functional, a.sourceEquality, a.range, a.base, a.step,
      a.dispatch, a.baseSound, a.stepSound]

end Freigen.Ast.Reflector.Construct
