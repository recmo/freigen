import Freigen.Reflect.Registry

namespace Freigen
namespace Ast
namespace Reflector

open Lean Meta

/-! ## Precise finite host representations

This module is the complete policy boundary for recognizing host `Fin`/`ZMod` types and selecting
their tagged AST representations. Generic registry resolution does not know their declaration
names or inspect finite target codes.
-/

private def zmodName : Name := .str .anonymous "ZMod"
def zmodCastName : Name := .str zmodName "cast"
private def zmodCarrierName : Name := ``ZModCarrier

private def isZModApp (e : Lean.Expr) : Bool :=
  e.isAppOfArity zmodName 1 || e.isAppOfArity zmodCarrierName 1

def preciseFiniteRepr? (hostType : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if hostType.isAppOfArity ``Fin 1 then
    if let some n ← getNatValue? (← whnf (hostType.getArg! 0)) then
      return some (← mkAppM ``finTaggedRepr #[mkNatLit n])
  if isZModApp hostType then
    if let some n ← getNatValue? (← whnf (hostType.getArg! 0)) then
      return some (← mkAppM ``zmodTaggedRepr #[mkNatLit n])
  return none

def preciseFiniteReprForTp? (targetTp : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let .app (.const ``Tp.base _) objectTp ← whnf targetTp | return none
  match ← whnf objectTp with
  | .app (.const ``Tp0.fin _) n => return some (← mkAppM ``finTaggedRepr #[n])
  | .app (.const ``Tp0.zmod _) n => return some (← mkAppM ``zmodTaggedRepr #[n])
  | _ => return none

end Reflector
end Ast
end Freigen
