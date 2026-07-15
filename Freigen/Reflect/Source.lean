import Freigen.Ast.Basic
import Lean.DeclarationRange
import Lean.Elab.Term

namespace Freigen
namespace Ast
namespace Reflector

open Lean Meta Elab Term

/-! ## Source-range quotation -/

private def quoteSourceRange (module : Name) (startPos endPos : Position) : Lean.Expr :=
  mkAppN (mkConst ``SourceRange.mk) #[toExpr module,
    mkNatLit startPos.line, mkNatLit startPos.column,
    mkNatLit endPos.line, mkNatLit endPos.column]

def declarationSourceRange? (decl : Name) : MetaM (Option Lean.Expr) := do
  let some ranges ← findDeclarationRanges? decl | return none
  let env ← getEnv
  let module := match env.getModuleIdxFor? decl with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  return some (quoteSourceRange module ranges.range.pos ranges.range.endPos)

def syntaxSourceRange? (stx : Syntax) : TermElabM (Option Lean.Expr) := do
  let some range := stx.getRange? | return none
  let fileMap ← getFileMap
  return some (quoteSourceRange (← getMainModule)
    (fileMap.toPosition range.start) (fileMap.toPosition range.stop))


end Reflector
end Ast
end Freigen
