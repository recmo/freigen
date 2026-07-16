import Freigen.Reflect.Emit
import Lean.Elab.Command
import Lean.Elab.SyntheticMVars

namespace Freigen
namespace Ast
namespace Reflector

open Lean Meta Elab Term

/-- Inspect specialization discovery independently of execution. -/
elab "#reflect_plan " t:term : command => Command.liftTermElabM do
  let root ← elabTermAndSynthesize t none
  let plan ← discover (← instantiateMVars root)
  logInfo m!"AST reflection plan: {plan.specializations.map (·.name)}"

/-- Concrete semantic reflection, retained as a debugging surface for smart constructors. -/
elab "reflect_semantic% " t:term : term => do
  let source ← elabTermAndSynthesize t none
  reflectTerm (← instantiateMVars source) (← syntaxSourceRange? t)

/-- AST `reflect%`: closed PHOAS code bundled with its relational soundness theorem. -/
elab "reflect% " t:term : term => do
  let source ← elabTermAndSynthesize t none
  reflectProgram (← instantiateMVars source) (← syntaxSourceRange? t)

elab doc:(Lean.Parser.Command.docComment)? "reflect_def " nm:ident " := " t:term : command =>
  Command.liftTermElabM do
    let source ← elabTermAndSynthesize t none
    let reflected ← reflectProgram (← instantiateMVars source) (← syntaxSourceRange? t)
    synthesizeSyntheticMVarsNoPostponing
    let reflected ← instantiateMVars reflected
    let code ← mkAppM ``Subtype.val #[reflected]
    let sound ← mkAppM ``Subtype.property #[reflected]
    let codeName := (← getCurrNamespace) ++ nm.getId
    let soundName := codeName.appendAfter "_sound"
    addAndCompile (.defnDecl {
      name := codeName
      levelParams := []
      type := ← inferType code
      value := code
      hints := .regular (getMaxHeight (← getEnv) code + 1)
      safety := .safe
    })
    let soundType := (← inferType sound).replace fun e =>
      if e == code then some (mkConst codeName) else none
    addDecl (.thmDecl {
      name := soundName
      levelParams := []
      type := soundType
      value := ← mkExpectedTypeHint sound soundType
    })
    if let some d := doc then
      addDocStringCore codeName (← Lean.getDocStringText d)
    Term.addTermInfo' nm (mkConst codeName) (isBinder := true)

end Reflector
end Ast
end Freigen
