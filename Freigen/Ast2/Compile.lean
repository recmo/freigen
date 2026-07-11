import Freigen.Ast2.Reflector
import Freigen.Ast2.Sexp
import Lean.Elab.Command
import Lean.Elab.SyntheticMVars

namespace Freigen.Ast2

open Lean Meta Elab Term Command

abbrev CompileArtifact := String × Name × Name

initialize compileExt : SimplePersistentEnvExtension CompileArtifact (Array CompileArtifact) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[]
  }

private def registryEntries : CoreM (Array Name) := do
  let env ← getEnv
  return env.constants.toList.foldl (init := #[]) fun entries entry =>
    if ast2RenderAttr.hasTag env entry.1 then entries.push entry.1 else entries

private def resolveRender (H : Lean.Expr) : MetaM Lean.Expr := do
  let expected ← mkAppM ``RenderSpec #[H]
  let saved ← get
  for candidate in ← registryEntries do
    try
      let value ← mkConstWithFreshMVarLevels candidate
      let ⟨args, _, result⟩ ← forallMetaTelescope (← inferType value)
      unless ← isDefEq result expected do throwError "not this renderer"
      for arg in args do
        unless ← arg.mvarId!.isAssigned do
          throwError "renderer has unresolved parameters"
      return ← instantiateMVars (mkAppN value args)
    catch _ => set saved
  throwError "#compile: target signature has no @[ast2_render] declaration"

/-- Reflect, kernel-check, serialize, and register an AST2 program for the `:prog` facet. -/
elab "#compile " program:term " => " path:str : command => do
  let (reflected, targetSig) ← liftTermElabM do
    let source ← elabTermAndSynthesize program none
    let source ← instantiateMVars source
    let plan ← Reflector.discover source
    let reflected ← elabTermAndSynthesize (← `(reflect% $program)) none
    synthesizeSyntheticMVarsNoPostponing
    pure (← instantiateMVars reflected, plan.targetSig)
  let idx := (compileExt.getState (← getEnv)).size
  let base : Name := if program.raw.isIdent then program.raw.getId else `compiled
  let reflectedName := (← getMainModule) ++ base ++ Name.mkSimple s!"ast2_reflected_{idx}"
  let reflectedType ← liftTermElabM <| inferType reflected
  liftCoreM <| addAndCompile <| .defnDecl {
    name := reflectedName
    levelParams := (collectLevelParams (collectLevelParams {} reflected) reflectedType).params.toList
    type := reflectedType
    value := reflected
    hints := .opaque
    safety := .safe
  }
  let (serialized, soundName) ← liftTermElabM do
    let reflectedConst ← mkConstWithFreshMVarLevels reflectedName
    let code ← mkAppM ``Subtype.val #[reflectedConst]
    let render ← resolveRender targetSig
    let serialized ← mkAppM ``serialize #[render, code]
    pure (serialized, reflectedName.appendAfter "_sound")
  let serializedType ← liftTermElabM <| inferType serialized
  let serializedName := reflectedName.appendAfter "_sexp"
  liftCoreM <| addAndCompile <| .defnDecl {
    name := serializedName
    levelParams := []
    type := serializedType
    value := serialized
    hints := .opaque
    safety := .safe
  }
  -- A named theorem makes the certificate inspectable independently of the serialized string.
  let soundValue ← liftTermElabM do
    let reflectedConst ← mkConstWithFreshMVarLevels reflectedName
    mkAppM ``Subtype.property #[reflectedConst]
  let soundType ← liftTermElabM <| inferType soundValue
  liftCoreM <| addDecl <| .thmDecl {
    name := soundName
    levelParams := []
    type := soundType
    value := soundValue
  }
  modifyEnv (compileExt.addEntry · (path.getString, serializedName, soundName))

end Freigen.Ast2
