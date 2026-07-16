import Freigen.Compile.Registry
import Lean

open Lean Meta

/-- Render an artifact serialized by its `#compile` command. -/
unsafe def emitEntry (path : String) (serialized sound : Name) : MetaM Unit := do
  let contents ← evalExpr String (mkConst ``String)
    (← mkConstWithFreshMVarLevels serialized)
  let p : System.FilePath := path
  if let some dir := p.parent then IO.FS.createDirAll dir
  IO.FS.writeFile p contents
  IO.println s!"freigen: emitted {path} ({contents.length} bytes)"
  let statement ← inferType (← mkConstWithFreshMVarLevels sound)
  IO.println s!"  ⊢ {← ppExpr statement}"

/-- Import the given modules (loading env extensions) and flush every `#compile` artifact to disk. -/
unsafe def runImpl (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.eprintln "usage: freigen <Module.Name> [Module.Name …]"
    IO.Process.exit 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let targetMods := args.foldl (·.insert ·.toName) (∅ : NameSet)
  let imports := args.toArray.map fun m => { module := m.toName : Import }
  let env ← importModules imports {} (loadExts := true)
  -- Emit only artifacts declared *in the requested library's own modules*, not ones pulled in
  -- transitively from dependencies (e.g. Freigen's own examples).
  let arts := Freigen.Ast.compileExt.getState env |>.filter fun (_, serialized, _) =>
    match env.getModuleIdxFor? serialized with
    | some idx => targetMods.contains env.header.moduleNames[idx.toNat]!
    | none     => false
  if arts.isEmpty then
    IO.println "freigen: no `#compile` artifacts found in the given modules"
    return
  let act : MetaM Unit := do
    arts.forM fun (path, serialized, sound) =>
      emitEntry path serialized sound
  let ctx : Core.Context := { fileName := "<freigen>", fileMap := default }
  discard <| (act.run').toIO ctx { env }

@[implemented_by runImpl]
def run (_args : List String) : IO Unit := pure ()

/-- The `freigen` emitter, invoked by the `lake build <lib>:prog` facet with the target library's
    modules and an augmented `LEAN_PATH`. -/
def main (args : List String) : IO Unit := run args
