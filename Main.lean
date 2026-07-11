import Freigen
import Freigen.Ast2.Compile
import Lean

open Lean Meta

/-- Render one recorded artifact: evaluate `Freigen.serialize decl.1` (a `String` — the uniform
    S-expression format of `Freigen.Ast.Sexp`) and write it to `path`, creating parent directories.
    Runs in `MetaM` so instance synthesis picks up the declaration's `[DSL]` instance; `evalExpr`
    runs the serializer over the imported code.  Also prints the `≈`-soundness statement the
    reflection proved (`decl`'s subtype predicate at `decl.1`) for inspection during the build. -/
unsafe def emitEntry (path : String) (decl : Name) : MetaM Unit := do
  let c ← mkConstWithFreshMVarLevels decl
  let closed ← mkAppM ``Subtype.val #[c]                   -- decl.1 : the `Closed` program
  let e ← mkAppM ``Freigen.serialize #[closed]             -- serialize decl.1 : String
  let contents ← evalExpr String (mkConst ``String) e
  let p : System.FilePath := path
  if let some dir := p.parent then IO.FS.createDirAll dir
  IO.FS.writeFile p contents
  IO.println s!"freigen: emitted {path} ({contents.length} bytes)"
  -- The reflection's theorem: the subtype predicate `P` applied to the closed program `decl.1`.
  if let (``Subtype, #[_, pred]) := (← whnf (← inferType c)).getAppFnArgs then
    let stmt := (mkApp pred closed).headBeta
    IO.println s!"  ⊢ {← ppExpr stmt}"

/-- Render an AST2 artifact already serialized by its `#compile` command. -/
unsafe def emitAst2Entry (path : String) (serialized sound : Name) : MetaM Unit := do
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
  let arts := Freigen.compileExt.getState env |>.filter fun (_, decl) =>
    match env.getModuleIdxFor? decl with
    | some idx => targetMods.contains env.header.moduleNames[idx.toNat]!
    | none     => false
  let ast2Arts := Freigen.Ast2.compileExt.getState env |>.filter fun (_, serialized, _) =>
    match env.getModuleIdxFor? serialized with
    | some idx => targetMods.contains env.header.moduleNames[idx.toNat]!
    | none     => false
  if arts.isEmpty && ast2Arts.isEmpty then
    IO.println "freigen: no `#compile` artifacts found in the given modules"
    return
  let act : MetaM Unit := do
    arts.forM fun (path, decl) => emitEntry path decl
    ast2Arts.forM fun (path, serialized, sound) =>
      emitAst2Entry path serialized sound
  let ctx : Core.Context := { fileName := "<freigen>", fileMap := default }
  discard <| (act.run').toIO ctx { env }

@[implemented_by runImpl]
def run (_args : List String) : IO Unit := pure ()

/-- The `freigen` emitter, invoked by the `lake build <lib>:prog` facet with the target library's
    modules and an augmented `LEAN_PATH`. -/
def main (args : List String) : IO Unit := run args
