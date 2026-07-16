import Freigen.Ast.Sexp
import Lean.Elab.Command

namespace Freigen.Ast

open Lean

abbrev CompileArtifact := String × Name × Name

/-- Serialized programs recorded by `#compile` and consumed by the lightweight emitter. -/
initialize compileExt : SimplePersistentEnvExtension CompileArtifact (Array CompileArtifact) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[]
  }

end Freigen.Ast
