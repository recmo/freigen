import Freigen.Examples.Circuit.Basic
import Freigen.Examples.Storage
import Freigen.Examples.Recursion

/-! Axiom footprint smoke tests for generated reflection certificates. -/

namespace Freigen.Ast

#print axioms Example.symbolicHelperNamed_sound
#print axioms Example.symbolicRecursiveReflected_sound
#print axioms Example.tupledHelperReflected_sound
#print axioms StorageExample.reflected_sound
#print axioms RecursionExample.sumReflected_sound

end Freigen.Ast
