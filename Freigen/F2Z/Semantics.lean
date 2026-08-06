import Freigen.F2Z.Defs

namespace Freigen.F2Z.Semantics

def LC α := Std.ExtTreeMap Nat α

structure CS where
  A : Array (LC ℤ)
  B : Array (LC ℤ)
  C : Array (LC ℤ)
  M : Array (LC Bool)



end Freigen.F2Z.Semantics
