import Freigen.Examples.Circuit.Basic

/-! First-class function targets for the unified reflector. -/

namespace Freigen.Ast.FirstClassExample

open Example

def applyTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

def useTwice (x : Nat) : Circuit Nat :=
  pure (applyTwice (fun y => y + x) x)

def program : Circuit Nat := do
  let x ← Circuit.hint (pure 4)
  useTwice x

#reflect_plan program

-- Future acceptance target: generic PHOAS reification does not yet spill this capturing helper.
-- reflect_def reflected := program

end Freigen.Ast.FirstClassExample
