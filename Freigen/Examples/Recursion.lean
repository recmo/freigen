import Freigen.Examples.Circuit.Basic

/-! Structural recursion targets for the unified reflector. -/

namespace Freigen.Ast.RecursionExample

open Example

def countdown : Nat → Circuit Nat
  | 0 => pure 0
  | n + 1 => countdown n

def sum : Nat → Circuit Nat
  | 0 => pure 0
  | n + 1 => do
      let rest ← sum n
      pure (rest + n + 1)

def countAsserts : Nat → Circuit Nat
  | 0 => pure 0
  | n + 1 => do
      let _ ← Circuit.assert true
      countAsserts n

def countdownMain : Circuit Nat := do
  let n ← Circuit.hint (pure 5)
  countdown n

def sumMain : Circuit Nat := do
  let n ← Circuit.hint (pure 5)
  sum n

def countAssertsMain : Circuit Nat := do
  let n ← Circuit.hint (pure 3)
  countAsserts n

reflect_def sumReflected := sumMain

-- Future acceptance targets. The source programs remain checked above.
-- reflect_def countdownReflected := countdownMain
-- reflect_def countAssertsReflected := countAssertsMain

example : ITree.CompE.Eutt CircCompat Eq (Free.toITree sumMain)
    (Expr.denote (sumReflected (Tp.denote M))) :=
  sumReflected_sound

end Freigen.Ast.RecursionExample
