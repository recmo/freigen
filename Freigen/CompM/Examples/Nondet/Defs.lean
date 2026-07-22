import Freigen.CompM.Basic
import Freigen.ITree.Basic
import Freigen.Eff

namespace Freigen.CompM.Examples.Nondet

inductive Eff : Type
| rand
| print

def Spec : Eff.Spec where
  tag := Eff
  input
    | .rand => Unit
    | .print => ℤ
  output
    | .rand => ℤ
    | .print => Unit
  blockTag := fun _ => Empty
  blockInputs := nofun
  blockOutputs := nofun

end Nondet

abbrev Nondet α := CompM Nondet.Spec α

namespace Nondet

def rand : Nondet ℤ := CompM.op (E := Spec) Eff.rand () nofun
def print (z : ℤ) : Nondet Unit := CompM.op (E := Spec) Eff.print z nofun

def approxWith {α} (entropy : ℕ → ℤ) (t : Nondet α) (n: Nat): List ℤ :=
  go (entropy, 0) n ((t.run pure).approx n) where
  go : (ℕ → ℤ) × ℕ → (n : Nat) → IxPoly.M.Approx (Eff.Step Spec) n α → List ℤ := fun entropy n approx => match n, approx with
   | 0, IxPoly.M.Approx.zero _ => []
   | n+1, IxPoly.M.Approx._succ _ _ p k => match p with
     | .ret _ => []
     | .tau => go entropy n (k ())
     | .op Eff.rand () => go (entropy.1, entropy.2 + 1) n (k $ .inl (entropy.1 entropy.2))
     | .op Eff.print z => z :: go entropy n (k $ .inl ())
     | .fail => []

end Freigen.CompM.Examples.Nondet
