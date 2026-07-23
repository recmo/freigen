import Freigen.CompM.Basic
import Freigen.ITree.Basic
import Freigen.Eff

namespace Freigen.CompM.Examples.Nondet

inductive Eff : Type
| rand
| print

instance : Eff.Spec Eff where
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

abbrev Nondet α := CompM (Eff.Tau ⊕ Nondet.Eff) α

namespace Nondet

def rand : Nondet ℤ := CompM.op (E := Eff.Tau ⊕ Eff) (Sum.inr Eff.rand) () nofun
def print (z : ℤ) : Nondet Unit := CompM.op (E := Eff.Tau ⊕ Eff) (Sum.inr Eff.print) z nofun

def approxWith {α} (entropy : ℕ → ℤ) (t : Nondet α) (n: Nat): List ℤ :=
  go (entropy, 0) n ((t.run pure).approx n) where
  go : (ℕ → ℤ) × ℕ → (n : Nat) → IxPoly.M.Approx (Eff.Step $ Eff.Tau ⊕ Eff) n α → List ℤ := fun entropy n approx => match n, approx with
   | 0, IxPoly.M.Approx.zero _ => []
   | n+1, IxPoly.M.Approx._succ _ _ p k => match p with
     | .ret _ => []
     | .op (Sum.inr Eff.rand) () => go (entropy.1, entropy.2 + 1) n (k $ .inl (entropy.1 entropy.2))
     | .op (Sum.inr Eff.print) z => z :: go entropy n (k $ .inl ())
     | .op (Sum.inl _) _ => go entropy n (k $ .inl ())

end Freigen.CompM.Examples.Nondet
