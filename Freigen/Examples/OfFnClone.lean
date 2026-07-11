import Freigen.Examples.Circuit.Basic

/-!
# Array and vector reflection target

This deliberately remains ahead of the current object universe: `Array`, `Vector`, and indexed
lookup are not represented by `Tp` yet. The source stays live and executable so it remains a
concrete future reflector target. Once those representations exist, the final commented
`reflect_def` is the intended acceptance test.
-/

namespace Freigen.Ast.OfFnCloneExample

open Example

def MyArray.ofFn {A : Type} {n : Nat} (f : Fin n → A) : Array A :=
  go (Array.emptyWithCapacity n) n (Nat.le_refl n) where
  go (acc : Array A) : (i : Nat) → i ≤ n → Array A
    | i + 1, h =>
        have w : n - i - 1 < n :=
          Nat.lt_of_lt_of_le (Nat.sub_one_lt (Nat.sub_ne_zero_iff_lt.mpr h)) (Nat.sub_le n i)
        go (acc.push (f ⟨n - i - 1, w⟩)) i (Nat.le_of_succ_le h)
    | 0, _ => acc

theorem MyArray.size_go {A : Type} {n : Nat} (f : Fin n → A) :
    ∀ (i : Nat) (acc : Array A) (h : i ≤ n), (MyArray.ofFn.go f acc i h).size = acc.size + i := by
  intro i
  induction i with
  | zero => intro acc h; rfl
  | succ m ih => intro acc h; rw [MyArray.ofFn.go, ih]; simp; omega

theorem MyArray.size_ofFn {A : Type} {n : Nat} (f : Fin n → A) :
    (MyArray.ofFn f).size = n := by
  simp [MyArray.ofFn, MyArray.size_go]

def MyVector.ofFn {A : Type} {n : Nat} (f : Fin n → A) : Vector A n :=
  ⟨MyArray.ofFn f, MyArray.size_ofFn f⟩

def useOfFn (i : Fin 4) : Circuit Nat :=
  pure ((MyVector.ofFn (fun j : Fin 4 => j.val * 2)).get i)

example : Free Source Nat := useOfFn ⟨2, by decide⟩
example : Example.Circuit.evalWithHints (useOfFn ⟨2, by decide⟩) = some 4 := rfl

-- Future acceptance target, currently blocked on Array/Vector object representations:
-- reflect_def reflected := useOfFn ⟨2, by decide⟩

end Freigen.Ast.OfFnCloneExample
