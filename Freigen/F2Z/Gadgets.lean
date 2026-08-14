import Freigen.F2Z.Defs
import Freigen.F2Z.Correctness.Basic
import Mathlib.Data.List.DropRight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Digits.Lemmas
import Batteries.Data.Vector.Lemmas

namespace Freigen.F2Z

private theorem natCast_ofBits_eq_sum (f : Fin n → Bool) :
    (Nat.ofBits f : Int) =
      ∑ k : Fin n, 2 ^ k.val * (f k).toInt := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.ofBits_succ, Nat.cast_add, Nat.cast_mul, Fin.sum_univ_succ]
      simp only [Nat.cast_ofNat, Fin.val_zero, pow_zero, one_mul,
        Fin.val_succ, pow_succ]
      rw [ih, Finset.mul_sum]
      have hf : ((f 0).toNat : Int) = (f 0).toInt := by
        cases f 0 <;> rfl
      rw [hf, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.comp_apply]
      ring

structure Word (n : Nat) where
  bitsLE : Vector (LC Bool) n

def Word.evalZ (ρ : WF.Valuation) (w : Word n) : ℤ :=
  Nat.ofBits fun i => (w.bitsLE[i].eval ρ.bool)

def Word.take (m : Nat) (w : Word n) : Word (min m n) :=
  { bitsLE := w.bitsLE.take m }

def Word.takeLE (m : Nat) (h : m ≤ n) (w : Word n) : Word m :=
  (Nat.min_eq_left h) ▸ { bitsLE := w.bitsLE.take m }

def Word.rotateRight (k : Nat) (w : Word n) : Word n :=
  { bitsLE := show (n - k + min k n = n) by omega ▸ (w.bitsLE.drop k ++ w.bitsLE.take k) }

instance : HShiftRight (Word n) Nat (Word n) where
  hShiftRight w a := show (n - a + min a n = n) by omega ▸
    { bitsLE := w.bitsLE.drop a ++ Vector.replicate (min a n) (0 : LC Bool)}

instance : HXor (Word n) (Word n) (Word n) where
  hXor w₁ w₂ := { bitsLE := Vector.zipWith (· + ·) w₁.bitsLE w₂.bitsLE }

instance : GetElem (Word n) (Fin n) (LC Bool) (fun _ _ => True) where
  getElem w i _ := w.bitsLE[i]

structure U (n : Nat) where
  bits : Word n
  intBits : Vector (LC ℤ) n

instance : Inhabited (LC Bool) where
  default := 0

instance : Inhabited (LC ℤ) where
  default := 0

instance : Inhabited (U n) where
  default := {
    bits := {
      bitsLE := Vector.replicate n 0
    }
    intBits := Vector.replicate n 0
  }

def U.Valid (u : U n) (ρ : WF.Valuation) : Prop :=
  ∀ i : Fin n, u.intBits[i].eval ρ.int = (u.bits.bitsLE[i].eval ρ.bool).toInt

def U.fromWord (w : Word n) : Circuit (U n) := do
  let mut res := Vector.replicate n 0
  for h:i in [0:n] do
    let b ← f2z w.bitsLE[i]
    res := res.set! i b
  pure { bits := w, intBits := res }

def U.intVal (u : U n) : LC ℤ :=
  ∑ i : Fin n, 2 ^ i.val • u.intBits[i]

def U.eval : U n → WF.Valuation → BitVec n := fun u ρ =>
  BitVec.ofNat n $ (u.intVal.eval ρ.int).toNat

theorem U.eval_intVal_eq_evalZ (u : U n) (h : u.Valid ρ) :
    u.intVal.eval ρ.int = u.bits.evalZ ρ := by
  unfold U.intVal Word.evalZ
  rw [natCast_ofBits_eq_sum]
  simp only [LC.eval_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LC.eval_nsmul, h i]
  simp

def U.fromInt (n : Nat) (x : LC ℤ) : Circuit (U n) := do
  let bits ← hint h![x] fun h![(x: Int)] => match x with
    | .ofNat n => pure $ Vector.ofFn fun i => n.testBit i
    | _ => fail s!"negative integer {x} in U.fromInt"
  let r ← U.fromWord { bitsLE := bits }
  assertR1C 0 0 (x - r.intVal)
  pure r

def U.sum (us : Array (U n)) : Circuit (U n) := do
  let newZ := us.map (·.intVal) |>.sum
  let newBits ← U.fromInt (n + Nat.clog 2 us.size) newZ
  have : min n (n + Nat.clog 2 us.size) = n := by grind
  pure { bits := this ▸ newBits.bits.take n, intBits := this ▸ newBits.intBits.take n }

open Std.Do
open scoped Std.Do

private theorem Vector.set!_eq_setIfInBounds (xs : Vector α n) (i : Nat) (x : α) :
    xs.set! i x = xs.setIfInBounds i x := by
  rfl

@[simp]
theorem U.valid_default {n : Nat} : (default : U n).Valid ρ := by
  intro i
  change LC.eval ρ.int (Vector.replicate n (0 : LC ℤ))[i.val] =
    (LC.eval ρ.bool (Vector.replicate n (0 : LC Bool))[i.val]).toInt
  simp
  rfl

@[spec]
theorem U.fromWord_sound {ρ} {w : Word n}:
    ⦃ ⌜True⌝ ⦄
      (Sound.interp ρ $ U.fromWord w)
    ⦃ ⇓ u => ⌜u.bits = w⌝ ∧ ⌜u.Valid ρ⌝ ⦄ := by
  mvcgen [U.fromWord] invariants
  · ⇓⟨cur, res⟩ => ⌜∀ i : Fin n, i.val < cur.prefix.length →
      res[i].eval ρ.int = (w.bitsLE[i].eval ρ.bool).toInt⌝
  case vc1 pref cur _ _ _ h₁ _ h₂ =>
    rename_i suff out hloop hsplit
    have : cur = pref.length := by grind
    subst cur
    have hk : pref.length < n := by grind
    intro i hseen
    simp only [List.length_append, List.length_singleton] at hseen
    rw [Vector.set!_eq_setIfInBounds]
    simp only [Fin.getElem_fin] at h₁ ⊢
    by_cases hi : i.val < pref.length
    · rw [Vector.getElem_setIfInBounds_ne i.isLt (by omega)]
      exact h₁ i hi
    · have hieq : i.val = pref.length := by omega
      simpa [Vector.getElem_setIfInBounds, hieq] using h₂.symm
  case vc2 => simp
  case vc3 h =>
    constructor
    · trivial
    · intro i
      exact h i (by grind)

@[spec]
theorem U.fromWord_complete {ρ} {w : Word n} :
    ⦃ ⌜True⌝ ⦄ (Complete.interp ρ $ U.fromWord w)
    ⦃ ⇓ u => ⌜u.bits = w ∧ u.Valid ρ⌝ ⦄ := by
  mvcgen [U.fromWord] invariants
  · ⇓⟨cur, res⟩ => ⌜∀ i : Fin n, i.val < cur.prefix.length →
      res[i].eval ρ.int = (w.bitsLE[i].eval ρ.bool).toInt⌝
  case vc1 pref cur _ _ _ h₁ _ h₂ =>
    rename_i suff out hloop hsplit
    have : cur = pref.length := by grind
    subst cur
    have hk : pref.length < n := by grind
    intro i hseen
    simp only [List.length_append, List.length_singleton] at hseen
    rw [Vector.set!_eq_setIfInBounds]
    simp only [Fin.getElem_fin] at h₁ ⊢
    by_cases hi : i.val < pref.length
    · rw [Vector.getElem_setIfInBounds_ne i.isLt (by omega)]
      exact h₁ i hi
    · have hieq : i.val = pref.length := by omega
      simpa [Vector.getElem_setIfInBounds, hieq] using h₂
  case vc2 => simp
  case vc3 h =>
    constructor
    · trivial
    · intro i
      exact h i (by grind)

theorem U.fromWord_wf :
    WF.GadgetSpec
      (fun leftVal rightVal (left right : Word n) =>
        ∀ i : Fin n,
          WF.LCEq leftVal.bool rightVal.bool left.bitsLE[i] right.bitsLE[i])
      U.fromWord
      (fun leftVal rightVal left right =>
        (∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
          left.bits.bitsLE[i] right.bits.bitsLE[i]) ∧
        WF.LCEq leftVal.int rightVal.int left.intVal right.intVal) := by
  wfgen [U.fromWord]

theorem U.fromInt_sound {ρ} {n : Nat} {x : LC ℤ} :
    ⦃ ⌜True⌝ ⦄ (Sound.interp ρ $ U.fromInt n x)
    ⦃ ⇓ u => ⌜u.Valid ρ⌝ ∧ ⌜u.intVal.eval ρ.int = x.eval ρ.int⌝ ⦄ := by
  mvcgen [fromInt]
  intro b
  mvcgen
  simp only [Valid, LC.eval_zero, mul_zero, LC.eval_sub] at *
  grind

theorem U.fromInt_complete {ρ} {n : Nat} {x : LC ℤ} (h0 : x.eval ρ.int ≥ 0)
    (h2 : x.eval ρ.int < 2 ^ n) :
    ⦃ ⌜True⌝ ⦄ (Complete.interp ρ $ U.fromInt n x)
    ⦃ ⇓ u => ⌜u.Valid ρ⌝ ∧ ⌜u.intVal.eval ρ.int = x.eval ρ.int⌝ ⦄ := by
  mvcgen [fromInt]
  have : ∃n, LC.eval ρ.int x = Int.ofNat n := by
    exists (x.eval ρ.int).toNat
    simp_all
  rcases this with ⟨x', hx'⟩
  simp only [WF.interpHint, WF.evalArgs, hx', Int.ofNat_eq_natCast, Free.interp_pure,
    Option.pure_def, Option.some.injEq, exists_eq_left', Vector.map_ofFn]
  mvcgen
  rename_i r h
  rcases h with ⟨h, h'⟩
  have hxlt : x' < 2 ^ n := by
    rw [hx'] at h2
    exact Int.ofNat_lt.mp (by simpa using h2)
  have hbits : r.bits.evalZ ρ = x' := by
    simp [Word.evalZ, h, Nat.ofBits_testBit, Nat.mod_eq_of_lt hxlt]
  have hintVal : r.intVal.eval ρ.int = (x' : Int) :=
    (U.eval_intVal_eq_evalZ r h').trans (by simpa using hbits)
  constructor
  · simp [LC.eval_zero, LC.eval_sub, hx', hintVal]
  · mvcgen

theorem U.fromInt_wf :
    WF.GadgetSpec
      (fun leftVal rightVal (left right : LC ℤ) =>
        WF.LCEq leftVal.int rightVal.int left right)
      (U.fromInt n)
      (fun leftVal rightVal left right =>
        WF.LCEq leftVal.int rightVal.int left.intVal right.intVal ∧
        (∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
          left.bits.bitsLE[i] right.bits.bitsLE[i])) := by
  wfgen [U.fromInt]

-- theorem U.sum

end Freigen.F2Z
