import Freigen.F2Z.Cert
import Freigen.F2Z.Defs
import Mathlib.Data.List.DropRight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Digits.Lemmas
import Batteries.Data.Vector.Lemmas

namespace Freigen.F2Z

open Context

private theorem ofDigits_rdropWhile_false (l : List Bool) :
    Nat.ofDigits 2 ((l.rdropWhile (fun b => !b)).map Bool.toNat) =
      Nat.ofDigits 2 (l.map Bool.toNat) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l b ih =>
    cases b <;> simp [ih]

private theorem bits_ofDigits_bool (l : List Bool) :
    (Nat.ofDigits 2 (l.map Bool.toNat)).bits = l.rdropWhile (fun b => !b) := by
  let t := l.rdropWhile (fun b => !b)
  rw [← ofDigits_rdropWhile_false]
  have hdigits : Nat.digits 2 (Nat.ofDigits 2 (t.map Bool.toNat)) = t.map Bool.toNat := by
    apply Nat.digits_ofDigits 2 (by omega)
    · rintro x hx
      simp only [List.mem_map] at hx
      obtain ⟨b, _, rfl⟩ := hx
      cases b <;> simp
    · intro h
      have ht : t ≠ [] := by simpa using h
      have hlast := List.rdropWhile_last_not (fun b : Bool => !b) l ht
      simp only [List.getLast_map]
      cases hb : t.getLast ht <;> simp_all [t]
  rw [Nat.digits_two_eq_bits] at hdigits
  apply (List.map_inj_right (f := Bool.toNat)
    (fun a b h => by cases a <;> cases b <;> simp_all)).mp
  change (Nat.ofDigits 2 (t.map Bool.toNat)).bits.map Bool.toNat = t.map Bool.toNat
  have hfun : (fun b : Bool => bif b then 1 else 0) = Bool.toNat := by
    funext b
    cases b <;> rfl
  simpa only [hfun] using hdigits

private theorem ofDigits_bool_eq_sum {n : Nat} (f : Fin n → Bool) :
    Nat.ofDigits 2 ((List.ofFn f).map Bool.toNat) =
      ∑ k : Fin n, 2 ^ k.val * (f k).toNat := by
  simp [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn,
    Function.comp_def, mul_comm]

private theorem ofDigits_vector_eq_sum {n : Nat} (v : Vector Bool n) :
    Nat.ofDigits 2 (v.toList.map Bool.toNat) =
      ∑ k : Fin n, 2 ^ k.val * (v[k]).toNat := by
  rw [← Vector.ofFn_getElem (xs := v), Vector.toList_ofFn]
  simpa using ofDigits_bool_eq_sum (fun i : Fin n => v[i.val])

variable [ctx : Context]

def fromBits {n : Nat} (r : Vector WBool n):
    Circuit $ (i : Wℤ) × Cert (fun pℤ pB => pℤ i = ∑ k : Fin n, 2^k.val * (pB r[k]).toInt) :=
  match n with
  | 0 => pure ⟨0, by cert; simp⟩
  | n + 1 => do
    let ⟨i, ht⟩ ← fromBits r.tail
    let ⟨b, hh⟩ ← f2z r.head
    pure ⟨b + 2 • i, by
      cert
      simp only [Valuation.add_apply, ←hh, LinearMap.map_smul_of_tower, ht, Nat.add_one_sub_one,
        Int.nsmul_eq_mul, Nat.cast_ofNat, Fin.getElem_fin,
        Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, one_mul, Fin.val_succ,
        pow_succ, Finset.mul_sum]
      congr 2
      ext i
      ring_nf
      congr 4
      simp only [getElem, Vector.get_tail]
      grind
    ⟩

def toBits (n : ℕ) (i: Wℤ):
    Circuit $ (r: Vector WBool n) × Cert (fun ρℤ ρBool => ∃(ni : Nat), ρℤ i = ni ∧
      (r.toList.map (fun b => ρBool b) |>.rdropWhile (· = false)) = ni.bits) := do
  let r ← hint (argTps := [.z]) h![i] fun h![i] => do
    let rawBits := i.toNat.bits.toArray
    let padded := rawBits.take n ++ Array.replicate (n - rawBits.size) false
    let paddedVec : Vector Bool n := ⟨padded, by grind⟩
    paddedVec.mapM writeWitness
  let ⟨sum, hs⟩ ← fromBits r
  let c ← assertR1C sum 1 i
  return ⟨r, by
    cert
    let v := r.map ρBool
    let ni := Nat.ofDigits 2 (v.toList.map Bool.toNat)
    refine ⟨ni, ?_, ?_⟩
    · calc
        ρℤ i = ρℤ sum := by simpa using c.symm
        _ = ∑ k : Fin n, 2 ^ k.val * (ρBool r[k]).toInt := hs
        _ = (ni : Int) := by
          have h := congrArg (fun x : Nat => (x : Int)) (ofDigits_vector_eq_sum v).symm
          have hbool (b : Bool) : (b.toNat : Int) = b.toInt := by cases b <;> rfl
          simpa [v, ni, hbool] using h
    · simpa [v, ni, Vector.toList_map] using (bits_ofDigits_bool v.toList).symm
  ⟩



end Freigen.F2Z
