import Freigen.F2Z.Examples.EcdsaP256.Lemmas
import Freigen.F2Z.Examples.EcdsaP256.Radix32Impl

/-!
# Signed radix-32 ECDSA-P256 lemmas

The experimental radix-32 verifier proofs live in this module so proof
iterations do not repeatedly elaborate the much larger legacy lemma file.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open BigOperators
open Modular
open P256
open P256.Projective

set_option maxRecDepth 10000

def Radix32TableSpec (rho : WF.Valuation) (table : Radix32Table)
    (q : P256.Reference.Point) : Prop :=
  (∀ i : Fin 16,
    P256.Reference.NormalizedRep rho table.low[i] (i.val • q)) ∧
  P256.Reference.NormalizedRep rho table.p16 (16 • q)

def Radix32TableValid (rho : WF.Valuation) (table : Radix32Table) : Prop :=
  (∀ i : Fin 16, table.low[i].Valid rho) ∧ table.p16.Valid rho

@[spec] theorem materializeRadix32Multiples_sound {P : P256.Projective}
    {q : P256.Reference.Point}
    (hP : P256.Reference.Represents ρ
      (P256.AffineSlope.ofElems P.X P.Y) q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (materializeRadix32Multiples P)
    ⦃⇓ table => ⌜Radix32TableSpec ρ table q⌝⦄ := by
  mvcgen [materializeRadix32Multiples, Radix32TableSpec]
  case vc4.hP table htable => exact htable 8

@[spec] theorem materializeRadix32Multiples_complete {P : P256.Projective}
    {q : P256.Reference.Point}
    (hPvalid : P.Valid ρ)
    (hP : P256.Reference.Represents ρ
      (P256.AffineSlope.ofElems P.X P.Y) q)
    (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (materializeRadix32Multiples P)
    ⦃⇓ table => ⌜Radix32TableValid ρ table ∧
      Radix32TableSpec ρ table q⌝⦄ := by
  mvcgen [materializeRadix32Multiples, Radix32TableValid,
    Radix32TableSpec]
  case vc6.hPvalid table htable => exact (htable 8).1
  case vc7.hP table htable => exact (htable 8).2
  case vc9.success.success =>
    rename_i table htable p16 hp16
    exact ⟨⟨fun i => (htable i).1, hp16.1⟩,
      ⟨fun i => (htable i).2, by simpa using hp16.2⟩⟩

def SignedDigitSpec (rho : WF.Valuation) (value : LC ℤ)
    (digit : SignedDigit) : Prop :=
  digit.oneHot.Valid rho ∧ ∃ slot : Fin 33,
    digit.oneHot.intBits[slot].eval rho.int = 1 ∧
    value.eval rho.int = (slot.val : Int) - 16 ∧
    ∀ other : Fin 33,
      digit.oneHot.intBits[other].eval rho.int = 1 → other = slot

private theorem SignedDigitSpec.bit_zero_or_one
    (h : SignedDigitSpec ρ value digit) (slot : Fin 33) :
    digit.oneHot.intBits[slot].eval ρ.int = 0 ∨
      digit.oneHot.intBits[slot].eval ρ.int = 1 := by
  have hbit := h.1 slot
  cases hb : digit.oneHot.bits.bitsLE[slot].eval ρ.bool <;>
    rw [hb] at hbit <;> simp at hbit
  · exact Or.inl hbit
  · exact Or.inr hbit

private theorem SignedDigitSpec.bit_zero_of_ne
    (h : SignedDigitSpec ρ value digit) {chosen other : Fin 33}
    (hchosen : digit.oneHot.intBits[chosen].eval ρ.int = 1)
    (hunique : ∀ j : Fin 33,
      digit.oneHot.intBits[j].eval ρ.int = 1 → j = chosen)
    (hne : other ≠ chosen) :
    digit.oneHot.intBits[other].eval ρ.int = 0 := by
  rcases h.bit_zero_or_one other with hzero | hone
  · exact hzero
  · exact (hne (hunique other hone)).elim

private theorem SignedDigitSpec.weighted_eval
    (h : SignedDigitSpec ρ value digit) (f : Fin 33 → Int)
    {chosen : Fin 33}
    (hchosen : digit.oneHot.intBits[chosen].eval ρ.int = 1)
    (hunique : ∀ j : Fin 33,
      digit.oneHot.intBits[j].eval ρ.int = 1 → j = chosen) :
    (∑ slot : Fin 33, f slot • digit.oneHot.intBits[slot]).eval ρ.int =
      f chosen := by
  rw [LC.eval_sum]
  simp only [LC.eval_smul]
  apply Aux.sum_mul_oneHot
  · exact hchosen
  · intro other hne
    exact h.bit_zero_of_ne hchosen hunique hne

theorem SignedDigitSpec.value_eval (h : SignedDigitSpec ρ value digit) :
    digit.value.eval ρ.int = value.eval ρ.int := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  unfold SignedDigit.value
  rw [h.weighted_eval (fun slot => (slot.val : Int) - 16)
    hchosen hunique, hvalue]

theorem SignedDigitSpec.magnitude_eval
    (h : SignedDigitSpec ρ value digit) :
    digit.magnitude.eval ρ.int = (value.eval ρ.int).natAbs := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  unfold SignedDigit.magnitude
  rw [LC.eval_sum]
  simp only [LC.eval_nsmul, nsmul_eq_mul]
  rw [Aux.sum_mul_oneHot
    (fun slot : Fin 33 => (Int.natAbs ((slot.val : Int) - 16) : Int))
    (fun slot => digit.oneHot.intBits[slot].eval ρ.int) chosen hchosen]
  · rw [hvalue]
  · intro other hne
    exact h.bit_zero_of_ne hchosen hunique hne

theorem SignedDigitSpec.negative_eval
    (h : SignedDigitSpec ρ value digit) :
    digit.negative.eval ρ.int = if value.eval ρ.int < 0 then 1 else 0 := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  unfold SignedDigit.negative
  rw [h.weighted_eval
    (fun slot => if slot.val < 16 then (1 : Int) else 0)
    hchosen hunique]
  split <;> split <;> simp_all <;> omega

theorem SignedDigitSpec.isSixteen_eval
    (h : SignedDigitSpec ρ value digit) :
    digit.isSixteen.eval ρ.int =
      if value.eval ρ.int = -16 ∨ value.eval ρ.int = 16 then 1 else 0 := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  unfold SignedDigit.isSixteen
  rw [h.weighted_eval
    (fun slot => if slot.val = 0 ∨ slot.val = 32 then (1 : Int) else 0)
    hchosen hunique]
  split <;> split <;> simp_all <;> omega

private theorem signedDigitSpec_of_indicators {value : LC ℤ} {oneHot : U 33}
    (h : IndicatorsSpec ρ (value + 16) oneHot) :
    SignedDigitSpec ρ value ⟨oneHot⟩ := by
  rcases h with ⟨hvalid, slot, hslot, hvalue, hunique⟩
  refine ⟨hvalid, slot, hslot, ?_, hunique⟩
  have h16 : LC.eval ρ.int (16 : LC ℤ) = 16 := LC.eval_natCast ρ.int 16
  rw [LC.eval_add, h16] at hvalue
  omega

@[spec] theorem signedDigitIndicators_sound {value : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (signedDigitIndicators value)
    ⦃⇓ digit => ⌜SignedDigitSpec ρ value digit⌝⦄ := by
  mvcgen [signedDigitIndicators, SignedDigitSpec, IndicatorsSpec]
  exact signedDigitSpec_of_indicators ‹IndicatorsSpec ρ (value + 16) _›

@[spec] theorem signedDigitIndicators_complete {value : LC ℤ}
    (hlow : -16 ≤ value.eval ρ.int)
    (hhigh : value.eval ρ.int ≤ 16) :
    ⦃⌜True⌝⦄ Complete.interp ρ (signedDigitIndicators value)
    ⦃⇓ digit => ⌜SignedDigitSpec ρ value digit⌝⦄ := by
  mvcgen [signedDigitIndicators, SignedDigitSpec, IndicatorsSpec]
  case vc1.hd0 =>
    have h16 : LC.eval ρ.int (16 : LC ℤ) = 16 := LC.eval_natCast ρ.int 16
    rw [LC.eval_add, h16]
    omega
  case vc2.hdlt =>
    have h16 : LC.eval ρ.int (16 : LC ℤ) = 16 := LC.eval_natCast ρ.int 16
    rw [LC.eval_add, h16]
    omega
  case vc3.success =>
    exact signedDigitSpec_of_indicators ‹IndicatorsSpec ρ (value + 16) _›

theorem boothDigit_bounds {k : P256.Fn} (hk : k.val.Valid ρ)
    (i : Nat) (hi : i < 52) :
    -16 ≤ (boothDigit k i hi).eval ρ.int ∧
      (boothDigit k i hi).eval ρ.int ≤ 16 := by
  unfold boothDigit
  split
  · rename_i hlt
    have hlow := windowValue_eval hk (5 * i) 4 (by omega)
    have hlow0 : 0 ≤ (windowValue k (5 * i) 4 (by omega)).eval ρ.int := by
      rw [hlow]
      exact_mod_cast Nat.zero_le _
    have hlow16 : (windowValue k (5 * i) 4 (by omega)).eval ρ.int < 16 := by
      rw [hlow]
      exact_mod_cast (BitVec.extractLsb' (5 * i) 4 (k.val.eval ρ)).isLt
    have htop := windowValue_eval hk (5 * i + 4) 1 (by omega)
    have htop0 : 0 ≤ (windowValue k (5 * i + 4) 1 (by omega)).eval ρ.int := by
      rw [htop]
      exact_mod_cast Nat.zero_le _
    have htop2 : (windowValue k (5 * i + 4) 1 (by omega)).eval ρ.int < 2 := by
      rw [htop]
      exact_mod_cast (BitVec.extractLsb' (5 * i + 4) 1 (k.val.eval ρ)).isLt
    by_cases hzero : i = 0
    · simp only [if_pos hzero, LC.eval_sub, LC.eval_add, LC.eval_zero,
        LC.eval_nsmul, nsmul_eq_mul, add_zero]
      omega
    · have hp := windowValue_eval hk (5 * i - 1) 1 (by omega)
      have hp0 : 0 ≤ (windowValue k (5 * i - 1) 1 (by omega)).eval ρ.int := by
        rw [hp]
        exact_mod_cast Nat.zero_le _
      have hp2 : (windowValue k (5 * i - 1) 1 (by omega)).eval ρ.int < 2 := by
        rw [hp]
        exact_mod_cast (BitVec.extractLsb' (5 * i - 1) 1 (k.val.eval ρ)).isLt
      simp only [if_neg hzero, LC.eval_sub, LC.eval_add, LC.eval_nsmul,
        nsmul_eq_mul]
      omega
  · have h254 := windowValue_eval hk 254 1 (by omega)
    have h255 := windowValue_eval hk 255 1 (by omega)
    have h2540 : 0 ≤ (windowValue k 254 1 (by omega)).eval ρ.int := by
      rw [h254]
      exact_mod_cast Nat.zero_le _
    have h2542 : (windowValue k 254 1 (by omega)).eval ρ.int < 2 := by
      rw [h254]
      exact_mod_cast (BitVec.extractLsb' 254 1 (k.val.eval ρ)).isLt
    have h2550 : 0 ≤ (windowValue k 255 1 (by omega)).eval ρ.int := by
      rw [h255]
      exact_mod_cast Nat.zero_le _
    have h2552 : (windowValue k 255 1 (by omega)).eval ρ.int < 2 := by
      rw [h255]
      exact_mod_cast (BitVec.extractLsb' 255 1 (k.val.eval ρ)).isLt
    simp only [LC.eval_add]
    omega

end Freigen.F2Z.Examples.EcdsaP256
