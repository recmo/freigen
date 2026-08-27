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

theorem SignedDigitSpec.bounds (h : SignedDigitSpec ρ value digit) :
    -16 ≤ value.eval ρ.int ∧ value.eval ρ.int ≤ 16 := by
  rcases h.2 with ⟨chosen, _, hvalue, _⟩
  have hchosen : chosen.val < 33 := chosen.isLt
  omega

theorem SignedDigitSpec.magnitude_nonneg
    (h : SignedDigitSpec ρ value digit) :
    0 ≤ digit.magnitude.eval ρ.int := by
  rw [h.magnitude_eval]
  exact_mod_cast Nat.zero_le _

private theorem natAbs_cast_eq_neg_of_nonpos {x : Int} (hx : x ≤ 0) :
    (x.natAbs : Int) = -x := by
  have h := Int.natAbs_of_nonneg (a := -x) (by omega)
  simpa only [Int.natAbs_neg] using h

theorem SignedDigitSpec.magnitude_le_sixteen
    (h : SignedDigitSpec ρ value digit) :
    digit.magnitude.eval ρ.int ≤ 16 := by
  rw [h.magnitude_eval]
  rcases h.bounds with ⟨hlow, hhigh⟩
  by_cases hnonneg : 0 ≤ value.eval ρ.int
  · rw [Int.natAbs_of_nonneg hnonneg]
    exact_mod_cast hhigh
  · have hnonpos : value.eval ρ.int ≤ 0 := le_of_lt (lt_of_not_ge hnonneg)
    rw [natAbs_cast_eq_neg_of_nonpos hnonpos]
    omega

theorem SignedDigitSpec.isSixteen_eq_one_iff
    (h : SignedDigitSpec ρ value digit) :
    digit.isSixteen.eval ρ.int = 1 ↔
      digit.magnitude.eval ρ.int = 16 := by
  rw [h.isSixteen_eval, h.magnitude_eval]
  rcases h.bounds with ⟨hlow, hhigh⟩
  by_cases hsixteen : value.eval ρ.int = -16 ∨ value.eval ρ.int = 16
  · simp only [if_pos hsixteen, true_iff]
    rcases hsixteen with hneg | hpos
    · rw [hneg]
      decide
    · rw [hpos]
      decide
  · simp only [if_neg hsixteen, false_iff, ne_eq]
    by_cases hnonneg : 0 ≤ value.eval ρ.int
    · rw [Int.natAbs_of_nonneg hnonneg]
      omega
    · have hnonpos : value.eval ρ.int ≤ 0 := le_of_lt (lt_of_not_ge hnonneg)
      rw [natAbs_cast_eq_neg_of_nonpos hnonpos]
      omega

theorem SignedDigitSpec.isSixteen_bit
    (h : SignedDigitSpec ρ value digit) :
    digit.isSixteen.eval ρ.int = 0 ∨ digit.isSixteen.eval ρ.int = 1 := by
  rw [h.isSixteen_eval]
  split <;> simp

theorem SignedDigitSpec.lowMagnitude_bounds
    (h : SignedDigitSpec ρ value digit) :
    let lowMagnitude := digit.magnitude - 16 • digit.isSixteen
    0 ≤ lowMagnitude.eval ρ.int ∧ lowMagnitude.eval ρ.int < 16 := by
  dsimp
  simp only [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul]
  have hm0 := h.magnitude_nonneg
  have hm16 := h.magnitude_le_sixteen
  have hs := h.isSixteen_eval
  by_cases hsixteen : value.eval ρ.int = -16 ∨ value.eval ρ.int = 16
  · rw [if_pos hsixteen] at hs
    have hm : digit.magnitude.eval ρ.int = 16 :=
      h.isSixteen_eq_one_iff.mp hs
    omega
  · rw [if_neg hsixteen] at hs
    have hmne : digit.magnitude.eval ρ.int ≠ 16 := by
      intro hm
      have hsone : digit.isSixteen.eval ρ.int = 1 :=
        h.isSixteen_eq_one_iff.mpr hm
      omega
    omega

def Radix32MagnitudeSpec (ρ : WF.Valuation) (value : LC ℤ)
    (out : P256.AffineSlope.Point) (q : P256.Reference.Point) : Prop :=
  P256.Reference.NormalizedRep ρ out ((value.eval ρ.int).natAbs • q)

private theorem normalizedRep_of_coordinate_eq
    {source out : P256.AffineSlope.Point} {q : P256.Reference.Point}
    (hsource : P256.Reference.NormalizedRep ρ source q)
    (hinfinity : out.infinity.eval ρ.int = source.infinity.eval ρ.int)
    (hX : Modular.Lazy.evalZMod P256.base out.X ρ =
      Modular.Lazy.evalZMod P256.base source.X ρ)
    (hY : Modular.Lazy.evalZMod P256.base out.Y ρ =
      Modular.Lazy.evalZMod P256.base source.Y ρ) :
    P256.Reference.NormalizedRep ρ out q := by
  rcases hsource with ⟨⟨hbit, hcoordinates⟩, hnormalized⟩
  constructor
  · constructor
    · simpa [hinfinity] using hbit
    · unfold P256.Reference.circuitCoordinates at hcoordinates ⊢
      rw [hinfinity, hX, hY]
      exact hcoordinates
  · intro hq
    rcases hnormalized hq with ⟨hx, hy⟩
    exact ⟨hX.trans hx, hY.trans hy⟩

private theorem nsmul_ne_zero_of_prime_order {q : P256.Reference.Point}
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0)
    {k : Nat} (hk0 : k ≠ 0) (hk : k < P256.scalarModulus) :
    k • q ≠ 0 := by
  intro hzero
  have hdvd : P256.scalarModulus ∣ k := by
    rw [← Reference.Aux.addOrderOf_eq_scalarModulus hq horder,
      addOrderOf_dvd_iff_nsmul_eq_zero]
    exact hzero
  exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hk) hdvd

private theorem radix32MagnitudeSpec_of_select
    {value : LC ℤ} {q : P256.Reference.Point}
    (hdigit : SignedDigitSpec ρ value digit)
    (htable : Radix32TableSpec ρ table q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0)
    {low : P256.AffineSlope.Point} {X Y : P256.AffineSlope.Rep}
    (hlowExists : ∃ i : Fin 16,
      (digit.magnitude - 16 • digit.isSixteen).eval ρ.int = i.val ∧
      P256.Reference.NormalizedRep ρ low (i.val • q))
    (hX : P256.AffineSlope.SelectZModSpec ρ digit.isSixteen
      table.p16.X low.X X)
    (hY : P256.AffineSlope.SelectZModSpec ρ digit.isSixteen
      table.p16.Y low.Y Y) :
    Radix32MagnitudeSpec ρ value
      ⟨X, Y, low.infinity - digit.isSixteen⟩ q := by
  rcases hlowExists with ⟨i, hilow, hlow⟩
  have hs := hdigit.isSixteen_eval
  by_cases hsixteen : value.eval ρ.int = -16 ∨ value.eval ρ.int = 16
  · rw [if_pos hsixteen] at hs
    have hm : digit.magnitude.eval ρ.int = 16 :=
      hdigit.isSixteen_eq_one_iff.mp hs
    have hi0 : i.val = 0 := by
      simp only [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul, hs, hm] at hilow
      omega
    have hieq : i = 0 := Fin.eq_of_val_eq hi0
    subst i
    have hlowInfinity : low.infinity.eval ρ.int = 1 := by
      exact P256.Reference.Aux.represents_zero hlow.1
    unfold Radix32MagnitudeSpec
    have habs : (value.eval ρ.int).natAbs = 16 := by
      rcases hsixteen with hneg | hpos
      · rw [hneg]
        decide
      · rw [hpos]
        decide
    rw [habs]
    have hp16Nonzero : 16 • q ≠ 0 :=
      nsmul_ne_zero_of_prime_order hq horder (by omega) (by native_decide)
    have hp16Infinity : table.p16.infinity.eval ρ.int = 0 := by
      rcases hp : (16 • q) with _ | ⟨px, py, hpCurve⟩
      · exact (hp16Nonzero hp).elim
      · exact (P256.Reference.Aux.represents_some (hp ▸ htable.2.1)).1
    apply normalizedRep_of_coordinate_eq htable.2
    · simp only [LC.eval_sub, hs]
      omega
    · exact hX.1 hs
    · exact hY.1 hs
  · rw [if_neg hsixteen] at hs
    have hiAbs : i.val = (value.eval ρ.int).natAbs := by
      simp only [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul, hs,
        hdigit.magnitude_eval] at hilow
      omega
    have hlow' : P256.Reference.NormalizedRep ρ low
        ((value.eval ρ.int).natAbs • q) := by
      simpa [hiAbs] using hlow
    apply normalizedRep_of_coordinate_eq hlow'
    · simp only [LC.eval_sub, hs]
      omega
    · exact hX.2 hs
    · exact hY.2 hs

@[spec] theorem selectRadix32Magnitude_sound
    {value : LC ℤ} {q : P256.Reference.Point}
    (hdigit : SignedDigitSpec ρ value digit)
    (htable : Radix32TableSpec ρ table q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Sound.interp ρ (selectRadix32Magnitude digit table)
    ⦃⇓ out => ⌜Radix32MagnitudeSpec ρ value out q⌝⦄ := by
  mvcgen [selectRadix32Magnitude, Radix32MagnitudeSpec]
  case vc2.htable => exact htable.1
  case vc3.success =>
    rename_i low hlow X hX Y hY
    rcases hlow with ⟨i, hilow, hlow⟩
    have hs := hdigit.isSixteen_eval
    by_cases hsixteen : value.eval ρ.int = -16 ∨ value.eval ρ.int = 16
    · rw [if_pos hsixteen] at hs
      have hm : digit.magnitude.eval ρ.int = 16 :=
        hdigit.isSixteen_eq_one_iff.mp hs
      have hi0 : i.val = 0 := by
        simp only [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul, hs, hm] at hilow
        omega
      have hieq : i = 0 := Fin.eq_of_val_eq hi0
      subst i
      have hlowInfinity : low.infinity.eval ρ.int = 1 := by
        rcases hlow.1.1 with hinf | hinf
        · have hc := hlow.1.2
          simp [P256.Reference.circuitCoordinates, hinf,
            P256.Reference.coordinates] at hc
        · exact hinf
      unfold Radix32MagnitudeSpec
      have habs : (value.eval ρ.int).natAbs = 16 := by
        rcases hsixteen with hneg | hpos
        · rw [hneg]
          decide
        · rw [hpos]
          decide
      rw [habs]
      have hp16Nonzero : 16 • q ≠ 0 :=
        nsmul_ne_zero_of_prime_order hq horder (by omega) (by native_decide)
      have hp16Infinity : table.p16.infinity.eval ρ.int = 0 := by
        rcases hp : (16 • q) with _ | ⟨px, py, hpCurve⟩
        · exact (hp16Nonzero hp).elim
        · exact (P256.Reference.Aux.represents_some (hp ▸ htable.2.1)).1
      apply normalizedRep_of_coordinate_eq htable.2
      · simp only [LC.eval_sub, hs]
        omega
      · exact hX.1 hs
      · exact hY.1 hs
    · rw [if_neg hsixteen] at hs
      have hiAbs : i.val = (value.eval ρ.int).natAbs := by
        simp only [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul, hs,
          hdigit.magnitude_eval] at hilow
        omega
      have hlow' : P256.Reference.NormalizedRep ρ low
          ((value.eval ρ.int).natAbs • q) := by
        simpa [hiAbs] using hlow
      apply normalizedRep_of_coordinate_eq hlow'
      · simp only [LC.eval_sub, hs]
        omega
      · exact hX.2 hs
      · exact hY.2 hs

@[spec] theorem selectRadix32Magnitude_complete
    {value : LC ℤ} {q : P256.Reference.Point}
    (hdigit : SignedDigitSpec ρ value digit)
    (htableValid : Radix32TableValid ρ table)
    (htable : Radix32TableSpec ρ table q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (selectRadix32Magnitude digit table)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Radix32MagnitudeSpec ρ value out q⌝⦄ := by
  mvcgen [selectRadix32Magnitude, Radix32MagnitudeSpec,
    Radix32TableValid]
  case vc2.hd0 => exact hdigit.lowMagnitude_bounds.1
  case vc3.hdlt => exact hdigit.lowMagnitude_bounds.2
  case vc4.htableValid => exact htableValid.1
  case vc5.htable => exact htable.1
  case vc6.hchoose => exact hdigit.isSixteen_bit
  case vc7.hone => exact htableValid.2.2.1
  case vc8.honeCanonical => exact htableValid.2.2.2.1
  case vc9.hzero low hlow => exact hlow.1.2.1
  case vc10.hzeroCanonical low hlow => exact hlow.1.2.2.1
  case vc11.hchoose => exact hdigit.isSixteen_bit
  case vc12.hone => exact htableValid.2.2.2.2.2.1
  case vc13.honeCanonical => exact htableValid.2.2.2.2.2.2.1
  case vc14.hzero =>
    rename_i low hlow X hX
    exact hlow.1.2.2.2.2.1
  case vc15.hzeroCanonical =>
    rename_i low hlow X hX
    exact hlow.1.2.2.2.2.2.1
  case vc16.success =>
    rename_i low hlow X hX Y hY
    have hspec : Radix32MagnitudeSpec ρ value
        ⟨X, Y, low.infinity - digit.isSixteen⟩ q :=
      radix32MagnitudeSpec_of_select hdigit htable hq horder
        hlow.2 hX.1 hY.1
    exact ⟨⟨hX.2.2.2, hX.2.1, hX.2.2.1,
      hY.2.2.2, hY.2.1, hY.2.2.1, hspec.1.1⟩, hspec⟩

def ApplyPointSignSpec (ρ : WF.Valuation) (negative : LC ℤ)
    (out : P256.AffineSlope.Point) (q : P256.Reference.Point) : Prop :=
  P256.Reference.NormalizedRep ρ out
    (if negative.eval ρ.int = 1 then -q else q)

private theorem normalizedRep_neg_of_coordinate_eq
    {source out : P256.AffineSlope.Point} {q : P256.Reference.Point}
    (hsource : P256.Reference.NormalizedRep ρ source q)
    (hinfinity : out.infinity.eval ρ.int = source.infinity.eval ρ.int)
    (hX : Modular.Lazy.evalZMod P256.base out.X ρ =
      Modular.Lazy.evalZMod P256.base source.X ρ)
    (hY : Modular.Lazy.evalZMod P256.base out.Y ρ =
      -Modular.Lazy.evalZMod P256.base source.Y ρ) :
    P256.Reference.NormalizedRep ρ out (-q) := by
  rcases q with _ | ⟨qx, qy, hcurve⟩
  · change P256.Reference.NormalizedRep ρ out 0
    have hsourceY : Modular.Lazy.evalZMod P256.base source.Y ρ = 0 :=
      (hsource.2 rfl).2
    apply normalizedRep_of_coordinate_eq hsource hinfinity hX
    rw [hY, hsourceY]
    simp
  · obtain ⟨hsourceInfinity, hsourceX, hsourceY⟩ :=
      P256.Reference.Aux.represents_some hsource.1
    constructor
    · constructor
      · exact Or.inl (hinfinity.trans hsourceInfinity)
      · unfold P256.Reference.circuitCoordinates
        rw [if_neg (by rw [hinfinity, hsourceInfinity]; omega)]
        simp only [P256.Reference.coordinates,
          WeierstrassCurve.Affine.Point.neg_some]
        apply congrArg₂ P256.Reference.Coordinates.finite
        · exact hX.trans hsourceX
        · rw [hY, hsourceY]
          exact P256.Reference.negY_eq qx qy |>.symm
    · intro hzero
      simp at hzero

private theorem normalizedRep_y_pos_of_nonzero_order
    {P : P256.AffineSlope.Point} {q : P256.Reference.Point}
    (hPvalid : P.Valid ρ) (hP : P256.Reference.NormalizedRep ρ P q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0) :
    0 < P.Y.intVal.eval ρ.int := by
  have htwo : q + q ≠ 0 :=
    (Reference.Aux.no_two_torsion_of_order horder).resolve_left hq
  rcases q with _ | ⟨qx, qy, hcurve⟩
  · exact (hq rfl).elim
  · obtain ⟨_, _, hPyeq⟩ := P256.Reference.Aux.represents_some hP.1
    have hyneg : qy ≠ P256.Reference.curve.toAffine.negY qx qy := by
      intro hy
      exact htwo (WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy)
    have hrawne : P.Y.intVal.eval ρ.int ≠ 0 := by
      intro hzero
      apply hyneg
      rw [P256.Reference.negY_eq, ← hPyeq]
      change (Int.castRingHom (ZMod P256.base.modulus))
          (P.Y.intVal.eval ρ.int) =
        -(Int.castRingHom (ZMod P256.base.modulus))
          (P.Y.intVal.eval ρ.int)
      rw [hzero]
      simp
    exact lt_of_le_of_ne hPvalid.2.2.2.2.1.1 hrawne.symm

@[spec] theorem applyPointSign_sound
    (hnegative : negative.eval ρ.int = 0 ∨ negative.eval ρ.int = 1)
    (hP : P256.Reference.NormalizedRep ρ P q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (applyPointSign negative P)
    ⦃⇓ out => ⌜ApplyPointSignSpec ρ negative out q⌝⦄ := by
  mvcgen [applyPointSign, ApplyPointSignSpec]
  intro bits
  mvcgen
  case vc1.vc1.success =>
    rename_i outY _ hassert
    rcases hnegative with hnegative | hnegative
    · unfold ApplyPointSignSpec
      rw [if_neg (by omega)]
      apply normalizedRep_of_coordinate_eq
        (out := ⟨P.X, ⟨outY.intVal, 2⟩, P.infinity⟩) hP rfl rfl
      have houtYInt : outY.intVal.eval ρ.int = P.Y.intVal.eval ρ.int := by
        simp only [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul,
          LC.eval_ofConst, hnegative, zero_mul] at hassert
        omega
      change (Int.castRingHom (ZMod P256.base.modulus))
          (outY.intVal.eval ρ.int) =
        (Int.castRingHom (ZMod P256.base.modulus))
          (P.Y.intVal.eval ρ.int)
      rw [houtYInt]
    · unfold ApplyPointSignSpec
      rw [if_pos hnegative]
      apply normalizedRep_neg_of_coordinate_eq
        (out := ⟨P.X, ⟨outY.intVal, 2⟩, P.infinity⟩) hP rfl rfl
      have houtYInt : outY.intVal.eval ρ.int =
          (P256.base.modulus : Int) - P.Y.intVal.eval ρ.int := by
        simp only [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul,
          LC.eval_ofConst, hnegative, one_mul] at hassert
        omega
      change (Int.castRingHom (ZMod P256.base.modulus))
          (outY.intVal.eval ρ.int) =
        -(Int.castRingHom (ZMod P256.base.modulus))
          (P.Y.intVal.eval ρ.int)
      rw [houtYInt]
      norm_num

@[spec] theorem applyPointSign_complete
    (hnegative : negative.eval ρ.int = 0 ∨ negative.eval ρ.int = 1)
    (hPvalid : P.Valid ρ)
    (hP : P256.Reference.NormalizedRep ρ P q)
    (hnegativeNonzero : negative.eval ρ.int = 1 → q ≠ 0)
    (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (applyPointSign negative P)
    ⦃⇓ out => ⌜out.Valid ρ ∧ ApplyPointSignSpec ρ negative out q⌝⦄ := by
  mvcgen [applyPointSign, ApplyPointSignSpec]
  let value := if negative.eval ρ.int = 1 then
    (P256.base.modulus : Int) - P.Y.intVal.eval ρ.int
    else P.Y.intVal.eval ρ.int
  have hvalue0 : 0 ≤ value := by
    rcases hnegative with hzero | hone
    · simp [value, hzero, hPvalid.2.2.2.2.1.1]
    · have hylt := hPvalid.2.2.2.2.2.1
      simp [value, hone]
      omega
  have hvalueLt : value < P256.base.modulus := by
    rcases hnegative with hzero | hone
    · simpa [value, hzero] using hPvalid.2.2.2.2.2.1
    · have hypos := normalizedRep_y_pos_of_nonzero_order hPvalid hP
          (hnegativeNonzero hone) horder
      simp [value, hone]
      omega
  let bits : Vector Bool 256 :=
    Vector.ofFn fun i => value.toNat.testBit i.val
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, bits, value, hvalue0]
  · mvcgen
    rename_i outY houtY
    have hfit : value.toNat < 2 ^ 256 := by
      apply (Int.toNat_lt hvalue0).2
      exact hvalueLt.trans (by native_decide)
    have hword :
        (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits }).toNat =
          value.toNat := by
      rw [show Vector.map LC.ofConst bits =
          Vector.ofFn (n := 256) fun i =>
            LC.ofConst (value.toNat.testBit i.val) by
        ext i
        simp [bits]]
      exact Modular.Aux.constWord_eval_toNat value.toNat hfit ρ
    have houtVal : outY.intVal.eval ρ.int = value := by
      rw [U.Rel.intVal houtY, hword, Int.toNat_of_nonneg hvalue0]
    constructor
    · rcases hnegative with hzero | hone
      · simp [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul,
          LC.eval_ofConst, hzero, value, houtVal]
      · simp [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul,
          LC.eval_ofConst, hone, value, houtVal]
        ring
    · mvcgen
      constructor
      · refine ⟨hPvalid.1, hPvalid.2.1, hPvalid.2.2.1, rfl,
          ⟨U.intVal_nonneg outY houtY.1, ?_⟩, ?_,
          hPvalid.2.2.2.2.2.2⟩
        · rw [houtVal]
          change value < (2 : Int) * P256.base.modulus
          have hp : 0 < P256.base.modulus := by native_decide
          omega
        · simpa [houtVal] using hvalueLt
      · rcases hnegative with hzero | hone
        · unfold ApplyPointSignSpec
          rw [if_neg (by omega)]
          apply normalizedRep_of_coordinate_eq
            (out := ⟨P.X, ⟨outY.intVal, 2⟩, P.infinity⟩) hP rfl rfl
          change (Int.castRingHom (ZMod P256.base.modulus))
              (outY.intVal.eval ρ.int) =
            (Int.castRingHom (ZMod P256.base.modulus))
              (P.Y.intVal.eval ρ.int)
          rw [houtVal]
          simp [value, hzero]
        · unfold ApplyPointSignSpec
          rw [if_pos hone]
          apply normalizedRep_neg_of_coordinate_eq
            (out := ⟨P.X, ⟨outY.intVal, 2⟩, P.infinity⟩) hP rfl rfl
          change (Int.castRingHom (ZMod P256.base.modulus))
              (outY.intVal.eval ρ.int) =
            -(Int.castRingHom (ZMod P256.base.modulus))
              (P.Y.intVal.eval ρ.int)
          rw [houtVal]
          simp [value, hone]

def SignedRadix32PointSpec (ρ : WF.Valuation) (value : LC ℤ)
    (out : P256.AffineSlope.Point) (q : P256.Reference.Point) : Prop :=
  P256.Reference.NormalizedRep ρ out
    (if value.eval ρ.int < 0 then
      -((value.eval ρ.int).natAbs • q)
    else (value.eval ρ.int).natAbs • q)

private theorem signedPoint_eq_zsmul (x : Int)
    (q : P256.Reference.Point) :
    (if x < 0 then -(x.natAbs • q) else x.natAbs • q) = x • q := by
  cases x with
  | ofNat n => simp
  | negSucc n => simp

theorem SignedRadix32PointSpec.zsmul
    (h : SignedRadix32PointSpec ρ value out q) :
    P256.Reference.NormalizedRep ρ out (value.eval ρ.int • q) := by
  unfold SignedRadix32PointSpec at h
  rw [signedPoint_eq_zsmul] at h
  exact h

@[spec] theorem selectSignedRadix32Point_sound
    {value : LC ℤ} {q : P256.Reference.Point}
    (hdigit : SignedDigitSpec ρ value digit)
    (htable : Radix32TableSpec ρ table q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Sound.interp ρ (selectSignedRadix32Point digit table)
    ⦃⇓ out => ⌜SignedRadix32PointSpec ρ value out q⌝⦄ := by
  mvcgen [selectSignedRadix32Point, SignedRadix32PointSpec]
  case vc7.success.success =>
    intro hout
    simpa [ApplyPointSignSpec, SignedRadix32PointSpec,
      hdigit.negative_eval] using hout
  case vc9 =>
    intro _
    rw [hdigit.negative_eval]
    split <;> simp
  case vc10 =>
    intro h
    exact h

@[spec] theorem selectSignedRadix32Point_complete
    {value : LC ℤ} {q : P256.Reference.Point}
    (hdigit : SignedDigitSpec ρ value digit)
    (htableValid : Radix32TableValid ρ table)
    (htable : Radix32TableSpec ρ table q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (selectSignedRadix32Point digit table)
    ⦃⇓ out => ⌜out.Valid ρ ∧ SignedRadix32PointSpec ρ value out q⌝⦄ := by
  mvcgen [selectSignedRadix32Point, SignedRadix32PointSpec]
  case vc8.success.success =>
    intro houtValid hout
    exact ⟨houtValid, by simpa [ApplyPointSignSpec,
      SignedRadix32PointSpec, hdigit.negative_eval] using hout⟩
  case vc10 =>
    intros
    rw [hdigit.negative_eval]
    split <;> simp
  case vc11 =>
    intro hvalid _
    exact hvalid
  case vc12 =>
    intro h
    exact h.2
  case vc13 =>
    intro h hnegative
    have hvalueNeg : value.eval ρ.int < 0 := by
      rw [hdigit.negative_eval] at hnegative
      split at hnegative <;> omega
    apply nsmul_ne_zero_of_prime_order hq horder
    · exact Int.natAbs_ne_zero.mpr (by omega)
    · have hm := hdigit.magnitude_le_sixteen
      rw [hdigit.magnitude_eval] at hm
      exact lt_of_le_of_lt (by exact_mod_cast hm) (by native_decide)
  case vc14 =>
    intro _
    exact Reference.Aux.order_nsmul horder _

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

def radix32ChunkValue (rho : WF.Valuation) (k : P256.Fn)
    (i : Nat) : Nat :=
  (BitVec.extractLsb' (5 * i) 5 (k.val.eval rho)).toNat

def boothTopBitValue (rho : WF.Valuation) (k : P256.Fn)
    (i : Nat) : Nat :=
  (BitVec.extractLsb' (5 * i + 4) 1 (k.val.eval rho)).toNat

theorem radix32ChunkValue_split {k : P256.Fn} {i : Nat} :
    radix32ChunkValue ρ k i =
      (BitVec.extractLsb' (5 * i) 4 (k.val.eval ρ)).toNat +
        16 * boothTopBitValue ρ k i := by
  unfold radix32ChunkValue boothTopBitValue
  simp only [BitVec.extractLsb'_toNat, Nat.reducePow]
  rw [show 5 * i + 4 = 5 * i + 4 by omega, Nat.shiftRight_add]
  omega

theorem boothDigit_eval_regular {k : P256.Fn} (hk : k.val.Valid ρ)
    (i : Nat) (hi : i < 51) :
    (boothDigit k i (by omega)).eval ρ.int =
      (radix32ChunkValue ρ k i : Int) +
        (if i = 0 then 0 else (boothTopBitValue ρ k (i - 1) : Int)) -
        32 * (boothTopBitValue ρ k i : Int) := by
  unfold boothDigit
  simp only [dif_pos hi, LC.eval_sub, LC.eval_add, LC.eval_nsmul,
    nsmul_eq_mul]
  rw [windowValue_eval hk, windowValue_eval hk]
  have hsplit := radix32ChunkValue_split (ρ := ρ) (k := k) (i := i)
  have htop :
      ((BitVec.extractLsb' (5 * i + 4) 1
        (k.val.eval ρ)).toNat : Int) = boothTopBitValue ρ k i := rfl
  rw [htop]
  by_cases hzero : i = 0
  · simp [hzero] at hsplit ⊢
    omega
  · simp only [if_neg hzero]
    rw [windowValue_eval hk]
    have hstart : 5 * i - 1 = 5 * (i - 1) + 4 := by omega
    rw [hstart]
    change ((BitVec.extractLsb' (5 * i) 4
        (k.val.eval ρ)).toNat : Int) +
        (boothTopBitValue ρ k (i - 1) : Int) -
        16 * (boothTopBitValue ρ k i : Int) = _
    omega

def radix32Prefix (rho : WF.Valuation) (k : P256.Fn)
    (count : Nat) : Nat :=
  (k.val.eval rho).toNat / 2 ^ (255 - 5 * count)

theorem radix32Prefix_succ {k : P256.Fn} {count : Nat}
    (hcount : count < 51) :
    radix32Prefix ρ k (count + 1) =
      32 * radix32Prefix ρ k count +
        radix32ChunkValue ρ k (50 - count) := by
  unfold radix32Prefix radix32ChunkValue
  simp only [BitVec.extractLsb'_toNat, Nat.reducePow]
  rw [show 255 - 5 * count = (250 - 5 * count) + 5 by omega,
    show 255 - 5 * (count + 1) = 250 - 5 * count by omega,
    show 5 * (50 - count) = 250 - 5 * count by omega,
    Nat.shiftRight_eq_div_pow, pow_add]
  norm_num
  rw [← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod _ 32).symm

theorem boothDigit_eval_top {k : P256.Fn} (hk : k.val.Valid ρ) :
    (boothDigit k 51 (by omega)).eval ρ.int =
      (radix32Prefix ρ k 0 : Int) +
        (boothTopBitValue ρ k 50 : Int) := by
  unfold boothDigit radix32Prefix boothTopBitValue
  rw [dif_neg (by omega)]
  simp only [LC.eval_add]
  rw [windowValue_eval hk, windowValue_eval hk]
  simp only [BitVec.extractLsb'_toNat, Nat.reducePow]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  norm_num
  have hklt := (k.val.eval ρ).isLt
  omega

theorem boothDigit_prefix_succ {k : P256.Fn} (hk : k.val.Valid ρ)
    {count : Nat} (hcount : count < 51) :
    32 * ((radix32Prefix ρ k count : Int) +
      boothTopBitValue ρ k (50 - count)) +
        (boothDigit k (50 - count) (by omega)).eval ρ.int =
      (radix32Prefix ρ k (count + 1) : Int) +
        (if count + 1 = 51 then 0
          else boothTopBitValue ρ k (50 - (count + 1))) := by
  rw [boothDigit_eval_regular hk (50 - count) (by omega),
    radix32Prefix_succ hcount]
  by_cases hlast : count + 1 = 51
  · rw [if_pos hlast]
    have hi : 50 - count = 0 := by omega
    simp [hi]
    push_cast
    ring
  · rw [if_neg hlast]
    have hi : 50 - count ≠ 0 := by omega
    rw [if_neg hi]
    have hindex : 50 - count - 1 = 50 - (count + 1) := by omega
    rw [hindex]
    push_cast
    ring

def boothHorner (rho : WF.Valuation) (k : P256.Fn) : Nat → Int
  | 0 => (boothDigit k 51 (by omega)).eval rho.int
  | count + 1 =>
      32 * boothHorner rho k count +
        if hcount : count < 51 then
          (boothDigit k (50 - count) (by omega)).eval rho.int
        else 0

theorem boothHorner_eq_prefix {k : P256.Fn} (hk : k.val.Valid ρ)
    {count : Nat} (hcount : count ≤ 51) :
    boothHorner ρ k count =
      (radix32Prefix ρ k count : Int) +
        (if count = 51 then 0
          else boothTopBitValue ρ k (50 - count)) := by
  induction count with
  | zero =>
      simp [boothHorner, boothDigit_eval_top hk]
  | succ count ih =>
      have hcountLt : count < 51 := by omega
      rw [boothHorner, dif_pos hcountLt, ih (by omega),
        if_neg (by omega : count ≠ 51),
        boothDigit_prefix_succ hk hcountLt]

theorem boothHorner_full {k : P256.Fn} (hk : k.val.Valid ρ) :
    boothHorner ρ k 51 = ((k.val.eval ρ).toNat : Int) := by
  rw [boothHorner_eq_prefix hk (by omega)]
  simp [radix32Prefix]

def SignedRadix32StepPoint (rho : WF.Valuation) (u1 u2 : P256.Fn)
    (q : P256.Reference.Point) (i : Nat)
    (acc : P256.Reference.Point) : P256.Reference.Point :=
  let exponent := 254 - i
  let doubled := 2 • acc
  let withQ := if hq : exponent % 5 = 0 then
    doubled + (boothDigit u2 (exponent / 5) (by omega)).eval rho.int • q
  else doubled
  if exponent % 8 = 0 then
    withQ + (BitVec.extractLsb' exponent 8 (u1.val.eval rho)).toNat •
      P256.Reference.generator
  else withQ

private theorem generatorWindowRep_of_lookup {u : P256.Fn}
    (hu : u.val.Valid ρ) {start : Nat} {hfit : start + 8 ≤ 256}
    {out : P256.AffineSlope.Point}
    (h : ∃ j : Fin 256,
      (windowValue u start 8 hfit).eval ρ.int = j.val ∧
        P256.Reference.NormalizedRep ρ out
          (j.val • P256.Reference.generator)) :
    P256.Reference.NormalizedRep ρ out
      ((BitVec.extractLsb' start 8 (u.val.eval ρ)).toNat •
        P256.Reference.generator) := by
  rcases h with ⟨j, hj, hout⟩
  have hw := windowValue_eval hu start 8 hfit
  rw [hw] at hj
  have hjval : j.val =
      (BitVec.extractLsb' start 8 (u.val.eval ρ)).toNat := by
    exact_mod_cast hj.symm
  simpa [hjval] using hout

@[spec] theorem signedRadix32Step_sound
    {u1 u2 : P256.Fn} {q : P256.Reference.Point}
    {i : Nat} {hi : i < 255} {acc : P256.AffineSlope.Point}
    {accPoint : P256.Reference.Point}
    (hu1 : u1.val.Valid ρ) (hu2 : u2.val.Valid ρ)
    (hacc : P256.Reference.NormalizedRep ρ acc accPoint)
    (htable : Radix32TableSpec ρ qTable q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Sound.interp ρ (signedRadix32Step u1 u2 qTable i hi acc)
    ⦃⇓ out => ⌜P256.Reference.NormalizedRep ρ out
      (SignedRadix32StepPoint ρ u1 u2 q i accPoint)⌝⦄ := by
  mvcgen [signedRadix32Step, SignedRadix32StepPoint]
  case vc3.success =>
    intro hdouble
    split <;> mvcgen -trivial
    case vc1.value =>
      exact boothDigit u2 ((254 - i) / 5) (by omega)
    case vc2.q => exact q
    case vc3.hdigit => assumption
    case vc4.htable => exact htable
    case vc5.hq => exact hq
    case vc6.horder => exact horder
    case vc7.p => exact accPoint + accPoint
    case vc8.q =>
      exact (boothDigit u2 ((254 - i) / 5) (by omega)).eval ρ.int • q
    case vc9.hP => exact hdouble
    case vc10.hQ => exact SignedRadix32PointSpec.zsmul (by assumption)
    case vc11.success =>
      intro hwithQ
      split <;> mvcgen -trivial
      case vc2 =>
        intro _
        exact accPoint + accPoint +
          (boothDigit u2 ((254 - i) / 5) (by omega)).eval ρ.int • q
      case vc3 =>
        intro _
        exact (BitVec.extractLsb' (254 - i) 8
          (u1.val.eval ρ)).toNat • P256.Reference.generator
      case vc4 =>
        intro _
        exact hwithQ
      case vc5 =>
        intro hlookup
        exact generatorWindowRep_of_lookup hu1 hlookup
      case vc1.h.success.success =>
        intro hout
        unfold SignedRadix32StepPoint
        simp_all [two_nsmul]
      case vc1.isFalse =>
        unfold SignedRadix32StepPoint
        simp_all [two_nsmul]
    case vc1.h =>
      split <;> mvcgen -trivial
      case vc2 =>
        intro _
        exact accPoint + accPoint
      case vc3 =>
        intro _
        exact (BitVec.extractLsb' (254 - i) 8
          (u1.val.eval ρ)).toNat • P256.Reference.generator
      case vc4 =>
        intro _
        exact hdouble
      case vc5 =>
        intro hlookup
        exact generatorWindowRep_of_lookup hu1 hlookup
      case vc1.h.success.success =>
        intro hout
        unfold SignedRadix32StepPoint
        simp_all [two_nsmul]
      case vc1.isFalse =>
        unfold SignedRadix32StepPoint
        simp_all [two_nsmul]

end Freigen.F2Z.Examples.EcdsaP256
