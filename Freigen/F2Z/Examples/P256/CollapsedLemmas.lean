import Freigen.F2Z.Examples.P256.Lemmas

/-!
# Completeness lemmas for open-once P-256 addition

This module isolates the heavier completeness proof for the collapsed
complete-add selectors. Keeping it out of the foundational P-256 lemma module
lets cost-optimization iterations reuse the cached base proofs.
-/

namespace Freigen.F2Z.Examples.P256.AffineSlope.Aux

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Std.Do
open scoped Std.Do
open Modular

def CollapsedNumeratorSpec (ρ : WF.Valuation) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl) (out : AffineSlope.Rep) : Prop :=
  (control.doubleCase.eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      3 * (Modular.Lazy.evalZMod base P.X ρ *
        Modular.Lazy.evalZMod base P.X ρ) - 3) ∧
  ((control.active - control.doubleCase).eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      Modular.Lazy.evalZMod base Q.Y ρ -
        Modular.Lazy.evalZMod base P.Y ρ) ∧
  ((LC.ofConst 1 - control.active).eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ = 0)

def CollapsedDenominatorSpec (ρ : WF.Valuation) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl) (out : AffineSlope.Rep) : Prop :=
  (control.doubleCase.eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      2 * Modular.Lazy.evalZMod base P.Y ρ) ∧
  ((control.active - control.doubleCase).eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      Modular.Lazy.evalZMod base Q.X ρ -
        Modular.Lazy.evalZMod base P.X ρ) ∧
  ((LC.ofConst 1 - control.active).eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ = 1)

@[spec 2000] theorem selectGated3Formula_complete
    {description : String} {gate1 gate2 gate3 : LC ℤ}
    {value1 value2 value3 : AffineSlope.Rep}
    (hcases : Gated3Cases ρ gate1 gate2 gate3)
    (hvalue1 : value1.Valid ρ)
    (hvalue1Fit : value1.intVal.eval ρ.int < (2 ^ 262 : Nat))
    (hvalue2 : value2.Valid ρ)
    (hvalue2Fit : value2.intVal.eval ρ.int < (2 ^ 262 : Nat))
    (hvalue3 : value3.Valid ρ)
    (hvalue3Fit : value3.intVal.eval ρ.int < (2 ^ 262 : Nat)) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectGated3Rep 262 66 description
        gate1 gate2 gate3 value1 value2 value3)
    ⦃⇓ out => ⌜Gated3Spec ρ gate1 gate2 gate3 value1 value2 value3 out ∧
      out.Valid ρ ∧ out.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
      out.bound = 66⌝⦄ := by
  exact selectGated3Rep_complete hcases hvalue1 hvalue1Fit hvalue2
    hvalue2Fit hvalue3 hvalue3Fit le_rfl (by
      norm_num [base, baseModulus]
      native_decide)

@[spec] theorem selectSlopeOperandsCollapsed_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {p : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hP : Reference.Represents ρ P p)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectSlopeOperandsCollapsed P Q control)
    ⦃⇓ operands => ⌜operands.Valid ρ ∧
      SlopeOperandsSpec ρ P Q control operands ∧
      Modular.Lazy.evalZMod base operands.denominator ρ ≠ 0⌝⦄ := by
  rcases hPvalid with ⟨hPXbound, hPX, _, hPYbound, hPY, _, _⟩
  rcases hQvalid with ⟨hQXbound, hQX, _, hQYbound, hQY, _, _⟩
  have hthree : (AffineSlope.ofElem three).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 3 (by native_decide) (by native_decide))
  have hzero : (AffineSlope.ofElem zero).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 0 (by native_decide) (by native_decide))
  have hone : (AffineSlope.ofElem one).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 1 (by native_decide) (by native_decide))
  have fit8 {x : AffineSlope.Rep} (hx : x.Valid ρ)
      (hbound : x.bound ≤ 8) :
      x.intVal.eval ρ.int < (2 ^ 262 : Nat) := by
    calc
      x.intVal.eval ρ.int < x.bound * base.modulus := hx.2
      _ ≤ 8 * base.modulus := by
        exact_mod_cast Nat.mul_le_mul_right base.modulus hbound
      _ < (2 ^ 262 : Nat) := by
        norm_num [base, baseModulus]
        native_decide
  have hx2Bound : P.X.bound * P.X.bound <
      2 ^ Modular.Lazy.quotientExtraBits := by
    simp [hPXbound, Modular.Lazy.quotientExtraBits]
  have hcases := hcontrol.slope_gated_cases
  unfold AffineSlope.selectSlopeOperandsCollapsed
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun x2 => ⌜
    Modular.Lazy.MulZModSpec base ρ P.X P.X x2 ∧
      x2.Valid ρ ∧ x2.bound = 2⌝)
  case hx => exact Modular.Lazy.mul_complete_zmod base hPX hPX hx2Bound
  case hf =>
    intro x2
    unfold AffineSlope.finishSelectSlopeOperandsCollapsed
      AffineSlope.selectCollapsedNumerator
    rw [Complete.interp_bind]
    apply Triple.bind (Q := fun numerator => ⌜
      CollapsedNumeratorSpec ρ P Q control numerator ∧
        numerator.Valid ρ ∧
        numerator.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
        numerator.bound = 66⌝)
    case hx =>
      mvcgen -trivial
      case vc1.success =>
        rename_i hmul numerator
        intros hsel hvalid hfit hbound
        refine ⟨?_, hvalid, hfit, hbound⟩
        unfold CollapsedNumeratorSpec
        exact ⟨fun hdouble => (hsel.1 hdouble).trans (by
            simp [Modular.Lazy.MulZModSpec] at hmul
            simp [hmul.1, AffineSlope.sub, AffineSlope.scale,
              AffineSlope.ofElem]),
          fun hgeneric => (hsel.2.1 hgeneric).trans (by
            simp [AffineSlope.sub]),
          fun hinactive => (hsel.2.2 hinactive).trans (by
            simp [AffineSlope.ofElem])⟩
      all_goals intros
      all_goals first
        | exact hcases
        | exact Modular.Lazy.sub_valid base hQY hPY
        | exact Modular.Lazy.scale_valid base hPY (by omega)
        | exact Modular.Lazy.sub_valid base
            (Modular.Lazy.scale_valid base (by assumption) (by omega)) hthree
        | exact hzero
        | exact fit8 (Modular.Lazy.sub_valid base
            (Modular.Lazy.scale_valid base (by assumption) (by omega)) hthree)
            (by
              change 3 * x2.bound + 2 ≤ 8
              omega)
        | exact fit8 (Modular.Lazy.sub_valid base hQY hPY)
            (by
              change Q.Y.bound + P.Y.bound ≤ 8
              omega)
        | exact fit8 hzero (by
            simp [AffineSlope.ofElem, Modular.Lazy.ofElem])
    case hf =>
      intro numerator
      unfold AffineSlope.selectCollapsedDenominator
      rw [Complete.interp_bind]
      apply Triple.bind (Q := fun denominator => ⌜
        (CollapsedNumeratorSpec ρ P Q control numerator ∧
          numerator.Valid ρ ∧
          numerator.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
          numerator.bound = 66) ∧
        (CollapsedDenominatorSpec ρ P Q control denominator ∧
          denominator.Valid ρ ∧
          denominator.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
          denominator.bound = 66)⌝)
      case hx =>
        mvcgen -trivial
        case vc1.success =>
          rename_i hnum denominator
          intros hsel hvalid hfit hbound
          refine ⟨hnum, ?_, hvalid, hfit, hbound⟩
          unfold CollapsedDenominatorSpec
          exact ⟨fun hdouble => (hsel.1 hdouble).trans (by
              simp [AffineSlope.scale]),
            fun hgeneric => (hsel.2.1 hgeneric).trans (by
              simp [AffineSlope.sub]),
            fun hinactive => (hsel.2.2 hinactive).trans (by
              simp [AffineSlope.ofElem])⟩
        all_goals intros
        all_goals first
          | exact hcases
          | exact Modular.Lazy.sub_valid base hQX hPX
          | exact Modular.Lazy.scale_valid base hPY (by omega)
          | exact hone
          | exact fit8 (Modular.Lazy.scale_valid base hPY (by omega)) (by
              change 2 * P.Y.bound ≤ 8
              omega)
          | exact fit8 (Modular.Lazy.sub_valid base hQX hPX) (by
              change Q.X.bound + P.X.bound ≤ 8
              omega)
          | exact fit8 hone (by
              simp [AffineSlope.ofElem, Modular.Lazy.ofElem])
      case hf =>
        intro denominator
        rw [Complete.interp_pure]
        mvcgen -trivial
        have h :
            (CollapsedNumeratorSpec ρ P Q control numerator ∧
              numerator.Valid ρ ∧
              numerator.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
              numerator.bound = 66) ∧
            (CollapsedDenominatorSpec ρ P Q control denominator ∧
              denominator.Valid ρ ∧
              denominator.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
              denominator.bound = 66) := by assumption
        rcases h with ⟨hnum, hden⟩
        have hspec : SlopeOperandsSpec ρ P Q control
            ⟨numerator, denominator⟩ := by
          unfold SlopeOperandsSpec
          constructor
          · intro hactive
            constructor
            · intro hdouble
              exact ⟨hnum.1.1 hdouble, hden.1.1 hdouble⟩
            · intro hdouble
              have hg :
                  (control.active - control.doubleCase).eval ρ.int = 1 := by
                simp [hactive, hdouble]
              exact ⟨hnum.1.2.1 hg, hden.1.2.1 hg⟩
          · intro hactive
            have hi : (LC.ofConst 1 - control.active).eval ρ.int = 1 := by
              simp [hactive]
            exact ⟨hnum.1.2.2 hi, hden.1.2.2 hi⟩
        exact ⟨⟨hnum.2.1, hnum.2.2.2, hden.2.1, hden.2.2.2⟩,
          hspec, SlopeOperandsSpec.denominator_ne_zero hcontrol hspec hP
            hnoTwoTorsion⟩

@[spec] theorem addCandidateCollapsed_sound
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    (hcontrol : AddControlSpec ρ P Q control) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.addCandidateCollapsed P Q control)
    ⦃⇓ candidate => ⌜AddCandidateSpec ρ P Q control candidate⌝⦄ := by
  have hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1 := by
    rcases hcontrol with ⟨_, _, _, _, _, _, hdoubleCase, _, _⟩
    exact hdoubleCase.2
  mvcgen [AffineSlope.addCandidateCollapsed]
  all_goals intros <;> assumption

@[spec] theorem addCandidateCollapsed_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {p : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hP : Reference.Represents ρ P p)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.addCandidateCollapsed P Q control)
    ⦃⇓ candidate => ⌜candidate.1.Valid ρ ∧
      candidate.1.bound = 2 ∧
      candidate.1.intVal.eval ρ.int < base.modulus ∧
      candidate.2.Valid ρ ∧ candidate.2.bound = 2 ∧
      candidate.2.intVal.eval ρ.int < base.modulus ∧
      AddCandidateSpec ρ P Q control candidate⌝⦄ := by
  have hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1 := by
    rcases hcontrol with ⟨_, _, _, _, _, _, hdoubleCase, _, _⟩
    exact hdoubleCase.2
  mvcgen [AffineSlope.addCandidateCollapsed]
  all_goals intros
  all_goals assumption

def CollapsedSelectAddOutputSpec (ρ : WF.Valuation)
    (P Q : AffineSlope.Point) (control : AffineSlope.AddControl)
    (candidate : AffineSlope.Rep × AffineSlope.Rep)
    (out : AffineSlope.Point) : Prop :=
  ∃ bothInfinity oppositePair finiteOpposite : LC ℤ,
    AffineSlope.AndBitSpec ρ P.infinity Q.infinity bothInfinity ∧
    AffineSlope.AndBitSpec ρ control.sameX control.oppositeY
      oppositePair ∧
    AffineSlope.AndBitSpec ρ control.finite oppositePair
      finiteOpposite ∧
    Gated4Spec ρ control.active P.infinity
      (Q.infinity - bothInfinity) (control.finite - control.active)
      candidate.1 Q.X P.X (AffineSlope.ofElem zero) out.X ∧
    Gated4Spec ρ control.active P.infinity
      (Q.infinity - bothInfinity) (control.finite - control.active)
      candidate.2 Q.Y P.Y (AffineSlope.ofElem zero) out.Y ∧
    out.infinity.eval ρ.int =
      bothInfinity.eval ρ.int + finiteOpposite.eval ρ.int

@[spec] theorem selectAddOutputCollapsed_sound
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {candidate : AffineSlope.Rep × AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectAddOutputCollapsed P Q control candidate)
    ⦃⇓ out => ⌜CollapsedSelectAddOutputSpec ρ P Q control candidate out⌝⦄ := by
  mvcgen [AffineSlope.selectAddOutputCollapsed,
    AffineSlope.selectAddCoordinateCollapsed,
    CollapsedSelectAddOutputSpec]
  rename_i bothInfinity hbothInfinity X hX Y hY
    finiteOpposite hfiniteOpposite
  rcases hfiniteOpposite with
    ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
  exact ⟨bothInfinity, oppositePair, finiteOpposite,
    hbothInfinity, hoppositePair, hfiniteOpposite, hX, hY, by simp⟩

theorem CollapsedSelectAddOutputSpec.toSelectAddOutputSpec
    {P Q out : AffineSlope.Point} {control : AffineSlope.AddControl}
    {candidate : AffineSlope.Rep × AffineSlope.Rep}
    (hPinf : P.infinity.eval ρ.int = 0 ∨
      P.infinity.eval ρ.int = 1)
    (hQinf : Q.infinity.eval ρ.int = 0 ∨
      Q.infinity.eval ρ.int = 1)
    (hcontrol : AddControlSpec ρ P Q control)
    (hout : CollapsedSelectAddOutputSpec ρ P Q control candidate out) :
    SelectAddOutputSpec ρ P Q control candidate out := by
  have hactive := hcontrol.active_bit
  rcases hout with ⟨bothInfinity, oppositePair, finiteOpposite,
    hbothInfinity, hoppositePair, hfiniteOpposite, hX, hY, houtInfinity⟩
  let z := AffineSlope.ofElem zero
  let inactiveX0 := if Q.infinity.eval ρ.int = 1 then P.X else z
  let inactiveY0 := if Q.infinity.eval ρ.int = 1 then P.Y else z
  let inactiveX := if P.infinity.eval ρ.int = 1 then Q.X else inactiveX0
  let inactiveY := if P.infinity.eval ρ.int = 1 then Q.Y else inactiveY0
  refine ⟨inactiveX0, inactiveY0, inactiveX, inactiveY, ?_, ?_,
    ?_, ?_, ?_, ?_, bothInfinity, oppositePair, finiteOpposite,
    hbothInfinity, hoppositePair, hfiniteOpposite, houtInfinity⟩
  all_goals
    rcases hPinf with hp | hp <;>
    rcases hQinf with hq | hq <;>
    rcases hactive with ha | ha <;>
    simp_all [inactiveX0, inactiveY0, inactiveX, inactiveY, z,
      AffineSlope.SelectZModSpec, Gated4Spec, AffineSlope.AndBitSpec,
      AddControlSpec]

theorem active_zero_of_finite_zero {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    (hcontrol : AddControlSpec ρ P Q control)
    (hfinite0 : control.finite.eval ρ.int = 0) :
    control.active.eval ρ.int = 0 := by
  rcases hcontrol with ⟨_, _, _, doubleKind, genericCase, _,
    hdoubleCase, hgenericCase, hactive⟩
  have hd : control.doubleCase.eval ρ.int = 0 := by
    rw [hdoubleCase.1, hfinite0]
    norm_num
  have hg : genericCase.eval ρ.int = 0 := by
    rw [hgenericCase.1, hfinite0]
    norm_num
  omega

theorem output_gated_cases {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl} {bothInfinity : LC ℤ}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hbothInfinity :
      AffineSlope.AndBitSpec ρ P.infinity Q.infinity bothInfinity) :
    Gated4Cases ρ control.active P.infinity
      (Q.infinity - bothInfinity) (control.finite - control.active) := by
  rcases hP with ⟨_, _, _, _, _, _, hPinf⟩
  rcases hQ with ⟨_, _, _, _, _, _, hQinf⟩
  have hactive := hcontrol.active_bit
  have hfiniteActive := active_zero_of_finite_zero hcontrol
  rcases hPinf with hp | hp <;>
    rcases hQinf with hq | hq <;>
    rcases hactive with ha | ha <;>
    simp_all [Gated4Cases, AffineSlope.AndBitSpec, AddControlSpec]

@[spec 2000] theorem selectGated4Coordinate_complete
    {description : String} {gate1 gate2 gate3 gate4 : LC ℤ}
    {value1 value2 value3 value4 : AffineSlope.Rep}
    (hcases : Gated4Cases ρ gate1 gate2 gate3 gate4)
    (hvalue1 : value1.Valid ρ)
    (hvalue1Canonical : value1.intVal.eval ρ.int < base.modulus)
    (hvalue2 : value2.Valid ρ)
    (hvalue2Canonical : value2.intVal.eval ρ.int < base.modulus)
    (hvalue3 : value3.Valid ρ)
    (hvalue3Canonical : value3.intVal.eval ρ.int < base.modulus)
    (hvalue4 : value4.Valid ρ)
    (hvalue4Canonical : value4.intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectGated4Rep 256 2 description
        gate1 gate2 gate3 gate4 value1 value2 value3 value4)
    ⦃⇓ out => ⌜Gated4Spec ρ gate1 gate2 gate3 gate4
      value1 value2 value3 value4 out ∧ out.Valid ρ ∧
      out.intVal.eval ρ.int < base.modulus ∧ out.bound = 2⌝⦄ := by
  exact selectGated4Rep_complete hcases hvalue1 hvalue1Canonical
    hvalue2 hvalue2Canonical hvalue3 hvalue3Canonical
    hvalue4 hvalue4Canonical base.fits (by
      have := base.positive
      omega)

@[spec] theorem selectAddCoordinateCollapsed_complete
    {Pcoord Qcoord candidate : AffineSlope.Rep}
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {bothInfinity : LC ℤ}
    (hcases : Gated4Cases ρ control.active P.infinity
      (Q.infinity - bothInfinity) (control.finite - control.active))
    (hcandidate : candidate.Valid ρ)
    (hcandidateCanonical : candidate.intVal.eval ρ.int < base.modulus)
    (hQcoord : Qcoord.Valid ρ)
    (hQcoordCanonical : Qcoord.intVal.eval ρ.int < base.modulus)
    (hPcoord : Pcoord.Valid ρ)
    (hPcoordCanonical : Pcoord.intVal.eval ρ.int < base.modulus)
    (hzero : (AffineSlope.ofElem zero).Valid ρ)
    (hzeroCanonical :
      (AffineSlope.ofElem zero).intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectAddCoordinateCollapsed Pcoord Qcoord candidate
        P Q control bothInfinity)
    ⦃⇓ out => ⌜Gated4Spec ρ control.active P.infinity
      (Q.infinity - bothInfinity) (control.finite - control.active)
      candidate Qcoord Pcoord (AffineSlope.ofElem zero) out ∧
      out.Valid ρ ∧ out.intVal.eval ρ.int < base.modulus ∧
      out.bound = 2⌝⦄ := by
  unfold AffineSlope.selectAddCoordinateCollapsed
  exact selectGated4Coordinate_complete hcases hcandidate
    hcandidateCanonical hQcoord hQcoordCanonical hPcoord
    hPcoordCanonical hzero hzeroCanonical

@[spec] theorem selectAddOutputCollapsed_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {candidate : AffineSlope.Rep × AffineSlope.Rep}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidateX : candidate.1.Valid ρ)
    (hcandidateXCanonical :
      candidate.1.intVal.eval ρ.int < base.modulus)
    (hcandidateY : candidate.2.Valid ρ)
    (hcandidateYCanonical :
      candidate.2.intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectAddOutputCollapsed P Q control candidate)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      SelectAddOutputSpec ρ P Q control candidate out⌝⦄ := by
  have hP' := hP
  have hQ' := hQ
  have hcontrol' := hcontrol
  rcases hcontrol with ⟨hsame, hopposite, hfinite, _, _, _, _, _, _⟩
  rcases hP with ⟨hPXbound, hPX, hPXCanonical,
    hPYbound, hPY, hPYCanonical, hPinf⟩
  rcases hQ with ⟨hQXbound, hQX, hQXCanonical,
    hQYbound, hQY, hQYCanonical, hQinf⟩
  have hzeroElem : zero.Valid ρ :=
    Modular.ofNat_valid base 0 (by native_decide) (by native_decide)
  have hzero : (AffineSlope.ofElem zero).Valid ρ :=
    Modular.Lazy.ofElem_valid base hzeroElem
  have hzeroCanonical :
      (AffineSlope.ofElem zero).intVal.eval ρ.int < base.modulus :=
    hzeroElem.2
  mvcgen [AffineSlope.selectAddOutputCollapsed]
  all_goals first
    | exact hPinf
    | exact hQinf
    | exact hsame.1
    | exact hopposite.1
    | exact hfinite.2
    | exact hcandidateX
    | exact hcandidateY
    | exact hcandidateXCanonical
    | exact hcandidateYCanonical
    | exact hPX
    | exact hPY
    | exact hQX
    | exact hQY
    | exact hPXCanonical
    | exact hPYCanonical
    | exact hQXCanonical
    | exact hQYCanonical
    | exact hzero
    | exact hzeroCanonical
    | exact output_gated_cases hP' hQ' hcontrol' (by assumption)
    | skip
  case vc24.success.success.success.success =>
    rename_i bothInfinity hbothInfinity X hX Y hY
      finiteOpposite hfiniteOpposite
    rcases hfiniteOpposite with
      ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
    have hcollapsed : CollapsedSelectAddOutputSpec ρ P Q control
        candidate ⟨X, Y, bothInfinity + finiteOpposite⟩ :=
      ⟨bothInfinity, oppositePair, finiteOpposite,
        hbothInfinity, hoppositePair, hfiniteOpposite,
        hX.1, hY.1, by simp⟩
    have hout := hcollapsed.toSelectAddOutputSpec hPinf hQinf hcontrol'
    exact ⟨⟨hX.2.2.2, hX.2.1, hX.2.2.1,
      hY.2.2.2, hY.2.1, hY.2.2.1,
      SelectAddOutputSpec.infinity_bit hP' hQ' hcontrol' hout⟩,
      hout⟩

end Freigen.F2Z.Examples.P256.AffineSlope.Aux
