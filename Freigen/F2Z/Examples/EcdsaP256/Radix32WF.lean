import Freigen.F2Z.Examples.EcdsaP256.Radix32Production
import Freigen.F2Z.Examples.EcdsaP256.WF

/-! Quotient well-formedness proofs for the signed radix-32 verifier. -/

namespace Freigen.F2Z.Examples.EcdsaP256

open P256

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def Radix32Table.WFRel (lv rv : WF.Valuation)
    (left right : Radix32Table) : Prop :=
  WF.VectorRel AffineSlope.Point.WFRel lv rv left.low right.low ∧
  AffineSlope.Point.WFRel lv rv left.p16 right.p16

def SignedDigit.WFRel (lv rv : WF.Valuation)
    (left right : SignedDigit) : Prop :=
  U.FullWFRel lv rv left.oneHot right.oneHot

private theorem signedDigit_value_wfRel {lv rv : WF.Valuation}
    {left right : SignedDigit} (h : SignedDigit.WFRel lv rv left right) :
    WF.LCEq lv.int rv.int left.value right.value := by
  unfold SignedDigit.value WF.LCEq
  simp only [LC.eval_sum, LC.eval_nsmul, LC.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [h.2 i]

private theorem signedDigit_magnitude_wfRel {lv rv : WF.Valuation}
    {left right : SignedDigit} (h : SignedDigit.WFRel lv rv left right) :
    WF.LCEq lv.int rv.int left.magnitude right.magnitude := by
  unfold SignedDigit.magnitude WF.LCEq
  simp only [LC.eval_sum, LC.eval_nsmul, LC.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [h.2 i]

private theorem signedDigit_negative_wfRel {lv rv : WF.Valuation}
    {left right : SignedDigit} (h : SignedDigit.WFRel lv rv left right) :
    WF.LCEq lv.int rv.int left.negative right.negative := by
  unfold SignedDigit.negative WF.LCEq
  simp only [LC.eval_sum, LC.eval_nsmul, LC.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [h.2 i]

private theorem signedDigit_isSixteen_wfRel {lv rv : WF.Valuation}
    {left right : SignedDigit} (h : SignedDigit.WFRel lv rv left right) :
    WF.LCEq lv.int rv.int left.isSixteen right.isSixteen := by
  unfold SignedDigit.isSixteen WF.LCEq
  simp only [LC.eval_sum, LC.eval_nsmul, LC.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [h.2 i]

private theorem lceq_nsmul (k : Nat) {lv rv : WF.Valuation}
    {left right : LC ℤ} (h : WF.LCEq lv.int rv.int left right) :
    WF.LCEq lv.int rv.int (k • left) (k • right) := by
  unfold WF.LCEq at h ⊢
  simpa only [LC.eval_nsmul] using congrArg (k • ·) h

theorem materializeRadix32Multiples_wf_aux :
    WF.GadgetSpec Projective.WFRel materializeRadix32Multiples
      Radix32Table.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold materializeRadix32Multiples
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) materializeMultiples_wf_aux
  · intro lv rv h
    exact h
  · intro B tableL tableR htable
    apply WF.GadgetSpec.bind_rule
      (left := tableL[8]) (right := tableR[8])
      AffineSlope.doubleComplete_wf_aux
    · intro lv rv hB
      have ht := htable lv rv hB
      exact ht.2 ⟨8, by omega⟩
    · intro C p16L p16R hp16
      apply WF.Rel.pure
      intro lv rv hC
      have hp := hp16 lv rv hC
      have ht := htable lv rv hp.1
      exact ⟨ht.2, hp.2⟩

theorem signedDigitIndicators_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ) => WF.LCEq lv.int rv.int left right)
      signedDigitIndicators SignedDigit.WFRel := by
  wfgen' using [indicators_wf_aux]
    unfold [signedDigitIndicators, SignedDigit.WFRel]
  all_goals simp_all [WF.LCEq]
  all_goals try rfl

theorem selectBit_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ × LC ℤ × LC ℤ) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
        WF.LCEq lv.int rv.int left.2.2 right.2.2)
      (fun input => selectBit input.1 input.2.1 input.2.2)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  wfgen' using [U.fromWord_wf_rel] unfold [selectBit]
  case vc1 =>
    rename_i h
    change WF.LCEq leftVal.bool rightVal.bool outL[i] outR[i]
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem applyPointSign_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ × AffineSlope.Point) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        AffineSlope.Point.WFRel lv rv left.2 right.2)
      (fun input => applyPointSign input.1 input.2)
      AffineSlope.Point.WFRel := by
  wfgen' using [U.fromWord_wf_rel]
    unfold [applyPointSign, AffineSlope.Point.WFRel,
      Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i h
    change WF.LCEq leftVal.bool rightVal.bool outL[i] outR[i]
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem selectRadix32Magnitude_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : SignedDigit × Radix32Table) =>
        SignedDigit.WFRel lv rv left.1 right.1 ∧
        Radix32Table.WFRel lv rv left.2 right.2)
      (fun input => selectRadix32Magnitude input.1 input.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectRadix32Magnitude
  apply WF.GadgetSpec.bind_rule
    (left := (left.1.magnitude - 16 • left.1.isSixteen, left.2.low))
    (right := (right.1.magnitude - 16 • right.1.isSixteen, right.2.low))
    lookupPoint_wf_aux
  · intro lv rv h
    exact ⟨WF.eval_sub (signedDigit_magnitude_wfRel h.1)
      (lceq_nsmul 16 (signedDigit_isSixteen_wfRel h.1)), h.2.1⟩
  · intro B lowL lowR hlow
    apply WF.GadgetSpec.bind_rule
      (left := (left.1.isSixteen, left.2.p16.X, lowL.X))
      (right := (right.1.isSixteen, right.2.p16.X, lowR.X))
      AffineSlope.selectCanonical_wf_aux
    · intro lv rv hB
      have h := hlow lv rv hB
      exact ⟨signedDigit_isSixteen_wfRel h.1.1, h.1.2.2.1, h.2.1⟩
    · intro C XL XR hX
      apply WF.GadgetSpec.bind_rule
        (left := (left.1.isSixteen, left.2.p16.Y, lowL.Y))
        (right := (right.1.isSixteen, right.2.p16.Y, lowR.Y))
        AffineSlope.selectCanonical_wf_aux
      · intro lv rv hC
        have hx := hX lv rv hC
        have hl := hlow lv rv hx.1
        exact ⟨signedDigit_isSixteen_wfRel hl.1.1,
          hl.1.2.2.2.1, hl.2.2.1⟩
      · intro D YL YR hY
        apply WF.GadgetSpec.bind_rule
          (left := (left.1.isSixteen, left.2.p16.infinity, lowL.infinity))
          (right := (right.1.isSixteen, right.2.p16.infinity, lowR.infinity))
          selectBit_wf_aux
        · intro lv rv hD
          have hy := hY lv rv hD
          have hx := hX lv rv hy.1
          have hl := hlow lv rv hx.1
          exact ⟨signedDigit_isSixteen_wfRel hl.1.1,
            hl.1.2.2.2.2, hl.2.2.2⟩
        · intro E infinityL infinityR hinfinity
          apply WF.Rel.pure
          intro lv rv hE
          have hi := hinfinity lv rv hE
          have hy := hY lv rv hi.1
          have hx := hX lv rv hy.1
          exact ⟨hx.2, hy.2, hi.2⟩

theorem selectSignedRadix32Point_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : SignedDigit × Radix32Table) =>
        SignedDigit.WFRel lv rv left.1 right.1 ∧
        Radix32Table.WFRel lv rv left.2 right.2)
      (fun input => selectSignedRadix32Point input.1 input.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectSignedRadix32Point
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) selectRadix32Magnitude_wf_aux
  · intro lv rv h
    exact h
  · intro B pointL pointR hpoint
    apply WF.GadgetSpec.direct_rule
      (left := (left.1.negative, pointL))
      (right := (right.1.negative, pointR)) applyPointSign_wf_aux
    intro lv rv hB
    have hp := hpoint lv rv hB
    exact ⟨signedDigit_negative_wfRel hp.1.1, hp.2⟩

def SignedRadix32Input.WFRel : WF.Post (Fn × Fn × Projective) :=
  JointScalarInput.WFRel

private theorem windowValue_wfRel {lv rv : WF.Valuation}
    {left right : Fn} (h : Modular.Elem.ScalarWFRel lv rv left right)
    (start width : Nat) (hfit : start + width ≤ 256) :
    WF.LCEq lv.int rv.int
      (windowValue left start width hfit)
      (windowValue right start width hfit) := by
  unfold windowValue WF.LCEq
  simp only [LC.eval_sum, LC.eval_nsmul]
  apply Finset.sum_congr rfl
  intro j _
  have hb := h.2 ⟨start + j.val, by omega⟩
  unfold WF.LCEq at hb
  exact congrArg (2 ^ j.val • ·) hb

private theorem boothDigit_wfRel {lv rv : WF.Valuation}
    {left right : Fn} (h : Modular.Elem.ScalarWFRel lv rv left right)
    (i : Nat) (hi : i < 52) :
    WF.LCEq lv.int rv.int
      (boothDigit left i hi) (boothDigit right i hi) := by
  unfold boothDigit
  split
  · apply WF.eval_sub
    · apply WF.eval_add
      · exact windowValue_wfRel h (5 * i) 4 (by omega)
      · split
        · simp [WF.LCEq]
        · exact windowValue_wfRel h (5 * i - 1) 1 (by omega)
    · exact lceq_nsmul 16 (windowValue_wfRel h (5 * i + 4) 1 (by omega))
  · exact WF.eval_add
      (windowValue_wfRel h 255 1 (by omega))
      (windowValue_wfRel h 254 1 (by omega))

def SignedRadix32StepInput.WFRel :
    WF.Post (Fn × Fn × Radix32Table × AffineSlope.Point) :=
  fun lv rv left right =>
    Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
    Modular.Elem.ScalarWFRel lv rv left.2.1 right.2.1 ∧
    Radix32Table.WFRel lv rv left.2.2.1 right.2.2.1 ∧
    AffineSlope.Point.WFRel lv rv left.2.2.2 right.2.2.2

def GeneratorTailInput.WFRel : WF.Post (Fn × AffineSlope.Point) :=
  fun lv rv left right =>
    Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
    AffineSlope.Point.WFRel lv rv left.2 right.2

theorem generatorTail_wf_aux (exponent : Nat)
    (hfit : exponent % 8 = 0 → exponent + 8 ≤ 256) :
    WF.GadgetSpec GeneratorTailInput.WFRel
      (fun input => if _h : exponent % 8 = 0 then do
        let g ← lookupGeneratorByte
          (windowValue input.1 exponent 8 (hfit _h))
        AffineSlope.addComplete input.2 g
      else pure input.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  by_cases h : exponent % 8 = 0
  · simp only [dif_pos h]
    apply WF.GadgetSpec.bind_rule
      (left := windowValue left.1 exponent 8 (hfit h))
      (right := windowValue right.1 exponent 8 (hfit h))
      lookupGeneratorByte_wf_aux
    · intro lv rv hB
      exact windowValue_wfRel hB.1 exponent 8 (hfit h)
    · intro B gL gR hg
      apply WF.GadgetSpec.direct_rule
        (left := (left.2, gL)) (right := (right.2, gR))
        AffineSlope.addComplete_wf_aux
      intro lv rv hB
      have h' := hg lv rv hB
      exact ⟨h'.1.2, h'.2⟩
  · simp only [dif_neg h]
    apply WF.Rel.pure
    intro _ _ hB
    exact hB.2

theorem signedRadix32Step_wf_aux (i : Nat) (hi : i < 255) :
    WF.GadgetSpec SignedRadix32StepInput.WFRel
      (fun input => signedRadix32Step input.1 input.2.1 input.2.2.1
        i hi input.2.2.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold signedRadix32Step
  apply WF.GadgetSpec.bind_rule
    (left := left.2.2.2) (right := right.2.2.2)
    AffineSlope.doubleComplete_wf_aux
  · intro lv rv h
    exact h.2.2.2
  · intro B accDL accDR hdouble
    by_cases hq : (254 - i) % 5 = 0
    · simp only [dif_pos hq]
      apply WF.GadgetSpec.bind_rule
        (left := boothDigit left.2.1 ((254 - i) / 5) (by omega))
        (right := boothDigit right.2.1 ((254 - i) / 5) (by omega))
        signedDigitIndicators_wf_aux
      · intro lv rv hB
        have hd := hdouble lv rv hB
        exact boothDigit_wfRel hd.1.2.1 ((254 - i) / 5) (by omega)
      · intro C digitL digitR hdigit
        apply WF.GadgetSpec.bind_rule
          (left := (digitL, left.2.2.1))
          (right := (digitR, right.2.2.1))
          selectSignedRadix32Point_wf_aux
        · intro lv rv hC
          have hdig := hdigit lv rv hC
          have hd := hdouble lv rv hdig.1
          exact ⟨hdig.2, hd.1.2.2.1⟩
        · intro D qL qR hqPoint
          apply WF.GadgetSpec.bind_rule
            (left := (accDL, qL)) (right := (accDR, qR))
            AffineSlope.addComplete_wf_aux
          · intro lv rv hD
            have hq' := hqPoint lv rv hD
            have hdig := hdigit lv rv hq'.1
            have hd := hdouble lv rv hdig.1
            exact ⟨hd.2, hq'.2⟩
          · intro E accQL accQR hadd
            apply WF.GadgetSpec.direct_rule
              (left := (left.1, accQL)) (right := (right.1, accQR))
              (generatorTail_wf_aux (254 - i) (by intro hg; omega))
            intro lv rv hE
            have ha := hadd lv rv hE
            have hq' := hqPoint lv rv ha.1
            have hdig := hdigit lv rv hq'.1
            have hd := hdouble lv rv hdig.1
            exact ⟨hd.1.1, ha.2⟩
    · simp only [dif_neg hq]
      apply WF.GadgetSpec.direct_rule
        (left := (left.1, accDL)) (right := (right.1, accDR))
        (generatorTail_wf_aux (254 - i) (by intro hg; omega))
      intro lv rv hB
      have hd := hdouble lv rv hB
      exact ⟨hd.1.1, hd.2⟩

theorem signedRadix32JointScalarMul_wf_aux :
    WF.GadgetSpec SignedRadix32Input.WFRel
      (fun input => signedRadix32JointScalarMul input.1 input.2.1 input.2.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold signedRadix32JointScalarMul
  apply WF.GadgetSpec.bind_rule materializeRadix32Multiples_wf_aux
  · intro lv rv h
    exact h.2.2
  · intro B tableL tableR htable
    apply WF.GadgetSpec.bind_rule
      (left := boothDigit left.2.1 51 (by omega))
      (right := boothDigit right.2.1 51 (by omega))
      signedDigitIndicators_wf_aux
    · intro lv rv hB
      have ht := htable lv rv hB
      exact boothDigit_wfRel ht.1.2.1 51 (by omega)
    · intro C digitL digitR hdigit
      apply WF.GadgetSpec.bind_rule
        (left := (digitL, tableL)) (right := (digitR, tableR))
        selectSignedRadix32Point_wf_aux
      · intro lv rv hC
        have hd := hdigit lv rv hC
        have ht := htable lv rv hd.1
        exact ⟨hd.2, ht.2⟩
      · intro D initialL initialR hinitial
        refine WF.Rel.mono (WF.Rel.foldRange_rule
          (I := fun lv rv leftAcc rightAcc =>
            D lv rv ∧ AffineSlope.Point.WFRel lv rv leftAcc rightAcc)
          ?_ ?_) ?_
        · intro lv rv hD
          exact ⟨hD, (hinitial lv rv hD).2⟩
        · intro j hj P accL accR hacc
          have hinput : ∀ lv rv, P lv rv →
              SignedRadix32StepInput.WFRel lv rv
                (left.1, left.2.1, tableL, accL)
                (right.1, right.2.1, tableR, accR) := by
            intro lv rv hP
            have ha := hacc lv rv hP
            have hi := hinitial lv rv ha.1
            have hd := hdigit lv rv hi.1
            have ht := htable lv rv hd.1
            exact ⟨ht.1.1, ht.1.2.1, ht.2, ha.2⟩
          have hstep := (signedRadix32Step_wf_aux j hj.2.1).relHom P
            (left.1, left.2.1, tableL, accL)
            (right.1, right.2.1, tableR, accR) hinput
          exact WF.Rel.mono hstep (by
            intro lv rv outL outR hpost
            exact ⟨hpost.1, (hacc lv rv hpost.1).1, hpost.2⟩)
        · intro lv rv outL outR hpost
          exact hpost.2

theorem computeVerificationSum_radix32_wf_aux :
    WF.GadgetSpec PreparedVerification.WFRel computeVerificationSum
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold computeVerificationSum
  apply WF.GadgetSpec.direct_rule
    (left := (left.u1, left.u2, left.q))
    (right := (right.u1, right.u2, right.q))
    signedRadix32JointScalarMul_wf_aux
  intro lv rv h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem finishVerification_radix32_wf_aux :
    WF.GadgetSpec PreparedVerification.WFRel finishVerification
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold finishVerification
  apply WF.GadgetSpec.bind_rule_direct
    (left := left) (right := right) computeVerificationSum_radix32_wf_aux
  · intro lv rv h
    exact h
  · intro sumL sumR
    apply WF.GadgetSpec.direct_rule
      (left := (left.r, sumL)) (right := (right.r, sumR))
      checkVerificationX_wf_aux
    intro lv rv h
    exact ⟨h.1.2.2.2, h.2⟩

theorem verifyDigest_radix32_wf_aux :
    WF.GadgetSpec VerifyInput.WFRel
      (fun input => verifyDigest input.1 input.2.1 input.2.2.1 input.2.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold verifyDigest
  apply WF.GadgetSpec.bind_rule_direct
    (left := (left.2.1, left.2.2.1, left.2.2.2))
    (right := (right.2.1, right.2.2.1, right.2.2.2))
    canonicalizeInput_wf_aux
  · intro lv rv h
    exact h.2
  · intro inputL inputR
    apply WF.GadgetSpec.bind_rule_direct
      (left := (left.1, inputL)) (right := (right.1, inputR))
      prepareVerification_wf_aux
    · intro lv rv h
      exact ⟨h.1.1, h.2⟩
    · intro preparedL preparedR
      apply WF.GadgetSpec.direct_rule
        (left := preparedL) (right := preparedR)
        finishVerification_radix32_wf_aux
      intro lv rv h
      exact h.2

theorem verifyDigestFromBits_radix32_wf_aux :
    WF.GadgetSpec VerifyDigestBits.WFRel verifyDigestFromBits
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold verifyDigestFromBits
  apply WF.GadgetSpec.bind_rule_direct
    (left := verifyDigestInputWords left)
    (right := verifyDigestInputWords right) mapM_fromWord_wf_full
  · intro lv rv h
    exact verifyDigestInputWords_wf h
  · intro valuesL valuesR
    apply WF.GadgetSpec.direct_rule
      (left := (valuesL[0], ⟨valuesL[1], valuesL[2]⟩,
        ⟨valuesL[3], valuesL[4]⟩, ⟨valuesL[5], valuesL[6]⟩))
      (right := (valuesR[0], ⟨valuesR[1], valuesR[2]⟩,
        ⟨valuesR[3], valuesR[4]⟩, ⟨valuesR[5], valuesR[6]⟩))
      verifyDigest_radix32_wf_aux
    intro lv rv h
    exact ⟨h.2 0, h.2 1, h.2 2, h.2 3, h.2 4, h.2 5, h.2 6⟩

end Freigen.F2Z.Examples.EcdsaP256
