import Freigen.F2Z.Examples.P256.WF

/-!
# Well-formedness for open-once P-256 addition

The optimized selectors witness one representative and constrain it with
gated integer R1Cs.  These proofs keep the valuation-parametric quotient
correctness boundary used by the public ECDSA theorem.
-/

namespace Freigen.F2Z.Examples.P256.AffineSlope

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Std.Do
open scoped Std.Do
open Modular

theorem selectGated3Rep_wf_aux (width outBound : Nat)
    (description : String) :
    WF.GadgetSpec
      (fun lv rv
          (left right : LC ℤ × LC ℤ × LC ℤ × Rep × Rep × Rep) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
        WF.LCEq lv.int rv.int left.2.2.1 right.2.2.1 ∧
        left.2.2.2.1.WFRel lv rv right.2.2.2.1 ∧
        left.2.2.2.2.1.WFRel lv rv right.2.2.2.2.1 ∧
        left.2.2.2.2.2.WFRel lv rv right.2.2.2.2.2)
      (fun input => selectGated3Rep width outBound description
        input.1 input.2.1 input.2.2.1 input.2.2.2.1
        input.2.2.2.2.1 input.2.2.2.2.2)
      Modular.Lazy.Rep.WFRel := by
  wfgen' using [U.fromWord_wf_rel]
    unfold [selectGated3Rep, Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i h
    change WF.LCEq leftVal.bool rightVal.bool outL[i] outR[i]
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem selectGated4Rep_wf_aux (width outBound : Nat)
    (description : String) :
    WF.GadgetSpec
      (fun lv rv
          (left right :
            LC ℤ × LC ℤ × LC ℤ × LC ℤ × Rep × Rep × Rep × Rep) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
        WF.LCEq lv.int rv.int left.2.2.1 right.2.2.1 ∧
        WF.LCEq lv.int rv.int left.2.2.2.1 right.2.2.2.1 ∧
        left.2.2.2.2.1.WFRel lv rv right.2.2.2.2.1 ∧
        left.2.2.2.2.2.1.WFRel lv rv right.2.2.2.2.2.1 ∧
        left.2.2.2.2.2.2.1.WFRel lv rv right.2.2.2.2.2.2.1 ∧
        left.2.2.2.2.2.2.2.WFRel lv rv right.2.2.2.2.2.2.2)
      (fun input => selectGated4Rep width outBound description
        input.1 input.2.1 input.2.2.1 input.2.2.2.1
        input.2.2.2.2.1 input.2.2.2.2.2.1
        input.2.2.2.2.2.2.1 input.2.2.2.2.2.2.2)
      Modular.Lazy.Rep.WFRel := by
  wfgen' using [U.fromWord_wf_rel]
    unfold [selectGated4Rep, Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i h
    change WF.LCEq leftVal.bool rightVal.bool outL[i] outR[i]
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

def selectCollapsedNumerator_wf_aux :=
  selectGated3Rep_wf_aux 262 66 "collapsed numerator"

def selectCollapsedDenominator_wf_aux :=
  selectGated3Rep_wf_aux 262 66 "collapsed denominator"

theorem selectCollapsedNumeratorCall_wf_aux :
    WF.GadgetSpec
      (fun lv rv
          (left right : Point × Point × AddControl × Rep) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.WFRel lv rv right.2.2.2)
      (fun input => selectCollapsedNumerator
        input.1 input.2.1 input.2.2.1 input.2.2.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectCollapsedNumerator
  apply WF.GadgetSpec.direct_rule
    (left := (left.2.2.1.doubleCase,
      left.2.2.1.active - left.2.2.1.doubleCase,
      LC.ofConst 1 - left.2.2.1.active,
      sub (scale 3 left.2.2.2) (ofElem three),
      sub left.2.1.Y left.1.Y, ofElem zero))
    (right := (right.2.2.1.doubleCase,
      right.2.2.1.active - right.2.2.1.doubleCase,
      LC.ofConst 1 - right.2.2.1.active,
      sub (scale 3 right.2.2.2) (ofElem three),
      sub right.2.1.Y right.1.Y, ofElem zero))
    selectCollapsedNumerator_wf_aux
  intro lv rv h
  simp_all [Point.WFRel, AddControl.WFRel, sub, scale, ofElem,
    Modular.Lazy.sub, Modular.Lazy.scale, Modular.Lazy.ofElem,
    Modular.Lazy.Rep.WFRel, WF.LCEq, LC.eval_add, LC.eval_sub,
    LC.eval_nsmul, LC.eval_ofConst, three, zero, fpConst,
    Modular.ofNat, U.intVal]

theorem selectCollapsedDenominatorCall_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectCollapsedDenominator
        input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectCollapsedDenominator
  apply WF.GadgetSpec.direct_rule
    (left := (left.2.2.doubleCase,
      left.2.2.active - left.2.2.doubleCase,
      LC.ofConst 1 - left.2.2.active,
      scale 2 left.1.Y, sub left.2.1.X left.1.X, ofElem one))
    (right := (right.2.2.doubleCase,
      right.2.2.active - right.2.2.doubleCase,
      LC.ofConst 1 - right.2.2.active,
      scale 2 right.1.Y, sub right.2.1.X right.1.X, ofElem one))
    selectCollapsedDenominator_wf_aux
  intro lv rv h
  simp_all [Point.WFRel, AddControl.WFRel, sub, scale, ofElem,
    Modular.Lazy.sub, Modular.Lazy.scale, Modular.Lazy.ofElem,
    Modular.Lazy.Rep.WFRel, WF.LCEq, LC.eval_add, LC.eval_sub,
    LC.eval_nsmul, LC.eval_ofConst, one, fpConst, Modular.ofNat,
    U.intVal]

theorem finishSelectSlopeOperandsCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv
          (left right : Point × Point × AddControl × Rep) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.WFRel lv rv right.2.2.2)
      (fun input => finishSelectSlopeOperandsCollapsed
        input.1 input.2.1 input.2.2.1 input.2.2.2)
      SlopeOperands.WFRel := by
  wfgen' using [selectCollapsedNumeratorCall_wf_aux,
    selectCollapsedDenominatorCall_wf_aux]
    unfold [finishSelectSlopeOperandsCollapsed, SlopeOperands.WFRel]

theorem selectSlopeOperandsCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectSlopeOperandsCollapsed
        input.1 input.2.1 input.2.2)
      SlopeOperands.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectSlopeOperandsCollapsed
  apply WF.GadgetSpec.bind_rule
    (left := (left.1.X, left.1.X))
    (right := (right.1.X, right.1.X))
    (Modular.Lazy.mul_wf base)
  · intro lv rv h
    exact ⟨h.1.1, h.1.1⟩
  · intro B x2L x2R hx2
    apply WF.GadgetSpec.direct_rule
      (left := (left.1, left.2.1, left.2.2, x2L))
      (right := (right.1, right.2.1, right.2.2, x2R))
      finishSelectSlopeOperandsCollapsed_wf_aux
    intro lv rv hB
    have hh := hx2 lv rv hB
    exact ⟨hh.1.1, hh.1.2.1, hh.1.2.2, hh.2⟩

theorem addCandidateCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => addCandidateCollapsed input.1 input.2.1 input.2.2)
      (fun lv rv left right =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2) := by
  wfgen' using [selectSlopeOperandsCollapsed_wf_aux,
    finishAddCandidate_wf_aux] unfold [addCandidateCollapsed]
  case vc1 =>
    rename_i hrel
    apply WF.GadgetSpec.direct_rule
      (left := (left.1, left.2.1, outL))
      (right := (right.1, right.2.1, outR))
      finishAddCandidate_wf_aux
    intro lv rv hB
    have hh := hrel lv rv hB
    exact ⟨hh.1.1, hh.1.2.1, hh.2⟩

def selectCollapsedOutput_wf_aux :=
  selectGated4Rep_wf_aux 256 2 "collapsed output"

theorem selectAddCoordinateCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv
          (left right :
            Rep × Rep × Rep × Point × Point × AddControl × LC ℤ) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.1.WFRel lv rv right.2.2.2.1 ∧
        left.2.2.2.2.1.WFRel lv rv right.2.2.2.2.1 ∧
        left.2.2.2.2.2.1.WFRel lv rv right.2.2.2.2.2.1 ∧
        WF.LCEq lv.int rv.int left.2.2.2.2.2.2 right.2.2.2.2.2.2)
      (fun input => selectAddCoordinateCollapsed input.1 input.2.1
        input.2.2.1 input.2.2.2.1 input.2.2.2.2.1
        input.2.2.2.2.2.1 input.2.2.2.2.2.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectAddCoordinateCollapsed
  apply WF.GadgetSpec.direct_rule
    (left := (left.2.2.2.2.2.1.active,
      left.2.2.2.1.infinity,
      left.2.2.2.2.1.infinity - left.2.2.2.2.2.2,
      left.2.2.2.2.2.1.finite - left.2.2.2.2.2.1.active,
      left.2.2.1, left.2.1, left.1, ofElem zero))
    (right := (right.2.2.2.2.2.1.active,
      right.2.2.2.1.infinity,
      right.2.2.2.2.1.infinity - right.2.2.2.2.2.2,
      right.2.2.2.2.2.1.finite - right.2.2.2.2.2.1.active,
      right.2.2.1, right.2.1, right.1, ofElem zero))
    selectCollapsedOutput_wf_aux
  intro lv rv h
  simp_all [Point.WFRel, AddControl.WFRel, ofElem,
    Modular.Lazy.ofElem, Modular.Lazy.Rep.WFRel, WF.LCEq,
    LC.eval_sub, LC.eval_ofConst, zero, fpConst, Modular.ofNat, U.intVal]

theorem selectAddOutputCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv
          (left right : Point × Point × AddControl × (Rep × Rep)) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.1.WFRel lv rv right.2.2.2.1 ∧
        left.2.2.2.2.WFRel lv rv right.2.2.2.2)
      (fun input => selectAddOutputCollapsed input.1 input.2.1
        input.2.2.1 input.2.2.2)
      Point.WFRel := by
  wfgen' using [andBit_wf_aux, selectAddCoordinateCollapsed_wf_aux,
    and3Bit_wf_aux]
    unfold [selectAddOutputCollapsed, Point.WFRel, AddControl.WFRel,
      Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, WF.LCEq, LC.eval_add]
  all_goals grind

theorem addCompleteCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => addCompleteCollapsed input.1 input.2)
      Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold addCompleteCollapsed
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) classifyAdd_wf_aux
  · intro lv rv h
    exact h
  · intro B controlL controlR hcontrol
    apply WF.GadgetSpec.bind_rule
      (left := (left.1, left.2, controlL))
      (right := (right.1, right.2, controlR))
      addCandidateCollapsed_wf_aux
    · intro lv rv hB
      have h := hcontrol lv rv hB
      exact ⟨h.1.1, h.1.2, h.2⟩
    · intro C candidateL candidateR hcandidate
      apply WF.GadgetSpec.direct_rule
        (left := (left.1, left.2, controlL, candidateL))
        (right := (right.1, right.2, controlR, candidateR))
        selectAddOutputCollapsed_wf_aux
      intro lv rv hC
      have hc := hcandidate lv rv hC
      have hk := hcontrol lv rv hc.1
      exact ⟨hk.1.1, hk.1.2, hk.2, hc.2.1, hc.2.2⟩

end Freigen.F2Z.Examples.P256.AffineSlope
