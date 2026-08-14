import Freigen.F2Z.Examples.Sha256Core

namespace Freigen.F2Z

open Std.Do
open scoped Std.Do

@[simp]
theorem U.valid_bitVec (w : BitVec n) : ((w : U n).Valid ρ) := by
  intro i
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  change LC.eval ρ.int (LC.ofConst w[i.val].toInt) =
    (LC.eval ρ.bool (LC.ofConst w[i.val])).toInt
  rw [LC.eval_ofConst, LC.eval_ofConst]

@[simp]
theorem U.valid_consts (f : Fin n → Bool) :
    ({ bits := { bitsLE := Vector.ofFn fun i => LC.ofConst (f i) }
       intBits := Vector.ofFn fun i => LC.ofConst (f i).toInt } : U n).Valid ρ := by
  intro i
  simp [U.Valid]

@[simp]
theorem U.valid_vector_default (i : Fin m) :
    (default : Vector (U n) m)[i].Valid ρ := by
  change (Vector.replicate m (default : U n))[i].Valid ρ
  simp only [Fin.getElem_fin, Vector.getElem_replicate]
  exact U.valid_default

@[simp]
theorem U.valid_vector_default_nat (i : Nat) (hi : i < m) :
    (default : Vector (U n) m)[i].Valid ρ := by
  exact U.valid_vector_default ⟨i, hi⟩

theorem U.valid_getElem! {xs : Vector (U n) m}
    (h : ∀ i : Fin m, xs[i].Valid ρ) {i : Nat} (hi : i < m) :
    xs[i]!.Valid ρ := by
  rw [getElem!_pos xs i hi]
  exact h ⟨i, hi⟩

theorem U.valid_getElem {xs : Vector (U n) m}
    (h : ∀ i : Fin m, xs[i].Valid ρ) (i : Nat) (hi : i < m) :
    xs[i].Valid ρ := h ⟨i, hi⟩

theorem U.allValid_set! {xs : Vector (U n) m} {x : U n}
    (hxs : ∀ i : Fin m, xs[i].Valid ρ) (hx : x.Valid ρ)
    (j : Nat) (hj : j < m) : (xs.set! i x)[j].Valid ρ := by
  rw [show xs.set! i x = xs.setIfInBounds i x by rfl]
  simp only [Vector.getElem_setIfInBounds hj]
  split
  · exact hx
  · exact hxs ⟨j, hj⟩

theorem U.valid_of_pointwise_right {xs : Vector (U n) m}
    {P : Fin m → Prop} (h : ∀ i, P i ∧ xs[i].Valid ρ) :
    ∀ i : Fin m, xs[i].Valid ρ := fun i => (h i).2

theorem U.allValid_pair {x y : U n} (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ∀ u ∈ #[x, y], u.Valid ρ := by
  intro u hu
  simp only [Array.mem_def, List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl | rfl <;> assumption

theorem U.allValid_four {a b c d : U n} (ha : a.Valid ρ)
    (hb : b.Valid ρ) (hc : c.Valid ρ) (hd : d.Valid ρ) :
    ∀ u ∈ #[a, b, c, d], u.Valid ρ := by
  intro u hu
  simp only [Array.mem_def, List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl <;> assumption


theorem Array.mapM_push [Monad m] [LawfulMonad m]
    (f : α → m β) (xs : Array α) (x : α) :
    (xs.push x).mapM f = (do
      let ys ← xs.mapM f
      let y ← f x
      pure (ys.push y)) := by
  simp only [Array.mapM_eq_mapM_toList, Array.toList_push,
    List.mapM_append, List.mapM_cons, List.mapM_nil]
  simp

theorem Vector.mapM_push [Monad m] [LawfulMonad m]
    (f : α → m β) (xs : Vector α n) (x : α) :
    (xs.push x).mapM f = (do
      let ys ← xs.mapM f
      let y ← f x
      pure (ys.push y)) := by
  apply Vector.map_toArray_inj.mp
  rw [Vector.toArray_mapM, Vector.toArray_push, Array.mapM_push]
  rw [← Vector.toArray_mapM (f := f) (xs := xs)]
  rw [bind_map_left]
  simp only [← bind_pure_comp, bind_assoc, pure_bind,
    Vector.toArray_push]

theorem U.fromWord_wf_full :
    WF.GadgetSpec
      (fun leftVal rightVal (left right : Word n) =>
        ∀ i : Fin n,
          WF.LCEq leftVal.bool rightVal.bool left.bitsLE[i] right.bitsLE[i])
      U.fromWord
      (fun leftVal rightVal left right =>
        (∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
          left.bits.bitsLE[i] right.bits.bitsLE[i]) ∧
        (∀ i : Fin n, WF.LCEq leftVal.int rightVal.int
          left.intBits[i] right.intBits[i]) ∧
        WF.LCEq leftVal.int rightVal.int left.intVal right.intVal) := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.fromWord
  apply WF.Rel.forIn'_range_f2z_set!_bind
  · intro leftVal rightVal hinput i
    simp [WF.LCEq]
  · intro i hi leftVal rightVal hinput
    exact hinput ⟨i, by grind⟩
  · grind
  · intro A leftInts rightInts hA
    apply WF.Rel.pure
    intro leftVal rightVal hambient
    have hpost := hA leftVal rightVal hambient
    refine ⟨?_, hpost.2, WF.LCEq.uIntVal hpost.2⟩
    exact hpost.1

theorem U.fromInt_wf_full :
    WF.GadgetSpec
      (fun leftVal rightVal (left right : LC ℤ) =>
        WF.LCEq leftVal.int rightVal.int left right)
      (U.fromInt n)
      (fun leftVal rightVal left right =>
        (∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
          left.bits.bitsLE[i] right.bits.bitsLE[i]) ∧
        (∀ i : Fin n, WF.LCEq leftVal.int rightVal.int
          left.intBits[i] right.intBits[i]) ∧
        WF.LCEq leftVal.int rightVal.int left.intVal right.intVal) := by
  wfgen' using [U.fromWord_wf_full] unfold [U.fromInt]
  case vc1 hrel =>
    rcases hrel with ⟨_, values, _, _, hleft, hright⟩
    unfold WF.LCEq
    exact (hleft i.val i.isLt).trans (hright i.val i.isLt).symm
  case vc2 h =>
    unfold WF.LCEq at h
    simp only [WF.evalArgs]
    rw [h]
  case vc3 h =>
    unfold WF.ArgsEq
    simp only [WF.evalArgs]
    unfold WF.LCEq at h
    exact congrArg (fun x => h![x]) h

theorem U.mapM_fromWord_wf_full {n m : Nat} :
    WF.GadgetSpec
      (WF.VectorRel (n := m) fun lv rv (l r : Word n) =>
        ∀ i : Fin n, WF.LCEq lv.bool rv.bool l[i] r[i])
      (fun xs : Vector (Word n) m => xs.mapM U.fromWord)
      (WF.VectorRel (n := m) fun lv rv l r =>
        (∀ i : Fin n, WF.LCEq lv.bool rv.bool
          l.bits.bitsLE[i] r.bits.bitsLE[i]) ∧
        (∀ i : Fin n, WF.LCEq lv.int rv.int l.intBits[i] r.intBits[i]) ∧
        WF.LCEq lv.int rv.int l.intVal r.intVal) := by
  unfold WF.GadgetSpec
  intro left right
  apply WF.Rel.mono
    (U.fromWord_wf_full.relHom.vectorMapM
      (fun lv rv => WF.VectorRel
        (fun lv rv (l r : Word n) => ∀ i : Fin n,
          WF.LCEq lv.bool rv.bool l[i] r[i]) lv rv left right)
      left right (fun _ _ h => h))
  intro _ _ _ _ h
  exact h.2

def U.WFRel (leftVal rightVal : WF.Valuation) (left right : U n) : Prop :=
  WF.LCEq leftVal.int rightVal.int left.intVal right.intVal ∧
  ∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
    left.bits.bitsLE[i] right.bits.bitsLE[i]

theorem U.fromWord_wf_rel {n : Nat} :
    WF.GadgetSpec
      (fun lv rv (l r : Word n) => ∀ i : Fin n,
        WF.LCEq lv.bool rv.bool l[i] r[i])
      U.fromWord U.WFRel := by
  intro left right
  apply WF.Rel.mono (U.fromWord_wf_full left right)
  intro _ _ _ _ h
  exact ⟨h.2.2, h.1⟩

@[simp]
theorem U.wfRel_default (leftVal rightVal : WF.Valuation) :
    U.WFRel leftVal rightVal (default : U n) default := by
  unfold U.WFRel WF.LCEq U.intVal
  constructor
  · rw [LC.eval_sum, LC.eval_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [LC.eval_nsmul, LC.eval_nsmul]
    have hz : (default : U n).intBits[i] = 0 := by
      change (Vector.replicate n (0 : LC ℤ))[i] = 0
      simp
    rw [hz, LC.eval_zero, LC.eval_zero]
  · intro i
    have hz : (default : U n).bits.bitsLE[i] = 0 := by
      change (Vector.replicate n (0 : LC Bool))[i] = 0
      simp
    change LC.eval leftVal.bool (default : U n).bits.bitsLE[i] =
      LC.eval rightVal.bool (default : U n).bits.bitsLE[i]
    rw [hz, LC.eval_zero, LC.eval_zero]

theorem U.vector_default_get (i : Fin m) :
    (default : Vector (U n) m)[i] = default := by
  change (Vector.replicate m (default : U n))[i] = default
  simp

theorem U.vector_default_wfRel (leftVal rightVal : WF.Valuation) :
    WF.VectorRel U.WFRel leftVal rightVal
      (default : Vector (U n) m) default := by
  intro i
  simpa only [U.vector_default_get] using U.wfRel_default leftVal rightVal

theorem WF.VectorRel.set! {R : WF.Post α}
    {left right : Vector α n} {xL xR : α}
    (h : WF.VectorRel R leftVal rightVal left right)
    (hx : R leftVal rightVal xL xR) (i : Nat) :
    WF.VectorRel R leftVal rightVal (left.set! i xL) (right.set! i xR) := by
  intro j
  rw [show left.set! i xL = left.setIfInBounds i xL by rfl,
    show right.set! i xR = right.setIfInBounds i xR by rfl]
  change R leftVal rightVal
    (left.setIfInBounds i xL)[j.val]
    (right.setIfInBounds i xR)[j.val]
  rw [Vector.getElem_setIfInBounds (j := j.val) j.isLt,
    Vector.getElem_setIfInBounds (j := j.val) j.isLt]
  split
  · exact hx
  · exact h j

theorem WF.VectorRel.getElem! [Inhabited α] {R : WF.Post α}
    {left right : Vector α n}
    (h : WF.VectorRel R leftVal rightVal left right)
    {i : Nat} (hi : i < n) :
    R leftVal rightVal left[i]! right[i]! := by
  rw [getElem!_pos left i hi, getElem!_pos right i hi]
  exact h ⟨i, hi⟩

def Word.WFRel (leftVal rightVal : WF.Valuation)
    (left right : Word n) : Prop :=
  ∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool left[i] right[i]

theorem Word.WFRel.xor {uL uR vL vR : Word n}
    (hu : Word.WFRel leftVal rightVal uL uR)
    (hv : Word.WFRel leftVal rightVal vL vR) :
    Word.WFRel leftVal rightVal (uL ^^^ vL) (uR ^^^ vR) := by
  intro i
  unfold Word.WFRel at hu hv
  unfold WF.LCEq at ⊢
  change LC.eval leftVal.bool (uL ^^^ vL).bitsLE[i.val] =
    LC.eval rightVal.bool (uR ^^^ vR).bitsLE[i.val]
  rw [show uL ^^^ vL =
      { bitsLE := Vector.zipWith (· + ·) uL.bitsLE vL.bitsLE } by rfl,
    show uR ^^^ vR =
      { bitsLE := Vector.zipWith (· + ·) uR.bitsLE vR.bitsLE } by rfl]
  simp only [Vector.getElem_zipWith i.isLt, LC.eval_add]
  unfold WF.LCEq at hu hv
  have hui := hu i
  have hvi := hv i
  change LC.eval leftVal.bool uL.bitsLE[i.val] =
    LC.eval rightVal.bool uR.bitsLE[i.val] at hui
  change LC.eval leftVal.bool vL.bitsLE[i.val] =
    LC.eval rightVal.bool vR.bitsLE[i.val] at hvi
  rw [hui, hvi]

theorem Word.WFRel.xor3
    {uL uR vL vR wL wR : Word n}
    (hu : Word.WFRel leftVal rightVal uL uR)
    (hv : Word.WFRel leftVal rightVal vL vR)
    (hw : Word.WFRel leftVal rightVal wL wR) :
    Word.WFRel leftVal rightVal (uL ^^^ vL ^^^ wL)
      (uR ^^^ vR ^^^ wR) :=
  (hu.xor hv).xor hw

theorem Word.WFRel.rotateRight {uL uR : Word n}
    (h : Word.WFRel leftVal rightVal uL uR)
    (k : Nat) : Word.WFRel leftVal rightVal
      (uL.rotateRight k) (uR.rotateRight k) := by
  intro i
  unfold WF.LCEq
  change LC.eval leftVal.bool (uL.rotateRight k).bitsLE[i.val] =
    LC.eval rightVal.bool (uR.rotateRight k).bitsLE[i.val]
  rw [Word.rotateRight_getElem uL k i i.isLt,
    Word.rotateRight_getElem uR k i i.isLt]
  split
  · exact h ⟨_, by omega⟩
  · exact h ⟨_, by omega⟩

theorem Word.WFRel.shiftRight {uL uR : Word n}
    (h : Word.WFRel leftVal rightVal uL uR)
    (k : Nat) : Word.WFRel leftVal rightVal (uL >>> k) (uR >>> k) := by
  intro i
  unfold WF.LCEq
  change LC.eval leftVal.bool (uL >>> k).bitsLE[i.val] =
    LC.eval rightVal.bool (uR >>> k).bitsLE[i.val]
  rw [Word.shiftRight_getElem uL k i i.isLt,
    Word.shiftRight_getElem uR k i i.isLt]
  split
  · exact h ⟨_, by omega⟩
  · simp

def U.sumFixed (us : Vector (U n) m) : Circuit (U n) := do
  let newZ := us.toArray.map (fun x => x.intVal) |>.sum
  let newBits ← U.fromInt (n + Nat.clog 2 m) newZ
  pure (newBits.takeLE n (by omega))

theorem U.sum_toArray_eq_sumFixed (us : Vector (U n) m) :
    U.sum us.toArray = U.sumFixed us := by
  cases us with
  | mk array hsize =>
      cases hsize
      unfold U.sum U.sumFixed
      simp only
      apply bind_congr
      intro wide
      apply congrArg (fun x : U n => (pure x : Circuit (U n)))
      exact (U.takeLE_eq_truncate wide (by omega)).symm

@[simp]
theorem U.sum2_eq_sumFixed (a b : U n) :
    U.sum #[a, b] = U.sumFixed #v[a, b] :=
  U.sum_toArray_eq_sumFixed #v[a, b]

@[simp]
theorem U.sum4_eq_sumFixed (a b c d : U n) :
    U.sum #[a, b, c, d] = U.sumFixed #v[a, b, c, d] :=
  U.sum_toArray_eq_sumFixed #v[a, b, c, d]

@[simp]
theorem U.sum6_eq_sumFixed (a b c d e f : U n) :
    U.sum #[a, b, c, d, e, f] = U.sumFixed #v[a, b, c, d, e, f] :=
  U.sum_toArray_eq_sumFixed #v[a, b, c, d, e, f]

@[simp]
theorem U.sum7_eq_sumFixed (a b c d e f g : U n) :
    U.sum #[a, b, c, d, e, f, g] =
      U.sumFixed #v[a, b, c, d, e, f, g] :=
  U.sum_toArray_eq_sumFixed #v[a, b, c, d, e, f, g]

theorem U.lceq_intVal_sum {left right : Vector (U n) m}
    (h : WF.VectorRel U.WFRel leftVal rightVal left right) :
    WF.LCEq leftVal.int rightVal.int
      (left.toArray.map (fun x => x.intVal)).sum
      (right.toArray.map (fun x => x.intVal)).sum := by
  unfold WF.LCEq
  rw [LC.eval_array_sum, LC.eval_array_sum]
  apply congrArg Array.sum
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    simp only [Array.getElem_map]
    exact (h ⟨i, by simpa using hiLeft⟩).1

theorem U.sumFixed_wf {n m : Nat} :
    WF.GadgetSpec (WF.VectorRel (U.WFRel (n := n)))
      (U.sumFixed (n := n) (m := m)) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.sumFixed
  apply WF.GadgetSpec.bind_rule U.fromInt_wf_full
  · intro leftVal rightVal h
    exact U.lceq_intVal_sum h
  · intro B outL outR hpost
    apply WF.Rel.pure
    intro leftVal rightVal hB
    have h := hpost leftVal rightVal hB
    let hle : n ≤ n + Nat.clog 2 m := by omega
    unfold U.WFRel
    constructor
    · apply WF.LCEq.uIntVal
      intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.2.1 (i.castLE hle)
    · intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.1 (i.castLE hle)

end Freigen.F2Z

namespace Freigen.F2Z.Examples

open Std.Do
open scoped Std.Do

def scheduleStep (i : Nat) (w : Vector (U 32) 64) : Circuit (U 32) := do
  let wi15 := w[i - 15]!.bits
  let s0 ← U.fromWord $
    wi15.rotateRight 7 ^^^ wi15.rotateRight 18 ^^^ (wi15 >>> 3)
  let wi2 := w[i - 2]!.bits
  let s1 ← U.fromWord $
    wi2.rotateRight 17 ^^^ wi2.rotateRight 19 ^^^ (wi2 >>> 10)
  U.sumFixed #v[w[i - 16]!, s0, w[i - 7]!, s1]

@[simp]
theorem scheduleLoopBody_eq (i : Nat) (h : i ∈ [16:64])
    (w : Vector (U 32) 64) :
    (do
      let wi15 := w[i - 15]!.bits
      let s0 ← U.fromWord $
        wi15.rotateRight 7 ^^^ wi15.rotateRight 18 ^^^ (wi15 >>> 3)
      let wi2 := w[i - 2]!.bits
      let s1 ← U.fromWord $
        wi2.rotateRight 17 ^^^ wi2.rotateRight 19 ^^^ (wi2 >>> 10)
      let out ← U.sumFixed #v[w[i - 16]!, s0, w[i - 7]!, s1]
      pure (ForInStep.yield (w.set! i out))) =
    (do
      let out ← scheduleStep i w
      pure (ForInStep.yield (w.set! i out))) := by
  rfl

theorem scheduleStep_wf (i : Nat) (hi : i ∈ [16:64]) :
    WF.GadgetSpec (WF.VectorRel U.WFRel) (scheduleStep i) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold scheduleStep
  apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
  · intro leftVal rightVal h
    have hword := h.getElem! (i := i - 15) (by grind) |>.2
    change Word.WFRel leftVal rightVal _ _ at hword
    exact ((hword.rotateRight 7).xor (hword.rotateRight 18)).xor
      (hword.shiftRight 3)
  · intro B s0L s0R hs0
    apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
    · intro leftVal rightVal hB
      have hvec := (hs0 leftVal rightVal hB).1
      have hword := hvec.getElem! (i := i - 2) (by grind) |>.2
      change Word.WFRel leftVal rightVal _ _ at hword
      exact ((hword.rotateRight 17).xor (hword.rotateRight 19)).xor
        (hword.shiftRight 10)
    · intro C s1L s1R hs1
      apply WF.Rel.mono ((U.sumFixed_wf
        #v[left[i - 16]!, s0L, left[i - 7]!, s1L]
        #v[right[i - 16]!, s0R, right[i - 7]!, s1R]).frame (by
        intro leftVal rightVal hC
        have h0 := hs1 leftVal rightVal hC
        have h1 := hs0 leftVal rightVal h0.1
        have hvec := h1.1
        intro j
        fin_cases j
        · simpa using hvec.getElem! (i := i - 16) (by grind)
        · simpa using h1.2
        · simpa using hvec.getElem! (i := i - 7) (by grind)
        · simpa using h0.2))
      intro _ _ _ _ h
      exact h.2

abbrev RoundState :=
  U 32 × U 32 × U 32 × U 32 × U 32 × U 32 × U 32 × U 32

def roundStep (i : Nat) (w : Vector (U 32) 64)
    (r : RoundState) : Circuit RoundState := do
  let S1 ← U.fromWord $ r.2.2.2.2.1.bits.rotateRight 6 ^^^
    r.2.2.2.2.1.bits.rotateRight 11 ^^^ r.2.2.2.2.1.bits.rotateRight 25
  let ch ← U.ch r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1
  let S0 ← U.fromWord $ r.1.bits.rotateRight 2 ^^^
    r.1.bits.rotateRight 13 ^^^ r.1.bits.rotateRight 22
  let maj ← U.maj r.1 r.2.1 r.2.2.1
  let newE ← U.sumFixed #v[
    r.2.2.2.1, r.2.2.2.2.2.2.2, S1, ch, k[i]!, w[i]!]
  let newA ← U.sumFixed #v[
    r.2.2.2.2.2.2.2, S1, ch, k[i]!, w[i]!, S0, maj]
  pure ⟨newA, r.1, r.2.1, r.2.2.1, newE,
    r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

abbrev BVState :=
  BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

def scheduleStepBV (i : Nat) (w : Vector (BitVec 32) 64) :
    Vector (BitVec 32) 64 :=
  let s0 := w[i - 15]!.rotateRight 7 ^^^ w[i - 15]!.rotateRight 18 ^^^
    (w[i - 15]! >>> 3)
  let s1 := w[i - 2]!.rotateRight 17 ^^^ w[i - 2]!.rotateRight 19 ^^^
    (w[i - 2]! >>> 10)
  w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)

def roundStepBV (i : Nat) (w : Vector (BitVec 32) 64)
    (r : BVState) : BVState :=
  let S1 := r.2.2.2.2.1.rotateRight 6 ^^^ r.2.2.2.2.1.rotateRight 11 ^^^
    r.2.2.2.2.1.rotateRight 25
  let ch := chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1
  let S0 := r.1.rotateRight 2 ^^^ r.1.rotateRight 13 ^^^ r.1.rotateRight 22
  let maj := majBV r.1 r.2.1 r.2.2.1
  let newE := r.2.2.2.1 + r.2.2.2.2.2.2.2 + S1 + ch + k[i]! + w[i]!
  let newA := r.2.2.2.2.2.2.2 + S1 + ch + k[i]! + w[i]! + S0 + maj
  ⟨newA, r.1, r.2.1, r.2.2.1, newE,
    r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

def scheduleBV (m : Vector (BitVec 32) 16) : Vector (BitVec 32) 64 :=
  let init := ([0:16].toList).foldl
    (fun w i => w.set! i m[i]!) default
  ([16:64].toList).foldl (fun w i => scheduleStepBV i w) init

@[spec]
theorem U.sumFixed_sound {us : Vector (U n) m}
    (hvalid : ∀ i : Fin m, us[i].Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.sumFixed us)
    ⦃ ⇓ out => ⌜out.Valid ρ ∧
      out.eval ρ = (us.toArray.map fun u => u.eval ρ).sum⌝⦄ := by
  rw [← U.sum_toArray_eq_sumFixed]
  apply U.sum_sound
  intro u hu
  rw [Array.mem_iff_getElem] at hu
  obtain ⟨i, hi, rfl⟩ := hu
  exact hvalid ⟨i, by simpa using hi⟩

def scheduleValueBV (i : Nat) (w : Vector (BitVec 32) 64) : BitVec 32 :=
  let s0 := w[i - 15]!.rotateRight 7 ^^^ w[i - 15]!.rotateRight 18 ^^^
    (w[i - 15]! >>> 3)
  let s1 := w[i - 2]!.rotateRight 17 ^^^ w[i - 2]!.rotateRight 19 ^^^
    (w[i - 2]! >>> 10)
  w[i - 16]! + s0 + w[i - 7]! + s1

@[simp]
theorem Vector.getElem!_map [Inhabited α] [Inhabited β]
    (xs : Vector α n) (f : α → β)
    (i : Nat) (hi : i < n) : (xs.map f)[i]! = f (xs[i]!) := by
  rw [getElem!_pos (xs.map f) i (by simpa), getElem!_pos xs i hi,
    Vector.getElem_map f hi]

attribute [local simp] U.eval_eq_word_eval


@[spec]
theorem scheduleStep_sound (i : Nat) (hi : i ∈ [16:64])
    {w : Vector (U 32) 64} (hvalid : ∀ j : Fin 64, w[j].Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (scheduleStep i w)
    ⦃ ⇓ out => ⌜out.Valid ρ ∧ out.eval ρ =
      scheduleValueBV i (w.map (fun u => u.eval ρ))⌝⦄ := by
  unfold scheduleStep scheduleValueBV
  mvcgen
  case vc1 =>
    rename_i s0 hs0 s1 hs1 out houtValid houtEval
    refine ⟨houtValid, ?_⟩
    rw [houtEval]
    have heval0 := U.eval_eq_word_eval s0 _ hs0.2 hs0.1
    have heval1 := U.eval_eq_word_eval s1 _ hs1.2 hs1.1
    simp only [Word.eval_xor, Word.eval_rotateRight,
      Word.eval_shiftRight] at heval0 heval1
    simp only [Vector.toArray_mk, Array.map_toList, List.map_cons,
      List.map_nil, Array.sum_toList, List.sum_cons, List.sum_nil, add_zero]
    rw [heval0, heval1]
  case vc2 =>
    intro _ h2 j
    fin_cases j
    · exact U.valid_getElem! hvalid (by grind)
    · simp_all
    · exact U.valid_getElem! hvalid (by grind)
    · exact h2

def RoundEvalRel (r : RoundState) (v : BVState) (ρ : WF.Valuation) : Prop :=
  r.1.Valid ρ ∧ r.1.eval ρ = v.1 ∧
  r.2.1.Valid ρ ∧ r.2.1.eval ρ = v.2.1 ∧
  r.2.2.1.Valid ρ ∧ r.2.2.1.eval ρ = v.2.2.1 ∧
  r.2.2.2.1.Valid ρ ∧ r.2.2.2.1.eval ρ = v.2.2.2.1 ∧
  r.2.2.2.2.1.Valid ρ ∧ r.2.2.2.2.1.eval ρ = v.2.2.2.2.1 ∧
  r.2.2.2.2.2.1.Valid ρ ∧ r.2.2.2.2.2.1.eval ρ = v.2.2.2.2.2.1 ∧
  r.2.2.2.2.2.2.1.Valid ρ ∧ r.2.2.2.2.2.2.1.eval ρ = v.2.2.2.2.2.2.1 ∧
  r.2.2.2.2.2.2.2.Valid ρ ∧ r.2.2.2.2.2.2.2.eval ρ = v.2.2.2.2.2.2.2

set_option maxHeartbeats 800000 in
@[spec]
theorem roundStep_sound (i : Nat) (hi : i ∈ [0:64])
    {w : Vector (U 32) 64} {r : RoundState}
    (hw : ∀ j : Fin 64, w[j].Valid ρ)
    (hr : RoundEvalRel r v ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (roundStep i w r)
    ⦃ ⇓ out => ⌜RoundEvalRel out
      (roundStepBV i (w.map (fun u => u.eval ρ)) v) ρ⌝⦄ := by
  unfold roundStep roundStepBV
  mvcgen
  case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 =>
    simp_all only [RoundEvalRel]
  case vc7 | vc8 =>
    intro j
    fin_cases j
    all_goals first
      | exact U.valid_getElem! hw (by grind)
      | simp_all [RoundEvalRel]
  case vc9 =>
    simp_all only [RoundEvalRel, Vector.toArray_mk, Array.map_toList,
      List.map_cons, List.map_nil, Array.sum_toList, List.sum_cons,
      List.sum_nil, add_zero, Word.eval_xor, Word.eval_rotateRight,
      chBV, majBV,
      Vector.getElem!_map w (fun u => u.eval ρ) i (by grind)]

def VectorEvalRel (us : Vector (U n) m) (vs : Vector (BitVec n) m)
    (ρ : WF.Valuation) : Prop :=
  ∀ i : Fin m, us[i].Valid ρ ∧ us[i].eval ρ = vs[i]

theorem VectorEvalRel.set! (h : VectorEvalRel us vs ρ)
    (hx : x.Valid ρ ∧ x.eval ρ = y) (i : Nat) :
    VectorEvalRel (us.set! i x) (vs.set! i y) ρ := by
  intro j
  rw [show us.set! i x = us.setIfInBounds i x by rfl,
    show vs.set! i y = vs.setIfInBounds i y by rfl]
  simp only [Vector.getElem_setIfInBounds j.isLt]
  split
  · exact hx
  · exact h j

@[spec]
theorem Vector.mapM_fromWord_sound {s : Vector (Word width) n} :
    ⦃⌜True⌝⦄ Sound.interp ρ (s.mapM U.fromWord)
    ⦃ ⇓ us => ⌜VectorEvalRel us (s.map (Word.eval ρ.bool)) ρ⌝⦄ := by
  induction n with
  | zero =>
      rw [show s = #v[] from Vector.eq_empty]
      simp [VectorEvalRel]
      mvcgen
  | succ n ih =>
      obtain ⟨init, last, rfl⟩ := Vector.exists_push (xs := s)
      rw [Sound.interp_mapM, Vector.mapM_push]
      apply Triple.bind
        (Q := fun us => ⌜VectorEvalRel us (init.map (Word.eval ρ.bool)) ρ⌝)
      case hx => simpa [Sound.interp_mapM] using ih (s := init)
      case hf =>
        intro us
        apply Triple.bind
          (Q := fun u => ⌜VectorEvalRel us (init.map (Word.eval ρ.bool)) ρ ∧
            u.Valid ρ ∧ u.eval ρ = last.eval ρ.bool⌝)
        case hx =>
          mvcgen
          case vc1 h => exact ⟨h.1, U.eval_eq_word_eval _ _ h.2 h.1⟩
        case hf =>
          intro u
          apply Triple.pure
          simp only [SPred.entails_nil]
          intro h
          intro i
          by_cases hi : i.val < n
          · simpa [Vector.getElem_push, hi, VectorEvalRel] using h.1 ⟨i, hi⟩
          · have hieq : i = Fin.last n := by ext; simp; omega
            subst i
            simpa using h.2

theorem permCircuit_sound {m : Vector (Word 32) 16}
    {s : Vector (Word 32) 8} :
    ⦃⌜True⌝⦄ Sound.interp ρ (permCircuit m s)
    ⦃ ⇓ out => ⌜VectorEvalRel out
      (perm (m.map (Word.eval ρ.bool)) (s.map (Word.eval ρ.bool))) ρ⌝⦄ := by
  unfold permCircuit
  rw [Sound.interp_bind]
  apply Triple.bind
    (Q := fun us => ⌜VectorEvalRel us (s.map (Word.eval ρ.bool)) ρ⌝)
  case hx => exact Vector.mapM_fromWord_sound
  case hf =>
    intro su
    mvcgen invariants
    · ⇓⟨cur, w⟩ => ⌜VectorEvalRel w
        (cur.prefix.foldl
          (fun w i => w.set! i ((m[i]!).eval ρ.bool)) default) ρ⌝
    · ⇓⟨cur, w⟩ => ⌜VectorEvalRel w
        (cur.prefix.foldl scheduleStepBV
          (([0:16].toList).foldl
            (fun w i => w.set! i ((m[i]!).eval ρ.bool)) default)) ρ⌝
    · ⇓⟨cur, r⟩ => ⌜RoundEvalRel r
        (cur.prefix.foldl
          (fun r i => roundStepBV i (scheduleBV (m.map (Word.eval ρ.bool))) r)
          ⟨(su[0]).eval ρ, (su[1]).eval ρ, (su[2]).eval ρ,
            (su[3]).eval ρ, (su[4]).eval ρ, (su[5]).eval ρ,
            (su[6]).eval ρ, (su[7]).eval ρ⟩) ρ⌝

@[spec 0]
theorem permCircuit_sound_frame {m : Vector (Word 32) 16}
    {s : Vector (Word 32) 8} (P : Prop) :
    ⦃⌜P⌝⦄ Sound.interp ρ (permCircuit m s)
    ⦃ ⇓ out => ⌜P ∧ VectorEvalRel out
      (perm (m.map (Word.eval ρ.bool)) (s.map (Word.eval ρ.bool))) ρ⌝⦄ := by
  mvcgen
  case vc1 => exact permCircuit_sound
  case vc2 => tauto

@[spec]
theorem Vector.mapM_fromWord_complete {s : Vector (Word width) n} :
    ⦃⌜True⌝ ⦄
      Complete.interp ρ (s.mapM U.fromWord)
    ⦃ ⇓ us => ⌜∀ i : Fin n,
      us[i].bits = s[i] ∧ us[i].Valid ρ⌝ ⦄ := by
  induction n with
  | zero =>
      rw [show s = #v[] from Vector.eq_empty]
      simp
      mvcgen
  | succ n ih =>
      obtain ⟨init, last, rfl⟩ := Vector.exists_push (xs := s)
      rw [Complete.interp_mapM, Vector.mapM_push]
      apply Triple.bind
        (Q := fun us => ⌜∀ i : Fin n,
          us[i].bits = init[i] ∧ us[i].Valid ρ⌝)
      case hx => simpa [Complete.interp_mapM] using ih (s := init)
      case hf =>
        intro us
        apply Triple.bind
          (Q := fun u => ⌜(∀ i : Fin n,
            us[i].bits = init[i] ∧ us[i].Valid ρ) ∧
            u.bits = last ∧ u.Valid ρ⌝)
        case hx => exact U.fromWord_complete_frame _
        case hf =>
          intro u
          apply Triple.pure
          simp only [SPred.entails_nil]
          intro hpair i
          rcases hpair with ⟨hinit, hlast⟩
          by_cases hi : i.val < n
          · simpa [Vector.getElem_push, hi] using hinit ⟨i, hi⟩
          · have hieq : i = Fin.last n := by
              apply Fin.ext
              simp
              omega
            subst i
            simpa using hlast

theorem permCircuit_complete {m : Vector (Word 32) 16}
    {s : Vector (Word 32) 8} :
    ⦃⌜True⌝ ⦄ Complete.interp ρ (permCircuit m s)
    ⦃ ⇓ out => ⌜∀ i : Fin 8, out[i].Valid ρ⌝ ⦄ := by
  unfold permCircuit
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun us => ⌜∀ i : Fin 8,
    us[i].bits = s[i] ∧ us[i].Valid ρ⌝)
  case hx => exact Vector.mapM_fromWord_complete
  case hf =>
    intro su
    mvcgen invariants
    · ⇓⟨_, w⟩ => ⌜∀ i : Fin 64, w[i].Valid ρ⌝
    case vc1 pref cur suff hsplit w hvalid out hout =>
      intro i
      rw [show w.set! cur out = w.setIfInBounds cur out by rfl]
      simp only [Fin.getElem_fin, Vector.getElem_setIfInBounds i.isLt]
      split
      · exact hout.2
      · exact hvalid i
    case vc2.h.pre =>
      simp
    case vc3 =>
      simp only [forIn_eq_forIn']
      mvcgen invariants
      · ⇓⟨_, w⟩ => ⌜∀ i : Fin 64, w[i].Valid ρ⌝
      · ⇓⟨_, st⟩ => ⌜st.1.Valid ρ ∧ st.2.1.Valid ρ ∧
          st.2.2.1.Valid ρ ∧ st.2.2.2.1.Valid ρ ∧
          st.2.2.2.2.1.Valid ρ ∧ st.2.2.2.2.2.1.Valid ρ ∧
          st.2.2.2.2.2.2.1.Valid ρ ∧ st.2.2.2.2.2.2.2.Valid ρ⌝
      case vc2 =>
        intro j
        apply U.allValid_set!
        · assumption
        · grind
      case vc10.hvalid =>
        intro u hu
        simp only [Array.mem_def, Array.toList_append, Array.toList_push,
          Array.toList_empty, List.mem_append, List.mem_cons,
          List.mem_singleton, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · grind
        · grind
        · grind
        · grind
        · exact U.valid_bitVec _
        · apply U.valid_getElem
          · assumption
      case vc11.hvalid =>
        intro u hu
        simp only [Array.mem_def, Array.toList_append, Array.toList_push,
          Array.toList_empty, List.mem_append, List.mem_cons,
          List.mem_singleton, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · grind
        · grind
        · grind
        · exact U.valid_bitVec _
        · apply U.valid_getElem
          · assumption
        · grind
        · grind
      case vc1.hvalid =>
        apply U.allValid_four
        · apply U.valid_getElem! <;> first | assumption | grind
        · grind
        · apply U.valid_getElem! <;> first | assumption | grind
        · grind
      case vc12 => grind
      case vc13.h.pre =>
        have hsu : ∀ i : Fin 8, su[i].Valid ρ := by
          apply U.valid_of_pointwise_right
          assumption
        repeat' apply And.intro
        all_goals apply U.valid_getElem hsu <;> omega
      case vc14.hvalid | vc15.hvalid | vc16.hvalid | vc17.hvalid |
          vc18.hvalid | vc19.hvalid | vc20.hvalid | vc21.hvalid =>
        apply U.allValid_pair
        · apply U.valid_getElem
          apply U.valid_of_pointwise_right
          assumption
        · grind
      case vc22.success =>
        intro i
        fin_cases i <;> simp_all
      all_goals simp_all only [not_or, not_not]

set_option maxHeartbeats 800000 in
theorem permCircuit_wf :
    WF.GadgetSpec
      (fun lv rv
          (l r : Vector (Word 32) 16 × Vector (Word 32) 8) =>
        WF.VectorRel
            (fun lv rv (l r : Word 32) => ∀ i : Fin 32,
              WF.LCEq lv.bool rv.bool l[i] r[i])
            lv rv l.1 r.1 ∧
          WF.VectorRel
            (fun lv rv (l r : Word 32) => ∀ i : Fin 32,
              WF.LCEq lv.bool rv.bool l[i] r[i])
            lv rv l.2 r.2)
      (fun x => permCircuit x.1 x.2)
      (WF.VectorRel U.WFRel) := by
  unfold WF.GadgetSpec
  intro left right
  unfold permCircuit
  simp only [U.sum2_eq_sumFixed, U.sum4_eq_sumFixed,
    U.sum6_eq_sumFixed, U.sum7_eq_sumFixed]
  apply WF.GadgetSpec.bind_rule U.mapM_fromWord_wf_full
  · intro leftVal rightVal h
    exact h.2
  · intro B sL sR hs
    wfgen' using [U.fromWord_wf_rel, U.sumFixed_wf,
      U.ch_wf, U.maj_wf]
    case inv1 => exact WF.VectorRel U.WFRel
    case vc1 =>
      intro leftVal rightVal _
      exact U.vector_default_wfRel leftVal rightVal
    case vc2 =>
      wfgen' using [U.fromWord_wf_rel]
      case vc1 =>
        rename_i hambient houtPost hB
        have hout := houtPost leftVal rightVal hB
        have hinv := hambient leftVal rightVal hout.1
        exact ⟨hinv.1, WF.VectorRel.set! hinv.2 hout.2 a⟩
      case vc2 =>
        rename_i hambient hP
        have hB := (hambient leftVal rightVal hP).1
        exact (hs leftVal rightVal hB).1.1 ⟨a, by grind⟩ i
    case vc3 =>
      simp only [forIn_eq_forIn']
      intro A wL wR hw
      apply WF.Rel.forIn'_range_map_yield_bind_rule
        (I := WF.VectorRel U.WFRel)
        (xs := [16:64]) (initL := wL) (initR := wR)
        (fL := fun i _ w => scheduleStep i w)
        (fR := fun i _ w => scheduleStep i w)
        (nextL := fun i _ w out => w.set! i out)
        (nextR := fun i _ w out => w.set! i out)
      case hinit =>
        intro leftVal rightVal hA
        exact (hw leftVal rightVal hA).2
      case hstep =>
        intro i hi P left right hP
        apply WF.GadgetSpec.bind_rule (scheduleStep_wf i hi)
        · intro leftVal rightVal h
          exact (hP leftVal rightVal h).2
        · intro C outL outR hout
          apply WF.Rel.pure
          intro leftVal rightVal hC
          have ho := hout leftVal rightVal hC
          have hin := hP leftVal rightVal ho.1
          exact ⟨hin.1, WF.VectorRel.set! hin.2 ho.2 i⟩
      case hcont =>
        wfgen' using [U.fromWord_wf_rel, U.sumFixed_wf,
          U.ch_wf, U.maj_wf]

theorem permCirc'_wf :
    WF.GadgetSpec
      (WF.VectorRel fun lv rv (l r : LC Bool) =>
        WF.LCEq lv.bool rv.bool l r)
      permCirc'
      (WF.VectorRel fun lv rv (l r : LC Bool) =>
        WF.LCEq lv.bool rv.bool l r) := by
  unfold WF.GadgetSpec
  intro left right
  unfold permCirc'
  apply WF.GadgetSpec.bind_rule permCircuit_wf
  · intro lv rv h
    constructor
    · intro wi bi
      exact h ⟨wi.val * 32 + bi.val, by omega⟩
    · intro si bi
      exact h ⟨512 + si.val * 32 + bi.val, by omega⟩
  · intro A outL outR hout
    apply WF.Rel.pure
    intro lv rv hA
    have h := hout lv rv hA
    intro i
    exact (h.2 ⟨i.val / 32, by omega⟩).2 ⟨i.val % 32, by omega⟩

theorem permCirc'_complete_triple (inputWires : Vector (LC Bool) 768) :
    ⦃⌜True⌝⦄ Complete.interp ρ (permCirc' inputWires)
    ⦃ ⇓ _ => ⌜True⌝⦄ := by
  unfold permCirc'
  rw [Complete.interp_bind]
  apply Triple.bind
    (Q := fun out => ⌜∀ i : Fin 8, out[i].Valid ρ⌝)
  case hx => exact permCircuit_complete
  case hf =>
    intro out
    mvcgen

theorem eval_inputWord (values : Vector Bool 768) (valuation : Nat → Bool)
    (hvalues : ∀ i : Fin 768, valuation i.val = values[i])
    (base : Nat) (hbase : base + 32 ≤ 768) :
    Word.eval valuation
      { bitsLE := Vector.ofFn fun bi => ({base + bi.val} : LC Bool) } =
      BitVec.ofNat 32 (Nat.ofBits fun bi => values[base + bi.val]) := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_ofFnLE, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _)]
  apply congrArg Nat.ofBits
  funext bi
  simp only [Vector.getElem_ofFn, LC.eval_singleton]
  exact hvalues ⟨base + bi.val, by omega⟩

theorem messageWords_eval (values : Vector Bool 768) (valuation : Nat → Bool)
    (hvalues : ∀ i : Fin 768, valuation i.val = values[i]) :
    (Vector.ofFn fun wi : Fin 16 =>
      Word.mk (Vector.ofFn fun bi : Fin 32 =>
        ({wi.val * 32 + bi.val} : LC Bool))).map (Word.eval valuation) =
    Vector.ofFn fun wi : Fin 16 =>
      BitVec.ofNat 32 (Nat.ofBits fun bi : Fin 32 =>
        values[wi.val * 32 + bi.val]) := by
  apply Vector.ext
  intro wi hwi
  simp only [Vector.map_getElem, Vector.getElem_ofFn]
  exact eval_inputWord values valuation hvalues (wi * 32) (by omega)

theorem stateWords_eval (values : Vector Bool 768) (valuation : Nat → Bool)
    (hvalues : ∀ i : Fin 768, valuation i.val = values[i]) :
    (Vector.ofFn fun si : Fin 8 =>
      Word.mk (Vector.ofFn fun bi : Fin 32 =>
        ({512 + si.val * 32 + bi.val} : LC Bool))).map (Word.eval valuation) =
    Vector.ofFn fun si : Fin 8 =>
      BitVec.ofNat 32 (Nat.ofBits fun bi : Fin 32 =>
        values[512 + si.val * 32 + bi.val]) := by
  apply Vector.ext
  intro si hsi
  simp only [Vector.map_getElem, Vector.getElem_ofFn]
  exact eval_inputWord values valuation hvalues (512 + si * 32) (by omega)

theorem flatten_eval {out : Vector (U 32) 8}
    {value : Vector (BitVec 32) 8} (h : VectorEvalRel out value ρ) :
    (Vector.ofFn fun i : Fin 256 =>
      out[i.val / 32].bits.bitsLE[i.val % 32]).map
        (fun x => x.eval ρ.bool) =
      Vector.ofFn fun i : Fin 256 =>
        value[i.val / 32].toNat.testBit (i.val % 32) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.map_getElem, Vector.getElem_ofFn]
  have hu := h ⟨i / 32, by omega⟩
  have heval := U.eval_eq_ofFnLE _ hu.1
  have hbit := congrArg (fun x : BitVec 32 => x[i % 32]'(by omega)) heval
  rw [hu.2] at hbit
  simpa only [BitVec.getElem_ofFnLE,
    BitVec.getElem_eq_testBit_toNat] using hbit.symm

theorem permCirc'_sound_triple (inputs : Vector Bool 768)
    (wit : Nat → Bool)
    (hinputs : ∀ i : Fin 768, wit i.val = inputs[i])
    (cs : Semantics.CS) :
    ⦃⌜True⌝⦄ Sound.interp (Sound.csValuation cs wit)
      (permCirc' (Vector.ofFn fun i => ({i.val} : LC Bool)))
    ⦃ ⇓ out => ⌜out.map (fun x => x.eval wit) = perm' inputs⌝⦄ := by
  unfold permCirc'
  rw [Sound.interp_bind]
  apply Triple.bind
    (Q := fun out => ⌜VectorEvalRel out
      (perm
        ((Vector.ofFn fun wi : Fin 16 => Word.mk (Vector.ofFn fun bi : Fin 32 =>
          ({wi.val * 32 + bi.val} : LC Bool))).map
            (Word.eval (Sound.csValuation cs wit).bool))
        ((Vector.ofFn fun si : Fin 8 => Word.mk (Vector.ofFn fun bi : Fin 32 =>
          ({512 + si.val * 32 + bi.val} : LC Bool))).map
            (Word.eval (Sound.csValuation cs wit).bool)))
      (Sound.csValuation cs wit)⌝)
  case hx => exact permCircuit_sound
  case hf =>
    intro out
    apply Triple.pure
    simp only [SPred.entails_nil]
    intro hout
    rw [flatten_eval hout]
    unfold perm'
    simp only [Sound.csValuation]
    rw [messageWords_eval inputs wit hinputs,
      stateWords_eval inputs wit hinputs]

theorem permCirc'_complete : ∀ inputs, ∃ wit,
    Semantics.Witgen.runWithInputs permCirc' inputs = some wit ∧
    (sha256CS.2.satisfies (wit[·]!)) := by
  intro inputs
  apply Complete.adequate
  · exact permCirc'_wf
  · exact permCirc'_complete_triple _

theorem permCirc'_sound (inp : Vector Bool 768) (wit : Nat → Bool)
    (hWit : ∀ i : Fin 768, inp[i] = wit i.val) :
    sha256CS.2.satisfies wit →
      sha256CS.1.map (fun i => i.eval wit) = perm' inp := by
  intro hp
  apply Sound.adequate
    (circ := permCirc')
    (P := fun i o => o.map (·.eval wit) = perm' inp)
  · exact permCirc'_sound_triple inp wit (fun i => (hWit i).symm) _
  · exact fun i => (hWit i).symm
  · exact hp

end Freigen.F2Z.Examples
