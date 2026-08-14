import Freigen.F2Z.Examples.Sha256.Impl

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

theorem U.eval_bitVec (w : BitVec n) : ((w : U n).eval ρ) = w := by
  rw [U.eval_eq_ofFnLE _ (U.valid_bitVec w)]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_ofFnLE, Fin.getElem_fin, Vector.getElem_ofFn]
  change LC.eval ρ.bool
    ({ constant := w[i], coeffs := ∅, ne_zero := by simp } : LC Bool) = w[i]
  change w[i] + (∅ : Std.ExtTreeMap Nat Bool).foldMap
    (fun i c => c * ρ.bool i) = w[i]
  have hempty : (∅ : Std.ExtTreeMap Nat Bool).foldMap
      (fun i c => c * ρ.bool i) = 0 := Std.ExtTreeMap.foldMap_empty _
  rw [hempty, add_zero]

theorem U.eval_default : (default : U n).eval ρ = 0 := by
  rw [U.eval_eq_ofFnLE _ U.valid_default]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_ofFnLE]
  change LC.eval ρ.bool (Vector.replicate n (0 : LC Bool))[i] = (0 : BitVec n)[i]
  simp only [Vector.getElem_replicate, LC.eval_zero]
  have hz : (0 : BitVec n) = BitVec.ofNat n 0 := rfl
  rw [hz]
  rw [BitVec.getElem_eq_testBit_toNat]
  rw [BitVec.toNat_ofNat, Nat.zero_mod]
  have hzero : (0 : Bool) = false := by rfl
  rw [hzero]
  simp [Nat.testBit]

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

theorem U.sumPair_eval {out x y : U n} {xv yv : BitVec n}
    (hout : out.Valid ρ ∧ out.eval ρ =
      (#[x, y].map (fun u => u.eval ρ)).sum)
    (hx : x.eval ρ = xv) (hy : y.eval ρ = yv) :
    out.Valid ρ ∧ out.eval ρ = xv + yv := by
  refine ⟨hout.1, ?_⟩
  rw [hout.2, ← Array.sum_toList]
  simp only [Array.toList_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, hx, hy]
  simp

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

instance instInhabitedWord : Inhabited (Word n) :=
  ⟨{ bitsLE := Vector.replicate n (0 : LC Bool) }⟩

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
  MProd (U 32) (MProd (U 32) (MProd (U 32) (MProd (U 32)
    (MProd (U 32) (MProd (U 32) (MProd (U 32) (U 32)))))))

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

def roundStepBounded (i : Nat) (hi : i ∈ [0:64])
    (w : Vector (U 32) 64) (r : RoundState) : Circuit RoundState := do
  let S1 ← U.fromWord $ r.2.2.2.2.1.bits.rotateRight 6 ^^^
    r.2.2.2.2.1.bits.rotateRight 11 ^^^ r.2.2.2.2.1.bits.rotateRight 25
  let ch ← U.ch r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1
  let S0 ← U.fromWord $ r.1.bits.rotateRight 2 ^^^
    r.1.bits.rotateRight 13 ^^^ r.1.bits.rotateRight 22
  let maj ← U.maj r.1 r.2.1 r.2.2.1
  let newE ← U.sumFixed #v[
    r.2.2.2.1, r.2.2.2.2.2.2.2, S1, ch, k[i], w[i]]
  let newA ← U.sumFixed #v[
    r.2.2.2.2.2.2.2, S1, ch, k[i], w[i], S0, maj]
  pure ⟨newA, r.1, r.2.1, r.2.2.1, newE,
    r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

theorem roundStepBounded_eq (i : Nat) (hi : i ∈ [0:64])
    (w : Vector (U 32) 64) (r : RoundState) :
    roundStepBounded i hi w r = roundStep i w r := by
  simp only [roundStepBounded, roundStep,
    getElem!_pos k i (by grind), getElem!_pos w i (by grind)]

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

def permScheduleStepBV (i : Nat) (w : Vector (BitVec 32) 64) :=
  w.set! i
    (w[i - 16]! +
      (w[i - 15]!.rotateRight 7 ^^^ w[i - 15]!.rotateRight 18 ^^^
        (w[i - 15]! >>> 3)) + w[i - 7]! +
      (w[i - 2]!.rotateRight 17 ^^^ w[i - 2]!.rotateRight 19 ^^^
        (w[i - 2]! >>> 10)))

abbrev MBVState :=
  MProd (BitVec 32) (MProd (BitVec 32) (MProd (BitVec 32)
    (MProd (BitVec 32) (MProd (BitVec 32) (MProd (BitVec 32)
      (MProd (BitVec 32) (BitVec 32)))))))

def MBVState.toBV (r : MBVState) : BVState :=
  ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1,
    r.2.2.2.2.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2⟩

def addStateBV (s : Vector (BitVec 32) 8) (r : BVState) :
    Vector (BitVec 32) 8 :=
  #v[s[0] + r.1, s[1] + r.2.1, s[2] + r.2.2.1,
    s[3] + r.2.2.2.1, s[4] + r.2.2.2.2.1,
    s[5] + r.2.2.2.2.2.1, s[6] + r.2.2.2.2.2.2.1,
    s[7] + r.2.2.2.2.2.2.2]

theorem addStateBV_mprod (s : Vector (BitVec 32) 8) (r : MBVState)
    (v : BVState) (h : r.toBV = v) :
    #v[s[0] + r.1, s[1] + r.2.1, s[2] + r.2.2.1,
      s[3] + r.2.2.2.1, s[4] + r.2.2.2.2.1,
      s[5] + r.2.2.2.2.2.1, s[6] + r.2.2.2.2.2.2.1,
      s[7] + r.2.2.2.2.2.2.2] = addStateBV s v := by
  subst v
  rfl

def permRoundStepBV (i : Nat) (hi : i ∈ [0:64])
    (w : Vector (BitVec 32) 64) (r : MBVState) : MBVState :=
  ⟨r.2.2.2.2.2.2.2 +
      (r.2.2.2.2.1.rotateRight 6 ^^^ r.2.2.2.2.1.rotateRight 11 ^^^
        r.2.2.2.2.1.rotateRight 25) +
      chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1 + k[i] + w[i] +
      ((r.1.rotateRight 2 ^^^ r.1.rotateRight 13 ^^^ r.1.rotateRight 22) +
        majBV r.1 r.2.1 r.2.2.1),
    r.1, r.2.1, r.2.2.1,
    r.2.2.2.1 + (r.2.2.2.2.2.2.2 +
      (r.2.2.2.2.1.rotateRight 6 ^^^ r.2.2.2.2.1.rotateRight 11 ^^^
        r.2.2.2.2.1.rotateRight 25) +
      chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1 + k[i] + w[i]),
    r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

def permRoundStepBVUnchecked (i : Nat) (w : Vector (BitVec 32) 64)
    (r : MBVState) : MBVState :=
  ⟨r.2.2.2.2.2.2.2 +
      (r.2.2.2.2.1.rotateRight 6 ^^^ r.2.2.2.2.1.rotateRight 11 ^^^
        r.2.2.2.2.1.rotateRight 25) +
      chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1 + k[i]! + w[i]! +
      ((r.1.rotateRight 2 ^^^ r.1.rotateRight 13 ^^^ r.1.rotateRight 22) +
        majBV r.1 r.2.1 r.2.2.1),
    r.1, r.2.1, r.2.2.1,
    r.2.2.2.1 + (r.2.2.2.2.2.2.2 +
      (r.2.2.2.2.1.rotateRight 6 ^^^ r.2.2.2.2.1.rotateRight 11 ^^^
        r.2.2.2.2.1.rotateRight 25) +
      chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1 + k[i]! + w[i]!),
    r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

theorem permScheduleStepBV_eq (i : Nat) (w : Vector (BitVec 32) 64) :
    permScheduleStepBV i w = scheduleStepBV i w := by
  unfold permScheduleStepBV scheduleStepBV
  congr 1 <;> ac_rfl

theorem permRoundStepBV_eq (i : Nat) (hi : i ∈ [0:64])
    (w : Vector (BitVec 32) 64) (r : MBVState) :
    (permRoundStepBV i hi w r).toBV = roundStepBV i w r.toBV := by
  unfold permRoundStepBV MBVState.toBV roundStepBV
  simp only [getElem!_pos k i (by grind), getElem!_pos w i (by grind)]
  congr 1 <;> ac_rfl

theorem permRoundStepBV_eq_unchecked (i : Nat) (hi : i ∈ [0:64])
    (w : Vector (BitVec 32) 64) (r : MBVState) :
    permRoundStepBV i hi w r = permRoundStepBVUnchecked i w r := by
  unfold permRoundStepBV permRoundStepBVUnchecked
  simp only [getElem!_pos k i (by grind), getElem!_pos w i (by grind)]

theorem permRoundStepBVUnchecked_toBV (i : Nat)
    (w : Vector (BitVec 32) 64) (r : MBVState) :
    (permRoundStepBVUnchecked i w r).toBV = roundStepBV i w r.toBV := by
  unfold permRoundStepBVUnchecked MBVState.toBV roundStepBV
  congr 1 <;> ac_rfl

theorem MBVState.toBV_fold_permRoundStepBV (xs : List Nat)
    (w : Vector (BitVec 32) 64) (r : MBVState) :
    (xs.foldl (fun r i => permRoundStepBVUnchecked i w r) r).toBV =
      xs.foldl (fun r i => roundStepBV i w r) r.toBV := by
  induction xs generalizing r with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih, permRoundStepBVUnchecked_toBV]

/-- Proof-facing copy of the executable permutation.  The public golden model is
declared in `Correctness`; keeping this private-facing name avoids an import cycle. -/
def permModel (m : Vector (BitVec 32) 16)
    (s : Vector (BitVec 32) 8) : Vector (BitVec 32) 8 := Id.run $ do
  let mut w := Vector.replicate 64 (0 : BitVec 32)
  for h:i in [0:16] do
    w := w.set! i m[i]
  for i in [16:64] do
    let s0 := (w[i-15]!.rotateRight 7) ^^^
      (w[i-15]!.rotateRight 18) ^^^ (w[i-15]! >>> 3)
    let s1 := (w[i-2]!.rotateRight 17) ^^^
      (w[i-2]!.rotateRight 19) ^^^ (w[i-2]! >>> 10)
    w := w.set! i (w[i-16]! + s0 + w[i-7]! + s1)
  let mut a := s[0]
  let mut b := s[1]
  let mut c := s[2]
  let mut d := s[3]
  let mut e := s[4]
  let mut f := s[5]
  let mut g := s[6]
  let mut h := s[7]

  for h:i in [0:64] do
    let S1 := (e.rotateRight 6) ^^^ (e.rotateRight 11) ^^^
      (e.rotateRight 25)
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := h + S1 + ch + k[i] + w[i]
    let S0 := (a.rotateRight 2) ^^^ (a.rotateRight 13) ^^^
      (a.rotateRight 22)
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 := S0 + maj

    h := g
    g := f
    f := e
    e := d + temp1
    d := c
    c := b
    b := a
    a := temp1 + temp2

  #v[s[0] + a, s[1] + b, s[2] + c, s[3] + d,
    s[4] + e, s[5] + f, s[6] + g, s[7] + h]

theorem List.id_forIn'_yield (xs : List α) (init : β) (f : β → α → β) :
    (forIn' xs init fun x _ acc =>
      (pure (ForInStep.yield (f acc x)) : Id (ForInStep β))) =
    (pure (xs.foldl f init) : Id β) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      rw [List.forIn'_cons]
      change (forIn' xs (f init x) fun x _ acc =>
        (pure (ForInStep.yield (f acc x)) : Id (ForInStep β))) = _
      exact ih (f init x)

theorem Range.id_forIn'_yield (xs : Std.Legacy.Range) (init : β)
    (f : β → Nat → β) :
    (forIn' xs init fun i _ acc =>
      (pure (ForInStep.yield (f acc i)) : Id (ForInStep β))) =
    (pure (xs.toList.foldl f init) : Id β) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact List.id_forIn'_yield _ _ _

theorem Range.id_forIn'_yield_congr (xs : Std.Legacy.Range) (init : β)
    (f : (i : Nat) → i ∈ xs → β → β) (g : β → Nat → β)
    (h : ∀ i hi acc, f i hi acc = g acc i) :
    (forIn' xs init fun i hi acc =>
      (pure (ForInStep.yield (f i hi acc)) : Id (ForInStep β))) =
    (pure (xs.toList.foldl g init) : Id β) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  calc
    (forIn' xs.toList init fun i hi acc =>
      (pure (ForInStep.yield (f i (xs.mem_of_mem_range' hi) acc)) :
        Id (ForInStep β))) =
        forIn' xs.toList init (fun i _ acc =>
          pure (ForInStep.yield (g acc i))) := by
            apply List.forIn'_congr rfl rfl
            intro i hi acc
            rw [h]
    _ = pure (xs.toList.foldl g init) := List.id_forIn'_yield _ _ _

theorem permModel_eq_steps (m : Vector (BitVec 32) 16)
    (s : Vector (BitVec 32) 8) :
    permModel m s =
      let w := scheduleBV m
      let r := ([0:64].toList).foldl (fun r i => roundStepBV i w r)
        ⟨s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]⟩
      addStateBV s r := by
  unfold permModel scheduleBV
  simp only [Id.run, forIn_eq_forIn', pure_bind]
  have hinit :
      (forIn' [0:16] (Vector.replicate 64 (0 : BitVec 32)) fun i hi w =>
        (pure (ForInStep.yield (w.set! i m[i])) : Id _)) =
      pure (([0:16].toList).foldl (fun w i => w.set! i m[i]!) default) := by
    apply Range.id_forIn'_yield_congr
    intro i hi w
    rw [getElem!_pos m i (by grind)]
  conv_lhs =>
    enter [1]
    rw [hinit]
  simp only [pure_bind]
  let init := ([0:16].toList).foldl (fun w i => w.set! i m[i]!)
    (default : Vector (BitVec 32) 64)
  have hschedule :
      (forIn' [16:64] init fun i _ w =>
        (pure (ForInStep.yield (permScheduleStepBV i w)) : Id _)) =
      pure (([16:64].toList).foldl (fun w i => scheduleStepBV i w) init) := by
    apply Range.id_forIn'_yield_congr
    intro i hi w
    exact permScheduleStepBV_eq i w
  have hscheduleRaw := hschedule
  dsimp only [permScheduleStepBV] at hscheduleRaw
  conv_lhs =>
    enter [1]
    rw [hscheduleRaw]
  simp only [pure_bind]
  let w := ([16:64].toList).foldl (fun w i => scheduleStepBV i w) init
  have hround :
      (forIn' [0:64] ⟨s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]⟩
        fun i hi r => (pure (ForInStep.yield (permRoundStepBV i hi w r)) : Id _)) =
      pure (([0:64].toList).foldl
        (fun r i => permRoundStepBVUnchecked i w r)
        ⟨s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]⟩) := by
    apply Range.id_forIn'_yield_congr
    intro i hi r
    exact permRoundStepBV_eq_unchecked i hi w r
  have hroundRaw := hround
  dsimp only [permRoundStepBV, chBV, majBV] at hroundRaw
  dsimp only [w] at hroundRaw
  conv_lhs =>
    enter [1]
    exact hroundRaw
  simp only [pure_bind]
  have hfold := MBVState.toBV_fold_permRoundStepBV ([0:64].toList) w
    ⟨s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]⟩
  dsimp only [w, init] at hfold ⊢
  exact addStateBV_mprod s _ _ hfold

def permModel' (input : Vector Bool 768) : Vector Bool 256 :=
  let m := Vector.ofFn fun i => BitVec.ofNat 32 $
    Nat.ofBits fun (j : Fin 32) => input[i.val * 32 + j.val]
  let s := Vector.ofFn fun i => BitVec.ofNat 32 $
    Nat.ofBits fun (j : Fin 32) => input[512 + i.val * 32 + j.val]
  let out := permModel m s
  Vector.ofFn fun i => out[i.val / 32].toNat.testBit (i % 32)

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

@[spec]
theorem scheduleStep_sound (i : Nat) (hi : i ∈ [16:64])
    {w : Vector (U 32) 64} (hvalid : ∀ j : Fin 64, w[j].Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (scheduleStep i w)
    ⦃ ⇓ out => ⌜out.Valid ρ ∧ out.eval ρ =
      scheduleValueBV i (w.map (fun u => u.eval ρ))⌝⦄ := by
  unfold scheduleStep scheduleValueBV
  mvcgen
  case vc1 =>
    rename_i s0 hs0 s1 hs1 out
    intro houtValid houtEval
    refine ⟨houtValid, ?_⟩
    rw [houtEval]
    have heval0 := U.eval_eq_word_eval s0 _ hs0.2 hs0.1
    have heval1 := U.eval_eq_word_eval s1 _ hs1.2 hs1.1
    simp only [Word.eval_xor, Word.eval_rotateRight,
      Word.eval_shiftRight] at heval0 heval1
    rw [Word.eval_rotateRight _ _ 7 (by decide),
      Word.eval_rotateRight _ _ 18 (by decide)] at heval0
    rw [Word.eval_rotateRight _ _ 17 (by decide),
      Word.eval_rotateRight _ _ 19 (by decide)] at heval1
    have heval15 := U.eval_eq_word_eval w[i - 15]! _
      (U.valid_getElem! hvalid (by grind)) rfl
    have heval2 := U.eval_eq_word_eval w[i - 2]! _
      (U.valid_getElem! hvalid (by grind)) rfl
    rw [← heval15] at heval0
    rw [← heval2] at heval1
    simp [heval0, heval1,
      Vector.getElem!_map w (fun u => u.eval ρ) (i - 16) (by grind),
      Vector.getElem!_map w (fun u => u.eval ρ) (i - 15) (by grind),
      Vector.getElem!_map w (fun u => u.eval ρ) (i - 7) (by grind),
      Vector.getElem!_map w (fun u => u.eval ρ) (i - 2) (by grind)]
    ac_rfl
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

theorem RoundEvalRel.step {r : RoundState} {v : BVState}
    (hr : RoundEvalRel r v ρ) (i : Nat)
    {wi : U 32} {wv : Vector (BitVec 32) 64}
    (hwi : wi.eval ρ = wv[i]!)
    {S1 ch S0 maj newE newA : U 32}
    (hS1 : S1.bits = r.2.2.2.2.1.bits.rotateRight 6 ^^^
      r.2.2.2.2.1.bits.rotateRight 11 ^^^
      r.2.2.2.2.1.bits.rotateRight 25 ∧ S1.Valid ρ)
    (hch : ch.Valid ρ ∧ ch.eval ρ =
      chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
        (r.2.2.2.2.2.2.1.eval ρ))
    (hS0 : S0.bits = r.1.bits.rotateRight 2 ^^^
      r.1.bits.rotateRight 13 ^^^ r.1.bits.rotateRight 22 ∧ S0.Valid ρ)
    (hmaj : maj.Valid ρ ∧ maj.eval ρ =
      majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ))
    (hnewE : newE.Valid ρ ∧ newE.eval ρ =
      (#[r.2.2.2.1, r.2.2.2.2.2.2.2, S1, ch, (k[i]! : U 32), wi].map
        (fun u => u.eval ρ)).sum)
    (hnewA : newA.Valid ρ ∧ newA.eval ρ =
      (#[r.2.2.2.2.2.2.2, S1, ch, (k[i]! : U 32), wi, S0, maj].map
        (fun u => u.eval ρ)).sum) :
    RoundEvalRel ⟨newA, r.1, r.2.1, r.2.2.1, newE,
      r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩
      (roundStepBV i wv v) ρ := by
  have hS1eval := U.eval_eq_word_eval S1 _ hS1.2 hS1.1
  have hS0eval := U.eval_eq_word_eval S0 _ hS0.2 hS0.1
  simp only [Word.eval_xor,
    Word.eval_rotateRight (n := 32) _ _ 6 (by decide),
    Word.eval_rotateRight (n := 32) _ _ 11 (by decide),
    Word.eval_rotateRight (n := 32) _ _ 25 (by decide)] at hS1eval
  simp only [Word.eval_xor,
    Word.eval_rotateRight (n := 32) _ _ 2 (by decide),
    Word.eval_rotateRight (n := 32) _ _ 13 (by decide),
    Word.eval_rotateRight (n := 32) _ _ 22 (by decide)] at hS0eval
  rcases hr with ⟨haV, haE, hbV, hbE, hcV, hcE, hdV, hdE,
    heV, heE, hfV, hfE, hgV, hgE, hhV, hhE⟩
  have heWord := U.eval_eq_word_eval r.2.2.2.2.1 _ heV rfl
  have haWord := U.eval_eq_word_eval r.1 _ haV rfl
  rw [← heWord, heE] at hS1eval
  rw [← haWord, haE] at hS0eval
  unfold RoundEvalRel
  simp only [roundStepBV, Prod.fst, Prod.snd]
  refine ⟨hnewA.1, ?_, haV, haE, hbV, hbE, hcV, hcE,
    hnewE.1, ?_, heV, heE, hfV, hfE, hgV, hgE⟩
  · rw [hnewA.2, ← Array.sum_toList]
    simp only [Array.toList_map, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hS1eval, hS0eval, hch.2, hmaj.2,
      U.eval_bitVec, hwi, haE, hbE, hcE,
      heE, hfE, hgE, hhE]
    ac_rfl

  · rw [hnewE.2, ← Array.sum_toList]
    simp only [Array.toList_map, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hS1eval, hch.2, U.eval_bitVec, hwi,
      hdE, heE, hfE, hgE, hhE]
    ac_rfl

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
    have hwi : w[i]!.Valid ρ := U.valid_getElem! hw (by grind)
    have hki : ((k[i]!) : U 32).Valid ρ := U.valid_bitVec _
    intro j
    fin_cases j <;> simp_all [RoundEvalRel]
  case vc9 =>
    rename_i S1 hS1 ch hch S0 hS0 maj hmaj newE hnewE newA hnewA
    apply RoundEvalRel.step hr i
      (Vector.getElem!_map w (fun u => u.eval ρ) i (by grind)).symm
      hS1 hch hS0 hmaj hnewE hnewA

def VectorEvalRel (us : Vector (U n) m) (vs : Vector (BitVec n) m)
    (ρ : WF.Valuation) : Prop :=
  ∀ i : Fin m, us[i].Valid ρ ∧ us[i].eval ρ = vs[i]

theorem RoundEvalRel.stepIndexed {r : RoundState} {v : BVState}
    {w : Vector (U 32) 64} {wv : Vector (BitVec 32) 64}
    (hr : RoundEvalRel r v ρ) (hw : VectorEvalRel w wv ρ)
    (i : Nat) (hi : i < 64)
    {S1 ch S0 maj newE newA : U 32}
    (hS1 : S1.bits = r.2.2.2.2.1.bits.rotateRight 6 ^^^
      r.2.2.2.2.1.bits.rotateRight 11 ^^^
      r.2.2.2.2.1.bits.rotateRight 25 ∧ S1.Valid ρ)
    (hch : ch.Valid ρ ∧ ch.eval ρ =
      chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
        (r.2.2.2.2.2.2.1.eval ρ))
    (hS0 : S0.bits = r.1.bits.rotateRight 2 ^^^
      r.1.bits.rotateRight 13 ^^^ r.1.bits.rotateRight 22 ∧ S0.Valid ρ)
    (hmaj : maj.Valid ρ ∧ maj.eval ρ =
      majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ))
    (hnewE : newE.Valid ρ ∧ newE.eval ρ =
      (#[r.2.2.2.1, r.2.2.2.2.2.2.2, S1, ch, (k[i] : U 32), w[i]].map
        (fun u => u.eval ρ)).sum)
    (hnewA : newA.Valid ρ ∧ newA.eval ρ =
      (#[r.2.2.2.2.2.2.2, S1, ch, (k[i] : U 32), w[i], S0, maj].map
        (fun u => u.eval ρ)).sum) :
    RoundEvalRel ⟨newA, r.1, r.2.1, r.2.2.1, newE,
      r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩
      (roundStepBV i wv v) ρ := by
  apply RoundEvalRel.step hr i
  · simpa only [getElem!_pos w i hi, getElem!_pos wv i hi,
      Fin.getElem_fin] using (hw ⟨i, hi⟩).2
  · exact hS1
  · exact hch
  · exact hS0
  · exact hmaj
  · simpa only [getElem!_pos k i hi, getElem!_pos w i hi,
      Fin.getElem_fin] using hnewE
  · simpa only [getElem!_pos k i hi, getElem!_pos w i hi,
      Fin.getElem_fin] using hnewA

theorem RoundEvalRel.ofVector {us : Vector (U 32) 8}
    {vs : Vector (BitVec 32) 8} (h : VectorEvalRel us vs ρ) :
    RoundEvalRel ⟨us[0], us[1], us[2], us[3], us[4], us[5], us[6], us[7]⟩
      ⟨vs[0], vs[1], vs[2], vs[3], vs[4], vs[5], vs[6], vs[7]⟩ ρ := by
  exact ⟨(h 0).1, (h 0).2, (h 1).1, (h 1).2,
    (h 2).1, (h 2).2, (h 3).1, (h 3).2,
    (h 4).1, (h 4).2, (h 5).1, (h 5).2,
    (h 6).1, (h 6).2, (h 7).1, (h 7).2⟩

theorem VectorEvalRel.allValid8 {us : Vector (U n) 8}
    {vs : Vector (BitVec n) 8} (h : VectorEvalRel us vs ρ) :
    us[0].Valid ρ ∧ us[1].Valid ρ ∧ us[2].Valid ρ ∧ us[3].Valid ρ ∧
      us[4].Valid ρ ∧ us[5].Valid ρ ∧ us[6].Valid ρ ∧ us[7].Valid ρ :=
  ⟨(h 0).1, (h 1).1, (h 2).1, (h 3).1,
    (h 4).1, (h 5).1, (h 6).1, (h 7).1⟩

theorem VectorEvalRel.set! (h : VectorEvalRel us vs ρ)
    (hx : x.Valid ρ ∧ x.eval ρ = y) (i : Nat) :
    VectorEvalRel (us.set! i x) (vs.set! i y) ρ := by
  intro j
  rw [show us.set! i x = us.setIfInBounds i x by rfl,
    show vs.set! i y = vs.setIfInBounds i y by rfl]
  change (us.setIfInBounds i x)[j.val].Valid ρ ∧
    (us.setIfInBounds i x)[j.val].eval ρ =
      (vs.setIfInBounds i y)[j.val]
  rw [Vector.getElem_setIfInBounds (xs := us) (x := x) j.isLt,
    Vector.getElem_setIfInBounds (xs := vs) (x := y) j.isLt]
  split
  · exact hx
  · exact h j

theorem VectorEvalRel.getElem! {us : Vector (U n) len}
    {vs : Vector (BitVec n) len} (h : VectorEvalRel us vs ρ)
    (i : Nat) (hi : i < len) :
    us[i]!.Valid ρ ∧ us[i]!.eval ρ = vs[i]! := by
  rw [getElem!_pos us i hi, getElem!_pos vs i hi]
  exact h ⟨i, hi⟩

def messageEvalBV (m : Vector (Word 32) 16) (ρ : WF.Valuation) :=
  m.map (Word.eval ρ.bool)

def scheduleEvalBV (m : Vector (Word 32) 16) (ρ : WF.Valuation) :=
  scheduleBV (messageEvalBV m ρ)

theorem List.foldl_congr_of_mem {xs : List α} {f g : β → α → β}
    (h : ∀ x ∈ xs, ∀ acc, f acc x = g acc x) (init : β) :
    xs.foldl f init = xs.foldl g init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h x (by simp) init]
      apply ih
      intro y hy
      exact h y (by simp [hy])

theorem scheduleBV_eq_raw (m : Vector (Word 32) 16) (ρ : WF.Valuation) :
    scheduleBV (m.map (Word.eval ρ.bool)) =
      (([16:64].toList).foldl (fun w i => scheduleStepBV i w)
        (([0:16].toList).foldl
          (fun w i => w.set! i ((m[i]!).eval ρ.bool)) default)) := by
  unfold scheduleBV
  apply congrArg (([16:64].toList).foldl fun w i => scheduleStepBV i w)
  apply List.foldl_congr_of_mem
  intro i hi w
  have hi' : i < 16 := by grind
  rw [Vector.getElem!_map m (Word.eval ρ.bool) i hi']

def initialRoundEvalBV (su : Vector (U 32) 8) (ρ : WF.Valuation) : BVState :=
  ⟨(su[0]).eval ρ, (su[1]).eval ρ, (su[2]).eval ρ,
    (su[3]).eval ρ, (su[4]).eval ρ, (su[5]).eval ρ,
    (su[6]).eval ρ, (su[7]).eval ρ⟩

theorem RoundEvalRel.ofVectorEval {us : Vector (U 32) 8}
    {vs : Vector (BitVec 32) 8} (h : VectorEvalRel us vs ρ) :
    RoundEvalRel ⟨us[0], us[1], us[2], us[3], us[4], us[5], us[6], us[7]⟩
      (initialRoundEvalBV us ρ) ρ := by
  exact ⟨(h 0).1, rfl, (h 1).1, rfl, (h 2).1, rfl, (h 3).1, rfl,
    (h 4).1, rfl, (h 5).1, rfl, (h 6).1, rfl, (h 7).1, rfl⟩

def roundsEvalBV (xs : List Nat) (m : Vector (Word 32) 16)
    (su : Vector (U 32) 8) (ρ : WF.Valuation) : BVState :=
  xs.foldl (fun r i => roundStepBV i
      (scheduleBV (m.map (Word.eval ρ.bool))) r)
    (initialRoundEvalBV su ρ)

@[simp]
theorem roundsEvalBV_nil : roundsEvalBV [] m su ρ = initialRoundEvalBV su ρ :=
  rfl

theorem roundsEvalBV_append_singleton :
    roundsEvalBV (xs ++ [i]) m su ρ =
      roundStepBV i
        (([16:64].toList).foldl (fun w i => scheduleStepBV i w)
          (([0:16].toList).foldl
            (fun w i => w.set! i ((m[i]!).eval ρ.bool)) default))
        (roundsEvalBV xs m su ρ) := by
  simp only [roundsEvalBV, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [scheduleBV_eq_raw]

theorem scheduleEvalBV_eq :
    scheduleEvalBV m ρ = scheduleBV (m.map (Word.eval ρ.bool)) := rfl

attribute [irreducible] roundsEvalBV

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
          case vc1 =>
            intro hbits hvalid
            exact ⟨by assumption, hvalid,
              U.eval_eq_word_eval _ _ hvalid hbits⟩
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
      (permModel (m.map (Word.eval ρ.bool)) (s.map (Word.eval ρ.bool))) ρ⌝⦄ := by
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
    case vc1 =>
      rename_i pref cur suff hrange ws hws out hout
      have hcur : cur < 16 := by grind
      have houtEval : out.eval ρ = (m[cur]!).eval ρ.bool := by
        rw [U.eval_eq_word_eval out _ hout.2 hout.1]
        simp only [getElem!_pos m cur hcur]
      simpa [List.foldl_append] using hws.set! ⟨hout.2, houtEval⟩ cur
    case vc2 =>
      intro j
      refine ⟨U.valid_vector_default j, ?_⟩
      rw [U.vector_default_get]
      rw [List.foldl_nil]
      have hz : (default : Vector (BitVec 32) 64)[j] = 0 := by
        change (Vector.replicate 64 (0 : BitVec 32))[j] = 0
        simp
      rw [hz]
      exact U.eval_default
    case vc3 =>
      simp only [forIn_eq_forIn']
      mvcgen -trivial invariants
      · ⇓⟨cur, w⟩ => ⌜VectorEvalRel w
          (cur.prefix.foldl (fun w i => scheduleStepBV i w)
            (([0:16].toList).foldl
              (fun w i => w.set! i ((m[i]!).eval ρ.bool)) default)) ρ⌝
      · ⇓⟨cur, ⟨a, b, c, d, e, f, g, h⟩⟩ =>
          ⌜RoundEvalRel ⟨a, b, c, d, e, f, g, h⟩
          (roundsEvalBV cur.prefix m su ρ) ρ⌝
      case vc1.hvalid =>
        apply U.allValid_four
        · apply U.valid_getElem!
          · intro j; exact (show VectorEvalRel _ _ ρ from by assumption) j |>.1
          · grind
        · grind
        · apply U.valid_getElem!
          · intro j; exact (show VectorEvalRel _ _ ρ from by assumption) j |>.1
          · grind
        · grind
      case vc2 =>
        rename_i pref cur suff hrange w hw s0 hs0 s1 hs1 out hout
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        apply hw.set!
        refine ⟨hout.1, ?_⟩
        rw [hout.2, ← Array.sum_toList]
        have heval0 := U.eval_eq_word_eval s0 _ hs0.2 hs0.1
        have heval1 := U.eval_eq_word_eval s1 _ hs1.2 hs1.1
        simp only [Word.eval_xor, Word.eval_shiftRight] at heval0 heval1
        rw [Word.eval_rotateRight _ _ 7 (by decide),
          Word.eval_rotateRight _ _ 18 (by decide)] at heval0
        rw [Word.eval_rotateRight _ _ 17 (by decide),
          Word.eval_rotateRight _ _ 19 (by decide)] at heval1
        have heval15 := U.eval_eq_word_eval w[cur - 15]! _
          (U.valid_getElem! (fun j => (hw j).1) (by grind)) rfl
        have heval2 := U.eval_eq_word_eval w[cur - 2]! _
          (U.valid_getElem! (fun j => (hw j).1) (by grind)) rfl
        have hw16 := hw.getElem! (cur - 16) (by grind)
        have hw15 := hw.getElem! (cur - 15) (by grind)
        have hw7 := hw.getElem! (cur - 7) (by grind)
        have hw2 := hw.getElem! (cur - 2) (by grind)
        rw [← heval15] at heval0
        rw [← heval2] at heval1
        simp only [Array.toList_map, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.foldl_append, List.foldl_cons,
          scheduleStepBV,
          heval0, heval1, hw16.2, hw15.2, hw7.2, hw2.2,
          Vector.getElem!_map w (fun u => u.eval ρ) (cur - 16) (by grind),
          Vector.getElem!_map w (fun u => u.eval ρ) (cur - 15) (by grind),
          Vector.getElem!_map w (fun u => u.eval ρ) (cur - 7) (by grind),
          Vector.getElem!_map w (fun u => u.eval ρ) (cur - 2) (by grind)]
        ac_rfl
      case vc3.h.pre => simpa using (show VectorEvalRel _ _ ρ from by assumption)
      case vc4.hu | vc5.hv | vc6.hw | vc7.hu | vc8.hv | vc9.hw =>
        simp_all only [RoundEvalRel]
      case vc10.hvalid =>
        intro u hu
        simp only [Array.mem_def, List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · simp_all [RoundEvalRel]
        · simp_all [RoundEvalRel]
        · grind
        · grind
        · exact U.valid_bitVec _
        · apply U.valid_getElem (i := _)
          · intro j
            exact ((show VectorEvalRel _ _ ρ from by assumption) j).1
      case vc11.hvalid =>
        intro u hu
        simp only [Array.mem_def, List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simp_all [RoundEvalRel]
        · grind
        · grind
        · exact U.valid_bitVec _
        · apply U.valid_getElem (i := _)
          · intro j
            exact ((show VectorEvalRel _ _ ρ from by assumption) j).1
        · grind
        · grind
      case vc12 =>
        rename_i hsu wInit hInit w hw pref cur suff hrange r hr
          S1 hS1 ch hch S0 hS0 maj hmaj newE hnewE newA hnewA
        rw [roundsEvalBV_append_singleton]
        have hcur : cur < 64 := by grind
        have hwi : w[cur]!.eval ρ =
            (([16:64].toList).foldl (fun w i => scheduleStepBV i w)
              (([0:16].toList).foldl
                (fun w i => w.set! i ((m[i]!).eval ρ.bool)) default))[cur]! := by
          rw [getElem!_pos w cur hcur,
            getElem!_pos _ cur hcur]
          exact (hw ⟨cur, hcur⟩).2
        have hnewE' : newE.Valid ρ ∧ newE.eval ρ =
            (#[r.2.2.2.1, r.2.2.2.2.2.2.2, S1, ch,
              (k[cur]! : U 32), w[cur]!].map (fun u => u.eval ρ)).sum := by
          rw [getElem!_pos k cur hcur, getElem!_pos w cur hcur]
          exact hnewE
        have hnewA' : newA.Valid ρ ∧ newA.eval ρ =
            (#[r.2.2.2.2.2.2.2, S1, ch, (k[cur]! : U 32), w[cur]!,
              S0, maj].map (fun u => u.eval ρ)).sum := by
          rw [getElem!_pos k cur hcur, getElem!_pos w cur hcur]
          exact hnewA
        exact RoundEvalRel.step hr cur hwi hS1 hch hS0 hmaj hnewE' hnewA'
      case vc13.h.pre =>
        have hsu := show VectorEvalRel su _ ρ from by assumption
        rw [roundsEvalBV_nil]
        exact RoundEvalRel.ofVectorEval hsu
      case vc14.hvalid =>
        exact U.allValid_pair
          ((show VectorEvalRel su _ ρ from by assumption) 0).1
          (show RoundEvalRel _ _ ρ from by assumption).1
      case vc15.hvalid =>
        exact U.allValid_pair
          ((show VectorEvalRel su _ ρ from by assumption) 1).1
          (show RoundEvalRel _ _ ρ from by assumption).2.2.1
      case vc16.hvalid =>
        exact U.allValid_pair
          ((show VectorEvalRel su _ ρ from by assumption) 2).1
          (show RoundEvalRel _ _ ρ from by assumption).2.2.2.2.1
      case vc17.hvalid =>
        exact U.allValid_pair
          ((show VectorEvalRel su _ ρ from by assumption) 3).1
          (show RoundEvalRel _ _ ρ from by assumption).2.2.2.2.2.2.1
      case vc18.hvalid =>
        exact U.allValid_pair
          ((show VectorEvalRel su _ ρ from by assumption) 4).1
          (show RoundEvalRel _ _ ρ from by assumption).2.2.2.2.2.2.2.2.1
      case vc19.hvalid =>
        exact U.allValid_pair
          ((show VectorEvalRel su _ ρ from by assumption) 5).1
          (show RoundEvalRel _ _ ρ from by assumption).2.2.2.2.2.2.2.2.2.2.1
      case vc20.hvalid =>
        exact U.allValid_pair
          ((show VectorEvalRel su _ ρ from by assumption) 6).1
          (show RoundEvalRel _ _ ρ from by assumption).2.2.2.2.2.2.2.2.2.2.2.2.1
      case vc21.hvalid =>
        exact U.allValid_pair
          ((show VectorEvalRel su _ ρ from by assumption) 7).1
          (show RoundEvalRel _ _ ρ from by assumption).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      case vc22.success =>
        intro j
        have hsu := show VectorEvalRel su (s.map (Word.eval ρ.bool)) ρ from
          by assumption
        have hr := show RoundEvalRel _ (roundsEvalBV [0:64].toList m su ρ) ρ from
          by assumption
        have hinit : initialRoundEvalBV su ρ =
            ⟨(s.map (Word.eval ρ.bool))[0], (s.map (Word.eval ρ.bool))[1],
              (s.map (Word.eval ρ.bool))[2], (s.map (Word.eval ρ.bool))[3],
              (s.map (Word.eval ρ.bool))[4], (s.map (Word.eval ρ.bool))[5],
              (s.map (Word.eval ρ.bool))[6], (s.map (Word.eval ρ.bool))[7]⟩ := by
          unfold initialRoundEvalBV
          apply Prod.ext
          · exact (hsu 0).2
          · apply Prod.ext
            · exact (hsu 1).2
            · apply Prod.ext
              · exact (hsu 2).2
              · apply Prod.ext
                · exact (hsu 3).2
                · apply Prod.ext
                  · exact (hsu 4).2
                  · apply Prod.ext
                    · exact (hsu 5).2
                    · apply Prod.ext <;> first | exact (hsu 6).2 | exact (hsu 7).2
        unfold roundsEvalBV at hr
        rw [hinit] at hr
        rw [permModel_eq_steps]
        fin_cases j
        · simpa [addStateBV] using
            U.sumPair_eval (by assumption) (hsu 0).2 hr.2.1
        · simpa [addStateBV] using
            U.sumPair_eval (by assumption) (hsu 1).2 hr.2.2.2.1
        · simpa [addStateBV] using
            U.sumPair_eval (by assumption) (hsu 2).2 hr.2.2.2.2.2.1
        · simpa [addStateBV] using
            U.sumPair_eval (by assumption) (hsu 3).2 hr.2.2.2.2.2.2.2.1
        · simpa [addStateBV] using
            U.sumPair_eval (by assumption) (hsu 4).2 hr.2.2.2.2.2.2.2.2.2.1
        · simpa [addStateBV] using
            U.sumPair_eval (by assumption) (hsu 5).2 hr.2.2.2.2.2.2.2.2.2.2.2.1
        · simpa [addStateBV] using
            U.sumPair_eval (by assumption) (hsu 6).2
              hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        · simpa [addStateBV] using
            U.sumPair_eval (by assumption) (hsu 7).2
              hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

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

def RoundWFRel (lv rv : WF.Valuation) (l r : RoundState) : Prop :=
  U.WFRel lv rv l.1 r.1 ∧
  U.WFRel lv rv l.2.1 r.2.1 ∧
  U.WFRel lv rv l.2.2.1 r.2.2.1 ∧
  U.WFRel lv rv l.2.2.2.1 r.2.2.2.1 ∧
  U.WFRel lv rv l.2.2.2.2.1 r.2.2.2.2.1 ∧
  U.WFRel lv rv l.2.2.2.2.2.1 r.2.2.2.2.2.1 ∧
  U.WFRel lv rv l.2.2.2.2.2.2.1 r.2.2.2.2.2.2.1 ∧
  U.WFRel lv rv l.2.2.2.2.2.2.2 r.2.2.2.2.2.2.2

theorem U.wfRel_bitVec (lv rv : WF.Valuation) (x : BitVec n) :
    U.WFRel lv rv (x : U n) (x : U n) := by
  have hbit (v : Nat → Bool) (j : Fin n) :
      LC.eval v ((x : U n).bits.bitsLE[j]) = x[j] := by
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
    change x[j] + (∅ : Std.ExtTreeMap Nat Bool).foldMap
      (fun i c => c * v i) = x[j]
    have hz : (∅ : Std.ExtTreeMap Nat Bool).foldMap
        (fun i c => c * v i) = 0 := Std.ExtTreeMap.foldMap_empty _
    rw [hz, add_zero]
  have hint (v : Nat → ℤ) (j : Fin n) :
      LC.eval v ((x : U n).intBits[j]) = x[j].toInt := by
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
    change x[j].toInt + (∅ : Std.ExtTreeMap Nat ℤ).foldMap
      (fun i c => c * v i) = x[j].toInt
    have hz : (∅ : Std.ExtTreeMap Nat ℤ).foldMap
        (fun i c => c * v i) = 0 := Std.ExtTreeMap.foldMap_empty _
    rw [hz, add_zero]
  unfold U.WFRel WF.LCEq U.intVal
  constructor
  · rw [LC.eval_sum, LC.eval_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [LC.eval_nsmul, hint]
  · intro j
    rw [hbit, hbit]

theorem U.ch_wf_rel :
    WF.GadgetSpec
      (fun lv rv (l r : U n × U n × U n) =>
        U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2.1 r.2.1 ∧
          U.WFRel lv rv l.2.2 r.2.2)
      (fun x => U.ch x.1 x.2.1 x.2.2) U.WFRel := by
  exact U.ch_wf

theorem U.maj_wf_rel :
    WF.GadgetSpec
      (fun lv rv (l r : U n × U n × U n) =>
        U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2.1 r.2.1 ∧
          U.WFRel lv rv l.2.2 r.2.2)
      (fun x => U.maj x.1 x.2.1 x.2.2) U.WFRel := by
  exact U.maj_wf

theorem roundStep_wf (i : Nat) (hi : i ∈ [0:64]) :
    WF.GadgetSpec
      (fun lv rv (l r : Vector (U 32) 64 × RoundState) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧
          RoundWFRel lv rv l.2 r.2)
      (fun x => roundStep i x.1 x.2) RoundWFRel := by
  unfold WF.GadgetSpec
  rintro ⟨wL, rL⟩ ⟨wR, rR⟩
  unfold roundStep
  apply WF.GadgetSpec.bind_rule
    (left := rL.2.2.2.2.1.bits.rotateRight 6 ^^^
      rL.2.2.2.2.1.bits.rotateRight 11 ^^^ rL.2.2.2.2.1.bits.rotateRight 25)
    (right := rR.2.2.2.2.1.bits.rotateRight 6 ^^^
      rR.2.2.2.2.1.bits.rotateRight 11 ^^^ rR.2.2.2.2.1.bits.rotateRight 25)
    U.fromWord_wf_rel
  · intro lv rv h
    have he := h.2.2.2.2.2.1.2
    change Word.WFRel lv rv rL.2.2.2.2.1.bits rR.2.2.2.2.1.bits at he
    exact ((he.rotateRight 6).xor (he.rotateRight 11)).xor
      (he.rotateRight 25)
  · intro A S1L S1R hS1
    apply WF.GadgetSpec.bind_rule
      (left := ⟨rL.2.2.2.2.1, rL.2.2.2.2.2.1, rL.2.2.2.2.2.2.1⟩)
      (right := ⟨rR.2.2.2.2.1, rR.2.2.2.2.2.1, rR.2.2.2.2.2.2.1⟩)
      U.ch_wf_rel
    · intro lv rv hA
      have h := (hS1 lv rv hA).1.2
      exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩
    · intro B chL chR hch
      apply WF.GadgetSpec.bind_rule
        (left := rL.1.bits.rotateRight 2 ^^^ rL.1.bits.rotateRight 13 ^^^
          rL.1.bits.rotateRight 22)
        (right := rR.1.bits.rotateRight 2 ^^^ rR.1.bits.rotateRight 13 ^^^
          rR.1.bits.rotateRight 22)
        U.fromWord_wf_rel
      · intro lv rv hB
        have ha := (hS1 lv rv (hch lv rv hB).1).1.2.1.2
        change Word.WFRel lv rv rL.1.bits rR.1.bits at ha
        exact ((ha.rotateRight 2).xor (ha.rotateRight 13)).xor
          (ha.rotateRight 22)
      · intro C S0L S0R hS0
        apply WF.GadgetSpec.bind_rule
          (left := ⟨rL.1, rL.2.1, rL.2.2.1⟩)
          (right := ⟨rR.1, rR.2.1, rR.2.2.1⟩) U.maj_wf_rel
        · intro lv rv hC
          have hA := hS0 lv rv hC
          have hB := hch lv rv hA.1
          have hr := (hS1 lv rv hB.1).1.2
          exact ⟨hr.1, hr.2.1, hr.2.2.1⟩
        · intro D majL majR hmaj
          apply WF.GadgetSpec.bind_rule
            (left := #v[rL.2.2.2.1, rL.2.2.2.2.2.2.2, S1L, chL,
              (k[i]! : U 32), wL[i]!])
            (right := #v[rR.2.2.2.1, rR.2.2.2.2.2.2.2, S1R, chR,
              (k[i]! : U 32), wR[i]!]) U.sumFixed_wf
          · intro lv rv hD
            have hC := hmaj lv rv hD
            have hB := hS0 lv rv hC.1
            have hA := hch lv rv hB.1
            have h0 := hS1 lv rv hA.1
            have hw := h0.1.1
            have hr := h0.1.2
            intro j
            fin_cases j
            · exact hr.2.2.2.1
            · exact hr.2.2.2.2.2.2.2
            · exact h0.2
            · exact hA.2
            · exact U.wfRel_bitVec _ _ _
            · exact hw.getElem! (i := i) (by grind)
          · intro E newEL newER hnewE
            apply WF.GadgetSpec.bind_rule
              (left := #v[rL.2.2.2.2.2.2.2, S1L, chL, (k[i]! : U 32),
                wL[i]!, S0L, majL])
              (right := #v[rR.2.2.2.2.2.2.2, S1R, chR, (k[i]! : U 32),
                wR[i]!, S0R, majR]) U.sumFixed_wf
            · intro lv rv hE
              have hD := hnewE lv rv hE
              have hC := hmaj lv rv hD.1
              have hB := hS0 lv rv hC.1
              have hA := hch lv rv hB.1
              have h0 := hS1 lv rv hA.1
              have hw := h0.1.1
              have hr := h0.1.2
              intro j
              fin_cases j
              · exact hr.2.2.2.2.2.2.2
              · exact h0.2
              · exact hA.2
              · exact U.wfRel_bitVec _ _ _
              · exact hw.getElem! (i := i) (by grind)
              · exact hB.2
              · exact hC.2
            · intro F newAL newAR hnewA
              apply WF.Rel.pure
              intro lv rv hF
              have hE := hnewA lv rv hF
              have hD := hnewE lv rv hE.1
              have hC := hmaj lv rv hD.1
              have hB := hS0 lv rv hC.1
              have hA := hch lv rv hB.1
              have h0 := hS1 lv rv hA.1
              have hr := h0.1.2
              exact ⟨hE.2, hr.1, hr.2.1, hr.2.2.1, hD.2,
                hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1⟩

theorem RoundWFRel.ofVector
    {sL sR : Vector (U 32) 8}
    (h : WF.VectorRel U.WFRel lv rv sL sR) :
    RoundWFRel lv rv
      ⟨sL[0], sL[1], sL[2], sL[3], sL[4], sL[5], sL[6], sL[7]⟩
      ⟨sR[0], sR[1], sR[2], sR[3], sR[4], sR[5], sR[6], sR[7]⟩ :=
  ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩

theorem roundStepBounded_wf (i : Nat) (hi : i ∈ [0:64]) :
    WF.GadgetSpec
      (fun lv rv (l r : Vector (U 32) 64 × RoundState) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧ RoundWFRel lv rv l.2 r.2)
      (fun x => roundStepBounded i hi x.1 x.2) RoundWFRel := by
  unfold WF.GadgetSpec
  intro left right
  change WF.Rel RoundWFRel _
    (roundStepBounded i hi left.1 left.2)
    (roundStepBounded i hi right.1 right.2)
  rw [roundStepBounded_eq, roundStepBounded_eq]
  exact roundStep_wf i hi left right

def finishRounds (s : Vector (U 32) 8) (r : RoundState) :
    Circuit (Vector (U 32) 8) := do
  let a ← U.sumFixed #v[s[0], r.1]
  let b ← U.sumFixed #v[s[1], r.2.1]
  let c ← U.sumFixed #v[s[2], r.2.2.1]
  let d ← U.sumFixed #v[s[3], r.2.2.2.1]
  let e ← U.sumFixed #v[s[4], r.2.2.2.2.1]
  let f ← U.sumFixed #v[s[5], r.2.2.2.2.2.1]
  let g ← U.sumFixed #v[s[6], r.2.2.2.2.2.2.1]
  let h ← U.sumFixed #v[s[7], r.2.2.2.2.2.2.2]
  pure #v[a, b, c, d, e, f, g, h]

def roundStateVector (r : RoundState) : Vector (U 32) 8 :=
  #v[r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1,
    r.2.2.2.2.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2]

theorem finishRounds_eq_ofFnM (s : Vector (U 32) 8) (r : RoundState) :
    finishRounds s r = Vector.ofFnM (fun i =>
      U.sumFixed #v[s[i], (roundStateVector r)[i]]) := by
  simp [finishRounds, Vector.ofFnM_succ, Vector.ofFnM_zero, roundStateVector]

theorem finishRounds_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Vector (U 32) 8 × RoundState) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧ RoundWFRel lv rv l.2 r.2)
      (fun x => finishRounds x.1 x.2) (WF.VectorRel U.WFRel) := by
  unfold WF.GadgetSpec
  rintro ⟨sL, rL⟩ ⟨sR, rR⟩
  change WF.Rel (WF.VectorRel U.WFRel) _
    (finishRounds sL rL) (finishRounds sR rR)
  rw [finishRounds_eq_ofFnM, finishRounds_eq_ofFnM]
  apply WF.Rel.mono (WF.Rel.vectorOfFnM (S := fun _ => U.WFRel) ?_)
  · intro lv rv left right h
    exact h.2
  · intro i A _ _ hA
    apply U.sumFixed_wf.relHom
    intro lv rv h
    have hinput := hA lv rv h
    have hs := hinput.1
    have hr := hinput.2
    intro j
    fin_cases j
    · exact hs i
    · unfold roundStateVector
      unfold RoundWFRel at hr
      fin_cases i
      · exact hr.1
      · exact hr.2.1
      · exact hr.2.2.1
      · exact hr.2.2.2.1
      · exact hr.2.2.2.2.1
      · exact hr.2.2.2.2.2.1
      · exact hr.2.2.2.2.2.2.1
      · exact hr.2.2.2.2.2.2.2

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
          exact ⟨ho.1, hin.1, WF.VectorRel.set! hin.2 ho.2 i⟩
      case hcont =>
        intro C wL wR hleft
        have H : WF.Rel (WF.VectorRel U.WFRel) C
            ((forIn' [0:64]
                ⟨sL[0], sL[1], sL[2], sL[3], sL[4], sL[5], sL[6], sL[7]⟩
                fun i hi r => do
                  let out ← roundStepBounded i hi wL r
                  pure (ForInStep.yield out)) >>= finishRounds sL)
            ((forIn' [0:64]
                ⟨sR[0], sR[1], sR[2], sR[3], sR[4], sR[5], sR[6], sR[7]⟩
                fun i hi r => do
                  let out ← roundStepBounded i hi wR r
                  pure (ForInStep.yield out)) >>= finishRounds sR) := by
          apply WF.Rel.forIn'_range_map_yield_bind_rule
            (I := RoundWFRel) (xs := [0:64])
            (fL := fun i hi r => roundStepBounded i hi wL r)
            (fR := fun i hi r => roundStepBounded i hi wR r)
            (nextL := fun _ _ _ out => out)
            (nextR := fun _ _ _ out => out)
          case hinit =>
            intro lv rv hC
            have h0 := hleft lv rv hC
            have h1 := hw lv rv h0.1
            apply RoundWFRel.ofVector
            intro i
            have hsi := (hs lv rv h1.1).2 i
            exact ⟨hsi.2.2, hsi.1⟩
          case hstep =>
            intro i hi P rL rR hP
            have hstep := (roundStepBounded_wf i hi).relHom P
              ⟨wL, rL⟩ ⟨wR, rR⟩ (by
                intro lv rv h
                have hp := hP lv rv h
                exact ⟨(hleft lv rv hp.1).2, hp.2⟩)
            apply WF.Rel.mono hstep
            intro lv rv _ _ hout
            exact ⟨hout.1, (hP lv rv hout.1).1, hout.2⟩
          case hcont =>
            intro D rL rR hr
            apply WF.Rel.mono (finishRounds_wf.relHom D
              ⟨sL, rL⟩ ⟨sR, rR⟩ ?_)
            · intro lv rv _ _ h
              exact h.2
            · intro lv rv hD
              have hround := hr lv rv hD
              have h0 := hleft lv rv hround.1
              have h1 := hw lv rv h0.1
              refine ⟨?_, hround.2⟩
              intro i
              have hsi := (hs lv rv h1.1).2 i
              exact ⟨hsi.2.2, hsi.1⟩
        unfold finishRounds at H
        simpa only [roundStepBounded, bind_assoc, pure_bind] using H

def messageInput (inp : Vector (LC Bool) 768) : Vector (Word 32) 16 :=
  Vector.ofFn fun wi => Word.mk (Vector.ofFn fun bi =>
    inp[wi.val * 32 + bi.val])

def stateInput (inp : Vector (LC Bool) 768) : Vector (Word 32) 8 :=
  Vector.ofFn fun si => Word.mk (Vector.ofFn fun bi =>
    inp[512 + si.val * 32 + bi.val])

def flattenOutput (out : Vector (U 32) 8) : Vector (LC Bool) 256 :=
  Vector.ofFn fun i => out[i.val / 32].bits.bitsLE[i.val % 32]

theorem permCirc'_eq (inp : Vector (LC Bool) 768) :
    permCirc' inp = (do
      let out ← permCircuit (messageInput inp) (stateInput inp)
      pure (flattenOutput out)) := rfl

theorem messageInput_get (inp : Vector (LC Bool) 768)
    (wi : Fin 16) (bi : Fin 32) :
    (messageInput inp)[wi][bi] = inp[wi.val * 32 + bi.val] := by
  simp only [messageInput, Fin.getElem_fin, Vector.getElem_ofFn]
  change (Vector.ofFn fun bj : Fin 32 =>
    inp[wi.val * 32 + bj.val])[bi] = _
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]

theorem stateInput_get (inp : Vector (LC Bool) 768)
    (si : Fin 8) (bi : Fin 32) :
    (stateInput inp)[si][bi] = inp[512 + si.val * 32 + bi.val] := by
  simp only [stateInput, Fin.getElem_fin, Vector.getElem_ofFn]
  change (Vector.ofFn fun bj : Fin 32 =>
    inp[512 + si.val * 32 + bj.val])[bi] = _
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]

theorem messageInput_wf
    (h : WF.VectorRel (fun lv rv (l r : LC Bool) =>
      WF.LCEq lv.bool rv.bool l r) lv rv left right) :
    WF.VectorRel (fun lv rv (l r : Word 32) => ∀ i : Fin 32,
      WF.LCEq lv.bool rv.bool l[i] r[i]) lv rv
      (messageInput left) (messageInput right) := by
  intro wi bi
  rw [messageInput_get, messageInput_get]
  exact h ⟨wi.val * 32 + bi.val, by omega⟩

theorem stateInput_wf
    (h : WF.VectorRel (fun lv rv (l r : LC Bool) =>
      WF.LCEq lv.bool rv.bool l r) lv rv left right) :
    WF.VectorRel (fun lv rv (l r : Word 32) => ∀ i : Fin 32,
      WF.LCEq lv.bool rv.bool l[i] r[i]) lv rv
      (stateInput left) (stateInput right) := by
  intro si bi
  rw [stateInput_get, stateInput_get]
  exact h ⟨512 + si.val * 32 + bi.val, by omega⟩

attribute [irreducible] messageInput stateInput flattenOutput

theorem permCirc'_wf :
    WF.GadgetSpec
      (WF.VectorRel fun lv rv (l r : LC Bool) =>
        WF.LCEq lv.bool rv.bool l r)
      permCirc'
      (WF.VectorRel fun lv rv (l r : LC Bool) =>
        WF.LCEq lv.bool rv.bool l r) := by
  unfold WF.GadgetSpec
  intro left right
  rw [permCirc'_eq, permCirc'_eq]
  apply WF.GadgetSpec.bind_rule
    (left := ⟨messageInput left, stateInput left⟩)
    (right := ⟨messageInput right, stateInput right⟩) permCircuit_wf
  · intro lv rv h
    exact ⟨messageInput_wf h, stateInput_wf h⟩
  · intro A outL outR hout
    apply WF.Rel.pure
    intro lv rv hA
    have h := hout lv rv hA
    intro i
    change WF.LCEq lv.bool rv.bool
      (flattenOutput outL)[i] (flattenOutput outR)[i]
    rw [show (flattenOutput outL)[i] =
      outL[i.val / 32].bits.bitsLE[i.val % 32] by
        unfold flattenOutput; simp,
      show (flattenOutput outR)[i] =
      outR[i.val / 32].bits.bitsLE[i.val % 32] by
        unfold flattenOutput; simp]
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
      BitVec.ofNat 32 (Nat.ofBits fun bi : Fin 32 => values[base + bi.val]) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [Word.eval, BitVec.getElem_ofFnLE, Fin.getElem_fin,
    Vector.getElem_ofFn, LC.eval_singleton]
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _),
    Nat.testBit_ofBits_lt _ _ hi]
  exact hvalues ⟨base + i, by omega⟩

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
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
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
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
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
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  have hu := h ⟨i / 32, by omega⟩
  have heval := U.eval_eq_ofFnLE _ hu.1
  have hbit := congrArg (fun x : BitVec 32 => x[i % 32]'(by omega)) heval
  rw [hu.2] at hbit
  simp only [BitVec.getElem_ofFnLE] at hbit
  rw [BitVec.getElem_eq_testBit_toNat] at hbit
  exact hbit.symm

def permSoundPost (wireInputs : Vector (LC Bool) 768)
    (valuation : WF.Valuation) (out : Vector (U 32) 8) : Prop :=
  VectorEvalRel out
    (permModel
      ((messageInput wireInputs).map (Word.eval valuation.bool))
      ((stateInput wireInputs).map (Word.eval valuation.bool))) valuation

theorem permCirc'_sound_triple (inputs : Vector Bool 768)
    (wit : Nat → Bool)
    (hinputs : ∀ i : Fin 768, wit i.val = inputs[i])
    (cs : Semantics.CS) :
    ⦃⌜True⌝⦄ Sound.interp (Sound.csValuation cs wit)
    (permCirc' (Vector.ofFn fun i => ({i.val} : LC Bool)))
    ⦃ ⇓ out => ⌜out.map (fun x => x.eval wit) = permModel' inputs⌝⦄ := by
  rw [permCirc'_eq]
  rw [Sound.interp_bind]
  apply Triple.bind
    (Q := fun out => ⌜permSoundPost
      (Vector.ofFn fun i => ({i.val} : LC Bool))
      (Sound.csValuation cs wit) out⌝)
  case hx =>
    unfold permSoundPost
    exact permCircuit_sound
  case hf =>
    intro out
    apply Triple.pure
    simp only [SPred.entails_nil]
    intro hout
    unfold permSoundPost at hout
    unfold messageInput stateInput at hout
    unfold flattenOutput
    simp only [Sound.csValuation] at hout ⊢
    simp only [Fin.getElem_fin, Vector.getElem_ofFn] at hout
    rw [flatten_eval hout]
    have hperm := congrArg₂ permModel
      (messageWords_eval inputs wit hinputs)
      (stateWords_eval inputs wit hinputs)
    rw [hperm]
    rfl


end Freigen.F2Z.Examples
