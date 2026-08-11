import Freigen.F2Z.Defs
import Freigen.F2Z.Gadgets
import Freigen.F2Z.Semantics
import Freigen.F2Z.Correctness.Basic
import Batteries.Data.Int
import Mathlib.Algebra.BigOperators.Fin

namespace Freigen.F2Z.Examples

namespace VectorMapM

open Std.Do
open scoped Std.Do

def vectorToArrayPost {β : Type u} {n : Nat} {ps : PostShape}
    (Q : PostCond (Vector β n) ps) : PostCond (Array β) ps :=
  (spred(fun a => ∀ v, ⌜v.toArray = a⌝ → Q.1 v), Q.2)

@[spec]
theorem vectorMapM_of_array [Monad m] [WPMonad m ps]
    {f : α → m β} {xs : Vector α n}
    {P : Assertion ps} {Q : PostCond (Vector β n) ps}
    (h : Triple (xs.toArray.mapM f) P (vectorToArrayPost Q)) :
    Triple (xs.mapM f) P Q := by
  rw [← Vector.toArray_mapM] at h
  apply Triple.iff.mpr
  have hwp := Triple.iff.mp h
  rw [WPMonad.wp_map] at hwp
  apply hwp.trans
  apply (wp (xs.mapM f)).mono
  simp only [PostCond.entails]
  constructor
  · intro v
    simp only [PredTrans.apply, vectorToArrayPost]
    refine (SPred.forall_elim v).trans ?_
    simpa using
      (SPred.true_imp.mp : (spred(⌜True⌝ → Q.1 v) ⊢ₛ Q.1 v))
  · exact ExceptConds.entails.refl _

end VectorMapM

def k : Vector (BitVec 32) 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

def perm (m : Vector (BitVec 32) 16) (s : Vector (BitVec 32) 8) : Vector (BitVec 32) 8 := Id.run $ do
  let mut w := Vector.replicate 64 (0 : BitVec 32)
  for h:i in [0:16] do
    w := w.set! i m[i]
  for i in [16:64] do
    let s0 := (w[i-15]!.rotateRight 7) ^^^ (w[i-15]!.rotateRight 18) ^^^ (w[i-15]! >>> 3)
    let s1 := (w[i-2]!.rotateRight 17) ^^^ (w[i-2]!.rotateRight 19) ^^^ (w[i-2]! >>> 10)
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
    let S1 := (e.rotateRight 6) ^^^ (e.rotateRight 11) ^^^ (e.rotateRight 25)
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := h + S1 + ch + k[i] + w[i]
    let S0 := (a.rotateRight 2) ^^^ (a.rotateRight 13) ^^^ (a.rotateRight 22)
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

  #v[s[0] + a, s[1] + b, s[2] + c, s[3] + d, s[4] + e, s[5] + f, s[6] + g, s[7] + h]

/-- https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf -/
example : perm
    #v[
      0x61626380, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000018
    ]
    #v[
      0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
    ] =
    #v[
      0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
      0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad
    ]
  := by native_decide

example : perm
    #v[
      0x61626364, 0x62636465, 0x63646566, 0x64656667,
      0x65666768, 0x66676869, 0x6768696a, 0x68696a6b,
      0x696a6b6c, 0x6a6b6c6d, 0x6b6c6d6e, 0x6c6d6e6f,
      0x6d6e6f70, 0x6e6f7071, 0x80000000, 0x00000000
    ]
    #v[
      0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
    ] =
    #v[
      0x85e655d6, 0x417a1795, 0x3363376a, 0x624cde5c,
      0x76e09589, 0xcac5f811, 0xcc4b32c1, 0xf20e533a
    ]
  := by native_decide

example : perm
    #v[
      0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x000001c0
    ]
    #v[
      0x85e655d6, 0x417a1795, 0x3363376a, 0x624cde5c,
      0x76e09589, 0xcac5f811, 0xcc4b32c1, 0xf20e533a
    ] =
    #v[
      0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039,
      0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1
    ]
  := by native_decide

section Circuit

local instance : Inhabited (LC ℤ) := ⟨0⟩
local instance : Inhabited (LC Bool) := ⟨0⟩

def fromBitsBE {n : ℕ} (r : Vector (LC Bool) n) : Circuit (LC ℤ) := do
  let bits ← r.reverse.mapM f2z
  return ∑ i : Fin n, 2 ^ i.val • bits[i]

def toBitsBE (n : ℕ) (i : LC ℤ) : Circuit (Vector (LC Bool) n) := do
  return (← toBits n i).reverse

def _root_.Vector.rotateRight {n : Nat} (v : Vector α n) (k : Nat) : Vector α n :=
  let k := k % n
  have : (n - (n - k) + min (n - k) n) = n := by omega
  this ▸ (v.drop (n - k) ++ v.take (n - k))

def permCircuit (m : Vector (Vector (LC Bool) 32) 16)
    (s : Vector (Vector (LC Bool) 32) 8) :
    Circuit (Vector (Vector (LC Bool) 32) 8) := do
  let mut w : Vector (Vector (LC Bool) 32 × LC ℤ) 64 := default
  for h:i in [0:16] do
    w := w.set! i (m[i], ←fromBitsBE m[i])
  for i in [16:64] do
    let wi15 := w[i-15]!.1
    let s0 ← fromBitsBE $ Vector.ofFn fun i => (wi15.rotateRight 7)[i] + (wi15.rotateRight 18)[i] + (wi15.drop 3)[i]!
    let wi2 := w[i-2]!.1
    let s1 ← fromBitsBE $ Vector.ofFn fun i => (wi2.rotateRight 17)[i] + (wi2.rotateRight 19)[i] + (wi2.drop 10)[i]!
    let sumBits ← toBitsBE 34 $ w[i-16]!.2 + s0 + w[i-7]!.2 + s1


  --   let s0 ← toBits 32 ((w[i-15]! ^^^ (w[i-15]!.rotateRight 7) ^^^ (w[i-15]!.rotateRight 18)) >>> 3)
  --   let s1 ← toBits 32 ((w[i-2]! ^^^ (w[i-2]!.rotateRight 17) ^^^ (w[i-2]!.rotateRight 19)) >>> 10)
  --   let sum ← fromBits w[i-16]! + fromBits s0 + fromBits w[i-7]! + fromBits s1
  --   let sumBits ← toBits 32 sum
  --   w := w.set! i sumBits
  -- let mut a := s[0]
  -- let mut b := s[1]
  -- let mut c := s[2]
  -- let mut d := s[3]
  -- let mut e := s[4]
  -- let mut f := s[5]
  -- let mut g := s[6]
  -- let mut h := s[7]
  sorry

end Circuit

section WF

private theorem list_mapM_f2z_rel
    {P : WF.Assumption} {xsL xsR : List (LC Bool)}
    (hlen : xsL.length = xsR.length)
    (hxs : ∀ leftVal rightVal, P leftVal rightVal →
      List.Forall₂ (WF.LCEq leftVal.bool rightVal.bool) xsL xsR) :
    WF.Rel
      (fun leftVal rightVal ysL ysR =>
        P leftVal rightVal ∧
        List.Forall₂ (WF.LCEq leftVal.int rightVal.int) ysL ysR)
      P (xsL.mapM f2z) (xsR.mapM f2z) := by
  induction xsL generalizing xsR P with
  | nil =>
      cases xsR with
      | nil =>
          simp only [List.mapM_nil]
          exact .pure fun leftVal rightVal hP => ⟨hP, .nil⟩
      | cons => simp at hlen
  | cons x xs ih =>
      cases xsR with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.mapM_cons]
          apply WF.Rel.f2z
          · intro leftVal rightVal hP
            cases hxs leftVal rightVal hP with
            | cons hhead _ => exact hhead
          · intro outL outR
            let P' : WF.Assumption := fun leftVal rightVal =>
              P leftVal rightVal ∧
              outL.eval leftVal.int = (x.eval leftVal.bool).toInt ∧
              outR.eval rightVal.int = (y.eval rightVal.bool).toInt
            have htail : ∀ leftVal rightVal, P' leftVal rightVal →
                List.Forall₂ (WF.LCEq leftVal.bool rightVal.bool) xs ys := by
              intro leftVal rightVal hP'
              cases hxs leftVal rightVal hP'.1 with
              | cons _ htail => exact htail
            have hrel := ih (P := P') (xsR := ys)
              (by simpa using hlen) htail
            apply hrel.bind (fun tail => pure (outL :: tail))
              (fun tail => pure (outR :: tail))
            intro S tailL tailR hpost
            apply WF.Rel.pure
            intro leftVal rightVal hS
            have hp := hpost leftVal rightVal hS
            refine ⟨hp.1.1, .cons ?_ hp.2⟩
            unfold WF.LCEq
            cases hxs leftVal rightVal hp.1.1 with
            | cons hhead _ =>
                unfold WF.LCEq at hhead
                exact hp.1.2.1.trans
                  ((congrArg Bool.toInt hhead).trans hp.1.2.2.symm)

private theorem array_mapM_f2z_rel
    {P : WF.Assumption} {xsL xsR : Array (LC Bool)}
    (hlen : xsL.size = xsR.size)
    (hxs : ∀ leftVal rightVal, P leftVal rightVal →
      List.Forall₂ (WF.LCEq leftVal.bool rightVal.bool)
        xsL.toList xsR.toList) :
    WF.Rel
      (fun leftVal rightVal ysL ysR =>
        P leftVal rightVal ∧
        List.Forall₂ (WF.LCEq leftVal.int rightVal.int)
          ysL.toList ysR.toList)
      P (xsL.mapM f2z) (xsR.mapM f2z) := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  have hrel := list_mapM_f2z_rel
    (P := P) (xsL := xsL.toList) (xsR := xsR.toList)
    (by simpa using hlen) hxs
  apply hrel.bind (fun ys => pure ys.toArray) (fun ys => pure ys.toArray)
  intro S ysL ysR hpost
  exact .pure fun leftVal rightVal hS => by
    simpa using hpost leftVal rightVal hS

private def sumArray (bits : Array (LC ℤ)) (n : Nat) : LC ℤ :=
  ∑ i : Fin n, 2 ^ i.val • bits[i.val]?.getD 0

private theorem fromBitsBE_eq_array (r : Vector (LC Bool) n) :
    fromBitsBE r = (do
      let bits ← r.reverse.toArray.mapM f2z
      pure (sumArray bits n)) := by
  unfold fromBitsBE
  rw [← Vector.toArray_mapM]
  simp only [bind_pure_comp, Functor.map_map]
  congr 1
  funext bits
  simp [sumArray]

theorem fromBitsBE_wf :
    WF.GadgetSpec
      (fun leftVal rightVal (left right : Vector (LC Bool) n) =>
        ∀ i : Fin n,
          WF.LCEq leftVal.bool rightVal.bool left[i] right[i])
      fromBitsBE
      (fun leftVal rightVal left right =>
        WF.LCEq leftVal.int rightVal.int left right) := by
  intro left right
  rw [fromBitsBE_eq_array, fromBitsBE_eq_array]
  let P : WF.Assumption := fun leftVal rightVal =>
    ∀ i : Fin n,
      WF.LCEq leftVal.bool rightVal.bool left[i] right[i]
  have hinputs : ∀ leftVal rightVal, P leftVal rightVal →
      List.Forall₂ (WF.LCEq leftVal.bool rightVal.bool)
        left.reverse.toArray.toList right.reverse.toArray.toList := by
    intro leftVal rightVal hP
    apply List.forall₂_iff_get.mpr
    constructor
    · simp
    · intro i hiLeft hiRight
      simp only [List.get_eq_getElem, Array.getElem_toList]
      have hi : i < n := by simpa using hiLeft
      change WF.LCEq leftVal.bool rightVal.bool
        left.reverse[i] right.reverse[i]
      rw [Vector.getElem_reverse hi, Vector.getElem_reverse hi]
      exact hP ⟨n - 1 - i, by omega⟩
  have hrel := array_mapM_f2z_rel
    (P := P) (xsL := left.reverse.toArray)
    (xsR := right.reverse.toArray) (by simp) hinputs
  apply hrel.bind (fun bits => pure (sumArray bits n))
    (fun bits => pure (sumArray bits n))
  intro S bitsL bitsR hpost
  exact .pure fun leftVal rightVal hS => by
    have hp := hpost leftVal rightVal hS
    unfold WF.LCEq sumArray
    simp only [LC.eval_sum, LC.eval_nsmul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hlen := hp.2.length_eq
    have hsize : bitsL.size = bitsR.size := by simpa using hlen
    by_cases hi : i.val < bitsL.size
    · have hiR : i.val < bitsR.size := by omega
      have hget := hp.2.get (i := i.val)
        (by simpa using hi) (by simpa using hiR)
      unfold WF.LCEq at hget
      simpa [List.get_eq_getElem, hi, hiR] using hget
    · have hiR : ¬i.val < bitsR.size := by omega
      simp [hi, hiR]

end WF

section Sound

open scoped Sound
open Std.Do
variable {valuation : WF.Valuation}

private theorem natCast_ofBits_eq_sum {n : Nat} (f : Fin n → Bool) :
    (Nat.ofBits f : ℤ) = ∑ i : Fin n, (2 : ℤ) ^ i.val * (f i).toInt := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.ofBits_succ, Fin.sum_univ_succ]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, pow_zero, one_mul, Fin.val_succ]
    rw [ih, Finset.mul_sum]
    have hb (b : Bool) : (b.toNat : ℤ) = b.toInt := by cases b <;> rfl
    simp only [Function.comp_apply, pow_succ, hb]
    ring_nf

@[spec]
theorem fromBitsBE_sound {r : Vector (LC Bool) n} :
  ⦃ ⌜True⌝ ⦄
  (Sound.interp valuation $ fromBitsBE r)
  ⦃⇓ a => ⌜a.eval valuation.int =
    Nat.ofBits (Vector.get $ r.reverse |>.map (LC.eval valuation.bool))⌝⦄ := by
  mvcgen [fromBitsBE, Array.mapM_eq_foldlM] invariants
  · ⇓⟨cursor, out⟩ =>
      ⌜cursor.prefix.map (Bool.toInt ∘ LC.eval valuation.bool) =
        out.toList.map (LC.eval valuation.int)⌝
  case vc1.step.success => simp_all
  case vc3.h.post.success =>
    simp [VectorMapM.vectorToArrayPost]
    intro hB a rfl
    have hv : (r.map (LC.eval valuation.bool)).reverse.map Bool.toInt =
        a.map (LC.eval valuation.int) := by
      apply Vector.toList_inj.mp
      simpa only [Vector.toList, Vector.toArray_map, Vector.toArray_reverse,
        Array.toList_map, Array.toList_reverse, List.map_reverse, List.map_map,
        Function.comp_apply] using hB
    rw [natCast_ofBits_eq_sum]
    change (∑ i : Fin n, (2 : ℤ) ^ i.val * a[i].eval valuation.int) =
      ∑ i : Fin n,
        (2 : ℤ) ^ i.val * ((r.map (LC.eval valuation.bool)).reverse[i]).toInt
    apply Finset.sum_congr rfl
    intro i _
    have hi := congrArg (fun v : Vector ℤ n => v[i]) hv
    have hi' : ((r.map (LC.eval valuation.bool)).reverse[i]).toInt =
        a[i].eval valuation.int := by simpa using hi
    rw [← hi']

end Sound

section Complete

open Std.Do
open scoped Std.Do

@[spec]
theorem fromBitsBE_complete {r : Vector (LC Bool) n}
    {valuation : WF.Valuation} :
    ⦃ ⌜True⌝ ⦄
    Complete.interp valuation (fromBitsBE r)
    ⦃⇓ a => ⌜a.eval valuation.int =
      Nat.ofBits (Vector.get $ r.reverse |>.map (LC.eval valuation.bool))⌝⦄ := by
  mvcgen [fromBitsBE, Array.mapM_eq_foldlM] invariants
  · ⇓⟨cursor, out⟩ =>
      ⌜cursor.prefix.map (Bool.toInt ∘ LC.eval valuation.bool) =
        out.toList.map (LC.eval valuation.int)⌝
  case vc1.step.success => simp_all
  case vc3.h.post.success =>
    simp [VectorMapM.vectorToArrayPost]
    intro hB a rfl
    mvcgen
    have hv : (r.map (LC.eval valuation.bool)).reverse.map Bool.toInt =
        a.map (LC.eval valuation.int) := by
      apply Vector.toList_inj.mp
      simpa only [Vector.toList, Vector.toArray_map, Vector.toArray_reverse,
        Array.toList_map, Array.toList_reverse, List.map_reverse, List.map_map,
        Function.comp_apply] using hB
    rw [natCast_ofBits_eq_sum]
    simp only [LC.eval_sum, LC.eval_nsmul]
    change (∑ i : Fin n, (2 : ℤ) ^ i.val * a[i].eval valuation.int) =
      ∑ i : Fin n,
        (2 : ℤ) ^ i.val * ((r.map (LC.eval valuation.bool)).reverse[i]).toInt
    apply Finset.sum_congr rfl
    intro i _
    have hi := congrArg (fun v : Vector ℤ n => v[i]) hv
    have hi' : ((r.map (LC.eval valuation.bool)).reverse[i]).toInt =
        a[i].eval valuation.int := by simpa using hi
    rw [← hi']

end Complete

end Freigen.F2Z.Examples
