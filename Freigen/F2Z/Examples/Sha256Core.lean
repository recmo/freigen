import Freigen.F2Z.Defs
import Freigen.F2Z.Gadgets
import Freigen.F2Z.Semantics
import Freigen.F2Z.Correctness.Basic
import Freigen.F2Z.Correctness.WFGen
import Batteries.Data.Int
import Batteries.Data.BitVec.Lemmas
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

def perm' (m : Vector Bool 768): Vector Bool 256 :=
  let mWords := Vector.ofFn fun i => BitVec.ofNat 32 $ Nat.ofBits fun (j : Fin 32) => m[i.val*32 + j.val]
  let sWords := Vector.ofFn fun i => BitVec.ofNat 32 $ Nat.ofBits fun (j : Fin 32) => m[512 + i.val*32 + j.val]
  let s' := perm mWords sWords
  Vector.ofFn fun i => s'[i.val / 32].toNat.testBit (i % 32)

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

instance : Coe (BitVec n) (U n) where
  coe w := {
    bits := { bitsLE := Vector.ofFn fun i => w[i] }
    intBits := Vector.ofFn fun i => w[i].toInt
  }

def U.ch (u v w : U n) : Circuit (U n) := do
  let chBits ← Vector.ofFnM (n:=n) fun i => do
    let h ← hint h![u.bits[i], v.bits[i], w.bits[i]] fun h![u, v, w] =>
      pure $ #v[(u && v) ^^ ((!u) && w)]
    pure h[0]
  let ch ← U.fromWord { bitsLE := chBits }
  let uv ← U.fromWord $ u.bits ^^^ v.bits
  let uw ← U.fromWord $ u.bits ^^^ w.bits
  assertR1C 0 0 $ v.intVal + w.intVal - uv.intVal + uw.intVal - 2 • ch.intVal
  pure ch

def U.maj (u v w : U n) : Circuit (U n) := do
  let majBits ← Vector.ofFnM (n:=n) fun i => do
    let h ← hint h![u.bits[i], v.bits[i], w.bits[i]] fun h![u, v, w] =>
      pure $ #v[(u && v) ^^ (u && w) ^^ (v && w)]
    pure h[0]
  let maj ← U.fromWord { bitsLE := majBits }
  let uvw ← U.fromWord $ u.bits ^^^ v.bits ^^^ w.bits
  assertR1C 0 0 $ u.intVal + v.intVal + w.intVal - uvw.intVal - 2 • maj.intVal
  pure maj

def permCircuit (m : Vector (Word 32) 16)
    (s : Vector (Word 32) 8) :
    Circuit (Vector (U 32) 8) := do
  let s ← s.mapM U.fromWord
  let mut w : Vector (U 32) 64 := default
  for h:i in [0:16] do
    w := w.set! i $ ←U.fromWord m[i]
  for i in [16:64] do
    let wi15 := w[i-15]!.bits
    let s0 ← U.fromWord $ wi15.rotateRight 7 ^^^ wi15.rotateRight 18 ^^^ (wi15 >>> 3)
    let wi2 := w[i-2]!.bits
    let s1 ← U.fromWord $ wi2.rotateRight 17 ^^^ wi2.rotateRight 19 ^^^ (wi2 >>> 10)
    w := w.set! i $ ←U.sum #[w[i-16]!, s0, w[i-7]!, s1]

  let mut a := s[0]
  let mut b := s[1]
  let mut c := s[2]
  let mut d := s[3]
  let mut e := s[4]
  let mut f := s[5]
  let mut g := s[6]
  let mut h := s[7]

  for hi:i in [0:64] do
    let S1 ← U.fromWord $ e.bits.rotateRight 6 ^^^ e.bits.rotateRight 11 ^^^ e.bits.rotateRight 25
    let ch ← U.ch e f g
    let S0 ← U.fromWord $ a.bits.rotateRight 2 ^^^ a.bits.rotateRight 13 ^^^ a.bits.rotateRight 22
    let maj ← U.maj a b c

    let oldH := h

    h := g
    g := f
    f := e
    e ← U.sum #[d, oldH, S1, ch, k[i], w[i]]
    d := c
    c := b
    b := a
    a ← U.sum #[oldH, S1, ch, k[i], w[i], S0, maj]

  pure $ #v[
    ←U.sum #[s[0], a],
    ←U.sum #[s[1], b],
    ←U.sum #[s[2], c],
    ←U.sum #[s[3], d],
    ←U.sum #[s[4], e],
    ←U.sum #[s[5], f],
    ←U.sum #[s[6], g],
    ←U.sum #[s[7], h]
  ]

def permCirc' (inp : Vector (LC Bool) 768): Circuit (Vector (LC Bool) 256) := do
  let m := Vector.ofFn fun wi => Word.mk $ Vector.ofFn fun bi => inp[wi.val * 32 + bi.val]
  let s := Vector.ofFn fun si => Word.mk $ Vector.ofFn fun bi => inp[512 + si.val * 32 + bi.val]
  let out ← permCircuit m s
  pure $ Vector.ofFn fun si => out[si.val / 32].bits.bitsLE[si.val % 32]

abbrev sha256CS : Vector (LC Bool) 256 × Semantics.CS := Semantics.CSBuilder.runWithInputs permCirc'

#eval sha256CS.2.stats

#eval Semantics.Witgen.runWithInputs permCirc' (Vector.ofFn fun i => 0) |>.map (·.size)

end Circuit

section Sound

open Std.Do

abbrev chB (u v w : Bool) : Bool := (u && v) ^^ ((!u) && w)
abbrev chBV (u v w : BitVec n) : BitVec n := (u &&& v) ^^^ ((~~~u) &&& w)
abbrev majB (u v w : Bool) : Bool := (u && v) ^^ (u && w) ^^ (v && w)
abbrev majBV (u v w : BitVec n) : BitVec n :=
  (u &&& v) ^^^ (u &&& w) ^^^ (v &&& w)

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

private theorem bitVec_toNat_eq_sum (x : BitVec n) :
    (x.toNat : Int) =
      ∑ k : Fin n, 2 ^ k.val * (x[k.val]).toInt := by
  rw [← natCast_ofBits_eq_sum]
  congr 1
  rw [show (fun i : Fin n => x[i.val]) =
      (fun i => x.toNat.testBit i.val) by
    funext i
    exact BitVec.getElem_eq_testBit_toNat x i.val i.isLt]
  exact (Nat.ofBits_testBit x.toNat n |>.trans
    (Nat.mod_eq_of_lt x.isLt)).symm

private theorem ch_arith (u v w : BitVec n) :
    (v.toNat : Int) + w.toNat - (u ^^^ v).toNat + (u ^^^ w).toNat =
      2 * ((chBV u v w).toNat : Int) := by
  rw [bitVec_toNat_eq_sum, bitVec_toNat_eq_sum,
    bitVec_toNat_eq_sum, bitVec_toNat_eq_sum,
    bitVec_toNat_eq_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [chBV, BitVec.getElem_xor, BitVec.getElem_and,
    BitVec.getElem_not]
  generalize u[i.val] = ub
  generalize v[i.val] = vb
  generalize w[i.val] = wb
  cases ub <;> cases vb <;> cases wb <;> norm_num <;> ring

private theorem maj_arith (u v w : BitVec n) :
    (u.toNat : Int) + v.toNat + w.toNat - (u ^^^ v ^^^ w).toNat =
      2 * ((majBV u v w).toNat : Int) := by
  rw [bitVec_toNat_eq_sum, bitVec_toNat_eq_sum,
    bitVec_toNat_eq_sum, bitVec_toNat_eq_sum,
    bitVec_toNat_eq_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [majBV, BitVec.getElem_xor, BitVec.getElem_and]
  generalize u[i.val] = ub
  generalize v[i.val] = vb
  generalize w[i.val] = wb
  cases ub <;> cases vb <;> cases wb <;> norm_num <;> ring

private theorem U.eval_eq_ofFnLE_of_valid (u : U n) (h : u.Valid ρ) :
    u.eval ρ = BitVec.ofFnLE (fun i => u.bits.bitsLE[i].eval ρ.bool) := by
  apply BitVec.toNat_inj.mp
  simp [U.eval, U.eval_intVal_eq_evalZ u h, Word.evalZ,
    Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _)]

private theorem U.intVal_eval_eq_eval_toNat (u : U n) (h : u.Valid ρ) :
    u.intVal.eval ρ.int = (u.eval ρ).toNat := by
  rw [U.eval_eq_ofFnLE_of_valid u h, U.eval_intVal_eq_evalZ u h]
  simp [Word.evalZ]

private theorem U.eval_eq_xor_of_bits_eq (out u v : U n)
    (hout : out.Valid ρ) (hu : u.Valid ρ) (hv : v.Valid ρ)
    (hbits : out.bits = u.bits ^^^ v.bits) :
    out.eval ρ = u.eval ρ ^^^ v.eval ρ := by
  rw [U.eval_eq_ofFnLE_of_valid out hout,
    U.eval_eq_ofFnLE_of_valid u hu,
    U.eval_eq_ofFnLE_of_valid v hv]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_ofFnLE, BitVec.getElem_xor]
  rw [hbits]
  change LC.eval ρ.bool
      (Vector.zipWith (· + ·) u.bits.bitsLE v.bits.bitsLE)[i] = _
  rw [Vector.getElem_zipWith hi, LC.eval_add]
  generalize LC.eval ρ.bool u.bits.bitsLE[i] = ub
  generalize LC.eval ρ.bool v.bits.bitsLE[i] = vb
  cases ub <;> cases vb <;> rfl

private theorem U.eval_eq_chBV_of_bits (out u v w : U n)
    (hout : out.Valid ρ) (hu : u.Valid ρ) (hv : v.Valid ρ)
    (hw : w.Valid ρ)
    (hbits : ∀ i : Fin n, out.bits[i].eval ρ.bool =
      chB (u.bits[i].eval ρ.bool) (v.bits[i].eval ρ.bool)
        (w.bits[i].eval ρ.bool)) :
    out.eval ρ = chBV (u.eval ρ) (v.eval ρ) (w.eval ρ) := by
  rw [U.eval_eq_ofFnLE_of_valid out hout,
    U.eval_eq_ofFnLE_of_valid u hu,
    U.eval_eq_ofFnLE_of_valid v hv,
    U.eval_eq_ofFnLE_of_valid w hw]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_ofFnLE, chBV, BitVec.getElem_xor,
    BitVec.getElem_and, BitVec.getElem_not]
  exact hbits ⟨i, hi⟩

private theorem U.eval_eq_xor3_of_bits_eq (out u v w : U n)
    (hout : out.Valid ρ) (hu : u.Valid ρ) (hv : v.Valid ρ)
    (hw : w.Valid ρ)
    (hbits : out.bits = u.bits ^^^ v.bits ^^^ w.bits) :
    out.eval ρ = u.eval ρ ^^^ v.eval ρ ^^^ w.eval ρ := by
  rw [U.eval_eq_ofFnLE out hout, U.eval_eq_ofFnLE u hu,
    U.eval_eq_ofFnLE v hv, U.eval_eq_ofFnLE w hw]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_ofFnLE, BitVec.getElem_xor]
  rw [hbits]
  change LC.eval ρ.bool
      (Vector.zipWith (· + ·)
        (Vector.zipWith (· + ·) u.bits.bitsLE v.bits.bitsLE)
        w.bits.bitsLE)[i] = _
  rw [Vector.getElem_zipWith hi, Vector.getElem_zipWith hi,
    LC.eval_add, LC.eval_add]
  generalize LC.eval ρ.bool u.bits.bitsLE[i] = ub
  generalize LC.eval ρ.bool v.bits.bitsLE[i] = vb
  generalize LC.eval ρ.bool w.bits.bitsLE[i] = wb
  cases ub <;> cases vb <;> cases wb <;> rfl

private theorem U.eval_eq_majBV_of_bits (out u v w : U n)
    (hout : out.Valid ρ) (hu : u.Valid ρ) (hv : v.Valid ρ)
    (hw : w.Valid ρ)
    (hbits : ∀ i : Fin n, out.bits[i].eval ρ.bool =
      majB (u.bits[i].eval ρ.bool) (v.bits[i].eval ρ.bool)
        (w.bits[i].eval ρ.bool)) :
    out.eval ρ = majBV (u.eval ρ) (v.eval ρ) (w.eval ρ) := by
  rw [U.eval_eq_ofFnLE out hout, U.eval_eq_ofFnLE u hu,
    U.eval_eq_ofFnLE v hv, U.eval_eq_ofFnLE w hw]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_ofFnLE, majBV, BitVec.getElem_xor,
    BitVec.getElem_and]
  exact hbits ⟨i, hi⟩

private theorem Word.lceq_xor (leftVal rightVal : Nat → Bool)
    (leftU rightU leftV rightV : Word n) (i : Fin n)
    (hu : WF.LCEq leftVal rightVal leftU[i] rightU[i])
    (hv : WF.LCEq leftVal rightVal leftV[i] rightV[i]) :
    WF.LCEq leftVal rightVal
      (leftU ^^^ leftV).bitsLE[i] (rightU ^^^ rightV).bitsLE[i] := by
  unfold WF.LCEq at hu hv ⊢
  rw [show leftU ^^^ leftV =
      { bitsLE := Vector.zipWith (· + ·) leftU.bitsLE leftV.bitsLE } by rfl,
    show rightU ^^^ rightV =
      { bitsLE := Vector.zipWith (· + ·) rightU.bitsLE rightV.bitsLE } by rfl]
  simp only [Fin.getElem_fin, Vector.getElem_zipWith i.isLt, LC.eval_add]
  change LC.eval leftVal leftU.bitsLE[i] =
    LC.eval rightVal rightU.bitsLE[i] at hu
  change LC.eval leftVal leftV.bitsLE[i] =
    LC.eval rightVal rightV.bitsLE[i] at hv
  simp only [Fin.getElem_fin] at hu hv
  rw [hu, hv]

private theorem Word.lceq_xor3 (leftVal rightVal : Nat → Bool)
    (leftU rightU leftV rightV leftW rightW : Word n) (i : Fin n)
    (hu : WF.LCEq leftVal rightVal leftU[i] rightU[i])
    (hv : WF.LCEq leftVal rightVal leftV[i] rightV[i])
    (hw : WF.LCEq leftVal rightVal leftW[i] rightW[i]) :
    WF.LCEq leftVal rightVal
      (leftU ^^^ leftV ^^^ leftW).bitsLE[i]
      (rightU ^^^ rightV ^^^ rightW).bitsLE[i] := by
  exact Word.lceq_xor leftVal rightVal
    (leftU ^^^ leftV) (rightU ^^^ rightV) leftW rightW i
    (Word.lceq_xor leftVal rightVal leftU rightU leftV rightV i hu hv) hw

private theorem ch_argsEq (leftVal rightVal : WF.Valuation)
    (uL uR vL vR wL wR : U n) (i : Fin n)
    (hu : WF.LCEq leftVal.bool rightVal.bool uL.bits[i] uR.bits[i])
    (hv : WF.LCEq leftVal.bool rightVal.bool vL.bits[i] vR.bits[i])
    (hw : WF.LCEq leftVal.bool rightVal.bool wL.bits[i] wR.bits[i]) :
    WF.ArgsEq leftVal rightVal h![uL.bits[i], vL.bits[i], wL.bits[i]]
      h![uR.bits[i], vR.bits[i], wR.bits[i]] := by
  unfold WF.ArgsEq
  simp only [WF.evalArgs]
  unfold WF.LCEq at hu hv hw
  rw [hu, hv, hw]

@[spec]
theorem U.ch_sound {u v w : U n} { hu : u.Valid ρ } { hv : v.Valid ρ } { hw : w.Valid ρ } :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.ch u v w) ⦃ ⇓ r => ⌜r.Valid ρ ∧ r.eval ρ = chBV (u.eval ρ) (v.eval ρ) (w.eval ρ)⌝ ⦄ := by
  mvcgen [U.ch] invariants
  · fun _ _ _ => ⌜True⌝
  case vc1 => simp
  case vc3 =>
    rename_i chBits ch hch uv huv uw huw hass
    rcases hch with ⟨_, hchValid⟩
    rcases huv with ⟨huvBits, huvValid⟩
    rcases huw with ⟨huwBits, huwValid⟩
    refine ⟨hchValid, ?_⟩
    have huvEval := U.eval_eq_xor_of_bits_eq uv u v huvValid hu hv huvBits
    have huwEval := U.eval_eq_xor_of_bits_eq uw u w huwValid hu hw huwBits
    have harith := ch_arith (u.eval ρ) (v.eval ρ) (w.eval ρ)
    rw [← huvEval, ← huwEval,
      ← U.intVal_eval_eq_eval_toNat v hv,
      ← U.intVal_eval_eq_eval_toNat w hw,
      ← U.intVal_eval_eq_eval_toNat uv huvValid,
      ← U.intVal_eval_eq_eval_toNat uw huwValid] at harith
    simp only [LC.eval_zero, zero_mul, LC.eval_add, LC.eval_sub,
      two_nsmul] at hass
    have hchValue :
        ch.intVal.eval ρ.int =
          ((chBV (u.eval ρ) (v.eval ρ) (w.eval ρ)).toNat : Int) := by
      linarith
    rw [show ch.eval ρ = BitVec.ofNat n (ch.intVal.eval ρ.int).toNat by rfl]
    rw [hchValue]
    change BitVec.ofNat n
      (chBV (u.eval ρ) (v.eval ρ) (w.eval ρ)).toNat = _
    simpa using BitVec.ofNat_toNat n
      (chBV (u.eval ρ) (v.eval ρ) (w.eval ρ))

@[spec]
theorem U.ch_complete {u v w : U n} {hu : u.Valid ρ}
    {hv : v.Valid ρ} {hw : w.Valid ρ} :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.ch u v w)
    ⦃ ⇓ r => ⌜r.Valid ρ ∧
      r.eval ρ = chBV (u.eval ρ) (v.eval ρ) (w.eval ρ)⌝ ⦄ := by
  unfold U.ch
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun chBits => ⌜∀ i : Fin n,
    chBits[i].eval ρ.bool = chB
      (u.bits[i].eval ρ.bool) (v.bits[i].eval ρ.bool)
      (w.bits[i].eval ρ.bool)⌝)
  case hx =>
    mvcgen invariants
    · fun i hi xs => ⌜∀ j : Fin i,
        xs[j].eval ρ.bool = chB
          (u.bits[j.castLE hi].eval ρ.bool)
          (v.bits[j.castLE hi].eval ρ.bool)
          (w.bits[j.castLE hi].eval ρ.bool)⌝
    case vc1 =>
      rename_i i hi xs
      simp only [WF.evalArgs, WF.interpHint, Free.interp_pure]
      intro hprefix
      let ix : Fin n := ⟨i, hi⟩
      refine ⟨#v[chB (u.bits[ix].eval ρ.bool)
        (v.bits[ix].eval ρ.bool) (w.bits[ix].eval ρ.bool)], by rfl, ?_⟩
      change ∀ j : Fin (i + 1), _
      intro j
      by_cases hj : j.val < i
      · have hcast :
            (⟨j.val, hj⟩ : Fin i).castLE (Nat.le_of_lt hi) =
              j.castLE (Nat.succ_le_of_lt hi) := Fin.ext rfl
        have hold := hprefix ⟨j.val, hj⟩
        rw [hcast] at hold
        simpa [Vector.getElem_push, hj] using hold
      · have hjEq : j.val = i := by omega
        have hcast : j.castLE (Nat.succ_le_of_lt hi) = ix := Fin.ext hjEq
        rw [hcast]
        simp [hjEq, ix]
    case vc2 => simp
    case vc3 => simp
  case hf =>
    intro chBits
    mvcgen
    case vc1 =>
      rename_i hbits ch hch uv huv uw huw
      rcases hch with ⟨hchBits, hchValid⟩
      rcases huv with ⟨huvBits, huvValid⟩
      rcases huw with ⟨huwBits, huwValid⟩
      have hchEval :
          ch.eval ρ = chBV (u.eval ρ) (v.eval ρ) (w.eval ρ) := by
        apply U.eval_eq_chBV_of_bits ch u v w hchValid hu hv hw
        intro i
        rw [hchBits]
        exact hbits i
      have huvEval := U.eval_eq_xor_of_bits_eq uv u v huvValid hu hv huvBits
      have huwEval := U.eval_eq_xor_of_bits_eq uw u w huwValid hu hw huwBits
      have harith := ch_arith (u.eval ρ) (v.eval ρ) (w.eval ρ)
      rw [← huvEval, ← huwEval,
        ← U.intVal_eval_eq_eval_toNat v hv,
        ← U.intVal_eval_eq_eval_toNat w hw,
        ← U.intVal_eval_eq_eval_toNat uv huvValid,
        ← U.intVal_eval_eq_eval_toNat uw huwValid] at harith
      have hchInt := U.intVal_eval_eq_eval_toNat ch hchValid
      rw [hchEval] at hchInt
      constructor
      · simp only [LC.eval_zero, zero_mul, LC.eval_add, LC.eval_sub,
          two_nsmul]
        linarith
      · change ch.Valid ρ ∧
          ch.eval ρ = chBV (u.eval ρ) (v.eval ρ) (w.eval ρ)
        exact ⟨hchValid, hchEval⟩

@[spec]
theorem U.maj_sound {u v w : U n} {hu : u.Valid ρ}
    {hv : v.Valid ρ} {hw : w.Valid ρ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.maj u v w)
    ⦃ ⇓ r => ⌜r.Valid ρ ∧
      r.eval ρ = majBV (u.eval ρ) (v.eval ρ) (w.eval ρ)⌝ ⦄ := by
  mvcgen [U.maj] invariants
  · fun _ _ _ => ⌜True⌝
  case vc1 => simp
  case vc3 =>
    rename_i majBits maj hmaj uvw huvw hass
    rcases hmaj with ⟨_, hmajValid⟩
    rcases huvw with ⟨huvwBits, huvwValid⟩
    refine ⟨hmajValid, ?_⟩
    have huvwEval := U.eval_eq_xor3_of_bits_eq uvw u v w
      huvwValid hu hv hw huvwBits
    have harith := maj_arith (u.eval ρ) (v.eval ρ) (w.eval ρ)
    rw [← huvwEval,
      ← U.intVal_eval_eq_eval_toNat u hu,
      ← U.intVal_eval_eq_eval_toNat v hv,
      ← U.intVal_eval_eq_eval_toNat w hw,
      ← U.intVal_eval_eq_eval_toNat uvw huvwValid] at harith
    simp only [LC.eval_zero, zero_mul, LC.eval_add, LC.eval_sub,
      two_nsmul] at hass
    have hmajValue :
        maj.intVal.eval ρ.int =
          ((majBV (u.eval ρ) (v.eval ρ) (w.eval ρ)).toNat : Int) := by
      linarith
    rw [show maj.eval ρ =
      BitVec.ofNat n (maj.intVal.eval ρ.int).toNat by rfl, hmajValue]
    change BitVec.ofNat n
      (majBV (u.eval ρ) (v.eval ρ) (w.eval ρ)).toNat = _
    simpa using BitVec.ofNat_toNat n
      (majBV (u.eval ρ) (v.eval ρ) (w.eval ρ))

@[spec]
theorem U.maj_complete {u v w : U n} {hu : u.Valid ρ}
    {hv : v.Valid ρ} {hw : w.Valid ρ} :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.maj u v w)
    ⦃ ⇓ r => ⌜r.Valid ρ ∧
      r.eval ρ = majBV (u.eval ρ) (v.eval ρ) (w.eval ρ)⌝ ⦄ := by
  unfold U.maj
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun majBits => ⌜∀ i : Fin n,
    majBits[i].eval ρ.bool = majB
      (u.bits[i].eval ρ.bool) (v.bits[i].eval ρ.bool)
      (w.bits[i].eval ρ.bool)⌝)
  case hx =>
    mvcgen invariants
    · fun i hi xs => ⌜∀ j : Fin i,
        xs[j].eval ρ.bool = majB
          (u.bits[j.castLE hi].eval ρ.bool)
          (v.bits[j.castLE hi].eval ρ.bool)
          (w.bits[j.castLE hi].eval ρ.bool)⌝
    case vc1 =>
      rename_i i hi xs
      simp only [WF.evalArgs, WF.interpHint, Free.interp_pure]
      intro hprefix
      let ix : Fin n := ⟨i, hi⟩
      refine ⟨#v[majB (u.bits[ix].eval ρ.bool)
        (v.bits[ix].eval ρ.bool) (w.bits[ix].eval ρ.bool)], by rfl, ?_⟩
      intro j
      by_cases hj : j.val < i
      · have hcast :
            (⟨j.val, hj⟩ : Fin i).castLE (Nat.le_of_lt hi) =
              j.castLE (Nat.succ_le_of_lt hi) := Fin.ext rfl
        have hold := hprefix ⟨j.val, hj⟩
        rw [hcast] at hold
        simpa [Vector.getElem_push, hj] using hold
      · have hjEq : j.val = i := by omega
        have hcast : j.castLE (Nat.succ_le_of_lt hi) = ix := Fin.ext hjEq
        rw [hcast]
        simp [hjEq, ix]
    case vc2 => simp
    case vc3 => simp
  case hf =>
    intro majBits
    mvcgen
    case vc1 =>
      rename_i hbits maj hmaj uvw huvw
      rcases hmaj with ⟨hmajBits, hmajValid⟩
      rcases huvw with ⟨huvwBits, huvwValid⟩
      have hmajEval :
          maj.eval ρ = majBV (u.eval ρ) (v.eval ρ) (w.eval ρ) := by
        apply U.eval_eq_majBV_of_bits maj u v w hmajValid hu hv hw
        intro i
        rw [hmajBits]
        exact hbits i
      have huvwEval := U.eval_eq_xor3_of_bits_eq uvw u v w
        huvwValid hu hv hw huvwBits
      have harith := maj_arith (u.eval ρ) (v.eval ρ) (w.eval ρ)
      rw [← huvwEval,
        ← U.intVal_eval_eq_eval_toNat u hu,
        ← U.intVal_eval_eq_eval_toNat v hv,
        ← U.intVal_eval_eq_eval_toNat w hw,
        ← U.intVal_eval_eq_eval_toNat uvw huvwValid] at harith
      have hmajInt := U.intVal_eval_eq_eval_toNat maj hmajValid
      rw [hmajEval] at hmajInt
      constructor
      · simp only [LC.eval_zero, zero_mul, LC.eval_add, LC.eval_sub,
          two_nsmul]
        linarith
      · exact ⟨hmajValid, hmajEval⟩

theorem U.ch_wf :
    WF.GadgetSpec
      (fun leftVal rightVal
          (left right : U n × U n × U n) =>
        (WF.LCEq leftVal.int rightVal.int
            left.1.intVal right.1.intVal ∧
          ∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
            left.1.bits[i] right.1.bits[i]) ∧
        (WF.LCEq leftVal.int rightVal.int
            left.2.1.intVal right.2.1.intVal ∧
          ∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
            left.2.1.bits[i] right.2.1.bits[i]) ∧
        (WF.LCEq leftVal.int rightVal.int
            left.2.2.intVal right.2.2.intVal ∧
          ∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
            left.2.2.bits[i] right.2.2.bits[i]))
      (fun x => U.ch x.1 x.2.1 x.2.2)
      (fun leftVal rightVal left right =>
        WF.LCEq leftVal.int rightVal.int left.intVal right.intVal ∧
        ∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
          left.bits[i] right.bits[i]) := by
  unfold WF.GadgetSpec
  intro left right
  dsimp only
  unfold U.ch
  apply (WF.Rel.vectorOfFnM
    (S := fun i leftVal rightVal leftOut rightOut =>
      WF.LCEq leftVal.bool rightVal.bool leftOut rightOut) ?_).bind
  ·
    wfgen' using [U.fromWord_wf]
    all_goals apply Word.lceq_xor <;> grind
  · intro i P _ _ hP
    wfgen'
    case vc1 hrel =>
      rcases hrel with ⟨_, values, _, _, hleft, hright⟩
      unfold WF.LCEq
      simp only [Fin.getElem_fin]
      exact (hleft j.val j.isLt).trans (hright j.val j.isLt).symm
    case vc2 => exact ⟨Nat.le_refl 0, Nat.zero_lt_one, rfl⟩
    case vc3 hambient =>
      have hinput := hP leftVal rightVal hambient
      have hargs := ch_argsEq leftVal rightVal
        left.1 right.1 left.2.1 right.2.1 left.2.2 right.2.2 i
        (hinput.1.2 i) (hinput.2.1.2 i) (hinput.2.2.2 i)
      unfold WF.ArgsEq at hargs
      rw [hargs]
    case vc4 hambient =>
      have hinput := hP leftVal rightVal hambient
      exact ch_argsEq leftVal rightVal
        left.1 right.1 left.2.1 right.2.1 left.2.2 right.2.2 i
        (hinput.1.2 i) (hinput.2.1.2 i) (hinput.2.2.2 i)

theorem U.maj_wf :
    WF.GadgetSpec
      (fun leftVal rightVal
          (left right : U n × U n × U n) =>
        (WF.LCEq leftVal.int rightVal.int
            left.1.intVal right.1.intVal ∧
          ∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
            left.1.bits[i] right.1.bits[i]) ∧
        (WF.LCEq leftVal.int rightVal.int
            left.2.1.intVal right.2.1.intVal ∧
          ∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
            left.2.1.bits[i] right.2.1.bits[i]) ∧
        (WF.LCEq leftVal.int rightVal.int
            left.2.2.intVal right.2.2.intVal ∧
          ∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
            left.2.2.bits[i] right.2.2.bits[i]))
      (fun x => U.maj x.1 x.2.1 x.2.2)
      (fun leftVal rightVal left right =>
        WF.LCEq leftVal.int rightVal.int left.intVal right.intVal ∧
        ∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
          left.bits[i] right.bits[i]) := by
  unfold WF.GadgetSpec
  intro left right
  dsimp only
  unfold U.maj
  apply (WF.Rel.vectorOfFnM
    (S := fun i leftVal rightVal leftOut rightOut =>
      WF.LCEq leftVal.bool rightVal.bool leftOut rightOut) ?_).bind
  · wfgen' using [U.fromWord_wf]
    all_goals apply Word.lceq_xor3 <;> grind
  · intro i P _ _ hP
    wfgen'
    case vc1 hrel =>
      rcases hrel with ⟨_, values, _, _, hleft, hright⟩
      unfold WF.LCEq
      simp only [Fin.getElem_fin]
      exact (hleft j.val j.isLt).trans (hright j.val j.isLt).symm
    case vc2 => exact ⟨Nat.le_refl 0, Nat.zero_lt_one, rfl⟩
    case vc3 hambient =>
      have hinput := hP leftVal rightVal hambient
      have hargs := ch_argsEq leftVal rightVal
        left.1 right.1 left.2.1 right.2.1 left.2.2 right.2.2 i
        (hinput.1.2 i) (hinput.2.1.2 i) (hinput.2.2.2 i)
      unfold WF.ArgsEq at hargs
      rw [hargs]
    case vc4 hambient =>
      have hinput := hP leftVal rightVal hambient
      exact ch_argsEq leftVal rightVal
        left.1 right.1 left.2.1 right.2.1 left.2.2 right.2.2 i
        (hinput.1.2 i) (hinput.2.1.2 i) (hinput.2.2.2 i)

@[spec 0]
theorem U.ch_sound_frame {u v w : U n} (hu : u.Valid ρ)
    (hv : v.Valid ρ) (hw : w.Valid ρ) (P : Prop) :
    ⦃⌜P⌝⦄ Sound.interp ρ (U.ch u v w)
    ⦃ ⇓ r => ⌜P ∧ r.Valid ρ ∧
      r.eval ρ = chBV (u.eval ρ) (v.eval ρ) (w.eval ρ)⌝ ⦄ := by
  mvcgen
  case vc1 => tauto
  case vc2 => exact fun _ => hu
  case vc3 => exact fun _ => hv
  case vc4 => exact fun _ => hw

@[spec 0]
theorem U.ch_complete_frame {u v w : U n} (hu : u.Valid ρ)
    (hv : v.Valid ρ) (hw : w.Valid ρ) (P : Prop) :
    ⦃⌜P⌝⦄ Complete.interp ρ (U.ch u v w)
    ⦃ ⇓ r => ⌜P ∧ r.Valid ρ ∧
      r.eval ρ = chBV (u.eval ρ) (v.eval ρ) (w.eval ρ)⌝ ⦄ := by
  mvcgen
  case vc1 => tauto
  case vc2 => exact fun _ => hu
  case vc3 => exact fun _ => hv
  case vc4 => exact fun _ => hw

@[spec 0]
theorem U.maj_sound_frame {u v w : U n} (hu : u.Valid ρ)
    (hv : v.Valid ρ) (hw : w.Valid ρ) (P : Prop) :
    ⦃⌜P⌝⦄ Sound.interp ρ (U.maj u v w)
    ⦃ ⇓ r => ⌜P ∧ r.Valid ρ ∧
      r.eval ρ = majBV (u.eval ρ) (v.eval ρ) (w.eval ρ)⌝ ⦄ := by
  mvcgen
  case vc1 => tauto
  case vc2 => exact fun _ => hu
  case vc3 => exact fun _ => hv
  case vc4 => exact fun _ => hw

@[spec 0]
theorem U.maj_complete_frame {u v w : U n} (hu : u.Valid ρ)
    (hv : v.Valid ρ) (hw : w.Valid ρ) (P : Prop) :
    ⦃⌜P⌝⦄ Complete.interp ρ (U.maj u v w)
    ⦃ ⇓ r => ⌜P ∧ r.Valid ρ ∧
      r.eval ρ = majBV (u.eval ρ) (v.eval ρ) (w.eval ρ)⌝ ⦄ := by
  mvcgen
  case vc1 => tauto
  case vc2 => exact fun _ => hu
  case vc3 => exact fun _ => hv
  case vc4 => exact fun _ => hw

end Sound

end Freigen.F2Z.Examples
