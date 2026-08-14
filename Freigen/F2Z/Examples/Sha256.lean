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

instance : Coe (BitVec n) (U n) where
  coe w := {
    bits := { bitsLE := Vector.ofFn fun i => w[i] }
    intBits := Vector.ofFn fun i => w[i].toInt
  }

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

    h := g
    g := f
    f := e
    e ← U.sum #[d, h, S1, ch, k[i], w[i]]
    d := c
    c := b
    b := a
    a ← U.sum #[h, S1, ch, k[i], w[i], S0, maj]

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

end Circuit

section Sound

open Std.Do

abbrev chB (u v w : BitVec n) : BitVec n := (u &&& v) ^^^ ((~~~u) &&& w)

@[spec]
theorem U.ch_sound {u v w : U n} { hu : u.Valid ρ } { hv : v.Valid ρ } { hw : w.Valid ρ } :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.ch u v w) ⦃ ⇓ r => ⌜r.Valid ρ ∧ r.eval ρ = chB (u.eval ρ) (v.eval ρ) (w.eval ρ)⌝ ⦄ := by
  mvcgen [U.ch]

end Sound

end Freigen.F2Z.Examples
