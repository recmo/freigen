import Freigen.F2Z.Examples.EcdsaP256.Impl

/-! Experimental signed radix-32 joint scalar multiplication. -/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open BigOperators
open Modular
open P256
open P256.Projective

set_option maxRecDepth 10000

structure Radix32Table where
  low : Vector AffineSlope.Point 16
  p16 : AffineSlope.Point

def materializeRadix32Multiples (P : Projective) :
    Circuit Radix32Table := do
  let table ← materializeMultiples P
  let p16 ← doubleMultiple 8 table[8]
  pure ⟨table, p16⟩

def applyPointSign (negative : LC ℤ) (P : AffineSlope.Point) :
    Circuit AffineSlope.Point := do
  let bits ← hint h![negative, P.Y.intVal]
    fun h![(s : Int), (y : Int)] =>
      let value := if s = 1 then (base.modulus : Int) - y else y
      if _h : 0 ≤ value then
        pure $ Vector.ofFn (n := 256) fun i => value.toNat.testBit i
      else fail s!"negative signed point coordinate {value}"
  let Y ← U.fromWord { bitsLE := bits }
  assertR1C negative
    (LC.ofConst (base.modulus : Int) - 2 • P.Y.intVal)
    (Y.intVal - P.Y.intVal)
  pure ⟨P.X, ⟨Y.intVal, 2⟩, P.infinity⟩

structure SignedDigit where
  oneHot : U 33

def SignedDigit.value (digit : SignedDigit) : LC ℤ :=
  ∑ slot : Fin 33, ((slot.val : Int) - 16) • digit.oneHot.intBits[slot]

def SignedDigit.magnitude (digit : SignedDigit) : LC ℤ :=
  ∑ slot : Fin 33,
    Int.natAbs ((slot.val : Int) - 16) • digit.oneHot.intBits[slot]

def SignedDigit.negative (digit : SignedDigit) : LC ℤ :=
  ∑ slot : Fin 16,
    digit.oneHot.intBits[(⟨slot.val, by omega⟩ : Fin 33)]

def SignedDigit.isSixteen (digit : SignedDigit) : LC ℤ :=
  digit.oneHot.intBits[0] + digit.oneHot.intBits[32]

def signedDigitIndicators (value : LC ℤ) : Circuit SignedDigit := do
  let oneHot ← indicators 33 (value + 16)
  pure ⟨oneHot⟩

def boothDigit (k : Fn) (i : Nat) (hi : i < 52) : LC ℤ :=
  if _h : i < 51 then
    let chunk := windowValue k (5 * i) 5 (by omega)
    let previous := if _hzero : i = 0 then 0
      else k.val.intBits[5 * i - 1]'(by omega)
    chunk + previous - 32 • k.val.intBits[5 * i + 4]'(by omega)
  else
    k.val.intBits[255] + k.val.intBits[254]

def selectRadix32Magnitude (digit : SignedDigit) (table : Radix32Table) :
    Circuit AffineSlope.Point := do
  let lowMagnitude := digit.magnitude - 16 • digit.isSixteen
  let low ← lookupPoint lowMagnitude table.low
  let X ← AffineSlope.selectCanonical digit.isSixteen table.p16.X low.X
  let Y ← AffineSlope.selectCanonical digit.isSixteen table.p16.Y low.Y
  pure ⟨X, Y, low.infinity - digit.isSixteen⟩

def selectSignedRadix32Point (digit : SignedDigit)
    (table : Radix32Table) : Circuit AffineSlope.Point := do
  let point ← selectRadix32Magnitude digit table
  applyPointSign digit.negative point

def signedRadix32Step (u1 u2 : Fn)
    (qTable : Radix32Table)
    (i : Nat) (hi : i < 255) (acc : AffineSlope.Point) :
    Circuit AffineSlope.Point := do
  let acc ← AffineSlope.doubleComplete acc
  let exponent := 254 - i
  let acc ← if _hq : exponent % 5 = 0 then do
    have hdigit : exponent / 5 < 52 := by omega
    let digit ← signedDigitIndicators (boothDigit u2 (exponent / 5) hdigit)
    let q ← selectSignedRadix32Point digit qTable
    AffineSlope.addComplete acc q
  else pure acc
  if _hg : exponent % 8 = 0 then do
    have hfit : exponent + 8 ≤ 256 := by omega
    let g ← lookupGeneratorByte (windowValue u1 exponent 8 hfit)
    AffineSlope.addComplete acc g
  else pure acc

def signedRadix32JointScalarMul (u1 u2 : Fn) (q : Projective) :
    Circuit AffineSlope.Point := do
  let qTable ← materializeRadix32Multiples q
  let topDigit ← signedDigitIndicators (boothDigit u2 51 (by omega))
  let initial ← selectSignedRadix32Point topDigit qTable
  WF.foldRange [:255] initial fun i hi acc =>
    signedRadix32Step u1 u2 qTable i hi.2.1 acc

end Freigen.F2Z.Examples.EcdsaP256
