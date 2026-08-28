import Freigen.F2Z.Examples.EcdsaP256.Radix32Impl

/-! Production ECDSA verifier using signed radix-32 variable-base multiplication. -/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open Modular
open P256

def computeVerificationSum (input : PreparedVerification) :
    Circuit AffineSlope.Point :=
  signedRadix32JointScalarMul input.u1 input.u2 input.q

def finishVerification (input : PreparedVerification) : Circuit Unit := do
  let sum ← computeVerificationSum input
  checkVerificationX input.r sum

/-- Verify an ECDSA-P256 signature over an already computed SHA-256 digest
using signed radix-32 Booth recoding for the variable-base scalar. -/
def verifyDigest (digest : U 256) (key : PublicKey)
    (sig : Signature) (aux : Aux) : Circuit Unit := do
  let input ← canonicalizeInput key sig aux
  let prepared ← prepareVerification digest input
  finishVerification prepared

def verifyDigestFromBits
    (inputs : Vector (LC Bool) verifyDigestInputBits) : Circuit Unit := do
  let values ← (verifyDigestInputWords inputs).mapM U.fromWord
  verifyDigest values[0] ⟨values[1], values[2]⟩
    ⟨values[3], values[4]⟩ ⟨values[5], values[6]⟩

/-- Constraint system for the signed radix-32 prehashed ECDSA verifier. -/
def verifyDigestCS : Unit × Semantics.CS :=
  Semantics.CSBuilder.runWithInputs verifyDigestFromBits

end Freigen.F2Z.Examples.EcdsaP256
