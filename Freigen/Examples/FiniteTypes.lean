import Freigen.Compile

namespace Freigen.Examples.FiniteTypes

open Freigen Ast

/-- The fast regression suite uses the AST's carrier directly.  It is definitionally equal to
    Mathlib's `ZMod` family; actual-Mathlib compatibility is checked separately. -/

inductive NoOp : Type

abbrev Source : ITree.HSig where
  op := NoOp
  input e := nomatch e
  output e := nomatch e
  branch e := nomatch e
  branchInput e := nomatch e
  branchOutput e := nomatch e

abbrev Target : Signature where
  op := NoOp
  input e := nomatch e
  output e := nomatch e
  branch e := nomatch e
  branchInput e := nomatch e
  branchOutput e := nomatch e

@[ast_compat] def noOpCompat : Signature.Compat Source Target where
  opRel e := nomatch e
  input {e} := nomatch e
  output {e} := nomatch e
  branch {e} := nomatch e
  branchInput {e} := nomatch e
  branchOutput {e} := nomatch e

def noOpRender : RenderSpec Target where
  opName e := nomatch e
  branches e := nomatch e

abbrev Circuit := Free Source

def finLiteralSource : Circuit (Fin 5) :=
  pure ⟨3, by decide⟩

def finLiteralReflected := reflect% finLiteralSource

example : Closed Target (.base (.fin 5)) := finLiteralReflected.1

def zmodLiteralSource : Circuit (ZModCarrier 7) :=
  pure 3

def zmodLiteralReflected := reflect% zmodLiteralSource

example : Closed Target (.base (.zmod 7)) := zmodLiteralReflected.1

def addFin (x : Fin 5) : Circuit (Fin 5) :=
  pure (x + 1)

def addFinSource : Circuit (Fin 5) :=
  addFin ⟨2, by decide⟩

def addFinReflected := reflect% addFinSource

example : Closed Target (.base (.fin 5)) := addFinReflected.1

def finValue (x : Fin 5) : Circuit Nat :=
  pure x.val

def finValueSource : Circuit Nat :=
  finValue ⟨2, by decide⟩

def finValueReflected := reflect% finValueSource

example : Closed Target (.base .nat) := finValueReflected.1

/-- Here `n` remains a runtime argument inside the spilled helpers.  The dependent `Fin (n + 1)`
    therefore uses the carrier representation, while the closed program still specializes to an
    ordinary Nat result. -/
def symbolicFinValue (n : Nat) (x : Fin (n + 1)) : Circuit Nat :=
  pure x.val

def symbolicFinCaller (n : Nat) : Circuit Nat :=
  symbolicFinValue n ⟨0, Nat.zero_lt_succ n⟩

def symbolicFinSource : Circuit Nat :=
  symbolicFinCaller 4

def symbolicFinReflected := reflect% symbolicFinSource

example : Closed Target (.base .nat) := symbolicFinReflected.1

def addZMod (x : ZModCarrier 7) : Circuit (ZModCarrier 7) :=
  pure (x + 1)

def addZModSource : Circuit (ZModCarrier 7) :=
  addZMod 2

def addZModReflected := reflect% addZModSource

example : Closed Target (.base (.zmod 7)) := addZModReflected.1

def zmodValue (x : ZModCarrier 7) : Circuit Int :=
  pure (ZModCarrier.toInt 7 x)

def zmodValueSource : Circuit Int :=
  zmodValue 3

def zmodValueReflected := reflect% zmodValueSource

example : Closed Target (.base .int) := zmodValueReflected.1
def intArithmeticSource : Circuit Int :=
  pure ((-4 : Int) * 3 + 2)

def intArithmeticReflected := reflect% intArithmeticSource

example : Closed Target (.base .int) := intArithmeticReflected.1

def zmodZeroArithmeticSource : Circuit (ZModCarrier 0) :=
  pure ((-4 : ZModCarrier 0) + 2)

def zmodZeroArithmeticReflected := reflect% zmodZeroArithmeticSource

example : Closed Target (.base (.zmod 0)) := zmodZeroArithmeticReflected.1

/-- A numeral used as a dependent type index is a specialization argument, not a runtime Nat
    argument.  Consequently the helper itself is compiled at the precise finite type. -/
def dependentFin {n : Nat} (x : Fin n) : Circuit (Fin n) :=
  pure x

def dependentFinSource : Circuit (Fin 5) :=
  dependentFin (n := 5) ⟨4, by decide⟩

def dependentFinReflected := reflect% dependentFinSource

example : Closed Target (.base (.fin 5)) := dependentFinReflected.1

def dependentZMod {n : Nat} (x : ZModCarrier n) : Circuit (ZModCarrier n) :=
  pure x

def dependentZModSource : Circuit (ZModCarrier 7) :=
  dependentZMod (n := 7) 6

def dependentZModReflected := reflect% dependentZModSource

example : Closed Target (.base (.zmod 7)) := dependentZModReflected.1

/-- The same dependent helper used at distinct literal indices produces distinct monomorphic
    helper bodies.  This is deliberately a single reflected program, so accidental key merging is
    observable as a missing `lam` in the serialized AST. -/
def polymorphicFinValue {n : Nat} (x : Fin n) : Circuit Nat :=
  pure x.val

def twoFinSpecializationsSource : Circuit Nat := do
  let five ← polymorphicFinValue (n := 5) ⟨3, by decide⟩
  let seven ← polymorphicFinValue (n := 7) ⟨4, by decide⟩
  pure (five + seven)

/--
info: AST reflection plan: [Freigen.Examples.FiniteTypes.polymorphicFinValue,
 Freigen.Examples.FiniteTypes.polymorphicFinValue]
-/
#guard_msgs in
#reflect_plan twoFinSpecializationsSource

def twoFinSpecializationsReflected := reflect% twoFinSpecializationsSource

example : Closed Target (.base .nat) := twoFinSpecializationsReflected.1

def checkedFinTag : Closed Target (.base (.fin 5)) := fun _ =>
  .natLit 7 fun value =>
    .checkedCast (.finTag 5) value fun tagged =>
      .ret tagged

example : CheckedCast.denote (.finTag 5) 4 = some ⟨4, by decide⟩ := rfl
example : CheckedCast.denote (.finTag 5) 5 = none := rfl
example : CheckedCast.denote (.zmodTag 7) 6 = some (6 : ZModCarrier 7) := rfl
example : CheckedCast.denote (.zmodTag 7) 7 = none := rfl
example : CheckedCast.denote (.zmodTag 0) (-3) = some (-3 : ZModCarrier 0) := rfl

/-- Symbolic bounds retain the carrier fallback; checked tagging is the explicit boundary back to
    a precise type once a concrete bound is available. -/
example (n : Nat) : (finRepr n).code = .nat := rfl
example (n : Nat) : (zmodRepr n).code = .int := rfl

end Freigen.Examples.FiniteTypes
