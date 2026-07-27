import Freigen.CompM.Basic
import Freigen.Eff
import Freigen.Free

namespace Freigen.Circuit

inductive Scope : Type u where
| constraint
| hint

inductive ConstraintEff where
| assert_r1c
| rangecheck (n: Nat)
| assert_spread (n: Nat)
| one
| hint (n : Nat) (α : Type)

inductive HintEff : Type u where
| write_witness

def Eff (W F : Type) : Scope → Type _
| .constraint => ConstraintEff
| .hint => HintEff

instance {W F} : Freigen.Eff.Spec (Γ := Scope) (Eff W F) where
  input := fun
  | .constraint, .assert_r1c => W × W × W
  | .constraint, .rangecheck _ => W
  | .constraint, .assert_spread _ => W × W
  | .constraint, .one => Unit
  | .constraint, .hint n _ => Vector W n
  | .hint, .write_witness => F
  output := fun
  | .constraint, .assert_r1c => Unit
  | .constraint, .rangecheck _ => Unit
  | .constraint, .assert_spread _ => Unit
  | .constraint, .one => W
  | .constraint, .hint _ α => α
  | .hint, .write_witness => W
  blockTag := fun
  | .constraint, .assert_r1c => PEmpty
  | .constraint, .rangecheck _ => PEmpty
  | .constraint, .assert_spread _ => PEmpty
  | .constraint, .one => PEmpty
  | .constraint, .hint _ _ => PUnit
  | .hint, .write_witness => PEmpty
  blockCtx := fun
  | .constraint, .assert_r1c => nofun
  | .constraint, .rangecheck _ => nofun
  | .constraint, .assert_spread _ => nofun
  | .constraint, .one => nofun
  | .constraint, .hint _ _ => fun _ => .hint
  | .hint, .write_witness => nofun
  blockInputs := fun
  | .constraint, .assert_r1c => nofun
  | .constraint, .rangecheck _ => nofun
  | .constraint, .assert_spread _ => nofun
  | .constraint, .one => nofun
  | .constraint, .hint n _ => fun _ => Vector F n
  | .hint, .write_witness => nofun
  blockOutputs := fun
  | .constraint, .assert_r1c => nofun
  | .constraint, .rangecheck _ => nofun
  | .constraint, .assert_spread _ => nofun
  | .constraint, .one => nofun
  | .constraint, .hint _ α => fun _ => α
  | .hint, .write_witness => nofun

end Circuit

def Circuit (F : Type) (W : Type) : Type → Type _ := Free (Circuit.Eff W F) .constraint

instance {F W} : Monad (Circuit F W) := inferInstanceAs (Monad (Free (Circuit.Eff W F) .constraint))
instance {F W} : LawfulMonad (Circuit F W) := inferInstanceAs (LawfulMonad (Free (Circuit.Eff W F) .constraint))

namespace Circuit

def Hint (F : Type) (W : Type) : Type → Type _ := Free (Circuit.Eff W F) .hint

instance {F W} : Monad (Hint F W) := inferInstanceAs (Monad (Free (Circuit.Eff W F) .hint))
instance {F W} : LawfulMonad (Hint F W) := inferInstanceAs (LawfulMonad (Free (Circuit.Eff W F) .hint))

def assert_r1c {F W} (a b c : W) : Circuit F W Unit :=
  Free.op (E := Circuit.Eff W F) (γ := .constraint) .assert_r1c (a, b, c) nofun

def rangecheck {F W} (n : Nat) (a : W) : Circuit F W Unit :=
  Free.op (E := Circuit.Eff W F) (γ := .constraint) (.rangecheck n) a nofun

def assert_spread {F W} (n : Nat) (a b : W) : Circuit F W Unit :=
  Free.op (E := Circuit.Eff W F) (γ := .constraint) (.assert_spread n) (a, b) nofun

def one {F W} : Circuit F W W :=
  Free.op (E := Circuit.Eff W F) (γ := .constraint) .one PUnit.unit nofun

def hint {F W α} (n : Nat) (args : Vector W n) (h : Hint F W α) : Circuit F W α :=
  Free.op (E := Circuit.Eff W F) (γ := .constraint) (.hint n α) args fun _ _ => h

def write_witness {F W} (a : F) : Hint F W W :=
  Free.op (E := Circuit.Eff W F) (γ := .hint) .write_witness a nofun

end Freigen.Circuit
