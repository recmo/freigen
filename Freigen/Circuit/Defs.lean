import Freigen.CompM.Basic
import Freigen.Eff
import Freigen.Free

namespace Freigen.Circuit

inductive Scope : Type u where
| constraint
| hint

inductive ConstraintEff (W : Type) where
| assert_r1c (a b c : W)
| rangecheck (n : Nat) (a : W)
| assert_spread (n : Nat) (a b : W)
| one
| hint (n : Nat) (α : Type) (args : Vector W n)

inductive HintEff (F : Type) : Type u where
| write_witness (a : F)

def Eff (W F : Type) : Scope → Type _
| .constraint => ConstraintEff W
| .hint => HintEff F

instance {W F} : Freigen.Eff.Spec (Γ := Scope) (Eff W F) where
  output := fun
  | .constraint, .assert_r1c _ _ _ => Unit
  | .constraint, .rangecheck _ _ => Unit
  | .constraint, .assert_spread _ _ _ => Unit
  | .constraint, .one => W
  | .constraint, .hint _ α _ => α
  | .hint, .write_witness _ => W
  blockTag := fun
  | .constraint, .assert_r1c _ _ _ => PEmpty
  | .constraint, .rangecheck _ _ => PEmpty
  | .constraint, .assert_spread _ _ _ => PEmpty
  | .constraint, .one => PEmpty
  | .constraint, .hint _ _ _ => PUnit
  | .hint, .write_witness _ => PEmpty
  blockCtx := fun
  | .constraint, .assert_r1c _ _ _ => nofun
  | .constraint, .rangecheck _ _ => nofun
  | .constraint, .assert_spread _ _ _ => nofun
  | .constraint, .one => nofun
  | .constraint, .hint _ _ _ => fun _ => .hint
  | .hint, .write_witness _ => nofun
  blockInputs := fun
  | .constraint, .assert_r1c _ _ _ => nofun
  | .constraint, .rangecheck _ _ => nofun
  | .constraint, .assert_spread _ _ _ => nofun
  | .constraint, .one => nofun
  | .constraint, .hint n _ _ => fun _ => Vector F n
  | .hint, .write_witness _ => nofun
  blockOutputs := fun
  | .constraint, .assert_r1c _ _ _ => nofun
  | .constraint, .rangecheck _ _ => nofun
  | .constraint, .assert_spread _ _ _ => nofun
  | .constraint, .one => nofun
  | .constraint, .hint _ α _ => fun _ => α
  | .hint, .write_witness _ => nofun

end Circuit

def Circuit (F : Type) (W : Type) : Type → Type _ := Free (Circuit.Eff W F) .constraint

instance {F W} : Monad (Circuit F W) := inferInstanceAs (Monad (Free (Circuit.Eff W F) .constraint))
instance {F W} : LawfulMonad (Circuit F W) := inferInstanceAs (LawfulMonad (Free (Circuit.Eff W F) .constraint))

namespace Circuit

def Hint (F : Type) (W : Type) : Type → Type _ := Free (Circuit.Eff W F) .hint

instance {F W} : Monad (Hint F W) := inferInstanceAs (Monad (Free (Circuit.Eff W F) .hint))
instance {F W} : LawfulMonad (Hint F W) := inferInstanceAs (LawfulMonad (Free (Circuit.Eff W F) .hint))

def assert_r1c {F W} (a b c : W) : Circuit F W Unit :=
  Free.op (E := Circuit.Eff W F) (γ := .constraint) (.assert_r1c a b c) nofun

def rangecheck {F W} (n : Nat) (a : W) : Circuit F W Unit :=
  Free.op (E := Circuit.Eff W F) (γ := .constraint) (.rangecheck n a) nofun

def assert_spread {F W} (n : Nat) (a b : W) : Circuit F W Unit :=
  Free.op (E := Circuit.Eff W F) (γ := .constraint) (.assert_spread n a b) nofun

def one {F W} : Circuit F W W :=
  Free.op (E := Circuit.Eff W F) (γ := .constraint) .one nofun

def hint {F W α} (n : Nat) (args : Vector W n)
    (h : Vector F n → Hint F W α) : Circuit F W α :=
  Free.op (E := Circuit.Eff W F) (γ := .constraint) (.hint n α args)
    (fun _ inputs => h inputs)

def write_witness {F W} (a : F) : Hint F W W :=
  Free.op (E := Circuit.Eff W F) (γ := .hint) (.write_witness a) nofun

-- def runWithHints {F} (c : Circuit F F α) : Option α :=

end Freigen.Circuit
