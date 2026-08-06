import Freigen.F2Z.Context
import Freigen.F2Z.Eff

namespace Freigen.F2Z

open Context

variable [ctx : Context]

def Circuit : Type → Type _ :=
  Free (Eff ctx) .constraint

instance : Monad (Circuit) :=
  inferInstanceAs (Monad (Free (Eff ctx) .constraint))

instance : LawfulMonad (Circuit) :=
  inferInstanceAs (LawfulMonad (Free (Eff ctx) .constraint))

def Hint : Type → Type _ :=
  Free (Eff ctx) .hint

instance : Monad (Hint) :=
  inferInstanceAs (Monad (Free (Eff ctx) .hint))

instance : LawfulMonad (Hint) :=
  inferInstanceAs (LawfulMonad (Free (Eff ctx) .hint))

def assertR1C (a b c : Wℤ) :
    Circuit (Cert $ fun ρ _ => ρ a * ρ b = ρ c) :=
  Free.op (E := Eff ctx) (γ := .constraint) (Eff.ConstraintEff.assertR1C a b c) nofun

def f2z (a : WBool) :
    Circuit ((x : Wℤ) × (Cert $ fun ρℤ ρBool => (Bool.toInt <| ρBool a) = ρℤ x)) :=
  Free.op (E := Eff ctx) (γ := .constraint) (Eff.ConstraintEff.f2z a) nofun

def hint {α} {argTps : List Eff.WitnessSide}
    (args : HList (Eff.WitnessSize.denoteW ctx.Wℤ ctx.WBool) argTps)
    (body : HList (Eff.WitnessSize.denoteF) argTps → Hint α):
    Circuit α :=
  Free.op (E := Eff ctx) (γ := .constraint) (Eff.ConstraintEff.hint argTps args α)
    (fun _ i => body i)

def writeWitness (a : Bool) : Hint WBool :=
  Free.op (E := Eff ctx) (γ := .hint) (Eff.HintEff.writeWitness a) nofun

end Freigen.F2Z
