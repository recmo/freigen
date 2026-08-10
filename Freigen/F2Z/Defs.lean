import Freigen.F2Z.Context
import Freigen.F2Z.Eff

namespace Freigen.F2Z

open Context

variable [ctx : Context]

abbrev Circuit : Type → Type _ :=
  Free (Eff ctx) .constraint

instance : Monad (Circuit) :=
  inferInstanceAs (Monad (Free (Eff ctx) .constraint))

instance : LawfulMonad (Circuit) :=
  inferInstanceAs (LawfulMonad (Free (Eff ctx) .constraint))

abbrev Hint : Type → Type _ :=
  Free (Eff ctx) .hint

instance : Monad (Hint) :=
  inferInstanceAs (Monad (Free (Eff ctx) .hint))

instance : LawfulMonad (Hint) :=
  inferInstanceAs (LawfulMonad (Free (Eff ctx) .hint))

def assertR1C (a b c : Wℤ) : Circuit Unit :=
  Free.op (E := Eff ctx) (γ := .constraint) (Eff.ConstraintEff.assertR1C a b c) nofun

def f2z (a : WBool) : Circuit Wℤ :=
  Free.op (E := Eff ctx) (γ := .constraint) (Eff.ConstraintEff.f2z a) nofun

def hint {n : Nat} {argTps : List Eff.WitnessSide}
    (args : HList (Eff.WitnessSide.denoteW ctx.Wℤ ctx.WBool) argTps)
    (body : HList Eff.WitnessSide.denoteF argTps → Vector Bool n) :
    Circuit (Vector WBool n) :=
  Free.op (E := Eff ctx) (γ := .constraint) (Eff.ConstraintEff.hint argTps args n)
    (fun _ i => pure (body i))

end Freigen.F2Z
