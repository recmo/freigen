import Freigen.F2Z.Context
import Freigen.CompM.Basic
import Freigen.Eff
import Freigen.Free.Basic
import Freigen.Wheels

namespace Freigen.F2Z.Eff

inductive Scope : Type u
| constraint : Scope
| hint : Scope

inductive WitnessSide
| z : WitnessSide
| f₂ : WitnessSide

def WitnessSize.denoteW (Wℤ WBool : Type) : WitnessSide → Type
| WitnessSide.z  => Wℤ
| WitnessSide.f₂ => WBool

def WitnessSize.denoteF : WitnessSide → Type
| WitnessSide.z  => ℤ
| WitnessSide.f₂ => Bool

inductive ConstraintEff (ctx : Context) where
| assertR1C (a b c : ctx.Wℤ)
| f2z (a : ctx.WBool)
| hint (argTps : List WitnessSide)
    (args : HList (WitnessSize.denoteW ctx.Wℤ ctx.WBool) argTps) (α : Type)

inductive HintEff (ctx : Context) : Type u where
| writeWitness (a: Bool)

end Eff

def Eff (ctx : Context) : Eff.Scope → Type _
| .constraint => Eff.ConstraintEff ctx
| .hint => Eff.HintEff ctx

namespace Eff

open Context

instance [ctx : Context]:
    Freigen.Eff.Spec (Γ := Eff.Scope) (Eff ctx) where
  output := fun
    | .constraint, .assertR1C a b c => Cert $ fun ρ _ => ρ a * ρ b = ρ c
    | .constraint, .f2z a =>
      (x : ctx.Wℤ) × (Cert $ fun ρℤ ρBool => (Bool.toInt <| ρBool a) = ρℤ x)
    | .constraint, .hint _ _ α => α
    | .hint, .writeWitness _ => ctx.WBool
  blockTag := fun
    | .constraint, .assertR1C _ _ _ => PEmpty
    | .constraint, .f2z _ => PEmpty
    | .constraint, .hint _ _ _ => PUnit
    | .hint, .writeWitness _ => PEmpty
  blockCtx := fun
    | .constraint, .assertR1C _ _ _ => nofun
    | .constraint, .f2z _ => nofun
    | .constraint, .hint _ _ _ => fun _ => .hint
    | .hint, .writeWitness _ => nofun
  blockInputs := fun
    | .constraint, .assertR1C _ _ _ => nofun
    | .constraint, .f2z _ => nofun
    | .constraint, .hint argTps _ _ => fun _ => HList WitnessSize.denoteF argTps
    | .hint, .writeWitness _ => nofun
  blockOutputs := fun
    | .constraint, .assertR1C _ _ _ => nofun
    | .constraint, .f2z _ => fun _ => ctx.Wℤ
    | .constraint, .hint _ _ α => fun _ => α
    | .hint, .writeWitness _ => nofun

end Freigen.F2Z.Eff
