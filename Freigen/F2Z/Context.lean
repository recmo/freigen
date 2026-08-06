import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.BooleanRing

namespace Freigen.F2Z

variable {F W} [Semiring F] [AddCommMonoid W]

class ModuleWithOne (F: outParam Type) W [Semiring F] [AddCommMonoid W]
    extends Module F W, One W

variable [ModuleWithOne F W]

instance (priority := 100) : NatCast W where
    natCast n := n • 1

structure Valuation
    (W : Type) [AddCommMonoid W] [ModuleWithOne F W] where
  toFun : W →ₗ[F] F
  one_map : toFun 1 = 1

instance : CoeFun (Valuation W) fun _ => W → F where
  coe v := v.toFun

class CertLogic {Wℤ} {WBool}
    [AddCommMonoid Wℤ] [ModuleWithOne ℤ Wℤ]
    [AddCommMonoid WBool] [ModuleWithOne Bool WBool]
    (C : (Valuation Wℤ → Valuation WBool → Prop) → Sort u) where
  derive :
    {ι : Type} →
    {P : ι → Valuation Wℤ → Valuation WBool → Prop} →
    {Q : Valuation Wℤ → Valuation WBool → Prop} →
    (∀ ρ₁ ρ₂, (∀ i, P i ρ₁ ρ₂) → Q ρ₁ ρ₂) →
    ((i : ι) → C (P i)) →
    C Q

class Context where
    Wℤ : Type
    WBool : Type
    [monoidWZ : AddCommMonoid Wℤ]
    [moduleWZ : ModuleWithOne ℤ Wℤ]
    [monoidWBool : AddCommMonoid WBool]
    [moduleWBool : ModuleWithOne Bool WBool]
    Cert : (Valuation Wℤ → Valuation WBool → Prop) → Sort u
    [cert : CertLogic Cert]

attribute [implicit_reducible]
  Context.monoidWZ
  Context.moduleWZ
  Context.monoidWBool
  Context.moduleWBool
  Context.cert

attribute [instance]
  Context.monoidWZ
  Context.moduleWZ
  Context.monoidWBool
  Context.moduleWBool
  Context.cert

end Freigen.F2Z
