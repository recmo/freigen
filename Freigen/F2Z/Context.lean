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

@[simp]
theorem Valuation.one_apply (ρ : Valuation W) : ρ (1 : W) = 1 :=
  ρ.one_map

@[simp]
theorem Valuation.add_apply (ρ : Valuation W) (x y : W) :
    ρ (x + y) = ρ x + ρ y :=
  ρ.toFun.map_add x y

@[simp]
theorem Valuation.smul_apply (ρ : Valuation W) (a : F) (x : W) :
    ρ (a • x) = a * ρ x :=
  ρ.toFun.map_smul a x

class Context where
    Wℤ : Type
    WBool : Type
    [monoidWZ : AddCommMonoid Wℤ]
    [moduleWZ : ModuleWithOne ℤ Wℤ]
    [monoidWBool : AddCommMonoid WBool]
    [moduleWBool : ModuleWithOne Bool WBool]

attribute [implicit_reducible]
  Context.monoidWZ
  Context.moduleWZ
  Context.monoidWBool
  Context.moduleWBool

attribute [instance]
  Context.monoidWZ
  Context.moduleWZ
  Context.monoidWBool
  Context.moduleWBool

end Freigen.F2Z
