import Freigen.Wheels
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.BooleanRing

namespace Freigen.F2Z

section

variable {F W} [Semiring F] [AddCommMonoid W]

class ModuleWithOne (F : outParam Type) W [Semiring F] [AddCommMonoid W]
    extends Module F W, One W

instance : ModuleWithOne ℤ ℤ where
instance : ModuleWithOne Bool Bool where

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

end

def WitnessId := Option Nat

instance : Ord WitnessId := inferInstanceAs (Ord (Option Nat))
instance : Repr WitnessId := inferInstanceAs (Repr (Option Nat))
instance : Std.TransCmp (@compare WitnessId _) :=
  inferInstanceAs (Std.TransCmp (@compare (Option Nat) _))
instance : Std.LawfulEqCmp (@compare WitnessId _) :=
  inferInstanceAs (Std.LawfulEqCmp (@compare (Option Nat) _))

structure LC F [Semiring F] where
  coeffs : Std.ExtTreeMap WitnessId F
  ne_zero : ∀ {k : WitnessId}, coeffs[k]? ≠ some 0

instance [Semiring F] [Repr F] : Repr (LC F) where
  reprPrec lc _ := repr lc.coeffs.toList

variable {F} [Semiring F]

instance : FunLike (LC F) WitnessId F where
  coe f a := f.coeffs[a]?.getD 0
  coe_injective a b h := by
    simp only at h
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    congr 1
    simp only at h
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    have := congrFun h k
    cases hak : a[k]? <;> cases hbk : b[k]? <;> grind

instance {F} [Semiring F] : GetElem (LC F) WitnessId F (fun _ _ => True) where
  getElem lc k _ := lc.coeffs[k]?.getD 0

@[ext]
theorem LC.ext : {a b : LC F} → (∀ k, a k = b k) → a = b := by
  intro a b h
  apply DFunLike.coe_injective
  ext
  apply h

def WitnessId.eval (witness : Nat → F) : WitnessId → F
  | none => 1
  | some n => witness n

variable [DecidableEq F]

instance : Singleton WitnessId (LC F) where
  singleton x := {
    coeffs := if (1 : F) = 0 then ∅ else { (x, 1) }
    ne_zero := by
      intro k
      by_cases h : (1 : F) = 0
      · simp_all
      · simp [h]
        change ((default : Std.ExtTreeMap WitnessId F).insert x 1)[k]? ≠ some (0 : F)
        rw [Std.ExtTreeMap.getElem?_insert]
        by_cases hp : x = k
        · simp [h, hp]
        · simp [default, hp]
  }

instance : One (LC F) where
  one := { none }

instance : Add (LC F) where
  add a b := {
    coeffs := Std.ExtTreeMap.mergeWith (fun _ => (· + ·)) a.coeffs b.coeffs
      |>.filter (fun _ c => c ≠ 0)
    ne_zero := by simp
  }

private theorem LC.add_def {a b : LC F} : a + b = {
    coeffs := Std.ExtTreeMap.mergeWith (fun _ => (· + ·)) a.coeffs b.coeffs
      |>.filter (fun _ c => c ≠ 0)
    ne_zero := by simp
  } := by rfl

@[simp]
theorem LC.add_apply {a b : LC F} {k : WitnessId} :
    (a + b) k = a k + b k := by
  simp only [LC.add_def, DFunLike.coe, Std.ExtTreeMap.getElem?_filter']
  simp only [Std.ExtTreeMap.getElem?_mergeWith]
  have := @a.ne_zero k
  have := @b.ne_zero k
  generalize a.coeffs[k]? = a at *
  generalize b.coeffs[k]? = b at *
  cases a <;> cases b <;> grind

instance : Zero (LC F) where
  zero := {
    coeffs := Std.ExtTreeMap.empty
    ne_zero := by simp
  }

omit [DecidableEq F] in
@[simp]
theorem LC.zero_apply {k : WitnessId} :
    (0 : LC F) k = 0 := by rfl

def LC.map {F G} [Semiring F] [Semiring G] [DecidableEq G]
    (f : F → G) (lc : LC F) : LC G :=
  { coeffs := lc.coeffs.map (fun _ => f) |>.filter (fun _ c => c ≠ 0)
    ne_zero := by simp }

@[simp]
theorem LC.map_apply {F G} [Semiring F] [Semiring G] [DecidableEq G]
    {f : F → G} {lc : LC F} {k : WitnessId} (h : f 0 = 0) :
    (LC.map f lc) k = f (lc k) := by
  simp only [LC.map, DFunLike.coe, Std.ExtTreeMap.getElem?_filter', Std.ExtTreeMap.getElem?_map]
  generalize lc.coeffs[k]? = c at *
  cases c <;> grind

instance : AddCommMonoid (LC F) where
  nsmul n lc := lc.map (fun c => n * c)
  nsmul_succ := by
    intro _ x
    ext k
    rw [LC.map_apply, LC.add_apply, LC.map_apply]
    all_goals grind
  nsmul_zero := by
    intro
    ext k
    rw [LC.map_apply] <;> simp
  add_assoc := by intros; ext; simp [add_assoc]
  zero_add := by intros; ext; simp
  add_zero := by intros; ext; simp
  add_comm := by intros; ext; simp [add_comm]

instance : Module F (LC F) where
  smul a lc := lc.map (fun c => a * c)
  mul_smul := by intros; ext; simp [HSMul.hSMul, mul_assoc]
  one_smul := by intros; ext; simp [HSMul.hSMul, one_mul]
  smul_zero := by intros; ext; simp [HSMul.hSMul, mul_zero]
  smul_add := by intros; ext; simp [HSMul.hSMul, mul_add]
  add_smul := by intros; ext; simp [HSMul.hSMul, add_mul]
  zero_smul := by intros; ext; simp [HSMul.hSMul, zero_mul]

instance : ModuleWithOne F (LC F) where

def LC.eval (witness : Nat → F) : Valuation (LC F) where
  toFun := {
    toFun f := f.coeffs.foldMap (fun i c => c * i.eval witness)
    map_add' := by
      intro x y
      simp only [add_def]
      rw [Std.ExtTreeMap.foldMap_filter, Std.ExtTreeMap.foldMap_mergeWith]
      · intro k
        cases k <;> simp [WitnessId.eval, add_mul]
      · intro k v h
        simp at h
        simp [h]
    map_smul' := by
      intro a x
      simp only [HSMul.hSMul, SMul.smul, map]
      rw [Std.ExtTreeMap.foldMap_filter, Std.ExtTreeMap.foldMap_map,
        ← Std.ExtTreeMap.foldMap_const_mul]
      · congr 1; ext; simp [mul_assoc]
      · intros; simp_all
  }
  one_map := by
    simp [OfNat.ofNat, One.one, Singleton.singleton]
    split
    · apply Eq.symm
      assumption
    · change (0 + (1 * 1) = (1 : F))
      simp

end Freigen.F2Z
