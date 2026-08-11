import Freigen.Wheels
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.BooleanRing

namespace Freigen.F2Z

structure LC F [Semiring F] where
  constant : F
  coeffs : Std.ExtTreeMap Nat F
  ne_zero : ∀ {k : Nat}, coeffs[k]? ≠ some 0

instance [Semiring F] [Repr F] : Repr (LC F) where
  reprPrec lc _ := repr (lc.constant, lc.coeffs.toList)

variable {F} [Semiring F]

def LC.coeff (f : LC F) (a : Nat) : F :=
  f.coeffs[a]?.getD 0

instance : CoeFun (LC F) fun _ => Nat → F where
  coe := LC.coeff

instance : Coe F (LC F) where
  coe c := { constant := c, coeffs := ∅, ne_zero := by simp }

instance {F} [Semiring F] : GetElem (LC F) Nat F (fun _ _ => True) where
  getElem lc k _ := lc.coeff k

@[ext]
theorem LC.ext {a b : LC F} (hconstant : a.constant = b.constant)
    (hcoeffs : ∀ k, a k = b k) : a = b := by
  rcases a with ⟨ac, a, ha⟩
  rcases b with ⟨bc, b, hb⟩
  simp only at hconstant hcoeffs
  subst bc
  congr 1
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  have := hcoeffs k
  simp only [LC.coeff] at this
  cases hak : a[k]? <;> cases hbk : b[k]? <;> grind

variable [DecidableEq F]

omit [DecidableEq F] in
def LC.ofConst (c : F) : LC F where
  constant := c
  coeffs := ∅
  ne_zero := by simp

omit [DecidableEq F] in
@[simp]
theorem LC.ofConst_constant (c : F) : (LC.ofConst c).constant = c := by
  rfl

omit [DecidableEq F] in
@[simp]
theorem LC.ofConst_apply (c : F) (k : Nat) :
    (LC.ofConst c).coeff k = 0 := by
  rfl

instance : Singleton Nat (LC F) where
  singleton x := {
    constant := 0
    coeffs := if (1 : F) = 0 then ∅ else { (x, 1) }
    ne_zero := by
      intro k
      by_cases h : (1 : F) = 0
      · simp_all
      · simp [h]
        change ((default : Std.ExtTreeMap Nat F).insert x 1)[k]? ≠ some (0 : F)
        rw [Std.ExtTreeMap.getElem?_insert]
        by_cases hp : x = k
        · simp [h, hp]
        · simp [default, hp]
  }

@[simp]
theorem LC.singleton_constant (k : Nat) :
    ({k} : LC F).constant = 0 := by
  rfl

instance : One (LC F) where
  one := {
    constant := 1
    coeffs := ∅
    ne_zero := by simp
  }

instance : Add (LC F) where
  add a b := {
    constant := a.constant + b.constant
    coeffs := Std.ExtTreeMap.mergeWith (fun _ => (· + ·)) a.coeffs b.coeffs
      |>.filter (fun _ c => c ≠ 0)
    ne_zero := by simp
  }

private theorem LC.add_def {a b : LC F} : a + b = {
    constant := a.constant + b.constant
    coeffs := Std.ExtTreeMap.mergeWith (fun _ => (· + ·)) a.coeffs b.coeffs
      |>.filter (fun _ c => c ≠ 0)
    ne_zero := by simp
  } := by rfl

@[simp]
theorem LC.add_apply {a b : LC F} {k : Nat} :
    (a + b).coeff k = a.coeff k + b.coeff k := by
  change (a + b).coeffs[k]?.getD 0 =
    a.coeffs[k]?.getD 0 + b.coeffs[k]?.getD 0
  simp only [LC.add_def, Std.ExtTreeMap.getElem?_filter']
  simp only [Std.ExtTreeMap.getElem?_mergeWith]
  have := @a.ne_zero k
  have := @b.ne_zero k
  generalize a.coeffs[k]? = a at *
  generalize b.coeffs[k]? = b at *
  cases a <;> cases b <;> grind

@[simp]
theorem LC.add_constant {a b : LC F} :
    (a + b).constant = a.constant + b.constant := by
  rfl

instance : Zero (LC F) where
  zero := {
    constant := 0
    coeffs := Std.ExtTreeMap.empty
    ne_zero := by simp
  }

omit [DecidableEq F] in
@[simp]
theorem LC.zero_apply {k : Nat} :
    (0 : LC F).coeff k = 0 := by rfl

omit [DecidableEq F] in
@[simp]
theorem LC.zero_constant : (0 : LC F).constant = 0 := by
  rfl

omit [DecidableEq F] in
@[simp]
theorem LC.one_constant : (1 : LC F).constant = 1 := by
  rfl

def LC.map {F G} [Semiring F] [Semiring G] [DecidableEq G]
    (f : F → G) (lc : LC F) : LC G :=
  { constant := f lc.constant
    coeffs := lc.coeffs.map (fun _ => f) |>.filter (fun _ c => c ≠ 0)
    ne_zero := by simp }

@[simp]
theorem LC.map_apply {F G} [Semiring F] [Semiring G] [DecidableEq G]
    {f : F → G} {lc : LC F} {k : Nat} (h : f 0 = 0) :
    (LC.map f lc).coeff k = f (lc.coeff k) := by
  change (LC.map f lc).coeffs[k]?.getD 0 = f (lc.coeffs[k]?.getD 0)
  simp only [LC.map, Std.ExtTreeMap.getElem?_filter', Std.ExtTreeMap.getElem?_map]
  generalize lc.coeffs[k]? = c at *
  cases c <;> grind

@[simp]
theorem LC.map_constant {F G} [Semiring F] [Semiring G] [DecidableEq G]
    {f : F → G} {lc : LC F} :
    (LC.map f lc).constant = f lc.constant := by
  rfl

instance : AddCommMonoid (LC F) where
  nsmul n lc := lc.map (fun c => n * c)
  nsmul_succ := by
    intros
    ext <;> simp [Nat.cast_succ, add_mul]
  nsmul_zero := by
    intro
    ext <;> simp
  add_assoc := by intros; ext <;> simp [add_assoc]
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp [add_comm]

instance : Module F (LC F) where
  smul a lc := lc.map (fun c => a * c)
  mul_smul := by intros; ext <;> simp [HSMul.hSMul, mul_assoc]
  one_smul := by intros; ext <;> simp [HSMul.hSMul, one_mul]
  smul_zero := by intros; ext <;> simp [HSMul.hSMul, mul_zero]
  smul_add := by intros; ext <;> simp [HSMul.hSMul, mul_add]
  add_smul := by intros; ext <;> simp [HSMul.hSMul, add_mul]
  zero_smul := by intros; ext <;> simp [HSMul.hSMul, zero_mul]

instance (priority := 100) : NatCast (LC F) where
  natCast n := n • 1

def LC.eval (witness : Nat → F) (f : LC F) : F :=
  f.constant + f.coeffs.foldMap (fun i c => c * witness i)

omit [DecidableEq F] in
@[simp]
theorem LC.eval_zero (witness : Nat → F) :
    (0 : LC F).eval witness = 0 := by
  change 0 + (∅ : Std.ExtTreeMap Nat F).foldMap
    (fun i c => c * witness i) = 0
  rw [zero_add]
  exact Std.ExtTreeMap.foldMap_empty _

@[simp]
theorem LC.eval_add (witness : Nat → F) (x y : LC F) :
    (x + y).eval witness = x.eval witness + y.eval witness := by
  simp only [LC.eval, add_def]
  rw [Std.ExtTreeMap.foldMap_filter, Std.ExtTreeMap.foldMap_mergeWith]
  · ac_rfl
  · intro k
    simp [add_mul]
  · intro k v h
    simp at h
    simp [h]

@[simp]
theorem LC.eval_nsmul (witness : Nat → F) (n : Nat) (x : LC F) :
    (n • x).eval witness = n • x.eval witness := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, ih, add_mul]

@[simp]
theorem LC.eval_smul (witness : Nat → F) (a : F) (x : LC F) :
    (a • x).eval witness = a * x.eval witness := by
  simp only [LC.eval, HSMul.hSMul, SMul.smul, map]
  rw [Std.ExtTreeMap.foldMap_filter, Std.ExtTreeMap.foldMap_map]
  · have hmap :
        (x.coeffs.foldMap fun k v => a * v * witness k) =
          x.coeffs.foldMap fun k v => a * (v * witness k) := by
      congr 1
      funext k v
      simp [mul_assoc]
    rw [hmap, Std.ExtTreeMap.foldMap_const_mul x.coeffs
      (fun k v => v * witness k) a]
    simp [mul_add]
  · intros; simp_all

omit [DecidableEq F] in
@[simp]
theorem LC.eval_one (witness : Nat → F) :
    (1 : LC F).eval witness = 1 := by
  change 1 + (∅ : Std.ExtTreeMap Nat F).foldMap
    (fun i c => c * witness i) = 1
  have h : (∅ : Std.ExtTreeMap Nat F).foldMap
      (fun i c => c * witness i) = 0 :=
    Std.ExtTreeMap.foldMap_empty _
  rw [h, add_zero]

omit [DecidableEq F] in
@[simp]
theorem LC.eval_ofConst (witness : Nat → F) (c : F) :
    (LC.ofConst c).eval witness = c := by
  change c + (∅ : Std.ExtTreeMap Nat F).foldMap
    (fun i x => x * witness i) = c
  have h : (∅ : Std.ExtTreeMap Nat F).foldMap
      (fun i x => x * witness i) = 0 :=
    Std.ExtTreeMap.foldMap_empty _
  rw [h, add_zero]

@[simp]
theorem LC.eval_singleton (witness : Nat → F) (k : Nat) :
    ({k} : LC F).eval witness = witness k := by
  rw [LC.eval, LC.singleton_constant, zero_add]
  by_cases h : (1 : F) = 0
  · have hz (x : F) : x = 0 := by
      calc
        x = x * 1 := (mul_one x).symm
        _ = x * 0 := by rw [h]
        _ = 0 := mul_zero x
    change (if (1 : F) = 0 then
      (∅ : Std.ExtTreeMap Nat F) else {(k, (1 : F))}).foldMap
      (fun i c => c * witness i) = witness k
    rw [if_pos h]
    have hempty : (∅ : Std.ExtTreeMap Nat F).foldMap
        (fun i c => c * witness i) = 0 :=
      Std.ExtTreeMap.foldMap_empty _
    exact hempty.trans (hz (witness k)).symm
  · change (if (1 : F) = 0 then
      (∅ : Std.ExtTreeMap Nat F) else {(k, (1 : F))}).foldMap
      (fun i c => c * witness i) = witness k
    rw [if_neg h, Std.ExtTreeMap.foldMap_singleton]
    simp

@[simp]
theorem LC.eval_sum {I : Type*} (witness : Nat → F)
    (s : Finset I) (f : I → LC F) :
    (∑ i ∈ s, f i).eval witness = ∑ i ∈ s, (f i).eval witness := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

@[simp]
theorem LC.eval_natCast (witness : Nat → F) (n : Nat) :
    (n : LC F).eval witness = n := by
  change (n • (1 : LC F)).eval witness = (n : F)
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, ih]

end Freigen.F2Z
