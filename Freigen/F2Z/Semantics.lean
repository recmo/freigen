import Freigen.F2Z.Defs
import Freigen.Wheels

namespace Freigen.F2Z.Semantics

def WitnessId := Option Nat

instance : Ord WitnessId := inferInstanceAs (Ord (Option Nat))
instance : Repr WitnessId := inferInstanceAs (Repr (Option Nat))
instance : Std.TransCmp (@compare WitnessId _) :=
  inferInstanceAs (Std.TransCmp (@compare (Option Nat) _))
instance : Std.LawfulEqCmp (@compare WitnessId _) :=
  inferInstanceAs (Std.LawfulEqCmp (@compare (Option Nat) _))

structure LC F [Semiring F] where
  coeffs : Std.ExtTreeMap WitnessId F
  ne_zero : ∀ {k: WitnessId}, coeffs[k]? ≠ some 0

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
    cases hak: a[k]? <;> cases hbk: b[k]? <;> grind

instance {F} [Semiring F] : GetElem (LC F) WitnessId F (fun _ _ => True) where
  getElem lc k _ := lc.coeffs[k]?.getD 0

@[ext]
theorem LC.ext : {a b : LC F} → (∀ k, a k = b k) → a = b := by
  intro a b h
  apply DFunLike.coe_injective
  ext
  apply h

def WitnessId.eval (witness : Nat → F): WitnessId → F
| none => 1
| some n => witness n

variable [DecidableEq F]

instance : Singleton WitnessId (LC F) where
  singleton x := {
    coeffs := if (1 : F) = 0 then ∅ else { (x, 1) }
    ne_zero := by
      intro k
      by_cases h: (1 : F) = 0
      · simp_all
      · simp [h]
        change ((default : Std.ExtTreeMap WitnessId F).insert x 1)[k]? ≠ some (0:F)
        rw [Std.ExtTreeMap.getElem?_insert]
        by_cases hp: x = k
        · simp [h, hp]
        · simp [default, hp]
  }

instance : One (LC F) where
  one := { none }

instance : Add (LC F) where
  add a b := {
    coeffs := Std.ExtTreeMap.mergeWith (fun _ => (·+·)) a.coeffs b.coeffs
      |>.filter (fun _ c => c ≠ 0)
    ne_zero := by simp
  }

private theorem LC.add_def {a b : LC F}: a + b = {
    coeffs := Std.ExtTreeMap.mergeWith (fun _ => (·+·)) a.coeffs b.coeffs
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

def LC.map {F G} [Semiring F] [Semiring G] [DecidableEq G] (f : F → G) (lc : LC F) : LC G :=
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

def LC.eval (witness : Nat → F): LC F →ₗ[F] F where
  toFun f :=
    f.coeffs.foldMap (fun i c => c * i.eval witness)
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
      ←Std.ExtTreeMap.foldMap_const_mul]
    · congr 1; ext; simp [mul_assoc]
    · intros; simp_all

structure R1C F [Semiring F] where
  a : LC F
  b : LC F
  c : LC F
deriving Repr

def R1C.satisfies (r1c : R1C F) (witness : Nat → F): Prop :=
  r1c.a.eval witness * r1c.b.eval witness = r1c.c.eval witness

def R1C.satisfies' (r1c : R1C F) (witness : Nat → F): Bool :=
  r1c.a.eval witness * r1c.b.eval witness = r1c.c.eval witness

structure CS where
  r1cs : Array (R1C ℤ)
  m : Array (LC Bool)
deriving Inhabited, Repr

def CS.satisfies' (cs : CS) (witness : Nat → Bool): Bool :=
  let mw := cs.m.map (Bool.toInt ∘ LC.eval witness)
  let mw := fun i => mw[i]!
  cs.r1cs.all (fun r1c => r1c.satisfies' mw)

def CS.satisfies (cs : CS) (witness : Nat → Bool): Prop :=
  let mw := cs.m.map (Bool.toInt ∘ LC.eval witness)
  let mw := fun i => mw[i]!
  ∀ r1c ∈ cs.r1cs, r1c.satisfies mw

structure CSBuilder where
  result : CS
  nextWit : Nat
deriving Inhabited


namespace CSBuilder

scoped instance ctx : Context where
  Wℤ := LC ℤ
  WBool := LC Bool

def fresh : StateM CSBuilder (LC Bool) := do
  modifyGet (fun s => ({ some s.nextWit }, { s with nextWit := s.nextWit + 1 }))

def NoMonad : Type → Type u := fun _ => PUnit

instance : Monad NoMonad where
  pure _ := PUnit.unit
  bind _ _ := PUnit.unit

abbrev RunnerM : Eff.Scope → Type → Type
| .constraint => StateM CSBuilder
| .hint => NoMonad

instance : (γ : Eff.Scope) → Monad (RunnerM γ)
| .constraint => inferInstance
| .hint       => inferInstance

def run' (circ : Vector (LC Bool) n → Circuit Unit): StateM CSBuilder Unit := do
  let initial ← Vector.ofFnM (fun _ => CSBuilder.fresh)
  Free.interp (M := RunnerM) (@fun
    | .constraint, .assertR1C a b c, _ => do
        let cs ← get
        let r1c : R1C ℤ := { a := a, b := b, c := c }
        set { cs with result := { cs.result with r1cs := cs.result.r1cs.push r1c } }
    | .constraint, .f2z a, _ => do
        let cs ← get
        let nextIdx := cs.result.m.size
        let lc : LC ℤ := { some nextIdx }
        set { cs with result := { cs.result with m := cs.result.m.push a } }
        pure lc
    | .constraint, .hint _ _ _, _ => Vector.ofFnM (fun _ => CSBuilder.fresh)
    | .hint, .fail _, _ => ()
  ) (circ initial)

def run (circ : Vector (LC Bool) n → Circuit (ctx := ctx) Unit): CS :=
  (StateT.run (run' circ) default).2.1

end CSBuilder

namespace Witgen

scoped instance ctx : Context where
  Wℤ := ℤ
  WBool := Bool

abbrev RunnerM : Eff.Scope → Type → Type
| .constraint => StateM (Array Bool)
| .hint => Option

instance : (γ : Eff.Scope) → Monad (RunnerM γ)
| .constraint => inferInstance
| .hint       => inferInstance

def run' (circ : Vector Bool n → Circuit Unit) (inp : Vector Bool n): StateM (Array Bool) Unit := do
  set inp.toArray
  Free.interp (M := RunnerM) (@fun
    | .constraint, .assertR1C _ _ _, _ => pure ()
    | .constraint, .f2z a, _ => pure a.toInt
    | .constraint, .hint _ args n, blkO => do
      let r := (blkO () args).getD (Vector.replicate n false)
      modify (fun arr => arr ++ r.toArray)
      pure r
    | .hint, .fail _, _ => none
  ) (circ inp)

def run (circ : Vector Bool n → Circuit Unit) (inp : Vector Bool n): Array Bool :=
  (StateT.run (run' circ inp) default).2

end Witgen

namespace Ex

variable [ctx : Context]
open Context

def fromBits {n : Nat} (r : Vector WBool n):
    Circuit Wℤ :=
  match n with
  | 0 => pure 0
  | _ + 1 => do
    let i ← fromBits r.tail
    let b ← f2z r.head
    pure (b + 2 • i)

def toBits (n : ℕ) (i: Wℤ):
    Circuit (Vector WBool n) := do
  let r ← hint (argTps := [.z]) h![i] fun h![i] =>
    let rawBits := i.toNat.bits.toArray
    let padded := rawBits.take n ++ Array.replicate (n - rawBits.size) false
    let paddedVec : Vector Bool n := ⟨padded, by grind⟩
    paddedVec
  let sum ← fromBits r
  assertR1C sum 1 i
  return r

def smol (inp : Vector WBool 8) : Circuit Unit := do
  let a ← fromBits inp
  let _ ← toBits 4 a

end Ex

open scoped CSBuilder in
def smolCS := CSBuilder.run Ex.smol

open scoped Witgen in
def smolWit := Witgen.run Ex.smol (#v[true, false, true, true, false, false, false, false])

#eval CS.satisfies' smolCS (fun i => smolWit[i]!)

end Freigen.F2Z.Semantics
