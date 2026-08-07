import Freigen.F2Z.Defs
import Std.Tactic.Do

namespace Freigen.F2Z

open Context
open Std.Do
open scoped Std.Do

/-!
`Direct` is a deliberately small relational semantics for circuit programs.  It is not an R1CS
builder: valuations interpret wires directly, failed constraints have no successful outcomes, and
allocation effects choose wires nondeterministically.  This makes it useful as the first WP model
while the real constraint-system interpreter is still under construction.
-/
namespace Direct

/-! ## Demonic nondeterminism -/

/-- A nondeterministic computation represented by its healthy weakest-precondition transformer. -/
abbrev Nondet := PredTrans .pure

namespace Nondet

instance : WP Nondet .pure where
  wp x := x

instance : WPMonad Nondet .pure where
  wp_pure _ := rfl
  wp_bind _ _ := rfl

/-- Choose an arbitrary value.  Its WP requires the continuation for every possible choice. -/
def choose (α : Type u) : Nondet α where
  trans Q := spred(∀ a, Q.1 a)
  conjunctiveRaw := by
    intro Q₁ Q₂
    apply SPred.bientails.of_eq
    apply ULift.ext
    simp
    aesop

/-- Choose any value satisfying `P`; choices not satisfying `P` are not outcomes. -/
def chooseWhere (P : α → Prop) : Nondet α where
  trans Q := spred(∀ a, ⌜P a⌝ → Q.1 a)
  conjunctiveRaw := by
    intro Q₁ Q₂
    apply SPred.bientails.of_eq
    apply ULift.ext
    simp
    aesop

end Nondet

/-! ## Direct interpretation -/

/-- Concrete meanings for the two kinds of symbolic wires. -/
structure Assignment (ctx : Context) where
  z : Valuation ctx.Wℤ
  bool : Valuation ctx.WBool

/-- The assignment is a read-only parameter of source-level assertions and postconditions. -/
abbrev Shape (ctx : Context) : PostShape :=
  .arg (Assignment ctx) .pure

/-- A computation with no successful outcomes.  Every partial-correctness postcondition holds. -/
def Nondet.abort : Nondet α :=
  PredTrans.const ⌜True⌝

/-- Canonical witness that a Boolean-valued integer wire always exists. -/
def boolWire (ctx : Context) (b : Bool) : ctx.Wℤ :=
  if b then 1 else 0

@[simp]
theorem Assignment.z_boolWire (ρ : Assignment ctx) (b : Bool) :
    ρ.z (boolWire ctx b) = b.toInt := by
  cases b <;> simp [boolWire]

theorem Assignment.exists_f2zWire (ρ : Assignment ctx) (a : ctx.WBool) :
    ∃ x : ctx.Wℤ, (ρ.bool a).toInt = ρ.z x :=
  ⟨boolWire ctx (ρ.bool a), (ρ.z_boolWire _).symm⟩

/-- The direct handler at a fixed assignment, with no state or exception transformer stack. -/
def handler (ctx : Context) (ρ : Assignment ctx) :
    Freigen.Eff.Handler (Eff ctx) (fun _ : Eff.Scope.{0} => Nondet) :=
  fun {γ} e _ => match γ, e with
    | .constraint, .assertR1C a b c =>
        if ρ.z a * ρ.z b = ρ.z c then pure () else Nondet.abort
    | .constraint, .f2z a =>
        Nondet.chooseWhere fun x : ctx.Wℤ => (ρ.bool a).toInt = ρ.z x
    | .constraint, .hint _ _ n => Nondet.choose (Vector ctx.WBool n)
    | .hint, e => e.elim

def interp (ctx : Context) (ρ : Assignment ctx) {γ : Eff.Scope} {α : Type}
    (x : Free (Eff ctx) γ α) : Nondet α :=
  Free.interp (M := fun _ : Eff.Scope.{0} => Nondet) (handler ctx ρ) x

/-! ## WP for source programs -/

/-- The WP of a source program is the WP of its direct interpretation. -/
instance (ctx : Context) (γ : Eff.Scope) : WP (Free (Eff ctx) γ) (Shape ctx) where
  wp x := PredTrans.pushArg fun ρ => (fun a => (a, ρ)) <$> interp ctx ρ x

/-- Interpretation respects `pure` and `bind`, so source-program WPs compose through `do`. -/
instance (ctx : Context) (γ : Eff.Scope) : WPMonad (Free (Eff ctx) γ) (Shape ctx) where
  wp_pure a := by
    ext Q
    simp [WP.wp, interp]
  wp_bind x f := by
    ext Q
    simp [WP.wp, interp]

/-! ## Exact primitive specifications -/

namespace Spec

variable [ctx : Context]

private theorem interp_assertR1C (ρ : Assignment ctx) (a b c : Wℤ) :
    interp ctx ρ (Freigen.F2Z.assertR1C a b c) =
      (if ρ.z a * ρ.z b = ρ.z c then pure () else Nondet.abort) := by
  rw [Freigen.F2Z.assertR1C, interp, Free.interp_op]
  rfl

/-- A failed constraint has no successful outcomes. -/
@[spec] theorem assertR1C (a b c : Wℤ) (Q : PostCond Unit (Shape ctx)) :
    Triple (Freigen.F2Z.assertR1C a b c)
      (spred(fun ρ =>
        if ρ.z a * ρ.z b = ρ.z c then Q.1 () ρ else ⌜True⌝))
      Q := by
  rw [Triple.iff]
  intro ρ
  simp only [SPred.entails_nil]
  change _ → ((interp ctx ρ (Freigen.F2Z.assertR1C a b c)).apply
    (fun x => Q.1 x ρ, Q.2)).down
  rw [show interp ctx ρ (Freigen.F2Z.assertR1C a b c) =
    (if ρ.z a * ρ.z b = ρ.z c then pure () else Nondet.abort) from
    interp_assertR1C ρ a b c]
  split
  · change (Q.1 () ρ).down → (Q.1 () ρ).down
    exact id
  · change True → True
    exact id

private theorem interp_f2z (ρ : Assignment ctx) (a : WBool) :
    interp ctx ρ (Freigen.F2Z.f2z a) =
      Nondet.chooseWhere (fun x : Wℤ => (ρ.bool a).toInt = ρ.z x) := by
  rw [Freigen.F2Z.f2z, interp, Free.interp_op]
  rfl

/--
The direct semantics forgets the fresh wire's identity and permits any wire with the allocated
value.  There is no failure branch: `boolWire` witnesses that such a wire always exists.
-/
@[spec] theorem f2z (a : WBool) (Q : PostCond Wℤ (Shape ctx)) :
    Triple (Freigen.F2Z.f2z a)
      (spred(fun ρ => ∀ x, ⌜(ρ.bool a).toInt = ρ.z x⌝ → Q.1 x ρ))
      Q := by
  rw [Triple.iff]
  intro ρ
  simp only [SPred.entails_nil]
  change _ → ((interp ctx ρ (Freigen.F2Z.f2z a)).apply
    (fun x => Q.1 x ρ, Q.2)).down
  rw [show interp ctx ρ (Freigen.F2Z.f2z a) =
    Nondet.chooseWhere (fun x : Wℤ => (ρ.bool a).toInt = ρ.z x) from interp_f2z ρ a]
  simp [PredTrans.apply, Nondet.chooseWhere]

private theorem interp_hint (ρ : Assignment ctx) {n : Nat} {argTps : List Eff.WitnessSide}
    (args : HList (Eff.WitnessSize.denoteW ctx.Wℤ ctx.WBool) argTps)
    (body : HList Eff.WitnessSize.denoteF argTps → Vector Bool n) :
    interp ctx ρ (Freigen.F2Z.hint args body) =
      Nondet.choose (Vector WBool n) := by
  rw [Freigen.F2Z.hint, interp, Free.interp_op]
  rfl

/--
The executable hint body does not enter the soundness rule: every symbolic Boolean vector is a
possible result.  Subsequent constraints must establish all facts used about it.
-/
@[spec] theorem hint {n : Nat} {argTps : List Eff.WitnessSide}
    (args : HList (Eff.WitnessSize.denoteW ctx.Wℤ ctx.WBool) argTps)
    (body : HList Eff.WitnessSize.denoteF argTps → Vector Bool n)
    (Q : PostCond (Vector WBool n) (Shape ctx)) :
    Triple (Freigen.F2Z.hint args body)
      (spred(fun ρ => ∀ r, Q.1 r ρ)) Q := by
  rw [Triple.iff]
  intro ρ
  simp only [SPred.entails_nil]
  change _ → ((interp ctx ρ (Freigen.F2Z.hint args body)).apply
    (fun x => Q.1 x ρ, Q.2)).down
  rw [show interp ctx ρ (Freigen.F2Z.hint args body) = Nondet.choose (Vector WBool n) from
    interp_hint ρ args body]
  simp [PredTrans.apply, Nondet.choose]

end Spec

end Direct

end Freigen.F2Z
