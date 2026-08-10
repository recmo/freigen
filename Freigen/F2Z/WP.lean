import Freigen.F2Z.Defs
import Freigen.F2Z.Semantics
import Std.Tactic.Do

namespace Freigen.F2Z

open Context
open Std.Do
open scoped Std.Do
open Semantics (LC)

abbrev Nondet := PredTrans .pure

namespace Nondet

instance : WP Nondet .pure where
  wp x := x

instance : WPMonad Nondet .pure where
  wp_pure _ := rfl
  wp_bind _ _ := rfl

def chooseWhere (P : α → Prop) : Nondet α where
  trans Q := spred(∀ a, ⌜P a⌝ → Q.1 a)
  conjunctiveRaw := by
    intro Q₁ Q₂
    apply SPred.bientails.of_eq
    apply ULift.ext
    simp
    aesop

def choose (α : Type u) : Nondet α := chooseWhere (fun _ => True)

end Nondet


-- /-- Concrete meanings for the two kinds of symbolic wires. -/
-- structure Assignment (ctx : Context) where
--   z : Valuation ctx.Wℤ
--   bool : Valuation ctx.WBool

abbrev Shape : PostShape :=
  .arg (Valuation (LC Bool)) $ .arg (Valuation (LC ℤ)) .pure

/-- A computation with no successful outcomes. Every partial-correctness postcondition holds. -/
def Nondet.abort : Nondet α :=
  PredTrans.const ⌜True⌝

-- /-- Canonical witness that a Boolean-valued integer wire always exists. -/
-- def boolWire (ctx : Context) (b : Bool) : ctx.Wℤ :=
--   if b then 1 else 0

-- @[simp]
-- theorem Assignment.z_boolWire (ρ : Assignment ctx) (b : Bool) :
--     ρ.z (boolWire ctx b) = b.toInt := by
--   cases b <;> simp [boolWire]

-- theorem Assignment.exists_f2zWire (ρ : Assignment ctx) (a : ctx.WBool) :
--     ∃ x : ctx.Wℤ, (ρ.bool a).toInt = ρ.z x :=
--   ⟨boolWire ctx (ρ.bool a), (ρ.z_boolWire _).symm⟩

local instance ctx : Context where
  Wℤ := LC ℤ
  WBool := LC Bool

abbrev RunnerM : Eff.Scope → Type → Type
| .constraint => Nondet
| .hint       => Semantics.CSBuilder.NoMonad

instance : (e: Eff.Scope) → Monad (RunnerM e)
| .constraint => inferInstance
| .hint       => inferInstance

instance : (e: Eff.Scope) → LawfulMonad (RunnerM e)
| .constraint => inferInstance
| .hint       => inferInstance

def handler (ρB : Valuation (LC Bool)) (ρZ : Valuation (LC ℤ)) :
    Freigen.Eff.Handler (Eff ctx) RunnerM :=
  fun {γ} e _ => match γ, e with
    | .constraint, .assertR1C a b c =>
        if ρZ a * ρZ b = ρZ c then pure () else Nondet.abort
    | .constraint, .f2z a =>
        Nondet.chooseWhere fun x : ctx.Wℤ => (ρB a).toInt = ρZ x
    | .constraint, .hint _ _ n => Nondet.choose (Vector ctx.WBool n)
    | .hint, .fail _ => ()

def interp (ρB : Valuation (LC Bool)) (ρZ : Valuation (LC ℤ)) {α : Type}
    (x : Circuit α) : Nondet α :=
  Free.interp (M := RunnerM) (handler ρB ρZ) x

instance : WP Circuit Shape where
  wp x := PredTrans.pushArg fun ρB => PredTrans.pushArg fun ρZ =>
    (fun a => ((a, ρB), ρZ)) <$> interp ρB ρZ x

instance : WPMonad Circuit Shape where
  wp_pure a := by
    ext Q
    simp [WP.wp, interp]
  wp_bind x f := by
    ext Q
    simp [WP.wp, interp]

abbrev SoundnessTriple {α} (x : Circuit α) (P : Assertion Shape) (Q : PostCond α Shape) :=
  Triple x P Q

-- /-! ## WP for source programs -/

-- /-- The WP of a source program is the WP of its direct interpretation. -/
-- instance (ctx : Context) (γ : Eff.Scope) : WP (Free (Eff ctx) γ) (Shape ctx) where
--   wp x := PredTrans.pushArg fun ρ => (fun a => (a, ρ)) <$> interp ctx ρ x

-- /-- Interpretation respects `pure` and `bind`, so source-program WPs compose through `do`. -/
-- instance (ctx : Context) (γ : Eff.Scope) : WPMonad (Free (Eff ctx) γ) (Shape ctx) where
--   wp_pure a := by
--     ext Q
--     simp [WP.wp, interp]
--   wp_bind x f := by
--     ext Q
--     simp [WP.wp, interp]

-- /-! ## Exact primitive specifications -/

-- namespace Spec

-- variable [ctx : Context]

-- private theorem interp_assertR1C (ρ : Assignment ctx) (a b c : Wℤ) :
--     interp ctx ρ (Freigen.F2Z.assertR1C a b c) =
--       (if ρ.z a * ρ.z b = ρ.z c then pure () else Nondet.abort) := by
--   rw [Freigen.F2Z.assertR1C, interp, Free.interp_op]
--   rfl

-- /-- A failed constraint has no successful outcomes. -/
-- @[spec] theorem assertR1C (a b c : Wℤ) (Q : PostCond Unit (Shape ctx)) :
    -- Triple (Freigen.F2Z.assertR1C a b c)
      -- (spred(fun ρ =>
        -- if ρ.z a * ρ.z b = ρ.z c then Q.1 () ρ else ⌜True⌝))
      -- Q := by
--   rw [Triple.iff]
--   intro ρ
--   simp only [SPred.entails_nil]
--   change _ → ((interp ctx ρ (Freigen.F2Z.assertR1C a b c)).apply
--     (fun x => Q.1 x ρ, Q.2)).down
--   rw [show interp ctx ρ (Freigen.F2Z.assertR1C a b c) =
--     (if ρ.z a * ρ.z b = ρ.z c then pure () else Nondet.abort) from
--     interp_assertR1C ρ a b c]
--   split
--   · change (Q.1 () ρ).down → (Q.1 () ρ).down
--     exact id
--   · change True → True
--     exact id

-- private theorem interp_f2z (ρ : Assignment ctx) (a : WBool) :
--     interp ctx ρ (Freigen.F2Z.f2z a) =
--       Nondet.chooseWhere (fun x : Wℤ => (ρ.bool a).toInt = ρ.z x) := by
--   rw [Freigen.F2Z.f2z, interp, Free.interp_op]
--   rfl

-- /--
-- The direct semantics forgets the fresh wire's identity and permits any wire with the allocated
-- value.  There is no failure branch: `boolWire` witnesses that such a wire always exists.
-- -/
-- @[spec] theorem f2z (a : WBool) (Q : PostCond Wℤ (Shape ctx)) :
--     Triple (Freigen.F2Z.f2z a)
--       (spred(fun ρ => ∀ x, ⌜(ρ.bool a).toInt = ρ.z x⌝ → Q.1 x ρ))
--       Q := by
--   rw [Triple.iff]
--   intro ρ
--   simp only [SPred.entails_nil]
--   change _ → ((interp ctx ρ (Freigen.F2Z.f2z a)).apply
--     (fun x => Q.1 x ρ, Q.2)).down
--   rw [show interp ctx ρ (Freigen.F2Z.f2z a) =
--     Nondet.chooseWhere (fun x : Wℤ => (ρ.bool a).toInt = ρ.z x) from interp_f2z ρ a]
--   simp [PredTrans.apply, Nondet.chooseWhere]

-- private theorem interp_hint (ρ : Assignment ctx) {n : Nat} {argTps : List Eff.WitnessSide}
--     (args : HList (Eff.WitnessSize.denoteW ctx.Wℤ ctx.WBool) argTps)
--     (body : HList Eff.WitnessSize.denoteF argTps → Vector Bool n) :
--     interp ctx ρ (Freigen.F2Z.hint args body) =
--       Nondet.choose (Vector WBool n) := by
--   rw [Freigen.F2Z.hint, interp, Free.interp_op]
--   rfl

-- /--
-- The executable hint body does not enter the soundness rule: every symbolic Boolean vector is a
-- possible result.  Subsequent constraints must establish all facts used about it.
-- -/
-- @[spec] theorem hint {n : Nat} {argTps : List Eff.WitnessSide}
--     (args : HList (Eff.WitnessSize.denoteW ctx.Wℤ ctx.WBool) argTps)
--     (body : HList Eff.WitnessSize.denoteF argTps → Vector Bool n)
--     (Q : PostCond (Vector WBool n) (Shape ctx)) :
--     Triple (Freigen.F2Z.hint args body)
--       (spred(fun ρ => ∀ r, Q.1 r ρ)) Q := by
--   rw [Triple.iff]
--   intro ρ
--   simp only [SPred.entails_nil]
--   change _ → ((interp ctx ρ (Freigen.F2Z.hint args body)).apply
--     (fun x => Q.1 x ρ, Q.2)).down
--   rw [show interp ctx ρ (Freigen.F2Z.hint args body) = Nondet.choose (Vector WBool n) from
--     interp_hint ρ args body]
--   simp [PredTrans.apply, Nondet.choose]

-- end Spec

-- end Direct

end Freigen.F2Z
