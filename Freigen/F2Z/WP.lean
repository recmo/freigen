import Freigen.F2Z.Defs
import Freigen.F2Z.Semantics
import Std.Tactic.Do

namespace Freigen.F2Z.Sound

open Context
open Std.Do
open scoped Std.Do
open Semantics (LC)

def Nondet := PredTrans .pure

namespace Nondet

instance : Monad Nondet := inferInstanceAs (Monad $ PredTrans .pure)
instance : LawfulMonad Nondet := inferInstanceAs (LawfulMonad $ PredTrans .pure)

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

abbrev Shape : PostShape :=
  .arg (Valuation (LC Bool)) $ .arg (Valuation (LC ℤ)) .pure

def Nondet.abort : Nondet α :=
  PredTrans.const ⌜True⌝

scoped instance ctx : Context where
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

-- instance : WP Circuit Shape where
--   wp x := PredTrans.pushArg fun ρB => PredTrans.pushArg fun ρZ =>
--     (fun a => ((a, ρB), ρZ)) <$> interp ρB ρZ x

-- instance : WPMonad Circuit Shape where
--   wp_pure a := by
--     ext Q
--     simp [WP.wp, interp]
--   wp_bind x f := by
--     ext Q
--     simp [WP.wp, interp]

variable {ρB : Valuation (LC Bool)} {ρZ : Valuation (LC ℤ)}

@[simp, spec]
theorem interp_bind {x : Circuit α} {f : α → Circuit β} : interp ρB ρZ (do let a ← x; f a) = (do let a ← interp ρB ρZ x; interp ρB ρZ (f a)) := by
  simp [interp, Free.interp_bind]

@[simp, spec]
theorem interp_pure (a : α) :
    interp ρB ρZ (pure a : Circuit α) = pure a := by
  rfl

@[simp, spec]
theorem interp_map (g : α → β) (x : Circuit α) :
    interp ρB ρZ (g <$> x) = g <$> interp ρB ρZ x := by
  rw [← bind_pure_comp, interp_bind]
  simp only [interp_pure, bind_pure_comp]

private theorem interp_list_mapM (xs : List α) (f : α → Circuit β) :
    interp ρB ρZ (xs.mapM f) =
      xs.mapM (fun x => interp ρB ρZ (f x)) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, interp_bind]

private theorem interp_array_mapM (xs : Array α) (f : α → Circuit β) :
    interp ρB ρZ (xs.mapM f) =
      xs.mapM (fun x => interp ρB ρZ (f x)) := by
  simp only [Array.mapM_eq_mapM_toList, interp_map, interp_list_mapM]

@[simp, spec]
theorem interp_mapM (xs : Vector α n) (f : α → Circuit β) :
    interp ρB ρZ (xs.mapM f) =
      xs.mapM (fun x => interp ρB ρZ (f x)) := by
  apply Vector.map_toArray_inj.mp
  rw [← interp_map, Vector.toArray_mapM, interp_array_mapM, Vector.toArray_mapM]

@[spec]
theorem f2z {a ρB ρZ}:
    ⦃⌜True⌝⦄ interp ρB ρZ (f2z a) ⦃⇓ r => ⌜(ρB a).toInt = ρZ r⌝⦄ := by
  rw [Triple.iff]
  simp only [SPred.entails_nil]
  simp only [SPred.down_pure_nil, wp, interp, F2Z.f2z]
  rw [Free.interp_op]
  simp only [PredTrans.apply, handler, Nondet.chooseWhere, SPred.imp_nil, SPred.down_pure_nil,
    SPred.forall_nil]
  tauto

theorem adequate {circ : [Context] → Circuit (ctx := ctx) α} {wit} { P : α → Prop} :
    ⦃ ⌜True⌝ ⦄ interp (LC.eval wit) ((Semantics.CSBuilder.run circ default).2.intValuation wit) circ ⦃ ⇓ v => ⌜P v⌝ ⦄ →
    (Semantics.CSBuilder.run circ default).2.satisfies wit →
    P (Semantics.CSBuilder.run circ default).1 := by sorry

end Sound

namespace Complete

-- scoped instance Context : Context where
--   Wℤ := ℤ
--   WBool := Bool

end Freigen.F2Z.Complete
