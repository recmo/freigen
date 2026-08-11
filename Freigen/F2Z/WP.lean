import Freigen.F2Z.Defs
import Freigen.F2Z.Semantics
import Freigen.F2Z.Nondet
import Freigen.F2Z.Completeness
import Std.Tactic.Do

namespace Freigen.F2Z.Sound

open Std.Do
open scoped Std.Do

abbrev Shape : PostShape :=
  .arg (Nat → Bool) $ .arg (Nat → ℤ) .pure

abbrev RunnerM : Eff.Scope → Type → Type
| .constraint => Nondet
| .hint       => Semantics.CSBuilder.NoMonad

instance : (e: Eff.Scope) → Monad (RunnerM e)
| .constraint => inferInstance
| .hint       => inferInstance

instance : (e: Eff.Scope) → LawfulMonad (RunnerM e)
| .constraint => inferInstance
| .hint       => inferInstance

def handler (ρB : Nat → Bool) (ρZ : Nat → ℤ) :
    Freigen.Eff.Handler Eff RunnerM :=
  fun {γ} e _ => match γ, e with
    | .constraint, .assertR1C a b c =>
        if a.eval ρZ * b.eval ρZ = c.eval ρZ then pure () else Nondet.abort
    | .constraint, .f2z a =>
        Nondet.chooseWhere fun x : LC ℤ => (a.eval ρB).toInt = x.eval ρZ
    | .constraint, .hint _ _ n => Nondet.choose (Vector (LC Bool) n)
    | .hint, .fail _ => ()

def interp (ρB : Nat → Bool) (ρZ : Nat → ℤ) {α : Type}
    (x : Circuit α) : Nondet α :=
  Free.interp (M := RunnerM) (handler ρB ρZ) x

variable {ρB : Nat → Bool} {ρZ : Nat → ℤ}

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
    ⦃⌜True⌝⦄ interp ρB ρZ (f2z a) ⦃⇓ r => ⌜(a.eval ρB).toInt = r.eval ρZ⌝⦄ := by
  rw [Triple.iff]
  simp only [SPred.entails_nil]
  simp only [SPred.down_pure_nil, wp, interp, F2Z.f2z]
  rw [Free.interp_op]
  simp only [PredTrans.apply, handler, Nondet.chooseWhere, SPred.imp_nil, SPred.down_pure_nil,
    SPred.forall_nil]
  tauto

private theorem satisfies_of_r1cs_prefix {cs : Semantics.CS} {wit : Nat → Bool}
    {pre : Array (Semantics.R1C ℤ)} {r1c : Semantics.R1C ℤ}
    (hprefix : (pre.push r1c).toList <+: cs.r1cs.toList)
    (hsat : cs.satisfies wit) :
    r1c.satisfies (cs.intWitness wit) := by
  have hmemList : r1c ∈ cs.r1cs.toList :=
    hprefix.mem (by simp)
  have hmem : r1c ∈ cs.r1cs := Array.mem_def.mpr hmemList
  change ∀ r ∈ cs.r1cs, r.satisfies (cs.intWitness wit) at hsat
  exact hsat r1c hmem

private theorem intWitness_eq_of_m_prefix {cs : Semantics.CS} {wit : Nat → Bool}
    {pre : Array (LC Bool)} {a : LC Bool}
    (hprefix : (pre.push a).toList <+: cs.m.toList) :
    cs.intWitness wit pre.size = (a.eval wit).toInt := by
  have hi : pre.size < (pre.push a).toList.length := by simp
  have hget := hprefix.getElem hi
  have hsize : pre.size < cs.m.size := by
    simpa using lt_of_lt_of_le hi hprefix.length_le
  have hget' : cs.m[pre.size]'hsize = a := by
    calc
      cs.m[pre.size] = cs.m.toList[pre.size] := rfl
      _ = (pre.push a).toList[pre.size] := hget.symm
      _ = a := by simp
  unfold Semantics.CS.intWitness
  rw [getElem!_pos _ _ (by simpa using hsize), Array.getElem_map, hget']
  rfl

private theorem interp_runAt {a : Circuit α} {s sf : Semantics.CSBuilder}
    {wit : Nat → Bool} {Q : PostCond α .pure}
    (hext : Semantics.CSBuilder.Extends
      (StateT.run (Semantics.CSBuilder.runAt a) s).2 sf)
    (hsat : sf.result.satisfies wit)
    (hwp : ((interp wit (sf.result.intWitness wit) a).apply Q).down) :
    (Q.1 (StateT.run (Semantics.CSBuilder.runAt a) s).1).down := by
  let motive := fun (γ : Eff.Scope) (α : Type) (a : Free Eff γ α) =>
    match γ with
    | .constraint => ∀ (s sf : Semantics.CSBuilder) (wit : Nat → Bool)
        (Q : PostCond α .pure),
        Semantics.CSBuilder.Extends
          (StateT.run (Semantics.CSBuilder.runAt a) s).2 sf →
        sf.result.satisfies wit →
        ((interp wit (sf.result.intWitness wit) a).apply Q).down →
        (Q.1 (StateT.run (Semantics.CSBuilder.runAt a) s).1).down
    | .hint => True
  refine (Free.recOn (motive := motive) a ?_ ?_) s sf wit Q hext hsat hwp
  · intro γ α value
    cases γ with
    | hint => trivial
    | constraint =>
      intro s sf wit Q hext hsat hwp
      change (Q.1 value).down
      change (Q.1 value).down at hwp
      exact hwp
  · intro γ α e blocks k _ ihk
    cases γ with
    | hint => trivial
    | constraint =>
      intro s sf wit Q hext hsat hwp
      cases e with
      | assertR1C a b c =>
          simp [Semantics.CSBuilder.runAt, Semantics.CSBuilder.handler,
            interp, handler] at hext hwp ⊢
          let s₁ : Semantics.CSBuilder := {
            s with result := {
              s.result with r1cs := s.result.r1cs.push { a := a, b := b, c := c }
            }
          }
          have hs₁sf : Semantics.CSBuilder.Extends s₁ sf :=
            (Semantics.CSBuilder.run'_extends (a := k ()) (s := s₁)).trans hext
          have hr1c := satisfies_of_r1cs_prefix hs₁sf.1 hsat
          change a.eval (sf.result.intWitness wit) * b.eval (sf.result.intWitness wit) =
            c.eval (sf.result.intWitness wit) at hr1c
          have hwp' : ((interp wit (sf.result.intWitness wit) (k ())).apply Q).down := by
            simpa [interp, hr1c] using hwp
          exact ihk () s₁ sf wit Q hext hsat hwp'
      | f2z a =>
          simp [Semantics.CSBuilder.runAt, Semantics.CSBuilder.handler,
            interp, handler] at hext hwp ⊢
          let out : LC ℤ := {s.result.m.size}
          let s₁ : Semantics.CSBuilder := {
            s with result := { s.result with m := s.result.m.push a }
          }
          have hs₁sf : Semantics.CSBuilder.Extends s₁ sf :=
            (Semantics.CSBuilder.run'_extends (a := k out) (s := s₁)).trans hext
          have hidx := intWitness_eq_of_m_prefix hs₁sf.2 (wit := wit)
          have hrel : (a.eval wit).toInt = out.eval (sf.result.intWitness wit) := by
            simp [out, hidx]
          change ∀ x : LC ℤ,
            (a.eval wit).toInt = x.eval (sf.result.intWitness wit) →
              ((interp wit (sf.result.intWitness wit) (k x)).apply Q).down at hwp
          exact ihk out s₁ sf wit Q hext hsat (hwp out hrel)
      | hint argTps args n =>
          simp [Semantics.CSBuilder.runAt, Semantics.CSBuilder.handler,
            interp, handler] at hext hwp ⊢
          let out : Vector (LC Bool) n :=
            Vector.ofFn fun i => {s.nextWit + i.val}
          let s₁ : Semantics.CSBuilder := {
            s with nextWit := s.nextWit + n
          }
          change ∀ x : Vector (LC Bool) n, True →
            ((interp wit (sf.result.intWitness wit) (k x)).apply Q).down at hwp
          exact ihk out s₁ sf wit Q hext hsat (hwp out True.intro)

theorem adequate {circ : Circuit α} {wit} {P : α → Prop} :
    ⦃ ⌜True⌝ ⦄ interp wit ((Semantics.CSBuilder.run circ default).2.intWitness wit) circ ⦃ ⇓ v => ⌜P v⌝ ⦄ →
    (Semantics.CSBuilder.run circ default).2.satisfies wit →
    P (Semantics.CSBuilder.run circ default).1 := by
  intro htriple hsat
  simp only [Semantics.CSBuilder.run, Semantics.CSBuilder.run'] at htriple hsat ⊢
  generalize hrun : StateT.run (Semantics.CSBuilder.runAt circ) default = result at htriple hsat ⊢
  rcases result with ⟨value, sf⟩
  simp only at htriple hsat ⊢
  rw [Triple.iff] at htriple
  simp only [SPred.entails_nil, SPred.down_pure_nil, wp] at htriple
  have hwp := htriple True.intro
  have h := interp_runAt
    (a := circ)
    (s := default)
    (sf := sf)
    (wit := wit)
    (Q := (⇓ v => ⌜P v⌝))
    (by simpa [hrun] using Semantics.CSBuilder.Extends.refl sf)
    hsat
    hwp
  simpa [hrun] using h

end Sound
