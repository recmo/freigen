import Freigen.F2Z.Defs
import Freigen.F2Z.Semantics
import Std.Tactic.Do

namespace Freigen.F2Z.Sound

open Std.Do
open scoped Std.Do

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
  .arg (Nat → Bool) $ .arg (Nat → ℤ) .pure

def Nondet.abort : Nondet α :=
  PredTrans.const ⌜True⌝

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

namespace Complete

open Std.Do
open scoped Std.Do

private structure Related (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) : Prop where
  nextWit_eq : cs.nextWit = ws.bools.size
  m_bounded : ∀ a ∈ cs.result.m, a.Bounded ws.bools.size
  m_eval : cs.result.m.map (Bool.toInt ∘ LC.eval ws.boolWitness) = ws.ints
  r1cs_bounded : ∀ r ∈ cs.result.r1cs,
    r.a.Bounded ws.ints.size ∧ r.b.Bounded ws.ints.size ∧
      r.c.Bounded ws.ints.size
  r1cs_satisfy : ∀ r ∈ cs.result.r1cs, r.satisfies ws.intWitness

private theorem Related.initial : Related default default := by
  refine {
    nextWit_eq := rfl
    m_bounded := by
      intro a ha
      change a ∈ (#[] : Array (LC Bool)) at ha
      simp at ha
    m_eval := by
      native_decide
    r1cs_bounded := by
      intro r hr
      change r ∈ (#[] : Array (Semantics.R1C ℤ)) at hr
      simp at hr
    r1cs_satisfy := by
      intro r hr
      change r ∈ (#[] : Array (Semantics.R1C ℤ)) at hr
      simp at hr
  }

private theorem Related.intWitness_eq {cs : Semantics.CSBuilder}
    {ws : Semantics.Witgen.State} (h : Related cs ws) :
    cs.result.intWitness ws.boolWitness = ws.intWitness := by
  unfold Semantics.CS.intWitness
  rw [h.m_eval]
  rfl

private theorem Related.satisfies {cs : Semantics.CSBuilder}
    {ws : Semantics.Witgen.State} (h : Related cs ws) :
    cs.result.satisfies ws.boolWitness := by
  change ∀ r ∈ cs.result.r1cs,
    r.satisfies (cs.result.intWitness ws.boolWitness)
  intro r hr
  rw [h.intWitness_eq]
  exact h.r1cs_satisfy r hr

private theorem boolWitness_append (ws : Semantics.Witgen.State)
    (r : Array Bool) {i : Nat} (hi : i < ws.bools.size) :
    ws.boolWitness i = ({ ws with bools := ws.bools ++ r }).boolWitness i := by
  unfold Semantics.Witgen.State.boolWitness
  change ws.bools[i]! = (ws.bools ++ r)[i]!
  rw [getElem!_pos ws.bools i hi,
    getElem!_pos (ws.bools ++ r) i (by simp; omega)]
  exact (Array.getElem_append_left hi).symm

private theorem intWitness_push (ws : Semantics.Witgen.State)
    (v : ℤ) {i : Nat} (hi : i < ws.ints.size) :
    ws.intWitness i = ({ ws with ints := ws.ints.push v }).intWitness i := by
  unfold Semantics.Witgen.State.intWitness
  change ws.ints[i]! = (ws.ints.push v)[i]!
  rw [getElem!_pos ws.ints i hi,
    getElem!_pos (ws.ints.push v) i (by simp; omega)]
  exact (Array.getElem_push_lt hi).symm

private theorem Related.assertR1C {cs : Semantics.CSBuilder}
    {ws : Semantics.Witgen.State} (h : Related cs ws)
    {a b c : LC ℤ}
    (hbounded : a.Bounded ws.ints.size ∧ b.Bounded ws.ints.size ∧
      c.Bounded ws.ints.size)
    (hsat : a.eval ws.intWitness * b.eval ws.intWitness = c.eval ws.intWitness) :
    Related
      { cs with result := {
          cs.result with r1cs := cs.result.r1cs.push { a := a, b := b, c := c }
        } }
      ws := by
  refine {
    nextWit_eq := h.nextWit_eq
    m_bounded := h.m_bounded
    m_eval := h.m_eval
    r1cs_bounded := ?_
    r1cs_satisfy := ?_
  }
  · intro r hr
    rw [Array.mem_push] at hr
    rcases hr with hr | rfl
    · exact h.r1cs_bounded r hr
    · exact hbounded
  · intro r hr
    rw [Array.mem_push] at hr
    rcases hr with hr | rfl
    · exact h.r1cs_satisfy r hr
    · exact hsat

private theorem Related.f2z {cs : Semantics.CSBuilder}
    {ws : Semantics.Witgen.State} (h : Related cs ws) (a : LC Bool)
    (hbounded : a.Bounded ws.bools.size) :
    Related
      { cs with result := { cs.result with m := cs.result.m.push a } }
      { ws with ints := ws.ints.push (a.eval ws.boolWitness).toInt } := by
  let v := (a.eval ws.boolWitness).toInt
  let ws' : Semantics.Witgen.State := { ws with ints := ws.ints.push v }
  refine {
    nextWit_eq := h.nextWit_eq
    m_bounded := ?_
    m_eval := ?_
    r1cs_bounded := ?_
    r1cs_satisfy := ?_
  }
  · intro x hx
    rw [Array.mem_push] at hx
    rcases hx with hx | rfl
    · exact h.m_bounded x hx
    · exact hbounded
  · change (cs.result.m.push a).map
      (Bool.toInt ∘ LC.eval ws'.boolWitness) = ws'.ints
    rw [show ws'.boolWitness = ws.boolWitness from rfl]
    simpa only [v, ws', Array.map_push, Function.comp_apply] using
      congrArg (fun xs => xs.push v) h.m_eval
  · intro r hr
    obtain ⟨ha, hb, hc⟩ := h.r1cs_bounded r hr
    simpa [ws', v] using ⟨ha.mono (by simp), hb.mono (by simp), hc.mono (by simp)⟩
  · intro r hr
    obtain ⟨ha, hb, hc⟩ := h.r1cs_bounded r hr
    have hea := LC.eval_eq_of_bounded ha (fun i hi => intWitness_push ws v hi)
    have heb := LC.eval_eq_of_bounded hb (fun i hi => intWitness_push ws v hi)
    have hec := LC.eval_eq_of_bounded hc (fun i hi => intWitness_push ws v hi)
    simpa [Semantics.R1C.satisfies, ws', v, hea, heb, hec] using
      h.r1cs_satisfy r hr

private theorem Related.hint {cs : Semantics.CSBuilder}
    {ws : Semantics.Witgen.State} (h : Related cs ws) (r : Array Bool) :
    Related { cs with nextWit := cs.nextWit + r.size }
      { ws with bools := ws.bools ++ r } := by
  let ws' : Semantics.Witgen.State := { ws with bools := ws.bools ++ r }
  refine {
    nextWit_eq := by simp [h.nextWit_eq]
    m_bounded := ?_
    m_eval := ?_
    r1cs_bounded := h.r1cs_bounded
    r1cs_satisfy := h.r1cs_satisfy
  }
  · intro a ha
    exact (h.m_bounded a ha).mono (by simp)
  · calc
      cs.result.m.map (Bool.toInt ∘ LC.eval ws'.boolWitness) =
          cs.result.m.map (Bool.toInt ∘ LC.eval ws.boolWitness) := by
        apply Array.ext
        · simp
        · intro i hi₁ hi₂
          simp only [Array.getElem_map]
          apply congrArg Bool.toInt
          have hi : i < cs.result.m.size := by simpa using hi₁
          apply LC.eval_eq_of_bounded (h.m_bounded _ (Array.getElem_mem hi))
          intro k hk
          exact (boolWitness_append ws r hk).symm
      _ = ws.ints := h.m_eval

private theorem runAt_adequate {a : Circuit α}
    {cs : Semantics.CSBuilder} {ws ws' : Semantics.Witgen.State}
    {value : α} (hrel : Related cs ws)
    (hrun : StateT.run (Semantics.Witgen.runAt a) ws = some (value, ws')) :
    let result := StateT.run (Semantics.CSBuilder.runAt a) cs
    result.1 = value ∧ Related result.2 ws' := by
  let motive := fun (γ : Eff.Scope) (α : Type) (a : Free Eff γ α) =>
    match γ with
    | .constraint => ∀ (cs : Semantics.CSBuilder)
        (ws ws' : Semantics.Witgen.State) (value : α),
        Related cs ws →
        StateT.run (Semantics.Witgen.runAt a) ws = some (value, ws') →
        let result := StateT.run (Semantics.CSBuilder.runAt a) cs
        result.1 = value ∧ Related result.2 ws'
    | .hint => True
  refine (Free.recOn (motive := motive) a ?_ ?_)
    cs ws ws' value hrel hrun
  · intro γ α value
    cases γ with
    | hint => trivial
    | constraint =>
      intro cs ws ws' value' hrel hrun
      simp [Semantics.Witgen.runAt, Semantics.CSBuilder.runAt] at hrun ⊢
      rcases hrun with ⟨rfl, rfl⟩
      exact ⟨rfl, hrel⟩
  · intro γ α e blocks k _ ihk
    cases γ with
    | hint => trivial
    | constraint =>
      intro cs ws ws' value hrel hrun
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind (lawfulM := fun γ => match γ with
            | .constraint => inferInstance
            | .hint => inferInstance),
        Free.interp_op (lawfulM := fun γ => match γ with
            | .constraint => inferInstance
            | .hint => inferInstance)] at hrun
      unfold Semantics.CSBuilder.runAt
      rw [Free.interp_bind (lawfulM := fun γ => match γ with
            | .constraint => inferInstance
            | .hint => inferInstance),
        Free.interp_op (lawfulM := fun γ => match γ with
            | .constraint => inferInstance
            | .hint => inferInstance)]
      cases e with
      | assertR1C a b c =>
          by_cases hall : a.Bounded ws.ints.size ∧ b.Bounded ws.ints.size ∧
              c.Bounded ws.ints.size ∧
              a.eval ws.intWitness * b.eval ws.intWitness = c.eval ws.intWitness
          · rcases hall with ⟨ha, hb, hc, hsat⟩
            simp [Semantics.Witgen.handler, ha, hb, hc, hsat] at hrun
            simp [Semantics.CSBuilder.handler]
            exact ihk () _ _ _ _ (hrel.assertR1C ⟨ha, hb, hc⟩ hsat) hrun
          · simp [Semantics.Witgen.handler, hall] at hrun
      | f2z a =>
          by_cases ha : a.Bounded ws.bools.size
          · have hsize : cs.result.m.size = ws.ints.size := by
              simpa using congrArg Array.size hrel.m_eval
            simp [Semantics.Witgen.handler, ha] at hrun
            simp [Semantics.CSBuilder.handler]
            rw [hsize]
            exact ihk ({ws.ints.size} : LC ℤ) _ _ _ _
              (hrel.f2z a ha) hrun
          · simp [Semantics.Witgen.handler, ha] at hrun
      | hint argTps args n =>
          cases hbody : Semantics.Witgen.runAt (blocks ()
            (Semantics.Witgen.evalArgs ws args)) with
          | none =>
              unfold Semantics.Witgen.runAt at hbody
              simp [Semantics.Witgen.handler, hbody] at hrun
          | some r =>
              unfold Semantics.Witgen.runAt at hbody
              simp [Semantics.Witgen.handler, hbody] at hrun
              have hn : r.toArray.size = n := by simp
              have hrel' : Related
                  { cs with nextWit := cs.nextWit + n }
                  { ws with bools := ws.bools ++ r.toArray } := by
                simpa [hn] using hrel.hint r.toArray
              simp [Semantics.CSBuilder.handler]
              simpa only [Semantics.CSBuilder.runAt, hrel.nextWit_eq] using
                ihk (Vector.ofFn fun i => ({ws.bools.size + i.val} : LC Bool))
                  _ _ _ _ hrel' hrun

private theorem adequate_run' {α} {circ : Circuit α} {value : α}
    {ws : Semantics.Witgen.State} :
    StateT.run (Semantics.Witgen.run' circ) default = some (value, ws) →
    (Semantics.CSBuilder.run circ default).2.satisfies ws.boolWitness := by
  intro hrun
  have h := runAt_adequate
    (a := circ) (cs := default) (ws := default) (ws' := ws) (value := value)
    Related.initial (by simpa [Semantics.Witgen.run'] using hrun)
  simp only [Semantics.CSBuilder.run, Semantics.CSBuilder.run'] at ⊢
  generalize hcs : StateT.run (Semantics.CSBuilder.runAt circ) default = result at h ⊢
  rcases result with ⟨result, cs⟩
  exact h.2.satisfies

theorem adequate_run {α} {circ : Circuit α} {wit : Array Bool} :
    Semantics.Witgen.run circ = some wit →
    (Semantics.CSBuilder.run circ default).2.satisfies (wit[·]!) := by
  intro hrun
  unfold Semantics.Witgen.run at hrun
  generalize hstate : StateT.run (Semantics.Witgen.run' circ) default = result at hrun
  cases result with
  | none => simp at hrun
  | some result =>
      rcases result with ⟨value, ws⟩
      simp at hrun
      subst wit
      exact adequate_run' hstate

theorem adequate {α} {circ : Circuit α} :
    ⦃ ⌜True⌝ ⦄ Semantics.Witgen.run circ ⦃ ⇓ _ => ⌜True⌝ ⦄ →
    ∃ wit, Semantics.Witgen.run circ = some wit ∧
      (Semantics.CSBuilder.run circ default).2.satisfies (wit[·]!) := by
  intro htriple
  rw [Triple.iff] at htriple
  let P : Option (Array Bool) → Prop
    | some _ => True
    | none => False
  have hsome : P (Semantics.Witgen.run circ) := by
    apply Option.of_wp_eq rfl P
    simpa [P, PostCond.noThrow, ExceptConds.false, ExceptConds.const] using htriple
  cases hrun : Semantics.Witgen.run circ with
  | none =>
      simp [P, hrun] at hsome
  | some wit =>
      refine ⟨wit, rfl, ?_⟩
      exact adequate_run hrun


end Freigen.F2Z.Complete
