import Freigen.F2Z.Semantics
import Freigen.F2Z.Nondet
import Freigen.F2Z.WF
import Std.Tactic.Do

namespace Freigen.F2Z.Complete

open Std.Do
open scoped Std.Do

/-- The proof-facing semantics has no allocator or mutable state. -/
abbrev InterpM (_ : Eff.Scope) := Option

instance : (scope : Eff.Scope) → Monad (InterpM scope)
  | .constraint => inferInstance
  | .hint => inferInstance

instance : (scope : Eff.Scope) → LawfulMonad (InterpM scope)
  | .constraint => inferInstance
  | .hint => inferInstance

def interpHandler (valuation : WF.Valuation) :
    Freigen.Eff.Handler Eff InterpM :=
  @fun
    | .constraint, .assertR1C a b c, _ =>
        if a.eval valuation.int * b.eval valuation.int = c.eval valuation.int then
          some ()
        else
          none
    | .constraint, .f2z a, _ =>
        some (LC.ofConst (a.eval valuation.bool).toInt)
    | .constraint, .hint _ args _, block => do
        let values ← block () (WF.evalArgs valuation args)
        pure (values.map LC.ofConst)
    | .hint, .fail _, _ => none

/-- Stateless denotation of a circuit under a total valuation. -/
def interp (valuation : WF.Valuation) (circ : Circuit α) : Option α :=
  Free.interp (interpHandler valuation) circ

@[simp]
theorem interp_pure (valuation : WF.Valuation) (value : α) :
    interp valuation (pure value : Circuit α) = some value := by
  rfl

@[simp]
theorem interp_bind (valuation : WF.Valuation)
    (circ : Circuit α) (k : α → Circuit β) :
    interp valuation (circ >>= k) =
      (interp valuation circ >>= fun value => interp valuation (k value)) := by
  simp [interp, Free.interp_bind]

@[simp]
theorem interp_assertR1C (valuation : WF.Valuation) (a b c : LC ℤ) :
    interp valuation (F2Z.assertR1C a b c) =
      if a.eval valuation.int * b.eval valuation.int = c.eval valuation.int then
        some ()
      else
        none := by
  unfold interp F2Z.assertR1C
  rw [Free.interp_op]
  rfl

@[simp]
theorem interp_f2z (valuation : WF.Valuation) (a : LC Bool) :
    interp valuation (F2Z.f2z a) =
      some (LC.ofConst (a.eval valuation.bool).toInt) := by
  unfold interp F2Z.f2z
  rw [Free.interp_op]
  rfl

@[simp]
theorem interp_hint (valuation : WF.Valuation)
    {argTps : List Eff.WitnessSide}
    (args : HList Eff.WitnessSide.denoteW argTps)
    (body : HList Eff.WitnessSide.denoteF argTps → Vector Bool n) :
    interp valuation (F2Z.hint args body) =
      some ((body (WF.evalArgs valuation args)).map LC.ofConst) := by
  unfold interp F2Z.hint
  rw [Free.interp_op]
  simp [interpHandler]

private def BoolsRealize (ws : Semantics.Witgen.State)
    (valuation : Nat → Bool) : Prop :=
  ∀ i, i < ws.bools.size → valuation i = ws.boolWitness i

private structure RightRealizes (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) (valuation : WF.Valuation) : Prop where
  bools : BoolsRealize ws valuation.bool
  ints : ∀ (i : Nat) (hi : i < cs.result.m.size),
    valuation.int i =
      ((cs.result.m[i]'hi).eval valuation.bool).toInt

private structure Compatible (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) (leftVal rightVal : WF.Valuation) : Prop where
  left_bools : BoolsRealize ws leftVal.bool
  right : RightRealizes cs ws rightVal

private def leftValuation (ws : Semantics.Witgen.State) : WF.Valuation where
  bool := ws.boolWitness
  int := Semantics.Witgen.zeroWitness

private def rightValuation (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) : WF.Valuation where
  bool := ws.boolWitness
  int := cs.result.intWitness ws.boolWitness

private theorem BoolsRealize.self (ws : Semantics.Witgen.State) :
    BoolsRealize ws ws.boolWitness := by
  intro i hi
  rfl

private theorem RightRealizes.canonical (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) :
    RightRealizes cs ws (rightValuation cs ws) := by
  constructor
  · exact BoolsRealize.self ws
  · intro i hi
    simp only [rightValuation, Semantics.CS.intWitness]
    rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_map]
    rfl

private def ConstraintsValid (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) : Prop :=
  ∀ valuation, RightRealizes cs ws valuation →
    ∀ r ∈ cs.result.r1cs, r.satisfies valuation.int

private theorem ConstraintsValid.initial :
    ConstraintsValid default default := by
  intro valuation hrel r hr
  change r ∈ (#[] : Array (Semantics.R1C ℤ)) at hr
  simp at hr

private theorem boolWitness_append (ws : Semantics.Witgen.State)
    (values : Array Bool) {i : Nat} (hi : i < ws.bools.size) :
    ws.boolWitness i = ({ ws with bools := ws.bools ++ values }).boolWitness i := by
  unfold Semantics.Witgen.State.boolWitness
  rw [getElem!_pos ws.bools i hi,
    getElem!_pos (ws.bools ++ values) i (by simp; omega)]
  exact (Array.getElem_append_left hi).symm

private theorem BoolsRealize.of_append {ws : Semantics.Witgen.State}
    {values : Array Bool} {valuation : Nat → Bool}
    (h : BoolsRealize { ws with bools := ws.bools ++ values } valuation) :
    BoolsRealize ws valuation := by
  intro i hi
  rw [h i (by simp; omega)]
  exact boolWitness_append ws values hi |>.symm

private theorem evalArgs_canonical (ws : Semantics.Witgen.State) :
    {argTps : List Eff.WitnessSide} →
    (args : HList Eff.WitnessSide.denoteW argTps) →
    WF.evalArgs (leftValuation ws) args = Semantics.Witgen.evalArgs ws args
  | [], .nil => rfl
  | .z :: _, .cons x xs => by
      change HList.cons (a := .z) (show ℤ from x.eval Semantics.Witgen.zeroWitness)
        (WF.evalArgs (leftValuation ws) xs) =
        HList.cons (a := .z) (show ℤ from x.eval Semantics.Witgen.zeroWitness)
          (Semantics.Witgen.evalArgs ws xs)
      rw [evalArgs_canonical ws xs]
  | .f₂ :: _, .cons x xs => by
      change HList.cons (a := .f₂) (show Bool from x.eval ws.boolWitness)
        (WF.evalArgs (leftValuation ws) xs) =
        HList.cons (a := .f₂) (show Bool from x.eval ws.boolWitness)
          (Semantics.Witgen.evalArgs ws xs)
      rw [evalArgs_canonical ws xs]

private def csHintOut (cs : Semantics.CSBuilder) (n : Nat) :
    Vector (LC Bool) n :=
  Vector.ofFn fun i => ({cs.nextWit + i.val} : LC Bool)

private def pushR1C (cs : Semantics.CSBuilder) (a b c : LC ℤ) :
    Semantics.CSBuilder :=
  { cs with result := { cs.result with
      r1cs := cs.result.r1cs.push { a, b, c } } }

private def pushF2Z (cs : Semantics.CSBuilder) (a : LC Bool) :
    Semantics.CSBuilder :=
  { cs with result := { cs.result with m := cs.result.m.push a } }

private def pushHint (cs : Semantics.CSBuilder) (n : Nat) :
    Semantics.CSBuilder :=
  { cs with nextWit := cs.nextWit + n }

private def appendHint (ws : Semantics.Witgen.State) (values : Vector Bool n) :
    Semantics.Witgen.State :=
  { ws with bools := ws.bools ++ values.toArray }

private theorem csHintOut_realizes
    (cs : Semantics.CSBuilder) (ws : Semantics.Witgen.State)
    (values : Vector Bool n) (valuation : Nat → Bool)
    (hnext : cs.nextWit = ws.bools.size)
    (h : BoolsRealize (appendHint ws values) valuation) :
    WF.RealizesBools valuation (csHintOut cs n) values := by
  intro i hi
  simp only [csHintOut, Vector.getElem_ofFn, LC.eval_singleton]
  rw [hnext]
  rw [h (ws.bools.size + i) (by simp [appendHint]; omega)]
  unfold Semantics.Witgen.State.boolWitness appendHint
  rw [getElem!_pos _ _ (by simp; omega)]
  rw [Array.getElem_append_right (by omega)]
  simp

private theorem RightRealizes.of_pushR1C
    {cs : Semantics.CSBuilder} {ws : Semantics.Witgen.State}
    {valuation : WF.Valuation} {a b c : LC ℤ}
    (h : RightRealizes (pushR1C cs a b c) ws valuation) :
    RightRealizes cs ws valuation := by
  exact ⟨h.bools, by intro i hi; simpa [pushR1C] using h.ints i hi⟩

private theorem RightRealizes.of_pushF2Z
    {cs : Semantics.CSBuilder} {ws : Semantics.Witgen.State}
    {valuation : WF.Valuation} {a : LC Bool}
    (h : RightRealizes (pushF2Z cs a) ws valuation) :
    RightRealizes cs ws valuation := by
  refine ⟨h.bools, ?_⟩
  intro i hi
  simpa [pushF2Z, Array.getElem_push_lt hi] using
    h.ints i (by simp [pushF2Z]; omega)

private theorem RightRealizes.of_pushHint
    {cs : Semantics.CSBuilder} {ws : Semantics.Witgen.State}
    {valuation : WF.Valuation} {values : Vector Bool n}
    (h : RightRealizes (pushHint cs n) (appendHint ws values) valuation) :
    RightRealizes cs ws valuation := by
  refine ⟨BoolsRealize.of_append h.bools, ?_⟩
  intro i hi
  simpa [pushHint, appendHint] using h.ints i hi

private theorem Compatible.leftCanonical
    {cs : Semantics.CSBuilder} {ws : Semantics.Witgen.State}
    {rightVal : WF.Valuation} (h : RightRealizes cs ws rightVal) :
    Compatible cs ws (leftValuation ws) rightVal :=
  ⟨BoolsRealize.self ws, h⟩

private theorem constBools_realizes (valuation : Nat → Bool)
    (values : Vector Bool n) :
    WF.RealizesBools valuation (values.map LC.ofConst) values := by
  intro i hi
  simp

private theorem runAt_interp_adequate
    {P : WF.Assumption} {left right : Circuit α}
    {ws ws' : Semantics.Witgen.State} {value : α}
    (hrel : WF.Rel (fun _ _ _ _ => True) P left right)
    (rightVal : WF.Valuation)
    (hP : ∀ leftVal, BoolsRealize ws leftVal.bool →
      P leftVal rightVal)
    (hrun : StateT.run (Semantics.Witgen.runAt left) ws =
      some (value, ws')) :
    ∃ result, interp rightVal right = some result := by
  induction hrel generalizing ws ws' value with
  | pure hpost =>
      simp [Semantics.Witgen.runAt] at hrun
      exact ⟨_, rfl⟩
  | @assertR1C P aL bL cL aR bR cR kL kR ha hb hc hcont ih =>
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.assertR1C at hrun
      rw [Free.interp_op] at hrun
      by_cases hsat :
          aL.eval Semantics.Witgen.zeroWitness *
            bL.eval Semantics.Witgen.zeroWitness =
            cL.eval Semantics.Witgen.zeroWitness
      · simp [Semantics.Witgen.handler, hsat] at hrun
        have hp := hP (leftValuation ws) (BoolsRealize.self ws)
        have ha' := ha (leftValuation ws) rightVal hp
        have hb' := hb (leftValuation ws) rightVal hp
        have hc' := hc (leftValuation ws) rightVal hp
        unfold WF.LCEq at ha' hb' hc'
        have hsatRight :
            aR.eval rightVal.int * bR.eval rightVal.int =
              cR.eval rightVal.int := by
          rw [← ha', ← hb', ← hc']
          exact hsat
        obtain ⟨result, hresult⟩ := ih hP hrun
        refine ⟨result, ?_⟩
        unfold interp
        rw [Free.interp_bind]
        unfold F2Z.assertR1C
        rw [Free.interp_op]
        simp [interpHandler, hsatRight]
        exact hresult
      · simp [Semantics.Witgen.handler, hsat] at hrun
  | @f2z P aL aR kL kR ha hcont ih =>
      let outL : LC ℤ := LC.ofConst (aL.eval ws.boolWitness).toInt
      let outR : LC ℤ := LC.ofConst (aR.eval rightVal.bool).toInt
      have hP' : ∀ leftVal, BoolsRealize ws leftVal.bool →
          (P leftVal rightVal ∧
            outL.eval leftVal.int = (aL.eval leftVal.bool).toInt ∧
            outR.eval rightVal.int = (aR.eval rightVal.bool).toInt) := by
        intro leftVal hleft
        have hp := hP leftVal hleft
        have hpCanonical := hP (leftValuation ws) (BoolsRealize.self ws)
        have harg := ha leftVal rightVal hp
        have hargCanonical := ha (leftValuation ws) rightVal hpCanonical
        unfold WF.LCEq at harg hargCanonical
        refine ⟨hp, ?_, ?_⟩
        · simp only [outL, LC.eval_ofConst]
          exact congrArg Bool.toInt (hargCanonical.trans harg.symm)
        · simp [outR]
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.f2z at hrun
      rw [Free.interp_op] at hrun
      simp [Semantics.Witgen.handler] at hrun
      obtain ⟨result, hresult⟩ := ih outL outR hP' hrun
      refine ⟨result, ?_⟩
      unfold interp
      rw [Free.interp_bind]
      unfold F2Z.f2z
      rw [Free.interp_op]
      simp [interpHandler]
      exact hresult
  | @hint P n argTps argsL argsR bodyL bodyR kL kR
      hargs hbody hcont ih =>
      let valuesL := bodyL (Semantics.Witgen.evalArgs ws argsL)
      let valuesR := bodyR (WF.evalArgs rightVal argsR)
      let outL : Vector (LC Bool) n := valuesL.map LC.ofConst
      let outR : Vector (LC Bool) n := valuesR.map LC.ofConst
      let wsNext := appendHint ws valuesL
      have hP' : ∀ leftVal, BoolsRealize wsNext leftVal.bool →
          (P leftVal rightVal ∧
            WF.RealizesBools leftVal.bool outL
              (bodyL (WF.evalArgs leftVal argsL)) ∧
            WF.RealizesBools rightVal.bool outR
              (bodyR (WF.evalArgs rightVal argsR))) := by
        intro leftVal hleft
        have hleftOld := BoolsRealize.of_append hleft
        have hp := hP leftVal hleftOld
        have hpCanonical := hP (leftValuation ws) (BoolsRealize.self ws)
        have hbodyAny := hbody leftVal rightVal hp
        have hbodyCanonical := hbody (leftValuation ws) rightVal hpCanonical
        rw [evalArgs_canonical] at hbodyCanonical
        refine ⟨hp, ?_, ?_⟩
        · rw [hbodyAny, ← hbodyCanonical]
          exact constBools_realizes leftVal.bool valuesL
        · exact constBools_realizes rightVal.bool valuesR
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.hint at hrun
      rw [Free.interp_op] at hrun
      simp [Semantics.Witgen.handler] at hrun
      obtain ⟨result, hresult⟩ := ih outL outR hP' hrun
      refine ⟨result, ?_⟩
      unfold interp
      rw [Free.interp_bind]
      unfold F2Z.hint
      rw [Free.interp_op]
      simp [interpHandler]
      exact hresult

/-- The valuation induced by a completed witness-generator run. -/
def witnessValuation (wit : Array Bool) : WF.Valuation where
  bool := fun i => wit[i]!
  int := Semantics.Witgen.zeroWitness

/--
Every successful concrete witness-generator run of a well-formed circuit is represented
by a successful execution of the stateless `Option` denotation.

The result is existential because the public witness-generator runner discards the
circuit's return value and exposes only the completed Boolean witness array.
-/
theorem interp_adequate {circ : Circuit α} {wit : Array Bool} :
    WF.WellFormed circ →
    Semantics.Witgen.run circ = some wit →
    ∃ result, interp (witnessValuation wit) circ = some result := by
  intro hwf hrun
  unfold Semantics.Witgen.run at hrun
  generalize hstate : StateT.run (Semantics.Witgen.run' circ) default = runResult at hrun
  cases runResult with
  | none => simp at hrun
  | some runResult =>
      rcases runResult with ⟨value, ws⟩
      simp at hrun
      subst wit
      exact runAt_interp_adequate hwf (witnessValuation ws.bools)
        (fun _ _ => True.intro)
        (by simpa [Semantics.Witgen.run'] using hstate)

private theorem runAt_adequate {P : WF.Assumption} {left right : Circuit α}
    {cs : Semantics.CSBuilder} {ws ws' : Semantics.Witgen.State} {value : α}
    (hrel : WF.Rel (fun _ _ _ _ => True) P left right)
    (hnext : cs.nextWit = ws.bools.size)
    (hP : ∀ leftVal rightVal,
      Compatible cs ws leftVal rightVal → P leftVal rightVal)
    (hvalid : ConstraintsValid cs ws)
    (hrun : StateT.run (Semantics.Witgen.runAt left) ws = some (value, ws')) :
    let result := StateT.run (Semantics.CSBuilder.runAt right) cs
    result.2.nextWit = ws'.bools.size ∧ ConstraintsValid result.2 ws' := by
  induction hrel generalizing cs ws ws' value with
  | pure hpost =>
      simp [Semantics.Witgen.runAt] at hrun
      rcases hrun with ⟨rfl, rfl⟩
      change cs.nextWit = ws.bools.size ∧ ConstraintsValid cs ws
      exact ⟨hnext, hvalid⟩
  | @assertR1C P aL bL cL aR bR cR kL kR ha hb hc hcont ih =>
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.assertR1C at hrun
      rw [Free.interp_op] at hrun
      unfold Semantics.CSBuilder.runAt
      rw [Free.interp_bind]
      unfold F2Z.assertR1C
      rw [Free.interp_op]
      by_cases hsat :
          aL.eval Semantics.Witgen.zeroWitness *
            bL.eval Semantics.Witgen.zeroWitness =
            cL.eval Semantics.Witgen.zeroWitness
      · simp [Semantics.Witgen.handler, Semantics.CSBuilder.handler, hsat] at hrun ⊢
        let cs' := pushR1C cs aR bR cR
        have hP' : ∀ leftVal rightVal,
            Compatible cs' ws leftVal rightVal → P leftVal rightVal := by
          intro leftVal rightVal hcompat
          exact hP leftVal rightVal
            ⟨hcompat.left_bools, hcompat.right.of_pushR1C⟩
        have hvalid' : ConstraintsValid cs' ws := by
          intro valuation hrealizes r hr
          simp only [cs', pushR1C, Array.mem_push] at hr
          rcases hr with hr | rfl
          · exact hvalid valuation hrealizes.of_pushR1C r hr
          · have hp := hP (leftValuation ws) valuation
                (Compatible.leftCanonical hrealizes.of_pushR1C)
            have ha' := ha (leftValuation ws) valuation hp
            have hb' := hb (leftValuation ws) valuation hp
            have hc' := hc (leftValuation ws) valuation hp
            unfold WF.LCEq at ha' hb' hc'
            unfold Semantics.R1C.satisfies
            rw [← ha', ← hb', ← hc']
            exact hsat
        exact ih hnext hP' hvalid' hrun
      · simp [Semantics.Witgen.handler, hsat] at hrun
  | @f2z P aL aR kL kR ha hcont ih =>
      let outL : LC ℤ := LC.ofConst (aL.eval ws.boolWitness).toInt
      let outR : LC ℤ := {cs.result.m.size}
      let cs' := pushF2Z cs aR
      have hP' : ∀ leftVal rightVal,
          Compatible cs' ws leftVal rightVal →
          (P leftVal rightVal ∧
            outL.eval leftVal.int = (aL.eval leftVal.bool).toInt ∧
            outR.eval rightVal.int = (aR.eval rightVal.bool).toInt) := by
        intro leftVal rightVal hcompat
        have hrightOld := hcompat.right.of_pushF2Z
        have hp := hP leftVal rightVal
          ⟨hcompat.left_bools, hrightOld⟩
        have hpCanonical := hP (leftValuation ws) rightVal
          (Compatible.leftCanonical hrightOld)
        have harg := ha leftVal rightVal hp
        have hargCanonical := ha (leftValuation ws) rightVal hpCanonical
        unfold WF.LCEq at harg hargCanonical
        refine ⟨hp, ?_, ?_⟩
        · simp only [outL, LC.eval_ofConst]
          exact congrArg Bool.toInt (hargCanonical.trans harg.symm)
        · have hnew := hcompat.right.ints cs.result.m.size
              (by simp [cs', pushF2Z])
          simpa [outR, cs', pushF2Z] using hnew
      have hvalid' : ConstraintsValid cs' ws := by
        intro valuation hrealizes r hr
        apply hvalid valuation hrealizes.of_pushF2Z r
        simpa [cs', pushF2Z] using hr
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.f2z at hrun
      rw [Free.interp_op] at hrun
      unfold Semantics.CSBuilder.runAt
      rw [Free.interp_bind]
      unfold F2Z.f2z
      rw [Free.interp_op]
      simp [Semantics.Witgen.handler, Semantics.CSBuilder.handler] at hrun ⊢
      exact ih outL outR hnext hP' hvalid' hrun
  | @hint P n argTps argsL argsR bodyL bodyR kL kR
      hargs hbody hcont ih =>
      let values := bodyL (Semantics.Witgen.evalArgs ws argsL)
      let outL : Vector (LC Bool) n := values.map LC.ofConst
      let outR := csHintOut cs n
      let cs' := pushHint cs n
      let wsNext := appendHint ws values
      have hP' : ∀ leftVal rightVal,
          Compatible cs' wsNext leftVal rightVal →
          (P leftVal rightVal ∧
            WF.RealizesBools leftVal.bool outL
              (bodyL (WF.evalArgs leftVal argsL)) ∧
            WF.RealizesBools rightVal.bool outR
              (bodyR (WF.evalArgs rightVal argsR))) := by
        intro leftVal rightVal hcompat
        have hleftOld := BoolsRealize.of_append hcompat.left_bools
        have hrightOld := hcompat.right.of_pushHint
        have hp := hP leftVal rightVal ⟨hleftOld, hrightOld⟩
        have hpCanonical := hP (leftValuation ws) rightVal
          (Compatible.leftCanonical hrightOld)
        have hbodyAny := hbody leftVal rightVal hp
        have hbodyCanonical := hbody (leftValuation ws) rightVal hpCanonical
        rw [evalArgs_canonical] at hbodyCanonical
        have hright := csHintOut_realizes cs ws values rightVal.bool
          hnext hcompat.right.bools
        refine ⟨hp, ?_, ?_⟩
        · rw [hbodyAny, ← hbodyCanonical]
          exact constBools_realizes leftVal.bool values
        · rw [← hbodyCanonical]
          exact hright
      have hvalid' : ConstraintsValid cs' wsNext := by
        intro valuation hrealizes r hr
        apply hvalid valuation hrealizes.of_pushHint r
        simpa [cs', pushHint] using hr
      have hnext' : cs'.nextWit = wsNext.bools.size := by
        simp [cs', pushHint, wsNext, appendHint, hnext]
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.hint at hrun
      rw [Free.interp_op] at hrun
      unfold Semantics.CSBuilder.runAt
      rw [Free.interp_bind]
      unfold F2Z.hint
      rw [Free.interp_op]
      simp [Semantics.Witgen.handler, Semantics.CSBuilder.handler] at hrun ⊢
      exact ih outL outR hnext' hP' hvalid' hrun

private theorem ConstraintsValid.satisfies
    {cs : Semantics.CSBuilder} {ws : Semantics.Witgen.State}
    (h : ConstraintsValid cs ws) :
    cs.result.satisfies ws.boolWitness := by
  intro r hr
  exact h (rightValuation cs ws) (RightRealizes.canonical cs ws) r hr

private theorem adequate_run' {circ : Circuit α} {value : α}
    {ws : Semantics.Witgen.State} (hwf : WF.WellFormed circ)
    (hrun : StateT.run (Semantics.Witgen.run' circ) default =
      some (value, ws)) :
    (Semantics.CSBuilder.run circ default).2.satisfies ws.boolWitness := by
  have h := runAt_adequate hwf rfl
    (fun _ _ _ => True.intro) ConstraintsValid.initial
    (by simpa [Semantics.Witgen.run'] using hrun)
  simp only [Semantics.CSBuilder.run, Semantics.CSBuilder.run'] at ⊢
  generalize hcs : StateT.run (Semantics.CSBuilder.runAt circ) default = result at h ⊢
  rcases result with ⟨result, cs⟩
  exact h.2.satisfies

theorem adequate_run {circ : Circuit α} {wit : Array Bool} :
    WF.WellFormed circ →
    Semantics.Witgen.run circ = some wit →
    (Semantics.CSBuilder.run circ default).2.satisfies (wit[·]!) := by
  intro hwf hrun
  unfold Semantics.Witgen.run at hrun
  generalize hstate : StateT.run (Semantics.Witgen.run' circ) default = result at hrun
  cases result with
  | none => simp at hrun
  | some result =>
      rcases result with ⟨value, ws⟩
      simp at hrun
      subst wit
      exact adequate_run' hwf hstate

theorem adequate {circ : Circuit α} :
    WF.WellFormed circ →
    ⦃ ⌜True⌝ ⦄ Semantics.Witgen.run circ ⦃ ⇓ _ => ⌜True⌝ ⦄ →
    ∃ wit, Semantics.Witgen.run circ = some wit ∧
      (Semantics.CSBuilder.run circ default).2.satisfies (wit[·]!) := by
  intro hwf htriple
  rw [Triple.iff] at htriple
  let P : Option (Array Bool) → Prop
    | some _ => True
    | none => False
  have hsome : P (Semantics.Witgen.run circ) := by
    apply Option.of_wp_eq rfl P
    simpa [P, PostCond.noThrow, ExceptConds.false, ExceptConds.const] using htriple
  cases hrun : Semantics.Witgen.run circ with
  | none => simp [P, hrun] at hsome
  | some wit =>
      refine ⟨wit, rfl, ?_⟩
      exact adequate_run hwf hrun

end Freigen.F2Z.Complete
