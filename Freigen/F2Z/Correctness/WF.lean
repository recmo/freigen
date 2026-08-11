import Freigen.F2Z.Defs

namespace Freigen.F2Z.WF

/-- A total interpretation of every Boolean and integer witness identifier. -/
structure Valuation where
  bool : Nat → Bool
  int : Nat → ℤ

/-- Two linear combinations have the same value in their respective valuations. -/
def LCEq {F : Type u} [Semiring F] [DecidableEq F]
    (leftVal rightVal : Nat → F) (left right : LC F) : Prop :=
  left.eval leftVal = right.eval rightVal

/-- Evaluate a heterogeneous list of hint arguments. -/
def evalArgs (valuation : Valuation) :
    {argTps : List Eff.WitnessSide} →
    HList Eff.WitnessSide.denoteW argTps →
    HList Eff.WitnessSide.denoteF argTps
  | [], .nil => .nil
  | .z :: _, .cons x xs =>
      .cons (show ℤ from x.eval valuation.int) (evalArgs valuation xs)
  | .f₂ :: _, .cons x xs =>
      .cons (show Bool from x.eval valuation.bool) (evalArgs valuation xs)

/-- Hint arguments are equivalent when they evaluate to the same heterogeneous tuple. -/
def ArgsEq (leftVal rightVal : Valuation)
    {argTps : List Eff.WitnessSide}
    (left right : HList Eff.WitnessSide.denoteW argTps) : Prop :=
  evalArgs leftVal left = evalArgs rightVal right

/-- A vector of Boolean LCs realizes a vector of values under a valuation. -/
def RealizesBools (valuation : Nat → Bool)
    (xs : Vector (LC Bool) n) (values : Vector Bool n) : Prop :=
  ∀ (i : Nat) (hi : i < n),
    LC.eval valuation xs[i] = values[i]

/-- Assumptions describing which pairs of total valuations are currently related. -/
abbrev Assumption := Valuation → Valuation → Prop

/-- A postcondition over two results under two total valuations. -/
abbrev Post (alpha : Type) := Valuation → Valuation → alpha → alpha → Prop

/--
The representation-parametric semantics of circuits.

`P` describes the currently related pairs of total valuations. Effects strengthen `P`
with the semantic equations satisfied by their returned LCs. Nothing is allocated or
mutated in this semantics: the valuations are total from the beginning, and a circuit
must behave uniformly for every pair satisfying `P`.
-/
inductive Rel {alpha : Type} (Q : Post alpha) :
    Assumption → Circuit alpha → Circuit alpha → Prop
  | pure {P : Assumption} {left right : alpha} :
      (∀ leftVal rightVal, P leftVal rightVal →
        Q leftVal rightVal left right) →
      Rel Q P (pure left) (pure right)
  | assertR1C {P : Assumption}
      {aL bL cL aR bR cR : LC ℤ}
      {kL kR : Unit → Circuit alpha} :
      (∀ leftVal rightVal, P leftVal rightVal →
        LCEq leftVal.int rightVal.int aL aR) →
      (∀ leftVal rightVal, P leftVal rightVal →
        LCEq leftVal.int rightVal.int bL bR) →
      (∀ leftVal rightVal, P leftVal rightVal →
        LCEq leftVal.int rightVal.int cL cR) →
      Rel Q P (kL ()) (kR ()) →
      Rel Q P
        (F2Z.assertR1C aL bL cL >>= kL)
        (F2Z.assertR1C aR bR cR >>= kR)
  | f2z {P : Assumption} {aL aR : LC Bool}
      {kL kR : LC ℤ → Circuit alpha} :
      (∀ leftVal rightVal, P leftVal rightVal →
        LCEq leftVal.bool rightVal.bool aL aR) →
      (∀ outL outR,
        Rel Q
          (fun leftVal rightVal =>
            P leftVal rightVal ∧
            outL.eval leftVal.int = (aL.eval leftVal.bool).toInt ∧
            outR.eval rightVal.int = (aR.eval rightVal.bool).toInt)
          (kL outL) (kR outR)) →
      Rel Q P
        (F2Z.f2z aL >>= kL)
        (F2Z.f2z aR >>= kR)
  | hint {P : Assumption} {n : Nat} {argTps : List Eff.WitnessSide}
      {argsL argsR : HList Eff.WitnessSide.denoteW argTps}
      {bodyL bodyR : HList Eff.WitnessSide.denoteF argTps → Vector Bool n}
      {kL kR : Vector (LC Bool) n → Circuit alpha} :
      (∀ leftVal rightVal, P leftVal rightVal →
        ArgsEq leftVal rightVal argsL argsR) →
      (∀ leftVal rightVal, P leftVal rightVal →
        bodyL (evalArgs leftVal argsL) =
          bodyR (evalArgs rightVal argsR)) →
      (∀ outL outR,
        Rel Q
          (fun leftVal rightVal =>
            P leftVal rightVal ∧
            RealizesBools leftVal.bool outL
              (bodyL (evalArgs leftVal argsL)) ∧
            RealizesBools rightVal.bool outR
              (bodyR (evalArgs rightVal argsR)))
          (kL outL) (kR outR)) →
      Rel Q P
        (F2Z.hint argsL bodyL >>= kL)
        (F2Z.hint argsR bodyR >>= kR)

theorem Rel.assertR1C_pure {Q : Post Unit} {P : Assumption}
    {aL bL cL aR bR cR : LC ℤ}
    (ha : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.int rightVal.int aL aR)
    (hb : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.int rightVal.int bL bR)
    (hc : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.int rightVal.int cL cR)
    (hpost : ∀ leftVal rightVal, P leftVal rightVal →
      Q leftVal rightVal () ()) :
    Rel Q P (F2Z.assertR1C aL bL cL) (F2Z.assertR1C aR bR cR) := by
  simpa only [bind_pure] using
    Rel.assertR1C ha hb hc (Rel.pure hpost)

theorem Rel.mono {P Q : Post alpha} {R : Assumption}
    {left right : Circuit alpha} (h : Rel P R left right)
    (hpq : ∀ leftVal rightVal left right,
      P leftVal rightVal left right → Q leftVal rightVal left right) :
    Rel Q R left right := by
  induction h with
  | pure hpost => exact .pure fun l r hR => hpq _ _ _ _ (hpost l r hR)
  | assertR1C ha hb hc _ ih => exact .assertR1C ha hb hc ih
  | f2z ha _ ih => exact .f2z ha ih
  | hint hargs hbody _ ih => exact .hint hargs hbody ih

theorem Rel.bind {P : Post alpha} {Q : Post beta} {R : Assumption}
    {left right : Circuit alpha} (h : Rel P R left right)
    (fL fR : alpha → Circuit beta)
    (hcont : ∀ (S : Assumption) left right,
      (∀ leftVal rightVal, S leftVal rightVal →
        P leftVal rightVal left right) →
      Rel Q S (fL left) (fR right)) :
    Rel Q R (left >>= fL) (right >>= fR) := by
  induction h with
  | pure hpost => simpa using hcont _ _ _ hpost
  | assertR1C ha hb hc _ ih =>
      simpa only [bind_assoc] using Rel.assertR1C ha hb hc ih
  | f2z ha _ ih =>
      simpa only [bind_assoc] using Rel.f2z ha ih
  | hint hargs hbody _ ih =>
      simpa only [bind_assoc] using Rel.hint hargs hbody ih

/-- A relational specification under a predicate on global valuations. -/
def Valid (P : Assumption) (left right : Circuit alpha) (Q : Post alpha) : Prop :=
  Rel Q P left right

/-- A reusable relational contract for a gadget. -/
def GadgetSpec (P : Valuation → Valuation → input → input → Prop)
    (gadget : input → Circuit output) (Q : Post output) : Prop :=
  ∀ left right,
    Rel Q (fun leftVal rightVal => P leftVal rightVal left right)
      (gadget left) (gadget right)

/-- A closed circuit behaves uniformly for every pair of total valuations. -/
def WellFormed (circ : Circuit alpha) : Prop :=
  Rel (fun _ _ _ _ => True) (fun _ _ => True) circ circ

theorem wellFormed_iff {circ : Circuit alpha} :
    WellFormed circ ↔
      Rel (fun _ _ _ _ => True) (fun _ _ => True) circ circ :=
  Iff.rfl

attribute [grind intro] Rel
attribute [grind ←] Rel.assertR1C_pure
attribute [grind =]
  LC.eval_zero LC.eval_add LC.eval_nsmul LC.eval_smul
  LC.eval_one LC.eval_ofConst LC.eval_singleton Vector.getElem_map
attribute [grind unfold]
  WellFormed Valid LCEq ArgsEq evalArgs RealizesBools

/-- Discharge representation-parametricity goals after unfolding the circuit under test. -/
macro "wfgen" : tactic =>
  `(tactic| grind +splitImp)

end Freigen.F2Z.WF
