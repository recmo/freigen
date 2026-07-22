import Freigen.IxPoly.Basic
import Freigen.Eff

namespace Freigen

def ITree (E : Eff.Spec) (α : Type _): Type _ := (Eff.Step E).M α
namespace ITree

open IxPoly

def corec {E} {A : Type _ → Type _} (f : (i : Type _) → A i → Eff.Step E A i): {i : Type _} → A i → ITree E i :=
  IxPoly.M.corec f

def observe {E α} : ITree E α ≃ Eff.Step E (ITree E) α := IxPoly.M.observe

def roll {E α} : Eff.Step E (ITree E) α → ITree E α := IxPoly.M.observe.symm

theorem observe_roll {E α} (x : Eff.Step E (ITree E) α): observe (roll x) = x := observe.apply_symm_apply _

theorem roll_observe {E α} (x : ITree E α): roll (observe x) = x := observe.symm_apply_apply _

theorem observe_corec {E} {A : Type _ → Type _} (f : (i : Type _) → A i → Eff.Step E A i) {i : Type _} (a : A i):
    observe (corec f a) = IxPoly.map (fun _ y => corec f y) i (f i a) := IxPoly.M.observe_corec

def ret {E α} (x : α) : ITree E α := roll $ Eff.Step.ret x
def tau {E α} (x : ITree E α) : ITree E α := roll $ Eff.Step.tau x
def fail {E α} : ITree E α := roll $ Eff.Step.fail
def op {E α} (e : E.tag) (inp : E.input e)
    (blocks : (t : E.blockTag e) → E.blockInputs e t → ITree E (E.blockOutputs e t))
    (k : (o : E.output e) → ITree E α) : ITree E α :=
  roll $ Eff.Step.op e inp blocks k

theorem roll_ret {E α} (x : α) : roll (E:=E) (Eff.Step.ret x) = ret x := rfl
theorem roll_tau {E α} (x : ITree E α) : roll (E:=E) (Eff.Step.tau x) = tau x := rfl
theorem roll_fail {E α} : roll (E:=E) (α:=α) Eff.Step.fail = fail := rfl
theorem roll_op {E α} (e : E.tag) (inp : E.input e)
    (blocks : (t : E.blockTag e) → E.blockInputs e t → ITree E (E.blockOutputs e t))
    (k : (o : E.output e) → ITree E α) :
    roll (E:=E) (Eff.Step.op e inp blocks k) = op e inp blocks k := rfl

@[simp]
theorem observe_ret {E α} (x : α) : observe (ret x (E:=E)) = Eff.Step.ret x := rfl

@[simp]
theorem observe_tau {E α} (x : ITree E α) : observe (tau x (E:=E)) = Eff.Step.tau x := rfl

@[simp]
theorem observe_fail {E α} : observe (fail (E:=E) (α:=α)) = Eff.Step.fail := rfl

@[simp]
theorem observe_op {E α} (e : E.tag) (inp : E.input e)
    (blocks : (t : E.blockTag e) → E.blockInputs e t → ITree E (E.blockOutputs e t))
    (k : (o : E.output e) → ITree E α) :
    observe (op e inp blocks k (E:=E)) = Eff.Step.op e inp blocks k := rfl

protected def casesOn {E} { motive : (α : Type _) → ITree E α → Sort* } {α} (x : ITree E α)
    (ret : ∀ {α} x, motive α (ret x))
    (tau : ∀ {α} x, motive α (tau x))
    (fail : ∀ {α}, motive α fail)
    (op : ∀ {α} e inp blocks k, motive α (op e inp blocks k)):
    motive α x := by
  have : x = roll (observe x) := (observe.symm_apply_apply _).symm
  rw [this]
  cases observe x using Eff.Step.casesOn <;> apply_assumption

inductive BisimRelF {E}
    (R : (α : Type _) → ITree E α → ITree E α → Prop):
    (α : Type _) → Eff.Step E (ITree E) α → Eff.Step E (ITree E) α → Prop where
| ret {α} (x : α): BisimRelF R α (Eff.Step.ret x) (Eff.Step.ret x)
| tau {α} (x y : ITree E α) (hr : R _ x y) : BisimRelF R α (Eff.Step.tau x) (Eff.Step.tau y)
| fail {α} : BisimRelF R α Eff.Step.fail Eff.Step.fail
| op {α} (e : E.tag) (inp : E.input e)
    (k1 k2 : (o : E.output e) → ITree E α)
    (blocks1 blocks2 : (t : E.blockTag e) → E.blockInputs e t → ITree E (E.blockOutputs e t))
    (h1 : ∀ o, R _ (k1 o) (k2 o))
    (h2 : ∀ t i, R _ (blocks1 t i) (blocks2 t i)):
  BisimRelF R α (Eff.Step.op e inp blocks1 k1) (Eff.Step.op e inp blocks2 k2)

theorem BisimRelF.toLiftR {E} {R : (α : Type _) → ITree E α → ITree E α → Prop} : BisimRelF R ≤ IxPoly.M.LiftR (Eff.Step E) R := by
  intro α x y hxy
  cases hxy <;> constructor
  case ret | fail => intro a; cases a
  case tau => intro _; assumption
  case op =>
    intro a
    cases a <;> apply_assumption

theorem BisimRelF.refl {E R}
    (hrefl : ∀ {α} (x : ITree E α), R α x x)
    {α} (x : Eff.Step E (ITree E) α): BisimRelF R α x x := by
  cases x using Eff.Step.casesOn <;> constructor <;> intros <;> apply_assumption

theorem BisimRelF.refl_upToEq {E R}
    {α} (x : Eff.Step E (ITree E) α): BisimRelF (M.IxRel.upToEq R) α x x := by
  apply BisimRelF.refl
  intros
  apply Or.inl
  rfl

theorem bisim {E α} (R : (α : Type _) → ITree E α → ITree E α → Prop)
    (step : ∀{α x y}, R α x y → BisimRelF R α (observe x) (observe y))
    {x y : ITree E α} (hxy : R _ x y) : x = y := by
  apply IxPoly.M.Bisim.coind (R := R)
  · intro α x y hxy
    apply BisimRelF.toLiftR
    apply step hxy
  · assumption

theorem bisim_up_to_eq {E α} (R : (α : Type _) → ITree E α → ITree E α → Prop)
    (step : ∀{α x y}, R α x y → BisimRelF (M.IxRel.upToEq R) α (observe x) (observe y))
    {x y : ITree E α} (hxy : R _ x y) : x = y := by
  apply bisim (R := M.IxRel.upToEq R)
  · intro _ x y hxy
    cases hxy
    · rename_i h
      cases h
      apply BisimRelF.refl_upToEq
    · apply step
      assumption
  · right
    assumption

theorem bisim₂ {E α} {Seed : Type _ → Type _}
    (left right : (i : Type _) → Seed i → ITree E i)
    (step : ∀ {i} (s : Seed i), BisimRelF (M.IxRel.span Seed left right) i (observe (left i s)) (observe (right i s)))
    (seed : Seed α): left α seed = right α seed := by
  apply bisim (R := M.IxRel.span Seed left right)
  intro i x y hxy
  rcases hxy with ⟨s, rfl, rfl⟩
  apply step
  exists seed

theorem bisim₂_up_to_eq {E α} {Seed : Type _ → Type _}
    (left right : (i : Type _) → Seed i → ITree E i)
    (step : ∀ {i} (s : Seed i), BisimRelF (M.IxRel.upToEq (M.IxRel.span Seed left right)) i (observe (left i s)) (observe (right i s)))
    (seed : Seed α): left α seed = right α seed := by
  apply bisim_up_to_eq (R := M.IxRel.span Seed left right)
  intro i x y hxy
  rcases hxy with ⟨s, rfl, rfl⟩
  apply step
  exists seed

def BindCarrier E α R := (ITree E α × (α → ITree E R)) ⊕ ITree E R
def bindCo {E α} R : BindCarrier E α R → Eff.Step E (BindCarrier E α) R
| .inl (e, f) => match e.observe with
  | ⟨.ret x, _⟩ => IxPoly.map (fun _ => .inr) _ (f x).observe
  | ⟨.tau, cont⟩ => ⟨.tau, fun () => .inl (cont (), f)⟩
  | ⟨.fail, _⟩ => ⟨.fail, fun x => PEmpty.elim x⟩
  | ⟨.op e x, cont⟩ => ⟨.op e x, fun
    | .inl o => .inl (cont $ .inl o, f)
    | .inr b => .inr (cont $ .inr b)
  ⟩
| .inr e => IxPoly.map (fun _ => .inr) _ e.observe

theorem bindCo_copy {E β} {x : ITree E β} : corec (bindCo (α := α)) (.inr x) = x := by
  apply bisim (R := fun _ x y => x = corec (bindCo (α := α)) (.inr y))
  intro _ x y hxy
  cases hxy
  · simp only [observe_corec, bindCo, IxPoly.map_map]
    cases y.observe using Eff.Step.casesOn <;> {
       try simp; constructor <;> { intros ; apply_assumption }
    }
  · rfl

instance {E} : Monad (ITree E) where
  pure := fun x => ret x
  bind {α β} (a : ITree E α) (f : α → ITree E β) := corec bindCo (.inl (a, f))

@[simp]
theorem ret_bind {E β} {α} {x : α} {f : α → ITree E β} : ret x >>= f = f x := by
  apply observe.injective
  simp only [Bind.bind, observe_corec, bindCo, ret,
    observe_roll, IxPoly.map_map, Eff.Step.ret, bindCo_copy, IxPoly.map_id]

@[simp]
theorem tau_bind {E β} {α} {x : ITree E α} {f : α → ITree E β} : tau x >>= f = tau (x >>= f) := by
  apply observe.injective
  simp only [Bind.bind, observe_corec, bindCo, tau, observe_roll, Eff.Step.tau, IxPoly.map]
  congr

@[simp]
theorem fail_bind {E β} {α} {f : α → ITree E β} : fail >>= f = fail := by
  apply observe.injective
  simp only [Bind.bind, observe_corec, bindCo, fail, observe_roll, Eff.Step.fail, IxPoly.map]
  congr
  ext a
  cases a

@[simp]
theorem op_bind {E β} {α} {e : E.tag} {inp : E.input e}
    {blocks : (t : E.blockTag e) → E.blockInputs e t → ITree E (E.blockOutputs e t)}
    {k : (o : E.output e) → ITree E α}
    {f : α → ITree E β}:
    (op e inp blocks k) >>= f =
      op e inp
        blocks
        (fun o => k o >>= f) := by
  apply observe.injective
  simp only [Bind.bind, observe_corec, bindCo, op, observe_roll, IxPoly.map]
  simp only [Eff.Step.op]
  congr
  ext a; cases a
  · rfl
  · simp [bindCo_copy]

inductive BindPureRel {E} : (α: Type _) → ITree E α → ITree E α → Prop where
| root {α} (m : ITree E α) : BindPureRel α (m >>= pure) m
| refl {α} (m : ITree E α) : BindPureRel α m m

theorem bind_pure {E α} (a : ITree E α) : a >>= pure = a := by
  apply bisim₂_up_to_eq (Seed := ITree E) (left := fun _ x => x >>= pure) (right := fun _ x => x)
  intro _ m
  cases m using ITree.casesOn with
  | ret | fail => simp [pure, BisimRelF.refl_upToEq]
  | tau x =>
    simp only [tau_bind, observe_tau]
    apply BisimRelF.tau
    right
    exists x
  | op e inp blocks k =>
    simp only [op_bind]
    apply BisimRelF.op
    · intro
      right
      apply Exists.intro
      apply And.intro <;> rfl
    · intros; left; rfl

theorem bind_assoc {E α β γ} {a : ITree E α} {f : α → ITree E β} {g : β → ITree E γ}:
    (a >>= f) >>= g = a >>= fun x => f x >>= g := by
  apply bisim₂_up_to_eq (Seed := fun γ => ITree E α × (α → ITree E β) × (β → ITree E γ))
    (left := fun _ ⟨x, f, g⟩ => (x >>= f) >>= g)
    (right := fun _ ⟨x, f, g⟩ => x >>= fun y => f y >>= g)
    (seed := ⟨a, f, g⟩)
  intro _ ⟨x, f, g⟩
  simp only
  cases x using ITree.casesOn with
  | ret | fail => simp [BisimRelF.refl_upToEq]
  | tau x =>
    simp only [tau_bind, observe_tau]
    apply BisimRelF.tau
    right
    exists ⟨x, f, g⟩
  | op e inp blocks k =>
    simp only [op_bind]
    apply BisimRelF.op
    · intro o
      right
      exists ⟨k o, f, g⟩
    · intros; left; rfl

instance {E} : LawfulMonad (ITree E) := LawfulMonad.mk' _
  bind_pure
  (fun _ _ => ret_bind)
  (fun _ _ _ => bind_assoc)

private def LoopCarrier (E : Eff.Spec) (β : Type _) (α : Type _) : Type _ :=
    (ITree E (ForInStep β) × (β → ITree E α)) ⊕ ITree E α

private def loopCo {E : Eff.Spec} {β : Type _} (body : β → ITree E (ForInStep β)) (α : Type _):
  LoopCarrier E β α → Eff.Step E (LoopCarrier E β) α
| .inl (m, f) => match m.observe with
  | ⟨.ret (.done v), _⟩ => IxPoly.map (fun _ => .inr) _ (f v).observe
  | ⟨.ret (.yield v), _⟩ => Eff.Step.tau (.inl (body v, f))
  | ⟨.tau, k⟩ => Eff.Step.tau (.inl (k (), f))
  | ⟨.fail, _⟩ => Eff.Step.fail
  | ⟨.op e inp, k⟩ => Eff.Step.op e inp
      (fun t i => .inr (k $ .inr ⟨t, i⟩))
      (fun o => .inl (k $ .inl o, f))
| .inr m => IxPoly.map (fun _ => .inr) _ m.observe

private theorem loopCo_copy {E β} {body : β → ITree E (ForInStep β)} {x : ITree E α} :
    corec (loopCo body) (.inr x) = x := by
  apply bisim (R := fun _ x y => x = corec (loopCo body) (.inr y))
  intro _ x y hxy
  cases hxy
  · simp only [observe_corec, loopCo, IxPoly.map_map]
    cases y.observe using Eff.Step.casesOn <;> {
       try simp; constructor <;> { intros ; apply_assumption }
    }
  · rfl

def loop {E β α} (body : β → ITree E (ForInStep β))
    (initial : β) (k : β → ITree E α) : ITree E α :=
  corec (loopCo body) (.inl (body initial, k))

theorem loop_def {E β α} {body : β → ITree E (ForInStep β)}
    {initial : β} {k : β → ITree E α} :
    loop body initial k =
      (body initial >>= fun x => match x with
        | .done v => k v
        | .yield v => tau (loop body v k)) := by
  unfold loop
  apply bisim₂_up_to_eq
    (Seed := LoopCarrier E β)
    (left := fun _ x => corec (loopCo body) x)
    (right := fun _ x => match x with
      | .inr t => t
      | .inl (m, f) => m >>= fun x => match x with
        | .done v => f v
        | .yield v => tau $ corec (loopCo body) (.inl (body v, f)))
    (seed := .inl (body initial, k))
  intro i x
  cases x with
  | inr m =>
    simp only [observe_corec, loopCo, IxPoly.map_map]
    cases m.observe using Eff.Step.casesOn with
    | ret | fail => simp [BisimRelF.refl_upToEq]
    | tau x =>
      simp only [Eff.Step.map_tau]
      apply BisimRelF.tau
      right
      exists (.inr x)
    | op e inp blocks k =>
      simp only [Eff.Step.map_op]
      apply BisimRelF.op
      · intro o
        right
        exists (.inr (k o))
      · intros
        left
        exact loopCo_copy
  | inl m =>
    rcases m with ⟨m, f⟩
    simp only
    have : m = roll (observe m) := (observe.symm_apply_apply _).symm
    rw [this]
    cases m.observe using Eff.Step.casesOn with
    | ret x =>
      simp only [roll_ret, ret_bind]
      cases x with
      | done v =>
        simp only [observe_corec, loopCo, observe_ret, Eff.Step.ret, map_map, loopCo_copy, IxPoly.map_id]
        apply BisimRelF.refl_upToEq
      | yield v =>
        simp only [observe_tau, observe_corec, loopCo, observe_ret, Eff.Step.ret, Eff.Step.map_tau]
        apply BisimRelF.tau
        left
        rfl
    | fail =>
      simp only [roll_fail, observe_corec, loopCo, observe_fail, fail_bind]
      conv => enter [3,3]; rw [Eff.Step.fail]
      simp only [Eff.Step.map_fail]
      apply BisimRelF.fail
    | tau x =>
      simp only [roll_tau, observe_corec, loopCo, observe_tau, tau_bind]
      conv => enter [3,3]; rw [Eff.Step.tau]
      simp only [Eff.Step.map_tau]
      apply BisimRelF.tau
      right
      exists (.inl (x, f))
    | op e inp blocks k =>
      simp only [roll_op, observe_corec, loopCo, observe_op, op_bind]
      conv => enter [3,3]; rw [Eff.Step.op]
      simp only [Eff.Step.map_op]
      apply BisimRelF.op
      · intro o
        right
        exists (.inl (k o, f))
      · intros
        left
        exact loopCo_copy

private theorem loopCo_bind {E β α}
    (body : β → ITree E (ForInStep β))
    (m : ITree E (ForInStep β)) (k : β → ITree E α) :
    corec (loopCo body) (.inl (m, pure)) >>= k =
      corec (loopCo body) (.inl (m, k)) := by
  symm
  apply bisim₂_up_to_eq
    (Seed := fun α => ITree E (ForInStep β) × (β → ITree E α))
    (left := fun i ⟨m, k⟩ =>
      corec (loopCo body) ((.inl (m, k)) : LoopCarrier E β i))
    (right := fun _ ⟨m, k⟩ =>
      corec (loopCo body) ((.inl (m, pure)) : LoopCarrier E β β) >>= k)
    (seed := ⟨m, k⟩)
  intro i seed
  rcases seed with ⟨m, k⟩
  have hm : m = roll (observe m) := (observe.symm_apply_apply _).symm
  rw [hm]
  cases observe m using Eff.Step.casesOn with
  | ret x =>
    cases x with
    | done v =>
      have unfold : ∀ {j : Type} (f : β → ITree E j),
          corec (loopCo body) (.inl (ret (.done v), f)) = f v := by
        intro j f
        apply observe.injective
        simp only [observe_corec, loopCo, observe_ret, Eff.Step.ret, IxPoly.map_map,
          loopCo_copy, IxPoly.map_id]
      simp only [roll_ret]
      rw [unfold k, unfold pure]
      simp only [pure, ret_bind]
      apply BisimRelF.refl_upToEq
    | yield v =>
      have unfold : ∀ {j : Type} (f : β → ITree E j),
          corec (loopCo body) (.inl (ret (.yield v), f)) =
            tau (corec (loopCo body) (.inl (body v, f))) := by
        intro j f
        apply observe.injective
        simp only [observe_corec, loopCo, observe_ret, Eff.Step.ret, Eff.Step.map_tau, observe_tau]
      simp only [roll_ret]
      rw [unfold k, unfold pure]
      simp only [tau_bind, observe_tau]
      apply BisimRelF.tau
      right
      exists ⟨body v, k⟩
  | tau next =>
    have unfold : ∀ {j : Type} (f : β → ITree E j),
        corec (loopCo body) (.inl (tau next, f)) =
          tau (corec (loopCo body) (.inl (next, f))) := by
      intro j f
      apply observe.injective
      have hco :
          loopCo body j (.inl (tau next, f)) = Eff.Step.tau (.inl (next, f)) := by
        simp only [loopCo, observe_tau, Eff.Step.tau]
      rw [observe_corec, observe_tau, hco, Eff.Step.map_tau]
    simp only [roll_tau]
    rw [unfold k, unfold pure]
    simp only [tau_bind, observe_tau]
    apply BisimRelF.tau
    right
    exists ⟨next, k⟩
  | fail =>
    have unfold : ∀ {j : Type} (f : β → ITree E j),
        corec (loopCo body) (.inl (fail, f)) = fail := by
      intro j f
      apply observe.injective
      rw [observe_corec, observe_fail]
      change IxPoly.map (fun _ y => corec (loopCo body) y) _ Eff.Step.fail = _
      simp only [Eff.Step.map_fail]
    simp only [roll_fail]
    rw [unfold k, unfold pure]
    simp only [fail_bind, observe_fail]
    apply BisimRelF.fail
  | op e inp blocks next =>
    have unfold : ∀ {j : Type} (f : β → ITree E j),
        corec (loopCo body) (.inl (op e inp blocks next, f)) =
          op e inp blocks (fun o => corec (loopCo body) (.inl (next o, f))) := by
      intro j f
      apply observe.injective
      have hco :
          loopCo body j (.inl (op e inp blocks next, f)) =
            Eff.Step.op e inp
              (fun t x => (.inr (blocks t x) : LoopCarrier E β (E.blockOutputs e t)))
              (fun o => .inl (next o, f)) := by
        simp only [loopCo, observe_op, Eff.Step.op]
      rw [observe_corec, observe_op, hco, Eff.Step.map_op]
      congr 1
      funext t x
      exact loopCo_copy
    simp only [roll_op]
    rw [unfold k, unfold pure]
    simp only [op_bind, observe_op]
    apply BisimRelF.op
    · intro o
      right
      exists ⟨next o, k⟩
    · intros
      left
      rfl

theorem loop_bind {E β α} (body : β → ITree E (ForInStep β))
    (initial : β) (k : β → ITree E α) :
    loop body initial pure >>= k = loop body initial k :=
  loopCo_bind body (body initial) k

end Freigen.ITree
