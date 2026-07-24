import Freigen.IxPoly.Basic
import Freigen.Eff

namespace Freigen

def ITree (E : Type u) [Eff.Spec E] (α : Type _): Type _ := (Eff.Step E).M α
namespace ITree

open IxPoly

variable {E : Type u} [eS : Eff.Spec E]

def corec {A : Type _ → Type _} (f : (i : Type _) → A i → Eff.Step E A i): {i : Type _} → A i → ITree E i :=
  IxPoly.M.corec f

def observe {α} : ITree E α ≃ Eff.Step E (ITree E) α := IxPoly.M.observe

def roll {α} : Eff.Step E (ITree E) α → ITree E α := IxPoly.M.observe.symm

theorem observe_roll {α} (x : Eff.Step E (ITree E) α): observe (roll x) = x := observe.apply_symm_apply _

theorem roll_observe {α} (x : ITree E α): roll (observe x) = x := observe.symm_apply_apply _

theorem observe_corec {A : Type _ → Type _} (f : (i : Type _) → A i → Eff.Step E A i) {i : Type _} (a : A i):
    observe (corec f a) = IxPoly.map (fun _ y => corec f y) i (f i a) := IxPoly.M.observe_corec

def ret {α} (x : α) : ITree E α := roll $ Eff.Step.ret x
def op {α} (e : E) (inp : eS.input e)
    (blocks : (t : eS.blockTag e) → eS.blockInputs e t → ITree E (eS.blockOutputs e t))
    (k : (o : eS.output e) → ITree E α) : ITree E α :=
  roll $ Eff.Step.op e inp blocks k

theorem roll_ret {α} (x : α) : roll (E:=E) (Eff.Step.ret x) = ret x := rfl

theorem roll_op {α} (e : E) (inp : eS.input e)
    (blocks : (t : eS.blockTag e) → eS.blockInputs e t → ITree E (eS.blockOutputs e t))
    (k : (o : eS.output e) → ITree E α) :
    roll (E:=E) (Eff.Step.op e inp blocks k) = op e inp blocks k := rfl

@[simp]
theorem observe_ret {α} (x : α) : observe (ret x (E:=E)) = Eff.Step.ret x := rfl

@[simp]
theorem observe_op {α} (e : E) (inp : eS.input e)
    (blocks : (t : eS.blockTag e) → eS.blockInputs e t → ITree E (eS.blockOutputs e t))
    (k : (o : eS.output e) → ITree E α) :
    observe (op e inp blocks k (E:=E)) = Eff.Step.op e inp blocks k := rfl

protected def casesOn { motive : (α : Type _) → ITree E α → Sort* } {α} (x : ITree E α)
    (ret : ∀ {α} x, motive α (ret x))
    (op : ∀ {α} e inp blocks k, motive α (op e inp blocks k)):
    motive α x := by
  have : x = roll (observe x) := (observe.symm_apply_apply _).symm
  rw [this]
  cases observe x using Eff.Step.casesOn <;> apply_assumption

inductive BisimRelF
    (R : (α : Type _) → ITree E α → ITree E α → Prop):
    (α : Type _) → Eff.Step E (ITree E) α → Eff.Step E (ITree E) α → Prop where
| ret {α} (x : α): BisimRelF R α (Eff.Step.ret x) (Eff.Step.ret x)
| op {α} (e : E) (inp : eS.input e)
    (k1 k2 : (o : eS.output e) → ITree E α)
    (blocks1 blocks2 : (t : eS.blockTag e) → eS.blockInputs e t → ITree E (eS.blockOutputs e t))
    (h1 : ∀ o, R _ (k1 o) (k2 o))
    (h2 : ∀ t i, R _ (blocks1 t i) (blocks2 t i)):
  BisimRelF R α (Eff.Step.op e inp blocks1 k1) (Eff.Step.op e inp blocks2 k2)

theorem BisimRelF.toLiftR {R : (α : Type _) → ITree E α → ITree E α → Prop} : BisimRelF R ≤ IxPoly.M.LiftR (Eff.Step E) R := by
  intro α x y hxy
  cases hxy <;> constructor
  case ret => intro a; cases a
  -- case tau => intro _; assumption
  case op =>
    intro a
    cases a <;> apply_assumption

theorem BisimRelF.refl {R}
    (hrefl : ∀ {α} (x : ITree E α), R α x x)
    {α} (x : Eff.Step E (ITree E) α): BisimRelF R α x x := by
  cases x using Eff.Step.casesOn <;> constructor <;> intros <;> apply_assumption

theorem BisimRelF.refl_upToEq {R}
    {α} (x : Eff.Step E (ITree E) α): BisimRelF (M.IxRel.upToEq R) α x x := by
  apply BisimRelF.refl
  intros
  apply Or.inl
  rfl

theorem bisim {α} (R : (α : Type _) → ITree E α → ITree E α → Prop)
    (step : ∀{α x y}, R α x y → BisimRelF R α (observe x) (observe y))
    {x y : ITree E α} (hxy : R _ x y) : x = y := by
  apply IxPoly.M.Bisim.coind (R := R)
  · intro α x y hxy
    apply BisimRelF.toLiftR
    apply step hxy
  · assumption

theorem bisim_up_to_eq {α} (R : (α : Type _) → ITree E α → ITree E α → Prop)
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

theorem bisim₂ {α} {Seed : Type _ → Type _}
    (left right : (i : Type _) → Seed i → ITree E i)
    (step : ∀ {i} (s : Seed i), BisimRelF (M.IxRel.span Seed left right) i (observe (left i s)) (observe (right i s)))
    (seed : Seed α): left α seed = right α seed := by
  apply bisim (R := M.IxRel.span Seed left right)
  intro i x y hxy
  rcases hxy with ⟨s, rfl, rfl⟩
  apply step
  exists seed

theorem bisim₂_up_to_eq {α} {Seed : Type _ → Type _}
    (left right : (i : Type _) → Seed i → ITree E i)
    (step : ∀ {i} (s : Seed i), BisimRelF (M.IxRel.upToEq (M.IxRel.span Seed left right)) i (observe (left i s)) (observe (right i s)))
    (seed : Seed α): left α seed = right α seed := by
  apply bisim_up_to_eq (R := M.IxRel.span Seed left right)
  intro i x y hxy
  rcases hxy with ⟨s, rfl, rfl⟩
  apply step
  exists seed

def BindCarrier α R := (ITree E α × (α → ITree E R)) ⊕ ITree E R
def bindCo {α : Type} (R : Type) :
    BindCarrier (E:=E) α R → Eff.Step E (BindCarrier (E:=E) α) R
| .inl (e, f) => match e.observe with
  | ⟨.ret x, _⟩ => IxPoly.map (fun _ => .inr) _ (f x).observe
  | ⟨.op e x, cont⟩ => ⟨.op e x, fun
    | .inl o => .inl (cont $ .inl o, f)
    | .inr b => .inr (cont $ .inr b)
  ⟩
| .inr e => IxPoly.map (fun _ => .inr) _ e.observe

theorem bindCo_copy {α β : Type} {x : ITree E β} :
    corec (bindCo (α := α)) (.inr x) = x := by
  apply bisim (R := fun _ x y => x = corec (bindCo (α := α)) (.inr y))
  intro _ x y hxy
  cases hxy
  · simp only [observe_corec, bindCo, IxPoly.map_map]
    cases y.observe using Eff.Step.casesOn <;> {
       try simp; constructor <;> { intros ; apply_assumption }
    }
  · rfl

instance : Monad (ITree E) where
  pure := fun x => ret x
  bind {α β} (a : ITree E α) (f : α → ITree E β) := corec bindCo (.inl (a, f))

@[simp]
theorem ret_bind {α β : Type} {x : α}
    {f : α → ITree E β} : ret x >>= f = f x := by
  apply observe.injective
  simp only [Bind.bind, observe_corec, bindCo, ret,
    observe_roll, IxPoly.map_map, Eff.Step.ret, bindCo_copy, IxPoly.map_id]

@[simp]
theorem op_bind {α β : Type} {e : E} {inp : eS.input e}
    {blocks : (t : eS.blockTag e) → eS.blockInputs e t → ITree E (eS.blockOutputs e t)}
    {k : (o : eS.output e) → ITree E α}
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

@[simp]
theorem hasOp_bind
    {F : Type u} {α β : Type}
    [Eff.Spec F] [Eff.Has F E]
    {e : F} {inp : Eff.Spec.input e}
    {blocks :
      (t : Eff.Spec.blockTag e) →
      Eff.Spec.blockInputs e t →
      ITree E (Eff.Spec.blockOutputs e t)}
    {k : Eff.Spec.output e → ITree E α}
    {f : α → ITree E β} :
    (roll (Eff.Step.Has.op e inp blocks k) >>= f) =
      roll
        (Eff.Step.Has.op e inp blocks
          (fun o => k o >>= f)) := by
  simp only [Eff.Step.Has.op, roll_op, op_bind]

inductive BindPureRel:
    (α : Type) → ITree E α → ITree E α → Prop where
| root {α} (m : ITree E α) : BindPureRel α (m >>= pure) m
| refl {α} (m : ITree E α) : BindPureRel α m m

theorem bind_pure {α : Type} (a : ITree E α) :
    a >>= pure = a := by
  apply bisim₂_up_to_eq (Seed := ITree E) (left := fun _ x => x >>= pure) (right := fun _ x => x)
  intro _ m
  cases m using ITree.casesOn with
  | ret => simp [pure, BisimRelF.refl_upToEq]
  | op e inp blocks k =>
    simp only [op_bind]
    apply BisimRelF.op
    · intro
      right
      apply Exists.intro
      apply And.intro <;> rfl
    · intros; left; rfl

theorem bind_assoc {α β γ : Type}
    {a : ITree E α} {f : α → ITree E β} {g : β → ITree E γ}:
    (a >>= f) >>= g = a >>= fun x => f x >>= g := by
  apply bisim₂_up_to_eq (Seed := fun γ => ITree E α × (α → ITree E β) × (β → ITree E γ))
    (left := fun _ ⟨x, f, g⟩ => (x >>= f) >>= g)
    (right := fun _ ⟨x, f, g⟩ => x >>= fun y => f y >>= g)
    (seed := ⟨a, f, g⟩)
  intro _ ⟨x, f, g⟩
  simp only
  cases x using ITree.casesOn with
  | ret => simp [BisimRelF.refl_upToEq]
  | op e inp blocks k =>
    simp only [op_bind]
    apply BisimRelF.op
    · intro o
      right
      exists ⟨k o, f, g⟩
    · intros; left; rfl

instance : LawfulMonad (ITree E) := LawfulMonad.mk' _
  bind_pure
  (fun _ _ => ret_bind)
  (fun _ _ _ => bind_assoc)

section Loops

variable [Eff.Has Eff.Tau E]

def tau {α} (x : ITree E α) : ITree E α := roll $ Eff.Step.tau x

@[simp]
theorem observe_tau {α} (x : ITree E α) : observe (tau x) = Eff.Step.tau x := rfl

@[simp]
theorem tau_bind {α β : Type} {x : ITree E α}
    {f : α → ITree E β} : tau x >>= f = tau (x >>= f) := by
  apply observe.injective
  simp only [tau, Eff.Step.tau, hasOp_bind]

private def LoopCarrier (E : Type u) [Eff.Spec E] (α β γ : Type) : Type _ :=
    (ITree E (α ⊕ β) × (β → ITree E γ)) ⊕ ITree E γ

private def loopCo {α β : Type}
    (body : α → ITree E (α ⊕ β)) (γ : Type):
  LoopCarrier E α β γ → Eff.Step E (LoopCarrier E α β) γ
| .inl (m, f) => match m.observe with
  | ⟨.ret (.inr v), _⟩ => IxPoly.map (fun _ => .inr) _ (f v).observe
  | ⟨.ret (.inl v), _⟩ => Eff.Step.tau (.inl (body v, f))
  | ⟨.op e inp, k⟩ => Eff.Step.op e inp
      (fun t i => .inr (k $ .inr ⟨t, i⟩))
      (fun o => .inl (k $ .inl o, f))
| .inr m => IxPoly.map (fun _ => .inr) _ m.observe

private theorem loopCo_copy {α β γ : Type}
    {body : α → ITree E (α ⊕ β)} {x : ITree E γ} :
    corec (loopCo body) (.inr x) = x := by
  apply bisim (R := fun _ x y => x = corec (loopCo body) (.inr y))
  intro _ x y hxy
  cases hxy
  · simp only [observe_corec, loopCo, IxPoly.map_map]
    cases y.observe using Eff.Step.casesOn <;> {
       try simp; constructor <;> { intros ; apply_assumption }
    }
  · rfl

def loop {α β γ : Type} (body : α → ITree E (α ⊕ β))
    (initial : α) (k : β → ITree E γ) : ITree E γ :=
  corec (loopCo body) (.inl (body initial, k))

theorem loop_def {α β γ : Type}
    {body : α → ITree E (α ⊕ β)}
    {initial : α} {k : β → ITree E γ} :
    loop body initial k =
      (body initial >>= fun x => match x with
        | .inr v => k v
        | .inl v => tau (loop body v k)) := by
  unfold loop
  apply bisim₂_up_to_eq
    (Seed := LoopCarrier E α β)
    (left := fun _ x => corec (loopCo body) x)
    (right := fun _ x => match x with
      | .inr t => t
      | .inl (m, f) => m >>= fun x => match x with
        | .inr v => f v
        | .inl v => tau $ corec (loopCo body) (.inl (body v, f)))
    (seed := .inl (body initial, k))
  intro i x
  cases x with
  | inr m =>
    simp only [observe_corec, loopCo, IxPoly.map_map]
    cases m.observe using Eff.Step.casesOn with
    | ret => simp [BisimRelF.refl_upToEq]
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
      | inr v =>
        simp only [observe_corec, loopCo, observe_ret, Eff.Step.ret, map_map, loopCo_copy, IxPoly.map_id]
        apply BisimRelF.refl_upToEq
      | inl v =>
        simp only [observe_tau, observe_corec, loopCo, observe_ret, Eff.Step.ret, Eff.Step.map_tau]
        apply BisimRelF.op
        · intro
          left
          rfl
        · intro t
          exact (nomatch Eff.Step.Has.lowerBlockTag t)
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

private theorem loopCo_bind {α β γ : Type}
    (body : α → ITree E (α ⊕ β))
    (m : ITree E (α ⊕ β)) (k : β → ITree E γ) :
    corec (loopCo body) (.inl (m, pure)) >>= k =
      corec (loopCo body) (.inl (m, k)) := by
  symm
  apply bisim₂_up_to_eq
    (Seed := fun γ => ITree E (α ⊕ β) × (β → ITree E γ))
    (left := fun i ⟨m, k⟩ =>
      corec (loopCo body) ((.inl (m, k)) : LoopCarrier (E:=E) α β i))
    (right := fun _ ⟨m, k⟩ =>
      corec (loopCo body) ((.inl (m, pure)) : LoopCarrier (E:=E) α β β) >>= k)
    (seed := ⟨m, k⟩)
  intro i seed
  rcases seed with ⟨m, k⟩
  have hm : m = roll (observe m) := (observe.symm_apply_apply _).symm
  rw [hm]
  cases observe m using Eff.Step.casesOn with
  | ret x =>
    cases x with
    | inr v =>
      have unfold : ∀ {j : Type} (f : β → ITree E j),
          corec (loopCo body) (.inl (ret (.inr v), f)) = f v := by
        intro j f
        apply observe.injective
        simp only [observe_corec, loopCo, observe_ret, Eff.Step.ret, IxPoly.map_map,
          loopCo_copy, IxPoly.map_id]
      simp only [roll_ret]
      rw [unfold k, unfold pure]
      simp only [pure, ret_bind]
      apply BisimRelF.refl_upToEq
    | inl v =>
      have unfold : ∀ {j : Type} (f : β → ITree E j),
          corec (loopCo body) (.inl (ret (.inl v), f)) =
            tau (corec (loopCo body) (.inl (body v, f))) := by
        intro j f
        apply observe.injective
        simp only [observe_corec, loopCo, observe_ret, Eff.Step.ret, Eff.Step.map_tau, observe_tau]
      simp only [roll_ret]
      rw [unfold k, unfold pure]
      simp only [tau_bind, observe_tau]
      apply BisimRelF.op
      · intro
        right
        exists ⟨body v, k⟩
      · intro t
        exact (nomatch Eff.Step.Has.lowerBlockTag t)
  | op e inp blocks next =>
    have unfold : ∀ {j : Type} (f : β → ITree E j),
        corec (loopCo body) (.inl (op e inp blocks next, f)) =
          op e inp blocks (fun o => corec (loopCo body) (.inl (next o, f))) := by
      intro j f
      apply observe.injective
      have hco :
          loopCo body j (.inl (op e inp blocks next, f)) =
            Eff.Step.op e inp
              (fun t x => (.inr (blocks t x) : LoopCarrier (E:=E) α β (eS.blockOutputs e t)))
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

theorem loop_bind {α β γ : Type}
    (body : α → ITree E (α ⊕ β))
    (initial : α) (k : β → ITree E γ) :
    loop body initial pure >>= k = loop body initial k :=
  loopCo_bind body (body initial) k

end Loops

end Freigen.ITree
