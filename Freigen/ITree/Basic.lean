import Freigen.IxPoly.Basic

namespace Freigen.ITree

open Freigen.IxPoly

structure EffSpec where
  tag : Type u
  input : tag → Type v
  output : tag → Type v
  blockTag : tag → Type u
  blockInputs : (t : tag) → blockTag t → Type v
  blockOutputs : (t : tag) → blockTag t → Type v

inductive NodeTag (E : EffSpec) : Type _ → Type _ where
| ret {R} : R → NodeTag E R
| tau {R} : NodeTag E R
| fail {R} : NodeTag E R
| op {R} (e : E.tag) : E.input e → NodeTag E R

def NodeTag.fields {i} {E : EffSpec}: NodeTag E i → Type _
| ret _ => PEmpty
| tau => PUnit
| fail => PEmpty
| op e _ => E.output e ⊕ ((t : E.blockTag e) × E.blockInputs e t)

def NodeTag.elem {E : EffSpec} {α : Type _} : (t : NodeTag E α) → (p : t.fields) → Type _
| ret _, x => nomatch x
| fail, x => nomatch x
| tau, () => α
| op _ _, Sum.inl _ => α
| op e _, Sum.inr ⟨o, _⟩ => E.blockOutputs e o

def Step (E : EffSpec) : Endo (Type _) where
  Tag := fun α => NodeTag E α
  Field := fun _=> NodeTag.fields
  Elem := fun _ => NodeTag.elem

namespace Step

def ret {E α Y} (x : α) : Step E Y α := ⟨.ret x, fun a => PEmpty.elim a⟩
def tau {E α Y} (x : Y α) : Step E Y α := ⟨.tau, fun () => x⟩
def fail {E α Y} : Step E Y α := ⟨.fail, fun a => PEmpty.elim a⟩
def op {E α Y} (e : E.tag) (inp : E.input e)
    (blocks : (t : E.blockTag e) → E.blockInputs e t → Y (E.blockOutputs e t))
    (k : (o : E.output e) → Y α) : Step E Y α :=
  ⟨.op e inp, fun
    | Sum.inl o => k o
    | Sum.inr ⟨t, i⟩ => blocks t i
  ⟩

protected def casesOn {E Y} { motive : (α : Type _) → Step E Y α → Sort* } {α} (x : Step E Y α)
    (ret : ∀ {α} x, motive α (ret x))
    (tau : ∀ {α} x, motive α (tau x))
    (fail : ∀ {α}, motive α fail)
    (op : ∀ {α} e inp blocks k, motive α (op e inp blocks k)):
    motive α x := by
  rcases x with ⟨tag, fields⟩
  cases tag with
  | ret a =>
    convert ret a
    simp only [Step.ret]
    congr 2
    ext a; cases a
  | tau =>
    convert tau (fields ())
    · rfl
    · simp only [Step.tau]
      congr
  | fail =>
    convert fail
    simp only [Step.fail]
    congr 2
    ext a; cases a
  | op e inp =>
    convert op e inp (fun t i => fields (.inr ⟨t, i⟩)) (fun o => fields (.inl o))
    simp only [Step.op]
    congr 2
    ext a; cases a <;> rfl

@[simp]
theorem map_ret {E} {Y Z : Type _ → Type _} {f : (α : Type _) → Y α → Z α} {α : Type _} {x : α}:
    IxPoly.map (F := Step E) f α (Step.ret x) = Step.ret x := by
  simp only [map, ret]
  congr 1
  ext a; cases a

@[simp]
theorem map_tau {E} {Y Z : Type _ → Type _} {f : (α : Type _) → Y α → Z α} {α : Type _} {x : Y α}:
    IxPoly.map (F := Step E) f α (Step.tau x) = Step.tau (f α x) := by
  simp only [map, tau]
  congr 1

@[simp]
theorem map_fail {E} {Y Z : Type _ → Type _} {f : (α : Type _) → Y α → Z α} {α : Type _}:
    IxPoly.map (F := Step E) f α (Step.fail) = Step.fail := by
  simp only [map, fail]
  congr 1
  ext a; cases a

@[simp]
theorem map_op {E} {Y Z : Type _ → Type _} {f : (α : Type _) → Y α → Z α} {α : Type _}
    {e : E.tag} {inp : E.input e}
    {blocks : (t : E.blockTag e) → E.blockInputs e t → Y (E.blockOutputs e t)}
    {k : (o : E.output e) → Y α}:
    IxPoly.map (F := Step E) f α (Step.op e inp blocks k) =
      Step.op e inp (fun t i => f _ (blocks t i)) (fun o => f _ (k o)) := by
  simp only [map, op]
  congr 1
  ext a; cases a <;> rfl

end Step

end ITree

def ITree (E : ITree.EffSpec) (α : Type _): Type _ := (ITree.Step E).M α

namespace ITree

open IxPoly

def corec {E} {A : Type _ → Type _} (f : (i : Type _) → A i → Step E A i): {i : Type _} → A i → ITree E i :=
  IxPoly.M.corec f

def observe {E α} : ITree E α ≃ Step E (ITree E) α := IxPoly.M.observe

def roll {E α} : Step E (ITree E) α → ITree E α := IxPoly.M.observe.symm

theorem observe_roll {E α} (x : Step E (ITree E) α): observe (roll x) = x := observe.apply_symm_apply _

theorem roll_observe {E α} (x : ITree E α): roll (observe x) = x := observe.symm_apply_apply _

theorem observe_corec {E} {A : Type _ → Type _} (f : (i : Type _) → A i → Step E A i) {i : Type _} (a : A i):
    observe (corec f a) = IxPoly.map (fun _ y => corec f y) i (f i a) := IxPoly.M.observe_corec

def ret {E α} (x : α) : ITree E α := roll $ Step.ret x
def tau {E α} (x : ITree E α) : ITree E α := roll $ Step.tau x
def fail {E α} : ITree E α := roll $ Step.fail
def op {E α} (e : E.tag) (inp : E.input e)
    (blocks : (t : E.blockTag e) → E.blockInputs e t → ITree E (E.blockOutputs e t))
    (k : (o : E.output e) → ITree E α) : ITree E α :=
  roll $ Step.op e inp blocks k

@[simp]
theorem observe_tau {E α} (x : ITree E α): observe (tau x) = Step.tau x := by
  simp only [tau, observe_roll, Step.tau]

protected def casesOn {E} { motive : (α : Type _) → ITree E α → Sort* } {α} (x : ITree E α)
    (ret : ∀ {α} x, motive α (ret x))
    (tau : ∀ {α} x, motive α (tau x))
    (fail : ∀ {α}, motive α fail)
    (op : ∀ {α} e inp blocks k, motive α (op e inp blocks k)):
    motive α x := by
  have : x = roll (observe x) := (observe.symm_apply_apply _).symm
  rw [this]
  cases observe x using Step.casesOn <;> apply_assumption

inductive BisimRelF {E}
    (R : (α : Type _) → ITree E α → ITree E α → Prop):
    (α : Type _) → Step E (ITree E) α → Step E (ITree E) α → Prop where
| ret {α} (x : α): BisimRelF R α (Step.ret x) (Step.ret x)
| tau {α} (x y : ITree E α) (hr : R _ x y) : BisimRelF R α (Step.tau x) (Step.tau y)
| fail {α} : BisimRelF R α Step.fail Step.fail
| op {α} (e : E.tag) (inp : E.input e)
    (k1 k2 : (o : E.output e) → ITree E α)
    (blocks1 blocks2 : (t : E.blockTag e) → E.blockInputs e t → ITree E (E.blockOutputs e t))
    (h1 : ∀ o, R _ (k1 o) (k2 o))
    (h2 : ∀ t i, R _ (blocks1 t i) (blocks2 t i)):
  BisimRelF R α (Step.op e inp blocks1 k1) (Step.op e inp blocks2 k2)

theorem BisimRelF.toLiftR {E} {R : (α : Type _) → ITree E α → ITree E α → Prop} : BisimRelF R ≤ IxPoly.M.LiftR (Step E) R := by
  intro α x y hxy
  cases hxy <;> constructor
  case ret | fail => intro a; cases a
  case tau => intro _; assumption
  case op =>
    intro a
    cases a <;> apply_assumption

theorem BisimRelF.refl {E R}
    (hrefl : ∀ {α} (x : ITree E α), R α x x)
    {α} (x : Step E (ITree E) α): BisimRelF R α x x := by
  cases x using Step.casesOn <;> constructor <;> intros <;> apply_assumption

theorem BisimRelF.refl_upToEq {E R}
    {α} (x : Step E (ITree E) α): BisimRelF (M.IxRel.upToEq R) α x x := by
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
def bindCo {E α} R : BindCarrier E α R → Step E (BindCarrier E α) R
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
    cases y.observe using Step.casesOn <;> {
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
    observe_roll, IxPoly.map_map, Step.ret, bindCo_copy, IxPoly.map_id]

@[simp]
theorem tau_bind {E β} {α} {x : ITree E α} {f : α → ITree E β} : tau x >>= f = tau (x >>= f) := by
  apply observe.injective
  simp only [Bind.bind, observe_corec, bindCo, tau, observe_roll, Step.tau, IxPoly.map]
  congr

@[simp]
theorem fail_bind {E β} {α} {f : α → ITree E β} : fail >>= f = fail := by
  apply observe.injective
  simp only [Bind.bind, observe_corec, bindCo, fail, observe_roll, Step.fail, IxPoly.map]
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
  simp only [Step.op]
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



end Freigen.ITree
