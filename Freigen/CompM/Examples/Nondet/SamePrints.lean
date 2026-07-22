import Freigen.CompM.Basic
import Freigen.CompM.Examples.Nondet.Defs
import Freigen.ITree.Basic

namespace Freigen.CompM.Examples.Nondet.SamePrints

inductive Silent {α} : Nondet α → (β : Type) → (β → Nondet α) → Prop where
| tick : (k : Unit → Nondet α) → Silent (tick >>= k) Unit k
| rand : (k : ℤ → Nondet α) → Silent (Nondet.rand >>= k) ℤ k

inductive Step {α β} (RR : α → β → Prop) (R : Nondet α → Nondet β → Prop) : Nondet α → Nondet β → Prop where
-- aligning silent steps – recursing through R because both sides progress
| silent {t1 t2 β1 β2 k1 k2} :
    Silent t1 β1 k1 → Silent t2 β2 k2 →
    (∀ x1 x2, R (k1 x1) (k2 x2)) →
    Step RR R t1 t2
-- the important cases:
-- * prints relate if they print the same thing and continuations agree
-- * rets relate if they are the same
-- * fails relate if they align
| print {z k1 k2} : R k1 k2 → Step RR R (Nondet.print z *> k1) (Nondet.print z *> k2)
| ret {k₁ k₂} : RR k₁ k₂ → Step RR R (pure k₁) (pure k₂)
| fail : Step RR R CompM.fail CompM.fail
-- skipping silent steps on one side – recursing through SamePrintsF, to avoid consuming an
-- infinite number of them (preserve termination)
| silentL : ∀ {t1 t2 β k}, Silent t1 β k → (∀ i, Step RR R (k i) t2) → Step RR R t1 t2
| silentR : ∀ {t1 t2 β k}, Silent t2 β k → (∀ i, Step RR R t1 (k i)) → Step RR R t1 t2

def SamePrintsA {α β} (RR : α → β → Prop): (Nondet α → Nondet β → Prop) →o (Nondet α → Nondet β → Prop) where
  toFun R := Step RR R
  monotone' := by
    intro _ _ _ _ _ h12
    induction h12
    · apply Step.silent <;> solve_by_elim
    · apply Step.print ; solve_by_elim
    · apply Step.ret ; solve_by_elim
    · apply Step.fail
    · apply Step.silentL <;> solve_by_elim
    · apply Step.silentR <;> solve_by_elim

end SamePrints

def SamePrints {α β} (RR : α → β → Prop) : Nondet α → Nondet β → Prop := (SamePrints.SamePrintsA RR).gfp

namespace SamePrints

protected theorem out {x : Nondet α} {y : Nondet β} {RR : α → β → Prop}
    (h : SamePrints RR x y) :
    Step RR (SamePrints RR) x y := by
  change SamePrintsA RR (SamePrints RR) x y
  have := OrderHom.isFixedPt_gfp (SamePrintsA RR (α := α))
  unfold Function.IsFixedPt at this
  unfold SamePrints
  rw [this]
  exact h

protected theorem roll {α β} {x : Nondet α} {y : Nondet β} {RR : α → β → Prop}
    (h : Step RR (SamePrints RR) x y) :
    SamePrints RR x y := by
  change SamePrintsA RR (SamePrints RR) x y at h
  have hfix := OrderHom.isFixedPt_gfp (SamePrintsA RR (α := α))
  unfold Function.IsFixedPt at hfix
  unfold SamePrints at h ⊢
  simpa only [hfix] using h

protected theorem coind {α β} (a b) {RR : α → β → Prop} (R : Nondet α → Nondet β → Prop)
    (h_stable : ∀x y, R x y → Step RR R x y)
    (h : R a b) : SamePrints RR a b := OrderHom.le_gfp (SamePrintsA RR) h_stable a b h

protected theorem coind_up_to_fix {α β} (a b) {RR : α → β → Prop} (R : Nondet α → Nondet β → Prop)
    (h_stable : ∀x y, R x y → Step RR (fun x y => SamePrints RR x y ∨ R x y) x y)
    (h : R a b) : SamePrints RR a b := by
  apply SamePrints.coind (RR := RR) (R := fun x y => SamePrints RR x y ∨ R x y)
  · intro x y hxy
    cases hxy
    · rename_i h
      apply (SamePrintsA RR).monotone (fun _ _ h => Or.inl h)
      exact h.out
    · tauto
  · tauto

theorem Silent.bind {α β : Type} {t : Nondet α} {k : β → Nondet α} {k2 : α → Nondet γ}
    (h : Silent t _ k): Silent (t >>= k2) _ (fun x => k x >>= k2) := by
  cases h <;> rw [bind_assoc] <;> constructor

protected theorem bind {α₁ α₂ β₁ β₂ : Type} {a₁ : Nondet α₁} {a₂ : Nondet α₂} {b₁ : α₁ → Nondet β₁}
    {b₂ : α₂ → Nondet β₂}
    {RRo : β₁ → β₂ → Prop} {RR : α₁ → α₂ → Prop}
    (h1 : SamePrints RR a₁ a₂) (h2 : ∀x y, RR x y → SamePrints RRo (b₁ x) (b₂ y)) :
    SamePrints RRo (a₁ >>= b₁) (a₂ >>= b₂) := by
  let R : Nondet β₁ → Nondet β₂ → Prop := fun x y =>
    ∃ x1 x2, SamePrints RR x1 x2 ∧ x = (x1 >>= b₁) ∧ y = (x2 >>= b₂)
  apply SamePrints.coind_up_to_fix (R := R)
  · rintro _ _ ⟨x, y, hxy, rfl, rfl⟩
    have := hxy.out
    clear hxy
    induction this with
    | silent =>
      apply Step.silent
      · apply Silent.bind; assumption
      · apply Silent.bind; assumption
      grind
    | print =>
      simp only [seqRight_eq_bind, bind_assoc]
      apply Step.print
      grind
    | ret =>
      simp only [pure_bind]
      apply (SamePrintsA _).monotone (fun _ _ h => Or.inl h)
      apply SamePrints.out
      solve_by_elim
    | fail =>
      simp only [CompM.fail_bind]
      apply Step.fail
    | silentL =>
      apply Step.silentL
      · apply Silent.bind; assumption
      assumption
    | silentR =>
      apply Step.silentR
      · apply Silent.bind; assumption
      assumption
  · exact ⟨a₁, a₂, h1, rfl, rfl⟩

protected theorem rand {β₁ β₂ : Type} {b₁ : ℤ → Nondet β₁} {b₂ : ℤ → Nondet β₂} {RR : β₁ → β₂ → Prop}
    (h2 : ∀x y, SamePrints RR (b₁ x) (b₂ y)):
  SamePrints RR (Nondet.rand >>= b₁) (Nondet.rand >>= b₂) := by
  apply SamePrints.roll
  apply Step.silent
  · apply Silent.rand
  · apply Silent.rand
  assumption

protected theorem print {z : ℤ}:
  SamePrints Eq (Nondet.print z) (Nondet.print z) := by
  apply SamePrints.roll
  have : pure (f := Nondet) = fun _ => pure () := by simp
  conv =>
    congr
    · skip
    · skip
    · rw [←bind_pure (x := Nondet.print z), this]
    · rw [←bind_pure (x := Nondet.print z), this]
  apply Step.print
  apply SamePrints.roll
  apply Step.ret
  rfl

protected theorem ret {α β : Type} {x : α} {y : β} {R : α → β → Prop} (h : R x y):
  SamePrints R (pure x) (pure y) := by
  apply SamePrints.roll
  apply Step.ret h

def ForInStep.Rel {α β} (RR : α → β → Prop) (I : α → β → Prop):
    ForInStep α → ForInStep β → Prop
  | .done x, .done y => RR x y
  | .yield x, .yield y => I x y
  | _, _ => False

def LoopPair {α β}
  (b₁ : α → Nondet (ForInStep α))
  (b₂ : β → Nondet (ForInStep β))
  (I : α → β → Prop) : Nondet α → Nondet β → Prop :=
  fun x y =>
    ∃ s₁ s₂,
      I s₁ s₂ ∧
      x = CompM.loop b₁ s₁ ∧
      y = CompM.loop b₂ s₂

inductive Steps {α β} (RR : α → β → Prop) (R : Nondet α → Nondet β → Prop) : Nondet α → Nondet β → Prop where
| done {x y} : SamePrints RR x y → Steps RR R x y
| step {x y} : Step RR (Steps RR R) x y → Steps RR R x y
| recur {x y} : R x y → Steps RR R x y

theorem Step.strengthen {α β} {RR : α → β → Prop} {R R' : Nondet α → Nondet β → Prop}
    (h : R ≤ R') {x y} (hstep : Step RR R x y):
    Step RR R' x y := by
  apply (SamePrintsA RR).monotone h
  exact hstep

protected theorem loop_coind {α₁ α₂}
    {b₁ : α₁ → Nondet (ForInStep α₁)} {b₂ : α₂ → Nondet (ForInStep α₂)}
    {i₁ : α₁} {i₂ : α₂} {RR : α₁ → α₂ → Prop}
    (I : α₁ → α₂ → Prop)
    (hinit : I i₁ i₂)
    (hstep : ∀ s₁ s₂, I s₁ s₂ →
      Step RR (Steps RR (LoopPair b₁ b₂ I))
      (loop b₁ s₁) (loop b₂ s₂)):
    SamePrints RR (loop b₁ i₁) (loop b₂ i₂) := by
  apply SamePrints.coind (R := Steps RR (LoopPair b₁ b₂ I))
  · rintro x y hxy
    cases hxy with
    | done h =>
      have := h.out
      apply Step.strengthen (hstep := this)
      intro x y hxy
      apply Steps.done hxy
    | step h => assumption
    | recur h =>
      rcases h with ⟨s₁, s₂, hI, rfl, rfl⟩
      apply hstep _ _ hI
  · apply Steps.recur
    exists i₁, i₂

end Freigen.CompM.Examples.Nondet.SamePrints
