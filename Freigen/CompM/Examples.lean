import Freigen.CompM.Basic
import Freigen.IxPoly.Examples.Seq
import Freigen.ITree.Basic

namespace Freigen.CompM.Example

inductive NondetEff : Type
| rand
| print

def NondetSpec : ITree.EffSpec where
  tag := NondetEff
  input
    | .rand => Unit
    | .print => ℤ
  output
    | .rand => ℤ
    | .print => Unit
  blockTag := fun _ => Empty
  blockInputs := nofun
  blockOutputs := nofun

abbrev Nondet α := CompM NondetSpec α

def Nondet.rand : Nondet ℤ := CompM.op (E := NondetSpec) NondetEff.rand () nofun
def Nondet.print (z : ℤ) : Nondet Unit := CompM.op (E := NondetSpec) NondetEff.print z nofun

def approxWith {α} (entropy : ℕ → ℤ) (t : Nondet α) (n: Nat): List ℤ :=
  go (entropy, 0) n ((t.run pure).approx n) where
  go : (ℕ → ℤ) × ℕ → (n : Nat) → IxPoly.M.Approx (ITree.Step NondetSpec) n α → List ℤ := fun entropy n approx => match n, approx with
   | 0, IxPoly.M.Approx.zero _ => []
   | n+1, IxPoly.M.Approx._succ _ _ p k => match p with
     | .ret _ => []
     | .tau => go entropy n (k ())
     | .op NondetEff.rand () => go (entropy.1, entropy.2 + 1) n (k $ .inl (entropy.1 entropy.2))
     | .op NondetEff.print z => z :: go entropy n (k $ .inl ())
     | .fail => []

def scaryLoop : Nondet Unit := do
  while true do
    let x ← Nondet.rand
    Nondet.print (x*x)

def scaryLoopDet : Nondet Unit := do
  while true do
    let x ← Nondet.rand
    Nondet.print (x - x)

#eval approxWith Int.ofNat scaryLoop 1000
example : approxWith Int.ofNat scaryLoop 20 = [0, 1, 4, 9, 16, 25, 36] := by rfl
example : approxWith Int.ofNat scaryLoopDet 20 = [0, 0, 0, 0, 0, 0, 0] := by rfl

inductive Silent {α} : Nondet α → (β : Type) → (β → Nondet α) → Prop where
| tick : (k : Unit → Nondet α) → Silent (tick >>= k) Unit k
| rand : (k : ℤ → Nondet α) → Silent (Nondet.rand >>= k) ℤ k

inductive SamePrintsF {α} (R : Nondet α → Nondet α → Prop) : Nondet α → Nondet α → Prop where
-- aligning silent steps – recursing through R because both sides progress
| silent {t1 t2 β1 β2 k1 k2} :
    Silent t1 β1 k1 → Silent t2 β2 k2 →
    (∀ x1 x2, R (k1 x1) (k2 x2)) →
    SamePrintsF R t1 t2
-- the important cases:
-- * prints relate if they print the same thing and continuations agree
-- * rets relate if they are the same
-- * fails relate if they align
| print {z k1 k2} : R k1 k2 → SamePrintsF R (Nondet.print z >>= fun _ => k1) (Nondet.print z >>= fun _ => k2)
| ret {k} : SamePrintsF R (pure k) (pure k)
| fail : SamePrintsF R CompM.fail CompM.fail
-- skipping silent steps on one side – recursing through SamePrintsF, to avoid consuming an
-- infinite number of them (preserve termination)
| silentL : ∀ {t1 t2 β k}, Silent t1 β k → (∀ i, SamePrintsF R (k i) t2) → SamePrintsF R t1 t2
| silentR : ∀ {t1 t2 β k}, Silent t2 β k → (∀ i, SamePrintsF R t1 (k i)) → SamePrintsF R t1 t2

def SamePrintsA {α}: (Nondet α → Nondet α → Prop) →o (Nondet α → Nondet α → Prop) where
  toFun R := SamePrintsF R
  monotone' := by
    intro _ _ _ _ _ h12
    induction h12
    · apply SamePrintsF.silent <;> solve_by_elim
    · apply SamePrintsF.print ; solve_by_elim
    · apply SamePrintsF.ret
    · apply SamePrintsF.fail
    · apply SamePrintsF.silentL <;> solve_by_elim
    · apply SamePrintsF.silentR <;> solve_by_elim


def SamePrints {α} : Nondet α → Nondet α → Prop := SamePrintsA.gfp

theorem SamePrints.out {x y : Nondet α}
    (h : SamePrints x y) :
    SamePrintsF SamePrints x y := by
  change SamePrintsA SamePrints x y
  have := OrderHom.isFixedPt_gfp (SamePrintsA (α := α))
  unfold Function.IsFixedPt at this
  unfold SamePrints
  rw [this]
  exact h

theorem SamePrints.roll {α} {x y : Nondet α}
    (h : SamePrintsF SamePrints x y) :
    SamePrints x y := by
  change SamePrintsA SamePrints x y at h
  have hfix := OrderHom.isFixedPt_gfp (SamePrintsA (α := α))
  unfold Function.IsFixedPt at hfix
  unfold SamePrints at h ⊢
  simpa only [hfix] using h

theorem SamePrints.coind {α} (a b) (R : Nondet α → Nondet α → Prop)
    (h_stable : ∀x y, R x y → SamePrintsF R x y)
    (h : R a b) : SamePrints a b := OrderHom.le_gfp SamePrintsA h_stable a b h

theorem SamePrints.coind_up_to_fix {α} (a b) (R : Nondet α → Nondet α → Prop)
    (h_stable : ∀x y, R x y → SamePrintsF (fun x y => SamePrints x y ∨ R x y) x y)
    (h : R a b) : SamePrints a b := by
  apply SamePrints.coind (R := fun x y => SamePrints x y ∨ R x y)
  · intro x y hxy
    cases hxy
    · rename_i h
      apply SamePrintsA.monotone (fun _ _ h => Or.inl h)
      exact h.out
    · tauto
  · tauto

theorem Silent.bind {α β : Type} {t : Nondet α} {k : β → Nondet α} {k2 : α → Nondet γ}
    (h : Silent t _ k): Silent (t >>= k2) _ (fun x => k x >>= k2) := by
  cases h <;> rw [bind_assoc] <;> constructor

theorem SamePrints.bind {α β : Type} {a1 a2 : Nondet α} {b1 b2 : α → Nondet β}
    (h1 : SamePrints a1 a2) (h2 : ∀x, SamePrints (b1 x) (b2 x)) :
    SamePrints (a1 >>= b1) (a2 >>= b2) := by
  let R : Nondet β → Nondet β → Prop := fun x y =>
    ∃ x1 x2, SamePrints x1 x2 ∧ x = (x1 >>= b1) ∧ y = (x2 >>= b2)
  apply SamePrints.coind_up_to_fix (R := R)
  · rintro _ _ ⟨x, y, hxy, rfl, rfl⟩
    have := hxy.out
    clear hxy
    induction this with
    | silent =>
      apply SamePrintsF.silent
      · apply Silent.bind; assumption
      · apply Silent.bind; assumption
      grind
    | print =>
      simp only [bind_assoc]
      apply SamePrintsF.print
      grind
    | ret =>
      simp only [pure_bind]
      apply SamePrintsA.monotone (fun _ _ h => Or.inl h)
      apply SamePrints.out
      apply h2
    | fail =>
      simp only [CompM.fail_bind]
      apply SamePrintsF.fail
    | silentL =>
      apply SamePrintsF.silentL
      · apply Silent.bind; assumption
      assumption
    | silentR =>
      apply SamePrintsF.silentR
      · apply Silent.bind; assumption
      assumption
  · exact ⟨a1, a2, h1, rfl, rfl⟩

theorem SamePrints.rand {β : Type} {b1 b2 : ℤ → Nondet β}
    (h2 : ∀x y, SamePrints (b1 x) (b2 y)):
  SamePrints (Nondet.rand >>= b1) (Nondet.rand >>= b2) := by
  apply SamePrints.roll
  apply SamePrintsF.silent
  · apply Silent.rand
  · apply Silent.rand
  assumption

theorem SamePrints.print {z : ℤ}:
  SamePrints (Nondet.print z) (Nondet.print z) := by
  apply SamePrints.roll
  have : pure (f := Nondet) = fun _ => pure () := by simp
  conv =>
    congr
    · skip
    · rw [←bind_pure (x := Nondet.print z), this]
    · rw [←bind_pure (x := Nondet.print z), this]
  apply SamePrintsF.print
  apply SamePrints.roll
  apply SamePrintsF.ret

theorem SamePrints.loop {β : Type} {body₁ body₂ : β → Nondet (ForInStep β)}
    {init : β}
    (hbody : ∀x, SamePrints (body₁ x) (body₂ x)):
    SamePrints (CompM.loop body₁ init) (CompM.loop body₂ init) := by
  let next (body : β → Nondet (ForInStep β)) : ForInStep β → Nondet β
    | .done v  => pure v
    | .yield v => CompM.tick *> CompM.loop body v
  let R : Nondet β → Nondet β → Prop :=
    fun x y =>
      ∃ m₁ m₂,
        SamePrints m₁ m₂ ∧
        x = m₁ >>= next body₁ ∧
        y = m₂ >>= next body₂
  rw [CompM.loop_def body₁ init, CompM.loop_def body₂ init]
  apply SamePrints.coind (R := R)
  · rintro x y ⟨m₁, m₂, hm, rfl, rfl⟩
    have h := hm.out
    clear hm
    induction h with
    | silent =>
      apply SamePrintsF.silent
      · apply Silent.bind; assumption
      · apply Silent.bind; assumption
      grind
    | print =>
      simp only [bind_assoc]
      apply SamePrintsF.print
      grind
    | @ret r =>
      simp only [pure_bind]
      cases r with
      | done v => apply SamePrintsF.ret
      | yield v =>
        apply SamePrintsF.silent
        · apply Silent.tick
        · apply Silent.tick
        simp only [R]
        intros
        conv =>
          enter [1, x, 1, x, 2]
          congr <;> rw [CompM.loop_def]
        exists body₁ v, body₂ v
        grind
    | fail =>
      simp only [CompM.fail_bind]
      apply SamePrintsF.fail
    | silentL =>
      apply SamePrintsF.silentL
      · apply Silent.bind; assumption
      assumption
    | silentR =>
      apply SamePrintsF.silentR
      · apply Silent.bind; assumption
      assumption
  · tauto

def Deterministic {α} (t : Nondet α) : Prop := SamePrints t t

theorem scaryLoopDet_Deterministic : Deterministic scaryLoopDet := by
  apply SamePrints.bind
  · apply SamePrints.loop
    simp only [↓reduceIte, Int.sub_self, bind_pure_comp, forall_const]
    apply SamePrints.rand
    intros
    apply SamePrints.bind
    · apply SamePrints.print
    intro ⟨⟩
    apply SamePrints.roll SamePrintsF.ret
  · intro
    apply SamePrints.roll SamePrintsF.ret


end Freigen.CompM.Example
