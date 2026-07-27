import Freigen.ITree.Basic
import Freigen.ExactCodensity
import Freigen.Eff

namespace Freigen

def CompM
    {Γ : Type u} (E : Γ → Type u) [Eff.Spec E]
    (γ : Γ) (α : Type v) : Type _ :=
  ExactCodensity (ITree E γ) α

variable
  {Γ : Type u} {E : Γ → Type u} [eS : Eff.Spec E]
  {γ : Γ} {α β : Type}

instance {γ : Γ} : Monad (CompM E γ) :=
  inferInstanceAs (Monad (ExactCodensity (ITree E γ)))

instance {γ : Γ} : LawfulMonad (CompM E γ) :=
  inferInstanceAs (LawfulMonad (ExactCodensity (ITree E γ)))

namespace CompM

private theorem bind_def
    {γ : Γ} {α β : Type}
    (x : CompM E γ α) (f : α → CompM E γ β) :
    x >>= f = ⟨fun g => x.run fun a => (f a).run g, by
      intros
      conv => lhs; rw [←x.exact]
      rw [bind_assoc]
      simp only [ExactCodensity.exact]⟩ := by
  rfl

def tick {γ : Γ} [Eff.Has.{u, 0} Eff.Tau E] :
    CompM E γ Unit :=
  ⟨fun f => ITree.tau (f ()), by simp⟩

def fail {γ : Γ} [Eff.Has Eff.Fail E] :
    CompM E γ α :=
  ⟨fun _ => ITree.fail, by simp⟩

def op {γ : Γ} (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)) :
    CompM E γ (eS.output γ e) :=
  ⟨fun f => ITree.op e (fun t i => (blocks t i).run pure) f, by simp⟩

def loop
    {γ : Γ} [Eff.Has Eff.Tau E]
    (body : α → CompM E γ (α ⊕ β)) (init : α) :
    CompM E γ β := {
  run := fun f => ITree.loop (fun a => (body a).run pure) init f
  exact := by
    intros
    apply ITree.loop_bind
}

theorem loop_def [Eff.Has Eff.Tau E]
  (body : α → CompM E γ (α ⊕ β))
  (s : α) :
  CompM.loop body s =
    body s >>= fun
      | .inr v  => pure v
      | .inl v => CompM.tick (E := E) (γ := γ) *> CompM.loop body v := by
  apply ExactCodensity.equiv.injective
  change (CompM.loop body s).run pure =
    ((body s >>= fun
      | .inr v => pure v
      | .inl v =>
        CompM.tick (E := E) (γ := γ) *> CompM.loop body v) :
        CompM E γ β).run pure
  simp only [loop, bind_def]
  rw [ITree.loop_def]
  rw [ExactCodensity.exact]
  congr 1
  funext x
  cases x <;> rfl

abbrev forInStepToSum : ForInStep α → α ⊕ α
  | .yield x => .inl x
  | .done x => .inr x

instance {γ : Γ} [Eff.Has Eff.Tau E] :
    ForIn (CompM E γ) Lean.Loop Unit where
  forIn _ init body := loop (fun a => forInStepToSum <$> (body () a)) init

end Freigen.CompM
