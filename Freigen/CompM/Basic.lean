import Freigen.ITree.Basic
import Freigen.ExactCodensity
import Freigen.Eff

namespace Freigen

def CompM (E : Type u) [Eff.Spec E] (α : Type) : Type _ :=
  ExactCodensity (ITree E) α

variable {E : Type u} [eS: Eff.Spec E] {α β : Type}

instance {E : Type u} [Eff.Spec E] : Monad (CompM E) := inferInstanceAs (Monad (ExactCodensity (ITree E)))
instance {E : Type u} [Eff.Spec E] : LawfulMonad (CompM E) := inferInstanceAs (LawfulMonad (ExactCodensity (ITree E)))

namespace CompM

private theorem bind_def {α β : Type _} (x : CompM E α) (f : α → CompM E β) :
    x >>= f = ⟨fun g => x.run fun a => (f a).run g, by
      intros
      conv => lhs; rw [←x.exact]
      rw [bind_assoc]
      simp only [ExactCodensity.exact]⟩ := by
  rfl

def tick [Eff.Has Eff.Tau E] : CompM E Unit := ⟨fun f => ITree.tau (f ()), by simp⟩
def op (e : E) (inp : eS.input e)
    (blocks : (t : eS.blockTag e) → eS.blockInputs e t → CompM E (eS.blockOutputs e t)): CompM E (eS.output e) :=
  ⟨fun f => ITree.op e inp (fun t i => (blocks t i).run pure) f, by simp⟩

def loop [Eff.Has Eff.Tau E] (body : α → CompM E (ForInStep α)) (init : α): CompM E α := {
  run := fun f => ITree.loop (fun a => (body a).run pure) init f
  exact := by
    intros
    apply ITree.loop_bind
}

theorem loop_def [Eff.Has Eff.Tau E]
  (body : β → CompM E (ForInStep β))
  (s : β) :
  CompM.loop body s =
    body s >>= fun
      | .done v  => pure v
      | .yield v => CompM.tick *> CompM.loop body v := by
  apply (ExactCodensity.equiv β).injective
  change (CompM.loop body s).run pure =
    ((body s >>= fun
      | .done v => pure v
      | .yield v => CompM.tick *> CompM.loop body v) : CompM E β).run pure
  simp only [loop, bind_def]
  rw [ITree.loop_def]
  rw [ExactCodensity.exact]
  congr 1
  funext x
  cases x <;> rfl

instance [Eff.Has Eff.Tau E] : ForIn (CompM E) Lean.Loop Unit where
  forIn _ init body := loop (fun a => body () a) init

end Freigen.CompM
