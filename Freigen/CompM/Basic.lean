import Freigen.ITree.Basic
import Freigen.ExactCodensity
import Freigen.Eff

namespace Freigen

def CompM (E : Eff.Spec.{u, 0}) (α : Type) : Type _ :=
  ExactCodensity (ITree E) α

instance {E} : Monad (CompM E) := inferInstanceAs (Monad (ExactCodensity (ITree E)))
instance {E} : LawfulMonad (CompM E) := inferInstanceAs (LawfulMonad (ExactCodensity (ITree E)))

namespace CompM

variable {E : Eff.Spec.{u, 0}} {α β : Type}

private theorem bind_def {α β : Type _} (x : CompM E α) (f : α → CompM E β) :
    x >>= f = ⟨fun g => x.run fun a => (f a).run g, by
      intros
      conv => lhs; rw [←x.exact]
      rw [bind_assoc]
      simp only [ExactCodensity.exact]⟩ := by
  rfl

def tick : CompM E Unit := ⟨fun f => ITree.tau (f ()), by simp⟩
def op (e : E.tag) (inp : E.input e)
    (blocks : (t : E.blockTag e) → E.blockInputs e t → ITree E (E.blockOutputs e t)): CompM E (E.output e) :=
  ⟨fun f => ITree.op e inp blocks f, by simp⟩
def fail : CompM E α := ⟨fun _ => ITree.fail, by simp⟩

@[simp]
theorem fail_bind (f : α → CompM E β) : fail >>= f = fail := by
  simp [fail, bind_def]

def loop (body : α → CompM E (ForInStep α)) (init : α): CompM E α := {
  run := fun f => ITree.loop (fun a => (body a).run pure) init f
  exact := by
    intros
    apply ITree.loop_bind
}

theorem loop_def
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

instance : ForIn (CompM E) Lean.Loop Unit where
  forIn _ init body := loop (fun a => body () a) init

end Freigen.CompM
