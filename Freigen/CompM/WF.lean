import Freigen.ITree.WF
import Freigen.CompM.Basic
import Freigen.Free

namespace Freigen.CompM

def WF {Γ : Type u} {E : Γ → Type u} [s: Eff.Spec E] {γ : Γ} {α : Type v} (t : CompM E γ α) : Prop :=
  ITree.WF (ExactCodensity.equiv t)

def toFree {Γ : Type u} {E : Γ → Type u} [s: Eff.Spec E] {γ : Γ} {α : Type v} (t : CompM E γ α) (h : WF t) :
    Free E γ α :=
  h.recC (motive := fun x _ => Free E x.γ x.α)
  (fun ⟨_, _, t⟩ _ recur =>
    t.casesOn (motive := fun (γ, α) t =>
      ((y : ITree.WF.Packed E) → ITree.WF.Child y ⟨γ, α, t⟩ → Free E y.γ y.α) → Free E γ α)
      (fun v _ => pure v)
      (fun e blocks k recur =>
        Free.op e (fun t i => recur ⟨_, _, blocks t i⟩  ITree.WF.Child.op_block) >>= (fun i =>
          recur ⟨_, _, k i⟩ ITree.WF.Child.op_cont
        )
      ) recur
  )


end Freigen.CompM
