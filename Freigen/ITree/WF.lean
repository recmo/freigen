import Freigen.ITree.Defs

namespace Freigen.ITree.WF

structure Packed {Γ : Type u} (E : Γ → Type u) [Eff.Spec E] where
  γ : Γ
  α : Type w
  t : ITree E γ α

inductive Child {Γ} {E : Γ → Type u} [s: Eff.Spec E] : Packed E → Packed E → Prop
| op_block {γ α e k t i} {blocks} :
    Child ⟨_, _, blocks t i⟩ ⟨γ, α, ITree.op e blocks k⟩
| op_cont {γ α e k} {blocks} {o} :
    Child ⟨_, _, k o⟩ ⟨γ, α, ITree.op e blocks k⟩

end WF

def WF {Γ : Type u} {E : Γ → Type u} {γ : Γ} {α} [s: Eff.Spec E] (t : ITree E γ α) : Prop :=
  Acc WF.Child ⟨γ, α, t⟩

namespace WF

end Freigen.ITree.WF
