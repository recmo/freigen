import Freigen.CompM.Basic
import Freigen.ITree.Basic
import Freigen.Eff

namespace Freigen.CompM.Examples

structure RecurC (inp : Type) (out : Type) where
  args : inp

def Recur {Γ} (i o : Type) (_γ : Γ) := RecurC i o

instance {Γ} {inp out : Type} : Eff.Spec (@Recur Γ inp out) where
  output := fun _ _ => out
  blockTag := fun _ _ => PEmpty
  blockCtx := nofun
  blockInputs := nofun
  blockOutputs := nofun

namespace Recur

def runCounted {Γ : Type} {γ : Γ} {α : Type} :
    (fuel : Nat) → CompM Eff.Tau γ α → Option (α × Nat)
  | 0, x =>
      match CompM.observe x with
      | ⟨.ret value, _⟩ => some (value, 0)
      | ⟨.op _, _⟩ => none
  | fuel + 1, x =>
      match CompM.observe x with
      | ⟨.ret value, _⟩ => some (value, 0)
      | ⟨.op _, children⟩ =>
          (runCounted fuel (children (.inl PUnit.unit))).map
            fun (value, steps) => (value, steps + 1)

def fix {Γ : Type} {E : Γ → Type} [Eff.Spec E] [Eff.Has Eff.Tau E]
    {inp out : Type}
    (f : (∀ {γ}, inp → CompM (Recur inp out ⊕ₑ E) γ out) →
      ∀ {γ}, inp → CompM (Recur inp out ⊕ₑ E) γ out) :
    ∀ {γ}, inp → CompM E γ out :=
  let recur : ∀ {γ}, inp → CompM (Recur inp out ⊕ₑ E) γ out :=
    fun i => CompM.liftL <| CompM.op (E := Recur inp out) ⟨i⟩ nofun
  let body : ∀ {γ}, inp → CompM (Recur inp out ⊕ₑ E) γ out := f recur
  fun i => CompM.interpL (body i) fun step =>
    Eff.Step.casesOn step
      (motive := fun i _ =>
        Eff.Step _ E
          (fun i => CompM (Recur inp out ⊕ₑ E) i.1 i.2) i)
      (fun value => Eff.Step.ret value)
      (fun {γ} {_} ⟨args⟩ _ k =>
        Eff.Step.tau (body (γ := γ) args >>= k))

def isEvenTail : Nat → CompM Eff.Tau () Bool := fix fun isEven => fun
| 0 => pure true
| 1 => pure false
| n + 2 => isEven n

#eval runCounted 10 (isEvenTail 4)

def isEvenStack : Nat → CompM Eff.Tau () Bool := fix fun isEven => fun
| 0 => pure true
| n + 1 => do pure !(←isEven n)

#eval runCounted 6 (isEvenStack 6)

end Freigen.CompM.Examples.Recur
