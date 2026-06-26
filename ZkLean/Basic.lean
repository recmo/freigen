import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Defs
import Lean

inductive Free (F : Type u → Type v) (α : Type u): Type _
| Pure : α → Free F α
| Impure : ∀{x}, F x -> (x -> Free F α) -> Free F α

def freeBind {F : Type u → Type v} {α β : Type u} (a : Free F α) (f : α → Free F β) : Free F β :=
  match a with
  | Free.Pure x => f x
  | Free.Impure a f' => Free.Impure a (fun x => freeBind (f' x) f)

instance {F : Type u → Type v} : Monad (Free F) where
  pure := Free.Pure
  bind := freeBind

#check Free.recOn

inductive hls : Nat → Type
| zero : hls 0
| succ : ∀ n, hls n → hls (n + 1)

#check hls.recOn

def foldFree [Functor F] [Monad M] (x : Free F α) (f : ∀{x}, F x → M x): M α := match x with
  | Free.Pure x => pure x
  | Free.Impure a f' => f a >>= fun x => foldFree (f' x) f

inductive CircuitF (WitnessOf : Type → Type) (𝔽 : Type) β
| Hint {α : Type} : α → (WitnessOf α -> β) -> CircuitF WitnessOf 𝔽 β
| AssertR1C : WitnessOf 𝔽 → WitnessOf 𝔽 → WitnessOf 𝔽 → β → CircuitF WitnessOf 𝔽 β

instance {WitnessOf : Type → Type} : Functor (CircuitF WitnessOf 𝔽) where
  map f a := match a with
    | CircuitF.Hint a f' => CircuitF.Hint a (f ∘ f')
    | CircuitF.AssertR1C b c d a => CircuitF.AssertR1C b c d (f a)

def Circuit (WitnessOf : Type → Type) (𝔽 : Type) := Free (CircuitF WitnessOf 𝔽)

instance {WitnessOf : Type → Type} : Monad (Circuit WitnessOf 𝔽) := inferInstanceAs $ Monad (Free (CircuitF WitnessOf 𝔽))

def Circuit.assert (WitnessOf : Type → Type) (𝔽 : Type) (a b c : WitnessOf 𝔽) : Circuit WitnessOf 𝔽 Unit := Free.Impure (CircuitF.AssertR1C a b c ()) pure

def Circuit.hint {WitnessOf : Type → Type} {𝔽 : Type} {α : Type} (a : α) : Circuit WitnessOf 𝔽 (WitnessOf α) := Free.Impure (CircuitF.Hint a id) pure

def Circuit.eval [r: Ring 𝔽] [DecidableEq 𝔽] (c : ∀ Witness, Circuit Witness 𝔽 α) : Option α := foldFree (c id) fun a => match a with
  | CircuitF.Hint a f => some (f a)
  | CircuitF.AssertR1C a b c next => if r.mul a b = c then pure next else none

def ContProp (t : Type) : Type := (t → Prop) → Prop

instance : Monad ContProp where
  pure p := fun k => k p
  bind p f := fun g => p (fun x => f x g)

def Circuit.assignable [r: Ring 𝔽] [DecidableEq 𝔽] (c : ∀ Witness, Circuit Witness 𝔽 α) (k : α → Prop) : Prop := foldFree (M:=ContProp) (c id) (fun a => match a with
  | CircuitF.Hint _ f => fun k => ∃a, k (f a)
  | CircuitF.AssertR1C a b c next => fun k => r.mul a b = c ∧ k next
) k
