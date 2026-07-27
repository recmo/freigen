import Freigen.IxPoly.Defs
import Freigen.ExactCodensity
import Freigen.Eff

namespace Freigen

variable {Γ : Type u} {E : Γ → Type u} [eS : Eff.Spec.{u, v} E]
  {γ : Γ} {α β : Type v}

private def wBind
    {i : Γ × Type v}
    (a : IxPoly.W (Eff.Step Γ E) i)
    (f : i.2 → IxPoly.W (Eff.Step Γ E) (i.1, β)) :
    IxPoly.W (Eff.Step Γ E) (i.1, β) :=
  match a with
  | IxPoly.W.mk _ p g =>
    match p with
    | .ret a => f a
    | .op e inp =>
      IxPoly.W.mk (F := Eff.Step Γ E) _ (Eff.NodeTag.op e inp) fun
        | .inl a =>
          wBind (i := (i.1, i.2))
            (show IxPoly.W (Eff.Step Γ E) (i.1, i.2) from g (.inl a)) f
        | .inr b => g (.inr b)

private theorem wBind_pure
    {i : Γ × Type v}
    (x : IxPoly.W (Eff.Step Γ E) i) :
    wBind (β := i.2) x
      (fun a => IxPoly.W.roll (Eff.Step.ret (γ := i.1) a)) = x := by
  induction x with
  | mk i p g ih =>
    cases p
    · simp [wBind, IxPoly.W.roll, Eff.Step.ret]
      ext a
      cases a
    · simp only [wBind]
      congr 2
      ext x
      cases x
      · simp only
        apply_assumption
      · rfl

private theorem wBind_assoc
    {i : Γ × Type v} {δ : Type v}
    (a : IxPoly.W (Eff.Step Γ E) i)
    (f : i.2 → IxPoly.W (Eff.Step Γ E) (i.1, β))
    (g : β → IxPoly.W (Eff.Step Γ E) (i.1, δ)) :
    wBind (wBind a f) g =
      wBind a (fun x => wBind (i := (i.1, β)) (f x) g) := by
  induction a with
  | mk i p children ih =>
    cases p
    · rfl
    · simp only [wBind]
      rw [wBind]
      congr 2
      ext x
      cases x
      · simp only
        apply ih
      · rfl

instance : Monad (fun α : Type v => IxPoly.W (Eff.Step Γ E) (γ, α)) where
  pure a := IxPoly.W.roll (Eff.Step.ret a)
  bind x f := wBind x f

instance : LawfulMonad (fun α : Type v => IxPoly.W (Eff.Step Γ E) (γ, α)) :=
  LawfulMonad.mk' _
    (by intros; apply wBind_pure)
    (by intros; change wBind _ _ = _; rfl)
    (by intros; apply wBind_assoc)

def Free
    {Γ : Type u} (E : Γ → Type u) [Eff.Spec.{u, v} E]
    (γ : Γ) (α : Type v) : Type _ :=
  ExactCodensity (fun α : Type v => IxPoly.W (Eff.Step Γ E) (γ, α)) α

private def wOp
    (e : E γ) (inp : eS.input γ e)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      IxPoly.W (Eff.Step Γ E)
        (eS.blockCtx γ e t, eS.blockOutputs γ e t)) :
    IxPoly.W (Eff.Step Γ E) (γ, eS.output γ e) :=
  IxPoly.W.mk (F := Eff.Step Γ E) _ (Eff.NodeTag.op e inp) fun
    | .inl a =>
      IxPoly.W.roll (F := Eff.Step Γ E) (Eff.Step.ret (γ := γ) a)
    | .inr ⟨b, i⟩ => blocks b i

def Free.op
    (e : E γ) (inp : eS.input γ e)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)) :
    Free E γ (eS.output γ e) :=
  ExactCodensity.equiv.symm <|
    wOp e inp (fun t i => ExactCodensity.equiv (blocks t i))

instance : Monad (Free E γ) :=
  inferInstanceAs
    (Monad (ExactCodensity
      (fun α : Type v => IxPoly.W (Eff.Step Γ E) (γ, α))))

instance : LawfulMonad (Free E γ) :=
  inferInstanceAs
    (LawfulMonad (ExactCodensity
      (fun α : Type v => IxPoly.W (Eff.Step Γ E) (γ, α))))

end Freigen
