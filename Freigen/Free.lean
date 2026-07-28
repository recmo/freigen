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
    | .op e =>
      IxPoly.W.mk (F := Eff.Step Γ E) _ (Eff.NodeTag.op e) fun
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
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      IxPoly.W (Eff.Step Γ E)
        (eS.blockCtx γ e t, eS.blockOutputs γ e t)) :
    IxPoly.W (Eff.Step Γ E) (γ, eS.output γ e) :=
  IxPoly.W.mk (F := Eff.Step Γ E) _ (Eff.NodeTag.op e) fun
    | .inl a =>
      IxPoly.W.roll (F := Eff.Step Γ E) (Eff.Step.ret (γ := γ) a)
    | .inr ⟨b, i⟩ => blocks b i

def Free.op
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)) :
    Free E γ (eS.output γ e) :=
  ExactCodensity.equiv.symm <|
    wOp e (fun t i => ExactCodensity.equiv (blocks t i))

instance : Monad (Free E γ) :=
  inferInstanceAs
    (Monad (ExactCodensity
      (fun α : Type v => IxPoly.W (Eff.Step Γ E) (γ, α))))

instance : LawfulMonad (Free E γ) :=
  inferInstanceAs
    (LawfulMonad (ExactCodensity
      (fun α : Type v => IxPoly.W (Eff.Step Γ E) (γ, α))))

private def wInterp
    {M : Γ → Type v → Type w}
    (monadM : (γ : Γ) → Monad (M γ))
    (handler : Eff.Handler E M) :
    {i : Γ × Type v} →
    IxPoly.W (Eff.Step Γ E) i →
    M i.1 i.2
  | (γ, _), .mk _ p children =>
    match p with
    | .ret x =>
      letI := monadM γ
      pure x
    | .op e =>
      letI := monadM γ
      handler e
        (fun t input =>
          wInterp monadM handler (children (.inr ⟨t, input⟩))) >>=
        fun output =>
          wInterp monadM handler (children (.inl output))

private theorem wInterp_wBind
    {M : Γ → Type v → Type w}
    (monadM : (γ : Γ) → Monad (M γ))
    (lawfulM : (γ : Γ) → @LawfulMonad (M γ) (monadM γ))
    (handler : Eff.Handler E M)
    {i : Γ × Type v} {β : Type v}
    (x : IxPoly.W (Eff.Step Γ E) i)
    (f : i.2 → IxPoly.W (Eff.Step Γ E) (i.1, β)) :
    wInterp monadM handler (wBind x f) =
      @Bind.bind (M i.1) (monadM i.1).toBind _ _
        (wInterp monadM handler x)
        (fun a =>
          wInterp (i := (i.1, β)) monadM handler (f a)) := by
  induction x with
  | mk i p children ih =>
    rcases i with ⟨γ, α⟩
    cases p with
    | ret x =>
      simp only [wBind, wInterp]
      letI := monadM γ
      letI := lawfulM γ
      simp
    | op e =>
      rw [wBind]
      simp only [wInterp]
      letI := monadM γ
      letI := lawfulM γ
      rw [bind_assoc]
      congr 1
      funext output
      exact ih (.inl output) f

private theorem wInterp_wOp
    {M : Γ → Type v → Type w}
    (monadM : (γ : Γ) → Monad (M γ))
    (lawfulM : (γ : Γ) → @LawfulMonad (M γ) (monadM γ))
    (handler : Eff.Handler E M)
    {γ : Γ}
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      IxPoly.W (Eff.Step Γ E)
        (eS.blockCtx γ e t, eS.blockOutputs γ e t)) :
    wInterp monadM handler (wOp e blocks) =
      handler e (fun t input =>
        wInterp monadM handler (blocks t input)) := by
  letI := monadM γ
  letI := lawfulM γ
  change
    (handler e (fun t input =>
      wInterp monadM handler (blocks t input)) >>= pure) =
    handler e (fun t input =>
      wInterp monadM handler (blocks t input))
  rw [bind_pure]

def Free.interp
    {M : Γ → Type v → Type w}
    [monadM : (γ : Γ) → Monad (M γ)]
    (handler : Eff.Handler E M)
    (x : Free E γ α) :
    M γ α :=
  wInterp monadM handler (ExactCodensity.equiv x)

@[simp]
theorem Free.interp_pure
    {M : Γ → Type v → Type w}
    [monadM : (γ : Γ) → Monad (M γ)]
    (handler : Eff.Handler E M)
    (x : α) :
    Free.interp handler (pure x : Free E γ α) =
      @pure (M γ) (monadM γ).toApplicative.toPure α x :=
  rfl

@[simp]
theorem Free.interp_bind
    {M : Γ → Type v → Type w}
    [monadM : (γ : Γ) → Monad (M γ)]
    [lawfulM : (γ : Γ) → @LawfulMonad (M γ) (monadM γ)]
    (handler : Eff.Handler E M)
    (x : Free E γ α)
    (f : α → Free E γ β) :
    Free.interp handler (x >>= f) =
      @Bind.bind (M γ) (monadM γ).toBind _ _
        (Free.interp handler x)
        (fun a => Free.interp handler (f a)) := by
  let lower {δ : Type v} (y : Free E γ δ) :
      IxPoly.W (Eff.Step Γ E) (γ, δ) :=
    ExactCodensity.equiv y
  have hExact :
      x.run (fun a => lower (f a)) =
        wBind (lower x) (fun a => lower (f a)) :=
    (x.exact _).symm
  calc
    Free.interp handler (x >>= f) =
        wInterp monadM handler
          (x.run fun a => lower (f a)) := rfl
    _ = wInterp monadM handler
          (wBind (lower x) (fun a => lower (f a))) :=
      congrArg (wInterp monadM handler) hExact
    _ = @Bind.bind (M γ) (monadM γ).toBind _ _
          (Free.interp handler x)
          (fun a => Free.interp handler (f a)) :=
      wInterp_wBind monadM lawfulM handler
        (lower x)
        (fun a => lower (f a))

@[simp]
theorem Free.interp_op
    {M : Γ → Type v → Type w}
    [monadM : (γ : Γ) → Monad (M γ)]
    [lawfulM : (γ : Γ) → @LawfulMonad (M γ) (monadM γ)]
    (handler : Eff.Handler E M)
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)) :
    Free.interp handler (Free.op e blocks) =
      handler e (fun t input =>
        Free.interp handler (blocks t input)) := by
  have hOp :
      ExactCodensity.equiv (Free.op e blocks) =
        wOp e (fun t input =>
          ExactCodensity.equiv (blocks t input)) :=
    ExactCodensity.equiv.apply_symm_apply _
  letI := monadM γ
  letI := lawfulM γ
  calc
    Free.interp handler (Free.op e blocks) =
        wInterp monadM handler
          (ExactCodensity.equiv (Free.op e blocks)) := rfl
    _ = wInterp monadM handler
          (wOp e (fun t input =>
            ExactCodensity.equiv (blocks t input))) :=
      congrArg (wInterp monadM handler) hOp
    _ = handler e (fun t input =>
          Free.interp handler (blocks t input)) :=
      wInterp_wOp monadM lawfulM handler e
        (fun t input => ExactCodensity.equiv (blocks t input))

end Freigen
