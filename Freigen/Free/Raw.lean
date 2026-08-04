import Freigen.IxPoly.Defs
import Freigen.Eff

namespace Freigen

def RawFree
    {Γ : Type u} (E : Γ → Type u) [Eff.Spec.{u, v} E]
    (γ : Γ) (α : Type v) : Type _ :=
  IxPoly.W (Eff.Step Γ E) (γ, α)

namespace RawFree

variable {Γ : Type u} {E : Γ → Type u} [eS : Eff.Spec.{u, v} E]
  {γ : Γ} {α β : Type v}

abbrev At
    {Γ : Type u} (E : Γ → Type u) [Eff.Spec.{u, v} E]
    (i : Γ × Type v) : Type _ :=
  IxPoly.W (Eff.Step Γ E) i

def bind
    {i : Γ × Type v}
    (a : IxPoly.W (Eff.Step Γ E) i)
    (f : i.2 → IxPoly.W (Eff.Step Γ E) (i.1, β)) :
    IxPoly.W (Eff.Step Γ E) (i.1, β) :=
  match a with
  | IxPoly.W.mk _ p children =>
    match p with
    | .ret a => f a
    | .op e =>
      IxPoly.W.mk (F := Eff.Step Γ E) _ (Eff.NodeTag.op e) fun
        | .inl a =>
          bind (i := (i.1, i.2))
            (show IxPoly.W (Eff.Step Γ E) (i.1, i.2) from
              children (.inl a))
            f
        | .inr b => children (.inr b)

private theorem bind_pure_law
    {i : Γ × Type v}
    (x : IxPoly.W (Eff.Step Γ E) i) :
    bind (β := i.2) x
      (fun a => IxPoly.W.roll (Eff.Step.ret (γ := i.1) a)) = x := by
  induction x with
  | mk i p children ih =>
    cases p
    · simp [bind, IxPoly.W.roll, Eff.Step.ret]
      ext field
      cases field
    · simp only [bind]
      congr 2
      ext field
      cases field
      · simp only
        apply_assumption
      · rfl

private theorem bind_assoc_law
    {i : Γ × Type v} {δ : Type v}
    (a : IxPoly.W (Eff.Step Γ E) i)
    (f : i.2 → IxPoly.W (Eff.Step Γ E) (i.1, β))
    (g : β → IxPoly.W (Eff.Step Γ E) (i.1, δ)) :
    bind (bind a f) g =
      bind a (fun x => bind (i := (i.1, β)) (f x) g) := by
  induction a with
  | mk i p children ih =>
    cases p
    · rfl
    · simp only [bind]
      rw [bind]
      congr 2
      ext field
      cases field
      · simp only
        apply ih
      · rfl

instance : Monad (RawFree E γ) where
  pure a := IxPoly.W.roll (Eff.Step.ret a)
  bind x f := bind x f

instance : LawfulMonad (RawFree E γ) :=
  LawfulMonad.mk' _
    (by intros; apply bind_pure_law)
    (by intros; change bind _ _ = _; rfl)
    (by intros; apply bind_assoc_law)

def op
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      RawFree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)) :
    RawFree E γ (eS.output γ e) :=
  IxPoly.W.mk (F := Eff.Step Γ E) _ (Eff.NodeTag.op e) fun
    | .inl a =>
      IxPoly.W.roll (F := Eff.Step Γ E) (Eff.Step.ret (γ := γ) a)
    | .inr ⟨b, i⟩ => blocks b i

theorem op_injective (e : E γ) :
    Function.Injective (RawFree.op e) := by
  intro blocks₁ blocks₂ h
  have h := congrArg IxPoly.W.observe h
  simp only [RawFree.op, IxPoly.W.observe] at h
  injection h with htag hchildren
  funext t input
  exact congrFun hchildren (Sum.inr ⟨t, input⟩)

@[simp]
theorem op_inj
    (e : E γ)
    {blocks₁ blocks₂ :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      RawFree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)} :
    RawFree.op e blocks₁ = RawFree.op e blocks₂ ↔
      blocks₁ = blocks₂ :=
  (RawFree.op_injective e).eq_iff

@[simp]
theorem op_ne_pure
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      RawFree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (x : eS.output γ e) :
    RawFree.op e blocks ≠ pure x := by
  intro h
  have h := congrArg IxPoly.W.observe h
  simp only [RawFree.op, Pure.pure, IxPoly.W.roll, Eff.Step.ret,
    IxPoly.W.observe] at h
  injection h with htag
  cases htag

@[simp]
theorem pure_ne_op
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      RawFree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (x : eS.output γ e) :
    pure x ≠ RawFree.op e blocks :=
  Ne.symm (RawFree.op_ne_pure e blocks x)

theorem bind_op
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      RawFree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (k : eS.output γ e → RawFree E γ α) :
    RawFree.bind (RawFree.op e blocks) k =
      IxPoly.W.mk (F := Eff.Step Γ E) _ (Eff.NodeTag.op e) fun
        | .inl output => k output
        | .inr ⟨t, input⟩ => blocks t input :=
  by
    unfold RawFree.op
    rw [RawFree.bind]
    congr 2
    funext field
    cases field with
    | inl output =>
        change k output = k output
        rfl
    | inr block =>
        rfl

@[simp]
theorem pure_ne_op_bind
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      RawFree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (k : eS.output γ e → RawFree E γ α)
    (x : α) :
    pure x ≠ RawFree.op e blocks >>= k := by
  intro h
  change (pure x : RawFree E γ α) =
    RawFree.bind (RawFree.op e blocks) k at h
  rw [RawFree.bind_op] at h
  have h := congrArg IxPoly.W.observe h
  simp only [Pure.pure, IxPoly.W.roll, Eff.Step.ret,
    IxPoly.W.observe] at h
  injection h with htag
  cases htag

theorem op_bind_effect_eq
    {e₁ e₂ : E γ}
    {blocks₁ :
      (t : eS.blockTag γ e₁) →
      eS.blockInputs γ e₁ t →
      RawFree E (eS.blockCtx γ e₁ t) (eS.blockOutputs γ e₁ t)}
    {blocks₂ :
      (t : eS.blockTag γ e₂) →
      eS.blockInputs γ e₂ t →
      RawFree E (eS.blockCtx γ e₂ t) (eS.blockOutputs γ e₂ t)}
    {k₁ : eS.output γ e₁ → RawFree E γ α}
    {k₂ : eS.output γ e₂ → RawFree E γ α}
    (h :
      (RawFree.op e₁ blocks₁ >>= k₁) =
        (RawFree.op e₂ blocks₂ >>= k₂)) :
    e₁ = e₂ := by
  change
    RawFree.bind (RawFree.op e₁ blocks₁) k₁ =
      RawFree.bind (RawFree.op e₂ blocks₂) k₂ at h
  rw [RawFree.bind_op, RawFree.bind_op] at h
  have htag := congrArg (fun x => (IxPoly.W.observe x).1) h
  simp only [IxPoly.W.observe] at htag
  injection htag

private theorem op_bind_payload_eq
    (e : E γ)
    (blocks₁ blocks₂ :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      RawFree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (k₁ k₂ : eS.output γ e → RawFree E γ α)
    (h :
      (RawFree.op e blocks₁ >>= k₁) =
        (RawFree.op e blocks₂ >>= k₂)) :
    blocks₁ = blocks₂ ∧ k₁ = k₂ := by
  change
    RawFree.bind (RawFree.op e blocks₁) k₁ =
      RawFree.bind (RawFree.op e blocks₂) k₂ at h
  rw [RawFree.bind_op, RawFree.bind_op] at h
  have h := congrArg IxPoly.W.observe h
  simp only [IxPoly.W.observe] at h
  injection h with htag hchildren
  constructor
  · funext t input
    exact congrFun hchildren (Sum.inr ⟨t, input⟩)
  · funext output
    exact congrFun hchildren (Sum.inl output)

@[simp]
theorem op_bind_inj
    (e₁ e₂ : E γ)
    (blocks₁ :
      (t : eS.blockTag γ e₁) →
      eS.blockInputs γ e₁ t →
      RawFree E (eS.blockCtx γ e₁ t) (eS.blockOutputs γ e₁ t))
    (blocks₂ :
      (t : eS.blockTag γ e₂) →
      eS.blockInputs γ e₂ t →
      RawFree E (eS.blockCtx γ e₂ t) (eS.blockOutputs γ e₂ t))
    (k₁ : eS.output γ e₁ → RawFree E γ α)
    (k₂ : eS.output γ e₂ → RawFree E γ α) :
    (RawFree.op e₁ blocks₁ >>= k₁) =
        (RawFree.op e₂ blocks₂ >>= k₂) ↔
      ∃ _h : e₁ = e₂,
        HEq (RawFree.op e₁ blocks₁) (RawFree.op e₂ blocks₂) ∧
          HEq k₁ k₂ := by
  constructor
  · intro h
    have he := RawFree.op_bind_effect_eq h
    subst e₂
    rcases RawFree.op_bind_payload_eq e₁ blocks₁ blocks₂ k₁ k₂ h with
      ⟨hblocks, hk⟩
    exact ⟨rfl,
      heq_of_eq (congrArg (RawFree.op e₁) hblocks),
      heq_of_eq hk⟩
  · rintro ⟨he, hOp, hk⟩
    subst e₂
    rw [eq_of_heq hOp, eq_of_heq hk]

@[simp]
theorem op_bind_inj'
    (e₁ e₂ : E γ)
    (blocks₁ :
      (t : eS.blockTag γ e₁) →
      eS.blockInputs γ e₁ t →
      RawFree E (eS.blockCtx γ e₁ t) (eS.blockOutputs γ e₁ t))
    (blocks₂ :
      (t : eS.blockTag γ e₂) →
      eS.blockInputs γ e₂ t →
      RawFree E (eS.blockCtx γ e₂ t) (eS.blockOutputs γ e₂ t))
    (k : eS.output γ e₁ →
      RawFree E γ (eS.output γ e₂)) :
    (RawFree.op e₁ blocks₁ >>= k) = RawFree.op e₂ blocks₂ ↔
      ∃ _h : e₁ = e₂,
        HEq (RawFree.op e₁ blocks₁) (RawFree.op e₂ blocks₂) ∧
          HEq k (fun x : eS.output γ e₂ =>
            (pure x : RawFree E γ (eS.output γ e₂))) := by
  simpa only [bind_pure] using
    RawFree.op_bind_inj e₁ e₂ blocks₁ blocks₂ k
      (fun x : eS.output γ e₂ =>
        (pure x : RawFree E γ (eS.output γ e₂)))

protected def recOn
    {motive : (i : Γ × Type v) → RawFree.At E i → Sort w}
    (step :
      ∀ {i} (layer : Eff.Step Γ E (RawFree.At E) i),
        (∀ field, motive _ (layer.2 field)) →
        motive i (IxPoly.W.roll layer)) :
    {i : Γ × Type v} →
    (raw : RawFree.At E i) →
    motive i raw
  | _, .mk _ p children =>
      step ⟨p, children⟩
        (fun field => RawFree.recOn step (children field))

def interp
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
          interp monadM handler (children (.inr ⟨t, input⟩))) >>=
        fun output =>
          interp monadM handler (children (.inl output))

theorem interp_bind
    {M : Γ → Type v → Type w}
    (monadM : (γ : Γ) → Monad (M γ))
    (lawfulM : (γ : Γ) → @LawfulMonad (M γ) (monadM γ))
    (handler : Eff.Handler E M)
    {i : Γ × Type v} {β : Type v}
    (x : IxPoly.W (Eff.Step Γ E) i)
    (f : i.2 → IxPoly.W (Eff.Step Γ E) (i.1, β)) :
    interp monadM handler (bind x f) =
      @Bind.bind (M i.1) (monadM i.1).toBind _ _
        (interp monadM handler x)
        (fun a =>
          interp (i := (i.1, β)) monadM handler (f a)) := by
  induction x with
  | mk i p children ih =>
    rcases i with ⟨γ, α⟩
    cases p with
    | ret x =>
      simp only [bind, interp]
      letI := monadM γ
      letI := lawfulM γ
      simp
    | op e =>
      rw [bind]
      simp only [interp]
      letI := monadM γ
      letI := lawfulM γ
      rw [bind_assoc]
      congr 1
      funext output
      exact ih (.inl output) f

theorem interp_op
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
    interp monadM handler (op e blocks) =
      handler e (fun t input =>
        interp monadM handler (blocks t input)) := by
  letI := monadM γ
  letI := lawfulM γ
  change
    (handler e (fun t input =>
      interp monadM handler (blocks t input)) >>= pure) =
    handler e (fun t input =>
      interp monadM handler (blocks t input))
  rw [bind_pure]

end RawFree

end Freigen
