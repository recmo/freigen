import Freigen.IxPoly.Basic

namespace Freigen.Eff

class Spec (tag : Type u) where
  input : tag → Type v
  output : tag → Type v
  blockTag : tag → Type u
  blockInputs : (t : tag) → blockTag t → Type v
  blockOutputs : (t : tag) → blockTag t → Type v

inductive NodeTag (T : Type u) [s: Spec T] : Type _ → Type _ where
| ret {R} : R → NodeTag T R
| op {R} (t : T) : s.input t → NodeTag T R

def NodeTag.fields {i} {T : Type u} [s : Spec T]: NodeTag T i → Type _
| ret _ => PEmpty
| op e _ => s.output e ⊕ ((t : s.blockTag e) × s.blockInputs e t)

def NodeTag.elem {T : Type u} [s : Spec T] {α : Type v} :
    (t : NodeTag T α) → (p : t.fields) → Type v
| ret _, x => nomatch x
| op _ _, Sum.inl _ => α
| op e _, Sum.inr ⟨o, _⟩ => s.blockOutputs e o

instance : Spec PEmpty where
  input := nofun
  output := nofun
  blockTag := nofun
  blockInputs := nofun
  blockOutputs := nofun

instance sumInst {T₁ T₂ : Type u} [Spec T₁] [Spec T₂] : Spec (T₁ ⊕ T₂) where
  input := fun
    | Sum.inl t => Spec.input t
    | Sum.inr t => Spec.input t
  output := fun
    | Sum.inl t => Spec.output t
    | Sum.inr t => Spec.output t
  blockTag := fun
    | Sum.inl t => Spec.blockTag t
    | Sum.inr t => Spec.blockTag t
  blockInputs := fun
    | Sum.inl t => Spec.blockInputs t
    | Sum.inr t => Spec.blockInputs t
  blockOutputs := fun
    | Sum.inl t => Spec.blockOutputs t
    | Sum.inr t => Spec.blockOutputs t

class inductive Has : (a: Type u) → [Spec a] → (b: Type u) → [Spec b] → Type _ where
| here {α : Type u} [s : Spec α] : Has α α
| inl {α β γ : Type u} [Spec α] [Spec β] [Spec γ] : Has α β → Has α (β ⊕ γ)
| inr {α β γ : Type u} [Spec α] [Spec β] [Spec γ] : Has α γ → Has α (β ⊕ γ)

instance [Spec α] : Has α α := Has.here
instance [Spec α] [Spec β] [Spec γ] [r: Has α β] : Has α (β ⊕ γ) := Has.inl r
instance [Spec α] [Spec β] [Spec γ] [r: Has α γ] : Has α (β ⊕ γ) := Has.inr r

def Has.mk {α β} [Spec α] [Spec β] [r: Has α β] : α → β
| a => match r with
  | Has.here => a
  | Has.inl r => Sum.inl (Has.mk a)
  | Has.inr r => Sum.inr (Has.mk a)

def Has.out {α β} [Spec α] [Spec β] [r: Has α β] : β → Option α
| b => match r, b with
  | Has.here, b => some b
  | Has.inl _, Sum.inl a => Has.out a
  | Has.inl _, Sum.inr _ => none
  | Has.inr _, Sum.inl _ => none
  | Has.inr _, Sum.inr a => Has.out a

def Step (T : Type u) [Spec T] : IxPoly.Endo (Type v) where
  Tag := fun α => NodeTag T α
  Field := fun _=> NodeTag.fields
  Elem := fun _ => NodeTag.elem

structure Tau : Type u
instance : Spec Tau where
  input := fun _ => PUnit
  output := fun _ => PUnit
  blockTag := fun _ => PEmpty
  blockInputs := fun _ => nofun
  blockOutputs := fun _ => nofun

structure Fail : Type u
instance : Spec Fail where
  input := fun _ => PUnit
  output := fun _ => PEmpty
  blockTag := fun _ => PEmpty
  blockInputs := fun _ => nofun
  blockOutputs := fun _ => nofun

namespace Step

def ret {E α Y} [Spec E] (x : α) : Step E Y α := ⟨.ret x, fun a => PEmpty.elim a⟩
def op {E α Y} [s: Spec E] (e : E) (inp : s.input e)
    (blocks : (t : s.blockTag e) → s.blockInputs e t → Y (s.blockOutputs e t))
    (k : (o : s.output e) → Y α) : Step E Y α :=
  ⟨.op e inp, fun
    | Sum.inl o => k o
    | Sum.inr ⟨t, i⟩ => blocks t i
  ⟩

def Has.liftInput {E F} [s: Spec E] [s' : Spec F] (h : Has F E) (e : F) (inp : s'.input e) : s.input (Has.mk e) :=
  match h with
  | Has.here => inp
  | Has.inl r => liftInput r e inp
  | Has.inr r => liftInput r e inp

def Has.lowerBlockTag {E F} [s: Spec E] [s' : Spec F] [h : Has F E] {e : F} (t : s.blockTag (Has.mk e)) : s'.blockTag e :=
  match h with
  | Has.here => t
  | Has.inl r => lowerBlockTag (h:=r) t
  | Has.inr r => lowerBlockTag (h:=r) t

def Has.lowerBlockInput {E F} [s: Spec E] [s' : Spec F] [h : Has F E]: {e : F} → (t : s.blockTag (Has.mk e)) →
    (i : s.blockInputs (Has.mk e) t) → s'.blockInputs e (lowerBlockTag t) :=
  match h with
  | Has.here => fun _ i => i
  | Has.inl r => fun t i => lowerBlockInput (h:=r) t i
  | Has.inr r => fun t i => lowerBlockInput (h:=r) t i

def Has.liftBlockOutput
    {E F} {Y : Type v → Type w}
    [s : Spec E] [s' : Spec F] [h : Has F E] :
    {e : F} →
    (t : s.blockTag (Has.mk e)) →
    Y (s'.blockOutputs e (Has.lowerBlockTag t)) →
    Y (s.blockOutputs (Has.mk e) t) := match h with
  | Has.here => fun _ x => x
  | Has.inl r => fun t x => liftBlockOutput (h:=r) t x
  | Has.inr r => fun t x => liftBlockOutput (h:=r) t x

def Has.lowerOutput
    {E F} [s : Spec E] [s' : Spec F] [h : Has F E]
    {e : F} (o : s.output (Has.mk e)) :
    s'.output e := match h with
  | Has.here => o
  | Has.inl r => lowerOutput (h:=r) o
  | Has.inr r => lowerOutput (h:=r) o

def Has.op {E F α Y} [s: Spec E] [s': Spec F] [h: Has F E] (e : F) (inp : s'.input e)
    (blocks : (t : s'.blockTag e) → s'.blockInputs e t → Y (s'.blockOutputs e t))
    (k : (o : s'.output e) → Y α) : Step E Y α :=
  Step.op (Has.mk e)
     (Has.liftInput h e inp)
     (fun t i => Has.liftBlockOutput t $ blocks (Has.lowerBlockTag t) (Has.lowerBlockInput t i))
     (fun o => k (Has.lowerOutput o))

 theorem Has.liftBlockOutput_naturality
      {E F} {Y : Type v → Type w} {Z : Type v → Type z}
      [s : Spec E] [s' : Spec F] [h : Has F E]
      (f : (α : Type v) → Y α → Z α) {e : F}
      (t : s.blockTag (Has.mk e))
      (x : Y (s'.blockOutputs e (Has.lowerBlockTag t))) :
      f _ (Has.liftBlockOutput (Y := Y) t x) =
        Has.liftBlockOutput (Y := Z) t (f _ x) := by
    induction h with
    | here => rfl
    | inl r ih => exact ih t x
    | inr r ih => exact ih t x

def tau {E α Y} [Spec E] [Has Tau E] (x : Y α) : Step E Y α := Has.op Tau.mk () nofun (fun () => x)

def fail {E α Y} [Spec E] [Has Fail E] : Step E Y α := Has.op Fail.mk () nofun nofun

protected def casesOn {E Y} [Spec E] { motive : (α : Type _) → Step E Y α → Sort* } {α} (x : Step E Y α)
    (ret : ∀ {α} x, motive α (ret x))
    (op : ∀ {α} e inp blocks k, motive α (op e inp blocks k)):
    motive α x := by
  rcases x with ⟨tag, fields⟩
  cases tag with
  | ret a =>
    convert ret a
    simp only [Step.ret]
    congr 2
    ext a; cases a
  | op e inp =>
    convert op e inp (fun t i => fields (.inr ⟨t, i⟩)) (fun o => fields (.inl o))
    simp only [Step.op]
    congr 2
    ext a; cases a <;> rfl

@[simp]
theorem map_ret {E} [Spec E] {Y Z : Type _ → Type _} {f : (α : Type _) → Y α → Z α} {α : Type _} {x : α}:
    IxPoly.map (F := Step E) f α (Step.ret x) = Step.ret x := by
  simp only [IxPoly.map, ret]
  congr 1
  ext a; cases a



-- @[simp]
-- theorem map_fail {E} {Y Z : Type _ → Type _} {f : (α : Type _) → Y α → Z α} {α : Type _}:
--     IxPoly.map (F := Step E) f α (Step.fail) = Step.fail := by
--   simp only [IxPoly.map, fail]
--   congr 1
--   ext a; cases a

@[simp]
theorem map_op {E} [h: Spec E] {Y Z : Type _ → Type _} {f : (α : Type _) → Y α → Z α} {α : Type _}
    {e : E} {inp : h.input e}
    {blocks : (t : h.blockTag e) → h.blockInputs e t → Y (h.blockOutputs e t)}
    {k : (o : h.output e) → Y α}:
    IxPoly.map (F := Step E) f α (Step.op e inp blocks k) =
      Step.op e inp (fun t i => f _ (blocks t i)) (fun o => f _ (k o)) := by
  simp only [IxPoly.map, op]
  congr 1
  ext a; cases a <;> rfl

  @[simp]
  theorem map_hasOp
      {E F} [Spec E] [Spec F] [Has F E]
      {Y Z : Type _ → Type _}
      (f : (α : Type _) → Y α → Z α) {α}
      (e : F) (inp : Spec.input e)
      (blocks :
        (t : Spec.blockTag e) →
        Spec.blockInputs e t →
        Y (Spec.blockOutputs e t))
      (k : Spec.output e → Y α) :
      IxPoly.map (F := Step E) f α (Has.op e inp blocks k) =
        Has.op e inp
          (fun t i => f _ (blocks t i))
          (fun o => f _ (k o)) := by
    unfold Has.op
    rw [map_op]
    congr 1
    funext t i
    apply Has.liftBlockOutput_naturality

@[simp]
theorem map_tau {E} [Spec E] [Has Tau E] {Y Z : Type _ → Type _} {f : (α : Type _) → Y α → Z α} {α : Type _} {x : Y α}:
    IxPoly.map (F := Step E) f α (Step.tau x) = Step.tau (f α x) := by
  simp only [tau, map_hasOp]
  congr 1
  ext a
  cases a

end Step

end Freigen.Eff
