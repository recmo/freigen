import Freigen.IxPoly.Basic

namespace Freigen.Eff

structure Spec where
  tag : Type u
  input : tag → Type v
  output : tag → Type v
  blockTag : tag → Type u
  blockInputs : (t : tag) → blockTag t → Type v
  blockOutputs : (t : tag) → blockTag t → Type v

inductive NodeTag (E : Spec) : Type _ → Type _ where
| ret {R} : R → NodeTag E R
| tau {R} : NodeTag E R
| fail {R} : NodeTag E R
| op {R} (e : E.tag) : E.input e → NodeTag E R

def NodeTag.fields {i} {E : Spec}: NodeTag E i → Type _
| ret _ => PEmpty
| tau => PUnit
| fail => PEmpty
| op e _ => E.output e ⊕ ((t : E.blockTag e) × E.blockInputs e t)

def NodeTag.elem {E : Spec} {α : Type _} : (t : NodeTag E α) → (p : t.fields) → Type _
| ret _, x => nomatch x
| fail, x => nomatch x
| tau, () => α
| op _ _, Sum.inl _ => α
| op e _, Sum.inr ⟨o, _⟩ => E.blockOutputs e o

def Step (E : Spec) : IxPoly.Endo (Type _) where
  Tag := fun α => NodeTag E α
  Field := fun _=> NodeTag.fields
  Elem := fun _ => NodeTag.elem

namespace Step

def ret {E α Y} (x : α) : Step E Y α := ⟨.ret x, fun a => PEmpty.elim a⟩
def tau {E α Y} (x : Y α) : Step E Y α := ⟨.tau, fun () => x⟩
def fail {E α Y} : Step E Y α := ⟨.fail, fun a => PEmpty.elim a⟩
def op {E α Y} (e : E.tag) (inp : E.input e)
    (blocks : (t : E.blockTag e) → E.blockInputs e t → Y (E.blockOutputs e t))
    (k : (o : E.output e) → Y α) : Step E Y α :=
  ⟨.op e inp, fun
    | Sum.inl o => k o
    | Sum.inr ⟨t, i⟩ => blocks t i
  ⟩

protected def casesOn {E Y} { motive : (α : Type _) → Step E Y α → Sort* } {α} (x : Step E Y α)
    (ret : ∀ {α} x, motive α (ret x))
    (tau : ∀ {α} x, motive α (tau x))
    (fail : ∀ {α}, motive α fail)
    (op : ∀ {α} e inp blocks k, motive α (op e inp blocks k)):
    motive α x := by
  rcases x with ⟨tag, fields⟩
  cases tag with
  | ret a =>
    convert ret a
    simp only [Step.ret]
    congr 2
    ext a; cases a
  | tau =>
    convert tau (fields ())
    · rfl
    · simp only [Step.tau]
      congr
  | fail =>
    convert fail
    simp only [Step.fail]
    congr 2
    ext a; cases a
  | op e inp =>
    convert op e inp (fun t i => fields (.inr ⟨t, i⟩)) (fun o => fields (.inl o))
    simp only [Step.op]
    congr 2
    ext a; cases a <;> rfl

@[simp]
theorem map_ret {E} {Y Z : Type _ → Type _} {f : (α : Type _) → Y α → Z α} {α : Type _} {x : α}:
    IxPoly.map (F := Step E) f α (Step.ret x) = Step.ret x := by
  simp only [IxPoly.map, ret]
  congr 1
  ext a; cases a

@[simp]
theorem map_tau {E} {Y Z : Type _ → Type _} {f : (α : Type _) → Y α → Z α} {α : Type _} {x : Y α}:
    IxPoly.map (F := Step E) f α (Step.tau x) = Step.tau (f α x) := by
  simp only [IxPoly.map, tau]
  congr 1

@[simp]
theorem map_fail {E} {Y Z : Type _ → Type _} {f : (α : Type _) → Y α → Z α} {α : Type _}:
    IxPoly.map (F := Step E) f α (Step.fail) = Step.fail := by
  simp only [IxPoly.map, fail]
  congr 1
  ext a; cases a

@[simp]
theorem map_op {E} {Y Z : Type _ → Type _} {f : (α : Type _) → Y α → Z α} {α : Type _}
    {e : E.tag} {inp : E.input e}
    {blocks : (t : E.blockTag e) → E.blockInputs e t → Y (E.blockOutputs e t)}
    {k : (o : E.output e) → Y α}:
    IxPoly.map (F := Step E) f α (Step.op e inp blocks k) =
      Step.op e inp (fun t i => f _ (blocks t i)) (fun o => f _ (k o)) := by
  simp only [IxPoly.map, op]
  congr 1
  ext a; cases a <;> rfl

theorem tau_def {E} {Y : Type _ → Type _} {α : Type _} {x : Y α}:
    Step.tau (E := E) x = ⟨.tau, fun _ => x⟩ := by rfl

end Step

end Freigen.Eff
