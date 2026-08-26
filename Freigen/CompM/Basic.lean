import Freigen.ITree.Basic
import Freigen.ExactCodensity
import Freigen.Eff

namespace Freigen

def CompM
    {Γ : Type u} (E : Γ → Type u) [Eff.Spec E]
    (γ : Γ) (α : Type v) : Type _ :=
  ExactCodensity (ITree E γ) α

variable
  {Γ : Type u} {E : Γ → Type u} [eS : Eff.Spec E]
  {γ : Γ} {α β : Type}

instance {γ : Γ} : Monad (CompM E γ) :=
  inferInstanceAs (Monad (ExactCodensity (ITree E γ)))

instance {γ : Γ} : LawfulMonad (CompM E γ) :=
  inferInstanceAs (LawfulMonad (ExactCodensity (ITree E γ)))

namespace CompM

private def treeEquiv {γ : Γ} {α : Type v} :
    CompM E γ α ≃ ITree E γ α :=
  ExactCodensity.equiv

private def actionEquiv
    {I : Type ui} {O : Type uo}
    {F : IxPoly I O}
    {X : I → Type ux} {Y : I → Type uy}
    (e : (i : I) → X i ≃ Y i)
    (o : O) :
    F X o ≃ F Y o where
  toFun := IxPoly.map (fun i => e i) o
  invFun := IxPoly.map (fun i => (e i).symm) o
  left_inv x := by
    rw [IxPoly.map_map]
    simpa only [Equiv.symm_apply_apply] using IxPoly.map_id o x
  right_inv y := by
    rw [IxPoly.map_map]
    simpa only [Equiv.apply_symm_apply] using IxPoly.map_id o y

def observe {γ : Γ} {α : Type v} :
    CompM E γ α ≃
      Eff.Step Γ E (fun i => CompM E i.1 i.2) (γ, α) :=
  treeEquiv.trans <|
    ITree.observe.trans <|
      actionEquiv (fun _ => treeEquiv.symm) (γ, α)

def roll {γ : Γ} {α : Type v} :
    Eff.Step Γ E (fun i => CompM E i.1 i.2) (γ, α) →
      CompM E γ α :=
  observe.symm

@[simp]
theorem observe_roll
    {γ : Γ} {α : Type v}
    (x : Eff.Step Γ E (fun i => CompM E i.1 i.2) (γ, α)) :
    observe (roll x) = x :=
  observe.apply_symm_apply x

@[simp]
theorem roll_observe
    {γ : Γ} {α : Type v}
    (x : CompM E γ α) :
    roll (observe x) = x :=
  observe.symm_apply_apply x

def corec
    {A : Γ × Type v → Type w}
    (f : (i : Γ × Type v) → A i → Eff.Step Γ E A i)
    {i : Γ × Type v}
    (a : A i) :
    CompM E i.1 i.2 :=
  treeEquiv.symm (ITree.corec f a)

theorem observe_corec
    {A : Γ × Type v → Type w}
    (f : (i : Γ × Type v) → A i → Eff.Step Γ E A i)
    {i : Γ × Type v}
    (a : A i) :
    observe (corec f a) =
      IxPoly.map
        (fun _ y => corec f y)
        i
        (f i a) := by
  change
    IxPoly.map (fun _ x => treeEquiv.symm x) i
      (ITree.observe
        (treeEquiv (treeEquiv.symm (ITree.corec f a)))) =
    IxPoly.map (fun _ y => treeEquiv.symm (ITree.corec f y)) i (f i a)
  rw [Equiv.apply_symm_apply, ITree.observe_corec]
  rw [IxPoly.map_map]

theorem eq_of_observe_eq
    {γ : Γ} {α : Type v}
    {x y : CompM E γ α}
    (h : observe x = observe y) :
    x = y :=
  observe.injective h

private theorem bind_def
    {γ : Γ} {α β : Type}
    (x : CompM E γ α) (f : α → CompM E γ β) :
    x >>= f = ⟨fun g => x.run fun a => (f a).run g, by
      intros
      conv => lhs; rw [←x.exact]
      rw [bind_assoc]
      simp only [ExactCodensity.exact]⟩ := by
  rfl

def tick {γ : Γ} [Eff.Has.{u, 0} Eff.Tau E] :
    CompM E γ Unit :=
  ⟨fun f => ITree.tau (f ()), by simp⟩

def fail {γ : Γ} [Eff.Has Eff.Fail E] :
    CompM E γ α :=
  ⟨fun _ => ITree.fail, by simp⟩

def op {γ : Γ} (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)) :
    CompM E γ (eS.output γ e) :=
  ⟨fun f => ITree.op e (fun t i => (blocks t i).run pure) f, by simp⟩

private def liftLCo
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    (i : Γ × Type v) (x : CompM L i.1 i.2) :
    Eff.Step Γ (L ⊕ₑ R) (fun i => CompM L i.1 i.2) i :=
  Eff.Step.casesOn (observe x)
    (motive := fun i _ =>
      Eff.Step Γ (L ⊕ₑ R) (fun i => CompM L i.1 i.2) i)
    (fun value => Eff.Step.ret value)
    (fun e blocks k =>
      Eff.Step.op (show (L ⊕ₑ R) _ from Sum.inl e) blocks k)

def liftL
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    {γ : Γ} {α : Type v} (x : CompM L γ α) :
    CompM (L ⊕ₑ R) γ α :=
  corec (i := (γ, α)) (liftLCo (L := L) (R := R)) x

private def liftRCo
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    (i : Γ × Type v) (x : CompM R i.1 i.2) :
    Eff.Step Γ (L ⊕ₑ R) (fun i => CompM R i.1 i.2) i :=
  Eff.Step.casesOn (observe x)
    (motive := fun i _ =>
      Eff.Step Γ (L ⊕ₑ R) (fun i => CompM R i.1 i.2) i)
    (fun value => Eff.Step.ret value)
    (fun e blocks k =>
      Eff.Step.op (show (L ⊕ₑ R) _ from Sum.inr e) blocks k)

def liftR
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    {γ : Γ} {α : Type v} (x : CompM R γ α) :
    CompM (L ⊕ₑ R) γ α :=
  corec (i := (γ, α)) (liftRCo (L := L) (R := R)) x

abbrev OpMap
    {Γ : Type u} (L R : Γ → Type u)
    [Eff.Spec.{u, v} L] [Eff.Spec.{u, v} R]
    (X : Γ × Type v → Type w) :=
  {i : Γ × Type v} → Eff.Step Γ L X i → Eff.Step Γ R X i

private def interpLCo
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    (mapOp : OpMap L R (fun i => CompM (L ⊕ₑ R) i.1 i.2))
    (i : Γ × Type v) (x : CompM (L ⊕ₑ R) i.1 i.2) :
    Eff.Step Γ R (fun i => CompM (L ⊕ₑ R) i.1 i.2) i :=
  Eff.Step.casesOn (observe x)
    (motive := fun i _ =>
      Eff.Step Γ R (fun i => CompM (L ⊕ₑ R) i.1 i.2) i)
    (fun value => Eff.Step.ret value)
    (fun e blocks k => match e with
      | .inl e => mapOp (Eff.Step.op e blocks k)
      | .inr e => Eff.Step.op e blocks k)

def interpL
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    {γ : Γ} {α : Type v} (x : CompM (L ⊕ₑ R) γ α)
    (mapOp : OpMap L R (fun i => CompM (L ⊕ₑ R) i.1 i.2)) :
    CompM R γ α :=
  corec (i := (γ, α)) (interpLCo mapOp) x

private def interpRCo
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    (mapOp : OpMap R L (fun i => CompM (L ⊕ₑ R) i.1 i.2))
    (i : Γ × Type v) (x : CompM (L ⊕ₑ R) i.1 i.2) :
    Eff.Step Γ L (fun i => CompM (L ⊕ₑ R) i.1 i.2) i :=
  Eff.Step.casesOn (observe x)
    (motive := fun i _ =>
      Eff.Step Γ L (fun i => CompM (L ⊕ₑ R) i.1 i.2) i)
    (fun value => Eff.Step.ret value)
    (fun e blocks k => match e with
      | .inl e => Eff.Step.op e blocks k
      | .inr e => mapOp (Eff.Step.op e blocks k))

def interpR
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    {γ : Γ} {α : Type v} (x : CompM (L ⊕ₑ R) γ α)
    (mapOp : OpMap R L (fun i => CompM (L ⊕ₑ R) i.1 i.2)) :
    CompM L γ α :=
  corec (i := (γ, α)) (interpRCo mapOp) x

def loop
    {γ : Γ} [Eff.Has Eff.Tau E]
    (body : α → CompM E γ (α ⊕ β)) (init : α) :
    CompM E γ β := {
  run := fun f => ITree.loop (fun a => (body a).run pure) init f
  exact := by
    intros
    apply ITree.loop_bind
}

theorem loop_def [Eff.Has Eff.Tau E]
  (body : α → CompM E γ (α ⊕ β))
  (s : α) :
  CompM.loop body s =
    body s >>= fun
      | .inr v  => pure v
      | .inl v => CompM.tick (E := E) (γ := γ) *> CompM.loop body v := by
  apply ExactCodensity.equiv.injective
  change (CompM.loop body s).run pure =
    ((body s >>= fun
      | .inr v => pure v
      | .inl v =>
        CompM.tick (E := E) (γ := γ) *> CompM.loop body v) :
        CompM E γ β).run pure
  simp only [loop, bind_def]
  rw [ITree.loop_def]
  rw [ExactCodensity.exact]
  congr 1
  funext x
  cases x <;> rfl

abbrev forInStepToSum : ForInStep α → α ⊕ α
  | .yield x => .inl x
  | .done x => .inr x

instance {γ : Γ} [Eff.Has Eff.Tau E] :
    ForIn (CompM E γ) Lean.Loop Unit where
  forIn _ init body := loop (fun a => forInStepToSum <$> (body () a)) init

end Freigen.CompM
