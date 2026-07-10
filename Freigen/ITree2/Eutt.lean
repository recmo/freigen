import Freigen.ITree2.Basic

namespace Freigen
namespace ITree2

universe u v w x

namespace HSig

/-- How operations in two higher-order signatures correspond. -/
structure Compat (S : HSig.{u, w}) (T : HSig.{v, x}) where
  opRel : S.op → T.op → Type (max u v w x)
  input : {e : S.op} → {h : T.op} → opRel e h → S.input e → T.input h → Prop
  output : {e : S.op} → {h : T.op} → opRel e h → S.output e → T.output h → Prop
  branch : {e : S.op} → {h : T.op} → opRel e h → S.branch e → T.branch h → Prop
  branchInput : {e : S.op} → {h : T.op} → (w : opRel e h) →
    {bs : S.branch e} → {bt : T.branch h} → branch w bs bt →
    S.branchInput e bs → T.branchInput h bt → Prop
  branchOutput : {e : S.op} → {h : T.op} → (w : opRel e h) →
    {bs : S.branch e} → {bt : T.branch h} → branch w bs bt →
    S.branchOutput e bs → T.branchOutput h bt → Prop

def Compat.refl (H : HSig.{u, w}) : Compat H H where
  opRel e h := ULift.{max u w, 0} (PLift.{0} (e = h))
  input
    | ⟨⟨rfl⟩⟩ => Eq
  output
    | ⟨⟨rfl⟩⟩ => Eq
  branch
    | ⟨⟨rfl⟩⟩ => Eq
  branchInput
    | ⟨⟨rfl⟩⟩, rfl => Eq
  branchOutput
    | ⟨⟨rfl⟩⟩, rfl => Eq

end HSig

namespace CompE

variable {S : HSig.{u, w}} {T : HSig.{v, x}} (C : HSig.Compat S T)

/-- One weak-bisimulation step under a correspondence between higher-order signatures. -/
inductive EuttF
    (R : (α : Type u) → (β : Type v) → (α → β → Prop) → CompE S α → CompE T β → Prop) :
    {α : Type u} → {β : Type v} → (α → β → Prop) → CompE S α → CompE T β → Prop where
  | ret (r : α → β → Prop) (a : α) (b : β) (h : r a b) : EuttF R r (ret a) (ret b)
  | fail (r : α → β → Prop) : EuttF R r (fail (H := S)) (fail (H := T))
  | tau (r : α → β → Prop) (x : CompE S α) (y : CompE T β) (h : R α β r x y) :
      EuttF R r (tau x) (tau y)
  | tauL (r : α → β → Prop) (x : CompE S α) {y : CompE T β} (h : EuttF R r x y) :
      EuttF R r (tau x) y
  | tauR (r : α → β → Prop) {x : CompE S α} (y : CompE T β) (h : EuttF R r x y) :
      EuttF R r x (tau y)
  | op (r : α → β → Prop) {e : S.op} {h : T.op} (w : C.opRel e h)
      (sourceInput : S.input e) (targetInput : T.input h)
      (hi : C.input w sourceInput targetInput)
      (sourceBlocks : (b : S.branch e) → S.branchInput e b →
        CompE S (S.branchOutput e b))
      (sourceK : S.output e → CompE S α)
      (targetBlocks : (b : T.branch h) → T.branchInput h b →
        CompE T (T.branchOutput h b))
      (targetK : T.output h → CompE T β)
      (hb : ∀ bs bt, (hbr : C.branch w bs bt) → ∀ xs xt,
        C.branchInput w hbr xs xt →
        R _ _ (C.branchOutput w hbr) (sourceBlocks bs xs) (targetBlocks bt xt))
      (hk : ∀ os ot, C.output w os ot → R α β r (sourceK os) (targetK ot)) :
      EuttF R r
        (bind (op e sourceInput (fun bx => sourceBlocks bx.1 bx.2) ret) sourceK)
        (bind (op h targetInput (fun bx => targetBlocks bx.1 bx.2) ret) targetK)

/-- Weak bisimulation whose visible operations are matched through `C`. -/
def Eutt {α : Type u} {β : Type v} (r : α → β → Prop) (x : CompE S α) (y : CompE T β) : Prop :=
  ∃ R, (∀ α β r x y, R α β r x y → EuttF C R r x y) ∧ R α β r x y

theorem EuttF.mono
    {R R' : (α : Type u) → (β : Type v) → (α → β → Prop) → CompE S α → CompE T β → Prop}
    (hm : ∀ α β r x y, R α β r x y → R' α β r x y)
    {α : Type u} {β : Type v} {r : α → β → Prop} {x y} (h : EuttF C R r x y) :
    EuttF C R' r x y := by
  induction h with
  | ret => exact .ret _ _ _ ‹_›
  | fail => exact .fail _
  | tau x y h => exact .tau _ x y (hm _ _ _ _ _ h)
  | tauL x h ih => exact .tauL _ x ih
  | tauR y h ih => exact .tauR _ y ih
  | op w sourceInput targetInput hi sourceBlocks sourceK targetBlocks targetK hb hk =>
      exact .op _ w sourceInput targetInput hi sourceBlocks sourceK targetBlocks targetK
        (fun bs bt hbr xs xt hx => hm _ _ _ _ _ (hb bs bt hbr xs xt hx))
        (fun os ot ho => hm _ _ _ _ _ (hk os ot ho))

theorem eutt_closed {α : Type u} {β : Type v} {r : α → β → Prop} {x y}
    (h : Eutt C r x y) : EuttF C (fun _ _ r x y => Eutt C r x y) r x y := by
  obtain ⟨R, hR, hxy⟩ := h
  exact (hR α β r x y hxy).mono C (fun _ _ _ _ _ h => ⟨R, hR, h⟩)

theorem Eutt.of_step {α : Type u} {β : Type v} {r : α → β → Prop} {x y}
    (h : EuttF C (fun _ _ r x y => Eutt C r x y) r x y) : Eutt C r x y := by
  let R := fun (α : Type u) (β : Type v) (r : α → β → Prop) (x : CompE S α) (y : CompE T β) =>
    Eutt C r x y ∨ EuttF C (fun _ _ r x y => Eutt C r x y) r x y
  refine ⟨R, ?_, Or.inr h⟩
  intro α β r x y hxy
  rcases hxy with hxy | hxy
  · exact (eutt_closed C hxy).mono C (fun _ _ _ _ _ h => Or.inl h)
  · exact hxy.mono C (fun _ _ _ _ _ h => Or.inl h)

end CompE
end ITree2
end Freigen
