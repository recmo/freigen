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

inductive Compat.SumRel {S : HSig.{u, w}} {T : HSig.{v, x}}
    {F : HSig.{u, w}} {G : HSig.{v, x}} (C : Compat S T) (D : Compat F G) :
    (S.op ⊕ F.op) → (T.op ⊕ G.op) → Type (max u v w x) where
  | inl {e h} : C.opRel e h → SumRel C D (.inl e) (.inl h)
  | inr {e h} : D.opRel e h → SumRel C D (.inr e) (.inr h)

def Compat.sum {S : HSig.{u, w}} {T : HSig.{v, x}}
    {F : HSig.{u, w}} {G : HSig.{v, x}} (C : Compat S T) (D : Compat F G) :
    Compat (HSig.sum S F) (HSig.sum T G) where
  opRel := SumRel C D
  input
    | .inl w => C.input w
    | .inr w => D.input w
  output
    | .inl w => C.output w
    | .inr w => D.output w
  branch
    | .inl w => C.branch w
    | .inr w => D.branch w
  branchInput
    | .inl w, h => C.branchInput w h
    | .inr w, h => D.branchInput w h
  branchOutput
    | .inl w, h => C.branchOutput w h
    | .inr w, h => D.branchOutput w h

def Compat.call {σ : Type u} {ρ : Type u} {σ' : Type v} {ρ' : Type v}
    (argRel : σ → σ' → Prop) (resultRel : ρ → ρ' → Prop) :
    Compat (Call.{u, w} σ ρ) (Call.{v, x} σ' ρ') where
  opRel
    | .call, .call => ULift.{max u v w x, 0} Unit
  input _ := argRel
  output _ := resultRel
  branch _ source _ := nomatch source
  branchInput _ h := nomatch h
  branchOutput _ h := nomatch h

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

theorem Eutt.congr {α : Type u} {β : Type v} {r : α → β → Prop}
    {x x' : CompE S α} {y y' : CompE T β}
    (hx : x = x') (hy : y = y') (h : Eutt C r x y) : Eutt C r x' y' := by
  cases hx
  cases hy
  exact h

theorem Eutt.tauR {α : Type u} {β : Type v} {r : α → β → Prop}
    {x : CompE S α} {y : CompE T β} (h : Eutt C r x y) :
    Eutt C r x (tau y) :=
  Eutt.of_step C (.tauR r y (eutt_closed C h))

theorem Eutt.tauL {α : Type u} {β : Type v} {r : α → β → Prop}
    {x : CompE S α} {y : CompE T β} (h : Eutt C r x y) :
    Eutt C r (tau x) y :=
  Eutt.of_step C (.tauL r x (eutt_closed C h))

/-- Relational bind congruence.  The intermediate result relation determines which pairs of
    continuations must themselves be bisimilar. -/
theorem Eutt.bind {α : Type u} {β : Type v} {γ : Type u} {δ : Type v}
    {r : α → β → Prop} {q : γ → δ → Prop}
    {m : CompE S α} {n : CompE T β} (hm : Eutt C r m n)
    (ks : α → CompE S γ) (kt : β → CompE T δ)
    (hk : ∀ a b, r a b → Eutt C q (ks a) (kt b)) :
    Eutt C q (bind m ks) (bind n kt) := by
  let R := fun (γ : Type u) (δ : Type v) (q : γ → δ → Prop)
      (x : CompE S γ) (y : CompE T δ) =>
    Eutt C q x y ∨
      ∃ (α : Type u) (β : Type v) (r : α → β → Prop)
        (m : CompE S α) (n : CompE T β)
        (ks : α → CompE S γ) (kt : β → CompE T δ),
        x = CompE.bind m ks ∧ y = CompE.bind n kt ∧ Eutt C r m n ∧
          ∀ a b, r a b → Eutt C q (ks a) (kt b)
  refine ⟨R, ?_, Or.inr ⟨α, β, r, m, n, ks, kt, rfl, rfl, hm, hk⟩⟩
  intro γ δ q x y hxy
  rcases hxy with hxy | ⟨α, β, r, m, n, ks, kt, rfl, rfl, hm, hk⟩
  · exact (eutt_closed C hxy).mono C (fun _ _ _ _ _ h => Or.inl h)
  · let go {m : CompE S α} {n : CompE T β}
        (step : EuttF C (fun _ _ r x y => Eutt C r x y) r m n) :
        EuttF C R q (CompE.bind m ks) (CompE.bind n kt) := by
        induction step with
        | ret a b h =>
            rw [bind_ret, bind_ret]
            exact (eutt_closed C (hk a b h)).mono C (fun _ _ _ _ _ h => Or.inl h)
        | fail =>
            rw [bind_fail, bind_fail]
            exact .fail q
        | tau mx ny h =>
            rw [bind_tau, bind_tau]
            exact .tau q (CompE.bind mx ks) (CompE.bind ny kt)
              (Or.inr ⟨_, _, _, mx, ny, ks, kt, rfl, rfl, h, hk⟩)
        | tauL mx h ih =>
            rw [bind_tau]
            exact .tauL q (CompE.bind mx ks) ih
        | tauR ny h ih =>
            rw [bind_tau]
            exact .tauR q (CompE.bind ny kt) ih
        | op w sourceInput targetInput hi sourceBlocks sourceK targetBlocks targetK hb ho =>
            rw [bind_assoc, bind_assoc]
            exact .op q w sourceInput targetInput hi sourceBlocks
              (fun o => CompE.bind (sourceK o) ks) targetBlocks
              (fun o => CompE.bind (targetK o) kt)
              (fun bs bt hbr xs xt hx => Or.inl (hb bs bt hbr xs xt hx))
              (fun os ot hot => Or.inr
                ⟨_, _, _, sourceK os, targetK ot, ks, kt, rfl, rfl,
                  (ho os ot hot), hk⟩)
    exact go (eutt_closed C hm)

end CompE
end ITree2
end Freigen
