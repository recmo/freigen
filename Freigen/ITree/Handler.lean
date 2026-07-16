import Freigen.ITree.Basic

/-!
# Indexed handler equations

One-step equations for interpreting a handler at either the public result fiber or a scoped block
fiber. The higher-level call-closing bisimulation lives in `Freigen.Ast.Run`.
-/

namespace Freigen
namespace ITree

universe u v w x y z

namespace CompE

variable {T : HSig.{v, x}}

private theorem mapStep_ret {β : Type v} {X : Ix T → Type y} {Y : Ix T → Type z}
    (f : ∀ i, X i → Y i) {i : Ix T} (value : result T β i) :
    (P T β).map f (Step.ret value : Step T β X i) = Step.ret value := by
  simp only [IxPFunctor.map, Step.ret]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext impossible
  nomatch impossible

private theorem mapStep_fail {β : Type v} {X : Ix T → Type y} {Y : Ix T → Type z}
    (f : ∀ i, X i → Y i) {i : Ix T} :
    (P T β).map f (Step.fail : Step T β X i) = Step.fail := by
  simp only [IxPFunctor.map, Step.fail]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext impossible
  nomatch impossible

private theorem mapStep_tau {β : Type v} {X : Ix T → Type y} {Y : Ix T → Type z}
    (f : ∀ i, X i → Y i) {i : Ix T} (child : X i) :
    (P T β).map f (Step.tau child) = Step.tau (f i child) := by
  simp only [IxPFunctor.map, Step.tau]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar
  rfl

private theorem mapStep_op {β : Type v} {X : Ix T → Type y} {Y : Ix T → Type z}
    (f : ∀ i, X i → Y i) {i : Ix T}
    (operation : T.op) (input : T.input operation)
    (blocks : (branch : T.Block operation) → X (.block operation branch))
    (continuation : T.output operation → X i) :
    (P T β).map f (Step.op operation input blocks continuation) =
      Step.op operation input
        (fun branch => f _ (blocks branch))
        (fun output => f _ (continuation output)) := by
  simp only [IxPFunctor.map, Step.op]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar <;> rfl

@[simp] theorem interpHandlerAt_ret {H F : HSig.{u, w}} (handler : Handler H F)
    {α : Type u} {i : Ix H} (value : result H α i) :
    interpHandlerAt handler
      (retAt (H := Sum H F) (α := α) (i := handlerSourceIx i)
        (handlerResultIn i value)) = retAt value := by
  cases i with
  | normal => exact interpHandler_ret handler value
  | block operation branch =>
      apply eq_of_destAt_eq
      rw [interpHandlerAt, dest_corecAt]
      change (P H α).map
          (fun i => corecAt (interpHandlerCo handler) (i := i))
          (interpHandlerCo handler (.block operation branch)
            (retAt (H := Sum H F) (α := α)
              (i := .block (.inl operation) branch) value)) =
        destAt (retAt value)
      rw [interpHandlerCo, dest_retAt, dest_retAt]
      exact mapStep_ret _ _

@[simp] theorem interpHandlerAt_tau {H F : HSig.{u, w}} (handler : Handler H F)
    {α : Type u} {i : Ix H} (tree : HandlerState H F α i) :
    interpHandlerAt handler (tauAt tree) = tauAt (interpHandlerAt handler tree) := by
  cases i with
  | normal => exact interpHandler_tau handler tree
  | block operation branch =>
      apply eq_of_destAt_eq
      rw [interpHandlerAt, dest_corecAt]
      change (P H α).map
          (fun i => corecAt (interpHandlerCo handler) (i := i))
          (interpHandlerCo handler (.block operation branch) (tauAt tree)) =
        destAt (tauAt (interpHandlerAt handler tree))
      rw [interpHandlerCo, dest_tauAt, dest_tauAt]
      exact mapStep_tau _ _

@[simp] theorem interpHandlerAt_fail {H F : HSig.{u, w}} (handler : Handler H F)
    {α : Type u} {i : Ix H} :
    interpHandlerAt handler (failAt : HandlerState H F α i) = failAt := by
  cases i with
  | normal => exact interpHandler_fail handler
  | block operation branch =>
      apply eq_of_destAt_eq
      rw [interpHandlerAt, dest_corecAt]
      change (P H α).map
          (fun i => corecAt (interpHandlerCo handler) (i := i))
          (interpHandlerCo handler (.block operation branch)
            (failAt : Tree (Sum H F) α (.block (.inl operation) branch))) =
        destAt failAt
      rw [interpHandlerCo, dest_failAt, dest_failAt]
      exact mapStep_fail _

theorem interpHandlerAt_op_left {H F : HSig.{u, w}} (handler : Handler H F)
    {α : Type u} {i : Ix H} (operation : H.op) (input : H.input operation)
    (blocks : (branch : H.Block operation) →
      HandlerState H F α (.block operation branch))
    (continuation : H.output operation → HandlerState H F α i) :
    interpHandlerAt handler (opAt (.inl operation) input blocks continuation) =
      opAt operation input
        (fun branch => interpHandlerAt handler (blocks branch))
        (fun output => interpHandlerAt handler (continuation output)) := by
  apply eq_of_destAt_eq
  rw [interpHandlerAt, dest_corecAt]
  cases i with
  | normal =>
      change (P H α).map
          (fun i => corecAt (interpHandlerCo handler) (i := i))
          (interpHandlerCoNormal handler
            (opAt (.inl operation) input blocks continuation)) = _
      have step : interpHandlerCoNormal handler
          (opAt (Sum.inl operation) input blocks continuation) =
          Step.op (H := H) operation input blocks continuation := by
        unfold interpHandlerCoNormal
        rw [show dest (opAt (Sum.inl operation) input blocks continuation) =
          Step.op (H := Sum H F) (Sum.inl operation) input blocks continuation from
            dest_opAt _ _ _ _]
        rfl
      rw [step, dest_opAt]
      exact mapStep_op _ _ _ _ _
  | block root branch =>
      change (P H α).map
          (fun i => corecAt (interpHandlerCo handler) (i := i))
          (interpHandlerCo handler (.block root branch)
            (opAt (.inl operation) input blocks continuation)) = _
      rw [interpHandlerCo, dest_opAt, dest_opAt]
      exact mapStep_op _ _ _ _ _

theorem interpHandlerAt_op_right {H F : HSig.{u, w}} (handler : Handler H F)
    {α : Type u} {i : Ix H} (operation : F.op) (input : F.input operation)
    (blocks : (branch : F.Block operation) →
      Tree (Sum H F) α (.block (.inr operation) branch))
    (continuation : F.output operation → HandlerState H F α i) :
    interpHandlerAt handler (opAt (.inr operation) input blocks continuation) =
      tauAt (interpHandlerAt handler
        (bindAt
          (@handler α operation input fun branch branchInput =>
            blocks ⟨branch, branchInput⟩)
          continuation)) := by
  apply eq_of_destAt_eq
  rw [interpHandlerAt, dest_corecAt]
  cases i with
  | normal =>
      change (P H α).map
          (fun i => corecAt (interpHandlerCo handler) (i := i))
          (interpHandlerCoNormal handler
            (opAt (.inr operation) input blocks continuation)) = _
      let child := bindAt
        (@handler α operation input fun branch branchInput =>
          blocks ⟨branch, branchInput⟩) continuation
      have step : interpHandlerCoNormal handler
          (opAt (Sum.inr operation) input blocks continuation) =
          @Step.tau H α (HandlerState H F α) .normal child := by
        unfold interpHandlerCoNormal
        rw [show dest (opAt (Sum.inr operation) input blocks continuation) =
          Step.op (H := Sum H F) (Sum.inr operation) input blocks continuation from
            dest_opAt _ _ _ _]
        rfl
      rw [step, dest_tauAt]
      exact mapStep_tau _ _
  | block root branch =>
      change (P H α).map
          (fun i => corecAt (interpHandlerCo handler) (i := i))
          (interpHandlerCo handler (.block root branch)
            (opAt (.inr operation) input blocks continuation)) = _
      rw [interpHandlerCo, dest_opAt, dest_tauAt]
      exact mapStep_tau _ _

end CompE
end ITree
end Freigen
