import Freigen.Ast.Basic
import Freigen.ITree.Handler

/-!
# Closing the global definition-call effect

Expressions denote to an open tree over visible target effects plus `Call ctx`. This module closes
that call effect with a completed definition telescope and proves the one scoped commuting law
needed by higher-order operation soundness.
-/

namespace Freigen.Ast

open ITree ITree.CompE

universe u v

/-! ## Closing ordinary computations -/

abbrev EvalM (H : Signature) (ctx : DefCtx) (α : Type) :=
  ITree.CompE (H.spec ctx) α

def Defs.run {H : Signature} {ctx : DefCtx}
    (defs : Defs H (Tp.denote ctx) ctx) (tree : OpenM H ctx α) :
    EvalM H ctx α :=
  ITree.CompE.interpHandler defs.callHandler tree

/-! ## Closing scoped operation blocks -/

private inductive RunBlockRel {H : Signature} {ctx : DefCtx}
    (defs : Defs H (Tp.denote ctx) ctx) (α : Type)
    (root : H.op) (rootBranch : (H.spec ctx).Block root) :
    (i : Ix (H.spec ctx)) → Tree (H.spec ctx) α i → Tree (H.spec ctx) α i → Prop where
  | root (tree : OpenM H ctx ((H.spec ctx).branchOutput root rootBranch.1)) :
      RunBlockRel defs α root rootBranch (.block root rootBranch)
        (interpHandlerAt defs.callHandler
          (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
            (e := .inl root) (b := ⟨rootBranch.1, rootBranch.2⟩) tree))
        (asBlock (α := α) (interpHandler defs.callHandler tree))
  | relabel {current : H.op} {currentBranch : (H.spec ctx).Block current}
      (tree : Tree (ITree.Sum (H.spec ctx) (Call ctx))
        ((H.spec ctx).branchOutput root rootBranch.1)
        (.block (.inl current) ⟨currentBranch.1, currentBranch.2⟩)) :
      RunBlockRel defs α root rootBranch (.block current currentBranch)
        (interpHandlerAt defs.callHandler
          (relabelBlock
            (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α) tree))
        (relabelBlock
          (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
          (interpHandlerAt defs.callHandler tree))
  | eq {i : Ix (H.spec ctx)} {left right : Tree (H.spec ctx) α i}
      (equal : left = right) : RunBlockRel defs α root rootBranch i left right

theorem Defs.run_asBlock {H : Signature} {ctx : DefCtx}
    (defs : Defs H (Tp.denote ctx) ctx) {α : Type}
    {root : H.op} {rootBranch : (H.spec ctx).Block root}
    (tree : OpenM H ctx ((H.spec ctx).branchOutput root rootBranch.1)) :
    interpHandlerAt defs.callHandler
        (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
          (e := .inl root) (b := ⟨rootBranch.1, rootBranch.2⟩) tree) =
      asBlock (α := α) (interpHandler defs.callHandler tree) := by
  refine IxPFunctor.M.bisim (P := P (H.spec ctx) α)
    (RunBlockRel defs α root rootBranch) ?_ _ _ (.root tree)
  intro i left right related
  cases related with
  | eq equal =>
      cases equal
      obtain ⟨position, children, equation⟩ : ∃ p c, destAt left = ⟨p, c⟩ :=
        ⟨_, _, rfl⟩
      exact ⟨position, children, children, equation, equation, fun _ => .eq rfl⟩
  | root tree =>
      rcases cases_view tree with
        ⟨value, rfl⟩ | rfl | ⟨child, rfl⟩ |
          ⟨operation, input, blocks, continuation, rfl⟩
      · have leftEq :
            interpHandlerAt (i := .block root rootBranch) defs.callHandler
                (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
                  (ret value)) =
              retAt (H := H.spec ctx) (α := α)
                (i := .block root rootBranch) value := by
            rw [asBlock_ret, interpHandlerAt_ret]
        have rightEq :
            asBlock (H := H.spec ctx) (α := α)
                (e := root) (b := rootBranch)
                (interpHandler defs.callHandler (ret value)) =
              retAt (H := H.spec ctx) (α := α)
                (i := .block root rootBranch) value := by
            rw [interpHandler_ret, asBlock_ret]
        rw [leftEq, rightEq]
        let step : Step (H.spec ctx) α (Tree (H.spec ctx) α)
            (.block root rootBranch) := Step.ret value
        exact ⟨step.1, step.2, step.2, raw_dest_mkAt step, raw_dest_mkAt step,
          fun impossible => nomatch impossible⟩
      · have leftEq :
            interpHandlerAt (i := .block root rootBranch) defs.callHandler
                (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
                  (e := .inl root) (b := ⟨rootBranch.1, rootBranch.2⟩)
                  (fail : OpenM H ctx _)) =
              (failAt : Tree (H.spec ctx) α (.block root rootBranch)) := by
            rw [asBlock_fail, interpHandlerAt_fail]
        have rightEq :
            asBlock (H := H.spec ctx) (α := α)
                (e := root) (b := rootBranch)
                (interpHandler defs.callHandler (fail : OpenM H ctx _)) =
              (failAt : Tree (H.spec ctx) α (.block root rootBranch)) := by
            rw [interpHandler_fail, asBlock_fail]
        rw [leftEq, rightEq]
        let step : Step (H.spec ctx) α (Tree (H.spec ctx) α)
            (.block root rootBranch) := Step.fail
        exact ⟨step.1, step.2, step.2, raw_dest_mkAt step, raw_dest_mkAt step,
          fun impossible => nomatch impossible⟩
      · have leftEq :
            interpHandlerAt (i := .block root rootBranch) defs.callHandler
                (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
                  (e := .inl root) (b := ⟨rootBranch.1, rootBranch.2⟩)
                  (tau child)) =
              tauAt (interpHandlerAt (i := .block root rootBranch) defs.callHandler
                (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
                  (e := .inl root) (b := ⟨rootBranch.1, rootBranch.2⟩)
                  child)) := by
            rw [asBlock_tau, interpHandlerAt_tau]
        have rightEq :
            asBlock (H := H.spec ctx) (α := α)
                (e := root) (b := rootBranch)
                (interpHandler defs.callHandler (tau child)) =
              tauAt (asBlock (H := H.spec ctx) (α := α)
                (e := root) (b := rootBranch)
                (interpHandler defs.callHandler child)) := by
            rw [interpHandler_tau, asBlock_tau]
        rw [leftEq, rightEq]
        let leftStep : Step (H.spec ctx) α (Tree (H.spec ctx) α)
            (.block root rootBranch) :=
          Step.tau (interpHandlerAt defs.callHandler
            (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α) child))
        let rightStep : Step (H.spec ctx) α (Tree (H.spec ctx) α)
            (.block root rootBranch) :=
          Step.tau (asBlock (α := α) (interpHandler defs.callHandler child))
        exact ⟨.tau, leftStep.2, rightStep.2,
          raw_dest_mkAt leftStep, raw_dest_mkAt rightStep, fun ar => by
            cases ar
            exact .root child⟩
      · cases operation with
        | inl visible =>
            have leftEq :
                interpHandlerAt (i := .block root rootBranch) defs.callHandler
                    (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
                      (e := .inl root) (b := ⟨rootBranch.1, rootBranch.2⟩)
                      (opAt (.inl visible) input blocks continuation)) =
                  opAt visible input
                    (fun branch => interpHandlerAt defs.callHandler
                      (relabelBlock
                        (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                        (blocks ⟨branch.1, branch.2⟩)))
                    (fun output => interpHandlerAt (i := .block root rootBranch)
                      defs.callHandler
                      (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
                        (e := .inl root) (b := ⟨rootBranch.1, rootBranch.2⟩)
                        (continuation output))) := by
              rw [asBlock_opAt, interpHandlerAt_op_left]
            have rightEq :
                asBlock (H := H.spec ctx) (α := α)
                    (e := root) (b := rootBranch)
                    (interpHandler defs.callHandler
                      (opAt (.inl visible) input blocks continuation)) =
                  opAt visible input
                    (fun branch => relabelBlock
                      (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                      (interpHandlerAt defs.callHandler
                        (blocks ⟨branch.1, branch.2⟩)))
                    (fun output => asBlock (H := H.spec ctx) (α := α)
                      (e := root) (b := rootBranch)
                      (interpHandler defs.callHandler (continuation output))) := by
              change asBlock (H := H.spec ctx) (α := α)
                  (e := root) (b := rootBranch)
                  (interpHandlerAt defs.callHandler
                    (opAt (.inl visible) input blocks continuation)) = _
              rw [interpHandlerAt_op_left, asBlock_opAt]
              rfl
            rw [leftEq, rightEq]
            let leftStep : Step (H.spec ctx) α (Tree (H.spec ctx) α)
                (.block root rootBranch) :=
              Step.op visible input
                (fun branch => interpHandlerAt defs.callHandler
                  (relabelBlock
                    (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                    (blocks ⟨branch.1, branch.2⟩)))
                (fun output => interpHandlerAt defs.callHandler
                  (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
                    (continuation output)))
            let rightStep : Step (H.spec ctx) α (Tree (H.spec ctx) α)
                (.block root rootBranch) :=
              Step.op visible input
                (fun branch => relabelBlock
                  (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                  (interpHandlerAt defs.callHandler (blocks ⟨branch.1, branch.2⟩)))
                (fun output => asBlock (α := α)
                  (interpHandler defs.callHandler (continuation output)))
            exact ⟨.op visible input, leftStep.2, rightStep.2,
              raw_dest_mkAt leftStep, raw_dest_mkAt rightStep, fun ar => by
                cases ar with
                | block branch => exact .relabel (blocks branch)
                | cont output => exact .root (continuation output)⟩
        | inr call =>
            cases call with
            | call fn =>
              cases fn with
              | mk ref captured =>
                let body := defs.denote .refl ref captured.unpack input
                let combined := ITree.CompE.bind body continuation
                have leftEq :
                    interpHandlerAt (i := .block root rootBranch) defs.callHandler
                        (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
                          (e := .inl root) (b := ⟨rootBranch.1, rootBranch.2⟩)
                          (opAt (.inr (.call (.mk ref captured))) input blocks
                            continuation)) =
                      tauAt (interpHandlerAt (i := .block root rootBranch)
                        defs.callHandler
                        (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
                          (e := .inl root) (b := ⟨rootBranch.1, rootBranch.2⟩)
                          combined)) := by
                  rw [asBlock_opAt, interpHandlerAt_op_right]
                  congr 2
                  change bindAt body
                      (fun output => asBlock
                        (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
                        (e := .inl root) (b := ⟨rootBranch.1, rootBranch.2⟩)
                        (continuation output)) =
                    asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
                      (e := .inl root) (b := ⟨rootBranch.1, rootBranch.2⟩)
                      combined
                  exact (asBlock_bind
                    (H := ITree.Sum (H.spec ctx) (Call ctx)) (γ := α)
                    (root := .inl root)
                    (branch := ⟨rootBranch.1, rootBranch.2⟩)
                    body continuation).symm
                have rightEq :
                    asBlock (H := H.spec ctx) (α := α)
                        (e := root) (b := rootBranch)
                        (interpHandler defs.callHandler
                          (opAt (.inr (.call (.mk ref captured))) input blocks
                            continuation)) =
                      tauAt (asBlock (H := H.spec ctx) (α := α)
                        (e := root) (b := rootBranch)
                        (interpHandler defs.callHandler combined)) := by
                  change asBlock (H := H.spec ctx) (α := α)
                      (e := root) (b := rootBranch)
                      (interpHandlerAt defs.callHandler
                        (opAt (.inr (.call (.mk ref captured))) input blocks
                          continuation)) = _
                  rw [interpHandlerAt_op_right]
                  change asBlock (H := H.spec ctx) (α := α)
                      (e := root) (b := rootBranch)
                      (tau (interpHandler defs.callHandler combined)) = _
                  rw [asBlock_tau]
                rw [leftEq, rightEq]
                let leftStep : Step (H.spec ctx) α (Tree (H.spec ctx) α)
                    (.block root rootBranch) :=
                  Step.tau (interpHandlerAt defs.callHandler
                    (asBlock (H := ITree.Sum (H.spec ctx) (Call ctx)) (α := α)
                      combined))
                let rightStep : Step (H.spec ctx) α (Tree (H.spec ctx) α)
                    (.block root rootBranch) :=
                  Step.tau (asBlock (α := α)
                    (interpHandler defs.callHandler combined))
                exact ⟨.tau, leftStep.2, rightStep.2,
                  raw_dest_mkAt leftStep, raw_dest_mkAt rightStep, fun ar => by
                    cases ar
                    exact .root combined⟩
  | @relabel current currentBranch tree =>
      rcases cases_viewAt tree with
        ⟨value, rfl⟩ | rfl | ⟨child, rfl⟩ |
          ⟨operation, input, blocks, continuation, rfl⟩
      · have leftEq :
            interpHandlerAt (i := .block current currentBranch) defs.callHandler
                (relabelBlock
                  (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                  (retAt value)) =
              retAt (H := H.spec ctx) (α := α)
                (i := .block current currentBranch) value := by
            rw [relabelBlock_retAt, interpHandlerAt_ret]
        have rightEq :
            relabelBlock
                (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                (interpHandlerAt (i := .block current currentBranch)
                  defs.callHandler (retAt value)) =
              retAt (H := H.spec ctx) (α := α)
                (i := .block current currentBranch) value := by
            rw [interpHandlerAt_ret, relabelBlock_retAt]
        rw [leftEq, rightEq]
        let step : Step (H.spec ctx) α (Tree (H.spec ctx) α)
            (.block current currentBranch) := Step.ret value
        exact ⟨step.1, step.2, step.2, raw_dest_mkAt step, raw_dest_mkAt step,
          fun impossible => nomatch impossible⟩
      · have leftEq :
            interpHandlerAt (i := .block current currentBranch) defs.callHandler
                (relabelBlock
                  (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                  (failAt : Tree (ITree.Sum (H.spec ctx) (Call ctx)) _
                    (.block (.inl current) ⟨currentBranch.1, currentBranch.2⟩))) =
              (failAt : Tree (H.spec ctx) α (.block current currentBranch)) := by
            rw [relabelBlock_failAt, interpHandlerAt_fail]
        have rightEq :
            relabelBlock
                (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                (interpHandlerAt (i := .block current currentBranch) defs.callHandler
                  (failAt : Tree (ITree.Sum (H.spec ctx) (Call ctx)) _
                    (.block (.inl current) ⟨currentBranch.1, currentBranch.2⟩))) =
              (failAt : Tree (H.spec ctx) α (.block current currentBranch)) := by
            rw [interpHandlerAt_fail, relabelBlock_failAt]
        rw [leftEq, rightEq]
        let step : Step (H.spec ctx) α (Tree (H.spec ctx) α)
            (.block current currentBranch) := Step.fail
        exact ⟨step.1, step.2, step.2, raw_dest_mkAt step, raw_dest_mkAt step,
          fun impossible => nomatch impossible⟩
      · have leftEq :
            interpHandlerAt (i := .block current currentBranch) defs.callHandler
                (relabelBlock
                  (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                  (tauAt child)) =
              tauAt (interpHandlerAt (i := .block current currentBranch)
                defs.callHandler
                (relabelBlock
                  (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                  child)) := by
            rw [relabelBlock_tauAt, interpHandlerAt_tau]
        have rightEq :
            relabelBlock
                (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                (interpHandlerAt (i := .block current currentBranch)
                  defs.callHandler (tauAt child)) =
              tauAt (relabelBlock
                (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                (interpHandlerAt defs.callHandler child)) := by
            rw [interpHandlerAt_tau, relabelBlock_tauAt]
        rw [leftEq, rightEq]
        let leftStep : Step (H.spec ctx) α (Tree (H.spec ctx) α)
            (.block current currentBranch) :=
          Step.tau (interpHandlerAt defs.callHandler
            (relabelBlock
              (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α) child))
        let rightStep : Step (H.spec ctx) α (Tree (H.spec ctx) α)
            (.block current currentBranch) :=
          Step.tau (relabelBlock
            (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
            (interpHandlerAt defs.callHandler child))
        exact ⟨.tau, leftStep.2, rightStep.2,
          raw_dest_mkAt leftStep, raw_dest_mkAt rightStep, fun ar => by
            cases ar
            exact .relabel child⟩
      · cases operation with
        | inl visible =>
            have leftEq :
                interpHandlerAt (i := .block current currentBranch) defs.callHandler
                    (relabelBlock
                      (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                      (opAt (.inl visible) input blocks continuation)) =
                  opAt visible input
                    (fun branch => interpHandlerAt defs.callHandler
                      (relabelBlock
                        (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                        (blocks ⟨branch.1, branch.2⟩)))
                    (fun output => interpHandlerAt
                      (i := .block current currentBranch) defs.callHandler
                      (relabelBlock
                        (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                        (continuation output))) := by
              rw [relabelBlock_opAt, interpHandlerAt_op_left]
            have rightEq :
                relabelBlock
                    (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                    (interpHandlerAt (i := .block current currentBranch)
                      defs.callHandler
                      (opAt (.inl visible) input blocks continuation)) =
                  opAt visible input
                    (fun branch => relabelBlock
                      (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                      (interpHandlerAt defs.callHandler
                        (blocks ⟨branch.1, branch.2⟩)))
                    (fun output => relabelBlock
                      (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                      (interpHandlerAt defs.callHandler (continuation output))) := by
              rw [interpHandlerAt_op_left, relabelBlock_opAt]
            rw [leftEq, rightEq]
            let leftStep : Step (H.spec ctx) α (Tree (H.spec ctx) α)
                (.block current currentBranch) :=
              Step.op visible input
                (fun branch => interpHandlerAt defs.callHandler
                  (relabelBlock
                    (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                    (blocks ⟨branch.1, branch.2⟩)))
                (fun output => interpHandlerAt defs.callHandler
                  (relabelBlock
                    (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                    (continuation output)))
            let rightStep : Step (H.spec ctx) α (Tree (H.spec ctx) α)
                (.block current currentBranch) :=
              Step.op visible input
                (fun branch => relabelBlock
                  (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                  (interpHandlerAt defs.callHandler
                    (blocks ⟨branch.1, branch.2⟩)))
                (fun output => relabelBlock
                  (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                  (interpHandlerAt defs.callHandler (continuation output)))
            exact ⟨.op visible input, leftStep.2, rightStep.2,
              raw_dest_mkAt leftStep, raw_dest_mkAt rightStep, fun ar => by
                cases ar with
                | block branch => exact .relabel (blocks branch)
                | cont output => exact .relabel (continuation output)⟩
        | inr call =>
            cases call with
            | call fn =>
              cases fn with
              | mk ref captured =>
                let body := defs.denote .refl ref captured.unpack input
                let combined := bindAt body continuation
                have leftEq :
                    interpHandlerAt (i := .block current currentBranch)
                        defs.callHandler
                        (relabelBlock
                          (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                          (opAt (.inr (.call (.mk ref captured))) input blocks
                            continuation)) =
                      tauAt (interpHandlerAt (i := .block current currentBranch)
                        defs.callHandler
                        (relabelBlock
                          (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                          combined)) := by
                  rw [relabelBlock_opAt, interpHandlerAt_op_right]
                  congr 2
                  change bindAt body
                      (fun output => relabelBlock
                        (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                        (continuation output)) =
                    relabelBlock
                      (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                      combined
                  exact (relabelBlock_bind body continuation).symm
                have rightEq :
                    relabelBlock
                        (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                        (interpHandlerAt defs.callHandler
                          (opAt (.inr (.call (.mk ref captured))) input blocks
                            continuation)) =
                      tauAt (relabelBlock
                        (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                        (interpHandlerAt defs.callHandler combined)) := by
                  rw [interpHandlerAt_op_right, relabelBlock_tauAt]
                  rfl
                rw [leftEq, rightEq]
                let leftStep : Step (H.spec ctx) α (Tree (H.spec ctx) α)
                    (.block current currentBranch) :=
                  Step.tau (interpHandlerAt defs.callHandler
                    (relabelBlock
                      (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                      combined))
                let rightStep : Step (H.spec ctx) α (Tree (H.spec ctx) α)
                    (.block current currentBranch) :=
                  Step.tau (relabelBlock
                    (α := (H.spec ctx).branchOutput root rootBranch.1) (β := α)
                    (interpHandlerAt defs.callHandler combined))
                exact ⟨.tau, leftStep.2, rightStep.2,
                  raw_dest_mkAt leftStep, raw_dest_mkAt rightStep, fun ar => by
                    cases ar
                    exact .relabel combined⟩

/-- Interpreting the global call effect preserves a visible source operation, recursively
interpreting its scoped branches and ordinary continuation. -/
theorem Defs.run_op {H : Signature} {ctx : DefCtx}
    (defs : Defs H (Tp.denote ctx) ctx) (operation : H.op)
    (input : (H.input operation).denote ctx)
    (blocks : (branch : (H.spec ctx).Block operation) →
      OpenM H ctx ((H.spec ctx).branchOutput operation branch.1))
    (continuation : (H.output operation).denote ctx → OpenM H ctx α) :
    defs.run (op (.inl operation) input blocks continuation) =
      op operation input
        (fun branch => defs.run (blocks ⟨branch.1, branch.2⟩))
        (fun output => defs.run (continuation output)) := by
  unfold Defs.run op
  change interpHandlerAt (i := .normal) defs.callHandler
      (opAt (.inl operation) input (fun branch => asBlock (blocks branch))
        continuation) = _
  rw [interpHandlerAt_op_left]
  congr 1
  funext branch
  exact defs.run_asBlock (blocks branch)

end Freigen.Ast
