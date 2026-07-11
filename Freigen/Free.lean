import Freigen.ITree.Eutt

namespace Freigen

universe u v

/-- Free syntax for higher-order operations with dynamically bound block arguments. -/
inductive Free (H : ITree.HSig.{u, v}) : Type u → Type (max u v + 1) where
  | pure {α} : α → Free H α
  | op {α} (e : H.op) : H.input e →
      ((b : H.branch e) → H.branchInput e b → Free H (H.branchOutput e b)) →
      (H.output e → Free H α) → Free H α

def Free.bind {H} {α β} : Free H α → (α → Free H β) → Free H β
  | .pure a, f => f a
  | .op e i blocks k, f => .op e i blocks fun o => (k o).bind f

instance {H} : Monad (Free H) where
  pure := Free.pure
  bind := Free.bind

theorem Free.bind_pure {H α} (m : Free H α) : m.bind .pure = m := by
  induction m with
  | pure => rfl
  | op e i blocks k _ ih => exact congrArg (Free.op e i blocks) (funext ih)

theorem Free.bind_assoc {H} {α β γ} (m : Free H α)
    (f : α → Free H β) (g : β → Free H γ) :
    (m.bind f).bind g = m.bind fun a => (f a).bind g := by
  induction m with
  | pure => rfl
  | op e i blocks k _ ih => exact congrArg (Free.op e i blocks) (funext fun o => ih o f)

instance {H} : LawfulMonad (Free H) :=
  LawfulMonad.mk' (Free H)
    (fun m => Free.bind_pure m)
    (fun _ _ => rfl)
    (fun m f g => Free.bind_assoc m f g)

def Free.eval {M : Type u → Type v} [Monad M] {H α}
    (evalOp : (e : H.op) → H.input e →
      ((b : H.branch e) → H.branchInput e b → M (H.branchOutput e b)) →
      M (H.output e)) : Free H α → M α
  | .pure a => Pure.pure a
  | .op e i blocks k => do
      let o ← evalOp e i fun b x => Free.eval evalOp (blocks b x)
      Free.eval evalOp (k o)

theorem Free.eval_bind {M : Type u → Type v} [Monad M] [LawfulMonad M] {H} {α β}
    (evalOp : (e : H.op) → H.input e →
      ((b : H.branch e) → H.branchInput e b → M (H.branchOutput e b)) →
      M (H.output e)) (m : Free H α) (f : α → Free H β) :
    Free.eval evalOp (m.bind f) = Free.eval evalOp m >>= fun a => Free.eval evalOp (f a) := by
  induction m with
  | pure a =>
      exact (pure_bind (m := M) a (fun a => Free.eval evalOp (f a))).symm
  | op e i blocks k _ ih =>
      simp only [Free.bind, Free.eval]
      rw [LawfulMonad.bind_assoc]
      exact congrArg _ (funext fun o => ih o f)

def Free.toITree {H : ITree.HSig.{u, v}} {α : Type u} :
    Free H α → ITree.CompE H α :=
  Free.eval fun e i blocks =>
    ITree.CompE.op e i (fun bx => blocks bx.1 bx.2) ITree.CompE.ret

theorem Free.toITree_bind {H : ITree.HSig.{u, v}} {α β : Type u}
    (m : Free H α) (f : α → Free H β) :
    Free.toITree (m.bind f) =
      ITree.CompE.bind (Free.toITree m) (fun a => Free.toITree (f a)) :=
  Free.eval_bind _ m f

@[simp] theorem Free.toITree_op {H : ITree.HSig.{u, v}} {α : Type u}
    (e : H.op) (input : H.input e)
    (blocks : (b : H.branch e) → H.branchInput e b →
      Free H (H.branchOutput e b))
    (k : H.output e → Free H α) :
    Free.toITree (.op e input blocks k) =
      ITree.CompE.bind
        (ITree.CompE.op e input
          (fun bx => Free.toITree (blocks bx.1 bx.2)) ITree.CompE.ret)
        (fun o => Free.toITree (k o)) := by
  rfl

def Free.call {H : ITree.HSig.{u, v}} {σ ρ : Type u} (s : σ) :
    Free (ITree.Sum H (ITree.Call σ ρ)) ρ :=
  .op (.inr .call) s (fun b _ => nomatch b) .pure

theorem Free.toITree_call {H : ITree.HSig.{u, v}} {σ ρ : Type u} (s : σ) :
    Free.toITree (Free.call (H := H) (ρ := ρ) s) =
      ITree.CompE.op (H := ITree.Sum H (ITree.Call σ ρ)) (α := ρ)
        (Sum.inr ITree.CallOp.call) s
        (fun bx => nomatch bx.1) ITree.CompE.ret := by
  unfold Free.call Free.toITree
  simp only [Free.eval, ITree.CompE.pure_def, ITree.CompE.bind_def]
  rw [ITree.CompE.bind_ret_right]
  congr
  funext bx
  exact nomatch bx.1

end Freigen
