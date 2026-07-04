import Mathlib.Data.PFunctor.Univariate.M
import Freigen.ITree.Effect

/-!
# Interaction trees: a coinductive denotation domain with effects, divergence, and failure

`CompE ε br α` is a Lean realisation of **interaction trees** (Xia et al.) over an *event
signature* — a type of events `ε : Type` with a branching arity `br : ε → Type` — built as the
final coalgebra (`PFunctor.M`) of the one-step functor

```
Pos := ret α | tau | fail | vis (e : ε)              -- positions
Ar  := ret ↦ ∅ | tau ↦ Unit | fail ↦ ∅ | vis e ↦ br e -- arities (children)
```

so a computation is a (possibly infinite) tree whose leaves are `ret a` / `fail`, with internal
`tau` (a silent step — the guard that makes recursion productive) and `vis e k` (perform event
`e`, branch on its result).  This is the domain in which **recursion** denotes: `mrec` is a
*guarded corecursion*, total without any termination proof, and divergence is an infinite chain
of `tau`s.

Everything lives in `Type 0`: events are plain data (a first-order DSL signature's events are
`Effect Op`), and arities are computed types — no host `Type` is ever stored in a node.  That is
what lets **function values** denote as Kleisli arrows `a.denote → Comp Op b.denote` inside the
ordinary value universe.

`Comp Op` abbreviates the instantiation at a first-order DSL signature.  General recursion
(`interp`/`mrec`) extends an arbitrary signature with one *call* event `.inr (s : σ)` — the sum
extension `ε ⊕ σ` — whose payload `σ` may be **any** `Type 0`, in particular a state tuple
containing function values.
-/

namespace Freigen
namespace ITree

variable {ε : Type _} {br : ε → Type _}

/-! ## The one-step functor -/

/-- One-step *positions* of an interaction tree. -/
inductive Pos (ε : Type _) (α : Type _) : Type _
  | ret  : α → Pos ε α
  | tau  : Pos ε α
  | fail : Pos ε α
  | vis  : ε → Pos ε α

/-- Arity (set of children) of each position. -/
@[reducible] def Ar {ε α} (br : ε → Type _) : Pos ε α → Type _
  | .ret _  => PEmpty
  | .tau    => PUnit
  | .fail   => PEmpty
  | .vis e  => br e

/-- The polynomial one-step functor of interaction trees. -/
@[reducible] def P (ε : Type _) (br : ε → Type _) (α : Type _) : PFunctor := ⟨Pos ε α, Ar br⟩

/-- Interaction trees over the event signature `(ε, br)` returning `α`: the final coalgebra. -/
def CompE (ε : Type _) (br : ε → Type _) (α : Type _) : Type _ := (P ε br α).M

/-- Interaction trees over a first-order DSL signature. -/
abbrev Comp (Op : TpF → TpF → Type) (α : Type) : Type := CompE (Effect Op) Effect.arity α

/-! ## Constructors and their destructor laws

`M.mk`/`M.dest` are mutually inverse, so each constructor's `dest` computes by `M.dest_mk`. -/

/-- Converge with a value. -/
def ret (a : α) : CompE ε br α := PFunctor.M.mk ⟨Pos.ret a, PEmpty.elim⟩
/-- A silent step (the recursion guard; an infinite chain of these is divergence). -/
def tau (t : CompE ε br α) : CompE ε br α := PFunctor.M.mk ⟨Pos.tau, fun _ => t⟩
/-- Abort (e.g. an out-of-bounds read on a non-`Inhabited` element type). -/
def fail : CompE ε br α := PFunctor.M.mk ⟨Pos.fail, PEmpty.elim⟩
/-- Perform event `e`, continue with `k` on its result. -/
def vis (e : ε) (k : br e → CompE ε br α) : CompE ε br α := PFunctor.M.mk ⟨Pos.vis e, k⟩

@[simp] theorem dest_ret (a : α) :
    (ret (ε := ε) (br := br) a).dest = ⟨Pos.ret a, PEmpty.elim⟩ := PFunctor.M.dest_mk _
@[simp] theorem dest_tau (t : CompE ε br α) :
    (tau t).dest = ⟨Pos.tau, fun _ => t⟩ := PFunctor.M.dest_mk _
@[simp] theorem dest_fail :
    (fail (ε := ε) (br := br) (α := α)).dest = ⟨Pos.fail, PEmpty.elim⟩ := PFunctor.M.dest_mk _
@[simp] theorem dest_vis (e : ε) (k : br e → CompE ε br α) :
    (vis e k).dest = ⟨Pos.vis e, k⟩ := PFunctor.M.dest_mk _

/-- Two trees with equal one-step unfoldings are equal (destructor is injective). -/
theorem eq_of_dest_eq {x y : CompE ε br α} (h : x.dest = y.dest) : x = y := by
  rw [← PFunctor.M.mk_dest x, ← PFunctor.M.mk_dest y, h]

/-- A destructor view: every tree is `ret`/`fail`/`tau`/`vis`.  (Used pervasively below to case on
    a tree by its head while keeping a real equation, rather than only its `dest`.) -/
theorem cases_view {α : Type} (x : CompE ε br α) :
    (∃ a, x = ret a) ∨ x = fail ∨ (∃ t, x = tau t) ∨
      (∃ (e : ε) (k : br e → CompE ε br α), x = vis e k) := by
  obtain ⟨p, c, hd⟩ : ∃ p c, x.dest = ⟨p, c⟩ := ⟨_, _, rfl⟩
  match p, c, hd with
  | .ret a, c, hd =>
    exact Or.inl ⟨a, eq_of_dest_eq (by
      rw [hd, dest_ret]; exact Sigma.ext rfl (heq_of_eq (funext fun e => e.elim)))⟩
  | .fail, c, hd =>
    exact Or.inr (Or.inl (eq_of_dest_eq (by
      rw [hd, dest_fail]; exact Sigma.ext rfl (heq_of_eq (funext fun e => e.elim)))))
  | .tau, c, hd =>
    exact Or.inr (Or.inr (Or.inl ⟨c PUnit.unit, eq_of_dest_eq (by rw [hd, dest_tau])⟩))
  | .vis e, c, hd =>
    exact Or.inr (Or.inr (Or.inr ⟨e, c, eq_of_dest_eq (by rw [hd, dest_vis])⟩))

/-! ## Bind, by corecursion

State of the corecursion is `CompE ε br α ⊕ CompE ε br β`: `inl` is "still running the first tree"
(splice in `k a` at each `ret a`), `inr` is "copying the spliced result tree". -/

/-- The bind coalgebra (one step). -/
def bindCo {α β : Type} (k : α → CompE ε br β) :
    (CompE ε br α ⊕ CompE ε br β) → (P ε br β).Obj (CompE ε br α ⊕ CompE ε br β)
  | .inl m =>
    match m.dest with
    | ⟨p, c⟩ =>
      match p, c with
      | .ret a, _ => match (k a).dest with | ⟨b, g⟩ => ⟨b, fun i => .inr (g i)⟩
      | .tau,  c => ⟨Pos.tau, fun u => .inl (c u)⟩
      | .fail, _ => ⟨Pos.fail, PEmpty.elim⟩
      | .vis e, c => ⟨Pos.vis e, fun i => .inl (c i)⟩
  | .inr t =>
    match t.dest with | ⟨b, g⟩ => ⟨b, fun i => .inr (g i)⟩

/-- Monadic bind on interaction trees. -/
def bind {α β : Type _} (m : CompE ε br α) (k : α → CompE ε br β) : CompE ε br β :=
  PFunctor.M.corec (bindCo k) (.inl m)

/-- Copying an already-built tree (the `inr` state) is the identity. -/
theorem corec_inr {α β : Type} (k : α → CompE ε br β) (t : CompE ε br β) :
    PFunctor.M.corec (bindCo k) (.inr t) = t := by
  refine PFunctor.M.bisim
    (fun x y => x = PFunctor.M.corec (bindCo k) (.inr y)) ?_ _ _ rfl
  intro x y hxy
  subst hxy
  obtain ⟨b, g, hy⟩ : ∃ b g, y.dest = ⟨b, g⟩ := ⟨_, _, rfl⟩
  refine ⟨b, fun i => PFunctor.M.corec (bindCo k) (.inr (g i)), g, ?_, hy, fun i => rfl⟩
  rw [PFunctor.M.dest_corec]
  simp only [bindCo, hy, PFunctor.map]
  rfl

/-! ### Bind computation laws -/

@[simp] theorem bind_ret {α β : Type} (a : α) (k : α → CompE ε br β) : bind (ret a) k = k a := by
  apply eq_of_dest_eq
  obtain ⟨b, g, hk⟩ : ∃ b g, (k a).dest = ⟨b, g⟩ := ⟨_, _, rfl⟩
  rw [bind, PFunctor.M.dest_corec]
  simp only [bindCo, dest_ret, hk, PFunctor.map, Function.comp_def, corec_inr]

@[simp] theorem bind_tau {α β : Type} (t : CompE ε br α) (k : α → CompE ε br β) :
    bind (tau t) k = tau (bind t k) := by
  apply eq_of_dest_eq
  simp only [bind, PFunctor.M.dest_corec, bindCo, dest_tau, PFunctor.map, Function.comp_def]

@[simp] theorem bind_fail {α β : Type} (k : α → CompE ε br β) :
    bind (fail : CompE ε br α) k = fail := by
  apply eq_of_dest_eq
  simp only [bind, PFunctor.M.dest_corec, bindCo, dest_fail, PFunctor.map, Function.comp_def]
  congr 1
  funext e
  exact e.elim

@[simp] theorem bind_vis {α β : Type} (e : ε) (c : br e → CompE ε br α)
    (k : α → CompE ε br β) :
    bind (vis e c) k = vis e (fun i => bind (c i) k) := by
  apply eq_of_dest_eq
  simp only [bind, PFunctor.M.dest_corec, bindCo, dest_vis, PFunctor.map, Function.comp_def]

/-- Interaction trees are a monad (`pure = ret`, `bind` as above). -/
instance : Monad (CompE ε br) where
  pure := ret
  bind := bind

@[simp] theorem pure_def {α} (a : α) : (pure a : CompE ε br α) = ret a := rfl
@[simp] theorem bind_def {α β} (m : CompE ε br α) (k : α → CompE ε br β) :
    m >>= k = bind m k := rfl

/-- Right identity: `bind m ret = m` (by bisimulation). -/
theorem bind_ret_right {α} (m : CompE ε br α) : bind m ret = m := by
  suffices H : ∀ x y : CompE ε br α, (x = bind y ret ∨ x = y) → x = y from H _ _ (Or.inl rfl)
  refine PFunctor.M.bisim _ ?_
  rintro x y (rfl | rfl)
  · rcases cases_view y with ⟨a, rfl⟩ | rfl | ⟨t', rfl⟩ | ⟨e, c, rfl⟩
    · rw [bind_ret]
      exact ⟨Pos.ret a, PEmpty.elim, PEmpty.elim, dest_ret a, dest_ret a, fun i => i.elim⟩
    · rw [bind_fail]
      exact ⟨Pos.fail, PEmpty.elim, PEmpty.elim, dest_fail, dest_fail, fun i => i.elim⟩
    · rw [bind_tau]
      exact ⟨Pos.tau, _, _, dest_tau _, dest_tau _, fun _ => Or.inl rfl⟩
    · rw [bind_vis]
      exact ⟨Pos.vis e, _, _, dest_vis _ _, dest_vis _ _, fun i => Or.inl rfl⟩
  · obtain ⟨p, c, hd⟩ : ∃ p c, x.dest = ⟨p, c⟩ := ⟨_, _, rfl⟩
    exact ⟨p, c, c, hd, hd, fun _ => Or.inr rfl⟩

/-- Associativity of `bind` (by bisimulation). -/
theorem bind_assoc {α β γ} (m : CompE ε br α) (k : α → CompE ε br β) (h : β → CompE ε br γ) :
    bind (bind m k) h = bind m (fun a => bind (k a) h) := by
  suffices H : ∀ x y : CompE ε br γ,
      ((∃ m, x = bind (bind m k) h ∧ y = bind m (fun a => bind (k a) h)) ∨ x = y) → x = y from
    H _ _ (Or.inl ⟨m, rfl, rfl⟩)
  refine PFunctor.M.bisim _ ?_
  rintro x y (⟨m, rfl, rfl⟩ | rfl)
  · rcases cases_view m with ⟨a, rfl⟩ | rfl | ⟨t, rfl⟩ | ⟨e, c, rfl⟩
    · rw [bind_ret, bind_ret]
      obtain ⟨p, c', hd'⟩ : ∃ p c', (bind (k a) h).dest = ⟨p, c'⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c', c', hd', hd', fun _ => Or.inr rfl⟩
    · rw [bind_fail, bind_fail, bind_fail]
      exact ⟨Pos.fail, PEmpty.elim, PEmpty.elim, dest_fail, dest_fail, fun i => i.elim⟩
    · rw [bind_tau, bind_tau, bind_tau]
      exact ⟨Pos.tau, _, _, dest_tau _, dest_tau _, fun _ => Or.inl ⟨t, rfl, rfl⟩⟩
    · rw [bind_vis, bind_vis, bind_vis]
      exact ⟨Pos.vis e, _, _, dest_vis _ _, dest_vis _ _, fun i => Or.inl ⟨c i, rfl, rfl⟩⟩
  · obtain ⟨p, c, hd⟩ : ∃ p c, x.dest = ⟨p, c⟩ := ⟨_, _, rfl⟩
    exact ⟨p, c, c, hd, hd, fun _ => Or.inr rfl⟩

/-- With all three `bind` laws proved, interaction trees are a **lawful monad**. -/
instance : LawfulMonad (CompE ε br) :=
  LawfulMonad.mk' _
    (fun x => bind_ret_right x)
    (fun a k => bind_ret a k)
    (fun m k h => bind_assoc m k h)

/-! ## General recursion: `mrec`

A recursive call is a node *inside* the tree, so the continuation after it is preserved (this is
what makes non-tail recursion work).  We extend the event signature with one call event — the
**sum extension** `ε ⊕ σ` (a call carries its argument `s : σ`, and branches on the result `ρ`)
— let the body be a tree over the extended signature (calls allowed in any position), and tie
the knot by **interpreting** every call back into the body, guarded by a `tau`.

The call payload `σ` is an arbitrary `Type 0` — in particular a state tuple *containing function
values* (Kleisli arrows are `Type 0` here); nothing restricts recursion to first-order state. -/

variable {σ ρ : Type}

/-- The branching arity of the sum-extended signature: base events keep theirs; a call branches
    on the recursion's result type `ρ`. -/
@[reducible] def callBr (br : ε → Type) (ρ : Type) : ε ⊕ σ → Type :=
  Sum.elim br (fun _ => ρ)

/-- One step of interpreting a body tree: base events pass through; a call `.inr s` is replaced
    by the body re-run on `s` (with the call's continuation spliced after), guarded by a `tau`
    (which makes the corecursion productive). -/
def interpCo (body : σ → CompE (ε ⊕ σ) (callBr br ρ) ρ) {γ : Type} :
    CompE (ε ⊕ σ) (callBr br ρ) γ → (P ε br γ).Obj (CompE (ε ⊕ σ) (callBr br ρ) γ)
  | t =>
    match t.dest with
    | ⟨.ret b, _⟩ => ⟨Pos.ret b, PEmpty.elim⟩
    | ⟨.tau, c⟩   => ⟨Pos.tau, c⟩
    | ⟨.fail, _⟩  => ⟨Pos.fail, PEmpty.elim⟩
    | ⟨.vis e, c⟩ =>
      match e, c with
      | .inl e', c => ⟨Pos.vis e', c⟩
      | .inr s, c  => ⟨Pos.tau, fun _ => bind (body s) c⟩

/-- Interpret a body tree (calls allowed) into a plain tree, by guarded corecursion. -/
def interp (body : σ → CompE (ε ⊕ σ) (callBr br ρ) ρ) {γ : Type}
    (t : CompE (ε ⊕ σ) (callBr br ρ) γ) : CompE ε br γ :=
  PFunctor.M.corec (interpCo body) t

/-- **General recursion.** `mrec body` ties the recursive knot: run the body, interpreting each
    self-call by re-running the body.  The body may call itself in any position (the continuation
    after a call is kept in the tree), so both tail and non-tail recursion are supported. -/
def mrec (body : σ → CompE (ε ⊕ σ) (callBr br ρ) ρ) (s : σ) : CompE ε br ρ :=
  interp body (body s)

/-! ### `interp` computation laws -/

@[simp] theorem interp_ret (body : σ → CompE (ε ⊕ σ) (callBr br ρ) ρ) {γ} (b : γ) :
    interp body (ret b) = ret b := by
  apply eq_of_dest_eq
  simp only [interp, PFunctor.M.dest_corec, interpCo, dest_ret, PFunctor.map, Function.comp_def]
  congr 1; funext e; exact e.elim

@[simp] theorem interp_tau (body : σ → CompE (ε ⊕ σ) (callBr br ρ) ρ) {γ}
    (t : CompE (ε ⊕ σ) (callBr br ρ) γ) :
    interp body (tau t) = tau (interp body t) := by
  apply eq_of_dest_eq
  simp only [interp, PFunctor.M.dest_corec, interpCo, dest_tau, PFunctor.map, Function.comp_def]

@[simp] theorem interp_fail (body : σ → CompE (ε ⊕ σ) (callBr br ρ) ρ) {γ} :
    interp body (fail : CompE (ε ⊕ σ) (callBr br ρ) γ) = fail := by
  apply eq_of_dest_eq
  simp only [interp, PFunctor.M.dest_corec, interpCo, dest_fail, PFunctor.map, Function.comp_def]
  congr 1; funext e; exact e.elim

/-- Base events pass through interpretation unchanged. -/
@[simp] theorem interp_vis_base (body : σ → CompE (ε ⊕ σ) (callBr br ρ) ρ) {γ}
    (e : ε) (c : br e → CompE (ε ⊕ σ) (callBr br ρ) γ) :
    interp body (vis (Sum.inl e) c) = vis e (fun x => interp body (c x)) := by
  apply eq_of_dest_eq
  simp only [interp, PFunctor.M.dest_corec, interpCo, dest_vis, PFunctor.map, Function.comp_def]

/-- A self-call `s` is interpreted as the body re-run on `s` (continuation `c` spliced after),
    guarded by a `tau` — the recursion's unfolding step. -/
@[simp] theorem interp_vis_call (body : σ → CompE (ε ⊕ σ) (callBr br ρ) ρ) {γ}
    (s : σ) (c : ρ → CompE (ε ⊕ σ) (callBr br ρ) γ) :
    interp body (vis (Sum.inr s) c) = tau (interp body (bind (body s) c)) := by
  apply eq_of_dest_eq
  simp only [interp, PFunctor.M.dest_corec, interpCo, dest_vis, PFunctor.map, Function.comp_def,
             dest_tau]

/-- **`interp` is a monad morphism**: it commutes with `bind`.  This is what makes *non-tail*
    recursion compute correctly — the work after a recursive call (`k`) is pushed through the
    interpretation.  Proved by bisimulation (using `bind_assoc` at the `call` step). -/
theorem interp_bind (body : σ → CompE (ε ⊕ σ) (callBr br ρ) ρ) {β γ}
    (m : CompE (ε ⊕ σ) (callBr br ρ) β) (k : β → CompE (ε ⊕ σ) (callBr br ρ) γ) :
    interp body (bind m k) = bind (interp body m) (fun x => interp body (k x)) := by
  suffices H : ∀ x y : CompE ε br γ,
      ((∃ m : CompE (ε ⊕ σ) (callBr br ρ) β, x = interp body (bind m k) ∧
          y = bind (interp body m) (fun x => interp body (k x))) ∨ x = y) → x = y from
    H _ _ (Or.inl ⟨m, rfl, rfl⟩)
  refine PFunctor.M.bisim _ ?_
  rintro x y (⟨m, rfl, rfl⟩ | rfl)
  · rcases cases_view m with ⟨a, rfl⟩ | rfl | ⟨t, rfl⟩ | ⟨e, c, rfl⟩
    · rw [bind_ret, interp_ret, bind_ret]
      obtain ⟨p, c', hd'⟩ : ∃ p c', (interp body (k a)).dest = ⟨p, c'⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c', c', hd', hd', fun _ => Or.inr rfl⟩
    · simp only [bind_fail, interp_fail]
      exact ⟨Pos.fail, PEmpty.elim, PEmpty.elim, dest_fail, dest_fail, fun i => i.elim⟩
    · rw [bind_tau, interp_tau, interp_tau, bind_tau]
      exact ⟨Pos.tau, _, _, dest_tau _, dest_tau _, fun _ => Or.inl ⟨t, rfl, rfl⟩⟩
    · cases e with
      | inl e' =>
        rw [bind_vis, interp_vis_base, interp_vis_base, bind_vis]
        exact ⟨Pos.vis e', _, _, dest_vis _ _, dest_vis _ _,
               fun i => Or.inl ⟨c i, rfl, rfl⟩⟩
      | inr s =>
        rw [bind_vis, interp_vis_call, interp_vis_call, bind_tau]
        exact ⟨Pos.tau, _, _, dest_tau _, dest_tau _,
               fun _ => Or.inl ⟨bind (body s) c, by rw [bind_assoc]; rfl, rfl⟩⟩
  · obtain ⟨p, c, hd⟩ : ∃ p c, x.dest = ⟨p, c⟩ := ⟨_, _, rfl⟩
    exact ⟨p, c, c, hd, hd, fun _ => Or.inr rfl⟩

/-! ### Embedding a base tree into the call-extended signature

A function value's denotation is a *base* tree (`.fn` denotes at the DSL events); applying one
inside a `rec_` body splices it into the *extended* tree — `sumL` relabels events along
`Sum.inl`, adding nothing (no `tau`s), so its computation laws are equalities. -/

/-- The relabeling coalgebra. -/
def sumLCo {γ : Type} : CompE ε br γ → (P (ε ⊕ σ) (callBr br ρ) γ).Obj (CompE ε br γ)
  | t =>
    match t.dest with
    | ⟨.ret a, _⟩ => ⟨Pos.ret a, PEmpty.elim⟩
    | ⟨.tau, c⟩   => ⟨Pos.tau, c⟩
    | ⟨.fail, _⟩  => ⟨Pos.fail, PEmpty.elim⟩
    | ⟨.vis e, c⟩ => ⟨Pos.vis (Sum.inl e), c⟩

/-- Embed a base tree into the call-extended signature (events relabel along `inl`). -/
def sumL {γ : Type} (t : CompE ε br γ) : CompE (ε ⊕ σ) (callBr br ρ) γ :=
  PFunctor.M.corec sumLCo t

@[simp] theorem sumL_ret {γ : Type} (a : γ) :
    (sumL (ret a) : CompE (ε ⊕ σ) (callBr br ρ) γ) = ret a := by
  apply eq_of_dest_eq
  simp only [sumL, PFunctor.M.dest_corec, sumLCo, dest_ret, PFunctor.map, Function.comp_def]
  congr 1; funext e; exact e.elim

@[simp] theorem sumL_tau {γ : Type} (t : CompE ε br γ) :
    (sumL (tau t) : CompE (ε ⊕ σ) (callBr br ρ) γ) = tau (sumL t) := by
  apply eq_of_dest_eq
  simp only [sumL, PFunctor.M.dest_corec, sumLCo, dest_tau, PFunctor.map, Function.comp_def]

@[simp] theorem sumL_fail {γ : Type} :
    (sumL (fail : CompE ε br γ) : CompE (ε ⊕ σ) (callBr br ρ) γ) = fail := by
  apply eq_of_dest_eq
  simp only [sumL, PFunctor.M.dest_corec, sumLCo, dest_fail, PFunctor.map, Function.comp_def]
  congr 1; funext e; exact e.elim

@[simp] theorem sumL_vis {γ : Type} (e : ε) (c : br e → CompE ε br γ) :
    (sumL (vis e c) : CompE (ε ⊕ σ) (callBr br ρ) γ) = vis (Sum.inl e) (fun i => sumL (c i)) := by
  apply eq_of_dest_eq
  simp only [sumL, PFunctor.M.dest_corec, sumLCo, dest_vis, PFunctor.map, Function.comp_def]

/-- Interpreting an embedded (call-free) tree gives it back unchanged. -/
@[simp] theorem interp_sumL (body : σ → CompE (ε ⊕ σ) (callBr br ρ) ρ) {γ}
    (t : CompE ε br γ) : interp body (sumL t) = t := by
  suffices H : ∀ x y : CompE ε br γ, (x = interp body (sumL y) ∨ x = y) → x = y from
    H _ _ (Or.inl rfl)
  refine PFunctor.M.bisim _ ?_
  rintro x y (rfl | rfl)
  · rcases cases_view y with ⟨a, rfl⟩ | rfl | ⟨t', rfl⟩ | ⟨e, c, rfl⟩
    · rw [sumL_ret, interp_ret]
      exact ⟨Pos.ret a, PEmpty.elim, PEmpty.elim, dest_ret a, dest_ret a, fun i => i.elim⟩
    · rw [sumL_fail, interp_fail]
      exact ⟨Pos.fail, PEmpty.elim, PEmpty.elim, dest_fail, dest_fail, fun i => i.elim⟩
    · rw [sumL_tau, interp_tau]
      exact ⟨Pos.tau, _, _, dest_tau _, dest_tau _, fun _ => Or.inl rfl⟩
    · rw [sumL_vis, interp_vis_base]
      exact ⟨Pos.vis e, _, _, dest_vis _ _, dest_vis _ _, fun i => Or.inl rfl⟩
  · obtain ⟨p, c, hd⟩ : ∃ p c, x.dest = ⟨p, c⟩ := ⟨_, _, rfl⟩
    exact ⟨p, c, c, hd, hd, fun _ => Or.inr rfl⟩

/-- `sumL` is a monad morphism: it commutes with `bind` (by bisimulation). -/
theorem sumL_bind {β γ : Type} (m : CompE ε br β) (k : β → CompE ε br γ) :
    (sumL (bind m k) : CompE (ε ⊕ σ) (callBr br ρ) γ)
      = bind (sumL m) (fun x => sumL (k x)) := by
  suffices H : ∀ x y : CompE (ε ⊕ σ) (callBr br ρ) γ,
      ((∃ m : CompE ε br β, x = sumL (bind m k) ∧ y = bind (sumL m) (fun x => sumL (k x))) ∨
        x = y) → x = y from H _ _ (Or.inl ⟨m, rfl, rfl⟩)
  refine PFunctor.M.bisim _ ?_
  rintro x y (⟨m, rfl, rfl⟩ | rfl)
  · rcases cases_view m with ⟨a, rfl⟩ | rfl | ⟨t, rfl⟩ | ⟨e, c, rfl⟩
    · rw [bind_ret, sumL_ret, bind_ret]
      obtain ⟨p, c', hd'⟩ : ∃ p c', (sumL (k a) : CompE (ε ⊕ σ) (callBr br ρ) γ).dest = ⟨p, c'⟩ :=
        ⟨_, _, rfl⟩
      exact ⟨p, c', c', hd', hd', fun _ => Or.inr rfl⟩
    · rw [bind_fail, sumL_fail, sumL_fail, bind_fail]
      exact ⟨Pos.fail, PEmpty.elim, PEmpty.elim, dest_fail, dest_fail, fun i => i.elim⟩
    · rw [bind_tau, sumL_tau, sumL_tau, bind_tau]
      exact ⟨Pos.tau, _, _, dest_tau _, dest_tau _, fun _ => Or.inl ⟨t, rfl, rfl⟩⟩
    · rw [bind_vis, sumL_vis, sumL_vis, bind_vis]
      exact ⟨Pos.vis (Sum.inl e), _, _, dest_vis _ _, dest_vis _ _,
             fun i => Or.inl ⟨c i, rfl, rfl⟩⟩
  · obtain ⟨p, c, hd⟩ : ∃ p c, x.dest = ⟨p, c⟩ := ⟨_, _, rfl⟩
    exact ⟨p, c, c, hd, hd, fun _ => Or.inr rfl⟩

end ITree
end Freigen
