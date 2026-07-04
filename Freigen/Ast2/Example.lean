import Freigen.Ast2.Basic
import Freigen.ITree.Eutt

/-!
# A hand-reflected circuit and its soundness

A dry run for the reflector, with no metaprogramming: a source circuit (a `Freek` program with
a helper definition, a recursive definition, an `assert` effect, and a `hint` block) is mirrored
*by hand* into an `Expr` — node for node, the way the reflector would emit it — and the two are
proved equivalent **for every choice of effect and `bindEff` interpreters**:

```
∀ ε br hE hB,  Expr.denote hE hB (mainAst _) ≈ Freek.eval hE hB (mainSrc (CompE ε br))
```

The proof shape is the template for reflector soundness:

* a non-recursive helper (`lam`) is sound **by `rfl`** — its denotation and the source's
  evaluation are *definitionally* the same tree;
* a recursive definition (`letrec`) is sound **up to `≈`, by induction** on its argument: one
  `mrec` unfolding (`interp_vis_call`) produces the `tau` that `≈` absorbs, and
  `eutt_bind_cong` stitches the induction hypothesis to the helper's equality;
* the main body composes by `eutt_bind_cong` + `eutt_refl` (everything after the recursive
  call is again definitionally equal).
-/

namespace Freigen
namespace Ast2
namespace Example

open ITree

/-! ## The signatures

An `assert : bool → nat` effect (the output is a dummy) and a `hint : nat → nat` custom
control-flow operation carrying one block that computes the hinted value. -/

abbrev CircE : EffSig := ⟨Unit, fun _ => .bool, fun _ => .nat⟩

abbrev CircB : BindSig := ⟨Unit, fun _ => .nat, fun _ => .nat, fun _ => Unit, fun _ _ => .nat⟩

/-! ## The source circuit

Written over the coded signatures instantiated at a generic target monad `M` (the theorem picks
`M := CompE ε br`).  Structure: a helper definition, a structurally recursive definition calling
it, and a main body using the hint block and a final assert. -/

section Source
variable (M : Type → Type)

/-- Helper definition: assert `x ≤ x²`, return `x²`. -/
def sqAssertSrc (x : Nat) : Freek (CircE.spec M) (CircB.spec M) Nat := do
  let y := x * x
  let _ ← Freek.eff () (decide (x ≤ y))
  pure y

/-- Recursive definition: `Σ_{i=1..n} i²`, each square produced by the helper. -/
def sumSqSrc : Nat → Freek (CircE.spec M) (CircB.spec M) Nat
  | 0 => pure 0
  | n + 1 => do
    let s ← sumSqSrc n
    let y ← sqAssertSrc M (n + 1)
    pure (s + y)

/-- The circuit: sum of squares up to 3, passed through a hint block whose body recomputes it,
    then asserted equal to the computed value. -/
def mainSrc : Freek (CircE.spec M) (CircB.spec M) Nat := do
  let s ← sumSqSrc M 3
  let h : Nat ← Freek.bindEff () s (fun _ => pure s)
  let _ ← Freek.eff () (h == s)
  pure h

end Source

/-! ## The hand-reflected AST

Node for node what a reflector should emit: the helper spills as a `lam`, the recursive
definition as a `letrec` (the source's structural `match` becomes `n == 0` / `ite` /
`selfCall (n - 1)`, and its call to the helper an `app` of the captured `lam` atom), host
literals become `natLit`s, host primitives become `bin` nodes, and the `bindEff` block is
carried verbatim as a sub-computation. -/

section Ast
variable {V : Tp → Type}

/-- The reflection of `sqAssertSrc` — the body of the `lam` bound to it. -/
def sqAssertAst (x : V .nat) : Expr CircE CircB V none .nat :=
  .bin .mul x x fun y =>
  .bin .le x y fun c =>
  .eff () c fun _ =>
  .ret y

/-- The reflection of `sumSqSrc` — the `letrec` body. -/
def sumSqAst (sq : V (.fn .nat .nat)) (n : V .nat) :
    Expr CircE CircB V (some (.nat, .nat)) .nat :=
  .natLit 0 fun z =>
  .bin .eq n z fun c =>
  .ite c
    (.ret z)
    (.natLit 1 fun one =>
     .bin .sub n one fun n' =>
     .selfCall n' fun s =>
     .app sq n fun y =>
     .bin .add s y fun r =>
     .ret r)
    fun v => .ret v

/-- The reflection of `mainSrc` — the whole closed program. -/
def mainAst : Closed CircE CircB .nat := fun _ =>
  .lam sqAssertAst fun sq =>
  .letrec (sumSqAst sq) fun sumSq =>
  .natLit 3 fun three =>
  .app sumSq three fun s =>
  .bindEff () s (fun _ => .ret s) fun h =>
  .bin .eq h s fun c =>
  .eff () c fun _ =>
  .ret h

end Ast

/-! ## Soundness, parametric in the interpreters -/

section Sound
variable {ε : Type} {br : ε → Type}
variable (hE : EffInterp CircE ε br) (hB : BindInterp CircB ε br)

/-- `Freek.eval` at the tree domain — the coded signatures pinned once (the elaborator cannot
    recover `𝓔`/`𝓑` from the interpreters alone). -/
abbrev evalC (hE : EffInterp CircE ε br) (hB : BindInterp CircB ε br) {α : Type}
    (p : Freek (CircE.spec (CompE ε br)) (CircB.spec (CompE ε br)) α) : CompE ε br α :=
  Freek.eval (𝓔 := CircE.spec (CompE ε br)) (𝓑 := CircB.spec (CompE ε br)) hE hB p

/-- The denoted helper: a base-domain Kleisli arrow (what the `lam` atom stands for). -/
def sqD : Nat → CompE ε br Nat := fun x => Expr.denote hE hB (sqAssertAst x)

/-- The denoted `letrec` body: a tree over the call-extended signature (what `mrec` ties). -/
def bd : Nat → CompE (ε ⊕ Nat) (callBr br Nat) Nat := fun n =>
  Expr.denote hE hB (sumSqAst (sqD hE hB) n)

/-- **Helper soundness** — definitional: the denoted `lam` body *is* the evaluated source
    helper, for any interpreters. -/
theorem sq_sound (x : Nat) :
    sqD hE hB x = evalC hE hB (sqAssertSrc (CompE ε br) x) := rfl

/-- **Recursive-definition soundness**, by induction on the argument: the `mrec`-tied `letrec`
    body is `≈` (not `=` — each unfolding spends one `tau`) to the source's structural
    recursion, for any interpreters. -/
theorem sumSq_sound (n : Nat) :
    Eutt (mrec (bd hE hB) n) (evalC hE hB (sumSqSrc (CompE ε br) n)) := by
  induction n with
  | zero =>
    apply Eutt.of_eq
    show interp (bd hE hB) (ITree.bind (ITree.ret 0) fun v => ITree.ret v) = _
    rw [bind_ret, interp_ret]
    rfl
  | succ n ih =>
    -- One unfolding of the knot: `bd (n+1)` is *definitionally* a self-call `vis` followed by
    -- the helper's (`sumL`-embedded) computation; `interp` turns the call into a `tau`-guarded
    -- re-run of the body on `n`.
    have hunf : mrec (bd hE hB) (n + 1)
        = tau (ITree.bind (mrec (bd hE hB) n) fun s =>
            ITree.bind (sqD hE hB (n + 1)) fun y => ITree.ret (s + y)) := by
      show interp (bd hE hB)
          (ITree.bind
            (vis (Sum.inr n) fun (s : Nat) =>
              ITree.bind (sumL (sqD hE hB (n + 1))) fun y => ITree.ret (s + y))
            (fun v => ITree.ret v)) = _
      simp only [bind_vis, interp_vis_call, interp_bind, bind_assoc, bind_ret, interp_sumL,
                 interp_ret]
      rfl
    rw [hunf]
    exact eutt_tau_left (eutt_bind_cong ih fun s =>
      eutt_bind_cong (Eutt.of_eq (sq_sound hE hB (n + 1))) fun y => eutt_refl _)

/-- **Program soundness**: the hand-reflected AST and the source circuit are weakly bisimilar
    under *every* effect interpreter and *every* `bindEff` interpreter.  Everything around the
    recursive call — the `lam`, the literals, the `bindEff` with its block, the final assert —
    is definitionally equal on both sides, so the proof is one `bind`-congruence around
    `sumSq_sound`. -/
theorem main_sound :
    Eutt (Expr.denote hE hB (mainAst _)) (evalC hE hB (mainSrc (CompE ε br))) := by
  show Eutt
    (ITree.bind (mrec (bd hE hB) 3) fun s =>
      ITree.bind (hB () s fun _ => ITree.ret s) fun h =>
        ITree.bind (hE () (h == s)) fun _ => ITree.ret h)
    (ITree.bind (evalC hE hB (sumSqSrc (CompE ε br) 3)) fun s =>
      ITree.bind (hB () s fun _ => ITree.ret s) fun h =>
        ITree.bind (hE () (h == s)) fun _ => ITree.ret h)
  exact eutt_bind_cong (sumSq_sound hE hB 3) fun s => eutt_refl _

end Sound

end Example
end Ast2
end Freigen
