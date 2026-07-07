import Freigen.Ast2.Basic
import Freigen.ITree2.Eutt

/-!
# A hand-reflected circuit over `ITree2`

This file is intentionally small: it checks that the source `Circuit` and the hand-written AST
use the same `ITree2` effect and scoped-bind signatures.  Scoped control flow is represented by
`bindEff` nodes in the tree.
-/

namespace Freigen
namespace Ast2
namespace Example

/-! ## Source program -/

/-- Assert a boolean. -/
abbrev Circuit.assert (b : Bool) : Circuit Unit :=
  Freek.eff (𝓔 := circuitEff) (𝓑 := circuitBlock) () b Freek.pure

/-- Helper definition: assert `x ≤ x²`, return `x²`. -/
def sqAssertSrc (x : Nat) : Circuit Nat := do
  let y := x * x
  let _ ← Circuit.assert (decide (x ≤ y))
  pure y

/-- Recursive definition: `Σ_{i=1..n} i²`, each square produced by the helper. -/
def sumSqSrc : Nat → Circuit Nat
  | 0 => pure 0
  | n + 1 => do
    let s ← sumSqSrc n
    let y ← sqAssertSrc (n + 1)
    pure (s + y)

/-- The circuit: sum of squares up to 3, passed through a first-order hint block, then checked. -/
def mainSrc : Circuit Nat := do
  let s ← sumSqSrc 3
  let h ← Circuit.hint .nat (pure s)
  let _ ← Circuit.assert (h == s)
  pure h

/-! ## Coded signatures -/

abbrev CircE : EffSig := ⟨Unit, fun _ => .bool, fun _ => .unit⟩

abbrev CircB : BindSig := ⟨Tp0, fun _ => .unit, id, fun _ => Unit, fun t _ => t⟩

abbrev M : Type → Type 1 := ITree2.CompE CircE.spec CircB.spec

/-- Evaluate a user-level `Circuit` program into the same `ITree2` signature used by the AST. -/
abbrev evalC {α : Type} (p : Circuit α) : M α :=
  Freek.toITree p

/-! ## Hand-reflected AST -/

section Ast
variable {V : Tp0 → Type}

/-- The reflection of `sqAssertSrc` — the body of the `lam` bound to it. -/
def sqAssertAst (x : V .nat) : Expr CircE CircB V none .nat :=
  .bin .mul x x fun y =>
  .bin .le x y fun c =>
  .eff () c fun _ =>
  .ret y

/-- The reflection of `sumSqSrc` — the `letrec` body. -/
def sumSqAst (sq : V .nat → M (V .nat)) (n : V .nat) :
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
  .unitLit fun u =>
  .bindEff .nat u (fun _ => .ret s) fun h =>
  .bin .eq h s fun c =>
  .eff () c fun _ =>
  .ret h

end Ast

/-! ## Denoted trees -/

/-- The denoted helper as an `ITree2` Kleisli arrow. -/
def sqD : Nat → M Nat := fun x =>
  Expr.denote (sqAssertAst x)

/-- The denoted recursive body, with self-calls represented by `CircE ⊕ CallEff`. -/
def bd : Nat →
    ITree2.CompE (ITree2.SumEff CircE.spec (ITree2.CallEff Nat Nat)) CircB.spec Nat := fun n =>
  Expr.denote (sumSqAst sqD n)

/-- The hand-reflected program tree. -/
def mainTree : M Nat :=
  Expr.denote (mainAst _)

/-- The source program tree, using the same scoped-bind nodes. -/
def mainSourceTree : M Nat :=
  evalC mainSrc

/-! ## Top-down reflection: discovering the AST by `apply`

Instead of writing the AST and proving it sound after the fact, construct the pair of an AST
and its soundness proof top-down.  The AST component starts as a metavariable, and each
`apply` of a `reflect_*` lemma emits one node while consuming one source node.

This ITree2 version has no `EffInterp`/`BindInterp` bridge: source and AST both denote into
the same `CircE.spec`/`CircB.spec` tree signature, so the proof relation is plain equality.
-/

/-- Reflect `pure`: emit `ret` on an atom whose defining equation matches the source value. -/
theorem reflect_ret {α : Tp0} (v : α.denote) {v' : α.denote} (h : v = v') :
    Expr.denote (.ret v : Expr CircE CircB Tp0.denote none α) = evalC (.pure v') := by
  rw [h]
  rfl

/-- Reflect a primitive: emit a `bin` node binding a fresh atom `vc` with its defining
    equation. -/
theorem reflect_bin {a b c α : Tp0} (o : Bin a b c) (va : a.denote) (vb : b.denote)
    {k : c.denote → Expr CircE CircB Tp0.denote none α} {t : M α.denote}
    (ih : ∀ vc, vc = o.denote va vb → Expr.denote (k vc) = t) :
    Expr.denote (.bin o va vb k) = t :=
  ih _ rfl

/-- Reflect an effect node.  The input side condition is discharged from the accumulated
    defining equations. -/
theorem reflect_eff {α : Tp0} (e : CircE.ε) (i : (CircE.𝓘 e).denote)
    {i' : (CircE.𝓘 e).denote}
    {k : (CircE.𝓞 e).denote → Expr CircE CircB Tp0.denote none α}
    {ks : (CircE.𝓞 e).denote → Circuit α.denote} (hi : i = i')
    (ih : ∀ o, Expr.denote (k o) = evalC (ks o)) :
    Expr.denote (.eff e i k) = evalC (Freek.eff e i' ks) := by
  subst hi
  show ITree2.CompE.bind (EffSig.trigger (𝓑 := CircB) e i) (fun o => Expr.denote (k o)) =
    ITree2.CompE.bind (EffSig.trigger (𝓑 := CircB) e i) (fun o => evalC (ks o))
  exact congrArg (ITree2.CompE.bind (EffSig.trigger (𝓑 := CircB) e i)) (funext ih)

/-- `sqAssertSrc`, reflected top-down: the AST component is the `_`, discovered by the
    `apply` trace along the source circuit. -/
def sqAssertReflected (x : Nat) :
    { e : Expr CircE CircB Tp0.denote none .nat //
      Expr.denote e = evalC (sqAssertSrc x) } :=
  ⟨_, by
    unfold sqAssertSrc Circuit.assert
    apply reflect_bin .mul x x
    intro y hy
    apply reflect_bin .le x y
    intro c hc
    apply reflect_eff () c
    · rw [hy] at hc
      exact hc
    · intro _
      apply reflect_ret y
      exact hy⟩

/-- The top-down proof trace reconstructs exactly the hand-written helper AST. -/
example (x : Nat) : (sqAssertReflected x).1 = sqAssertAst (V := Tp0.denote) x := rfl

/-! ## Third style: pack-returning combinators

The same top-down trace, but the `reflect_*` theorems become functions returning packed
`(AST, proof)` values.  Each `apply` invokes a function whose result literally contains the
emitted node, so the syntax is assembled by the combinators themselves.
-/

/-- A reflection of source `m`, conditional on pending defining equations `Φ`. -/
def Reflection (Φ : Prop) (α : Tp0) (m : Circuit α.denote) : Type 2 :=
  { e : Expr CircE CircB Tp0.denote none α //
    Φ → Expr.denote e = evalC m }

/-- Reflect `pure`: the pack's node is `ret v`; the value condition may assume `Φ`. -/
def Reflection.ret {Φ : Prop} {α : Tp0} (v : α.denote) {v' : α.denote}
    (h : Φ → v = v') : Reflection Φ α (.pure v') :=
  ⟨.ret v, fun hΦ => by
    rw [h hΦ]
    rfl⟩

/-- Reflect a primitive.  The continuation works under the extended equation context
    `Φ ∧ vc = o.denote va vb`, discharged here at the actual primitive result. -/
def Reflection.bin {Φ : Prop} {a b c α : Tp0} (o : Bin a b c)
    (va : a.denote) (vb : b.denote) {m : Circuit α.denote}
    (k : ∀ vc, Reflection (Φ ∧ vc = o.denote va vb) α m) :
    Reflection Φ α m :=
  ⟨.bin o va vb fun vc => (k vc).1, fun hΦ => (k _).2 ⟨hΦ, rfl⟩⟩

/-- Reflect an effect node. -/
def Reflection.eff {Φ : Prop} {α : Tp0} (e : CircE.ε) (i : (CircE.𝓘 e).denote)
    {i' : (CircE.𝓘 e).denote} (hi : Φ → i = i')
    {ks : (CircE.𝓞 e).denote → Circuit α.denote}
    (k : ∀ o, Reflection Φ α (ks o)) :
    Reflection Φ α (Freek.eff e i' ks) :=
  ⟨.eff e i fun o => (k o).1, fun hΦ => by
    rw [hi hΦ]
    show ITree2.CompE.bind (EffSig.trigger (𝓑 := CircB) e i') (fun o =>
        Expr.denote ((k o).1)) =
      ITree2.CompE.bind (EffSig.trigger (𝓑 := CircB) e i') (fun o => evalC (ks o))
    exact congrArg (ITree2.CompE.bind (EffSig.trigger (𝓑 := CircB) e i'))
      (funext fun o => (k o).2 hΦ)⟩

/-- `sqAssertSrc` reflected in the third style: the same `apply` trace, but every `apply`
    calls a pack-returning function. -/
def sqAssertReflected' (x : Nat) : Reflection True .nat (sqAssertSrc x) := by
  unfold sqAssertSrc Circuit.assert
  apply Reflection.bin .mul x x
  intro y
  apply Reflection.bin .le x y
  intro c
  apply Reflection.eff () c
  · rintro ⟨⟨-, hy⟩, hc⟩
    rw [hy] at hc
    exact hc
  · intro _
    apply Reflection.ret y
    rintro ⟨⟨-, hy⟩, -⟩
    exact hy

/-- The third style also reconstructs exactly the hand-written helper AST. -/
example (x : Nat) : (sqAssertReflected' x).1 = sqAssertAst (V := Tp0.denote) x := rfl

/-! ## Application-shaped reflection

The old generic application combinator used `Freek.eval_bind` against the target tree monad.
For `ITree2.CompE` that requires monad laws that have not yet been ported to `ITree2`, so this
version makes the source bind shape an explicit premise.  For concrete unfolded examples the
premise is definitional and can still be generated by the walk. -/

/-- Reflect a helper application. -/
def Reflection.app {Φ : Prop} {α a b : Tp0} (f : a.denote → M b.denote) (x : a.denote)
    {fSrc : a.denote → Circuit b.denote}
    (hf : Φ → f x = evalC (fSrc x))
    {ks : b.denote → Circuit α.denote}
    (hsrc : Φ → evalC (Freek.bind (fSrc x) ks) =
      ITree2.CompE.bind (evalC (fSrc x)) fun o => evalC (ks o))
    (k : ∀ o, Reflection Φ α (ks o)) :
    Reflection Φ α (Freek.bind (fSrc x) ks) :=
  ⟨.app f x fun o => (k o).1, fun hΦ => by
    calc
      ITree2.CompE.bind (f x) (fun o => Expr.denote ((k o).1))
          = ITree2.CompE.bind (evalC (fSrc x)) (fun o => Expr.denote ((k o).1)) := by
              rw [hf hΦ]
      _ = ITree2.CompE.bind (evalC (fSrc x)) (fun o => evalC (ks o)) := by
              exact congrArg (ITree2.CompE.bind (evalC (fSrc x)))
                (funext fun o => (k o).2 hΦ)
      _ = evalC (Freek.bind (fSrc x) ks) := (hsrc hΦ).symm⟩

end Example
end Ast2
end Freigen
