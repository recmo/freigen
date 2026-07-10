import Freigen.Ast2.Reflect

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

abbrev M : Type → Type := ITree2.CompE CircE.spec CircB.spec

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

/-- `sqAssertSrc`, reflected top-down: the AST component is the `_`, discovered by the
    `apply` trace along the source circuit. -/
def sqAssertReflected (x : Nat) :
    { e : Expr CircE CircB Tp0.denote none .nat //
      Expr.denote e = evalC (sqAssertSrc x) } :=
  ⟨_, by
    unfold sqAssertSrc Circuit.assert
    change Expr.denote (_ : Expr CircE CircB Tp0.denote none .nat) =
      Freek.toITree
        (Freek.eff (𝓔 := CircE.spec) (𝓑 := CircB.spec) ()
          (decide (x ≤ x * x)) (fun _ => Freek.pure (x * x)))
    apply reflect_bin .mul x x
    intro y hy
    apply reflect_bin .le x y
    intro c hc
    apply reflect_eff (𝓔 := CircE) (𝓑 := CircB) () c
    · rw [hy] at hc
      exact hc
    · intro _
      apply reflect_ret y
      exact hy⟩

/-- The top-down proof trace reconstructs exactly the hand-written helper AST. -/
example (x : Nat) : (sqAssertReflected x).1 = sqAssertAst (V := Tp0.denote) x := rfl

/-! ## Third style: pack-returning combinators -/

/-- `sqAssertSrc` reflected in the third style: the same `apply` trace, but every `apply`
    calls a pack-returning function. -/
def sqAssertReflected' (x : Nat) :
    Reflection (𝓔 := CircE) (𝓑 := CircB) True .nat (sqAssertSrc x) := by
  unfold sqAssertSrc Circuit.assert
  change Reflection (𝓔 := CircE) (𝓑 := CircB) True .nat
    (Freek.eff (𝓔 := CircE.spec) (𝓑 := CircB.spec) ()
      (decide (x ≤ x * x)) (fun _ => Freek.pure (x * x)))
  apply Reflection.bin .mul x x
  intro y
  apply Reflection.bin .le x y
  intro c
  apply Reflection.eff (𝓔 := CircE) (𝓑 := CircB) () c
  · rintro ⟨⟨-, hy⟩, hc⟩
    rw [hy] at hc
    exact hc
  · intro _
    apply Reflection.ret y
    rintro ⟨⟨-, hy⟩, -⟩
    exact hy

/-- The third style also reconstructs exactly the hand-written helper AST. -/
example (x : Nat) : (sqAssertReflected' x).1 =
    sqAssertAst (V := Tp0.denote) x := rfl

end Example
end Ast2
end Freigen
