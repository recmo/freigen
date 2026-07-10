import Freigen.Ast2.Reflect

/-! A hand-reflected circuit over the unified higher-order `Freek`/`Expr` API. -/

namespace Freigen
namespace Ast2
namespace Example

inductive CircOp where
  | assert
  | hint (result : Tp0)

abbrev Circ : Signature where
  op := CircOp
  input
    | .assert => .bool
    | .hint _ => .unit
  output
    | .assert => .unit
    | .hint result => result
  branch
    | .assert => Empty
    | .hint _ => Unit
  branchInput := fun
    | .assert, b => nomatch b
    | .hint _, _ => .unit
  branchOutput := fun
    | .assert, b => nomatch b
    | .hint result, _ => result

abbrev Circuit := Freek Circ.spec
abbrev M := ITree2.CompE Circ.spec

def Circuit.assert (condition : Bool) : Circuit Unit :=
  .op .assert condition (fun b => nomatch b) .pure

def Circuit.hint (result : Tp0) (block : Circuit result.denote) : Circuit result.denote :=
  .op (.hint result) () (fun _ _ => block) .pure

def Circuit.evalWithHints : Circuit alpha → Option alpha :=
  Freek.eval fun
    | .assert, condition, _ => if condition then some () else none
    | .hint _, _, blocks => blocks () ()

def ConstraintM (alpha : Type) := (alpha → Prop) → Prop

instance : Monad ConstraintM where
  pure a := fun k => k a
  bind m f := fun k => m fun a => f a k

def Circuit.evalConstraints : Circuit alpha → ConstraintM alpha :=
  Freek.eval fun
    | .assert, condition, _ => fun k => condition ∧ k ()
    | .hint _, _, _ => fun k => ∃ x, k x

def sqAssertSrc (x : Nat) : Circuit Nat := do
  let y := x * x
  let _ ← Circuit.assert (decide (x ≤ y))
  pure y

def sumSqSrc : Nat → Circuit Nat
  | 0 => pure 0
  | n + 1 => do
      let s ← sumSqSrc n
      let y ← sqAssertSrc (n + 1)
      pure (s + y)

def mainSrc : Circuit Nat := do
  let s ← sumSqSrc 3
  let h ← Circuit.hint .nat (pure s)
  let _ ← Circuit.assert (h == s)
  pure h

section Ast

variable {V : Tp → Type}

def sqAssertAst (x : V .nat) : Expr Circ V none .nat :=
  .bin .mul x x fun y =>
  .bin .le x y fun condition =>
  .op .assert condition (fun b => nomatch b) fun _ =>
  .ret y

def sumSqAst (sq : V (.fn .nat .nat)) (n : V .nat) :
    Expr Circ V (some (.nat, .nat)) .nat :=
  .natLit 0 fun zero =>
  .bin .eq n zero fun condition =>
  .ite condition
    (.ret zero)
    (.natLit 1 fun one =>
      .bin .sub n one fun n' =>
      .selfCall n' fun s =>
      .app sq n fun y =>
      .bin .add s y fun result =>
      .ret result)
    fun value => .ret value

def mainAst : Closed Circ .nat := fun _ =>
  .lam sqAssertAst fun sq =>
  .letrec (sumSqAst sq) fun sumSq =>
  .natLit 3 fun three =>
  .app sumSq three fun s =>
  .unitLit fun unit =>
  .op (.hint .nat) unit (fun _ _ => .ret s) fun h =>
  .bin .eq h s fun condition =>
  .op .assert condition (fun b => nomatch b) fun _ =>
  .ret h

def identityAst : Closed Circ (.fn .nat .nat) := fun _ =>
  .lam (fun x => .ret x) fun identity =>
  .ret identity

end Ast

def sqD (x : Nat) : M Nat := Expr.denote (sqAssertAst x)

def recursiveBody (n : Nat) :
    ITree2.CompE (ITree2.Sum Circ.spec (ITree2.Call Nat Nat)) Nat :=
  Expr.denote (sumSqAst sqD n)

def mainTree : M Nat := Expr.denote (mainAst _)
def mainSourceTree : M Nat := Freek.toITree mainSrc

def identityTree : M (Nat → M Nat) := Expr.denote (identityAst _)

example : ITree2.CompE.bind identityTree (fun f => f 7) =
    ITree2.CompE.ret 7 := by
  change ITree2.CompE.bind (ITree2.CompE.ret (fun x => ITree2.CompE.ret x))
    (fun f => f 7) = ITree2.CompE.ret 7
  rw [ITree2.CompE.bind_ret]

def sqAssertReflected (x : Nat) : Reflection (H := Circ) True .nat (sqAssertSrc x) := by
  unfold sqAssertSrc Circuit.assert
  apply Reflection.bin .mul x x
  intro y
  apply Reflection.bin .le x y
  intro condition
  apply Reflection.op (H := Circ) CircOp.assert condition
    (i' := decide (x ≤ x * x))
  · rintro ⟨⟨-, hy⟩, hc⟩
    rw [hy] at hc
    exact hc
  · intro b
    exact nomatch b
  · intro _
    apply Reflection.ret y
    rintro ⟨⟨-, hy⟩, -⟩
    exact hy

/-! A dynamic binder used beneath recursion, which the previous two-channel AST rejected. -/

inductive DynOp where
  | withNat

abbrev DynSig : Signature where
  op := DynOp
  input := fun _ => .unit
  output := fun _ => .nat
  branch := fun _ => Unit
  branchInput := fun _ _ => .nat
  branchOutput := fun _ _ => .nat

def recursiveDynamicBlock {V : Tp → Type} (_n : V .nat) :
    Expr DynSig V (some (.nat, .nat)) .nat :=
  .unitLit fun unit =>
  .op .withNat unit
    (fun _ x => .selfCall x fun y => .ret y)
    fun y => .ret y

def dynamicSource : Freek DynSig.spec Nat :=
  .op .withNat () (fun _ x => .pure x) .pure

end Example
end Ast2
end Freigen
