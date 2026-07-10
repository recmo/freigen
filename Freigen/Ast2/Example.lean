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

inductive SourceOp : Type 1 where
  | assert
  | hint (result : Type)

/-- The circuit author's signature contains host types only; it has no dependency on `Tp0`. -/
abbrev Source : ITree2.HSig.{0, 1} where
  op := SourceOp
  input
    | .assert => Bool
    | .hint _ => Unit
  output
    | .assert => Unit
    | .hint result => result
  branch
    | .assert => Empty
    | .hint _ => Unit
  branchInput
    | .assert, b => nomatch b
    | .hint _, _ => Unit
  branchOutput
    | .assert, b => nomatch b
    | .hint result, _ => result

inductive CircRel : SourceOp → CircOp → Type 1 where
  | assert : CircRel .assert .assert
  | hint (result : Type) (code : Tp0) (repr : result → code.denote → Prop) :
      CircRel (.hint result) (.hint code)

abbrev CircCompat : Signature.Compat Source Circ where
  opRel := CircRel
  input
    | .assert, source, target => source = target
    | .hint _ _ _, source, target => source = target
  output
    | .assert, source, target => source = target
    | .hint _ _ repr, source, target => repr source target
  branch
    | .assert, source, _ => nomatch source
    | .hint _ _ _, source, target => source = target
  branchInput := by
    intro e h w bs bt hbr source target
    cases w with
    | assert => exact nomatch bs
    | hint => exact source = target
  branchOutput := by
    intro e h w bs bt hbr source target
    cases w with
    | assert => exact nomatch bs
    | hint _ _ repr => exact repr source target

def fin5NatRel : Fin 5 → Nat → Prop := fun source target => source.val = target

def fin5Hint : CircRel (.hint (Fin 5)) (.hint .nat) :=
  .hint (Fin 5) .nat fin5NatRel

theorem fin5NatRel_target (target : Nat) (h : target < 5) :
    ∃ source : Fin 5, fin5NatRel source target :=
  ⟨⟨target, h⟩, rfl⟩

abbrev Circuit (α : Type) := Freek Source α

abbrev M := ITree2.CompE Circ.spec

def Circuit.assert (condition : Bool) : Circuit Unit :=
  .op SourceOp.assert condition (fun b => nomatch b) .pure

def Circuit.hint {α : Type} (block : Circuit α) : Circuit α :=
  .op (.hint α) () (fun _ _ => block) .pure

def Circuit.evalWithHints (program : Circuit α) : Option α :=
  Freek.eval (H := Source) (M := Option) (fun
    | SourceOp.assert, condition, _ => if condition then some () else none
    | SourceOp.hint _, _, blocks => blocks () ()) program

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
  let h ← Circuit.hint (pure s)
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

def identityTree : M (Nat → M Nat) := Expr.denote (identityAst _)

example : ITree2.CompE.bind identityTree (fun f => f 7) =
    ITree2.CompE.ret 7 := by
  change ITree2.CompE.bind (ITree2.CompE.ret (fun x => ITree2.CompE.ret x))
    (fun f => f 7) = ITree2.CompE.ret 7
  rw [ITree2.CompE.bind_ret]

def sqAssertReflected (x : Nat) :
    ReflectionR CircCompat True .nat Eq
      (sqAssertSrc x) := by
  unfold sqAssertSrc Circuit.assert
  apply Reflection.bin .mul x x
  intro y
  apply Reflection.bin .le x y
  intro condition
  apply Reflection.op CircCompat SourceOp.assert CircOp.assert CircRel.assert condition
    (sourceInput := decide (x ≤ x * x))
  · rintro ⟨⟨-, hy⟩, hc⟩
    rw [hy] at hc
    exact hc.symm
  · intro b _
    exact nomatch b
  · intro _
    refine ⟨.ret y, ?_⟩
    intro _ _
    refine ⟨fun hPhi => ?_⟩
    apply ITree2.CompE.Eutt.of_step CircCompat
    exact .ret _ (x * x) y hPhi.1.2.symm

def hintReflected (x : Nat) :
    ReflectionR CircCompat True .nat Eq
      (Circuit.hint (pure x)) := by
  unfold Circuit.hint
  apply Reflection.op CircCompat (SourceOp.hint Nat) (CircOp.hint .nat)
    (CircRel.hint Nat .nat Eq) ()
    (sourceInput := ())
  · intro _
    rfl
  · intro _ _
    refine ⟨.ret x, ?_⟩
    intro _ _ _ _
    refine ⟨fun _ => ?_⟩
    apply ITree2.CompE.Eutt.of_step CircCompat
    exact .ret _ x x rfl
  · intro output
    refine ⟨.ret output, ?_⟩
    intro source hsource
    refine ⟨fun _ => ?_⟩
    apply ITree2.CompE.Eutt.of_step CircCompat
    exact .ret _ source output hsource

/-! A dynamic binder used beneath recursion. -/

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
