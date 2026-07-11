import Freigen.Ast2.Compile

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

@[ast2_render] def circRender : RenderSpec Circ where
  opName
    | .assert => "assert"
    | .hint _ => "hint"
  branches
    | .assert => []
    | .hint _ => [()]

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

@[ast2_compat] abbrev CircCompat : Signature.Compat Source Circ where
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

@[ast2_op] def circAssertOp : OpSpec CircCompat SourceOp.assert where
  target := .assert
  witness := .assert

@[ast2_op] def circHintOp (repr : ReprSpec α) : OpSpec CircCompat (SourceOp.hint α) where
  target := .hint repr.code
  witness := .hint α repr.code repr.relates

def fin5NatRel : Fin 5 → Nat → Prop := fun source target => source.val = target

def fin5Hint : CircRel (.hint (Fin 5)) (.hint .nat) :=
  .hint (Fin 5) .nat fin5NatRel

theorem fin5NatRel_target (target : Nat) (h : target < 5) :
    ∃ source : Fin 5, fin5NatRel source target :=
  ⟨⟨target, h⟩, rfl⟩

abbrev Circuit (α : Type) := Freek Source α

abbrev M := ITree2.CompE Circ.spec

@[ast2_inline] def Circuit.assert (condition : Bool) : Circuit Unit :=
  .op SourceOp.assert condition (fun b => nomatch b) .pure

@[ast2_inline] def Circuit.hint {α : Type} (block : Circuit α) : Circuit α :=
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

#reflect_plan mainSrc

def mainMacroReflected := reflect% mainSrc

example : ITree2.CompE.Eutt CircCompat Eq
    (Freek.toITree mainSrc) (Expr.denote (mainMacroReflected.1 (Tp.denote M))) :=
  mainMacroReflected.2

example : ∃ (body : Nat → Expr Circ (Tp.denote M) none .nat)
    (k : (Nat → M Nat) → Expr Circ (Tp.denote M) none .nat),
    (mainMacroReflected.1 (Tp.denote M)).stripSource =
      @Expr.lam Circ (Tp.denote M) none .nat .nat .nat body k := by
  refine ⟨_, _, rfl⟩

def symbolicHelperMain : Circuit Nat := do
  let x ← Circuit.hint (pure 4)
  sqAssertSrc x

#reflect_plan symbolicHelperMain

def symbolicHelperReflected := reflect% symbolicHelperMain

reflect_def symbolicHelperNamed := symbolicHelperMain

def triangularSrc : Nat → Circuit Nat
  | 0 => pure 0
  | n + 1 => do
      let subtotal ← triangularSrc n
      pure (subtotal + n + 1)

def symbolicRecursiveMain : Circuit Nat := do
  let n ← Circuit.hint (pure 5)
  triangularSrc n

#reflect_plan symbolicRecursiveMain

reflect_def symbolicRecursiveReflected := symbolicRecursiveMain

example : ITree2.CompE.Eutt CircCompat Eq
    (Freek.toITree symbolicRecursiveMain)
    (Expr.denote (symbolicRecursiveReflected (Tp.denote M))) :=
  symbolicRecursiveReflected_sound

example : (symbolicRecursiveReflected (Tp.denote M)).leadingSourceRanges.length ≥ 2 := by
  decide

#compile symbolicRecursiveMain => "build/ast2-symbolic-recursive.prog"

example : ∃ (body : Nat → Expr Circ (Tp.denote M) none .nat)
    (k : (Nat → M Nat) → Expr Circ (Tp.denote M) none .nat),
    (symbolicHelperReflected.1 (Tp.denote M)).stripSource =
      @Expr.lam Circ (Tp.denote M) none .nat .nat .nat body k := by
  refine ⟨_, _, rfl⟩

example : ITree2.CompE.Eutt CircCompat Eq
    (Freek.toITree symbolicHelperMain)
    (Expr.denote (symbolicHelperReflected.1 (Tp.denote M))) :=
  symbolicHelperReflected.2

example : ITree2.CompE.Eutt CircCompat Eq
    (Freek.toITree symbolicHelperMain) (Expr.denote (symbolicHelperNamed (Tp.denote M))) :=
  symbolicHelperNamed_sound

def twiceSqAssertSrc (x : Nat) : Circuit Nat := do
  let y ← sqAssertSrc x
  sqAssertSrc y

def nestedHelperMain : Circuit Nat := do
  let x ← Circuit.hint (pure 2)
  twiceSqAssertSrc x

#reflect_plan nestedHelperMain

reflect_def nestedHelperReflected := nestedHelperMain

def addTwoSrc (x y : Nat) : Circuit Nat :=
  pure (x + y)

def tupledHelperMain : Circuit Nat := do
  let x ← Circuit.hint (pure 8)
  let y ← Circuit.hint (pure 13)
  addTwoSrc x y

#reflect_plan tupledHelperMain

reflect_def tupledHelperReflected := tupledHelperMain

example : ITree2.CompE.Eutt CircCompat Eq
    (Freek.toITree tupledHelperMain)
    (Expr.denote (tupledHelperReflected (Tp.denote M))) :=
  tupledHelperReflected_sound

example : (nestedHelperReflected (Tp.denote M)).sourceRange?.isSome := by decide

example : ITree2.CompE.Eutt CircCompat Eq
    (Freek.toITree nestedHelperMain) (Expr.denote (nestedHelperReflected (Tp.denote M))) :=
  nestedHelperReflected_sound

def discardHint {α : Type} (x : α) : Circuit Unit := do
  let _ ← Circuit.hint (pure x)
  pure ()

def staticSpecializationMain : Circuit Unit := do
  let _ ← discardHint 5
  discardHint true

#reflect_plan staticSpecializationMain

reflect_def staticSpecializationReflected := staticSpecializationMain

example : ITree2.CompE.Eutt CircCompat Eq
    (Freek.toITree staticSpecializationMain)
    (Expr.denote (staticSpecializationReflected (Tp.denote M))) :=
  staticSpecializationReflected_sound

def pureReflected := reflect% (pure 7 : Circuit Nat)

example : (pureReflected.1 (Tp.denote M)).stripSource =
    Expr.natLit 7 (fun n => .ret n) := rfl

example : (pureReflected.1 (Tp.denote M)).sourceRange?.isSome := by decide

example : ITree2.CompE.Eutt CircCompat Eq
    (Freek.toITree (pure 7 : Circuit Nat))
    (Expr.denote (pureReflected.1 (Tp.denote M))) :=
  pureReflected.2

def hintMacroReflected := reflect% (Circuit.hint (pure 7 : Circuit Nat))

def assertMacroReflected := reflect% (Circuit.assert true)

example : ITree2.CompE.Eutt CircCompat Eq
    (Freek.toITree (Circuit.hint (pure 7 : Circuit Nat)))
    (Expr.denote (hintMacroReflected.1 (Tp.denote M))) :=
  hintMacroReflected.2

example : ITree2.CompE.Eutt CircCompat Eq
    (Freek.toITree (Circuit.assert true))
    (Expr.denote (assertMacroReflected.1 (Tp.denote M))) :=
  assertMacroReflected.2

def finHintSource : Circuit (Fin 5) :=
  Circuit.hint (pure ⟨3, by decide⟩)

def finHintMacroReflected := reflect% finHintSource

/-- This theorem demonstrates the intended partial representation: the generated target returns a
    `Nat`; soundness relates it to the source `Fin 5` by value equality, without claiming an
    equivalence between the two types. -/
example : ITree2.CompE.Eutt CircCompat fin5NatRel
    (Freek.toITree finHintSource)
    (Expr.denote (finHintMacroReflected.1 (Tp.denote M))) :=
  finHintMacroReflected.2

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
