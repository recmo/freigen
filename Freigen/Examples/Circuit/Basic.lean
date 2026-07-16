import Freigen.Compile

/-! A hand-reflected circuit over the unified higher-order `Free`/`Expr` API. -/

namespace Freigen
namespace Ast
namespace Example

inductive CircOp where
  | assert
  | hint (result : Tp)

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

@[ast_render] def circRender : RenderSpec Circ where
  opName
    | .assert => "assert"
    | .hint _ => "hint"
  branches
    | .assert => []
    | .hint _ => [()]

inductive SourceOp : Type 1 where
  | assert
  | hint (result : Type)

/-- The circuit author's signature contains host types only. -/
abbrev Source : ITree.HSig.{0, 1} where
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

inductive CircRel (ctx : DefCtx) : SourceOp → CircOp → Type 1 where
  | assert : CircRel ctx .assert .assert
  | hint (result : Type) (code : Tp) (repr : result → code.denote ctx → Prop) :
      CircRel ctx (.hint result) (.hint code)

@[ast_compat] abbrev CircCompat : ∀ ctx, Signature.Compat Source Circ ctx := fun ctx => {
  opRel := CircRel ctx
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
}

@[ast_op] def circAssertOp {ctx} : OpSpec (CircCompat ctx) SourceOp.assert where
  target := .assert
  witness := CircRel.assert

@[ast_op] def circHintOp {ctx} (repr : ReprSpec α) :
    OpSpec (CircCompat ctx) (SourceOp.hint α) where
  target := .hint repr.code
  witness := CircRel.hint α repr.code repr.relates

abbrev Circuit (α : Type) := Free Source α

@[ast_inline] def Circuit.assert (condition : Bool) : Circuit Unit :=
  .op SourceOp.assert condition (fun b => nomatch b) .pure

@[ast_inline] def Circuit.hint {α : Type} (block : Circuit α) : Circuit α :=
  .op (.hint α) () (fun _ _ => block) .pure

def Circuit.evalWithHints (program : Circuit α) : Option α :=
  Free.eval (H := Source) (M := Option) (fun
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

example : ITree.CompE.Eutt (CircCompat _) Eq
    (Free.toITree mainSrc) (Closed.denote mainMacroReflected.1) :=
  mainMacroReflected.2

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

example : ITree.CompE.Eutt (CircCompat _) Eq
    (Free.toITree symbolicRecursiveMain)
    (Closed.denote symbolicRecursiveReflected) :=
  symbolicRecursiveReflected_sound

#compile symbolicRecursiveMain => "build/symbolic-recursive.prog"

example : ITree.CompE.Eutt (CircCompat _) Eq
    (Free.toITree symbolicHelperMain)
    (Closed.denote symbolicHelperReflected.1) :=
  symbolicHelperReflected.2

example : ITree.CompE.Eutt (CircCompat _) Eq
    (Free.toITree symbolicHelperMain) (Closed.denote symbolicHelperNamed) :=
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

example : ITree.CompE.Eutt (CircCompat _) Eq
    (Free.toITree tupledHelperMain)
    (Closed.denote tupledHelperReflected) :=
  tupledHelperReflected_sound

example : ITree.CompE.Eutt (CircCompat _) Eq
    (Free.toITree nestedHelperMain) (Closed.denote nestedHelperReflected) :=
  nestedHelperReflected_sound

def discardHint {α : Type} (x : α) : Circuit Unit := do
  let _ ← Circuit.hint (pure x)
  pure ()

def staticSpecializationMain : Circuit Unit := do
  let _ ← discardHint 5
  discardHint true

#reflect_plan staticSpecializationMain

reflect_def staticSpecializationReflected := staticSpecializationMain

example : ITree.CompE.Eutt (CircCompat _) Eq
    (Free.toITree staticSpecializationMain)
    (Closed.denote staticSpecializationReflected) :=
  staticSpecializationReflected_sound

def pureReflected := reflect% (pure 7 : Circuit Nat)

example : ITree.CompE.Eutt (CircCompat _) Eq
    (Free.toITree (pure 7 : Circuit Nat))
    (Closed.denote pureReflected.1) :=
  pureReflected.2

def hintMacroReflected := reflect% (Circuit.hint (pure 7 : Circuit Nat))

def assertMacroReflected := reflect% (Circuit.assert true)

example : ITree.CompE.Eutt (CircCompat _) Eq
    (Free.toITree (Circuit.hint (pure 7 : Circuit Nat)))
    (Closed.denote hintMacroReflected.1) :=
  hintMacroReflected.2

example : ITree.CompE.Eutt (CircCompat _) Eq
    (Free.toITree (Circuit.assert true))
    (Closed.denote assertMacroReflected.1) :=
  assertMacroReflected.2

/-- `main` may expose first-order arguments even though `reflect%` currently emits closed programs. -/
def argumentMain : Code Circ [.nat] .nat where
  ctx := []
  program := fun _ => {
    defs := .nil
    main := fun
      | .cons x .nil => .ret x
  }

example : Code.denote argumentMain (.cons 7 .nil) =
    ITree.CompE.ret 7 := by
  simp only [Code.denote, argumentMain, Expr.denote, ITree.CompE.interpHandler_ret]

end Example
end Ast
end Freigen
