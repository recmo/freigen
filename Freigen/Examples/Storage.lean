import Freigen.Compile

/-!
# Storage effects

The storage example is expressed with the unified higher-order signature. Its
operations simply have no branches. This keeps storage on the same `Free`/`ITree`/relational
reflection path as scoped circuit effects.
-/

namespace Freigen.Ast.StorageExample

inductive StoreOp where
  | get
  | set

abbrev Source : ITree.HSig where
  op := StoreOp
  input
    | .get => Nat
    | .set => Nat × Nat
  output
    | .get => Nat
    | .set => Unit
  branch := fun _ => Empty
  branchInput := fun _ b => nomatch b
  branchOutput := fun _ b => nomatch b

abbrev Target : Signature where
  op := StoreOp
  input
    | .get => .nat
    | .set => .prod .nat .nat
  output
    | .get => .nat
    | .set => .unit
  branch := fun _ => Empty
  branchInput := fun _ b => nomatch b
  branchOutput := fun _ b => nomatch b

inductive StoreRel : StoreOp → StoreOp → Type where
  | get : StoreRel .get .get
  | set : StoreRel .set .set

@[ast_compat] abbrev Compat : Signature.Compat Source Target where
  opRel := StoreRel
  input
    | .get, source, target => source = target
    | .set, source, target =>
        source.1 = target.1 ∧ source.2 = target.2
  output
    | .get, source, target => source = target
    | .set, source, target => source = target
  branch := by
    intro _ _ _ source
    exact nomatch source
  branchInput := by
    intro _ _ _ source
    exact nomatch source
  branchOutput := by
    intro _ _ _ source
    exact nomatch source

@[ast_op] def getOp : OpSpec Compat StoreOp.get where
  target := .get
  witness := .get

@[ast_op] def setOp : OpSpec Compat StoreOp.set where
  target := .set
  witness := .set

@[ast_render] def render : RenderSpec Target where
  opName
    | .get => "get"
    | .set => "set"
  branches := fun _ => []

abbrev Store (A : Type) := Free Source A

@[ast_inline] def get (address : Nat) : Store Nat :=
  .op .get address (fun b => nomatch b) .pure

@[ast_inline] def set (address value : Nat) : Store Unit :=
  .op .set (address, value) (fun b => nomatch b) .pure

def run {A : Type} (program : Store A) : StateM (Nat → Nat) A :=
  Free.eval (H := Source) (M := StateM (Nat → Nat))
    (fun e input _ => match e with
      | StoreOp.get => fun store => (store input, store)
      | StoreOp.set =>
          fun store => ((), fun x => if x = input.1 then input.2 else store x)) program

def program : Store Nat := do
  set 0 42
  get 0

example : (run program).run' (fun _ => 0) = 42 := rfl

def getProgram : Store Nat := get 0

reflect_def reflected := getProgram

example : ITree.CompE.Eutt Compat Eq (Free.toITree getProgram)
    (Expr.denote (reflected (Tp.denote (ITree.CompE Target.spec)))) :=
  reflected_sound

-- Future acceptance target: pair-valued operation inputs are not yet reified generically.
-- reflect_def storeAndLoadReflected := program

end Freigen.Ast.StorageExample
