import Freigen.ITree2.Eutt

namespace Freigen

universe u v

/-! ## Unified higher-order source syntax -/

/-- Free syntax for higher-order operations with dynamically bound block arguments. -/
inductive Freek (H : ITree2.HSig.{u, v}) : Type u → Type (max u v + 1) where
  | pure {α} : α → Freek H α
  | op {α} (e : H.op) : H.input e →
      ((b : H.branch e) → H.branchInput e b → Freek H (H.branchOutput e b)) →
      (H.output e → Freek H α) → Freek H α

def Freek.bind {H} {α β} : Freek H α → (α → Freek H β) → Freek H β
  | .pure a, f => f a
  | .op e i blocks k, f => .op e i blocks fun o => (k o).bind f

instance {H} : Monad (Freek H) where
  pure := Freek.pure
  bind := Freek.bind

theorem Freek.bind_pure {H α} (m : Freek H α) : m.bind .pure = m := by
  induction m with
  | pure => rfl
  | op e i blocks k _ ih => exact congrArg (Freek.op e i blocks) (funext ih)

theorem Freek.bind_assoc {H} {α β γ} (m : Freek H α)
    (f : α → Freek H β) (g : β → Freek H γ) :
    (m.bind f).bind g = m.bind fun a => (f a).bind g := by
  induction m with
  | pure => rfl
  | op e i blocks k _ ih => exact congrArg (Freek.op e i blocks) (funext fun o => ih o f)

instance {H} : LawfulMonad (Freek H) :=
  LawfulMonad.mk' (Freek H)
    (fun m => Freek.bind_pure m)
    (fun _ _ => rfl)
    (fun m f g => Freek.bind_assoc m f g)

def Freek.eval {M : Type u → Type v} [Monad M] {H α}
    (evalOp : (e : H.op) → H.input e →
      ((b : H.branch e) → H.branchInput e b → M (H.branchOutput e b)) →
      M (H.output e)) : Freek H α → M α
  | .pure a => Pure.pure a
  | .op e i blocks k => do
      let o ← evalOp e i fun b x => Freek.eval evalOp (blocks b x)
      Freek.eval evalOp (k o)

theorem Freek.eval_bind {M : Type u → Type v} [Monad M] [LawfulMonad M] {H} {α β}
    (evalOp : (e : H.op) → H.input e →
      ((b : H.branch e) → H.branchInput e b → M (H.branchOutput e b)) →
      M (H.output e)) (m : Freek H α) (f : α → Freek H β) :
    Freek.eval evalOp (m.bind f) = Freek.eval evalOp m >>= fun a => Freek.eval evalOp (f a) := by
  induction m with
  | pure a =>
      exact (pure_bind (m := M) a (fun a => Freek.eval evalOp (f a))).symm
  | op e i blocks k _ ih =>
      simp only [Freek.bind, Freek.eval]
      rw [LawfulMonad.bind_assoc]
      exact congrArg _ (funext fun o => ih o f)

def Freek.toITree {H : ITree2.HSig.{u, v}} {α : Type u} :
    Freek H α → ITree2.CompE H α :=
  Freek.eval fun e i blocks =>
    ITree2.CompE.op e i (fun bx => blocks bx.1 bx.2) ITree2.CompE.ret

theorem Freek.toITree_bind {H : ITree2.HSig.{u, v}} {α β : Type u}
    (m : Freek H α) (f : α → Freek H β) :
    Freek.toITree (m.bind f) =
      ITree2.CompE.bind (Freek.toITree m) (fun a => Freek.toITree (f a)) :=
  Freek.eval_bind _ m f

/-!
## The object-type universe and the AST

A from-scratch restart of the AST.  What changes relative to `Freigen.Ast`:

* **Higher-order operations stay uninterpreted.** Ordinary effects are zero-branch operations;
  scoped constructs carry blocks that may dynamically bind values.
* **No `prog → defs → exprs` stratification.**  Function definitions — recursive or not — are
  a single inline `letrec` node, so the reflector can emit a definition in one pass, right
  where it is first encountered.
* **A self-call is a call event, not a first-class value.**  Inside a `letrec` body the
  definition reaches itself through the dedicated `selfCall` node, and the knot is tied by
  `mrec` — ITree-canon.  A first-class self is impossible: it would have to be a Kleisli arrow
  into the base domain *before* the knot exists.  The `Option (Tp × Tp)` **recursion-slot
  index** on `Expr` tracks the enclosing `letrec` statically. Operation blocks retain this slot,
  so recursive calls remain available beneath effects, handlers, and dynamic binders.
  *After* the knot, the continuation receives the definition as an ordinary first-class
  `V (.fn a b)` value.
* **Deliberately tiny universe**: `nat`/`bool`/products, first-order function binders, and a
  handful of primitives.

The reflector relates this AST to `Freek.toITree` in the same coinductive domain.
-/

namespace Ast2

/-! ### Object types -/

/-- First-order object types: exactly the types effects may exchange with the ITree event
    system. -/
inductive Tp0 : Type
  | nat  : Tp0
  | bool : Tp0
  | unit : Tp0
  | prod : Tp0 → Tp0 → Tp0

namespace Tp0

/-- Denote a first-order object type directly into Lean. -/
@[reducible] def denote : Tp0 → Type
  | .nat      => Nat
  | .bool     => Bool
  | .unit     => Unit
  | .prod a b => a.denote × b.denote

end Tp0

/-- The full object-language type universe: either a first-order type or a function type. -/
inductive Tp : Type
  | base : Tp0 → Tp
  | fn   : Tp → Tp → Tp

namespace Tp

abbrev nat : Tp := .base .nat
abbrev bool : Tp := .base .bool
abbrev unit : Tp := .base .unit
abbrev prod (a b : Tp0) : Tp := .base (.prod a b)

/-- Denote an object type over an arbitrary target monad `M`.  A function type denotes as a
    **Kleisli arrow into `M`** — a function value is a suspended, potentially effectful
    computation.  Quantifying the target keeps every downstream statement parametric in the
    interpreter.  Reducible so type-class search and unification see through it. -/
@[reducible] def denote (M : Type → Type) : Tp → Type
  | .base t => t.denote
  | .fn a b => a.denote M → M (b.denote M)

end Tp

/-! ### Reified primitive operations -/

/-- Unary primitives, indexed by (argument, result) first-order object type. -/
inductive Un : Tp0 → Tp0 → Type
  | not : Un .bool .bool
  | fst {a b : Tp0} : Un (.prod a b) a
  | snd {a b : Tp0} : Un (.prod a b) b

/-- Denote a unary primitive to its Lean operation. -/
def Un.denote {a b : Tp0} : Un a b → a.denote → b.denote
  | .not, x => !x
  | .fst, p => p.1
  | .snd, p => p.2

/-- Binary primitives, indexed by (left, right, result) first-order object type. -/
inductive Bin : Tp0 → Tp0 → Tp0 → Type
  | add : Bin .nat .nat .nat
  | sub : Bin .nat .nat .nat
  | mul : Bin .nat .nat .nat
  | eq  : Bin .nat .nat .bool
  | lt  : Bin .nat .nat .bool
  | le  : Bin .nat .nat .bool
  | and : Bin .bool .bool .bool
  | or  : Bin .bool .bool .bool
  | pair {a b : Tp0} : Bin a b (.prod a b)

/-- Denote a binary primitive to its Lean operation. -/
def Bin.denote {a b c : Tp0} :
    Bin a b c → a.denote → b.denote → c.denote
  | .add,  x, y => x + y
  | .sub,  x, y => x - y
  | .mul,  x, y => x * y
  | .eq,   x, y => x == y
  | .lt,   x, y => decide (x < y)
  | .le,   x, y => decide (x ≤ y)
  | .and,  x, y => x && y
  | .or,   x, y => x || y
  | .pair, x, y => (x, y)

/-! ### Unified higher-order AST -/

structure Signature : Type 1 where
  op : Type
  input : op → Tp0
  output : op → Tp0
  branch : op → Type
  branchInput : (e : op) → branch e → Tp0
  branchOutput : (e : op) → branch e → Tp0

@[reducible] def Signature.spec (H : Signature) : ITree2.HSig where
  op := H.op
  input := fun e => (H.input e).denote
  output := fun e => (H.output e).denote
  branch := H.branch
  branchInput := fun e b => (H.branchInput e b).denote
  branchOutput := fun e b => (H.branchOutput e b).denote

/-- An AST signature correspondence is the generic interaction-tree correspondence to its spec. -/
abbrev Signature.Compat (S : ITree2.HSig.{u, v}) (H : Signature) :=
  ITree2.HSig.Compat S H.spec

@[reducible] def DomR (H : Signature) : Option (Tp × Tp) → Type → Type
  | none => ITree2.CompE H.spec
  | some (a, b) => ITree2.CompE
      (ITree2.Sum H.spec
        (ITree2.Call (a.denote (ITree2.CompE H.spec)) (b.denote (ITree2.CompE H.spec))))

def DomR.ret {H : Signature} : {r : Option (Tp × Tp)} → {α : Type} → α → DomR H r α
  | none, _, x | some _, _, x => ITree2.CompE.ret x

def DomR.bind {H : Signature} : {r : Option (Tp × Tp)} → {α β : Type} →
    DomR H r α → (α → DomR H r β) → DomR H r β
  | none, _, _, m, k | some _, _, _, m, k => ITree2.CompE.bind m k

def DomR.lift {H : Signature} : {r : Option (Tp × Tp)} → {α : Type} →
    ITree2.CompE H.spec α → DomR H r α
  | none, _, t => t
  | some (a, b), _, t => ITree2.CompE.sumL
      (F := ITree2.Call (a.denote (ITree2.CompE H.spec))
        (b.denote (ITree2.CompE H.spec))) t

def DomR.perform {H : Signature} : {r : Option (Tp × Tp)} → (e : H.op) →
    (H.input e).denote →
    ((b : H.branch e) → (H.branchInput e b).denote →
      DomR H r (H.branchOutput e b).denote) →
    DomR H r (H.output e).denote
  | none, e, i, blocks => ITree2.CompE.op e i
      (fun bx => blocks bx.1 bx.2) ITree2.CompE.ret
  | some _, e, i, blocks => ITree2.CompE.op (.inl e) i
      (fun bx => blocks bx.1 bx.2) ITree2.CompE.ret

/-- PHOAS target for proof-erasing reflection. Operation blocks retain the ambient recursion
    slot and bind the value dynamically supplied to each branch. -/
inductive Expr (H : Signature) (V : Tp → Type) : Option (Tp × Tp) → Tp → Type 2 where
  | ret {r α} : V α → Expr H V r α
  | natLit {r α} : Nat → (V .nat → Expr H V r α) → Expr H V r α
  | boolLit {r α} : Bool → (V .bool → Expr H V r α) → Expr H V r α
  | unitLit {r α} : (V .unit → Expr H V r α) → Expr H V r α
  | un {r α a b} : Un a b → V (.base a) →
      (V (.base b) → Expr H V r α) → Expr H V r α
  | bin {r α a b c} : Bin a b c → V (.base a) → V (.base b) →
      (V (.base c) → Expr H V r α) → Expr H V r α
  | ite {r α β} : V .bool → Expr H V r β → Expr H V r β →
      (V β → Expr H V r α) → Expr H V r α
  | lam {r α a b} : (V a → Expr H V none b) →
      (V (.fn a b) → Expr H V r α) → Expr H V r α
  | app {r α a b} : V (.fn a b) → V a →
      (V b → Expr H V r α) → Expr H V r α
  | letrec {r α a b} : (V a → Expr H V (some (a, b)) b) →
      (V (.fn a b) → Expr H V r α) → Expr H V r α
  | selfCall {α a b} : V a → (V b → Expr H V (some (a, b)) α) →
      Expr H V (some (a, b)) α
  | op {r α} (e : H.op) : V (.base (H.input e)) →
      ((b : H.branch e) → V (.base (H.branchInput e b)) →
        Expr H V r (.base (H.branchOutput e b))) →
      (V (.base (H.output e)) → Expr H V r α) → Expr H V r α

def Expr.denote {H : Signature} : {r : Option (Tp × Tp)} → {α : Tp} →
    Expr H (Tp.denote (ITree2.CompE H.spec)) r α →
      DomR H r (α.denote (ITree2.CompE H.spec))
  | _, _, .ret v => DomR.ret v
  | _, _, .natLit n k => Expr.denote (k n)
  | _, _, .boolLit b k => Expr.denote (k b)
  | _, _, .unitLit k => Expr.denote (k ())
  | _, _, .un o x k => Expr.denote (k (o.denote x))
  | _, _, .bin o x y k => Expr.denote (k (o.denote x y))
  | _, _, .ite c t e k => DomR.bind (cond c (Expr.denote t) (Expr.denote e)) fun v =>
      Expr.denote (k v)
  | _, _, .lam body k => Expr.denote (k fun x => Expr.denote (body x))
  | _, _, .app f x k => DomR.bind (DomR.lift (f x)) fun v => Expr.denote (k v)
  | _, _, .letrec body k =>
      Expr.denote (k (ITree2.CompE.mrec fun x => Expr.denote (body x)))
  | _, _, .selfCall x k =>
      ITree2.CompE.op (Sum.inr ITree2.CallOp.call) x
        (fun bx => nomatch bx.1) fun v => Expr.denote (k v)
  | _, _, .op e i blocks k =>
      DomR.bind (DomR.perform e i fun b x => Expr.denote (blocks b x)) fun o =>
        Expr.denote (k o)

def Closed (H : Signature) (α : Tp) : Type 2 := ∀ V, Expr H V none α

end Ast2

end Freigen
