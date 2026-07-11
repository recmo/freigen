import Freigen.Free

namespace Freigen

universe u v

/-!
## The object-type universe and the AST

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

The reflector relates this AST to `Free.toITree` in the same coinductive domain.
-/

namespace Ast

/-- A source range retained by reflection. Positions use Lean's one-based line and zero-based
    Unicode-column convention. `module` identifies the source file through the Lean search path. -/
structure SourceRange where
  module : Lean.Name
  startLine : Nat
  startColumn : Nat
  endLine : Nat
  endColumn : Nat
  deriving Repr, DecidableEq

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

@[reducible] def Signature.spec (H : Signature) : ITree.HSig where
  op := H.op
  input := fun e => (H.input e).denote
  output := fun e => (H.output e).denote
  branch := H.branch
  branchInput := fun e b => (H.branchInput e b).denote
  branchOutput := fun e b => (H.branchOutput e b).denote

/-- An AST signature correspondence is the generic interaction-tree correspondence to its spec. -/
abbrev Signature.Compat (S : ITree.HSig.{u, v}) (H : Signature) :=
  ITree.HSig.Compat S H.spec

@[reducible] def DomSig (H : Signature) : Option (Tp × Tp) → ITree.HSig
  | none => H.spec
  | some (a, b) => ITree.Sum H.spec
      (ITree.Call (a.denote (ITree.CompE H.spec)) (b.denote (ITree.CompE H.spec)))

@[reducible] def DomSig.baseOp (H : Signature) : (r : Option (Tp × Tp)) → H.op → (DomSig H r).op
  | none, e => e
  | some _, e => .inl e

abbrev Signature.CompatAt (S : ITree.HSig.{u, v}) (H : Signature)
    (r : Option (Tp × Tp)) := ITree.HSig.Compat S (DomSig H r)

@[reducible] def DomR (H : Signature) (r : Option (Tp × Tp)) : Type → Type :=
  ITree.CompE (DomSig H r)

def DomR.ret {H : Signature} : {r : Option (Tp × Tp)} → {α : Type} → α → DomR H r α
  | none, _, x | some _, _, x => ITree.CompE.ret x

def DomR.bind {H : Signature} : {r : Option (Tp × Tp)} → {α β : Type} →
    DomR H r α → (α → DomR H r β) → DomR H r β
  | none, _, _, m, k | some _, _, _, m, k => ITree.CompE.bind m k

def DomR.lift {H : Signature} : {r : Option (Tp × Tp)} → {α : Type} →
    ITree.CompE H.spec α → DomR H r α
  | none, _, t => t
  | some (a, b), _, t => ITree.CompE.sumL
      (F := ITree.Call (a.denote (ITree.CompE H.spec))
        (b.denote (ITree.CompE H.spec))) t

def DomR.perform {H : Signature} : {r : Option (Tp × Tp)} → (e : H.op) →
    (H.input e).denote →
    ((b : H.branch e) → (H.branchInput e b).denote →
      DomR H r (H.branchOutput e b).denote) →
    DomR H r (H.output e).denote
  | none, e, i, blocks => ITree.CompE.op e i
      (fun bx => blocks bx.1 bx.2) ITree.CompE.ret
  | some _, e, i, blocks => ITree.CompE.op (.inl e) i
      (fun bx => blocks bx.1 bx.2) ITree.CompE.ret

/-- PHOAS target for proof-erasing reflection. Operation blocks retain the ambient recursion
    slot and bind the value dynamically supplied to each branch. -/
inductive Expr (H : Signature) (V : Tp → Type) : Option (Tp × Tp) → Tp → Type 2 where
  | source {r α} : SourceRange → Expr H V r α → Expr H V r α
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
    Expr H (Tp.denote (ITree.CompE H.spec)) r α →
      DomR H r (α.denote (ITree.CompE H.spec))
  | _, _, .source _ body => Expr.denote body
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
      Expr.denote (k (ITree.CompE.mrec fun x => Expr.denote (body x)))
  | _, _, .selfCall x k =>
      ITree.CompE.bind
        (ITree.CompE.op (Sum.inr ITree.CallOp.call) x
          (fun bx => nomatch bx.1) ITree.CompE.ret)
        fun v => Expr.denote (k v)
  | _, _, .op e i blocks k =>
      DomR.bind (DomR.perform e i fun b x => Expr.denote (blocks b x)) fun o =>
        Expr.denote (k o)

/-- Remove leading provenance annotations for structural consumers that do not need them. -/
def Expr.stripSource {H : Signature} {V : Tp → Type} :
    {r : Option (Tp × Tp)} → {α : Tp} → Expr H V r α → Expr H V r α
  | _, _, .source _ body => body.stripSource
  | _, _, body => body

def Expr.sourceRange? {H : Signature} {V : Tp → Type} {r : Option (Tp × Tp)} {α : Tp} :
    Expr H V r α → Option SourceRange
  | .source range _ => some range
  | _ => none

def Expr.leadingSourceRanges {H : Signature} {V : Tp → Type} :
    {r : Option (Tp × Tp)} → {α : Tp} → Expr H V r α → List SourceRange
  | _, _, .source range body => range :: body.leadingSourceRanges
  | _, _, _ => []

def Closed (H : Signature) (α : Tp) : Type 2 := ∀ V, Expr H V none α

/-- A typed environment for the first-order arguments of a reflected main program. -/
inductive MainArgs (V : Tp0 → Type) : List Tp0 → Type 1 where
  | nil : MainArgs V []
  | cons : V α → MainArgs V αs → MainArgs V (α :: αs)

namespace MainArgs

def map {V W : Tp0 → Type} (f : ∀ α, V α → W α) :
    {αs : List Tp0} → MainArgs V αs → MainArgs W αs
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons (f _ x) (xs.map f)

end MainArgs

/-- Closed AST program with an external, first-order main-argument telescope.  Specialized helper
    definitions are represented by nested `Expr.letrec` nodes in `main`. -/
structure Program (H : Signature) (args : List Tp0) (α : Tp) : Type 2 where
  main : ∀ V, MainArgs (fun t => V (.base t)) args → Expr H V none α

def Program.denote {H : Signature} {args : List Tp0} {α : Tp}
    (p : Program H args α)
    (xs : MainArgs Tp0.denote args) : ITree.CompE H.spec (α.denote (ITree.CompE H.spec)) :=
  Expr.denote (p.main _ xs)

end Ast

end Freigen
