import Freigen.Free

namespace Freigen

universe u v

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

/-! ## Object types and stratified definition references -/

/-- The complete object-language type universe. Function values are explicit closures rather than
Lean functions, so every type has one monad-independent runtime representation. -/
inductive Tp : Type
  | nat
  | int
  | bool
  | unit
  | prod : Tp → Tp → Tp
  | fn : Tp → Tp → Tp
  deriving DecidableEq

/-- A definition's captured environment, explicit argument, and result types. -/
structure DefSig where
  captures : Tp
  input : Tp
  output : Tp
  deriving DecidableEq

/-- New definitions are added at the head. A definition body can name itself and entries in its
tail, but cannot name definitions introduced later. -/
abbrev DefCtx := List DefSig

/-- A typed de Bruijn reference into a definition context. The first index is the closure
environment carried by values referring to the definition. -/
inductive DefRef : DefCtx → Tp → Tp → Tp → Type where
  | here : DefRef (decl :: prior) decl.captures decl.input decl.output
  | there : DefRef prior captures input output →
      DefRef (decl :: prior) captures input output

namespace DefRef

def weaken (decl : DefSig) :
    DefRef ctx captures input output →
      DefRef (decl :: ctx) captures input output :=
  .there

end DefRef

/-- Evidence that `large` extends `small` only by adding newer definitions. -/
inductive Extension (small : DefCtx) : DefCtx → Type where
  | refl : Extension small small
  | step : Extension small large → Extension small (decl :: large)

namespace Extension

def trans : Extension small middle → Extension middle large → Extension small large
  | extension, .refl => extension
  | extension, .step rest => .step (trans extension rest)

end Extension

def DefRef.lift : Extension small large →
    DefRef small captures input output → DefRef large captures input output
  | .refl, ref => ref
  | .step extension, ref => .there (ref.lift extension)

/-! ## Runtime values -/

/- Function values are code references paired with a packed captured environment. `Packed` is
the strictly-positive fixed point; `Closure` is its function fiber. Keeping the recursive domain
behind closures lets ordinary object data retain its direct Lean representation. -/
mutual
  inductive Packed (ctx : DefCtx) : Tp → Type
    | nat : Nat → Packed ctx .nat
    | int : Int → Packed ctx .int
    | bool : Bool → Packed ctx .bool
    | unit : Packed ctx .unit
    | prod : Packed ctx left → Packed ctx right → Packed ctx (.prod left right)
    | closure : Closure ctx input output → Packed ctx (.fn input output)

  inductive Closure (ctx : DefCtx) : Tp → Tp → Type
    | mk : DefRef ctx captures input output → Packed ctx captures →
        Closure ctx input output
end

namespace Tp

/-- Direct runtime denotation. Only function types use the inductive closure domain. -/
@[reducible] def denote (ctx : DefCtx) : Tp → Type
  | .nat => Nat
  | .int => Int
  | .bool => Bool
  | .unit => Unit
  | .prod left right => left.denote ctx × right.denote ctx
  | .fn input output => Closure ctx input output

end Tp

namespace Packed

def pack : {tp : Tp} → tp.denote ctx → Packed ctx tp
  | .nat, value => .nat value
  | .int, value => .int value
  | .bool, value => .bool value
  | .unit, _ => .unit
  | .prod _ _, value => .prod (pack value.1) (pack value.2)
  | .fn _ _, value => .closure value

def unpack : {tp : Tp} → Packed ctx tp → tp.denote ctx
  | .nat, .nat value => value
  | .int, .int value => value
  | .bool, .bool value => value
  | .unit, .unit => ()
  | .prod _ _, .prod left right => (left.unpack, right.unpack)
  | .fn _ _, .closure value => value

@[simp] theorem unpack_pack : {tp : Tp} → (value : tp.denote ctx) →
    unpack (pack value) = value
  | .nat, _ => rfl
  | .int, _ => rfl
  | .bool, _ => rfl
  | .unit, _ => rfl
  | .prod _ _, value => by
      simp only [pack, unpack, unpack_pack]
  | .fn _ _, _ => rfl

end Packed

/-! ## Reified primitive operations -/

inductive Un : Tp → Tp → Type
  | not : Un .bool .bool
  | fst : Un (.prod left right) left
  | snd : Un (.prod left right) right

def Un.denote : Un input output → input.denote ctx → output.denote ctx
  | .not, value => !value
  | .fst, value => value.1
  | .snd, value => value.2

inductive Bin : Tp → Tp → Tp → Type
  | add : Bin .nat .nat .nat
  | sub : Bin .nat .nat .nat
  | mul : Bin .nat .nat .nat
  | intAdd : Bin .int .int .int
  | intSub : Bin .int .int .int
  | intMul : Bin .int .int .int
  | eq : Bin .nat .nat .bool
  | intEq : Bin .int .int .bool
  | lt : Bin .nat .nat .bool
  | le : Bin .nat .nat .bool
  | and : Bin .bool .bool .bool
  | or : Bin .bool .bool .bool
  | pair : Bin left right (.prod left right)

def Bin.denote : Bin left right output →
    left.denote ctx → right.denote ctx → output.denote ctx
  | .add, left, right => left + right
  | .sub, left, right => left - right
  | .mul, left, right => left * right
  | .intAdd, left, right => left + right
  | .intSub, left, right => left - right
  | .intMul, left, right => left * right
  | .eq, left, right => left == right
  | .intEq, left, right => left == right
  | .lt, left, right => decide (left < right)
  | .le, left, right => decide (left ≤ right)
  | .and, left, right => left && right
  | .or, left, right => left || right
  | .pair, left, right => (left, right)

/-! ## Effect and call signatures -/

structure Signature : Type 1 where
  op : Type
  input : op → Tp
  output : op → Tp
  branch : op → Type
  branchInput : (e : op) → branch e → Tp
  branchOutput : (e : op) → branch e → Tp

@[reducible] def Signature.spec (signature : Signature) (ctx : DefCtx) : ITree.HSig where
  op := signature.op
  input := fun e => (signature.input e).denote ctx
  output := fun e => (signature.output e).denote ctx
  branch := signature.branch
  branchInput := fun e b => (signature.branchInput e b).denote ctx
  branchOutput := fun e b => (signature.branchOutput e b).denote ctx

abbrev Signature.Compat (S : ITree.HSig.{u, v}) (H : Signature) (ctx : DefCtx) :=
  ITree.HSig.Compat S (H.spec ctx)

inductive CallOp (ctx : DefCtx) where
  | call {input output : Tp} : Closure ctx input output → CallOp ctx

@[reducible] def Call (ctx : DefCtx) : ITree.HSig where
  op := CallOp ctx
  input
    | .call (input := input) _ => input.denote ctx
  output
    | .call (output := output) _ => output.denote ctx
  branch := fun _ => PEmpty
  branchInput := fun _ branch => nomatch branch
  branchOutput := fun _ branch => nomatch branch

abbrev OpenM (H : Signature) (ctx : DefCtx) :=
  ITree.CompE (ITree.Sum (H.spec ctx) (Call ctx))

/-- Emit one dynamically typed closure application into the global call effect. -/
def invoke {H : Signature} (fn : Closure ctx input output) (value : input.denote ctx) :
    OpenM H ctx (output.denote ctx) :=
  ITree.CompE.op (.inr (.call fn)) value
    (fun branch => nomatch branch.1) ITree.CompE.ret

@[simp] theorem bind_invoke {H : Signature}
    (fn : Closure ctx input output) (value : input.denote ctx)
    (k : output.denote ctx → OpenM H ctx α) :
    ITree.CompE.bind (invoke fn value) k =
      ITree.CompE.op (H := ITree.Sum (H.spec ctx) (Call ctx))
        (Sum.inr (.call fn)) value
        (fun branch => nomatch branch.1) k := by
  apply ITree.CompE.eq_of_dest_eq
  change ITree.CompE.destAt
      (ITree.CompE.bind
        (ITree.CompE.opAt (H := ITree.Sum (H.spec ctx) (Call ctx))
          (Sum.inr (.call fn)) value
          (fun branch => ITree.CompE.asBlock (nomatch branch.1)) ITree.CompE.ret)
        k) = _
  rw [ITree.CompE.bind_opAt]
  rw [ITree.CompE.dest_opAt]
  change _ = ITree.CompE.dest
    (ITree.CompE.op (H := ITree.Sum (H.spec ctx) (Call ctx))
      (Sum.inr (.call fn)) value
      (fun branch => nomatch branch.1) k)
  rw [ITree.CompE.dest_op]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar with
  | block branch => nomatch branch.1
  | cont output =>
      change ITree.CompE.bind (ITree.CompE.ret output) k = k output
      rw [ITree.CompE.bind_ret]

/-! ## Expressions -/

/-- Expressions use PHOAS only for ordinary values. Static code references are intrinsically
scoped de Bruijn references; function values are constructed explicitly as closures and applied
through the single global call effect. -/
inductive Expr (H : Signature) (scope : DefCtx) (V : Tp → Type) : Tp → Type 2 where
  | source {α} : SourceRange → Expr H scope V α → Expr H scope V α
  | ret {α} : V α → Expr H scope V α
  | natLit {α} : Nat → (V .nat → Expr H scope V α) → Expr H scope V α
  | intLit {α} : Int → (V .int → Expr H scope V α) → Expr H scope V α
  | boolLit {α} : Bool → (V .bool → Expr H scope V α) → Expr H scope V α
  | unitLit {α} : (V .unit → Expr H scope V α) → Expr H scope V α
  | un {α input output} : Un input output → V input →
      (V output → Expr H scope V α) → Expr H scope V α
  | bin {α left right output} : Bin left right output → V left → V right →
      (V output → Expr H scope V α) → Expr H scope V α
  | ite {α β} : V .bool → Expr H scope V β → Expr H scope V β →
      (V β → Expr H scope V α) → Expr H scope V α
  | closure {α captures input output} :
      DefRef scope captures input output → V captures →
      (V (.fn input output) → Expr H scope V α) → Expr H scope V α
  | app {α input output} : V (.fn input output) → V input →
      (V output → Expr H scope V α) → Expr H scope V α
  | op {α} (e : H.op) : V (H.input e) →
      ((b : H.branch e) → V (H.branchInput e b) →
        Expr H scope V (H.branchOutput e b)) →
      (V (H.output e) → Expr H scope V α) → Expr H scope V α

def Expr.denote {H : Signature} (extension : Extension scope full) :
    {α : Tp} → Expr H scope (Tp.denote full) α → OpenM H full (α.denote full)
  | _, .source _ body => body.denote extension
  | _, .ret value => ITree.CompE.ret value
  | _, .natLit value k => (k value).denote extension
  | _, .intLit value k => (k value).denote extension
  | _, .boolLit value k => (k value).denote extension
  | _, .unitLit k => (k ()).denote extension
  | _, .un operation input k => (k (operation.denote input)).denote extension
  | _, .bin operation left right k =>
      (k (operation.denote left right)).denote extension
  | _, .ite condition yes no k =>
      (cond condition (yes.denote extension) (no.denote extension)) >>= fun value =>
        (k value).denote extension
  | _, .closure ref captured k =>
      (k (.mk (ref.lift extension) (.pack captured))).denote extension
  | _, .app fn input k =>
      invoke fn input >>= fun output =>
          (k output).denote extension
  | _, .op operation input blocks k =>
      ITree.CompE.op (.inl operation) input
        (fun branch => (blocks branch.1 branch.2).denote extension)
        ITree.CompE.ret >>= fun output =>
          (k output).denote extension

def Expr.stripSource {H : Signature} {V : Tp → Type} :
    {α : Tp} → Expr H scope V α → Expr H scope V α
  | _, .source _ body => body.stripSource
  | _, body => body

def Expr.sourceRange? {H : Signature} {V : Tp → Type}
    {α : Tp} : Expr H scope V α → Option SourceRange
  | .source range _ => some range
  | _ => none

def Expr.leadingSourceRanges {H : Signature} {V : Tp → Type} :
    {α : Tp} → Expr H scope V α → List SourceRange
  | _, .source range body => range :: body.leadingSourceRanges
  | _, _ => []

/-! ## Definition tables and programs -/

inductive MainArgs (V : Tp → Type) : List Tp → Type 1 where
  | nil : MainArgs V []
  | cons : V α → MainArgs V αs → MainArgs V (α :: αs)

namespace MainArgs

def map {V W : Tp → Type} (f : ∀ α, V α → W α) :
    {αs : List Tp} → MainArgs V αs → MainArgs W αs
  | [], .nil => .nil
  | _ :: _, .cons value rest => .cons (f _ value) (rest.map f)

end MainArgs

/-- A definition telescope. Every body is syntactically scoped over exactly itself and the older
definitions, while its PHOAS values will later be instantiated in the completed context. -/
inductive Defs (H : Signature) (V : Tp → Type) : DefCtx → Type 2 where
  | nil : Defs H V []
  | add (prior : Defs H V ctx)
      (body : V decl.captures → V decl.input →
        Expr H (decl :: ctx) V decl.output) :
      Defs H V (decl :: ctx)

abbrev Bodies (H : Signature) (full : DefCtx) :=
  {captures input output : Tp} → DefRef full captures input output →
    captures.denote full → input.denote full → OpenM H full (output.denote full)

def Defs.denote {H : Signature} {full : DefCtx} :
    {scope : DefCtx} → Defs H (Tp.denote full) scope → Extension scope full →
      {captures input output : Tp} → DefRef scope captures input output →
        captures.denote full → input.denote full → OpenM H full (output.denote full)
  | _, .add _ body, extension, _, _, _, .here, captured, input =>
      (body captured input).denote extension
  | _, .add prior _, extension, _, _, _, .there ref, captured, input =>
      prior.denote
        (Extension.trans (Extension.step Extension.refl) extension)
        ref captured input

def Defs.callHandler {H : Signature} {full : DefCtx}
    (defs : Defs H (Tp.denote full) full) :
    ITree.CompE.Handler (H.spec full) (Call full)
  | _, .call (.mk ref captured), input, _ =>
      defs.denote .refl ref captured.unpack input

structure Program (H : Signature) (ctx : DefCtx) (V : Tp → Type)
    (args : List Tp) (output : Tp) : Type 2 where
  defs : Defs H V ctx
  main : MainArgs V args → Expr H ctx V output

/-- A closed definition telescope together with an argument-taking main expression. -/
structure Code (H : Signature) (args : List Tp) (output : Tp) : Type 2 where
  ctx : DefCtx
  program : ∀ V, Program H ctx V args output

abbrev Closed (H : Signature) (output : Tp) := Code H [] output

def Code.denote {H : Signature} {args : List Tp} {output : Tp}
    (code : Code H args output) :
    MainArgs (Tp.denote code.ctx) args →
      ITree.CompE (H.spec code.ctx) (output.denote code.ctx) :=
  let program := code.program (Tp.denote code.ctx)
  fun inputs =>
    ITree.CompE.interpHandler program.defs.callHandler
      ((program.main inputs).denote .refl)

def Closed.denote {H : Signature} {output : Tp} (code : Closed H output) :
    ITree.CompE (H.spec code.ctx) (output.denote code.ctx) :=
  Code.denote code .nil

end Ast
end Freigen
