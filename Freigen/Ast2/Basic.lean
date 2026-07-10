import Freigen.ITree2.Basic

namespace Freigen

universe u v

/-- The free monad over host effect and custom-control-flow signatures, in **leaf-grafting
    form**: every node carries its continuation, and `bind` is a *function* (structural
    grafting at `pure` leaves), not a constructor — which is what makes the `Monad` instance
    lawful on the nose (`pure_bind` is `rfl`; the other laws are inductions). -/
inductive Freek (𝓔 : ITree2.EffSig.{u}) (𝓑 : ITree2.BindSig.{u}) :
    Type u → Type (u+1) where
| pure {α : Type u} : α → Freek 𝓔 𝓑 α
| eff {α : Type u} (e : 𝓔.ε) : 𝓔.input e → (𝓔.output e → Freek 𝓔 𝓑 α) →
    Freek 𝓔 𝓑 α
| bindEff {α : Type u} (e : 𝓑.ε) : 𝓑.input e →
    ((b : 𝓑.branch e) → Freek 𝓔 𝓑 (𝓑.branchOutput e b)) →
    (𝓑.output e → Freek 𝓔 𝓑 α) → Freek 𝓔 𝓑 α

/-- Monadic bind: graft `f` at the `pure` leaves — extending each node's *continuation*, never
    a `bindEff` block. -/
def Freek.bind {𝓔 𝓑} {α β} : Freek 𝓔 𝓑 α → (α → Freek 𝓔 𝓑 β) → Freek 𝓔 𝓑 β
  | .pure a, f => f a
  | .eff e i k, f => .eff e i fun o => (k o).bind f
  | .bindEff e i bs k, f => .bindEff e i bs fun o => (k o).bind f

instance {𝓔 𝓑} : Monad (Freek 𝓔 𝓑) where
  pure := Freek.pure
  bind := Freek.bind

/-- Right identity, by induction (`pure_bind`, the left one, is `rfl`). -/
theorem Freek.bind_pure {𝓔 𝓑 α} (m : Freek 𝓔 𝓑 α) : m.bind .pure = m := by
  induction m with
  | pure a => rfl
  | eff e i k ih => exact congrArg (Freek.eff e i) (funext ih)
  | bindEff e i bs k _ ihk => exact congrArg (Freek.bindEff e i bs) (funext ihk)

/-- Associativity, by induction. -/
theorem Freek.bind_assoc {𝓔 𝓑} {α β γ} (m : Freek 𝓔 𝓑 α)
    (f : α → Freek 𝓔 𝓑 β) (g : β → Freek 𝓔 𝓑 γ) :
    (m.bind f).bind g = m.bind fun a => (f a).bind g := by
  induction m with
  | pure a => rfl
  | eff e i k ih => exact congrArg (Freek.eff e i) (funext fun o => ih o f)
  | bindEff e i bs k _ ihk => exact congrArg (Freek.bindEff e i bs) (funext fun o => ihk o f)

/-- **`Freek` is a lawful monad** — the point of the leaf-grafting representation.  `id_map` is
    `bind_pure` (map is the monad-default `bind ∘ pure`), `pure_bind` is `rfl` (grafting at the
    single `pure` leaf), and `bind_assoc` is the induction above. -/
instance {𝓔 𝓑} : LawfulMonad (Freek 𝓔 𝓑) :=
  LawfulMonad.mk' (Freek 𝓔 𝓑)
    (fun m => Freek.bind_pure m)
    (fun _ _ => rfl)
    (fun m f g => Freek.bind_assoc m f g)

def Freek.eval {M : Type u → Type v} [Monad M] {𝓔 𝓑 α}
    (evalEff : (e : 𝓔.ε) → 𝓔.input e → M (𝓔.output e))
    (evalBind : (e : 𝓑.ε) → 𝓑.input e →
      ((b: 𝓑.branch e) → M (𝓑.branchOutput e b)) → M (𝓑.output e))
    : Freek 𝓔 𝓑 α → M α
| .pure a => Pure.pure a
| .eff e i k => do
    let o ← evalEff e i
    Freek.eval evalEff evalBind (k o)
| .bindEff e i bs k => do
    let o ← evalBind e i (fun b => Freek.eval evalEff evalBind (bs b))
    Freek.eval evalEff evalBind (k o)

/-- `eval` is a **monad morphism**: it maps `Freek.bind` to the target's bind.  With `bind`
    computed by grafting this is a lemma rather than a definitional arm — the price of
    lawfulness — proved by induction, using the target's own laws (hence `[LawfulMonad M]`). -/
theorem Freek.eval_bind {M : Type u → Type v} [Monad M] [LawfulMonad M] {𝓔 𝓑} {α β}
    (evalEff : (e : 𝓔.ε) → 𝓔.input e → M (𝓔.output e))
    (evalBind : (e : 𝓑.ε) → 𝓑.input e →
      ((b: 𝓑.branch e) → M (𝓑.branchOutput e b)) → M (𝓑.output e))
    (m : Freek 𝓔 𝓑 α) (f : α → Freek 𝓔 𝓑 β) :
    Freek.eval evalEff evalBind (m.bind f)
      = Freek.eval evalEff evalBind m >>= fun a => Freek.eval evalEff evalBind (f a) := by
  -- `induction m` generalizes `f`; each node case unfolds `bind`/`eval` on both sides, pushes
  -- the continuation past target-monad associativity, and closes with the pointwise IH.
  induction m with
  | pure a => exact (pure_bind (m := M) a fun a => Freek.eval evalEff evalBind (f a)).symm
  | eff e i k ih =>
      simp only [Freek.bind, Freek.eval]
      rw [LawfulMonad.bind_assoc]
      exact congrArg _ (funext fun o => ih o f)
  | bindEff e i bs k _ ihk =>
      simp only [Freek.bind, Freek.eval]
      rw [LawfulMonad.bind_assoc]
      exact congrArg _ (funext fun o => ihk o f)

def Freek.toITree {𝓔 : ITree2.EffSig.{u}} {𝓑 : ITree2.BindSig.{u}} {α : Type u} :
    Freek 𝓔 𝓑 α → ITree2.CompE 𝓔 𝓑 α :=
  Freek.eval (M := ITree2.CompE 𝓔 𝓑)
    (fun e i => ITree2.CompE.vis e i ITree2.CompE.ret)
    (fun e i blocks => ITree2.CompE.bindEff e i blocks ITree2.CompE.ret)

theorem Freek.toITree_bind {𝓔 : ITree2.EffSig.{u}} {𝓑 : ITree2.BindSig.{u}}
    {α β : Type u}
    (m : Freek 𝓔 𝓑 α) (f : α → Freek 𝓔 𝓑 β) :
    Freek.toITree (m.bind f) =
      ITree2.CompE.bind (Freek.toITree m) (fun a => Freek.toITree (f a)) := by
  unfold Freek.toITree
  exact Freek.eval_bind
    (fun e i => ITree2.CompE.vis e i ITree2.CompE.ret)
    (fun e i blocks => ITree2.CompE.bindEff e i blocks ITree2.CompE.ret)
    m f

/-!
## The object-type universe and the AST

A from-scratch restart of the AST.  What changes relative to `Freigen.Ast`:

* **Custom control flow stays uninterpreted.**  The old soundness story picked *one*
  interpretation of a scoped construct (flatten it to a `bind`) and baked it into the
  denotation.  Here the AST has a `bindEff` node mirroring `Freek.bindEff` one-to-one, and the
  denotation emits that node directly into `ITree2`.
* **Effects and scoped binds are hoisted into the ITree2 signature.**  `Expr.denote` emits
  `vis` nodes for `eff` and `bindEff` nodes for scoped control flow.
* **No `prog → defs → exprs` stratification.**  Function definitions — recursive or not — are
  a single inline `letrec` node, so the reflector can emit a definition in one pass, right
  where it is first encountered.
* **A self-call is a call event, not a first-class value.**  Inside a `letrec` body the
  definition reaches itself through the dedicated `selfCall` node, and the knot is tied by
  `mrec` — ITree-canon.  A first-class self is impossible: it would have to be a Kleisli arrow
  into the base domain *before* the knot exists.  The `Option (Tp × Tp)` **recursion-slot
  index** on `Expr` tracks the enclosing `letrec` statically: `selfCall` is only available at
  a matching `some (a, b)`; `lam` bodies and `bindEff` blocks are `none`-indexed (a closure or
  a block may not self-call — the old design's `lam`-fails-inside-`rec_` restriction, now a
  *typing* fact instead of a denotation-time failure); an inner `letrec` shadows the slot.
  *After* the knot, the continuation receives the definition as an ordinary first-class
  `V (.fn a b)` value.
* **Deliberately tiny universe**: `nat`/`bool`/products, first-order function binders, and a
  handful of primitives.

Next: the one-pass reflector and its soundness against `Freek.toITree`.
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

abbrev circuitEff : ITree2.EffSig.{0} where
  ε := Unit
  input := fun _ => Bool
  output := fun _ => Unit

abbrev circuitBlock : ITree2.BindSig.{0} where
  ε := Tp0
  input := fun _ => Unit
  output := Tp0.denote
  branch := fun _ => Unit
  branchOutput := fun e _ => Tp0.denote e

def Circuit (α : Type) : Type _ := Freek circuitEff circuitBlock α

instance : Monad Circuit := inferInstanceAs (Monad (Freek _ _))

def Circuit.hint (β : Tp0) (f : Circuit β.denote) : Circuit β.denote :=
  Freek.bindEff (𝓔 := circuitEff) (𝓑 := circuitBlock) β () (fun _ => f) Freek.pure

def Circuit.eval_with_hints : Circuit α → Option α := Freek.eval
  (fun _ i => if i then some () else none)
  (fun _ _ k => k ())

def ConstraintM (α : Type _) := (α → Prop) → Prop

instance : Monad ConstraintM where
  pure a := fun k => k a
  bind m f := fun k => m (fun a => f a k)

def Circuit.eval_constraints : Circuit α → ConstraintM α := Freek.eval
  (fun _ i => fun k => i ∧ k ())
  (fun _ _ _ => fun k => ∃ x, k x)

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

/-! ### Coded effect signatures

The syntactic mirrors of the source `ITree2.EffSig`/`ITree2.BindSig`: the same shapes, but
with all payload types given by first-order object-type *codes* rather than host `Type`s — the
AST is data, so its vocabulary must be too. -/

/-- A first-order effect vocabulary coded in `Tp0`: event `e` takes a `𝓘 e` and returns an
    `𝓞 e`. -/
structure EffSig : Type 1 where
  ε : Type
  𝓘 : ε → Tp0
  𝓞 : ε → Tp0

/-- A custom-control-flow vocabulary coded in `Tp0`: operation `e` takes a `𝓘 e`, carries one
    sub-computation (block) per branch label `b : 𝓑 e` producing a `𝓑τ e b`, and returns an
    `𝓞 e`.  What an operation *does* with its blocks is not the AST's business; the node is
    emitted into `ITree2` and remains uninterpreted there. -/
structure BindSig : Type 1 where
  ε : Type
  𝓘 : ε → Tp0
  𝓞 : ε → Tp0
  𝓑 : ε → Type
  𝓑τ : (e : ε) → 𝓑 e → Tp0

/-- Instantiate a coded first-order effect signature as an `ITree2` effect signature. -/
@[reducible] def EffSig.spec (𝓔 : EffSig) : ITree2.EffSig where
  ε := 𝓔.ε
  input := fun e => (𝓔.𝓘 e).denote
  output := fun e => (𝓔.𝓞 e).denote

/-- Instantiate a coded custom-control-flow signature as an `ITree2` scoped-bind signature. -/
@[reducible] def BindSig.spec (𝓑 : BindSig) : ITree2.BindSig where
  ε := 𝓑.ε
  input := fun e => (𝓑.𝓘 e).denote
  output := fun e => (𝓑.𝓞 e).denote
  branch := 𝓑.𝓑
  branchOutput := fun e b => (𝓑.𝓑τ e b).denote

/-- Perform a coded first-order effect as an uninterpreted `ITree2` event. -/
def EffSig.trigger {𝓔 : EffSig} {𝓑 : BindSig} (e : 𝓔.ε) (i : (𝓔.𝓘 e).denote) :
    ITree2.CompE 𝓔.spec 𝓑.spec ((𝓔.𝓞 e).denote) :=
  ITree2.CompE.vis e i ITree2.CompE.ret

/-! ### The recursion-slot-indexed domain -/

/-- The recursion-slot-indexed domain: at `none`, the base domain; at `some (a, b)`, the
    call-extended domain of the enclosing `letrec` — base events plus a self-call event
    carrying an `a`-value and branching on the `b`-result. -/
@[reducible] def DomR (𝓔 : EffSig) (𝓑 : BindSig) :
    Option (Tp0 × Tp0) → Type → Type
  | none => ITree2.CompE 𝓔.spec 𝓑.spec
  | some (a, b) =>
      ITree2.CompE (ITree2.SumEff 𝓔.spec (ITree2.CallEff a.denote b.denote)) 𝓑.spec

/-- `ret` at either recursion slot. -/
def DomR.ret {𝓔 : EffSig} {𝓑 : BindSig} :
    {r : Option (Tp0 × Tp0)} → {γ : Type} → γ → DomR 𝓔 𝓑 r γ
  | none,        _, x => ITree2.CompE.ret x
  | some (_, _), _, x => ITree2.CompE.ret x

/-- `bind` at either recursion slot. -/
def DomR.bind {𝓔 : EffSig} {𝓑 : BindSig} :
    {r : Option (Tp0 × Tp0)} → {γ δ : Type} →
      DomR 𝓔 𝓑 r γ → (γ → DomR 𝓔 𝓑 r δ) → DomR 𝓔 𝓑 r δ
  | none,        _, _, m, k => ITree2.CompE.bind m k
  | some (_, _), _, _, m, k => ITree2.CompE.bind m k

/-- Embed a base-domain computation at either recursion slot (the identity at `none`; event
    relabelling along `inl` — no `tau`s — at `some`). -/
def DomR.lift {𝓔 : EffSig} {𝓑 : BindSig} :
    {r : Option (Tp0 × Tp0)} → {γ : Type} →
      ITree2.CompE 𝓔.spec 𝓑.spec γ → DomR 𝓔 𝓑 r γ
  | none,        _, t => t
  | some (a, b), _, t => ITree2.CompE.sumL
      (𝓕 := ITree2.CallEff a.denote b.denote) t

/-! ### The AST -/

/-- The dumb, typed AST: PHOAS over a value family `V`, continuation-passing (every node binds
    its result and continues — mirroring one step of a monadic source program), indexed by the
    **recursion slot** (the enclosing `letrec`'s first-order argument/result types, `none`
    outside one) and the first-order result object type. -/
inductive Expr (𝓔 : EffSig) (𝓑 : BindSig) (V : Tp0 → Type) :
    Option (Tp0 × Tp0) → Tp0 → Type 2
  | ret     {r α} : V α → Expr 𝓔 𝓑 V r α
  | natLit  {r α} : Nat → (V .nat → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α
  | boolLit {r α} : Bool → (V .bool → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α
  | unitLit {r α} : (V .unit → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α
  | un      {r α a b} : Un a b → V a → (V b → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α
  | bin     {r α a b c} : Bin a b c → V a → V b → (V c → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α
  /-- Branch on a boolean, **join through the continuation**: both arms produce a `β`, and the
      rest of the program is written once — reflecting `bind (cond c t e) k` never duplicates
      `k`.  The arms stay at the ambient slot, so a recursive definition may `selfCall` in
      either. -/
  | ite     {r α β} : V .bool → Expr 𝓔 𝓑 V r β → Expr 𝓔 𝓑 V r β →
      (V β → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α
  /-- A **function binder**: suspend `body` as a host Kleisli arrow.  The body is `none`-indexed
      — a closure may not `selfCall` an enclosing `letrec`. -/
  | lam     {r α a b} : (V a → Expr 𝓔 𝓑 V none b) →
      ((V a → ITree2.CompE 𝓔.spec 𝓑.spec (V b)) → Expr 𝓔 𝓑 V r α) →
      Expr 𝓔 𝓑 V r α
  /-- **Apply** a function value — effectful, like any operation. -/
  | app     {r α a b} : (V a → ITree2.CompE 𝓔.spec 𝓑.spec (V b)) → V a →
      (V b → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α
  /-- A (possibly) **recursive function definition**, inline: the body runs at slot
      `some (a, b)` — it reaches itself through `selfCall`, not through a binder — and the rest
      of the program receives the *tied* definition as an ordinary first-class `V (.fn a b)`
      function.  This single node replaces the old `Prog` telescope (`main`/`def_`/`rec_`): a
      non-recursive definition simply never self-calls, and the reflector emits definitions in
      one pass, where they are first encountered. -/
  | letrec  {r α a b} : (V a → Expr 𝓔 𝓑 V (some (a, b)) b) →
      ((V a → ITree2.CompE 𝓔.spec 𝓑.spec (V b)) → Expr 𝓔 𝓑 V r α) →
      Expr 𝓔 𝓑 V r α
  /-- **Call the enclosing recursive definition** — only available inside a `letrec` body with
      the matching slot. -/
  | selfCall {α a b} : V a → (V b → Expr 𝓔 𝓑 V (some (a, b)) α) →
      Expr 𝓔 𝓑 V (some (a, b)) α
  /-- Perform an effect. -/
  | eff     {r α} (e : 𝓔.ε) : V (𝓔.𝓘 e) →
      (V (𝓔.𝓞 e) → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α
  /-- Perform a custom-control-flow operation: the blocks are carried as **uninterpreted
      sub-computations** — the syntactic mirror of `Freek.bindEff`, reflected one-to-one, never
      flattened.  Blocks are `none`-indexed: a block may not `selfCall` the enclosing
      `letrec`. -/
  | bindEff {r α} (e : 𝓑.ε) : V (𝓑.𝓘 e) → ((b : 𝓑.𝓑 e) → Expr 𝓔 𝓑 V none (𝓑.𝓑τ e b)) →
      (V (𝓑.𝓞 e) → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α

/-- The AST's meaning.  First-order `eff` nodes are emitted as `vis` nodes and scoped
    operations are emitted as `bindEff` nodes in `ITree2`; no external bind interpreter is
    involved. -/
def Expr.denote {𝓔 : EffSig} {𝓑 : BindSig} :
    {r : Option (Tp0 × Tp0)} → {α : Tp0} →
      Expr 𝓔 𝓑 Tp0.denote r α → DomR 𝓔 𝓑 r α.denote
  | _, _, .ret v         => DomR.ret v
  | _, _, .natLit n k    => Expr.denote (k n)
  | _, _, .boolLit b k   => Expr.denote (k b)
  | _, _, .unitLit k     => Expr.denote (k ())
  | _, _, .un o a k      => Expr.denote (k (o.denote a))
  | _, _, .bin o a b k   => Expr.denote (k (o.denote a b))
  | _, _, .ite c t e k   =>
      DomR.bind (cond c (Expr.denote t) (Expr.denote e)) fun v =>
        Expr.denote (k v)
  | _, _, .lam body k    => Expr.denote (k fun x => Expr.denote (body x))
  | _, _, .app f x k     => DomR.bind (DomR.lift (f x)) fun v => Expr.denote (k v)
  | _, _, .letrec body k =>
      Expr.denote (k (ITree2.CompE.mrec fun s => Expr.denote (body s)))
  | _, _, .selfCall x k  =>
      ITree2.CompE.vis (Sum.inr ITree2.CallOp.call) x fun v => Expr.denote (k v)
  | _, _, .eff e i k     => DomR.bind (DomR.lift (EffSig.trigger (𝓑 := 𝓑) e i)) fun o =>
      Expr.denote (k o)
  | _, _, .bindEff e i blocks k =>
      DomR.bind
        (DomR.lift (ITree2.CompE.bindEff e i (fun b => Expr.denote (blocks b))
          ITree2.CompE.ret)) fun o =>
        Expr.denote (k o)

/-- A closed program, parametric in the value representation. -/
def Closed (𝓔 : EffSig) (𝓑 : BindSig) (α : Tp0) : Type 2 :=
  ∀ V, Expr 𝓔 𝓑 V none α

end Ast2

end Freigen
