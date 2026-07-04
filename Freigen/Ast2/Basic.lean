import Freigen.ITree.Basic
import Freigen.Free
import Freigen.Ast.Tp

namespace Freigen

structure EffSpec : Type _ where
  ε : Type _
  𝓘 : ε → Type _
  𝓞 : ε → Type _

structure BindSpec : Type _ where
  ε : Type u
  𝓘 : ε → Type v
  𝓞 : ε → Type w
  𝓑 : ε → Type x
  𝓑τ : (e: ε) → 𝓑 e → Type y

/-- The free monad over a host effect spec and a custom-control-flow spec, in **leaf-grafting
    form**: every node carries its continuation, and `bind` is a *function* (structural
    grafting at `pure` leaves), not a constructor — which is what makes the `Monad` instance
    lawful on the nose (`pure_bind` is `rfl`; the other laws are inductions). -/
inductive Freek (𝓔 : EffSpec) (𝓑 : BindSpec) : Type _ → Type _ where
| pure {α} : α → Freek 𝓔 𝓑 α
| eff {α} (e : 𝓔.ε) : 𝓔.𝓘 e → (𝓔.𝓞 e → Freek 𝓔 𝓑 α) → Freek 𝓔 𝓑 α
| bindEff {α} (e : 𝓑.ε) : 𝓑.𝓘 e → ((b : 𝓑.𝓑 e) → Freek 𝓔 𝓑 (𝓑.𝓑τ e b)) →
    (𝓑.𝓞 e → Freek 𝓔 𝓑 α) → Freek 𝓔 𝓑 α

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

def Freek.eval {M} [Monad M] {𝓔 𝓑 α}
    (evalEff : (e : 𝓔.ε) → 𝓔.𝓘 e → M (𝓔.𝓞 e))
    (evalBind : (e : 𝓑.ε) → 𝓑.𝓘 e → ((b: 𝓑.𝓑 e) → M (𝓑.𝓑τ e b)) → M (𝓑.𝓞 e))
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
theorem Freek.eval_bind {M} [Monad M] [LawfulMonad M] {𝓔 𝓑} {α β}
    (evalEff : (e : 𝓔.ε) → 𝓔.𝓘 e → M (𝓔.𝓞 e))
    (evalBind : (e : 𝓑.ε) → 𝓑.𝓘 e → ((b: 𝓑.𝓑 e) → M (𝓑.𝓑τ e b)) → M (𝓑.𝓞 e))
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

abbrev circuitEff : EffSpec where
  ε := Unit
  𝓘 := fun _ => Bool
  𝓞 := fun _ => Unit

abbrev circuitBlock : BindSpec where
  ε := Type
  𝓘 := fun _ => Unit
  𝓞 := id
  𝓑 := fun _ => Unit
  𝓑τ := fun e _ => e

def Circuit (α : Type _) : Type _ := Freek circuitEff circuitBlock α

instance : Monad Circuit := inferInstanceAs (Monad (Freek _ _))

def Circuit.hint {β : Type} (f : Circuit β) : Circuit β :=
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

open ITree in
def Freek.toITree {α} {𝓔: EffSpec} {𝓑: BindSpec}
    (evalBind :  (e : 𝓑.ε) → 𝓑.𝓘 e → ((b: 𝓑.𝓑 e) → CompE 𝓔.ε 𝓔.𝓞 (𝓑.𝓑τ e b)) → CompE 𝓔.ε 𝓔.𝓞 (𝓑.𝓞 e)):
  Freek 𝓔 𝓑 α → CompE 𝓔.ε 𝓔.𝓞 α := Freek.eval (fun e _ => ITree.vis e (fun o => ITree.ret o)) evalBind

/-!
## The object-type universe and the AST

A from-scratch restart of the AST.  What changes relative to `Freigen.Ast`:

* **Custom control flow stays uninterpreted.**  The old soundness story picked *one*
  interpretation of a scoped construct (flatten it to a `bind`) and baked it into the
  denotation.  Here the AST has a `bindEff` node mirroring `Freek.bindEff` one-to-one, and the
  denotation is parameterised by an interpreter for it (`BindInterp`), so every soundness
  statement quantifies over the interpretation of custom control flow.
* **The denotation fixes no event signature.**  `Expr.denote` targets `CompE ε br` for an
  *arbitrary* `(ε, br)`, given an interpreter for the effects (`EffInterp`) and one for custom
  control flow (`BindInterp`) — the same shape as `Freek.eval`'s `evalEff`/`evalBind`, at
  `M := CompE ε br`.  Because the domain is a parameter (never something the signatures must be
  defined "before"), signature payloads are full `Tp` — no first-order sub-universe — and
  `Tp.denote M` (with `.fn a b` a Kleisli arrow `a.denote M → M (b.denote M)`) instantiates at
  `M := CompE ε br` with no circularity.
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
* **Deliberately tiny universe**: `nat`/`bool`/products/functions and a handful of primitives.

Next: the one-pass reflector and its interpreter-parametric soundness against `Freek.eval`.
-/

namespace Ast2

open ITree

/-! ### Object types -/

/-- The universe of object-language types: `nat`/`bool`/`unit`, products, and functions. -/
inductive Tp : Type
  | nat  : Tp
  | bool : Tp
  | unit : Tp
  | prod : Tp → Tp → Tp
  | fn   : Tp → Tp → Tp

/-- Denote an object type over an arbitrary target monad `M`.  A function type denotes as a
    **Kleisli arrow into `M`** — a function value is a suspended, potentially effectful
    computation.  Quantifying the target keeps every downstream statement parametric in the
    interpreter.  Reducible so type-class search and unification see through it. -/
@[reducible] def Tp.denote (M : Type → Type) : Tp → Type
  | .nat      => Nat
  | .bool     => Bool
  | .unit     => Unit
  | .prod a b => a.denote M × b.denote M
  | .fn a b   => a.denote M → M (b.denote M)

/-! ### Reified primitive operations -/

/-- Unary primitives, indexed by (argument, result) object type. -/
inductive Un : Tp → Tp → Type
  | not : Un .bool .bool
  | fst {a b : Tp} : Un (.prod a b) a
  | snd {a b : Tp} : Un (.prod a b) b

/-- Denote a unary primitive to its Lean operation (`M`-independent on these types, but stated
    over `Tp.denote M` so it composes with the AST's denotation). -/
def Un.denote {M : Type → Type} {a b : Tp} : Un a b → a.denote M → b.denote M
  | .not, x => !x
  | .fst, p => p.1
  | .snd, p => p.2

/-- Binary primitives, indexed by (left, right, result) object type. -/
inductive Bin : Tp → Tp → Tp → Type
  | add : Bin .nat .nat .nat
  | sub : Bin .nat .nat .nat
  | mul : Bin .nat .nat .nat
  | eq  : Bin .nat .nat .bool
  | lt  : Bin .nat .nat .bool
  | le  : Bin .nat .nat .bool
  | and : Bin .bool .bool .bool
  | or  : Bin .bool .bool .bool
  | pair {a b : Tp} : Bin a b (.prod a b)

/-- Denote a binary primitive to its Lean operation. -/
def Bin.denote {M : Type → Type} {a b c : Tp} :
    Bin a b c → a.denote M → b.denote M → c.denote M
  | .add,  x, y => x + y
  | .sub,  x, y => x - y
  | .mul,  x, y => x * y
  | .eq,   x, y => x == y
  | .lt,   x, y => decide (x < y)
  | .le,   x, y => decide (x ≤ y)
  | .and,  x, y => x && y
  | .or,   x, y => x || y
  | .pair, x, y => (x, y)

/-! ### `Tp`-coded effect signatures

The syntactic mirrors of `EffSpec`/`BindSpec`: the same shapes, but with all payload types
given by `Tp` *codes* rather than host `Type`s — the AST is data, so its vocabulary must be
too.  `spec` instantiates a coded signature at a target monad, recovering the host-level spec
a source `Freek` program lives over. -/

/-- A first-order effect vocabulary coded in `Tp`: event `e` takes a `𝓘 e` and returns an
    `𝓞 e`. -/
structure EffSig : Type 1 where
  ε : Type
  𝓘 : ε → Tp
  𝓞 : ε → Tp

/-- A custom-control-flow vocabulary coded in `Tp`: operation `e` takes a `𝓘 e`, carries one
    sub-computation (block) per branch label `b : 𝓑 e` producing a `𝓑τ e b`, and returns an
    `𝓞 e`.  What an operation *does* with its blocks is never the AST's business — that is the
    interpreter's, which soundness quantifies over. -/
structure BindSig : Type 1 where
  ε : Type
  𝓘 : ε → Tp
  𝓞 : ε → Tp
  𝓑 : ε → Type
  𝓑τ : (e : ε) → 𝓑 e → Tp

/-- Instantiate a coded effect signature at a target monad.  (Reducible: downstream statements
    identify `(𝓔.spec M).𝓘 e` with `Tp.denote M (𝓔.𝓘 e)` definitionally.) -/
@[reducible] def EffSig.spec (𝓔 : EffSig) (M : Type → Type) : EffSpec where
  ε := 𝓔.ε
  𝓘 := fun e => (𝓔.𝓘 e).denote M
  𝓞 := fun e => (𝓔.𝓞 e).denote M

/-- Instantiate a coded custom-control-flow signature at a target monad. -/
@[reducible] def BindSig.spec (𝓑 : BindSig) (M : Type → Type) : BindSpec where
  ε := 𝓑.ε
  𝓘 := fun e => (𝓑.𝓘 e).denote M
  𝓞 := fun e => (𝓑.𝓞 e).denote M
  𝓑 := 𝓑.𝓑
  𝓑τ := fun e b => (𝓑.𝓑τ e b).denote M

/-! ### Interpreters and the recursion-slot-indexed domain -/

/-- An **effect interpreter** into the tree domain over `(ε, br)`: gives each effect its tree
    (typically a `vis` — but which event, and how the payload is packaged, is its choice).
    This is `Freek.eval`'s `evalEff` at `M := CompE ε br`, over coded types. -/
abbrev EffInterp (𝓔 : EffSig) (ε : Type) (br : ε → Type) : Type :=
  (e : 𝓔.ε) → Tp.denote (CompE ε br) (𝓔.𝓘 e) → CompE ε br (Tp.denote (CompE ε br) (𝓔.𝓞 e))

/-- A **`bindEff` interpreter** into the tree domain over `(ε, br)`: receives the operation,
    its (denoted) input, and one *denoted block* per branch label — full trees — and returns
    the operation's tree.  Run one block, run none, splice, iterate — entirely its business.
    This is `Freek.eval`'s `evalBind` at `M := CompE ε br`, over coded types. -/
abbrev BindInterp (𝓑 : BindSig) (ε : Type) (br : ε → Type) : Type :=
  (e : 𝓑.ε) → Tp.denote (CompE ε br) (𝓑.𝓘 e) →
    ((b : 𝓑.𝓑 e) → CompE ε br (Tp.denote (CompE ε br) (𝓑.𝓑τ e b))) →
    CompE ε br (Tp.denote (CompE ε br) (𝓑.𝓞 e))

/-- The recursion-slot-indexed domain: at `none`, the base domain; at `some (a, b)`, the
    call-extended domain of the enclosing `letrec` — base events plus a self-call event
    carrying an `a`-value and branching on the `b`-result. -/
@[reducible] def DomR (ε : Type) (br : ε → Type) : Option (Tp × Tp) → Type → Type
  | none => CompE ε br
  | some (a, b) =>
      CompE (ε ⊕ Tp.denote (CompE ε br) a) (callBr br (Tp.denote (CompE ε br) b))

/-- `ret` at either recursion slot. -/
def DomR.ret {ε : Type} {br : ε → Type} : {r : Option (Tp × Tp)} → {γ : Type} → γ → DomR ε br r γ
  | none,        _, x => ITree.ret x
  | some (_, _), _, x => ITree.ret x

/-- `bind` at either recursion slot. -/
def DomR.bind {ε : Type} {br : ε → Type} :
    {r : Option (Tp × Tp)} → {γ δ : Type} → DomR ε br r γ → (γ → DomR ε br r δ) → DomR ε br r δ
  | none,        _, _, m, k => ITree.bind m k
  | some (_, _), _, _, m, k => ITree.bind m k

/-- Embed a base-domain computation at either recursion slot (the identity at `none`; event
    relabelling along `inl` — no `tau`s — at `some`).  This is how an interpreter's tree, or an
    applied function value's computation, splices into a `letrec` body. -/
def DomR.lift {ε : Type} {br : ε → Type} :
    {r : Option (Tp × Tp)} → {γ : Type} → CompE ε br γ → DomR ε br r γ
  | none,        _, t => t
  | some (_, _), _, t => sumL t

/-! ### The AST -/

/-- The dumb, typed AST: PHOAS over a value family `V`, continuation-passing (every node binds
    its result and continues — mirroring one step of a monadic source program), indexed by the
    **recursion slot** (the enclosing `letrec`'s argument/result types, `none` outside one) and
    the result object type.  Literals are *syntactic* (`natLit`/`boolLit`), never semantic
    values — which is also what keeps the whole AST in `Type 0`. -/
inductive Expr (𝓔 : EffSig) (𝓑 : BindSig) (V : Tp → Type) : Option (Tp × Tp) → Tp → Type
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
  /-- A **function value**: suspend `body` as a first-class `.fn a b` atom.  The body is
      `none`-indexed — a closure may not `selfCall` an enclosing `letrec` (its denotation is a
      base-domain Kleisli arrow, which exists before any knot is tied). -/
  | lam     {r α a b} : (V a → Expr 𝓔 𝓑 V none b) → (V (.fn a b) → Expr 𝓔 𝓑 V r α) →
      Expr 𝓔 𝓑 V r α
  /-- **Apply** a function value — effectful, like any operation. -/
  | app     {r α a b} : V (.fn a b) → V a → (V b → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α
  /-- A (possibly) **recursive function definition**, inline: the body runs at slot
      `some (a, b)` — it reaches itself through `selfCall`, not through a binder — and the rest
      of the program receives the *tied* definition as an ordinary first-class `V (.fn a b)`
      value.  This single node replaces the old `Prog` telescope (`main`/`def_`/`rec_`): a
      non-recursive definition simply never self-calls, and the reflector emits definitions in
      one pass, where they are first encountered.  `a`, `b` are full `Tp` — recursion state may
      contain function values. -/
  | letrec  {r α a b} : (V a → Expr 𝓔 𝓑 V (some (a, b)) b) →
      (V (.fn a b) → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α
  /-- **Call the enclosing recursive definition** — only available inside a `letrec` body with
      the matching slot. -/
  | selfCall {α a b} : V a → (V b → Expr 𝓔 𝓑 V (some (a, b)) α) →
      Expr 𝓔 𝓑 V (some (a, b)) α
  /-- Perform an effect. -/
  | eff     {r α} (e : 𝓔.ε) : V (𝓔.𝓘 e) → (V (𝓔.𝓞 e) → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α
  /-- Perform a custom-control-flow operation: the blocks are carried as **uninterpreted
      sub-computations** — the syntactic mirror of `Freek.bindEff`, reflected one-to-one, never
      flattened.  Blocks are `none`-indexed: a block may not `selfCall` the enclosing
      `letrec`. -/
  | bindEff {r α} (e : 𝓑.ε) : V (𝓑.𝓘 e) → ((b : 𝓑.𝓑 e) → Expr 𝓔 𝓑 V none (𝓑.𝓑τ e b)) →
      (V (𝓑.𝓞 e) → Expr 𝓔 𝓑 V r α) → Expr 𝓔 𝓑 V r α

/-- **The AST's meaning**, given an effect interpreter and a `bindEff` interpreter — so an
    `Expr`'s denotation is the function `fun hE hB => Expr.denote hE hB e`, and soundness
    quantifies over the target signature `(ε, br)` and both interpreters.  At
    `V := Tp.denote (CompE ε br)`: a `lam` suspends its body as a base-domain Kleisli arrow, an
    `app` binds the arrow's computation (`lift`ed into a `letrec` body's extended domain), an
    `eff`/`bindEff` hands its input (and denoted blocks) to the interpreter, and a **`letrec`
    ties the knot with `mrec`** — a `selfCall` is the call event.  Only `mrec` introduces
    `tau`s: a `letrec`-free program denotes to a tree exactly as deep as its interpreters
    make it. -/
def Expr.denote {𝓔 : EffSig} {𝓑 : BindSig} {ε : Type} {br : ε → Type}
    (hE : EffInterp 𝓔 ε br) (hB : BindInterp 𝓑 ε br) :
    {r : Option (Tp × Tp)} → {α : Tp} →
      Expr 𝓔 𝓑 (Tp.denote (CompE ε br)) r α → DomR ε br r (Tp.denote (CompE ε br) α)
  | _, _, .ret v         => DomR.ret v
  | _, _, .natLit n k    => Expr.denote hE hB (k n)
  | _, _, .boolLit b k   => Expr.denote hE hB (k b)
  | _, _, .unitLit k     => Expr.denote hE hB (k ())
  | _, _, .un o a k      => Expr.denote hE hB (k (o.denote a))
  | _, _, .bin o a b k   => Expr.denote hE hB (k (o.denote a b))
  | _, _, .ite c t e k   =>
      DomR.bind (cond c (Expr.denote hE hB t) (Expr.denote hE hB e)) fun v =>
        Expr.denote hE hB (k v)
  | _, _, .lam body k    => Expr.denote hE hB (k fun x => Expr.denote hE hB (body x))
  | _, _, .app f x k     => DomR.bind (DomR.lift (f x)) fun v => Expr.denote hE hB (k v)
  | _, _, .letrec body k =>
      Expr.denote hE hB (k (mrec fun s => Expr.denote hE hB (body s)))
  | _, _, .selfCall x k  => vis (Sum.inr x) fun v => Expr.denote hE hB (k v)
  | _, _, .eff e i k     => DomR.bind (DomR.lift (hE e i)) fun o => Expr.denote hE hB (k o)
  | _, _, .bindEff e i blocks k =>
      DomR.bind (DomR.lift (hB e i fun b => Expr.denote hE hB (blocks b))) fun o =>
        Expr.denote hE hB (k o)

/-- A closed program, parametric in the value representation. -/
def Closed (𝓔 : EffSig) (𝓑 : BindSig) (α : Tp) : Type 1 :=
  ∀ V, Expr 𝓔 𝓑 V none α

end Ast2

/-! ### The signature bridge

A source program is written in a *host-level* monad — `Freek` over an `EffSpec`/`BindSpec`
whose payloads are plain `Type`s; the author never sees `Tp`.  The AST works over *coded*
signatures.  `Realizes` is the bridge: an (`M`-indexed) map `φ` of operation names under which
the host payload types are the denotations of the codes.  `φ` need not be surjective — a
`circuitBlock`-style spec has an operation per host `Type`, and the coded signature names only
the **representable fragment**, which is all a reflected program ever uses.  The `restrict`
transport is where that knowledge is *used*: a host interpreter restricts to a coded one, so a
reflected AST (denoted under the restricted interpreters) and its source (run through
`Freek.eval` under the host interpreters) meet in the same tree domain — soundness statements
therefore quantify over **host** interpreters. -/

open ITree in
/-- An interpreter for a host-level effect spec in the tree domain over `(ε, br)` —
    `Freek.eval`'s `evalEff` shape at `M := CompE ε br`. -/
@[reducible] def EffSpec.Interp (𝓔' : EffSpec) (ε : Type) (br : ε → Type) : Type _ :=
  (e : 𝓔'.ε) → 𝓔'.𝓘 e → CompE ε br (𝓔'.𝓞 e)

open ITree in
/-- An interpreter for a host-level custom-control-flow spec in the tree domain —
    `Freek.eval`'s `evalBind` shape at `M := CompE ε br`. -/
@[reducible] def BindSpec.Interp (𝓑' : BindSpec) (ε : Type) (br : ε → Type) : Type _ :=
  (e : 𝓑'.ε) → 𝓑'.𝓘 e → ((b : 𝓑'.𝓑 e) → CompE ε br (𝓑'.𝓑τ e b)) → CompE ε br (𝓑'.𝓞 e)

namespace Ast2

/-- The coded `𝓔` **realizes** (the representable fragment of) the host spec `𝓔'`: an
    `M`-indexed operation-name map under which the host payload types are pulled back along
    `Tp.denote` from the codes. -/
structure EffSig.Realizes (𝓔 : EffSig) (𝓔' : EffSpec) where
  φ : (M : Type → Type) → 𝓔.ε → 𝓔'.ε
  input_eq : ∀ M e, 𝓔'.𝓘 (φ M e) = Tp.denote M (𝓔.𝓘 e)
  output_eq : ∀ M e, 𝓔'.𝓞 (φ M e) = Tp.denote M (𝓔.𝓞 e)

/-- The coded `𝓑` realizes (the representable fragment of) the host spec `𝓑'`. -/
structure BindSig.Realizes (𝓑 : BindSig) (𝓑' : BindSpec) where
  φ : (M : Type → Type) → 𝓑.ε → 𝓑'.ε
  input_eq : ∀ M e, 𝓑'.𝓘 (φ M e) = Tp.denote M (𝓑.𝓘 e)
  output_eq : ∀ M e, 𝓑'.𝓞 (φ M e) = Tp.denote M (𝓑.𝓞 e)
  br_eq : ∀ M e, 𝓑'.𝓑 (φ M e) = 𝓑.𝓑 e
  brTp_eq : ∀ M e (b : 𝓑'.𝓑 (φ M e)),
    𝓑'.𝓑τ (φ M e) b = Tp.denote M (𝓑.𝓑τ e (cast (br_eq M e) b))

open ITree in
/-- Restrict a host interpreter to the coded signature across a realization — a reflected
    AST's denotation only ever needs the representable operations.  When the realization's
    equations are `rfl`, every `cast` reduces away. -/
def EffSig.Realizes.restrict {𝓔 : EffSig} {𝓔' : EffSpec} {ε : Type} {br : ε → Type}
    (h : 𝓔.Realizes 𝓔') (hE : 𝓔'.Interp ε br) : EffInterp 𝓔 ε br :=
  fun e i =>
    cast (congrArg (CompE ε br) (h.output_eq (CompE ε br) e))
      (hE (h.φ (CompE ε br) e) (cast (h.input_eq (CompE ε br) e).symm i))

open ITree in
/-- Restrict a host `bindEff` interpreter to the coded signature across a realization. -/
def BindSig.Realizes.restrict {𝓑 : BindSig} {𝓑' : BindSpec} {ε : Type} {br : ε → Type}
    (h : 𝓑.Realizes 𝓑') (hB : 𝓑'.Interp ε br) : BindInterp 𝓑 ε br :=
  fun e i blocks =>
    cast (congrArg (CompE ε br) (h.output_eq (CompE ε br) e))
      (hB (h.φ (CompE ε br) e) (cast (h.input_eq (CompE ε br) e).symm i)
        (fun b => cast (congrArg (CompE ε br) (h.brTp_eq (CompE ε br) e b).symm)
          (blocks (cast (h.br_eq (CompE ε br) e) b))))

end Ast2

end Freigen
