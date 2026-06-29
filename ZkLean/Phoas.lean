import ZkLean.Basic

/-!
# A PHOAS A-normal AST for free-monadic programs, with denotation and a reflecting elaborator

A sketch for *poking* at reflecting a real Lean term that builds a `Free F`
computation into an explicit syntax tree (`reflect%`), denoting that tree back into
`Free F` (`denote`), and handing back a *proof* that the round-trip is faithful.

We use **PHOAS** (Parametric Higher-Order Abstract Syntax): object-language
binders are Lean binders over an abstract variable representation `V : Tp → Type`.
No de Bruijn indices, no capture — we reuse Lean's binders.

## A universe of object types

The AST is no longer indexed by arbitrary Lean `Type`s.  Instead it carries a small
*object type universe* `Tp` (booleans, naturals, `ZMod n`, `Unit`, products, and
functions), with a denotation `Tp.denote : Tp → Type` back into Lean.  Indexing
everything by `Tp` (rather than `Type`) gives `reflect%` a concrete notion of which host
types are *supported*: it reifies each Lean type it meets into a `Tp` and aborts if it
cannot.

## One signature

An effect is described once, by a tiny GADT indexed by *(input type, result type)* over
plain **Lean** types — the signature knows nothing about the AST's `Tp` universe:

```
Op : Type → Type → Type        -- `Op I R` : an operation taking an `I`, returning an `R`
```

From this we *derive* the functor the freer monad `Free` needs: `Effect Op O` is some
operation `Op I O` packaged with its input `I`, and the runtime monad is the ordinary
`Free (Effect Op)`.  The AST (`Exp.op`) is what threads the object types in, by instantiating
the op at the *denotations* of its object types: `Op I.denote R.denote`.

## One A-normal AST

The AST is a single inductive family `Exp Op V α` (`α : Tp`), in **A-normal form**:
every non-trivial construct names its result with a continuation binder, and every
operand is an *atom* (a `V _`).  The constructors:

* `ret v`        — tail position: yield the atom `v : V α`.
* `lit n k`      — bind a host literal `n : α.denote` as an atom, continue with `k`.
* `op o i k`     — perform `o : Op I R` on the atom `i : V I`, bind its result, continue.
* `un`/`bin`     — apply a pure primitive (`Un`/`Bin`: arithmetic, comparison, tupling…)
                   to atoms, binding the result.
* `forN n s b k` — a bounded `for` loop over `0,…,n-1` threading a state atom through the
                   body `b`, then binding the final state into `k`.

Sequencing (`>>=`) is not a constructor: it is absorbed into the continuations of the
binding forms, which is exactly what A-normalisation buys us.
-/

namespace ZkFree

open Lean Lean.Meta Lean.Elab Lean.Elab.Term

/-! ## The object type universe -/

/-- The universe of object-language types the AST may mention. -/
inductive Tp : Type
  /-- Booleans. -/
  | bool : Tp
  /-- Naturals. -/
  | nat : Tp
  /-- The integers mod `n`. -/
  | zmod : Nat → Tp
  /-- The unit type. -/
  | unit : Tp
  /-- Product (tuple) types. -/
  | prod : Tp → Tp → Tp
  /-- Function types. -/
  | fn : Tp → Tp → Tp

/-- Denote an object type back into Lean.  Reducible so that type-class search (e.g.
    `ToString`) and unification see through it to the underlying Lean type. -/
@[reducible] def Tp.denote : Tp → Type
  | .bool     => Bool
  | .nat      => Nat
  | .zmod n   => ZMod n
  | .unit     => Unit
  | .prod a b => a.denote × b.denote
  | .fn a b   => a.denote → b.denote

/-! ## Heterogeneous lists (function argument tuples) -/

/-- A heterogeneous list: `HList β [i₀, i₁, …]` holds a `β i₀`, a `β i₁`, ….  Used for the
    argument lists of (multi-argument) functions. -/
inductive HList {ι : Type} (β : ι → Type) : List ι → Type
  | nil : HList β []
  | cons {i is} : β i → HList β is → HList β (i :: is)

/-- The first element of a non-empty `HList`. -/
def HList.head {ι : Type} {β : ι → Type} {i is} : HList β (i :: is) → β i
  | .cons x _ => x
/-- All but the first element of a non-empty `HList`. -/
def HList.tail {ι : Type} {β : ι → Type} {i is} : HList β (i :: is) → HList β is
  | .cons _ xs => xs

/-! ## Pure primitive operations -/

/-- Unary primitive operations, indexed by (argument, result) object type. -/
inductive Un : Tp → Tp → Type
  | not : Un .bool .bool
  | fst {a b : Tp} : Un (.prod a b) a
  | snd {a b : Tp} : Un (.prod a b) b

/-- Binary primitive operations, indexed by (left, right, result) object type. -/
inductive Bin : Tp → Tp → Tp → Type
  | add : Bin .nat .nat .nat
  | sub : Bin .nat .nat .nat
  | mul : Bin .nat .nat .nat
  | pow : Bin .nat .nat .nat
  | eq  : Bin .nat .nat .bool
  | and : Bin .bool .bool .bool
  | or  : Bin .bool .bool .bool
  | addZ {n : Nat} : Bin (.zmod n) (.zmod n) (.zmod n)
  | subZ {n : Nat} : Bin (.zmod n) (.zmod n) (.zmod n)
  | mulZ {n : Nat} : Bin (.zmod n) (.zmod n) (.zmod n)
  | pair {a b : Tp} : Bin a b (.prod a b)

/-- Denote a unary primitive to its Lean operation. -/
def Un.denote : Un a b → a.denote → b.denote
  | .not, x => !x
  | .fst, p => p.1
  | .snd, p => p.2

/-- Denote a binary primitive to its Lean operation. -/
def Bin.denote : Bin a b c → a.denote → b.denote → c.denote
  | .add,  x, y => x + y
  | .sub,  x, y => x - y
  | .mul,  x, y => x * y
  | .pow,  x, y => x ^ y
  | .eq,   x, y => x == y
  | .and,  x, y => x && y
  | .or,   x, y => x || y
  | .addZ, x, y => x + y
  | .subZ, x, y => x - y
  | .mulZ, x, y => x * y
  | .pair, x, y => (x, y)

/-! ## The effect signature and its derived functor -/

/-- The freer-monad functor generated by an operation signature `Op` over plain Lean types:
    one effect layer returning `O` is some operation `Op I O` packaged with its input `I`.
    `Op` knows nothing about `Tp` — the AST threads the object types in (see `Exp.op`). -/
inductive Effect (Op : Type → Type → Type 1) : Type → Type 1 where
  | mk {I O : Type} : Op I O → I → Effect Op O

/-! ## The AST -/

/-- Free-monadic PHOAS programs over an operation signature `Op`, in A-normal form.
    Functions are a second PHOAS variable family `F : List Tp → Tp → Type 1` (`F as b` names
    a function `as → b`, in the same spirit as `V` names values); they are *defined* at the
    top level (see `Prog`), and `call` invokes one by name.  Every operand is an atom (`V _`). -/
inductive Exp (Op : Type → Type → Type 1) (F : List Tp → Tp → Type 1) (V : Tp → Type) : Tp → Type 1
  /-- Tail position: return the atom `v`. -/
  | ret {α : Tp} : V α → Exp Op F V α
  /-- Bind a host literal `n : α.denote` as an atom, then continue. -/
  | lit {α β : Tp} : α.denote → (V α → Exp Op F V β) → Exp Op F V β
  /-- Perform operation `Op I.denote R.denote`: its **input** is the atom `i : V I`, and its
      **result** `R` is bound in the continuation.  The (`Tp`-agnostic) op is instantiated at
      the *denotations* of the object types `I`/`R`, which is how the AST threads typing in. -/
  | op {α I R : Tp} : Op I.denote R.denote → V I → (V R → Exp Op F V α) → Exp Op F V α
  /-- Apply a unary primitive to an atom, binding the result. -/
  | un {α a b : Tp} : Un a b → V a → (V b → Exp Op F V α) → Exp Op F V α
  /-- Apply a binary primitive to two atoms, binding the result. -/
  | bin {α a b c : Tp} : Bin a b c → V a → V b → (V c → Exp Op F V α) → Exp Op F V α
  /-- A bounded `for` loop over `0,…,n-1`: thread the state atom through `n`
      iterations of `body` (index and current state in, new state out), then bind the
      final state into the continuation. -/
  | forN {α s : Tp} : Nat → V s → (V .nat → V s → Exp Op F V s) → (V s → Exp Op F V α) → Exp Op F V α
  /-- Call a bound function on an `HList` of argument atoms, binding its result.  The function
      itself is *not* defined here — it is one of the program's top-level definitions (see
      `Prog`), referenced by its name `F as b`. -/
  | call {α : Tp} {as : List Tp} {b : Tp} :
      F as b → HList V as → (V b → Exp Op F V α) → Exp Op F V α
  /-- A *pure* object-language function value `α → β`.  Its body must be pure (built from
      `ret`/`lit`/`un`/`bin`/`lam`); used e.g. for a `hint`'s evaluator.  Bind it with `letE`. -/
  | lam {α β : Tp} : (V α → Exp Op F V β) → Exp Op F V (.fn α β)
  /-- `let`: name the result of a (sub)expression as an atom, then continue. -/
  | letE {α β : Tp} : Exp Op F V α → (V α → Exp Op F V β) → Exp Op F V β

/-- A whole program: a telescope of (monomorphic) function **definitions** pulled out in front
    of the `main` body.  Each `def_` binds a function-name `F as b` that the rest of the
    program (later definitions and `main`) may `call`; a definition's body cannot mention its
    own name, so programs are non-recursive by construction. -/
inductive Prog (Op : Type → Type → Type 1) (F : List Tp → Tp → Type 1) (V : Tp → Type)
    (mainArgs : List Tp) (α : Tp) : Type 1
  /-- The main body, after all definitions: itself a function of the program's inputs
      `mainArgs` (their atoms delivered as an `HList`). -/
  | main : (HList V mainArgs → Exp Op F V α) → Prog Op F V mainArgs α
  /-- A function definition `as → b` (body taking its arguments as an `HList`), binding its
      name in the rest of the program. -/
  | def_ {as : List Tp} {b : Tp} :
      (HList V as → Exp Op F V b) → (F as b → Prog Op F V mainArgs α) → Prog Op F V mainArgs α

/-- A *closed* program from inputs `mainArgs` to `α`: parametric in the function and variable
    representations. -/
def Closed (Op : Type → Type → Type 1) (mainArgs : List Tp) (α : Tp) : Type 2 :=
  ∀ F V, Prog Op F V mainArgs α

/-- The function representation used by `denote`: a function `as → b` denotes to a Kleisli
    arrow from the denoted argument tuple, `HList Tp.denote as → Free (Effect Op) b.denote`. -/
abbrev KleisliF (Op : Type → Type → Type 1) : List Tp → Tp → Type 1 :=
  fun as b => HList Tp.denote as → Free (Effect Op) b.denote

/-! ## Denotation (the identity interpreter, `V := Tp.denote`, `F := KleisliF Op`) -/

/-- Every object type is inhabited (so a *pure* expression always has a denotable value). -/
instance instInhabitedDenote : {α : Tp} → Inhabited α.denote
  | .bool     => ⟨false⟩
  | .nat      => ⟨0⟩
  | .zmod _   => ⟨0⟩
  | .unit     => ⟨()⟩
  | .prod a b => ⟨(@default _ (instInhabitedDenote (α := a)), @default _ (instInhabitedDenote (α := b)))⟩
  | .fn _ b   => ⟨fun _ => @default _ (instInhabitedDenote (α := b))⟩

/-- Denote a **pure** expression directly to its value — used to denote a `lam`'s body to a
    Lean function.  Effectful/looping constructors don't occur in a pure body; they fall to
    `default`. -/
def denoteVal {Op : Type → Type → Type 1} {α : Tp} : Exp Op (KleisliF Op) Tp.denote α → α.denote
  | .ret v       => v
  | .lit n k     => denoteVal (k n)
  | .un o a k    => denoteVal (k (Un.denote o a))
  | .bin o a b k => denoteVal (k (Bin.denote o a b))
  | .lam body    => fun x => denoteVal (body x)
  | .letE e k    => denoteVal (k (denoteVal e))
  | _            => default

/-- Denote an expression to a real `Free (Effect Op)` computation; a `call` applies the
    (already-denoted) function bound by an enclosing `Prog.def_`, and a `lam` denotes to a
    pure Lean function via `denoteVal`. -/
def denote {Op : Type → Type → Type 1} {α : Tp} :
    Exp Op (KleisliF Op) Tp.denote α → Free (Effect Op) α.denote
  | .ret v       => Free.Pure v
  | .lit n k     => denote (k n)
  | .op o i k    => Free.Impure (Effect.mk o i) (fun r => denote (k r))
  | .un o a k    => denote (k (Un.denote o a))
  | .bin o a b k => denote (k (Bin.denote o a b))
  | .forN n init body k =>
    freeBind
      (forIn [0:n] init
        (fun i acc => freeBind (denote (body i acc)) (fun acc' => Free.Pure (ForInStep.yield acc'))))
      (fun acc => denote (k acc))
  | .call cf args k => freeBind (cf args) (fun r => denote (k r))
  | .lam body       => Free.Pure (fun x => denoteVal (body x))
  | .letE e k       => freeBind (denote e) (fun v => denote (k v))

/-- Denote a whole program to a function from its inputs: each `def_` denotes its body to a
    Lean (Kleisli) function and binds it for the rest; `main` denotes to a function of the
    program's input tuple. -/
def denoteProg {Op : Type → Type → Type 1} {mainArgs : List Tp} {α : Tp} :
    Prog Op (KleisliF Op) Tp.denote mainArgs α → HList Tp.denote mainArgs → Free (Effect Op) α.denote
  | .main body   => fun args => denote (body args)
  | .def_ body k => denoteProg (k (fun a => denote (body a)))

/-! ## The `reflect%` elaborator

`reflect% e` takes a real Lean term `e : A₁ → … → Aₙ → Free (Effect Op) τ` (a function
returning a free-monadic value; `n = 0` is allowed) and produces

```
reflect% e : { g : A₁ → … → Aₙ → Exp Op Tp.denote τ̂ // ∀ a…, denote (g a…) = e a… }
```

where `τ̂` is the `Tp` reifying `τ`.  Every Lean type the walk needs (the result type, and
the type of each literal/atom) is reified into a `Tp` via `reifyTp`; if a type is not
expressible, the elaborator aborts.  The walk is continuation-passing, so the result
comes out A-normal, and `denote` of it is *definitionally* the original computation, so
the soundness proof is just `rfl`.
-/

/-- The denotation `Tp.denote : Tp → Type`, the variable representation `reflect%`
    targets (so the denoted program runs at the real Lean types). -/
private def denoteV : Expr := .const ``Tp.denote []

/-- Reify a Lean type into the object type universe `Tp`, or `none` if unsupported.
    Supported: `Bool`, `Nat`, `ZMod n`, `Unit`, products, and (non-dependent) functions. -/
private partial def reifyTp (T : Expr) : MetaM (Option Expr) := do
  -- Match the head *before* reducing — `whnf` would unfold e.g. `ZMod 5` to `Fin 5`.
  match_expr T with
  | Bool     => return some (.const ``Tp.bool [])
  | Nat      => return some (.const ``Tp.nat [])
  | ZMod n   => return some (mkApp (.const ``Tp.zmod []) n)
  | PUnit    => return some (.const ``Tp.unit [])
  | Prod A B =>
    let some a ← reifyTp A | return none
    let some b ← reifyTp B | return none
    return some (mkApp2 (.const ``Tp.prod []) a b)
  | _ =>
    -- a (non-dependent) function type `A → B`
    if let .forallE _ A B _ := T then
      if B.hasLooseBVars then return none      -- dependent Π: unsupported
      let some a ← reifyTp A | return none
      let some b ← reifyTp B | return none
      return some (mkApp2 (.const ``Tp.fn []) a b)
    else
      -- unfold a transparent alias (e.g. `Unit` → `PUnit`) and retry once
      let T' ← whnf T
      if T' == T then return none else reifyTp T'

/-- Reify a Lean type into a `Tp`, aborting elaboration if it is unsupported. -/
private def reifyTpOrThrow (T : Expr) : MetaM Expr := do
  match ← reifyTp T with
  | some tp => return tp
  | none    => throwError "reflect%: type is not expressible as a `Tp` \
                           (supported: `Bool`/`Nat`/`ZMod _`/`Unit`/`×`/`→`){indentExpr T}"

/-- One monomorphised function spill discovered during reflection: the source constant, its
    (object) argument-type list and result type, and the reflected body (a closed
    `HList V as → Exp Op F V b`, to become a top-level `Prog.def_`). -/
private structure DefEntry where
  name    : Name
  asList  : Expr
  retTp   : Expr
  bodyLam : Expr
  deriving Inhabited

/-- A reflection environment: the abstract function/variable representations `F`/`V` we build
    against, a substitution from continuation-bound host placeholders to object atoms, the
    running spill cache `defs`, whether we are inside a function body (bodies may not call
    definitions), and — during the second (build) pass — the function-name bound to each
    spill (`resolved`). -/
private structure Env where
  F : Expr
  V : Expr
  subst : List (FVarId × Expr)
  defs : IO.Ref (Array DefEntry)
  inBody : Bool := false
  resolved : Option (Array (DefEntry × Expr)) := none

/-- Bind a host literal `a : αTp.denote` as a fresh atom and feed that atom to `k`,
    wrapping the result in a `lit` node.  This is the A-normalisation step that turns a
    literal operand into an atom. -/
private def Env.mkLitBind (env : Env) (Op a αTp : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  withLocalDeclD `v (mkApp env.V αTp) fun vx => do
    let body ← k vx
    let lam ← mkLambdaFVars #[vx] body
    mkAppOptM ``Exp.lit #[Op, env.F, env.V, αTp, none, a, lam]

/-- `letE`-bind a function value `lam bodyLam : Exp … (.fn αt βt)`, feeding its atom to `k`. -/
private def Env.mkLam (env : Env) (Op αt βt bodyLam : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  let lamVal ← mkAppOptM ``Exp.lam #[Op, env.F, env.V, αt, βt, bodyLam]
  let fnTp := mkApp2 (.const ``Tp.fn []) αt βt
  withLocalDeclD `f (mkApp env.V fnTp) fun fAtom => do
    let lamK ← mkLambdaFVars #[fAtom] (← k fAtom)
    mkAppOptM ``Exp.letE #[Op, env.F, env.V, fnTp, none, lamVal, lamK]

/-- Emit a `ret` node returning the atom. -/
private def Env.mkRet (env : Env) (Op atom : Expr) : MetaM Expr :=
  mkAppOptM ``Exp.ret #[Op, env.F, env.V, none, atom]

/-- Build the argument tuple `HList env.V [tps]` from already-reflected atoms. -/
private def Env.mkArgHList (env : Env) (atoms : List Expr) : MetaM Expr := do
  let mut h ← mkAppOptM ``HList.nil #[none, env.V]
  for a in atoms.reverse do
    h ← mkAppM ``HList.cons #[a, h]
  pure h

/-- Project the `j`-th element out of an argument-`HList` value `hargs` (via `head`/`tail`). -/
private def projHList (hargs : Expr) (j : Nat) : MetaM Expr := do
  let mut h := hargs
  for _ in [0:j] do h ← mkAppM ``HList.tail #[h]
  mkAppM ``HList.head #[h]

/-- Pick the binary primitive for an arithmetic result type: `Nat` uses the `…` ops,
    `ZMod n` the `…Z` ops.  Returns the primitive and the result object type. -/
private def Env.arithOp (_env : Env) (natC zmodC : Name) (resTy : Expr) : MetaM (Expr × Expr) := do
  let cTp ← reifyTpOrThrow resTy
  match_expr cTp with
  | Tp.nat    => return (.const natC [], cTp)
  | Tp.zmod n => return (mkApp (.const zmodC []) n, cTp)
  | _         => throwError "reflect%: unsupported arithmetic result type{indentExpr cTp}"

/-- Build the projection primitive `@ctor a b` (`Un.fst`/`Un.snd`) for a value `p`
    whose object type must be a product `Tp.prod a b`. -/
private def Env.prodUn (_env : Env) (ctor : Name) (p : Expr) : MetaM Expr := do
  match_expr ← reifyTpOrThrow (← inferType p) with
  | Tp.prod a b => return mkApp2 (.const ctor []) a b
  | _           => throwError "reflect%: projection applied to a non-product{indentExpr p}"

mutual
  /-- Reflect a *pure* host value into an atom, A-normalising any arithmetic into a chain
      of `un`/`bin` lets, and feed the resulting atom to `k`.  Cases, in order:
      a continuation-bound variable is already an atom; a `ForInStep.yield` is unwrapped
      (loop-body tail); a value closed w.r.t. bound variables is `lit`-bound (also the
      point at which an unsupported type aborts); otherwise it must be a recognised
      primitive applied to sub-expressions, else we abort. -/
  private partial def Env.reflectExpr (env : Env) (Op a : Expr) (k : Expr → MetaM Expr) :
      MetaM Expr := do
    let a := a.consumeMData
    if let .fvar fid := a then
      if let some atom := env.subst.lookup fid then return ← k atom
    match_expr a with
    | ForInStep.yield _ v => return ← env.reflectExpr Op v k
    | ForInStep.done _ _  =>
        throwError "reflect%: `break`/early `return` inside a loop is not supported{indentExpr a}"
    | _ => pure ()
    -- a host lambda → an object-language `lam` value (its body reflected purely)
    if a.isLambda then
      if let .forallE _ A B _ := (← whnf (← inferType a)) then
        if let (some αt, some βt) := (← reifyTp A, ← reifyTp B) then
          let bodyLam ← withLocalDeclD `v (mkApp env.V αt) fun vArg =>
            withLocalDeclD `h A fun hx => do
              let env' := { env with subst := (hx.fvarId!, vArg) :: env.subst }
              mkLambdaFVars #[vArg] (← env'.reflectExpr Op (a.beta #[hx]) (env.mkRet Op ·))
          return ← env.mkLam Op αt βt bodyLam k
    -- closed w.r.t. bound variables → a literal (function arguments are allowed here)
    if !(a.hasAnyFVar fun fid => (env.subst.lookup fid).isSome) then
      return ← env.mkLitBind Op a (← reifyTpOrThrow (← inferType a)) k
    -- otherwise: a recognised primitive on sub-expressions
    match_expr a with
    | HMul.hMul _ _ _ _ x y => let (o, c) ← env.arithOp ``Bin.mul ``Bin.mulZ (← inferType a); env.reflectBin Op o c x y k
    | HAdd.hAdd _ _ _ _ x y => let (o, c) ← env.arithOp ``Bin.add ``Bin.addZ (← inferType a); env.reflectBin Op o c x y k
    | HSub.hSub _ _ _ _ x y => let (o, c) ← env.arithOp ``Bin.sub ``Bin.subZ (← inferType a); env.reflectBin Op o c x y k
    | HPow.hPow _ _ _ _ x y => env.reflectBin Op (.const ``Bin.pow []) (.const ``Tp.nat []) x y k
    | BEq.beq _ _ x y       => env.reflectBin Op (.const ``Bin.eq [])  (.const ``Tp.bool []) x y k
    | Bool.and x y          => env.reflectBin Op (.const ``Bin.and []) (.const ``Tp.bool []) x y k
    | Bool.or  x y          => env.reflectBin Op (.const ``Bin.or [])  (.const ``Tp.bool []) x y k
    | Bool.not x            => env.reflectUn  Op (.const ``Un.not [])   (.const ``Tp.bool []) x k
    | Prod.mk _ _ x y       =>
        let aTp ← reifyTpOrThrow (← inferType x)
        let bTp ← reifyTpOrThrow (← inferType y)
        env.reflectBin Op (mkApp2 (.const ``Bin.pair []) aTp bTp)
          (mkApp2 (.const ``Tp.prod []) aTp bTp) x y k
    | Prod.fst _ _ p        => env.reflectUn Op (← env.prodUn ``Un.fst p) (← reifyTpOrThrow (← inferType a)) p k
    | Prod.snd _ _ p        => env.reflectUn Op (← env.prodUn ``Un.snd p) (← reifyTpOrThrow (← inferType a)) p k
    | _ => throwError "reflect%: cannot reflect this operation on a bound variable \
                       (no matching object primitive){indentExpr a}"

  /-- Reflect a binary primitive: reflect both operands to atoms, then emit a `bin` node
      binding the result (of object type `cTp`). -/
  private partial def Env.reflectBin (env : Env) (Op binOp cTp x y : Expr)
      (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectExpr Op x fun ax =>
    env.reflectExpr Op y fun ay =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let lam ← mkLambdaFVars #[vc] (← k vc)
      mkAppOptM ``Exp.bin #[Op, env.F, env.V, none, none, none, none, binOp, ax, ay, lam]

  /-- Reflect a unary primitive: reflect the operand to an atom, then emit a `un` node. -/
  private partial def Env.reflectUn (env : Env) (Op unOp cTp x : Expr)
      (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectExpr Op x fun ax =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let lam ← mkLambdaFVars #[vc] (← k vc)
      mkAppOptM ``Exp.un #[Op, env.F, env.V, none, none, none, unOp, ax, lam]
end

/-- Reflect a list of host value-arguments into atoms (left to right), then continue with the
    collected atom list. -/
private partial def Env.reflectArgList (env : Env) (Op : Expr) :
    List Expr → (List Expr → MetaM Expr) → MetaM Expr
  | [],      k => k []
  | a :: as, k => env.reflectExpr Op a (fun atom => env.reflectArgList Op as (fun atoms => k (atom :: atoms)))

mutual
  /-- Reflect a host `Free (Effect Op) _` expression into an `Exp Op V _`, in A-normal
      form.  `k` is the *final* continuation: it consumes the atom holding this
      computation's result and produces the tail of the program. -/
  private partial def walkProg (env : Env) (Op e : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    let e := e.consumeMData.headBeta
    -- zeta-reduce `let`/`have` introduced by `do`-elaboration
    if let .letE _ _ v b _ := e then
      return ← walkProg env Op (b.instantiate1 v) k
    match_expr e with
    | Free.Pure _ _ a         => env.reflectExpr Op a k
    | Pure.pure _ _ _ a       => env.reflectExpr Op a k
    | Bind.bind _ _ _ _ x f   => walkBind env Op x f k
    | freeBind _ _ _ x f      => walkBind env Op x f k
    | ForIn.forIn _ _ _ _ beta range init body => walkForN env Op range init body beta k
    | Free.Impure _ _ _ eff cont =>
      -- `eff : Effect Op O` is `Effect.mk (o : Op I O) (inp : I)`; reify the (Lean) input and
      -- result types back to object types, then reflect the input atom
      match_expr eff with
      | Effect.mk _ I O o inp => do
          let Itp ← reifyTpOrThrow I
          let Otp ← reifyTpOrThrow O
          env.reflectExpr Op inp (fun ia => walkOp env Op Itp Otp o ia cont k)
      | _ => throwError "reflect%: effect is not an `Effect.mk`{indentExpr eff}"
    | _ =>
      -- a call to a user definition (a subroutine) → monomorphised `call`; otherwise (an
      -- effect primitive, or anything not call-shaped) unfold its head and inline
      match ← tryCall env Op e k with
      | some prog => pure prog
      | none =>
        match ← unfoldDefinition? e with
        | some e' => walkProg env Op e' k
        | none    => throwError "reflect%: don't know how to reflect computation{indentExpr e}"

  /-- Reflect a `bind x f`.  A *pure* `x` (`pure a`) is inlined via the monad left-identity
      law (`pure a >>= f ≡ f a`) — this elides the unit-typed `pure ()` actions that
      `do`-notation inserts between statements; otherwise `x` is an effect whose result atom
      is threaded into `f`. -/
  private partial def walkBind (env : Env) (Op x f : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    match_expr x.consumeMData.headBeta with
    | Free.Pure _ _ a   => walkProg env Op (f.beta #[a]) k
    | Pure.pure _ _ _ a => walkProg env Op (f.beta #[a]) k
    | _                 => walkProg env Op x (fun xa => walkBindCont env Op f xa k)

  /-- Continue a `bind`: `f : X → Free _ τ` is the binder, `xa : V α` is the atom holding
      the bound value.  Apply `f` to a host placeholder (rewritten to `xa`) and walk its
      body with the same final continuation `k`. -/
  private partial def walkBindCont (env : Env) (Op f xa : Expr) (k : Expr → MetaM Expr) :
      MetaM Expr := do
    let fty ← whnf (← inferType f)
    let .forallE _ X _ _ := fty
      | throwError "reflect%: expected a continuation function, got{indentExpr fty}"
    withLocalDeclD `h X fun hx => do
      let env' := { env with subst := (hx.fvarId!, xa) :: env.subst }
      walkProg env' Op (f.beta #[hx]) k

  /-- Emit an `op` node.  `Itp`/`Otp : Tp` are the op's input/result object types and `cont :
      Otp.denote → Free _ τ` its continuation; we introduce the object variable `vx : V Otp`
      it binds and a host placeholder `hx : Otp.denote` (rewritten to `vx`), then walk the
      rest.  `Itp`/`Otp` are passed explicitly because `Op` is opaque (they can't be recovered
      from `o`'s type by inverting `Tp.denote`). -/
  private partial def walkOp (env : Env) (Op Itp Otp o ia cont : Expr) (k : Expr → MetaM Expr) :
      MetaM Expr := do
    let cty ← whnf (← inferType cont)
    let .forallE _ Rt _ _ := cty
      | throwError "reflect%: expected an op continuation, got{indentExpr cty}"
    withLocalDeclD `v (mkApp env.V Otp) fun vx =>
    withLocalDeclD `h Rt fun hx => do
      let env' := { env with subst := (hx.fvarId!, vx) :: env.subst }
      let body ← walkProg env' Op (cont.beta #[hx]) k
      let lam ← mkLambdaFVars #[vx] body
      mkAppOptM ``Exp.op #[Op, env.F, env.V, none, Itp, Otp, o, ia, lam]

  /-- Reflect a `ForIn.forIn` over a constant range `[0:n]` into a `forN` node.  `beta` is
      the (host) loop-state type; `body : Nat → β → Free _ (ForInStep β)`.  We require a
      literal `[0:n]` (start 0, step 1), reflect the initial state to an atom, build the
      body under fresh index/state atoms (its tail `ForInStep.yield` is unwrapped by
      `reflectExpr`), and thread the final state into `k`. -/
  private partial def walkForN (env : Env) (Op range init body beta : Expr)
      (k : Expr → MetaM Expr) : MetaM Expr := do
    let sTp ← reifyTpOrThrow beta
    let nExpr ← match_expr range with
      | Std.Legacy.Range.mk start stop step _ => do
          unless ← isDefEq start (mkNatLit 0) do
            throwError "reflect%: loop range must start at 0{indentExpr range}"
          unless ← isDefEq step (mkNatLit 1) do
            throwError "reflect%: loop range must have step 1{indentExpr range}"
          pure stop
      | _ => throwError "reflect%: loop range is not a literal `[0:n]`{indentExpr range}"
    env.reflectExpr Op init fun initAtom => do
      let bodyLam ← withLocalDeclD `i (mkApp env.V (.const ``Tp.nat [])) fun vi =>
                    withLocalDeclD `s (mkApp env.V sTp) fun vs =>
                    withLocalDeclD `hi (.const ``Nat []) fun hi =>
                    withLocalDeclD `hs beta fun hs => do
                      let env' := { env with
                        subst := (hi.fvarId!, vi) :: (hs.fvarId!, vs) :: env.subst }
                      let bodyExp ← walkProg env' Op (body.beta #[hi, hs]) (env.mkRet Op ·)
                      mkLambdaFVars #[vi, vs] bodyExp
      let contLam ← withLocalDeclD `r (mkApp env.V sTp) fun vr => do
                      mkLambdaFVars #[vr] (← k vr)
      mkAppOptM ``Exp.forN #[Op, env.F, env.V, none, sTp, nExpr, initAtom, bodyLam, contLam]

  /-- Try to reflect `e` as a *call* to a user definition (returning `some prog`), or decline
      (`none`) so the caller inlines it instead.  A call is recognised purely by reflection:
      `e` must be an applied global `def` whose unfolding is **not** a bare `Free.Impure`
      (that would be an effect primitive — inline it) and which, after splitting off its
      *type parameters* (binders a later argument or the result depends on), has exactly one
      *value argument* of reifiable type.  Calls inside a function body are declined (so they
      inline) to keep every spill in one scope.  Qualifying calls are monomorphised: the
      `(constant, arg-type, result-type)` signature is looked up in the spill cache — a hit
      re-uses the bound function, a miss reflects the specialised body into a fresh `letFun`. -/
  private partial def tryCall (env : Env) (Op e : Expr) (k : Expr → MetaM Expr) :
      MetaM (Option Expr) := do
    if env.inBody then return none
    let fn := e.getAppFn
    let some cName := fn.constName? | return none
    let some ci := (← getEnv).find? cName | return none
    let some cVal := ci.value? | return none
    let fArgs := e.getAppArgs
    let cValInst := cVal.instantiateLevelParams ci.levelParams fn.constLevels!
    -- effect primitives (smart constructors unfolding to a bare `Free.Impure`) are inlined
    match_expr (cValInst.beta fArgs).consumeMData.headBeta with
    | Free.Impure _ _ _ _ _ => return none
    | _ => pure ()
    -- classify each binder as a type parameter (depended upon later) or a value argument
    let valuePos ← forallTelescope (← inferType fn) fun xs cod => do
      let mut vps : Array Nat := #[]
      for i in [0:xs.size] do
        let mut dep := cod.containsFVar xs[i]!.fvarId!
        for j in [i+1:xs.size] do
          if (← inferType xs[j]!).containsFVar xs[i]!.fvarId! then dep := true
        unless dep do vps := vps.push i
      pure vps
    -- a definition with ≥1 value argument becomes a call; anything else inlines
    if valuePos.size == 0 then return none
    let valueArgs := valuePos.toList.map (fArgs[·]!)
    let mut argTps : Array Expr := #[]
    for va in valueArgs do
      let some t ← reifyTp (← inferType va) | return none
      argTps := argTps.push t
    let asList ← mkListLit (.const ``Tp []) argTps.toList
    let some retTp ← (match_expr (← whnf (← inferType e)) with
                        | Free _ R => reifyTp R | _ => pure none) | return none
    let sigMatches (d : DefEntry) : MetaM Bool := do
      pure (d.name == cName && (← isDefEq d.asList asList) && (← isDefEq d.retTp retTp))
    -- reflect the argument atoms, build their `HList`, and emit a `call` to function `cf`
    let emit (cf : Expr) : MetaM Expr :=
      env.reflectArgList Op valueArgs (fun atoms => do
        env.emitCall Op cf asList retTp (← env.mkArgHList atoms) k)
    match env.resolved with
    | some resolved =>
      -- build pass: emit a call to the pre-bound function-name for this spill
      let some (_, cf) ← resolved.findM? (fun de => sigMatches de.1) | return none
      some <$> emit cf
    | none =>
      -- discovery pass: reflect the specialised body once (the main expression is discarded),
      -- recording the spill so the build pass can bind a name for it
      unless (← (← env.defs.get).findM? sigMatches).isSome do
        let hlistTy ← mkAppM ``HList #[env.V, asList]
        let bodyLam ← withLocalDeclD `args hlistTy fun hargs => do
          let decls : Array (Name × (Array Expr → MetaM Expr)) :=
            valueArgs.toArray.map (fun va => (`x, fun _ => inferType va))
          withLocalDeclsD decls fun hxs => do
            let mut subst := env.subst
            for j in [0:hxs.size] do
              subst := (hxs[j]!.fvarId!, ← projHList hargs j) :: subst
            let mut fullArgs := fArgs
            for j in [0:valuePos.size] do
              fullArgs := fullArgs.set! (valuePos[j]!) hxs[j]!
            let env' := { env with subst, inBody := true }
            let bodyExp ← walkProg env' Op (cValInst.beta fullArgs) (env.mkRet Op ·)
            mkLambdaFVars #[hargs] bodyExp
        env.defs.modify (·.push { name := cName, asList, retTp, bodyLam })
      -- a throwaway function-name suffices: the discovery pass's expression is discarded
      some <$> emit (← mkFreshExprMVar (mkApp2 env.F asList retTp))

  /-- Emit a `call cf args k`, binding the result atom for the continuation. -/
  private partial def Env.emitCall (env : Env) (Op cf asList retTp hl : Expr)
      (k : Expr → MetaM Expr) : MetaM Expr := do
    let contLam ← withLocalDeclD `r (mkApp env.V retTp) fun vr => do mkLambdaFVars #[vr] (← k vr)
    mkAppOptM ``Exp.call #[Op, env.F, env.V, none, asList, retTp, cf, hl, contLam]
end

elab "reflect% " t:term : term => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  -- Telescope the *type* (so this also works when `e` is a bare constant, not a
  -- literal `fun`), then apply `e` to the introduced arguments.
  forallTelescope (← inferType e) fun args codom => do
    let bty ← whnf codom
    let_expr Free F τ := bty
      | throwError "reflect%: the body must have type `Free F τ`, got{indentExpr bty}"
    let_expr Effect Op := F
      | throwError "reflect%: the functor must be `Effect Op`, got{indentExpr F}"
    -- the result type must be a supported object type (early, clear error)
    let _ ← reifyTpOrThrow τ
    -- `main`'s argument types must all be monomorphic (reify to `Tp`) and non-dependent: no
    -- argument may be a *type parameter* (used in a later argument's or the result's type).
    for i in [0:args.size] do
      if τ.containsFVar args[i]!.fvarId! then
        throwError "reflect%: `main`'s result type may not depend on its arguments"
      for j in [i+1:args.size] do
        if (← inferType args[j]!).containsFVar args[i]!.fvarId! then
          throwError "reflect%: `main` may not take a type-parameter argument\
                      {indentExpr (← inferType args[i]!)}"
    let mut mainArgTps : Array Expr := #[]
    for a in args do
      mainArgTps := mainArgTps.push (← reifyTpOrThrow (← inferType a))
    let mainArgsList ← mkListLit (.const ``Tp []) mainArgTps.toList
    -- Build the program against abstract `F : List Tp → Tp → Type 1` and `V : Tp → Type`.
    let tyTy := mkSort (.succ .zero)
    let tp := (.const ``Tp [] : Expr)
    let fTy ← mkArrow (mkApp (.const ``List [.zero]) tp) (← mkArrow tp (mkSort (.succ (.succ .zero))))
    withLocalDeclD `F fTy fun F => do
    withLocalDeclD `V (← mkArrow tp tyTy) fun V => do
      let defs ← IO.mkRef (#[] : Array DefEntry)
      let retK := fun (atom : Expr) => mkAppOptM ``Exp.ret #[Op, F, V, none, atom]
      let topBody := (← unfoldDefinition? (e.beta args)).getD (e.beta args)
      let hlistTy ← mkAppM ``HList #[V, mainArgsList]
      -- Walk `main` under an argument tuple `hargs`, substituting each host argument for its
      -- atom; `resolved` selects discovery (`none`) vs build (`some`) pass.
      let walkMain (resolved : Option (Array (DefEntry × Expr))) (hargs : Expr) : MetaM Expr := do
        let mut subst : List (FVarId × Expr) := []
        for i in [0:args.size] do
          subst := (args[i]!.fvarId!, ← projHList hargs i) :: subst
        walkProg { F := F, V := V, subst := subst, defs := defs, resolved := resolved } Op topBody retK
      -- Pass 1 (discovery): collect the function spills (their bodies); discard `main`.
      let _ ← withLocalDeclD `args hlistTy fun h => walkMain none h
      let entries ← defs.get
      -- Pass 2 (build): bind a name per spill, rebuild `main`, assemble the `Prog` with the
      -- definitions pulled out in front of `main` (definitions in discovery order).
      let prog ← withLocalDeclsD (entries.map fun d => (`f, fun _ => pure (mkApp2 F d.asList d.retTp)))
        fun cfs => do
          let resolved := entries.zip cfs
          let mainLam ← withLocalDeclD `args hlistTy fun h => do
            mkLambdaFVars #[h] (← walkMain (some resolved) h)
          let mut prog ← mkAppOptM ``Prog.main #[Op, F, V, mainArgsList, none, mainLam]
          for j in [0:entries.size] do
            let (d, cf) := resolved[entries.size - 1 - j]!
            prog ← mkAppOptM ``Prog.def_
              #[Op, F, V, mainArgsList, none, d.asList, d.retTp, d.bodyLam, ← mkLambdaFVars #[cf] prog]
          pure prog
      -- g := fun F V => prog   (`g.1` is `Closed Op mainArgs τ̂`)
      let g ← mkLambdaFVars #[F, V] prog
      let gTy ← inferType g
      let kf := mkApp (.const ``KleisliF []) Op
      -- the original arguments as an `HList Tp.denote mainArgs`, for the soundness statement
      let mut argHList ← mkAppOptM ``HList.nil #[none, denoteV]
      for (a, t) in (args.zip mainArgTps).reverse do
        argHList ← mkAppOptM ``HList.cons #[none, denoteV, t, none, a, argHList]
      -- predicate  fun g => ∀ args, denoteProg (g (KleisliF Op) Tp.denote) ⟨args…⟩ = e args
      let pred ← withLocalDeclD `g gTy fun gv => do
        let lhs ← mkAppOptM ``denoteProg #[Op, none, none, mkAppN gv #[kf, denoteV], argHList]
        let eq ← mkEq lhs (e.beta args)
        mkLambdaFVars #[gv] (← mkForallFVars args eq)
      -- proof  fun args => rfl   (denoteProg (g (KleisliF Op) Tp.denote) ⟨args…⟩ ≡ e args)
      let dp ← mkAppOptM ``denoteProg #[Op, none, none, mkAppN g #[kf, denoteV], argHList]
      let prf ← mkLambdaFVars args (← mkEqRefl dp)
      mkAppOptM ``Subtype.mk #[gTy, pred, g, prf]

/-! ## A pretty-printer (instantiating `V := fun _ => String`) -/

/-- Render a host literal of object type `α` for the pretty-printer.  Scalars print
    their value; functions (and `ZMod`, lacking a uniform `ToString`) print a placeholder. -/
def Tp.toStr : (α : Tp) → α.denote → String
  | .bool,     b => toString b
  | .nat,      n => toString n
  | .zmod n,   x => s!"{x.val}#{n}"          -- residue `#` modulus
  | .unit,     _ => "()"
  | .prod a b, p => s!"({Tp.toStr a p.1}, {Tp.toStr b p.2})"
  | .fn _ _,   _ => "<fn>"

/-- Render an object *type* for the pretty-printer (`ZMod n` prints as `Field<n>`). -/
def Tp.toTypeStr : Tp → String
  | .bool     => "Bool"
  | .nat      => "Nat"
  | .zmod n   => s!"Field<{n}>"
  | .unit     => "Unit"
  | .prod a b => s!"({a.toTypeStr} × {b.toTypeStr})"
  | .fn a b   => s!"({a.toTypeStr} → {b.toTypeStr})"

/-- Symbol for a unary primitive, for the pretty-printer. -/
def Un.sym : Un a b → String
  | .not => "!" | .fst => ".1 " | .snd => ".2 "

/-- Symbol for a binary primitive, for the pretty-printer. -/
def Bin.sym : Bin a b c → String
  | .add => "+" | .sub => "-" | .mul => "*" | .pow => "^" | .eq => "==" | .and => "&&" | .or => "||"
  | .addZ => "+" | .subZ => "-" | .mulZ => "*" | .pair => ","

/-- Indentation (two spaces per nesting level) for the pretty-printer. -/
private def ppIndent (d : Nat) : String := String.join (List.replicate d "  ")

/-- Value representation for pretty-printing: every atom is its name string. -/
abbrev PpV : Tp → Type := fun _ => String
/-- Function representation for pretty-printing: a function name (in `Type 1` via
    `ULift`, to match `Exp`'s `F : List Tp → Tp → Type 1`). -/
abbrev PpF : List Tp → Tp → Type 1 := fun _ _ => ULift String

/-- Collect the name strings out of a pretty-printing argument `HList`. -/
def hlistStrings : {as : List Tp} → HList PpV as → List String
  | [],    .nil       => []
  | _::_,  .cons x xs => x :: hlistStrings xs

/-- A fresh argument `HList` of names `x{i}, x{i+1}, …` for a pretty-printed function body. -/
def freshHList : (as : List Tp) → Nat → HList PpV as × Nat
  | [],    i => (.nil, i)
  | _::as, i => let (xs, j) := freshHList as (i + 1); (.cons s!"x{i}" xs, j)

/-- Render a typed binder list `x0 : T0, x1 : T1, …` from argument names and their types. -/
def ppBinders (as : List Tp) (argv : HList PpV as) : String :=
  String.intercalate ", " ((hlistStrings argv).zip (as.map Tp.toTypeStr) |>.map
    (fun (n, t) => s!"{n} : {t}"))

/-- Worker for `pp`, threading the nesting depth `d` (for indentation) and a fresh-name
    counter `i`.  Every binding is emitted on its own line at depth `d`; `forN`/`letFun`
    bodies are rendered one level deeper.  Note the `op`/`call` cases can render their
    operands directly — only possible because they are now atoms (here, `String`s). -/
private def ppAux {Op : Type → Type → Type 1} {α : Tp}
    (name : {I R : Type} → Op I R → String) :
    Nat → Nat → Exp Op PpF PpV α → (String × Nat)
  | d, i, .ret v => (s!"{ppIndent d}{v}", i)
  | d, i, @Exp.lit _ _ _ α _ val k =>
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} := {Tp.toStr α val}\n{rest}", i)
  | d, i, .letE (.lam body) k =>
    -- the common shape: `let v := λ x => …`
    let arg := s!"x{i}"
    let i := i + 1
    let (b, i) := ppAux name (d + 1) i (body arg)
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} := λ {arg} =>\n{b}\n{rest}", i)
  | d, i, .letE e k =>
    let (eStr, i) := ppAux name d i e
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} :=\n{eStr}\n{rest}", i)
  | d, i, .lam body =>
    let arg := s!"x{i}"
    let i := i + 1
    let (b, i) := ppAux name (d + 1) i (body arg)
    (s!"{ppIndent d}λ {arg} =>\n{b}", i)
  | d, i, .op o inp k =>
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} ← {name o}({inp})\n{rest}", i)
  | d, i, .un o a k =>
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} := {Un.sym o}{a}\n{rest}", i)
  | d, i, .bin o a b k =>
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    -- `pair` reads better as a tuple than as an infix `,`
    let rhs := if Bin.sym o == "," then s!"({a}, {b})" else s!"{a} {Bin.sym o} {b}"
    (s!"{ppIndent d}let {v} := {rhs}\n{rest}", i)
  | d, i, .forN n init body k =>
    let iv := s!"i{i}"
    let av := s!"a{i}"
    let i := i + 1
    let (b, i) := ppAux name (d + 1) i (body iv av)
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} := forN {n} from {init} via λ {iv} {av} =>\n{b}\n{rest}", i)
  | d, i, .call cf args k =>
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} := {cf.down}({String.intercalate ", " (hlistStrings args)})\n{rest}", i)

/-- Worker for `pp` over a whole `Prog`: print each pulled-out function definition (`f{i} = λ
    … => …`), then the `main` body. -/
private def ppProgAux {Op : Type → Type → Type 1} {mainArgs : List Tp} {α : Tp}
    (name : {I R : Type} → Op I R → String) :
    Nat → Prog Op PpF PpV mainArgs α → (String × Nat)
  | i, @Prog.main _ _ _ mainArgs _ body =>
    let (argv, i) := freshHList _ i
    let (b, i) := ppAux name 1 i (body argv)
    (s!"def main({ppBinders mainArgs argv}) =>\n{b}", i)
  | i, @Prog.def_ _ _ _ _ _ as _ body k =>
    let f := s!"f{i}"
    let i := i + 1
    let (argv, i) := freshHList _ i
    let (b, i) := ppAux name 1 i (body argv)
    let (rest, i) := ppProgAux name i (k (ULift.up f))
    (s!"def {f}({ppBinders as argv}) =>\n{b}\n{rest}", i)

/-- Pretty-print a whole program: the function definitions, then `def main`. -/
def pp {Op : Type → Type → Type 1} {mainArgs : List Tp} {α : Tp}
    (name : {I R : Type} → Op I R → String) (p : Prog Op PpF PpV mainArgs α) : String :=
  (ppProgAux name 0 p).1

/-! ## A concrete signature

The single source of truth — note `CircOp.assertNZ`'s input is a `nat`, which in a
program will be supplied as an *atom* (often a variable). -/

inductive CircOp : Type → Type → Type 1
  /-- A hint (advice): evaluate `f` on the seed `a`, returning the result `β`.  Its input
      packages both into a pair `α × (α → β)`, so this is a special "eval" operator. -/
  | hint {α β : Type} : CircOp (α × (α → β)) β
  /-- Assert the input `Nat` is nonzero; returns the `Bool` result of the check. -/
  | assertNZ : CircOp Nat Bool
  /-- Assert the input `Bool` holds; returns it. -/
  | assert   : CircOp Bool Bool

/-- Operation names, for the pretty-printer. -/
def CircOp.name : {I R : Type} → CircOp I R → String
  | _, _, .hint     => "hint"
  | _, _, .assertNZ => "assertNZ"
  | _, _, .assert   => "assert"

/-- Runtime smart constructors, living in the ordinary `Free (Effect CircOp)`.  `CircOp` is
    fully `Tp`-agnostic, so these are plain Lean-typed. -/
def hintF {α β : Type} (a : α) (f : α → β) : Free (Effect CircOp) β :=
  Free.Impure (Effect.mk CircOp.hint (a, f)) Free.Pure
def assertNZ (x : Nat) : Free (Effect CircOp) Bool :=
  Free.Impure (Effect.mk CircOp.assertNZ x) Free.Pure
def assert (b : Bool) : Free (Effect CircOp) Bool :=
  Free.Impure (Effect.mk CircOp.assert b) Free.Pure

/-! ## Examples / smoke tests -/

section Examples

variable {V : Tp → Type} {α : Tp}

/-- A real Lean `do`-block.  `hint` evaluates its function (here the identity) on the seed
    `k`; its `(seed, fn)` input is A-normalised into a `lit`-bound function and a `pair`.  The
    result threads `n` rather than computing on it. -/
def hostExample (k : Nat) : Free (Effect CircOp) Nat := do
  let n ← hintF k (fun s => s)
  let _ ← assertNZ n
  pure n


/-- Reflecting it yields a **closed** (`∀ V`) A-normal AST plus a `rfl`-backed proof. -/
def reflectedExample := reflect% hostExample

#check (reflectedExample.1 :
  (F : List Tp → Tp → Type 1) → (V : Tp → Type) → Prog CircOp F V [Tp.nat] Tp.nat)

/-- Soundness: `denoteProg` applied to the argument tuple matches the host (at `F := KleisliF`,
    `V := Tp.denote`). -/
example : ∀ k, denoteProg (reflectedExample.1 (KleisliF CircOp) Tp.denote) (.cons k .nil) =
    hostExample k := reflectedExample.2

/-- Closed case (`main` takes no arguments): `reflect%`'s program is literally a `Closed`. -/
example : denoteProg ((reflect% (hostExample 7)).1 (KleisliF CircOp) Tp.denote) .nil = hostExample 7 :=
  (reflect% (hostExample 7)).2

-- `main` takes its argument as a parameter (`x0`); `hint`'s `(seed, fn)` input pairs the seed
-- with the evaluator, now a real AST `λ` (here the identity):
--   def main(x0 : Nat) =>
--     let v2 := λ x1 =>
--       x1
--     let v3 := (x0, v2)
--     let v4 ← hint(v3)
--     let v5 ← assertNZ(v4)
--     v4
#eval IO.println (pp CircOp.name (reflectedExample.1 PpF PpV))

-- And it denotes back to an ordinary `Free (Effect CircOp)` computation (here at `k := 99`):
#check (denoteProg (reflectedExample.1 (KleisliF CircOp) Tp.denote) (.cons 99 .nil) :
  Free (Effect CircOp) Nat)


/-- A computation whose *result* type is not expressible as a `Tp`: `reflect%` must abort. -/
def badResult : Free (Effect CircOp) (List Nat) := pure []
#check_failure (reflect% badResult)

/-- Compile-time exponent. -/
def powN : Nat := 5

/-- Compute `x ^ powN` by iterated multiplication, accumulating in a `let mut` driven by a
    `for … in` loop, then assert the loop result equals a hinted value.

    The `let mut` + `for` lowers to `ForIn.forIn` over the `Free` monad, the body's `acc * x`
    is a pure operation on the loop-state atom (and on `main`'s argument atom `x`), and the
    `==` is another — so this exercises the loop node and the primitive-operation compiler. -/
def powExample (x : Nat) : Free (Effect CircOp) Bool := do
  let mut acc := 1
  for _ in [0:powN] do
    acc := acc * x
  let h ← hintF x (fun v => v ^ powN)
  assert (acc == h)

/-- It reflects into a `forN` loop whose body is a `bin .mul`, then a `hint`, a `bin .eq`,
    and the `assert` effect. -/
def reflectedPow := reflect% powExample

/-- Soundness still holds by `rfl`: `denote`'s `forN` case is defined via the very same
    `forIn`, so the round-trip is definitional even with the loop. -/
example : ∀ x, denoteProg (reflectedPow.1 (KleisliF CircOp) Tp.denote) (.cons x .nil) =
    powExample x := reflectedPow.2

-- `x` is `main`'s argument atom; the reference value is a `hint` whose evaluator is a real
-- AST `λ` computing `· ^ powN`:
--   def main(x0 : Nat) =>
--     let v1 := 1
--     let v4 := forN 5 from v1 via λ i2 a2 =>
--       let v3 := a2 * x0
--       v3
--     let v8 := λ x5 =>
--       let v6 := 5
--       let v7 := x5 ^ v6
--       v7
--     let v9 := (x0, v8)
--     let v10 ← hint(v9)
--     let v11 := v4 == v10
--     let v12 ← assert(v11)
--     v12
#eval IO.println (pp CircOp.name (reflectedPow.1 PpF PpV))

/-! ## Monomorphising definitions

`dbl` works for any `ZMod N`; `reflect%` recognises calls to it automatically (it is an
applied `def` that does not unfold to a bare effect primitive), monomorphises each call on
`N`, and shares a single spilled definition between equal `N`s. -/

/-- A `ZMod N`-polymorphic helper — no annotation needed. -/
def dbl {N : Nat} (x : ZMod N) : Free (Effect CircOp) (ZMod N) := pure (x + x)

/-- `dbl` is called at `N = 5`, `N = 7`, then `N = 5` again — so reflection should produce
    exactly two spilled functions (one per distinct `N`), the third call re-using the first. -/
def monoExample (a : ZMod 5) (b : ZMod 7) (c : ZMod 5) : Free (Effect CircOp) (ZMod 5) := do
  let p ← dbl a
  let _ ← dbl b
  let r ← dbl c
  pure (p + r)

def reflectedMono := reflect% monoExample

/-- Soundness by `rfl`: each `call` denotes to applying the (denoted) spilled body, which is
    definitionally the original `dbl` instance. -/
example : ∀ a b c, denoteProg (reflectedMono.1 (KleisliF CircOp) Tp.denote) (.cons a (.cons b (.cons c .nil))) =
    monoExample a b c := reflectedMono.2

-- Two definitions pulled out in front of `main` (`f0 = dbl@5`, `f3 = dbl@7`); `main` takes
-- its three arguments, and the third call (N=5) re-uses `f0`:
--   def f0(x1 : Field<5>) =>
--     let v2 := x1 + x1
--     v2
--   def f3(x4 : Field<7>) =>
--     let v5 := x4 + x4
--     v5
--   def main(x6 : Field<5>, x7 : Field<7>, x8 : Field<5>) =>
--     let v9 := f0(x6)           -- dbl a   (N=5)
--     let v10 := f3(x7)          -- dbl b   (N=7)
--     let v11 := f0(x8)          -- dbl c   (N=5, re-uses f0)
--     let v12 := v9 + v11
--     v12
#eval IO.println (pp CircOp.name (reflectedMono.1 PpF PpV))

/-! ## Multi-argument definitions

A function may take several arguments, passed as an `HList`. -/

/-- A two-argument `ZMod N`-polymorphic helper. -/
def muladd {N : Nat} (x y : ZMod N) : Free (Effect CircOp) (ZMod N) := pure (x * y + x)

/-- Two calls to the same `N = 5` instance: one spill, re-used. -/
def multiExample (a b : ZMod 5) : Free (Effect CircOp) (ZMod 5) := do
  let p ← muladd a b
  let q ← muladd b a
  pure (p + q)

def reflectedMulti := reflect% multiExample

/-- Soundness by `rfl`, with arguments delivered through the `HList`. -/
example : ∀ a b, denoteProg (reflectedMulti.1 (KleisliF CircOp) Tp.denote) (.cons a (.cons b .nil)) =
    multiExample a b := reflectedMulti.2

-- One two-argument function (`f0 = muladd@5`) pulled out in front of `main`, called twice:
--   def f0(x1 : Field<5>, x2 : Field<5>) =>
--     let v3 := x1 * x2
--     let v4 := v3 + x1
--     v4
--   def main(x5 : Field<5>, x6 : Field<5>) =>
--     let v7 := f0(x5, x6)       -- muladd a b
--     let v8 := f0(x6, x5)       -- muladd b a   (re-uses f0)
--     let v9 := v7 + v8
--     v9
#eval IO.println (pp CircOp.name (reflectedMulti.1 PpF PpV))

end Examples

end ZkFree
