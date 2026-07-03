import Freigen.Free
import Freigen.Ast.Tp
import Freigen.ITree.Basic

/-!
# The AST: syntax and denotation

`Code`/`Prog` is a dumb, typed imperative AST indexed by the object types `Tp`: instructions,
reified arithmetic (`un`/`bin`), boolean branches, **first-class functions** (`lam`/`app` —
function values are ordinary code blocks, potentially effectful, denoting as Kleisli arrows),
**calls to top-level function definitions** (`call` + `Prog.def_`/`Prog.rec_`), and scoped
blocks.  It is PHOAS over a function family `F` and values `V`, with the effect signatures
opaque.

## Denotation

`Tp.denote X` interprets object types over a first-order DSL signature `X : TpF → TpF → Type`,
with `(.fn a b).denote X = a.denote X → Comp X (b.denote X)` — a **Kleisli arrow** into the
interaction-tree domain.  The AST has no notion of purity: a function value is just a suspended
code block.  (This is only possible because the whole effect stack is `Type 0`.)

The code-level operation vocabulary is a `Tp`-indexed family `Opc : Tp → Tp → Type` — for
ordinary code the lift `OpT X` of the DSL signature, for a `rec_` body its `CallOp` extension
(the self-call, whose state may freely contain function values).  `denote` is parameterised by
an **event injection** (`Inj`): how each code-level op emits an event of the target signature.
At every concrete operation the injection's type-coercions reduce to `rfl`, so nothing is paid.

`denoteProg` gives a whole program meaning uniformly: a function denotes as a Kleisli
subroutine, and a recursive definition is tied by `mrec` — so a `Prog` cannot be mapped into a
finite monad (the AST does not assume termination).
-/

namespace Freigen

open Freigen.ITree

/-! ## Denotation of object types -/

/-- Denote an object type over a first-order DSL signature `X`.  A function type denotes as a
    **Kleisli arrow** into the interaction-tree domain — function values are (suspended,
    potentially effectful) computations, like any other code.  Reducible so type-class search
    and unification see through it. -/
@[reducible] def Tp.denote (X : TpF → TpF → Type) : Tp → Type
  | .bool     => Bool
  | .nat      => Nat
  | .zmod n   => ZMod n
  | .unit     => Unit
  | .prod a b => a.denote X × b.denote X
  | .fn a b   => a.denote X → Comp X (b.denote X)
  | .vec a n  => Vector (a.denote X) n
  | .array a  => Array (a.denote X)
  | .sum a b  => a.denote X ⊕ b.denote X
  | .fin n    => Fin n

/-- On first-order types the two denotations agree — **definitionally at every concrete type**:
    the proof is a `congrArg`-chain that reduces to `rfl` on constructors, so a `cast` along it
    vanishes.  (Stated as a `def` so it unfolds.) -/
def TpF.denote_tp (X : TpF → TpF → Type) : (t : TpF) → Tp.denote X t.tp = t.denote
  | .bool     => rfl
  | .nat      => rfl
  | .zmod _   => rfl
  | .unit     => rfl
  | .fin _    => rfl
  | .prod a b => congr (congrArg Prod (denote_tp X a)) (denote_tp X b)
  | .vec a n  => congrFun (congrArg Vector (denote_tp X a)) n
  | .array a  => congrArg Array (denote_tp X a)
  | .sum a b  => congr (congrArg Sum (denote_tp X a)) (denote_tp X b)

/-- Denote a unary primitive to its Lean operation. -/
def Un.denote {X : TpF → TpF → Type} {a b : Tp} : Un a b → a.denote X → b.denote X
  | .not, x => !x
  | .fst, p => p.1
  | .snd, p => p.2
  | .inl, x => Sum.inl x
  | .inr, x => Sum.inr x
  | .toArray, v => v.toArray
  | .finVal, i => i.val

/-- Denote a binary primitive to its Lean operation. -/
def Bin.denote {X : TpF → TpF → Type} {a b c : Tp} :
    Bin a b c → a.denote X → b.denote X → c.denote X
  | .add,  x, y => x + y
  | .sub,  x, y => x - y
  | .mul,  x, y => x * y
  | .pow,  x, y => x ^ y
  | .eq,   x, y => x == y
  | .lt,   x, y => decide (x < y)
  | .ble,  x, y => decide (x ≤ y)
  | .and,  x, y => x && y
  | .or,   x, y => x || y
  | .addZ, x, y => x + y
  | .subZ, x, y => x - y
  | .mulZ, x, y => x * y
  | .powZ, x, y => x ^ y
  | .pair, x, y => (x, y)
  | .push, xs, x => xs.push x

/-- Denote a partial primitive; `none` is the erased proof obligation failing. -/
def POp.denote {X : TpF → TpF → Type} :
    {as : List Tp} → {b : Tp} → POp as b → HList (Tp.denote X) as → Option (b.denote X)
  | _, _, @POp.vget _ n, .cons v (.cons i .nil) =>
      if h : i < n then some (v[i]'h) else none
  | _, _, @POp.vset _ n, .cons v (.cons i (.cons x .nil)) =>
      if h : i < n then some (v.set i x h) else none
  | _, _, .aget, .cons v (.cons i .nil) =>
      if h : i < v.size then some (v[i]'h) else none
  | _, _, .aset, .cons v (.cons i (.cons x .nil)) =>
      if h : i < v.size then some (v.set i x h) else none
  | _, _, @POp.arrToVec _ n, .cons arr .nil =>
      if h : arr.size = n then some ⟨arr, h⟩ else none
  | _, _, @POp.natToFin n, .cons m .nil =>
      if h : m < n then some ⟨m, h⟩ else none
  | _, _, .select, .cons c (.cons x (.cons y .nil)) =>
      some (bif c then x else y)

/-! ## The code-level operation vocabulary -/

/-- Lift a first-order DSL signature to the `Tp`-indexed code vocabulary. -/
inductive OpT (X : TpF → TpF → Type) : Tp → Tp → Type
  | mk {I R : TpF} : X I R → OpT X I.tp R.tp

/-- A code vocabulary extended with a single recursive-call operation `call : σ → ρ` — `σ`/`ρ`
    arbitrary object types (a recursion's state may contain function values). -/
inductive CallOp (Opc : Tp → Tp → Type) (σ ρ : Tp) : Tp → Tp → Type
  | base {I R : Tp} : Opc I R → CallOp Opc σ ρ I R
  | call : CallOp Opc σ ρ σ ρ

/-! ## The AST -/

/-- The dumb, typed imperative AST.  `F as b` names a top-level function `as → b`; `V α` an
    atom.  `X` is the DSL signature (typing `lit` payloads and `scope` witnesses); `Opc` the
    code-level op vocabulary (`OpT X` for ordinary code, its `CallOp` extension inside a `rec_`
    body); `SOp` the scoped vocabulary. -/
inductive Code (X : TpF → TpF → Type) (Opc : Tp → Tp → Type) (SOp : Type → Type)
    (F : List Tp → Tp → Type) (V : Tp → Type) : Tp → Type 1
  | ret   {α} : V α → Code X Opc SOp F V α
  | lit   {α β} : β.denote X → (V β → Code X Opc SOp F V α) → Code X Opc SOp F V α
  | un    {α a b} : Un a b → V a → (V b → Code X Opc SOp F V α) → Code X Opc SOp F V α
  | bin   {α a b c} : Bin a b c → V a → V b → (V c → Code X Opc SOp F V α) →
      Code X Opc SOp F V α
  | pop   {α as b} : POp as b → HList V as → (V b → Code X Opc SOp F V α) →
      Code X Opc SOp F V α
  | vec   {α a n} : Vector (V a) n → (V (.vec a n) → Code X Opc SOp F V α) →
      Code X Opc SOp F V α
  | arr   {α a} : List (V a) → (V (.array a) → Code X Opc SOp F V α) → Code X Opc SOp F V α
  | fold  {α a n} : V a → (V (.fin n) → V a → Code X Opc SOp F V a) →
      (V a → Code X Opc SOp F V α) → Code X Opc SOp F V α
  | vgen  {α a n} : (V (.fin n) → Code X Opc SOp F V a) →
      (V (.vec a n) → Code X Opc SOp F V α) → Code X Opc SOp F V α
  | op    {α} {I R : Tp} : Opc I R → V I → (V R → Code X Opc SOp F V α) →
      Code X Opc SOp F V α
  | ite   {α} : V .bool → Code X Opc SOp F V α → Code X Opc SOp F V α → Code X Opc SOp F V α
  | call  {α as b} : F as b → HList V as → (V b → Code X Opc SOp F V α) →
      Code X Opc SOp F V α
  | scope {α β} : SOp (β.denote X) → Code X Opc SOp F V β → (V β → Code X Opc SOp F V α) →
      Code X Opc SOp F V α
  /-- A **function value**: suspend `body` (an ordinary, potentially effectful code block) as a
      first-class `.fn a b` atom.  Inlining a closure would be a compiler pass — never this
      lowering's business. -/
  | lam   {α a b} : (V a → Code X Opc SOp F V b) → (V (.fn a b) → Code X Opc SOp F V α) →
      Code X Opc SOp F V α
  /-- **Apply** a function value — effectful, like `call`. -/
  | app   {α a b} : V (.fn a b) → V a → (V b → Code X Opc SOp F V α) → Code X Opc SOp F V α

/-- A program: a `def_`/`rec_` telescope around `main`.  Every function definition carries a
    **display name** (the source definition's name, uniquified across monomorphisations) —
    consumed only by the serializer; semantically the binder is the PHOAS `F`-name. -/
inductive Prog (X : TpF → TpF → Type) (SOp : Type → Type)
    (F : List Tp → Tp → Type) (V : Tp → Type) (mainArgs : List Tp) (α : Tp) : Type 1
  | main : (HList V mainArgs → Code X (OpT X) SOp F V α) → Prog X SOp F V mainArgs α
  | def_ {as b} : String → (HList V as → Code X (OpT X) SOp F V b) →
      (F as b → Prog X SOp F V mainArgs α) → Prog X SOp F V mainArgs α
  /-- A **recursive** function definition `arg → res`.  Its body lives over the **call-extended
      vocabulary** `CallOp (OpT X) arg res` — a self-call is the `CallOp.call` operation, whose
      state may freely contain function values — so it may recur in any position; it is denoted
      by `mrec`.  The body is parametric in `F` (it reaches the recursive knot through `call`,
      not through a name).  This node's very existence makes a total `Prog → Free` map
      **impossible to define** (no `mrec` in an inductive monad): the AST can't promise
      termination. -/
  | rec_ {arg res} : String →
      (∀ F', V arg → Code X (CallOp (OpT X) arg res) SOp F' V res) →
      (F [arg] res → Prog X SOp F V mainArgs α) → Prog X SOp F V mainArgs α

/-- A closed program, parametric in the function/value representations. -/
def Closed (X : TpF → TpF → Type) (SOp : Type → Type) (mainArgs : List Tp) (α : Tp) : Type 1 :=
  ∀ F V, Prog X SOp F V mainArgs α

/-! ## Denotation -/

/-- Comp-Kleisli over an arbitrary event signature: a function `as → b` denotes as a
    **subroutine in the interaction-tree domain**. -/
abbrev KCE (X : TpF → TpF → Type) (ε : Type) (br : ε → Type) : List Tp → Tp → Type :=
  fun as b => HList (Tp.denote X) as → CompE ε br (Tp.denote X b)

/-- Comp-Kleisli at the DSL signature. -/
abbrev KC (X : TpF → TpF → Type) : List Tp → Tp → Type :=
  KCE X (Effect X) Effect.arity

/-- Effect-sequencing fold of a tree-valued body over a list of indices — the denotation of a
    bounded loop.  Total structural recursion on the index list: no `tau`s, so a pure body's
    fold is *equal* (not merely `≈`) to the source's fold. -/
def foldComp {ε : Type} {br : ε → Type} {ι X : Type} (body : ι → X → CompE ε br X) :
    List ι → X → CompE ε br X
  | [],      acc => ITree.ret acc
  | i :: is, acc => ITree.bind (body i acc) (fun acc' => foldComp body is acc')

/-- Collect `n` sequential computations into a vector, in index order — the denotation of a
    bounded generator.  Total structural recursion on the count: no `tau`s. -/
def vgenComp {ε : Type} {br : ε → Type} {X : Type} :
    (n : Nat) → (Fin n → CompE ε br X) → CompE ε br (Vector X n)
  | 0,     _    => ITree.ret #v[]
  | n + 1, body =>
      ITree.bind (vgenComp n (fun i => body i.castSucc)) fun v =>
        ITree.bind (body (Fin.last n)) fun x => ITree.ret (v.push x)

/-- An **event injection**: how a code-level op vocabulary emits events of a target signature.
    `agree` is `rfl`-reducing at every concrete op, so the `cast` in the denotation vanishes. -/
structure Inj (X : TpF → TpF → Type) (Opc : Tp → Tp → Type) (ε : Type) (br : ε → Type) :
    Type 1 where
  emit  : {I R : Tp} → Opc I R → Tp.denote X I → ε
  agree : ∀ {I R : Tp} (o : Opc I R) (p : Tp.denote X I), br (emit o p) = Tp.denote X R

/-- The DSL injection: a lifted first-order op emits its packaged event (payload cast along
    `denote_tp` — vanishing at concrete types). -/
def injD (X : TpF → TpF → Type) : Inj X (OpT X) (Effect X) Effect.arity where
  emit  | .mk (I := I) o, p => Effect.mk o (cast (TpF.denote_tp X I) p)
  agree | .mk (R := R) _, _ => (TpF.denote_tp X R).symm

/-- Extend an injection to the call-extended vocabulary, targeting the sum-extended events —
    the self-call event carries the (arbitrary, possibly higher-order) state. -/
def Inj.withCall {X : TpF → TpF → Type} {Opc : Tp → Tp → Type} {ε : Type} {br : ε → Type}
    (inj : Inj X Opc ε br) (σT ρT : Tp) :
    Inj X (CallOp Opc σT ρT) (ε ⊕ Tp.denote X σT) (callBr br (Tp.denote X ρT)) where
  emit
    | .base o, p => Sum.inl (inj.emit o p)
    | .call, p => Sum.inr p
  agree
    | .base o, p => inj.agree o p
    | .call, _ => rfl

/-- **The AST's meaning** — denote a `Code` into the interaction-tree domain, at
    `V := Tp.denote X`, `F := KC X`.  A `call` binds a subroutine's result, a scoped block runs
    inline, a `lam` suspends its body as a Kleisli arrow, an `app` binds the arrow's
    computation; nothing here knows or cares whether the program (or a callee) is recursive. -/
def denoteI {X : TpF → TpF → Type} {Opc : Tp → Tp → Type} {SOp : Type → Type}
    (inj : Inj X Opc (Effect X) Effect.arity) :
    {α : Tp} → Code X Opc SOp (KC X) (Tp.denote X) α → Comp X (Tp.denote X α)
  | _, .ret v      => ret v
  | _, .lit a k    => denoteI inj (k a)
  | _, .un o a k   => denoteI inj (k (Un.denote o a))
  | _, .bin o a b k => denoteI inj (k (Bin.denote o a b))
  | _, .pop o args k => match POp.denote o args with
      | some v => denoteI inj (k v)
      | none   => fail
  | _, .vec elems k => denoteI inj (k elems)
  | _, .arr elems k => denoteI inj (k elems.toArray)
  | _, @Code.fold _ _ _ _ _ _ _ n init body k =>
      ITree.bind (foldComp (fun i acc => denoteI inj (body i acc)) (List.finRange n) init)
        (fun r => denoteI inj (k r))
  | _, @Code.vgen _ _ _ _ _ _ _ n body k =>
      ITree.bind (vgenComp n (fun i => denoteI inj (body i))) (fun r => denoteI inj (k r))
  | _, .op o i k   => vis (inj.emit o i) (fun r => denoteI inj (k (cast (inj.agree o i) r)))
  | _, .ite c t e  => cond c (denoteI inj t) (denoteI inj e)
  | _, .call cf args k => ITree.bind (cf args) (fun r => denoteI inj (k r))
  | _, .scope _ b k => ITree.bind (denoteI inj b) (fun x => denoteI inj (k x))
  | _, .lam body k => denoteI inj (k (fun x => denoteI inj (body x)))
  | _, .app f x k => ITree.bind (f x) (fun r => denoteI inj (k r))

/-- `denoteI` at the DSL injection — the single-argument form the reflector states (★)
    against. -/
abbrev denote {X : TpF → TpF → Type} {SOp : Type → Type} {α : Tp}
    (c : Code X (OpT X) SOp (KC X) (Tp.denote X) α) : Comp X (Tp.denote X α) :=
  denoteI (injD X) c

/-- The call-extended free monad / interaction trees (a recursion body's world): base events
    plus a self-call carrying the (arbitrary, possibly higher-order) state `σ`. -/
abbrev FreeC (X : TpF → TpF → Type) (σ ρ : Type) (SOp : Type → Type) : Type → Type 1 :=
  FreeE (Effect X ⊕ σ) (callBr Effect.arity ρ) SOp

/-- Comp-Kleisli at the call-extended events of a `rec_` body. -/
abbrev KCC (X : TpF → TpF → Type) (σT ρT : Tp) : List Tp → Tp → Type :=
  KCE X (Effect X ⊕ Tp.denote X σT) (callBr Effect.arity (Tp.denote X ρT))

/-- The call-extended tree domain. -/
abbrev CompC (X : TpF → TpF → Type) (σ ρ : Type) (γ : Type) : Type :=
  CompE (Effect X ⊕ σ) (callBr (Effect.arity (Op := X)) ρ) γ

/-- Denote a **`rec_` body** into the call-extended domain (self-calls become call events).
    Same arms as `denote`, except: the target events are extended, and a `lam` **fails** — a
    function value's denotation is a plain Kleisli arrow, so its body may not self-call the
    enclosing recursion (the reflector never emits one there). -/
def denoteC {X : TpF → TpF → Type} {Opc : Tp → Tp → Type} {SOp : Type → Type} {σ ρ : Type}
    (inj : Inj X Opc (Effect X ⊕ σ) (callBr Effect.arity ρ)) :
    {α : Tp} → Code X Opc SOp (KCE X (Effect X ⊕ σ) (callBr Effect.arity ρ)) (Tp.denote X) α →
      CompE (Effect X ⊕ σ) (callBr (Effect.arity (Op := X)) ρ) (Tp.denote X α)
  | _, .ret v      => ret v
  | _, .lit a k    => denoteC inj (k a)
  | _, .un o a k   => denoteC inj (k (Un.denote o a))
  | _, .bin o a b k => denoteC inj (k (Bin.denote o a b))
  | _, .pop o args k => match POp.denote o args with
      | some v => denoteC inj (k v)
      | none   => fail
  | _, .vec elems k => denoteC inj (k elems)
  | _, .arr elems k => denoteC inj (k elems.toArray)
  | _, @Code.fold _ _ _ _ _ _ _ n init body k =>
      ITree.bind (foldComp (fun i acc => denoteC inj (body i acc)) (List.finRange n) init)
        (fun r => denoteC inj (k r))
  | _, @Code.vgen _ _ _ _ _ _ _ n body k =>
      ITree.bind (vgenComp n (fun i => denoteC inj (body i))) (fun r => denoteC inj (k r))
  | _, .op o i k   => vis (inj.emit o i) (fun r => denoteC inj (k (cast (inj.agree o i) r)))
  | _, .ite c t e  => cond c (denoteC inj t) (denoteC inj e)
  | _, .call cf args k => ITree.bind (cf args) (fun r => denoteC inj (k r))
  | _, .scope _ b k => ITree.bind (denoteC inj b) (fun x => denoteC inj (k x))
  | _, .lam _ _ => fail
  | _, .app f x k => ITree.bind (sumL (f x)) (fun r => denoteC inj (k r))

/-- Denote a whole program into `Comp` — **uniformly**: `main` denotes to a function of the
    inputs, a `def_` binds its body's `Comp`-subroutine, and a **`rec_` ties the recursive knot
    with `mrec`** at the sum-extended events. -/
def denoteProg {X : TpF → TpF → Type} {SOp : Type → Type} {mainArgs : List Tp} {α : Tp} :
    Prog X SOp (KC X) (Tp.denote X) mainArgs α → HList (Tp.denote X) mainArgs →
      Comp X (Tp.denote X α)
  | .main body     => fun args => denoteI (injD X) (body args)
  | .def_ _ body k => denoteProg (k (fun a => denoteI (injD X) (body a)))
  | @Prog.rec_ _ _ _ _ _ _ arg res _ body k =>
      denoteProg (k (fun args =>
        mrec (fun s => denoteC ((injD X).withCall arg res)
          (body (KCE X (Effect X ⊕ Tp.denote X arg) (callBr Effect.arity (Tp.denote X res))) s))
          (HList.head args)))

end Freigen
