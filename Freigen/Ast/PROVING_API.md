# AST Proving API

## Purpose

This document specifies the intended correctness interface between:

1. a terminating source program in context-indexed `Free`;
2. the context-indexed AST using an `EffSig`;
3. the single corecursive AST evaluator into `CompM`;
4. macro-generated correctness and termination certificates.

The source and target deliberately use different recursion disciplines:

- the source is an inductive `W` tree wrapped in exact codensity as `Free`;
- source structural or well-founded recursion carries termination evidence;
- reflection drops that recursor or well-foundedness evidence;
- the target evaluator is one productive corecursor exposed through `CompM`;
- the generated certificate recovers semantic equivalence and target
  termination.

There is no source `CompM`, no second logical CPS language, and no
coinductive assumption for recursive source calls.

This document uses signatures close to Lean, but suppresses universe
parameters and routine implicit arguments.

---

## 1. Indices and notation

Effects are families over an explicit context type:

```lean
Γ  : Type
Es : Γ → Type       -- natural source effects
eff : EffSig        -- reflected target effects
```

The source and target use the same context type:

```lean
Γ := eff.Ctx
```

This is intentional. Pulling an effect signature back through `Tp.denote`
changes operation payload representations, not the set of effect contexts.

The important current types are:

```lean
Free  Es γ A
CompM E  γ A

Expr eff Var γ t
Program eff mainCtx inputTp outputTp Var
```

`γ` is an effect context. It is not part of the object-language type:

```lean
Tp
AbiTp
Tp.denote : Tp → Type
```

The polynomial underlying `Free` and `CompM` is indexed by pairs:

```lean
Γ × Type
```

The first component is the current effect context. The second is the current
semantic result type. An operation continuation stays in the enclosing
context; an operation block may move to `blockCtx`.

The target evaluator uses:

```lean
abbrev EvalEff (eff : EffSig) :=
  Eff.Tau ⊕ₑ (Eff.Fail ⊕ₑ eff.denote)
```

`Tau` represents administrative target steps. `Fail` represents malformed
target states such as an invalid function reference. A successful
correctness certificate proves that the latter is unreachable.

---

## 2. Source computations

The existing source type is:

```lean
def Free
    {Γ : Type}
    (E : Γ → Type) [Eff.Spec E]
    (γ : Γ) (A : Type) : Type :=
  ExactCodensity
    (fun A => IxPoly.W (Eff.Step Γ E) (γ, A))
    A
```

Expose the underlying inductive tree at a particular context:

```lean
abbrev RawFree
    {Γ : Type}
    (E : Γ → Type) [Eff.Spec E]
    (γ : Γ) (A : Type) :=
  IxPoly.W (Eff.Step Γ E) (γ, A)

def Free.lower (x : Free E γ A) : RawFree E γ A :=
  ExactCodensity.equiv x
```

The proving layer needs opaque laws:

```lean
Free.lower_pure
Free.lower_bind
Free.lower_op
```

The operation law must preserve both kinds of context:

```lean
Free.op
    (e : E γ)
    (blocks :
      (b : Eff.Spec.blockTag γ e) →
      Eff.Spec.blockInputs γ e b →
      Free E
        (Eff.Spec.blockCtx γ e b)
        (Eff.Spec.blockOutputs γ e b)) :
    Free E γ (Eff.Spec.output γ e)
```

Generated proofs rewrite through these laws. They do not unfold
`ExactCodensity`.

### 2.1 Embedding terminating source trees into `CompM`

Define the structural embedding:

```lean
def RawFree.toCompM :
    RawFree E γ A →
    CompM E γ A

def Free.toCompM (x : Free E γ A) : CompM E γ A :=
  x.lower.toCompM
```

At an operation node it recursively embeds:

- continuations at `(γ, A)`;
- each block at
  `(blockCtx γ e b, blockOutputs γ e b)`.

Required laws are:

```lean
Free.toCompM_pure
Free.toCompM_bind
Free.toCompM_op
```

`RawFree.toCompM` is used to state the public behavioral theorem. The
macro-facing certificate works directly with `Free.lower`, retaining the
source tree's induction principle.

---

## 3. The target evaluator

### 3.1 The corecursor carrier

`Eff.Step` is indexed by `eff.Ctx × Type`, so the evaluator carrier must have
the same index:

```lean
EvalState (eff : EffSig) : eff.Ctx × Type → Type
```

It must not instead have the stale shape:

```lean
-- Wrong:
EvalState eff : Tp → Type
```

There is no inverse from an arbitrary semantic `Type` to `Tp`. States created
from syntax retain their syntactic type witness through indexed constructors:

```lean
inductive EvalState (eff : EffSig) :
    eff.Ctx × Type → Type where

| expr {γ : eff.Ctx} {i o : Tp} :
    ProgramState eff →
    i.denote →
    (i.denote → Expr eff Tp.denote γ o) →
    EvalState eff (γ, o.denote)

-- Further constructors may represent return modes, continuation frames,
-- loops, calls, and copying. They obey the same `(context, result type)`
-- index.
```

This is an internal representation. Generated certificates never construct
or inspect raw evaluator-state constructors.

### 3.2 Public entry states

Expose smart constructors for the states used by certificates.

The main-expression and function-call modes retain the final heap:

```lean
EvalState.mainExpr :
  ProgramState eff →
  Expr eff Tp.denote γ t →
  EvalState eff (γ, ProgramState eff × t.denote)

EvalState.mainCall :
  ProgramState eff →
  FnRef →
  a.denote →
  EvalState eff (γ, ProgramState eff × b.denote)
```

The context `γ` on `mainCall` is the context in which the referenced
definition executes. The heap lookup checks it against the context stored
with the definition.

Effect blocks return exactly their intrinsic flat result:

```lean
EvalState.blockExpr :
  ProgramState eff →
  Expr eff Tp.denote γ t →
  IsAbiTp t →
  EvalState eff (γ, t.denote)
```

These are modes of the same carrier, not separate evaluators.

### 3.3 The one coalgebra

There is one evaluator step function:

```lean
def Expr.denoteCo :
    (i : eff.Ctx × Type) →
    EvalState eff i →
    Eff.Step eff.Ctx (EvalEff eff) (EvalState eff) i
```

The target tree is:

```lean
def EvalState.denote
    (state : EvalState eff (γ, R)) :
    CompM (EvalEff eff) γ R :=
  CompM.corec Expr.denoteCo state
```

The proof interface stays entirely at `CompM`:

```lean
CompM.observe :
  CompM E γ R ≃
    Eff.Step Γ E (fun i => CompM E i.1 i.2) (γ, R)

CompM.roll :
  Eff.Step Γ E (fun i => CompM E i.1 i.2) (γ, R) →
  CompM E γ R

CompM.observe_corec
CompM.observe_roll
CompM.roll_observe
```

The `ITree` representation and exact-codensity equivalence are implementation
details of `CompM`. Proofs do not lower a `CompM` to another representation.
There is no second evaluator and no side-channel `EvalView`.

### 3.4 Context-changing blocks

For an operation `e : eff.denote γ`, the coalgebra produces:

```lean
Eff.Step.op e blocks k
```

where:

```lean
k :
  Eff.Spec.output γ e →
  EvalState eff (γ, R)

blocks :
  (b : Eff.Spec.blockTag γ e) →
  Eff.Spec.blockInputs γ e b →
  EvalState eff
    (Eff.Spec.blockCtx γ e b,
     Eff.Spec.blockOutputs γ e b)
```

This is the central reason every logical relation over computations must be
context-indexed. A proof can enter a block in a different context and then
return to the enclosing continuation context.

### 3.5 Why block states do not return their heaps

An effect block must return exactly:

```lean
Eff.Spec.blockOutputs γ e b
```

not a heap pair. The AST requires all operation and block boundary values to
be `AbiTp`, and `AbiTp` excludes functions transitively. Consequently:

- a block cannot return a newly allocated `FnRef`;
- an operation cannot hide one in another ABI value;
- block-local closure allocation cannot become observable after the block;
- persistent closure-heap updates do not need to be merged into the
  enclosing continuation.

The block state still carries its heap while it executes. Only the final
block-local heap is discarded at the intrinsic block boundary.

---

## 4. Target termination

A `RawFree E γ A` is a well-founded effect tree. It may return, fail, or
perform an operation with arbitrarily many children, but it has no infinite
path.

Target evaluator states have heterogeneous contexts and result types, so pack
both indices:

```lean
structure PackedEvalState (eff : EffSig) where
  context : eff.Ctx
  result : Type
  state : EvalState eff (context, result)
```

Define the immediate-child relation from one `denoteCo` observation:

```lean
inductive EvalChild :
    PackedEvalState eff →
    PackedEvalState eff →
    Prop

| continuation
    {γ R}
    {parent : EvalState eff (γ, R)}
    {e blocks k}
    (h :
      Expr.denoteCo (γ, R) parent =
        Eff.Step.op e blocks k)
    (output : Eff.Spec.output γ e) :
    EvalChild
      ⟨γ, R, k output⟩
      ⟨γ, R, parent⟩

| block
    {γ R}
    {parent : EvalState eff (γ, R)}
    {e blocks k}
    (h :
      Expr.denoteCo (γ, R) parent =
        Eff.Step.op e blocks k)
    (b : Eff.Spec.blockTag γ e)
    (input : Eff.Spec.blockInputs γ e b) :
    EvalChild
      ⟨Eff.Spec.blockCtx γ e b,
       Eff.Spec.blockOutputs γ e b,
       blocks b input⟩
      ⟨γ, R, parent⟩
```

Then:

```lean
def EvalState.WellFounded
    (state : EvalState eff (γ, R)) : Prop :=
  Acc EvalChild ⟨γ, R, state⟩
```

`Tau` is represented as an ordinary effect node with one continuation child,
so the relation sees it automatically. `Fail` has no children.

Expose the analogous computation predicate and the corecursor preservation
theorem:

```lean
CompM.WellFounded :
  CompM E γ A → Prop

EvalState.wellFounded_denote :
  state.WellFounded →
  (EvalState.denote state).WellFounded
```

Do not define termination merely as Eutt to some `Free` tree unless the
chosen Eutt is already proved divergence-reflecting in the needed direction.
The central certificate below proves accessibility directly.

### 4.1 Reifying a terminating target

Because `Acc` supports recursion into `Type`, the library can define:

```lean
EvalState.reify :
  (state : EvalState eff (γ, R)) →
  state.WellFounded →
  RawFree (EvalEff eff) γ R
```

and prove that `reify.toCompM` is Eutt to the same target `CompM`.

The accessibility proof is erased. Computing `reify` observes the evaluator
again. A consumer that requires a materialized target `RawFree` without
replay must retain it as data; ordinary verification only needs the erased
theorem.

---

## 5. Values and closure heaps

Target values are:

```lean
abbrev TgtVal : Tp → Type := Tp.denote
```

In particular:

```lean
TgtVal (.fn a b) = FnRef
```

There is no global source interpretation of `Tp`. Each reflected value proof
names the actual Lean source type:

```lean
structure ValueRel
    (eff : EffSig)
    (A : Type)
    (t : Tp) where

  holds :
    ProgramState eff →
    A →
    t.denote →
    Prop

  mono :
    ∀ {h h' source target},
      HeapExtends h h' →
      holds h source target →
      holds h' source target
```

Standard constructors include:

```lean
ValueRel.eqUInt32
ValueRel.eqBool
ValueRel.prod
ValueRel.sum
ValueRel.array
ValueRel.fn
```

`Tp` remains context-free. Computation certificates, not value types, carry
the context in which a value-producing computation runs.

### 5.1 Kripke heap worlds

Generated terms must not inspect the concrete hash-map representation. Expose:

```lean
HeapExtends :
  ProgramState eff →
  ProgramState eff →
  Prop

HeapExtends.refl
HeapExtends.trans

ProgramState.alloc_extends :
  let (h', _) := h.alloc body
  HeapExtends h h'

ProgramState.lookup_of_extends :
  HeapExtends h h' →
  -- Every successful lookup in h remains the same lookup in h'.
  ...
```

`ValueRel` is Kripke because the heap is a world and `mono` says the relation
survives every future allocation. This keeps definition composition linear:
allocating a definition does not rebuild every older function proof.

---

## 6. Context-preserving effect transport

The source uses a natural effect family:

```lean
Es : eff.Ctx → Type
```

The reflected AST uses:

```lean
eff.denote : eff.Ctx → Type
```

Both families have the same root contexts, but corresponding block tags can
select contexts only propositionally equal. The transport must record this.

```lean
structure EffPullback
    (Es Et : Γ → Type)
    [Eff.Spec Es] [Eff.Spec Et] where

  forget :
    {γ : Γ} →
    Et γ →
    Es γ

  outputIso :
    ∀ {γ} (et : Et γ),
      Eff.Spec.output γ et ≃
      Eff.Spec.output γ (forget et)

  blockIso :
    ∀ {γ} (et : Et γ),
      Eff.Spec.blockTag γ et ≃
      Eff.Spec.blockTag γ (forget et)

  blockCtx_eq :
    ∀ {γ} (et : Et γ) (bt : Eff.Spec.blockTag γ et),
      Eff.Spec.blockCtx γ et bt =
      Eff.Spec.blockCtx γ (forget et) (blockIso et bt)

  blockInputIso :
    ∀ {γ} (et : Et γ) (bt : Eff.Spec.blockTag γ et),
      Eff.Spec.blockInputs γ et bt ≃
      Eff.Spec.blockInputs γ (forget et) (blockIso et bt)

  blockOutputIso :
    ∀ {γ} (et : Et γ) (bt : Eff.Spec.blockTag γ et),
      Eff.Spec.blockOutputs γ et bt ≃
      Eff.Spec.blockOutputs γ (forget et) (blockIso et bt)
```

The exact orientation of the equivalences is an API choice. Pick one and
provide named forward/backward helpers. Generated proofs must never manipulate
the casts induced by `blockCtx_eq` directly.

Useful derived helpers are:

```lean
P.sourceOutput
P.targetOutput
P.sourceBlockTag
P.targetBlockTag
P.sourceBlockInput
P.targetBlockInput
P.sourceBlockOutput
P.targetBlockOutput
P.castSourceBlockState
P.castTargetBlockState
```

For the AST, the principal transport is:

```lean
P : EffPullback Es eff.denote
```

The target evaluator actually emits `EvalEff eff`. User operations are
injected into that stack. `Tau` is handled silently by the behavioral
relation. `Fail` has no successful certificate rule.

### 6.1 Supported source operations

The target-to-source map is total. Compilation in the other direction is
partial:

```lean
structure EffPullback.Supported
    (P : EffPullback Es Et)
    {γ : Γ}
    (source : Es γ) where

  target : Et γ
  forget_eq : P.forget target = source
```

The reflector registry supplies `Supported` for every source operation it
emits.

Use equivalences only for the genuinely equivalent fragment. A
runtime-partial representation conversion needs a precondition or a
directional simulation theorem.

---

## 7. The central inductive certificate

The certificate relates:

- a source `RawFree` at context `γ`;
- a target evaluator state at the same context `γ`;
- possibly different source and target result types.

```lean
inductive FreeEval
    (P : EffPullback Es eff.denote) :
    {γ : eff.Ctx} →
    {A R : Type} →
    (Done : A → R → Prop) →
    RawFree Es γ A →
    EvalState eff (γ, R) →
    Prop
```

The shared root context is not cosmetic. It is what permits corresponding
operations to be compared. Block premises move both computations to the
transported block context.

### 7.1 Return rule

```lean
| ret
    (hsource :
      source.observe =
        Eff.Step.ret sourceResult)
    (htarget :
      Expr.denoteCo (γ, R) target =
        Eff.Step.ret targetResult)
    (hDone :
      Done sourceResult targetResult) :
    FreeEval P Done source target
```

### 7.2 Matched user-operation rule

Schematically:

```lean
| op
    {γ : eff.Ctx}
    (et : eff.denote γ)

    (sourceBlocks :
      (sb : Eff.Spec.blockTag γ (P.forget et)) →
      Eff.Spec.blockInputs γ (P.forget et) sb →
      RawFree Es
        (Eff.Spec.blockCtx γ (P.forget et) sb)
        (Eff.Spec.blockOutputs γ (P.forget et) sb))

    (sourceK :
      Eff.Spec.output γ (P.forget et) →
      RawFree Es γ A)

    (targetBlocks :
      (tb : Eff.Spec.blockTag γ et) →
      Eff.Spec.blockInputs γ et tb →
      EvalState eff
        (Eff.Spec.blockCtx γ et tb,
         Eff.Spec.blockOutputs γ et tb))

    (targetK :
      Eff.Spec.output γ et →
      EvalState eff (γ, R))

    (hsource : source.observe = ...)
    (htarget :
      Expr.denoteCo (γ, R) target =
        Eff.Step.op
          (injectUserOp et)
          (injectUserBlocks targetBlocks)
          targetK)

    (continuations :
      ∀ targetOutput,
        FreeEval P Done
          (sourceK (P.sourceOutput et targetOutput))
          (targetK targetOutput))

    (blocks :
      ∀ targetTag targetInput,
        FreeEval P
          (P.blockResultRel et targetTag)
          (P.sourceBlock sourceBlocks targetTag targetInput)
          (targetBlocks targetTag targetInput)) :

    FreeEval P Done source target
```

`P.sourceBlock` performs the hidden `blockCtx_eq` cast. The recursive block
certificate is therefore indexed by the target block context:

```lean
Eff.Spec.blockCtx γ et targetTag
```

No generated proof sees the equality cast.

### 7.3 Silent target-step rule

```lean
| targetTau
    (htarget :
      Expr.denoteCo (γ, R) target =
        Eff.Step.tau targetNext)
    (next :
      FreeEval P Done source targetNext) :
    FreeEval P Done source target
```

An analogous `sourceTau` rule is useful when `Es` itself contains a designated
silent `Tau` effect.

These constructors are inductive. A certificate may skip finitely many
administrative steps but cannot certify an infinite target-only `Tau` loop.

There is deliberately no target-`Fail` rule. Reaching invalid function lookup
or another evaluator failure makes `FreeEval` unprovable.

### 7.4 Root and block result relations

For a main expression, the terminal relation sees the final heap:

```lean
fun sourceResult (finalHeap, targetResult) =>
  HeapExtends initialHeap finalHeap ∧
  V.holds finalHeap sourceResult targetResult
```

For a block, the terminal relation is the flat result relation induced by
`P.blockOutputIso`.

The same `FreeEval` family handles both because it is polymorphic in `A`, `R`,
and `Done` at every context.

---

## 8. Derived behavior and termination

### 8.1 Context-indexed heterogeneous Eutt

The public behavioral relation compares computations at a shared context:

```lean
Eutt
    (P : EffPullback Es eff.denote)
    (RR : A → R → Prop)
    (source : CompM Es γ A)
    (target : CompM (EvalEff eff) γ R) :
    Prop
```

Internally its coinductive relation is indexed over context/result pairs so
that matched block children may move to another context.

Prove once:

```lean
FreeEval.toEutt
    (hDone :
      ∀ sourceResult targetResult,
        Done sourceResult targetResult →
        RR sourceResult targetResult)
    (h : FreeEval P Done source target) :
    Eutt P RR
      source.toCompM
      target.denote
```

This library proof uses `CompM.observe` and coinduction. Macro-generated
proofs only build the inductive `FreeEval` certificate.

### 8.2 Target accessibility

Also prove:

```lean
FreeEval.targetWellFounded :
  FreeEval P Done source target →
  EvalState.WellFounded target
```

This is ordinary induction over `FreeEval`. It proves target termination
without relying on a subtle divergence-reflection property of Eutt.

Thus one certificate has two projections:

```text
                         ┌──► context-indexed heterogeneous Eutt
FreeEval certificate ───┤
                         └──► target accessibility
```

---

## 9. Expression certificates

At context `γ`, for:

```lean
source : Free Es γ A
target : Expr eff Tp.denote γ t
```

define:

```lean
def ExprCertAt
    (P : EffPullback Es eff.denote)
    (initial : ProgramState eff)
    (V : ValueRel eff A t)
    (source : Free Es γ A)
    (target : Expr eff Tp.denote γ t) : Prop :=

  FreeEval P
    (fun sourceValue (finalHeap, targetValue) =>
      HeapExtends initial finalHeap ∧
      V.holds finalHeap sourceValue targetValue)
    source.lower
    (EvalState.mainExpr initial target)
```

There is no `source.run pure` and no coinductive source computation in this
macro-facing judgment.

### 9.1 Function relations

Object-language function types do not contain contexts:

```lean
.fn a b
```

The relation for a particular closure does contain its execution context:

```lean
def ValueRel.fn
    (P : EffPullback Es eff.denote)
    (callCtx : eff.Ctx)
    (sourceCall : F → A → Free Es callCtx B)
    (RA : ValueRel eff A a)
    (RB : ValueRel eff B b) :
    ValueRel eff F (.fn a b)
```

Its `holds` field is:

```lean
fun heap sourceFn targetRef =>
  ∀ future,
    HeapExtends heap future →
    ∀ sourceArg targetArg,
      RA.holds future sourceArg targetArg →
      FreeEval P
        (fun sourceResult (finalHeap, targetResult) =>
          HeapExtends future finalHeap ∧
          RB.holds finalHeap sourceResult targetResult)
        (sourceCall sourceFn sourceArg).lower
        (EvalState.mainCall
          (γ := callCtx)
          future targetRef targetArg)
```

The context belongs to the computation relation and closure-heap entry, not
to `Tp.fn`. Heap lookup proves that `targetRef` names a definition at
`callCtx`.

### 9.2 Macro-facing syntax rules

Provide opaque rules:

```lean
ExprCert.ret
ExprCert.lit
ExprCert.builtin
ExprCert.lam
ExprCert.app
ExprCert.ite
ExprCert.loop
ExprCert.op
```

All ordinary expression rules preserve the current context `γ`.

A representative application rule is:

```lean
ExprCert.app
    (hf :
      (ValueRel.fn P γ sourceCall RA RB).holds
        heap sourceFn targetRef)
    (hx :
      RA.holds heap sourceArg targetArg)
    (hk :
      ∀ future sourceResult targetResult,
        HeapExtends heap future →
        RB.holds future sourceResult targetResult →
        ExprCertAt P future RC
          (sourceK sourceResult)
          (targetK targetResult)) :
    ExprCertAt P heap RC
      (sourceCall sourceFn sourceArg >>= sourceK)
      (.app targetRef targetArg targetK)
```

All computations here run at the same `γ`.

A representative lambda rule is:

```lean
ExprCert.lam
    (body :
      ∀ future sourceArg targetArg,
        HeapExtends heap future →
        RA.holds future sourceArg targetArg →
        ExprCertAt P future RB
          (sourceCall sourceFn sourceArg)
          (targetBody targetArg))
    (k :
      ∀ future targetRef,
        HeapExtends heap future →
        (ValueRel.fn P γ sourceCall RA RB).holds
          future sourceFn targetRef →
        ExprCertAt P future RC
          (sourceK sourceFn)
          (targetK targetRef)) :
    ExprCertAt P heap RC
      (sourceK sourceFn)
      (.lam targetBody targetK)
```

The source substitutes a Lean function. The target allocates a `FnRef`.
`HeapExtends` connects the new heap to the old one.

### 9.3 The operation rule

For:

```lean
sourceOp : Es γ
targetOp : eff.denote γ
```

`ExprCert.op` accepts:

- `P.Supported sourceOp`;
- the corresponding target request;
- a certificate for every output continuation at the enclosing context `γ`;
- a certificate for every block at
  `eff.blockCtx γ targetOp blockTag`;
- the transported flat result relation for each block.

The rule hides:

- injection of `targetOp` into `EvalEff eff`;
- output and block payload equivalences;
- the equality cast between source and target block contexts;
- evaluator continuation-frame manipulation.

This is the only expression rule that changes context, and only its block
premises do so.

---

## 10. Definitions and recursion

Each target definition has its own execution context:

```lean
targetBody :
  FnRef →
  a.denote →
  Expr eff Tp.denote defCtx b
```

Its source counterpart has:

```lean
sourceCall :
  F →
  A →
  Free Es defCtx B
```

The definition certificate installs a
`ValueRel.fn P defCtx sourceCall RA RB`.

### 10.1 Local recursive-call hypothesis

Fix the newly allocated target reference `selfRef`:

```lean
def FunctionCallCorrect (sourceArg : A) : Prop :=
  ∀ future targetArg,
    HeapExtends installedHeap future →
    RA.holds future sourceArg targetArg →
    FreeEval P
      (fun sourceResult (finalHeap, targetResult) =>
        HeapExtends future finalHeap ∧
        RB.holds finalHeap sourceResult targetResult)
      (sourceCall sourceDef sourceArg).lower
      (EvalState.mainCall
        (γ := defCtx)
        future selfRef targetArg)
```

For well-founded recursion, checking the body at `x` receives:

```lean
ih :
  ∀ y, Smaller y x → FunctionCallCorrect y
```

A recursive target call is still ordinary `.app`. `RecExprCert.app`
specializes `ih` to the current future heap and related target argument.

The quantification over future heaps is essential: recursive calls may occur
after local closure allocation.

### 10.2 Well-founded closing rule

```lean
DefCert.wf
    (wf : WellFounded Smaller)
    (source_unfold :
      ∀ x,
        sourceCall sourceDef x =
        sourceBody sourceDef x)
    (body :
      ∀ x,
        (∀ y, Smaller y x → FunctionCallCorrect y) →
        BodyCorrect x) :
    InstalledFunctionCorrect
      (ctx := defCtx)
      ...
```

Its implementation is `wf.induction`. At each argument it:

1. unfolds the source function once;
2. unfolds target heap lookup and call once;
3. applies the body certificate;
4. discharges recursive calls from the induction hypothesis.

Target call `Tau`s are administrative steps consumed by `FreeEval`. They do
not justify recursion.

### 10.3 Structural recursors

Provide:

```lean
DefCert.structural
DefCert.natBrecOn
```

The `Nat.brecOn` rule consumes:

- the source unfolding theorem;
- certificates for the generated base/body functionals;
- recursive-call certificates supplied by the recursor induction hypothesis.

The reflector recognizes the recursor from Lean metadata. It does not
normalize or unroll recursive calls.

Nonrecursive definitions are the degenerate case:

```lean
DefCert.nonrecursive
```

---

## 11. Program certificates

A program has an explicit main context:

```lean
target :
  Program eff mainCtx inputTp outputTp Tp.denote

source :
  SourceInput →
  Free Es mainCtx SourceOutput
```

Individual definitions inside `target` may use other contexts. Each
`ProgramCert.define` premise records the definition's own `defCtx`.

```lean
def ProgramCertAt
    (P : EffPullback Es eff.denote)
    (heap : ProgramState eff)
    (source :
      SourceInput →
      Free Es mainCtx SourceOutput)
    (target :
      Program eff mainCtx inputTp outputTp Tp.denote) :
    Prop :=
  ...
```

Assembly rules:

```lean
ProgramCert.main

ProgramCert.define
    (definition :
      InstalledFunctionCorrect
        (ctx := defCtx)
        ...)
    (rest :
      ∀ heap' ref,
        HeapExtends heap heap' →
        FunctionRelated
          (ctx := defCtx)
          heap' sourceDef ref →
        ProgramCertAt P heap' sourceMain (targetRest ref)) :
    ProgramCertAt P heap sourceMain
      (.define targetBody targetRest)
```

`FunctionRelated` abbreviates the `holds` field of the appropriate
context-indexed `ValueRel.fn`.

The continuation of `ProgramCert.define` represents the static remainder of
the definition list. It is not a computation continuation.

### 11.1 Public denotation

The program denotation runs at `mainCtx`:

```lean
Program.denote :
  Program eff mainCtx inputTp outputTp Tp.denote →
  inputTp.val.denote →
  CompM
    (EvalEff eff)
    mainCtx
    (ProgramState eff × outputTp.val.denote)
```

For value-only clients:

```lean
Program.denoteValue target input :=
  (Program.denote target input).map Prod.snd
```

### 11.2 Public correctness

```lean
def OutputRel
    (sourceOutput : SourceOutput)
    (targetOutput :
      ProgramState eff × outputTp.val.denote) : Prop :=
  OutputValueRel.holds
    targetOutput.1
    sourceOutput
    targetOutput.2
```

```lean
def ProgramCorrect
    (P : EffPullback Es eff.denote)
    (source :
      SourceInput →
      Free Es mainCtx SourceOutput)
    (target :
      Program eff mainCtx inputTp outputTp Tp.denote) :
    Prop :=

  ∀ sourceInput targetInput,
    InputRel.holds
      (ProgramState.empty eff)
      sourceInput
      targetInput →
    Eutt P OutputRel
      (Free.toCompM (source sourceInput))
      (Program.denote target targetInput)
```

Both computations are rooted at `mainCtx`. Their block children may move
through other contexts according to the transported effect signatures.

A value-only theorem follows by relational `map` congruence and should not be
reproved by the macro.

### 11.3 Public termination

```lean
def ProgramTerminates
    (source :
      SourceInput →
      Free Es mainCtx SourceOutput)
    (target :
      Program eff mainCtx inputTp outputTp Tp.denote) :
    Prop :=

  ∀ sourceInput targetInput,
    InputRel.holds
      (ProgramState.empty eff)
      sourceInput
      targetInput →
    CompM.WellFounded
      (Program.denote target targetInput)
```

Keep the source visible in the theorem even if it could technically be erased
from the final proposition: it records where the accessibility proof came
from.

### 11.4 Combined result

```lean
structure ProgramVerified ... : Prop where
  correct :
    ProgramCorrect P source target
  terminates :
    ProgramTerminates source target
```

Both fields are projections of one `ProgramCertAt`. The macro does not build
parallel correctness and termination proofs.

---

## 12. Generated proof shape

A recursive definition at `fooCtx`, followed by a definition at `barCtx` and
a main expression at `mainCtx`, should elaborate approximately as:

```lean
exact ProgramCert.define
  (DefCert.wf
    (ctx := fooCtx)
    foo_wf
    foo_unfold
    (fun x ih =>
      ExprCert.ite
        ...
        (RecExprCert.app (ih y hyx) ...)
        ...))
  (fun heap₁ fooRef fooRelated hExt₁ =>

    ProgramCert.define
      (DefCert.nonrecursive
        (ctx := barCtx)
        (ExprCert.app fooRelated ...))
      (fun heap₂ barRef barRelated hExt₂ =>

        ProgramCert.main
          (ctx := mainCtx)
          (ExprCert.op
            supportedPrint
            ...
            (ExprCert.app barRelated ...))))
```

The Meta-level environment stores:

```text
source declaration
  ↦ definition context
  ↦ target FnRef local
  ↦ function-relation proof local
  ↦ argument/result ValueRel terms
  ↦ sourceCall term at that context
  ↦ source unfolding/recursor theorem
```

There is no reified logical context and no eager weakening of all prior
definitions.

---

## 13. Complexity requirements

1. `Free.lower` is shared once per source expression.
2. The macro never reduces the resulting `W` tree.
3. Every `ExprCert`, `DefCert`, and `ProgramCert` rule is opaque.
4. Each emitted AST node corresponds to one certificate theorem application.
5. Recursive source functions use their existing structural or
   well-founded induction principle.
6. Each definition certificate is constructed once and referenced at calls.
7. Older closure proofs survive allocation through `HeapExtends`.
8. The concrete hash-map heap is absent from generated proof terms.
9. Effect-transport witnesses are emitted once per operation or shared by a
   local `let`.
10. Block-context equality casts occur only inside transport helpers and
    opaque certificate rules.
11. Source bodies, target bodies, and relation terms are shared with
    `let`/`have`.
12. Bind reassociation and evaluator-stack manipulation occur only in library
    theorems.
13. Eutt and target accessibility are projections of one certificate.
14. Regression tests cover:
    - long definition chains;
    - repeated early calls;
    - definitions in different contexts;
    - effects whose blocks change context;
    - structurally recursive functions at large symbolic inputs.

The intended generated term size is:

```text
O(AST nodes + call sites + definitions)
```

It must not depend on concrete recursive unfolding depth.

---

## 14. Induction and coinduction boundary

Induction is used for:

1. the source `W` tree;
2. `FreeEval`;
3. source structural or well-founded recursion;
4. target accessibility.

Corecursion or coinduction is used only for:

1. constructing the target `CompM` from the
   `(eff.Ctx × Type)`-indexed evaluator state;
2. defining generic context-indexed heterogeneous Eutt;
3. proving `FreeEval.toEutt`.

In particular:

- recursive definitions are not closed by coinduction;
- target administrative `Tau`s are not termination guards;
- generated certificates never construct coinduction seeds;
- block context changes are handled by indices and `EffPullback`;
- evaluator continuation frames remain internal.

---

## 15. Implementation order

1. Finish the `(eff.Ctx × Type)`-indexed `EvalState`.
2. Implement `Expr.denoteCo` once and define its `CompM.corec`.
3. Add `Free.lower`, `RawFree.toCompM`, and their laws.
4. Define public evaluator entry-state constructors.
5. Define `HeapExtends` and allocation/lookup stability.
6. Define context-preserving `EffPullback`, including `blockCtx_eq`.
7. Add cast-free derived block transport helpers.
8. Define context-indexed heterogeneous Eutt.
9. Define inductive, context-indexed `FreeEval`.
10. Prove `FreeEval.toEutt` and `FreeEval.targetWellFounded`.
11. Define `ValueRel`, including context-indexed function relations.
12. Prove the opaque `ExprCert.*` rules.
13. Prove `DefCert.nonrecursive`, `DefCert.wf`, and structural specializations.
14. Define `ProgramCert.define/main`, `ProgramCorrect`,
    `ProgramTerminates`, and `ProgramVerified`.
15. Build the reflector using only the opaque certificate API.
16. Add proof-size, elaboration-time, context-transition, Eutt, and
    termination regression tests.

---

## 16. Decisions to preserve

- `Tp` and `AbiTp` are not parameterized by the effect context.
- Source computations are `Free Es γ A`.
- Target computations are `CompM (EvalEff eff) γ A`.
- `CompM.observe`/`roll` are the complete proof-facing coalgebra API; `ITree`
  and exact codensity remain implementation details.
- Source and target effect families share `eff.Ctx`.
- Operation continuations stay in the enclosing context.
- Operation blocks run in their intrinsic `blockCtx`.
- The corecursor carrier is indexed by `eff.Ctx × Type`.
- There is one target evaluator and no proof-only evaluator.
- Main and call modes expose the final heap.
- Block modes return only their intrinsic ABI result.
- The central source-to-target certificate is inductive.
- Correctness and target termination come from the same certificate.
- Target functions are `FnRef`; source functions remain Lean values.
- A function's execution context lives in its heap entry and function
  relation, not in `Tp.fn`.
- Closure validity is monotone under heap extension.
- Natural and reflected user effects are connected by a context-preserving
  pullback.
- Block-context casts are hidden behind the pullback API.
- Runtime-partial encodings use directional simulations rather than claiming
  Eutt equivalence.
- Recursive target calls are ordinary applications.
- Source recursion is justified by its original structural or
  well-foundedness theorem.
- The public behavioral theorem is context-indexed heterogeneous Eutt.
- The public termination theorem is explicit.
- Generated certificate size is linear in the emitted program.
