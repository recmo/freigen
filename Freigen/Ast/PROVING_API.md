# AST Proving API

## Purpose

This document specifies the intended correctness interface between:

1. a terminating source program in `Free`;
2. the AST using the `Tp`-pulled-back effect signature;
3. the corecursive AST evaluator, whose result is represented by `CompE`/`ITree`;
4. a macro-generated correctness and termination certificate.

The source and target deliberately use different recursion disciplines:

- the source is an inductive `W` tree, wrapped in exact codensity as `Free`;
- source structural or well-founded recursion carries a termination proof;
- the compiler drops that recursor/proof structure;
- the target evaluator is one productive corecursor into `ITree`;
- the generated certificate recovers both semantic equivalence and target
  termination.

There is no source `CompM`, no logical CPS computation type, and no
coinductive assumption for recursive source calls.

## Executive summary

```text
source : Free Es A
          │ Free.lower
          ▼
source : W (Eff.Step Es) A
          │
          │ inductive FreeEval certificate
          ▼
target evaluator state ────────────────► target ITree
          │                                  │
          ├── target is well-founded         │
          │                                  │
          └── heterogeneous Eutt ◄───────────┘
                against Free.toITree source
```

The central judgment is therefore not a coinductive relation between two
arbitrary `ITree`s. It is an inductive relation between:

- the well-founded source `W` tree; and
- a target evaluator state.

That judgment may consume finitely many silent target steps before matching a
source node. Its induction principle is exactly the resource needed to prove
that the erased target has no infinite execution path.

The main components are:

- `Free.lower` and `W.toITree`;
- `EffPullback`, relating the natural and pulled-back effects;
- `HeapExtends` and heap-indexed `ValueRel`;
- `FreeEval`, the inductive source-to-machine certificate;
- `ExprCert.*`, syntax-directed construction rules;
- `DefCert.structural` and `DefCert.wf`, which reuse source recursion proofs;
- `ProgramCert.define/main`, which assemble a whole program;
- public Eutt and termination consequences.

The macro never unfolds the evaluator, heap implementation, Eutt, or the
definition of `FreeEval`.

---

## 1. Source computations

The existing source type is:

```lean
def Free (E : Type u) [Eff.Spec E] (A : Type) : Type _ :=
  ExactCodensity (IxPoly.W (Eff.Step E)) A
```

Expose the underlying inductive tree:

```lean
abbrev RawFree (E : Type u) [Eff.Spec E] (A : Type) :=
  IxPoly.W (Eff.Step E) A

def Free.lower (x : Free E A) : RawFree E A :=
  ExactCodensity.equiv x
```

The exact-codensity law gives:

```lean
Free.lower_pure
Free.lower_bind
Free.lower_op
```

These are the only facts about `ExactCodensity` needed by the proving layer.
Generated proofs should rewrite through these opaque API theorems, not unfold
the codensity representation.

### 1.1 Embedding a terminating tree into `ITree`

Define the canonical structural embedding:

```lean
def RawFree.toITree :
    RawFree E A →
    ITree E A
```

It maps one `W` node to the corresponding `ITree` node and recursively embeds
every continuation and block child. Then:

```lean
def Free.toITree (x : Free E A) : ITree E A :=
  x.lower.toITree
```

Required laws include:

```lean
Free.toITree_pure
Free.toITree_bind
Free.toITree_op
```

`RawFree.toITree` is used only to state the public extensional theorem. The
macro-facing proof works directly with `Free.lower x`, preserving the source
tree's induction principle.

---

## 2. What “termination” means

A `RawFree E A` is a well-founded effect tree. It can:

- return;
- fail;
- perform an operation and continue;
- expose infinitely many possible children at one operation.

It cannot contain an infinite path. Thus “termination” here means
well-foundedness of every continuation and block path, not “returns
successfully”. It is also termination of the computation structure relative
to atomic effects; a separately supplied effect interpreter may itself
diverge.

Operation blocks may have result types different from the enclosing
computation, so first pack a state with its result index:

```lean
universe v

structure PackedEvalState (eff : EffSig) where
  Result : Type v
  state : EvalState eff Result
```

Define the immediate-child relation:

```lean
inductive EvalChild :
    PackedEvalState eff →
    PackedEvalState eff →
    Prop where

  | continuation
      {R}
      {parent : EvalState eff R}
      {e : Et}
      {input blocks k}
      (hstep :
        evalCo R parent =
          Eff.Step.op e input blocks k)
      (output : Eff.Spec.output e) :
      EvalChild
        ⟨R, k output⟩
        ⟨R, parent⟩

  | block
      {R}
      {parent : EvalState eff R}
      {e : Et}
      {input blocks k}
      (hstep :
        evalCo R parent =
          Eff.Step.op e input blocks k)
      (tag : Eff.Spec.blockTag e)
      (blockInput : Eff.Spec.blockInputs e tag) :
      EvalChild
        ⟨Eff.Spec.blockOutputs e tag,
          blocks tag blockInput⟩
        ⟨R, parent⟩
```

`EvalChild child parent` means that `child` is one of the ordinary
continuation or block states exposed by one `evalCo` step. Then define:

```lean
def EvalState.WellFounded
    (state : EvalState eff R) : Prop :=
  Acc EvalChild ⟨R, state⟩
```

The child relation sees:

- no children under a return or terminal failure;
- one child under a silent step;
- every ordinary continuation and block child under an operation.

An analogous public predicate may be exposed for `ITree`:

```lean
def ITree.WellFounded (t : ITree E A) : Prop := ...
```

with:

```lean
EvalState.wellFounded_evalTree :
  state.WellFounded →
  (evalTree state).WellFounded
```

Do not define termination merely as “is Eutt to some `Free` tree” unless the
chosen Eutt is already proved divergence-reflecting in the required direction.
The inductive `FreeEval` certificate below proves well-foundedness directly.

### 2.1 Proof versus reconstructible data

`FreeEval`, `EvalState.WellFounded`, and Eutt live in `Prop`, so their proofs
are erased. `Acc` is nevertheless specifically designed to justify
well-founded definitions, including definitions returning data. Consequently
the library can define:

```lean
EvalState.reify :
  (state : EvalState eff R) →
  state.WellFounded →
  RawFree Et R
```

by accessibility recursion, and prove that `reify` denotes the same effect
tree as `evalTree state`.

The proof is erased; computing `reify` observes the evaluator state again. If
a consumer instead needs a materialized target `RawFree` without replaying the
evaluator, compilation must retain that data or a `Type`-valued certificate.
For ordinary verification, the erased accessibility theorem is the intended
result.

---

## 3. Source and target values

Target values use the AST representation:

```lean
abbrev TgtVal : Tp → Type := Tp.denote
```

In particular:

```lean
TgtVal (.fn a b) = FnRef
```

There is no global source denotation of `Tp`. Each proof carries the actual
source Lean type and its relation to the reflected target type:

```lean
structure ValueRel
    (eff : EffSig)
    (A : Type ua)
    (t : Tp) where

  holds :
    ProgramState eff →
    A →
    TgtVal t →
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

The macro may register additional relations without extending `Tp` or defining
a recursive source value universe.

---

## 4. Closure heaps are Kripke worlds

The concrete heap representation must not occur in generated proof terms.
Expose:

```lean
def HeapExtends
    (old new : ProgramState eff) : Prop
```

meaning that every closure valid in `old` remains valid, with the same
signature and body, in `new`.

Required laws:

```lean
HeapExtends.refl
HeapExtends.trans

ProgramState.alloc_extends :
  let (h', _) := h.alloc body
  HeapExtends h h'

ProgramState.lookup_of_extends :
  HeapExtends h h' →
  -- Successful old lookups remain identical.
  ...
```

`ValueRel.holds h source target` is called Kripke because `h` is a world and
the relation remains true in every future world:

```lean
V.mono : HeapExtends h h' → V.holds h x y → V.holds h' x y
```

This makes definition composition linear. Installing a definition does not
rebuild the correctness proof for every older closure.

---

## 5. Pulled-back effects

The source uses its natural signature, while the target uses the `Tp`-encoded
signature. Relate them by:

```lean
structure EffPullback
    (Es : Type us) [Eff.Spec Es]
    (Et : Type ut) [Eff.Spec Et] where

  forget : Et → Es

  outputIso :
    ∀ et,
      Eff.Spec.output et ≃
      Eff.Spec.output (forget et)

  blockIso :
    ∀ et,
      Eff.Spec.blockTag et ≃
      Eff.Spec.blockTag (forget et)

  blockInputIso :
    ∀ et bt,
      Eff.Spec.blockInputs et bt ≃
      Eff.Spec.blockInputs (forget et) (blockIso et bt)

  blockOutputIso :
    ∀ et bt,
      Eff.Spec.blockOutputs et bt ≃
      Eff.Spec.blockOutputs (forget et) (blockIso et bt)
```

`Es` and `Et` contain fully applied operation requests, including their
operands, so `forget` transports the entire request.

The target-to-source map is total. Compilation in the other direction is
partial:

```lean
structure EffPullback.Supported
    (P : EffPullback Es Et)
    (source : Es) where
  target : Et
  forget_eq : P.forget target = source
```

The Meta-level registry supplies `Supported` for every operation it emits.

Use equivalences for the Eutt-equivalent fragment. Runtime-partial conversions
need a precondition or a directional simulation theorem instead.

The usual effect stack is composed from identity pullbacks for shared effects
and `EffPullback.sum`. `Tau` is silent for weak equivalence; `Fail` is a
matched terminal effect.

---

## 6. Target evaluator interface

The proof API treats the evaluator state as an abstract indexed carrier:

```lean
EvalState (eff : EffSig) : Type v → Type _
```

Its implementation may contain:

- the closure heap;
- the current expression or call;
- a defunctionalized continuation stack;
- loop frames;
- copy states needed by the corecursor.

None of these continuation constructors belong in macro-generated
certificates.

### 6.1 Public entry states

Return the heap as ordinary evaluator data. The result index of a main
expression or standalone function call is:

```lean
ProgramState eff × R
```

Thus the public entry states have types:

```lean
EvalState.mainExpr :
  ProgramState eff →
  Expr eff TgtVal t →
  EvalState eff (ProgramState eff × TgtVal t)

EvalState.mainCall :
  ProgramState eff →
  FnRef →
  TgtVal a →
  EvalState eff (ProgramState eff × TgtVal b)

EvalState.blockExpr :
  ProgramState eff →
  Expr eff TgtVal t →
  EvalState eff (TgtVal t)
```

`blockExpr` is available only when `t` is an ABI type accepted as an effect
block result.

These are smart constructors into the one internal state representation. They
are not names for additional evaluators.

### 6.2 The one coalgebra

There is exactly one one-step evaluator:

```lean
def evalCo
    (R : Type v)
    (state : EvalState eff R) :
    Eff.Step Et (EvalState eff) R :=
  -- The sole pattern match over the actual internal EvalState constructors.
  ...
```

The document intentionally does not prescribe or name those internal
constructors. Whatever representation implements the heap and continuation
machine is defined once beside `evalCo`. Generic library proofs may case-split
on it there; certificate statements and generated proofs use only
`mainExpr`, `mainCall`, `blockExpr`, and `evalCo`.

The target tree is:

```lean
def evalTree (state : EvalState eff R) : ITree Et R :=
  ITree.corec evalCo state
```

There is no heap-preserving side observation and no duplicate evaluator.

### 6.3 Intrinsic block results

An effect block is required by `Eff.Step` to return exactly:

```lean
Eff.Spec.blockOutputs e tag
```

not a heap pair. This is the one place where the heap cannot be part of the
observable result without changing the effect signature.

The indexed `EvalState` therefore distinguishes:

- main/call fibers, whose result index is `ProgramState eff × R`;
- block fibers, whose result index is the declared flat block output.

A block state still carries and updates its heap internally. At the block
boundary its terminal `evalCo` case returns only the flat block value and
discards the final heap.

This is not an additional semantic choice. Every effect input, output, block
input, and block output is forced to denote an `AbiType`, and `AbiType`
contains no `FnRef` transitively. Therefore:

- a block cannot return a newly allocated closure;
- an operation cannot smuggle such a closure through another ABI container;
- code after the operation has no typed reference by which it could observe
  block-local closure allocations.

`ProgramState` is persistent allocation state, not mutable user-visible state,
so there is no mutation that must be merged back either. Discarding the
block's final heap is consequently forced by the type discipline and is
semantics-preserving. The block computation still carries its starting/current
heap while it runs, so closures captured before or allocated and consumed
within that block remain valid for the lifetime of that execution.

---

## 7. The central inductive judgment

The judgment must itself be indexed by the source and target result types.
This matters because operation blocks change both indices. Define:

```lean
inductive FreeEval
    (P : EffPullback Es Et) :
    {A : Type} →
    {R : Type} →
    (Done : A → R → Prop) →
    RawFree Es A →
    EvalState eff R →
    Prop
```

The constructor shapes are:

```lean
| ret
    (hsource :
      source.observe =
        Eff.Step.ret sourceResult)
    (htarget :
      evalCo _ target =
        Eff.Step.ret targetResult)
    (hDone :
      Done sourceResult targetResult) :
    FreeEval P Done source target

| op
    (et : Et)
    (sourceBlocks :
      (st : Eff.Spec.blockTag (P.forget et)) →
      Eff.Spec.blockInputs (P.forget et) st →
      RawFree Es
        (Eff.Spec.blockOutputs (P.forget et) st))
    (sourceK :
      Eff.Spec.output (P.forget et) →
      RawFree Es A)
    (targetBlocks :
      (tt : Eff.Spec.blockTag et) →
      Eff.Spec.blockInputs et tt →
      EvalState eff (Eff.Spec.blockOutputs et tt))
    (targetK :
      Eff.Spec.output et →
      EvalState eff R)
    (hsource :
      source.observe =
        Eff.Step.op
          (P.forget et)
          sourceBlocks
          sourceK)
    (htarget :
      evalCo _ target =
        Eff.Step.op
          et
          targetBlocks
          targetK)
    (continuations :
      ∀ targetOutput,
        FreeEval P Done
          (sourceK
            (P.outputIso et targetOutput))
          (targetK targetOutput))
    (blocks :
      ∀ targetTag targetBlockInput,
        FreeEval P
          (fun sourceResult targetResult =>
            sourceResult =
              P.blockOutputIso
                et targetTag targetResult)
          (sourceBlocks
            (P.blockIso et targetTag)
            (P.blockInputIso
              et targetTag targetBlockInput))
          (targetBlocks
            targetTag targetBlockInput)) :
    FreeEval P Done source target

| sourceTau
    (hsource :
      source.observe =
        Eff.Step.tau sourceNext)
    (next :
      FreeEval P Done sourceNext target) :
    FreeEval P Done source target

| targetTau
    (htarget :
      evalCo _ target =
        Eff.Step.tau targetNext)
    (next :
      FreeEval P Done source targetNext) :
    FreeEval P Done source target
```

The root instantiation of `Done` receives the returned heap explicitly:

```lean
fun sourceResult (finalHeap, targetResult) =>
  HeapExtends initialHeap finalHeap ∧
  V.holds finalHeap sourceResult targetResult
```

Block instantiations use their flat transported result relation. Consequently
the same `FreeEval` family handles heap-returning main fibers and flat block
fibers without a side observation type.

There is no special `fail` rule. `Fail` is an ordinary matched `op` whose
output and block arities are empty, so its recursive premises are vacuous.

The silent constructors are inductive. Consequently a certificate can skip
any finite number of administrative `Tau`s, but cannot justify an infinite
target-only `Tau` loop.

In particular, do not encode `FreeEval` as a predicate at one fixed `A` and
`R`: that definition cannot descend into intrinsically typed block fibers.

The exact constructor surface should be hidden behind:

```lean
FreeEval.ret
FreeEval.op
FreeEval.sourceTau
FreeEval.targetTau
```

and higher-level `ExprCert.*` theorems.

### 7.1 Derived heterogeneous Eutt

Define the ordinary public relation:

```lean
Eutt
    (P : EffPullback Es Et)
    (RR : A → R → Prop)
    (source : ITree Es A)
    (target : ITree Et R) :
    Prop
```

Then prove once:

```lean
FreeEval.toEutt
    (hDone :
      ∀ sourceResult targetResult,
        Done sourceResult targetResult →
        RR sourceResult targetResult)
    (h : FreeEval P Done source target) :
    Eutt P RR
      source.toITree
      (evalTree target)
```

This proof corecurses only in the library. The input certificate is inductive.

### 7.2 Derived target well-foundedness

Also prove:

```lean
FreeEval.targetWellFounded :
  FreeEval P Done source target →
  EvalState.WellFounded target
```

This is an ordinary induction on the `FreeEval` certificate. It is independent
of whether the chosen Eutt presentation exposes a convenient
divergence-reflection theorem.

Thus correctness and termination are two projections of one certificate:

```text
                         ┌──► heterogeneous Eutt
FreeEval certificate ───┤
                         └──► target well-foundedness
```

---

## 8. Expression certificates

For:

```lean
source : Free Es A
target : Expr eff TgtVal t
```

define:

```lean
def ExprCertAt
    (P : EffPullback Es Et)
    (initial : ProgramState eff)
    (V : ValueRel eff A t)
    (source : Free Es A)
    (target : Expr eff TgtVal t) : Prop :=

  FreeEval P
    (fun sourceValue (finalHeap, targetValue) =>
      HeapExtends initial finalHeap ∧
      V.holds finalHeap sourceValue targetValue)
    source.lower
    (EvalState.mainExpr initial target)
```

There is no `source.run pure` and no source `ITree` in this judgment.

### 8.1 Function relations

A source function has ordinary terminating call semantics:

```lean
sourceCall :
  F →
  A →
  Free Es B
```

Define:

```lean
def ValueRel.fn
    (P : EffPullback Es Et)
    (sourceCall : F → A → Free Es B)
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
        (EvalState.mainCall future targetRef targetArg)
```

The closure may be called in any future heap. Its source result remains a
`Free` computation, not a source `ITree`.

### 8.2 Macro-facing rules

Provide opaque, syntax-directed theorems:

```lean
ExprCert.ret
ExprCert.lit
ExprCert.builtin
ExprCert.lam
ExprCert.app
ExprCert.ite
ExprCert.op
```

Representative application rule:

```lean
ExprCert.app
    (hf :
      (ValueRel.fn P sourceCall RA RB).holds
        heap sourceFn targetRef)
    (hx : RA.holds heap sourceArg targetArg)
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

Its proof uses:

- `Free.lower_bind`;
- the function relation;
- the generic evaluator push-frame lemma;
- induction/composition for `FreeEval`.

The target stack is handled inside the theorem. The generated proof supplies
only the concrete source and AST continuations.

Representative lambda rule:

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
        (ValueRel.fn P sourceCall RA RB).holds
          future sourceFn targetRef →
        ExprCertAt P future RC
          (sourceK sourceFn)
          (targetK targetRef)) :
    ExprCertAt P heap RC
      (sourceK sourceFn)
      (.lam targetBody targetK)
```

The source does not perform an effect to allocate a lambda. It substitutes the
Lean function into `sourceK`; the target allocates a `FnRef`, and the Kripke
function relation connects them.

`ExprCert.op` accepts:

- `P.Supported sourceOp`;
- related inputs;
- a certificate for every corresponding block;
- a certificate for every related output continuation.

All effect transports remain inside `ExprCert.op`.

---

## 9. Structural and well-founded recursion

The source already contains the information that recursive calls terminate.
The proof API must reuse it instead of inventing a coinductive self-call seed.

There is no `OpenExprCert`, `SelfCallSpec`, or coinductive
`DefCert.install`.

### 9.1 The local recursive-call hypothesis

Fix the newly allocated target reference `selfRef`. The induction motive must
already contain the Kripke quantification:

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
      (EvalState.mainCall future selfRef targetArg)
```

While checking the body at `x`, the proof context then contains:

```lean
ih :
  ∀ y, Smaller y x → FunctionCallCorrect y
```

A target self-call is still ordinary `.app`. A proof helper such as:

```lean
RecExprCert.app
```

merely specializes `ih y hyx` to the current future heap and related target
argument. It does not introduce another AST node or a coinductive assumption.

Quantifying over `future` in the motive is essential: a recursive call may
occur after the body has allocated more closures. `HeapExtends` lets the same
induction hypothesis remain valid there without copying any heap proof.

### 9.2 Well-founded closing theorem

The generic closing theorem has this shape:

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
    InstalledFunctionCorrect ...
```

Its proof is `wf.induction`. At each argument it:

1. unfolds the source function once with `source_unfold`;
2. unfolds target closure lookup/call once;
3. applies `body`;
4. discharges recursive calls from the induction hypothesis.

Target call `Tau`s are administrative silent steps consumed by `FreeEval`.
They are not what makes the recursion logically sound.

### 9.3 Structural recursors

Provide a specialization:

```lean
DefCert.structural
```

for definitions whose source equation follows an ordinary recursor. For
`Nat.brecOn`, provide a theorem tailored to the equation generated by Lean:

```lean
DefCert.natBrecOn
```

It should accept:

- the source unfolding theorem;
- certificates for the generated base/body functionals;
- recursive-call certificates supplied by the recursor induction hypothesis.

The reflector recognizes the recursor using Lean metadata and instantiates
this theorem. It does not normalize the recursive computation or unroll it at
the call site.

Nonrecursive definitions are the degenerate case and need no recursion
hypothesis.

---

## 10. Program certificates

Internally:

```lean
def ProgramCertAt
    (P : EffPullback Es Et)
    (heap : ProgramState eff)
    (source : SourceInput → Free Es SourceOutput)
    (target : Program eff inputTp outputTp TgtVal) :
    Prop := ...
```

The macro-facing assembly rules are:

```lean
ProgramCert.main

ProgramCert.define
    (definition : InstalledFunctionCorrect ...)
    (rest :
      ∀ heap' ref,
        HeapExtends heap heap' →
        FunctionRelated heap' sourceDef ref →
        ProgramCertAt P heap' sourceMain (targetRest ref)) :
    ProgramCertAt P heap sourceMain
      (.define targetBody targetRest)
```

`FunctionRelated` abbreviates `ValueRel.fn ... .holds`.

The continuation in `ProgramCert.define` is only the static sequence of
definitions in the certificate. It is not a semantic computation
continuation.

### 10.1 Public correctness theorem

The evaluator-facing denotation returns its final heap:

```lean
Program.denote :
  Program eff inputTp outputTp TgtVal →
  TgtVal inputTp →
  ITree Et (ProgramState eff × TgtVal outputTp)
```

For callers interested only in the ABI value, expose:

```lean
Program.denoteValue target input :=
  (Program.denote target input).map Prod.snd
```

Correctness is stated against the heap-returning denotation, using:

```lean
def OutputRel
    (sourceOutput : SourceOutput)
    (targetOutput : ProgramState eff × TgtVal outputTp) : Prop :=
  OutputValueRel.holds
    targetOutput.1
    sourceOutput
    targetOutput.2
```

Then:

```lean
def ProgramCorrect
    (P : EffPullback Es Et)
    (source : SourceInput → Free Es SourceOutput)
    (target : Program eff inputTp outputTp TgtVal) :
    Prop :=

  ∀ sourceInput targetInput,
    InputRel.holds
      (ProgramState.empty eff)
      sourceInput
      targetInput →
    Eutt P OutputRel
      (Free.toITree (source sourceInput))
      (Program.denote target targetInput)
```

This follows through `FreeEval.toEutt`.

A value-only Eutt theorem follows by relational `map` congruence; it should be
derived rather than reproved by the macro.

### 10.2 Public termination theorem

Expose separately:

```lean
def ProgramTerminates
    (source : SourceInput → Free Es SourceOutput)
    (target : Program eff inputTp outputTp TgtVal) :
    Prop :=

  ∀ sourceInput targetInput,
    InputRel.holds
      (ProgramState.empty eff)
      sourceInput
      targetInput →
    ITree.WellFounded
      (Program.denote target targetInput)
```

This follows through `FreeEval.targetWellFounded`.

The source argument may be omitted from the final definition if desired, but
keeping it visible documents where the termination evidence came from.

### 10.3 Combined theorem

The most useful macro result is:

```lean
structure ProgramVerified ... : Prop where
  correct : ProgramCorrect P source target
  terminates : ProgramTerminates source target
```

Both fields are derived from one `ProgramCertAt`; the macro must not construct
two parallel proofs.

---

## 11. Generated proof shape

A well-founded recursive definition should elaborate approximately as:

```lean
exact ProgramCert.define
  (DefCert.wf
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
        (ExprCert.app fooRelated ...))
      (fun heap₂ barRef barRelated hExt₂ =>

        ProgramCert.main
          (ExprCert.op
            supportedPrint
            ...
            (ExprCert.app barRelated ...))))
```

For a source `Nat.brecOn`, replace the generic `DefCert.wf` application with
`DefCert.natBrecOn`.

The Meta-level environment stores:

```text
source declaration
  ↦ target FnRef local
  ↦ function-relation proof local
  ↦ argument/result ValueRel terms
  ↦ sourceCall term
  ↦ source unfolding/recursor theorem
```

There is no reified logical context and no eager weakening of all prior
definitions.

---

## 12. Complexity requirements

1. `Free.lower` is shared once per source expression; the macro does not reduce
   the resulting `W` tree.
2. Every `ExprCert`, `DefCert`, and `ProgramCert` rule is opaque.
3. Each emitted AST node corresponds to one certificate theorem application.
4. Recursive source functions are proved with their existing
   structural/well-founded induction principle, never by unrolling examples.
5. Each definition certificate is built once and referenced at call sites.
6. Existing function relations are stable under `HeapExtends`; installing a
   definition does not copy old proofs.
7. The concrete heap is not represented as nested proof conjunctions or
   traversed at calls.
8. Effect transport witnesses are emitted once per operation occurrence or
   shared in local `let`s.
9. Source bodies, target bodies, and relation terms are shared through local
   `let`/`have` bindings.
10. Bind reassociation and evaluator-stack manipulation occur only inside
    opaque library theorems.
11. The Eutt and target-well-foundedness theorems are both projections of one
    certificate.
12. Regression tests cover long definition chains, repeated early calls, and
    structurally recursive functions at large symbolic inputs.

The intended generated term size is:

```text
O(AST nodes + call sites + definitions)
```

It must not depend on the number of recursive unfoldings at a concrete input.

---

## 13. Induction and coinduction boundary

The division is now sharp.

Induction is used for:

1. the source `W` tree;
2. `FreeEval`;
3. source structural or well-founded recursion;
4. target well-foundedness.

Corecursion/coinduction is used only for:

1. constructing the target `ITree`;
2. defining/proving generic heterogeneous Eutt;
3. the generic theorem `FreeEval.toEutt`.

In particular:

- recursive definitions are not closed by coinduction;
- target administrative `Tau`s do not serve as termination guards;
- generated certificates never construct coinduction seeds;
- the evaluator continuation stack remains an implementation detail.

This matches the actual authorial intent: a terminating source proof is erased
by compilation, while a corecursive target representation preserves behavior.

---

## 14. Implementation order

1. Add `Free.lower`, `RawFree.toITree`, `Free.toITree`, and their monad/effect
   laws.
2. Index main/call evaluator states by `ProgramState eff × R` and block states
   by their declared flat block result.
3. Implement the evaluator exactly once as ordinary `evalCo`, then define
   `evalTree := ITree.corec evalCo`.
4. Define `HeapExtends` and prove allocation/lookup stability.
5. Define `EffPullback`, `Supported`, identity, and sum composition.
6. Define heterogeneous Eutt over the two effect signatures.
7. Define inductive `FreeEval`.
8. Prove `FreeEval.toEutt` and `FreeEval.targetWellFounded`.
9. Define `ValueRel` and its base/product/sum/array/function constructors.
10. Prove the closed `ExprCert.*` rules, including bind/frame composition.
11. Prove `DefCert.nonrecursive`, `DefCert.wf`, and
    `DefCert.structural`.
12. Add the `Nat.brecOn` specialization.
13. Define `ProgramCert.define/main`, `ProgramCorrect`,
    `ProgramTerminates`, and `ProgramVerified`.
14. Build the macro using only the opaque certificate API.
15. Add proof-size, elaboration-time, Eutt, and termination regression tests.

---

## 15. Decisions to preserve

- Source programs are `Free`, not `CompM` or arbitrary `ITree`.
- `ExactCodensity` is lowered to the inductive `W` representation before
  logical reasoning.
- The proof logic contains no second CPS computation language.
- The target evaluator is a single corecursor into `ITree`.
- Main/call evaluator fibers return `(finalHeap, value)` directly.
- Intrinsic block fibers return their declared ABI result; the `AbiType`
  restriction makes their allocation-only final heap unobservable.
- The central source-to-target certificate is inductive.
- Correctness and target termination are derived from the same certificate.
- Target functions are `FnRef`; source functions remain ordinary Lean values.
- Closure validity is indexed by and monotone under heap extension.
- Target effects are a compile-time-partial pullback of natural source effects.
- Runtime-partial encodings use simulations rather than Eutt equivalence.
- Recursive target self-calls are ordinary applications.
- Source recursion is justified by the original structural/WF principle.
- The public behavior theorem is ordinary heterogeneous Eutt.
- The public termination theorem is explicit rather than hidden inside Eutt.
- Generated certificate size is linear in the emitted program.
