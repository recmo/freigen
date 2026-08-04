# AST Proving API

## Goal

The reflector starts with a terminating source computation:

```lean
source : Free Es γ A
```

and emits an AST whose evaluator produces:

```lean
target : CompM Et γ B
```

The generated theorem must establish:

1. `source` and `target` have related observable behavior;
2. every path through `target` is finite.

The proof architecture has three layers:

```text
generic computation theory
  CompM.observe, Eutt, WellFounded, WMeuttCert
                         │
                         ▼
AST value theory
  HeapExtends, ValueRel, ExprCert
                         │
                         ▼
program assembly
  DefCert, ProgramCert
```

The generic layer knows nothing about AST expressions, evaluator states,
heaps, closures, or programs.

---

## 1. Generic computation theory

### 1.1 Context-indexed computations

Effects are families over an explicit context:

```lean
E : Γ → Type
```

Computations have types:

```lean
Free  E γ A
CompM E γ A
```

Their polynomial index is:

```lean
Γ × Type
```

An operation continuation remains in the enclosing context. An operation
block may move to `Eff.Spec.blockCtx`.

The AST type language is not context-indexed:

```lean
Tp
AbiTp
Tp.denote : Tp → Type
```

A closure's execution context belongs to its heap entry and semantic
relation, not to `Tp.fn`.

### 1.2 `CompM` is the proof-facing coinductive type

Proofs use:

```lean
CompM.observe :
  CompM E γ A ≃
    Eff.Step Γ E
      (fun i => CompM E i.1 i.2)
      (γ, A)

CompM.roll :
  Eff.Step Γ E
    (fun i => CompM E i.1 i.2)
    (γ, A) →
  CompM E γ A

CompM.corec :
  ((i : Γ × Type) → X i → Eff.Step Γ E X i) →
  X (γ, A) →
  CompM E γ A
```

with:

```lean
CompM.observe_roll
CompM.roll_observe
CompM.observe_corec
CompM.eq_of_observe_eq
```

The underlying `ITree` and exact-codensity transport are implementation
details. Proofs never lower `CompM`.

### 1.3 Expose the inductive source

```lean
abbrev RawFree
    (E : Γ → Type) [Eff.Spec E]
    (γ : Γ) (A : Type) :=
  IxPoly.W (Eff.Step Γ E) (γ, A)

Free.lower :
  Free E γ A →
  RawFree E γ A
```

Required opaque laws:

```lean
Free.lower_pure
Free.lower_bind
Free.lower_op
```

Embed a finite source tree structurally:

```lean
RawFree.toCompM :
  RawFree E γ A →
  CompM E γ A

Free.toCompM :
  Free E γ A →
  CompM E γ A
```

`RawFree.toCompM` is ordinary recursion using `CompM.roll`.

---

## 2. Relating different effects

The generic theory takes:

```lean
effects : EffectRel Es Et
```

`EffectRel` describes when one visible source layer matches one visible
target layer. It relates:

- operation requests;
- operation results;
- block tags and inputs;
- block results;
- child contexts.

Its essential operation is a monotone relation lifting:

```lean
effects.lift Child Return sourceStep targetStep
```

It uses `Return` for return nodes and `Child` for corresponding continuation
and block children.

The precise Lean representation may use a packed indexed relation. It must
ensure that all target children are covered; otherwise it cannot establish
target well-foundedness.

### 2.1 Administrative target effects

The evaluator runs in:

```lean
abbrev EvalEff (eff : EffSig) :=
  Eff.Tau ⊕ₑ (Eff.Fail ⊕ₑ eff.denote)
```

The AST effect relation:

- matches injected `eff.denote` operations with source operations;
- treats `Tau` as silent;
- provides no successful match for `Fail`.

Thus a certificate proves invalid heap lookups and similar failures are
unreachable.

### 2.2 Cartesian encodings are optional

When target effects are a lossless representation of source effects, define:

```lean
EffCartesianMap Es eff.denote
```

It records erasure plus fiberwise equivalences for results and blocks. Then:

```lean
EffCartesianMap.toEffectRel :
  EffCartesianMap Es eff.denote →
  EffectRel Es (EvalEff eff)
```

This is one constructor for `EffectRel`, not the foundation of the logic.
Directional simulations and interpretation-specific relations must also fit.

The reflector may separately use:

```lean
EffCartesianMap.Supported sourceOp
```

to choose a target encoding of a particular source operation.

---

## 3. Behavior and termination

### 3.1 Heterogeneous Eutt

```lean
Eutt
    (effects : EffectRel Es Et)
    (RR : A → B → Prop)
    (source : CompM Es γ A)
    (target : CompM Et γ B) :
    Prop
```

Eutt observes both computations with `CompM.observe`, permits finite
stuttering by designated silent effects, and uses `effects.lift` for visible
layers.

Its internal relation is indexed by context and result type, so block context
changes require no AST-specific machinery.

The ordinary API includes:

```lean
Eutt.refl
Eutt.symm
Eutt.trans
Eutt.bind
Eutt.map
Eutt.coind
Eutt.coindUpTo
```

Symmetry and transitivity require the corresponding laws from `EffectRel`.

### 3.2 Generic well-foundedness

Define `CompChild` from every recursive field of `CompM.observe`, then:

```lean
def CompM.WellFounded
    (x : CompM E γ A) : Prop :=
  Acc CompChild ⟨γ, A, x⟩
```

This means every continuation and block path is finite. It is generic and
does not mention the AST evaluator.

Reification back to `RawFree` is an optional later theorem, not a prerequisite
for correctness.

### 3.3 The semantic W-to-M property

```lean
def WMeutt
    (effects : EffectRel Es Et)
    (RR : A → B → Prop)
    (source : RawFree Es γ A)
    (target : CompM Et γ B) : Prop :=

  Eutt effects RR source.toCompM target ∧
  target.WellFounded
```

This is the complete semantic meaning of a successful reflection certificate.

---

## 4. The generic inductive certificate

Generated code should not separately build an Eutt coinduction and an
accessibility proof. Provide one inductive proof system:

```lean
inductive WMeuttCert
    (effects : EffectRel Es Et) :
    {γ : Γ} →
    {A B : Type} →
    (RR : A → B → Prop) →
    RawFree Es γ A →
    CompM Et γ B →
    Prop
```

It has only two fundamental forms.

### 4.1 Matched visible layer

```lean
| visible
    (layer :
      effects.lift
        (fun ChildRR sourceChild targetChild =>
          WMeuttCert effects
            ChildRR sourceChild targetChild)
        RR
        source.observe
        target.observe) :
    WMeuttCert effects RR source target
```

`effects.lift` handles returns, operations, continuations, blocks, result
relations, and context transitions. `WMeuttCert` does not repeat them.

### 4.2 Finite silent target step

```lean
| targetTau
    (h : target.observe = Eff.Step.tau next)
    (cert :
      WMeuttCert effects RR source next) :
    WMeuttCert effects RR source target
```

Add `sourceTau` only when the source signature designates a silent effect.
There is no target-`Fail` constructor.

Because this relation is inductive, it cannot certify an infinite silent
loop.

### 4.3 Soundness

Prove once:

```lean
WMeuttCert.toEutt :
  WMeuttCert effects RR source target →
  Eutt effects RR source.toCompM target

WMeuttCert.targetWellFounded :
  WMeuttCert effects RR source target →
  target.WellFounded

WMeuttCert.sound :
  WMeuttCert effects RR source target →
  WMeutt effects RR source target
```

Also provide generic composition lemmas:

```lean
WMeuttCert.ret
WMeuttCert.op
WMeuttCert.targetTau
WMeuttCert.bind
WMeuttCert.map
WMeuttCert.weakenResult
WMeuttCert.transportEffects
```

This is the only generic certificate machinery the reflector needs.

---

## 5. The AST denotation boundary

The evaluator is one indexed corecursor:

```lean
Expr.denoteCo :
  (i : eff.Ctx × Type) →
  EvalState eff i →
  Eff.Step eff.Ctx (EvalEff eff) (EvalState eff) i
```

Expose:

```lean
Expr.denote :
  ProgramState eff →
  Expr eff Tp.denote γ t →
  CompM
    (EvalEff eff)
    γ
    (ProgramState eff × t.denote)
```

implemented by:

```lean
CompM.corec Expr.denoteCo initialState
```

Function calls expose the same heap-returning shape:

```lean
Function.denote :
  ProgramState eff →
  FnRef →
  a.denote →
  CompM
    (EvalEff eff)
    γ
    (ProgramState eff × b.denote)
```

The implicit `γ`, `a`, and `b` are checked against the closure entry. An
invalid reference or signature reaches the evaluator's `Fail` operation.

Effect blocks use the same coalgebra but return only their intrinsic ABI
result. Their final local heap is unobservable because effect boundaries
cannot transport `FnRef`.

`EvalState` appears only in the evaluator implementation. No correctness
relation mentions it.

---

## 6. Heap and value relations

This is the first genuinely AST-specific proof layer.

### 6.1 Heap extension

```lean
HeapExtends :
  ProgramState eff →
  ProgramState eff →
  Prop
```

Required laws:

```lean
HeapExtends.refl
HeapExtends.trans
ProgramState.alloc_extends
ProgramState.lookup_of_extends
```

Generated proofs never inspect the hash map.

### 6.2 Values

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
    HeapExtends heap future →
    holds heap source target →
    holds future source target
```

Provide relations for base types, products, sums, arrays, and functions.

### 6.3 Functions

For:

```lean
sourceCall :
  F →
  A →
  Free Es callCtx B
```

define:

```lean
ValueRel.fn
    effects callCtx sourceCall RA RB :
  ValueRel eff F (.fn a b)
```

`sourceFn` and `targetRef` are related in `heap` when every call in every
future extending heap produces a `WMeuttCert`:

```lean
∀ future sourceArg targetArg,
  HeapExtends heap future →
  RA.holds future sourceArg targetArg →
  WMeuttCert effects
    (fun sourceResult (finalHeap, targetResult) =>
      HeapExtends future finalHeap ∧
      RB.holds finalHeap sourceResult targetResult)
    (sourceCall sourceFn sourceArg).lower
    (Function.denote
      (γ := callCtx)
      future targetRef targetArg)
```

This Kripke quantification is real complexity: old closures must remain valid
after later allocations.

---

## 7. Expression certificates

For:

```lean
source : Free Es γ A
target : Expr eff Tp.denote γ t
```

the macro-facing judgment is just:

```lean
def ExprCert
    (effects : EffectRel Es (EvalEff eff))
    (heap : ProgramState eff)
    (V : ValueRel eff A t)
    (source : Free Es γ A)
    (target : Expr eff Tp.denote γ t) : Prop :=

  WMeuttCert effects
    (fun sourceResult (finalHeap, targetResult) =>
      HeapExtends heap finalHeap ∧
      V.holds finalHeap sourceResult targetResult)
    source.lower
    (Expr.denote heap target)
```

This is an abbreviation, not a new semantic relation.

Provide opaque syntax-directed constructors:

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

They hide:

- `CompM.observe_corec`;
- target administrative `Tau`s;
- evaluator continuation frames;
- heap allocation and lookup;
- effect-stack injection;
- block-context transport.

Operation blocks use the same `WMeuttCert` with the flat block-result relation
instead of the heap-returning root relation.

---

## 8. Definitions and recursion

A definition at `defCtx` has:

```lean
sourceCall :
  F → A → Free Es defCtx B

targetBody :
  FnRef → a.denote →
  Expr eff Tp.denote defCtx b
```

Installing it must establish:

```lean
(ValueRel.fn effects defCtx sourceCall RA RB).holds
  installedHeap sourceDef targetRef
```

### 8.1 Nonrecursive definitions

```lean
DefCert.nonrecursive
```

allocates the closure, proves its body with `ExprCert`, and returns heap
extension plus the function relation.

### 8.2 Well-founded recursion

Use the source termination proof:

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

`FunctionCallCorrect x` is precisely the future-heap call clause from
`ValueRel.fn`.

The proof is ordinary `wf.induction`. Recursive target calls are ordinary
applications; their `Tau`s are administrative and do not justify recursion.

Provide:

```lean
DefCert.structural
DefCert.natBrecOn
```

as specializations using source recursor metadata. The reflector never
concretely unrolls recursion.

---

## 9. Programs

```lean
source :
  SourceInput →
  Free Es mainCtx SourceOutput

target :
  Program eff mainCtx inputTp outputTp Tp.denote
```

Program assembly needs:

```lean
ProgramCert.main
ProgramCert.define
```

Each `define` combines a definition certificate, heap extension, its function
relation, and the certificate for the remaining static definition list.

The denotation is:

```lean
Program.denote :
  Program eff mainCtx inputTp outputTp Tp.denote →
  inputTp.val.denote →
  CompM
    (EvalEff eff)
    mainCtx
    (ProgramState eff × outputTp.val.denote)
```

Fix:

```lean
InputValueRel :
  ValueRel eff SourceInput inputTp.val

OutputValueRel :
  ValueRel eff SourceOutput outputTp.val

def OutputRel
    (sourceOutput : SourceOutput)
    (targetOutput :
      ProgramState eff × outputTp.val.denote) : Prop :=
  OutputValueRel.holds
    targetOutput.1
    sourceOutput
    targetOutput.2
```

Public correctness:

```lean
def ProgramCorrect : Prop :=
  ∀ sourceInput targetInput,
    InputValueRel.holds
      (ProgramState.empty eff)
      sourceInput
      targetInput →
    Eutt effects OutputRel
      (Free.toCompM (source sourceInput))
      (Program.denote target targetInput)
```

Public termination:

```lean
def ProgramTerminates : Prop :=
  ∀ sourceInput targetInput,
    InputValueRel.holds
      (ProgramState.empty eff)
      sourceInput
      targetInput →
    CompM.WellFounded
      (Program.denote target targetInput)
```

Both follow from one program-level `WMeuttCert`.

---

## 10. Generated proof shape

Generated proofs should be structural compositions:

```lean
exact ProgramCert.define
  (DefCert.wf
    foo_wf
    foo_unfold
    (fun x ih =>
      ExprCert.ite
        ...
        (ExprCert.app (ih y hyx) ...)
        ...))
  (fun heap₁ fooRef fooRelated hExt₁ =>
    ProgramCert.main
      (ExprCert.op
        relatedPrint
        ...
        (ExprCert.app fooRelated ...)))
```

The Meta environment stores:

```text
source declaration
  ↦ definition context
  ↦ target FnRef
  ↦ function-relation proof
  ↦ argument/result ValueRel
  ↦ sourceCall
  ↦ source unfolding/recursor theorem
```

Generated terms contain no evaluator states, raw observations, coinduction
seeds, accessibility relations, or hash-map proofs.

---

## 11. Minimal API

Generic:

```lean
CompM.observe / roll / corec
Free.lower
RawFree.toCompM
EffectRel
Eutt
CompM.WellFounded
WMeutt
WMeuttCert
WMeuttCert.sound
```

Optional effect encoding:

```lean
EffCartesianMap
EffCartesianMap.toEffectRel
EffCartesianMap.Supported
```

AST-specific:

```lean
HeapExtends
ValueRel
ValueRel.fn
Expr.denote
Function.denote
Program.denote
ExprCert.*
DefCert.*
ProgramCert.*
```

Anything else needs a concrete justification.

---

## 12. Complexity requirements

1. Lower each source `Free` once.
2. Never normalize the resulting `W`.
3. Use one opaque certificate theorem per AST node.
4. Construct each definition relation once and reference it at calls.
5. Preserve old function relations through `HeapExtends`.
6. Keep evaluator unfolding inside opaque library theorems.
7. Use source induction principles rather than concrete recursive unrolling.
8. Derive Eutt and termination from the same `WMeuttCert`.
9. Hide block-context transport inside `EffectRel`.

Expected generated proof size:

```text
O(AST nodes + call sites + definitions)
```

Regression tests must cover long definition lists, repeated early calls,
multiple effect contexts, context-changing blocks, and large symbolic
recursive inputs.

---

## 13. Implementation order

1. Finish the `CompM` coalgebra API.
2. Implement `RawFree.toCompM`.
3. Define `EffectRel`.
4. Define heterogeneous Eutt over `CompM`.
5. Define generic `CompM.WellFounded`.
6. Define `WMeutt` and `WMeuttCert`; prove soundness.
7. Add generic `WMeuttCert` composition lemmas.
8. Define `EffCartesianMap` only as an optional `EffectRel` constructor.
9. Finish `Expr.denote`, `Function.denote`, and `Program.denote`.
10. Define `HeapExtends` and `ValueRel`.
11. Define `ExprCert` as the specialization above and prove its constructors.
12. Add definition and program assembly theorems.
13. Build the reflector only against opaque certificate lemmas.
14. Add proof-size and elaboration-time regressions.

---

## 14. Non-goals

Do not introduce:

- `FreeEval` specialized to evaluator states;
- `PackedEvalState` or evaluator-specific child relations;
- proof-facing evaluator-state constructors;
- a second evaluator for proofs;
- a logical CPS computation language;
- mandatory effect isomorphisms where relations suffice;
- AST-specific target well-foundedness;
- reification as a correctness prerequisite;
- separate correctness and termination certificate trees;
- contexts inside `Tp`;
- special recursive-call AST nodes.

The proof theory begins after AST denotation, at `CompM`.
