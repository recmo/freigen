# Freigen Reflector: Reviewer’s Guide

Freigen reflects a higher-order `Free` program into a small typed PHOAS AST and constructs a
relational weak-bisimulation proof for that exact AST in the same traversal. The result is not just
code generation: every successful `reflect%` invocation returns closed syntax together with a
kernel-checked theorem relating its denotation to `Free.toITree`.

The central output type is [`Reflected`](Sound.lean), morally:

```lean
{ code : ∀ V, Expr H V none α //
    ITree.CompE.Eutt C result
      (Free.toITree source)
      (Expr.denote (code (Tp.denote (ITree.CompE H.spec)))) }
```

The elaborator is therefore outside the trusted argument: it may reject a source program or build
an inconvenient AST, but it cannot successfully attach an invalid certificate without Lean’s
kernel rejecting the generated declaration.

## What to look at

The implementation is organized around three claims.

1. **Specialization is planned, not discovered while emitting.** [`discover`](Plan.lean) produces
   an immutable dependency-ordered `Plan`. `HelperBoundary` contains the entire source-argument
   layout, so represented arguments, static specialization arguments, and reconstruction cannot
   disagree.
2. **Syntax and proof are synchronized locally.** Every computation node returns one
   [`Emission`](Comp.lean) containing semantic AST, generic PHOAS AST, and the theorem for the
   semantic AST. There is no later AST recovery, proof search over generated syntax, or global
   normalization pass.
3. **Recursion is reflected structurally.** The planner recognizes Lean’s generated `Nat.brecOn`
   shape. [`NatRec.lean`](NatRec.lean) relates that source functional to the AST’s `letrec`/`mrec`
   semantics, so a symbolic recursive argument is never normalized by the macro.

The most useful review questions are:

- Is `ReprSpec`—an encoder plus a source/target relation—the right boundary between host values and
  object types?
- Is `HelperBoundary` the canonical representation of monomorphic specialization and argument
  layout?
- Is the `Nat.brecOn` recognition/adequacy boundary the right prototype for additional recursion
  backends?
- Is simultaneous semantic/generic/proof emission preferable to emitting syntax first and proving
  it in a second traversal?
- Does the explicit [`Construct`](Construct.lean) adapter layer buy enough auditability to justify
  mirroring the signatures of computation AST nodes and proof constructors?

## Fast reading route

For a conceptual review, these six stops are sufficient:

1. [`../Ast/Basic.lean`](../Ast/Basic.lean): `Tp0`, `Tp`, `Expr`, and `Expr.denote`. These are the
   object language and its semantics.
2. [`Sound.lean`](Sound.lean): `Reflected`, `ReflectionWitnessAt`, `Adequate`, and the
   `Reflection.*`/`RecReflection.*` rules. This is the semantic contract.
3. [`Plan.lean`](Plan.lean): `HelperBoundary`, `SpecializationKey`, `Plan`, and `discover`. This is
   the complete policy for helper specialization and supported recursion recognition.
4. [`Comp.lean`](Comp.lean): `Emission`, `EmitContext`, the node emitters, and the small `emitComp`
   dispatcher. This is where source matching, AST construction, and proof construction coincide.
5. [`Emit.lean`](Emit.lean): `buildRecursiveHelper`, `buildOrdinaryHelper`, `emitProgram`, and
   `reflectProgram`. This installs the plan and packages the result; it does not traverse a second
   AST.
6. [`../Examples/Serialized.lean`](../Examples/Serialized.lean) and
   [`../AxCheck.lean`](../AxCheck.lean): exact generated trees and the axiom footprint of generated
   certificates.

For a full implementation audit, continue with `Registry.lean` → `Finite.lean` → `Resolve.lean` for
representation selection, `Value.lean` for value matching and its small syntax constructors,
`Construct.lean` for the named computation/proof signature boundary, and `NatConstruct.lean` for
its recursion-specific extension.

## One worked path

[`Examples/Circuit/Basic.lean`](../Examples/Circuit/Basic.lean) contains a recursive helper whose
argument comes from an effect, so macro-time evaluation cannot unroll it:

```lean
def triangularSrc : Nat → Circuit Nat
  | 0 => pure 0
  | n + 1 => do
      let subtotal ← triangularSrc n
      pure (subtotal + n + 1)

def symbolicRecursiveMain : Circuit Nat := do
  let n ← Circuit.hint (pure 5)
  triangularSrc n

#reflect_plan symbolicRecursiveMain
reflect_def symbolicRecursiveReflected := symbolicRecursiveMain
```

The plan reports one specialization, `triangularSrc`. The emitted tree contains one `letrec` and a
symbolic `self` call—not five unrolled copies. `reflect_def` creates both the closed program and:

```lean
symbolicRecursiveReflected_sound :
  ITree.CompE.Eutt CircCompat Eq
    (Free.toITree symbolicRecursiveMain)
    (Expr.denote (symbolicRecursiveReflected (Tp.denote M)))
```

The complete serialized tree, including source ranges, is guarded in
[`Serialized.lean`](../Examples/Serialized.lean). Any change to helper spilling, recursion shape,
finite tags, operation branches, or source annotations must update an exact expected AST.

## Claims and executable evidence

| Claim | Primary code | Evidence |
| --- | --- | --- |
| Successful reflection carries an `Eutt` certificate | [`Sound.lean`](Sound.lean), [`Emit.lean`](Emit.lean) | [`AxCheck.lean`](../AxCheck.lean) |
| Semantic and generic ASTs stay synchronized | `Emission` and `emitComp` in [`Comp.lean`](Comp.lean) | Full-AST guards in [`Serialized.lean`](../Examples/Serialized.lean) |
| Helpers are monomorphized by declaration and static arguments | `SpecializationKey` and `discover` in [`Plan.lean`](Plan.lean) | `twoFinSpecializationsSource` in [`FiniteTypes.lean`](../Examples/FiniteTypes.lean) |
| Symbolic recursion is represented by `letrec`/`self`, not unfolded | [`NatRec.lean`](NatRec.lean), `buildRecursiveHelper` in [`Emit.lean`](Emit.lean) | `symbolicRecursiveMain` and `sumMain` in [`Circuit/Basic.lean`](../Examples/Circuit/Basic.lean) and [`Recursion.lean`](../Examples/Recursion.lean) |
| Dynamic operation blocks preserve bound values and proofs | `emitOrdinaryDynamicBlocks` in [`Comp.lean`](Comp.lean) | Circuit `hint` guards in [`Serialized.lean`](../Examples/Serialized.lean) |
| Literal `Fin n`/`ZMod n` indices remain precise and casts are checked | [`Finite.lean`](Finite.lean), [`Value.lean`](Value.lean) | [`FiniteTypes.lean`](../Examples/FiniteTypes.lean), [`ZModCompatibility.lean`](../Examples/ZModCompatibility.lean) |
| Reflection does not depend on aggressive reduction | `exposeComp` in [`Comp.lean`](Comp.lean), recursion recognition in [`Plan.lean`](Plan.lean) | Cached builds plus symbolic helper/recursion AST guards |

## Reproduce the checks

From the repository root:

```sh
# Entire project, including every Freigen.* module
lake build

# Exact serialized AST regression suite
lake build Freigen.Examples.Serialized

# Print the axiom footprint of representative generated certificates
lake env lean Freigen/AxCheck.lean

# Exercise precise and symbolic Fin/ZMod reflection directly
lake env lean Freigen/Examples/FiniteTypes.lean

# Materialize artifacts recorded by #compile
lake build Freigen:prog
```

The cached full build is currently sub-second on the development machine; the important regression
criterion is that reflection remains proportional to the represented program rather than to
reducible source execution.

## Scope and known limits

The accepted fragment is deliberately explicit:

- `Free.pure`, `Free.bind`, and registered `Free.op` computations;
- registered first-order values, built-in literals, products/projections, supported unary and
  binary value operations, and checked finite-type casts;
- nonrecursive helpers with one represented argument or two represented arguments encoded as a
  product, interleaved with any closed static specialization arguments;
- structural `Nat.brecOn` helpers with one represented `Nat` argument;
- dynamic operation blocks in ordinary code; operations inside recursive bodies currently require
  empty branch types.

Unsupported dynamic helper arguments, unregistered representations or operations, other recursion
schemes, capturing first-class helper functions, and source-only variables escaping into PHOAS
code are elaboration errors. [`FirstClass.lean`](../Examples/FirstClass.lean) and the commented
targets in [`Recursion.lean`](../Examples/Recursion.lean) retain representative future acceptance
tests.

The main deliberate tradeoffs are:

- **Two phases.** Planning duplicates no emission work, but exists so specialization identity,
  recursion, and dependency order are settled before any proof term is built.
- **One lockstep emission.** Semantic code, generic code, and proof share control flow. This avoids
  recovery passes at the cost of an `Emission` invariant maintained by the node constructors.
- **Explicit construction adapters.** `Construct.lean` and `NatConstruct.lean` are verbose, but the
  long computation/proof-rule applications are centralized there and named at call sites. The
  smaller value-node applications remain next to value matching in `Value.lean`.
- **One recursion backend.** The generic soundness contracts support recursive bodies; only the
  `Nat.brecOn` recognition and adequacy backend is implemented.
- **Best-effort finite precision.** Literal bounds become `Tp0.fin n`/`Tp0.zmod n`; symbolic bounds
  use carrier representations until an explicit checked tag crosses back into a precise type.

---

# Implementation Reference

## Public surface

Importing [`Basic.lean`](Basic.lean) provides:

- `#reflect_plan program` — print pass-one specializations without emitting code;
- `reflect_semantic% program` — expose the semantic AST and witness for debugging;
- `reflect% program` — return closed PHOAS code and its relational theorem;
- `reflect_def name := program` — install stable code and `name_sound` declarations.

`#compile program => "path"` is the downstream serialization command from `Freigen.Compile`.

Registrations are explicit elaborator data rather than typeclass search: `ast_compat`, `ast_repr`,
`ast_op`, `ast_inline`, and `ast_render`.

## Files at a glance

| File | Sole responsibility |
| --- | --- |
| [`Attributes.lean`](Attributes.lean) | Declares the `ast_*` registry attributes. |
| [`Registry.lean`](Registry.lean) | Defines `ReprSpec`, `OpSpec`, and built-in representations. |
| [`Finite.lean`](Finite.lean) | Owns `Fin`/`ZMod` recognition and precise-tagging policy. |
| [`Resolve.lean`](Resolve.lean) | Selects explicit registry entries and invokes representation policy. |
| [`Source.lean`](Source.lean) | Quotes syntax and declaration source ranges. |
| [`Sound.lean`](Sound.lean) | Defines reflection contracts and proof constructors; no metaprogramming. |
| [`NatRec.lean`](NatRec.lean) | Proves the `Nat.brecOn` source-functional/AST recursion bridge. |
| [`Construct.lean`](Construct.lean) | Names computation-AST and proof-rule declaration applications. |
| [`NatConstruct.lean`](NatConstruct.lean) | Adds construction adapters for the Nat recursion backend. |
| [`Plan.lean`](Plan.lean) | Recognizes recursion and constructs the immutable helper plan. |
| [`Value.lean`](Value.lean) | Matches host values and constructs generic value syntax. |
| [`Comp.lean`](Comp.lean) | Matches computation nodes and emits code plus proofs in lockstep. |
| [`Emit.lean`](Emit.lean) | Builds/installs planned helpers, executes the root, and packages output. |
| [`Basic.lean`](Basic.lean) | Exposes the four public elaborators. |

The phase boundary is literal:

```text
registries ───────┐
source term ──────┴─→ discover → Plan
source term + Plan ─→ helper installation → paired emission → Reflected
```

## Pass 1: discovery

Pass 1 emits no AST and no proof terms. It:

1. Resolves source/target signature compatibility.
2. Classifies helper arguments as represented values, closed static arguments, or unsupported.
3. Uses one `SpecializationKey` representation in completed, active, and recursive state.
4. Walks helper bodies before recording callers, producing dependency order.
5. Marks re-entry of an active key as recursion.
6. Records the exact `ReprSpec` selected for every represented boundary argument and result.
7. Constructs a `HelperBoundary` containing every static segment and represented parameter.
8. Rejects unsupported boundaries before returning the plan.

The root has a separate entry path: an ordinary root is executed directly, while a recursive root
is deliberately planned as a helper. Operation mappings are resolved during emission; helper
specialization and argument classification are not repeated.

## Pass 2: paired emission

Pass 2 maintains three forms of each represented atom:

- a generic PHOAS atom `V α`, used only by closed AST code;
- a semantic target atom `α.denote`, used by `Expr.denote`;
- a source atom, used only by the source `Free` term and proof.

The environment also stores `Φ → Rel source target`. A source-only variable or relation proof is
rejected if it occurs in the generated AST projection.

Every source node produces one `Emission` containing semantic code, generic code, and a
`ReflectionWitnessAt` for the semantic code. `Construct.*` records name the arguments supplied to
computation-level `Expr.*` and `Reflection.*` declarations; `Value.lean` owns value syntax. Final
packaging abstracts the generic program over `V`, specializes it to the semantic carrier for the
theorem statement, and attaches the already-constructed witness.

Operation construction has three proof-rule cases: recursive operations with empty branches,
ordinary operations with empty branches, and ordinary operations with dynamic branches. The common
path resolves the operation, emits its continuation, selects one case, and constructs the final
node.

## Helper spilling and recursion

Nonrecursive specializations are installed in dependency order as nested `Expr.lam` nodes;
recursive specializations use `Expr.letrec`. A two-argument helper is spilled as one product
argument: calls construct the pair, the body projects it, and adequacy uses the conjunction of the
two representation relations. Each installed helper stores its PHOAS function value and an
`Adequate` theorem relating source and target calls.

Recursive helper construction uses the source definition’s `Nat.brecOn` functional to build the
zero and successor ASTs. `natBrecCode` gives semantic and generic bodies the same explicit syntax;
`mrec_natBrecBody_eq_code` transports structural-induction adequacy locally. Recursive calls become
`Expr.selfCall`, including beneath effects and continuations. There is no whole-program recursive
normalization or special case in final packaging.

## Partial finite representations

`ReprSpec` contains an encoding and source/target relation but does not assert target coverage.
When a bound reduces to a numeral, `Fin n` and `ZMod n` retain precise object types
`Tp0.fin n`/`Tp0.zmod n`, whose denotations are the actual finite host types. Literal construction
uses checked `finTag`/`zmodTag`; failure in the target semantics prevents an invalid carrier from
becoming a precise finite value. `finErase`/`zmodErase` expose carriers explicitly.

When a bound is symbolic, it cannot be stored in the first-order type tag. `Fin n` therefore uses a
`Nat` carrier related by `source.val = target`, and `ZMod n` uses its canonical `Int` carrier. Any
later boundary into a precise finite object is an explicit checked tag rather than definitional
equality. `ZModCarrier` is definitionally equal to Mathlib’s `ZMod` family;
[`ZModCompatibility.lean`](../Examples/ZModCompatibility.lean) checks that boundary against the
actual Mathlib type.

## Serialization and provenance

`#compile` creates reflected code, its serialized `String`, and a named soundness theorem, then
records the artifact in a persistent environment extension. The `:prog` library facet evaluates
recorded strings and writes them to their requested paths.

`Expr.source` is a denotationally transparent annotation containing a module and Lean source range.
Reflection records the invocation range, a named root’s declaration range, and every spilled
helper’s declaration range. Imported `.olean` files do not retain subterm `InfoTree` ranges, so
helper annotations are declaration-granular. Missing ranges omit the annotation; serialization
preserves those that exist.
