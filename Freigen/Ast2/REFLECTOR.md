# AST2 Reflector Design

## Public surface

The AST2 frontend owns the same surface syntax as the original frontend when its module is
imported:

- `reflect% program`
- `reflect_def name := program`
- `#compile program => "path"`

`reflect%` returns closed PHOAS code together with a relational `ITree2.CompE.Eutt` theorem.
The source and target signatures, representations, operation mappings, and serialization data are
declarations tagged with `ast2_compat`, `ast2_repr`, `ast2_op`, and `ast2_render`. They are explicit
elaborator inputs, not typeclasses.

## Pass 1: discovery

Pass 1 emits no AST and no proof terms. It:

1. Resolves the source/target compatibility declaration.
2. Classifies helper arguments as represented values or static specialization arguments.
3. Keys helpers by declaration and static arguments.
4. Walks helper bodies before recording callers, producing dependency order.
5. Marks re-entry of an active key as recursion.
6. Records the exact `ReprSpec` and `OpSpec` terms selected during discovery.

Pass 2 consumes this immutable plan. It does not repeat registry resolution.

## Pass 2: paired emission

Pass 2 maintains three distinct forms of every represented atom:

- a generic PHOAS atom `V α`, used only by closed AST code;
- a semantic target atom `α.denote`, used by `Expr.denote`;
- a source atom, used only by the source `Freek` term and proof.

The environment also stores `Φ → Rel source target`. A source-only variable or relation proof is
rejected if it occurs in the generated AST projection.

Every recursive call returns one paired emission. Its proof component is built by a
`Reflection.*` smart constructor, whose first projection must be definitionally equal to the
semantic instantiation of the generic code component. There is no later proof walk.

## Helper spilling

Nonrecursive specializations are emitted in pass-1 dependency order as nested `Expr.lam` nodes;
recursive specializations use `Expr.letrec`. A two-argument represented helper is spilled as one
product argument: calls construct the pair, the body projects it, and adequacy uses the conjunction
of the two representation relations. Single represented arguments may be mixed with any number of
static specialization arguments. For each specialization the emitter stores:

- its PHOAS function value;
- its `Adequate` theorem relating source calls to target calls.

Non-recursive helpers have an adequacy theorem obtained directly from their reflected body.
Recursive helpers use the source definition's structural induction to prove adequacy for the
`mrec` denotation. Calls compose through relational `Eutt.bind`, including non-tail calls.

The implemented recursive shape is structural recursion over one represented `Nat`. Pass 1 reads
the equation compiler metadata, while pass 2 emits a zero test, predecessor call through
`Expr.selfCall`, and `Expr.letrec`. Thus a symbolic argument does not have to reduce during macro
execution.

## Serialization

`#compile` creates three declarations: reflected code, its serialized `String`, and a named
soundness theorem. It records the latter two in a persistent environment extension. The `:prog`
facet evaluates the stored string, writes it to the requested path, and prints the theorem type.
Serialization traverses PHOAS structurally, including lambdas, recursive binders, self calls, and
the dynamically bound branches enumerated by the signature's `RenderSpec`.

## Source provenance

`Expr.source` is a denotationally transparent annotation containing a module and Lean source
range. Reflection currently records everything available without replaying dependencies:

- the exact syntax range supplied to `reflect%`, `reflect_def`, or `#compile`;
- the declaration range of the reflected root when it is a named declaration;
- the declaration range of every spilled helper body, including recursive bodies.

Imported `.olean` files do not retain subterm `InfoTree` ranges, so helper annotations are
declaration-granular for now. Missing ranges simply omit the annotation. The serializer preserves
annotations as `(source module startLine startColumn endLine endColumn (block ...))`.

## Partial representations

`ReprSpec` contains an encoding and a source/target relation, but does not assert target coverage.
For example, `Fin n` is represented by `Nat` with `source.val = target`. A reflected function's
soundness quantifies over related arguments; equivalently, callers obtain the usual theorem under
the target invariant `target < n`. Invalid target values remain outside the correctness claim.
