# Freigen reflector: reviewer’s guide

Freigen turns a higher-order `Free` computation into a typed two-level program and constructs the
weak-bisimulation certificate for that exact program during emission. A successful `reflect%`
returns, morally:

```lean
{ code : Closed H α //
    ITree.CompE.Eutt (C code.ctx) result
      (Free.toITree source)
      (Closed.denote code) }
```

The metaprogram can reject a source term or choose inconvenient code. It cannot certify incorrect
code without Lean’s kernel accepting a false proof term.

## The central design

The output language is defined in [`../Ast/Basic.lean`](../Ast/Basic.lean).

```text
Code       = definition telescope + main
Definition = captured environment × explicit argument → Expr
Expr       = values | primitives | if | closure ref env | app fn arg | visible operation
```

A `DefRef` is an intrinsically typed de Bruijn reference. A newly added definition is scoped over
itself and the older tail of the telescope. That gives exactly the intended stratification:
self-recursion and calls to dependencies are representable; forward references are not.

There is one function representation. `Tp.fn input output` denotes an explicit `Closure`, not a
Lean function. Constructing a closure pairs a `DefRef` with a packed captured environment, and
`Expr.app` invokes it. Consequently there is no local-lambda constructor, no distinct definition
call, no self-call node, and no `letrec`.

The semantic path is:

```text
Expr.denote
  : Expr → CompE (visible effects ⊕ Call completedDefinitions) result

Defs.callHandler
  : Call completedDefinitions → CompE visibleEffects result

Code.denote
  = interpHandler Defs.callHandler (main.denote ...)
```

The call handler dispatches the closure’s typed reference into `Defs.denote` and inserts the
handler’s guarded `tau`. Recursion is therefore an ordinary closure application in syntax and a
guarded coinductive call in semantics.

## The proof boundary

Three files contain the semantic argument.

1. [`../ITree/Basic.lean`](../ITree/Basic.lean) defines indexed tree fibers, `asBlock`,
   `relabelBlock`, monadic bind, call handling, and their coalgebraic laws.
2. [`../Ast/Run.lean`](../Ast/Run.lean) proves that interpreting calls commutes with embedding a
   computation into any scoped operation block. The proof is a direct indexed bisimulation; its
   call cases use `asBlock_bind` and `relabelBlock_bind`.
3. [`Sound.lean`](Sound.lean) defines `ReflectionWitness` and the compositional rules used by the
   macro. In particular, `Reflection.op` matches scoped branches using the theorem from
   `Ast.Run`; it contains no normalization oracle or unproved handler law.

[`../ITree/Handler.lean`](../ITree/Handler.lean) is deliberately small: it only exposes the five
one-step equations for interpreting return, failure, `tau`, visible operations, and calls at an
arbitrary result fiber.

## The two reflector passes

Pass one, [`Plan.lean`](Plan.lean), is read-only. `discover`:

- identifies supported helper boundaries;
- resolves host/object representations;
- specializes closed static arguments;
- recognizes re-entry into an active specialization as recursion;
- records definitions in dependency order.

It emits no AST and no proof terms. The result is an immutable `Plan`.

Pass two executes that plan:

- [`Emit.lean`](Emit.lean) allocates the final `DefCtx`, constructs definitions in dependency
  order, and packages `Code` plus its theorem.
- [`Comp.lean`](Comp.lean) is the computation dispatcher. Its “Source matching” section recognizes
  the few supported source shapes; its construction sections emit the corresponding syntax and
  proof together.
- [`Value.lean`](Value.lean) handles pure represented values.
- [`Construct.lean`](Construct.lean) and [`NatConstruct.lean`](NatConstruct.lean) are typed
  adapters for assembling long object-language and theorem applications.

Every computation emission carries three synchronized views: semantic target code, generic PHOAS
code, and the proof for the semantic code. There is no later traversal that attempts to recover a
proof from a finished AST.

## Recursion

The only current recursion backend is structural unary Nat recursion. The planner uses Lean’s
recursor metadata to recognize the generated `Nat.brecOn` application; it does not repeatedly
`whnf` the recursive source body.

[`NatRec.lean`](NatRec.lean) states and proves the bridge between that source functional and the
ordinary closure/application semantics of one definition in the final telescope.
[`NatConstruct.lean`](NatConstruct.lean) only builds applications of that theorem.

The important emitted shape is visible in
[`../Examples/Serialized.lean`](../Examples/Serialized.lean): a recursive branch constructs a
closure for its own `def` reference and applies it. The loop is neither unrolled nor represented by
a privileged recursive AST node.

## Recommended reading order

A conceptual review can stop after these eight files:

1. [`../Ast/Basic.lean`](../Ast/Basic.lean) — the language and denotation.
2. [`../ITree/Basic.lean`](../ITree/Basic.lean) — indexed scoped trees and call interpretation.
3. [`../Ast/Run.lean`](../Ast/Run.lean) — the scoped call-handler bisimulation.
4. [`Sound.lean`](Sound.lean) — the certificate interface and compositional proof rules.
5. [`Plan.lean`](Plan.lean) — specialization discovery.
6. [`Comp.lean`](Comp.lean) — source matching and node construction.
7. [`Emit.lean`](Emit.lean) — definition-table construction and packaging.
8. [`../Examples/Serialized.lean`](../Examples/Serialized.lean) and
   [`../AxCheck.lean`](../AxCheck.lean) — exact outputs and axiom footprints.

For the extension surface, then read [`Attributes.lean`](Attributes.lean),
[`Registry.lean`](Registry.lean), [`Resolve.lean`](Resolve.lean), and
[`Source.lean`](Source.lean). [`Basic.lean`](Basic.lean) contains only the public commands once
their implementation is understood.

## Files at a glance

| File | Responsibility |
| --- | --- |
| `Ast/Basic.lean` | Object language, closures, definition telescope, denotation |
| `Ast/Run.lean` | Call-handler/block commuting bisimulation |
| `Ast/Sexp.lean` | Stable two-level serialization |
| `ITree/Basic.lean` | Scoped coinductive trees, bind, handlers |
| `ITree/Handler.lean` | Indexed handler equations |
| `Reflect/Sound.lean` | Semantic contracts and proof constructors |
| `Reflect/Plan.lean` | Immutable specialization plan |
| `Reflect/Comp.lean` | Computation matching and lockstep emission |
| `Reflect/Emit.lean` | Plan execution and final code/theorem packaging |
| `Reflect/NatRec.lean` | Nat recursion adequacy |
| `Reflect/Value.lean` | Pure value reification |
| `Reflect/Construct*.lean` | Typed meta-level construction adapters |
| `Compile/Registry.lean` | Lightweight persistent artifact registry |
| `Compile.lean` | Reflection and artifact registration |
| `Main.lean` | Standalone artifact emitter; imports only the lightweight registry |

The split between `Compile.Registry` and `Compile` is a performance boundary: building the
emitter executable does not native-compile the reflector and example graph.

## Current accepted fragment

The reflector currently supports registered Nat, Int, Bool, Unit, product, and closure
representations; registered higher-order operations; ordinary specialized helpers; the supported
one- or two-value helper boundaries; structural unary Nat recursion; source locations; and dynamic
operation blocks.

Capturing local source lambdas, recursion schemes other than the Nat backend, unregistered values or
operations, and escaping source-only values are rejected during elaboration.

## Verification

From the repository root:

```sh
lake build
lake build Freigen.Examples.Serialized
lake env lean Freigen/AxCheck.lean
lake build Freigen:prog
(cd rust && cargo test)
```

The serialized guards contain the complete multiline AST for every supported example. The Rust
consumer parses the same closure/application format and executes recursion, main arguments, and
dynamic operation branches.
