# Freigen

Freigen reflects higher-order `Free` computations into a small typed program AST while constructing
a relational weak-bisimulation proof in lockstep.

## The object language

A `Code H args output` contains:

- a typed telescope of definitions;
- an argument-taking `main`;
- explicit closure values that pair a definition reference with its captured environment;
- ordinary `app` nodes for every function call.

Each definition has one captured-environment argument and one explicit argument. Its body may refer
to itself and to older definitions, never to definitions introduced later. There is no `letrec`,
local lambda, or special self-call node.

`Expr.denote` produces an open interaction tree over the visible target effects plus one global
call effect. `Code.denote` interprets that call effect with the completed definition telescope.
Recursive calls are therefore ordinary closure applications whose denotation is guarded by the call
handler's silent step.

## Public API

- `reflect% term` returns closed code bundled with its `ITree.CompE.Eutt` certificate.
- `reflect_def name := term` gives the code and theorem stable declaration names.
- `#reflect_plan term` displays the immutable specialization plan without emitting code.
- `#compile term => "path"` records a serialized artifact for `lake build <library>:prog`.

Reflection registration is explicit data, not typeclass search:
`@[ast_repr]`, `@[ast_compat]`, `@[ast_op]`, `@[ast_inline]`, and `@[ast_render]`.

## Where to start

For the design and audit path, read
[`Freigen/Reflect/README.md`](Freigen/Reflect/README.md). The shortest executable tour is:

1. [`Freigen/Ast/Basic.lean`](Freigen/Ast/Basic.lean) — object types, closures, expressions,
   definition telescopes, and denotation.
2. [`Freigen/Reflect/Plan.lean`](Freigen/Reflect/Plan.lean) — specialization discovery.
3. [`Freigen/Reflect/Comp.lean`](Freigen/Reflect/Comp.lean) — source-node matching and lockstep
   syntax/proof construction.
4. [`Freigen/Reflect/Emit.lean`](Freigen/Reflect/Emit.lean) — execution of the plan and final
   packaging.
5. [`Freigen/Examples/Serialized.lean`](Freigen/Examples/Serialized.lean) — complete guarded ASTs
   for every supported example.

## Checks

```sh
lake build
lake build Freigen:prog
(cd rust && cargo test)
```

The Rust consumer mirrors the same two-level format and tests parsing, closures, recursion,
argument-taking main, and dynamically bound operation branches.
