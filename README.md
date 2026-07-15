# Freigen

Freigen reflects higher-order free programs into a small typed AST while constructing a relational
weak-bisimulation proof in lockstep.

## Core API

- `ITree.HSig` describes effects and dynamically bound operation blocks. A normal first-order
  effect is simply an operation with no branches.
- `Free H A` is the source syntax. `Free.eval` interprets it and `Free.toITree` embeds it in the
  coinductive semantics.
- `Ast.Signature` is the `Tp0`-indexed reflected signature. `Signature.Compat` relates the source
  `HSig` to it without requiring source and target carrier types to be equivalent.
- `Ast.Expr` is the `Tp`-indexed PHOAS tree. `Expr.denote` interprets it into `ITree.CompE`.
- `reflect% term` returns closed AST code bundled with its relational `ITree.CompE.Eutt` proof.
- `reflect_def name := term` gives the code and theorem stable declaration names.
- `#reflect_plan term` prints the pass-one specialization plan.
- `#compile term => "path"` reflects, checks, serializes, and records an artifact for
  `lake build <library>:prog`.

Reflection registration is explicit data selected by the macro, not typeclass search:
`@[ast_repr]`, `@[ast_compat]`, `@[ast_op]`, `@[ast_inline]`, and `@[ast_render]`.

See [`Freigen/Examples/Circuit/Basic.lean`](Freigen/Examples/Circuit/Basic.lean) for dynamic binders,
effects, recursion, specialization, source locations, serialization, and soundness statements.
The other example modules retain storage, first-class function, and recursion targets, including
documented cases not yet supported by reflection.

The reflector’s reviewer guide, design map, trust story, and current limitations are documented in
[`Freigen/Reflect/README.md`](Freigen/Reflect/README.md).
