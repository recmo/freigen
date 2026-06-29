# Freigen

*frei* (free) + *eigen* (self) — reflecting effectful Lean programs into a free-monadic AST
and denoting them back, with the round-trip proven faithful by `rfl`.

- `Freigen/Free.lean` — the free monad and the freer-monad `Effect` functor
- `Freigen/Ast.lean` — the object-type universe `Tp`, the A-normal `Exp`/`Prog` AST, its denotation, and a pretty-printer
- `Freigen/Reflect.lean` — the `reflect%` elaborator (reify a `Free (Effect Op)` computation into a `Prog`)
- `Freigen/Examples/` — concrete operation signatures and example programs (one module per signature):
  - `Circuit.lean` — the `CircOp` signature (`hint`/`assert`)
  - `Storage.lean` — the `StoreOp` signature (`set`/`get`): a store of naturals addressed by naturals, with an operational denotation (`runStore`)
