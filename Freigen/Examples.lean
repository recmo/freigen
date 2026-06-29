import Freigen.Examples.Circuit
import Freigen.Examples.Storage

/-!
# Examples

The example signatures and programs, one module per operation signature:

- `Freigen.Examples.Circuit` — the `CircOp` signature (`hint`/`assert`): literals, primitives,
  loops, monomorphised and multi-argument definitions.
- `Freigen.Examples.Storage` — the `StoreOp` signature (`set`/`get`): a mutable store of
  naturals addressed by naturals, with an *operational* denotation (`runStore`).
-/
