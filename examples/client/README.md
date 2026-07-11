# Client

This downstream Lake package imports Freigen and exercises its `:prog` facet.

`Client/Program.lean` defines a higher-order `Free` circuit with two dynamic `hint` blocks and an
`assert`, then emits it with:

```sh
lake build Client:prog
```

`Client/Poseidon.lean` keeps the BN254 Poseidon implementation and known-answer tests live. Its
reflection target is intentionally commented: the current `Tp` universe has no `ZMod`/field
representation. The intended `reflect_def` and `#compile` lines remain beside the source as the
acceptance target for that extension.
