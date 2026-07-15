# Client

This downstream Lake package imports Freigen and exercises its `:prog` facet.

`Client/Program.lean` defines a higher-order `Free` circuit with two dynamic `hint` blocks and an
`assert`, then emits it with:

```sh
lake build Client:prog
```
