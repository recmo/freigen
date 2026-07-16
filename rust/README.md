# `freigen` Rust SDK

The Rust consumer for Freigen's promoted AST format. It parses `.prog` S-expressions into a typed
tree and executes programs with a client-supplied effect handler.

- `sexp` reads the uniform S-expression layer.
- `ast` mirrors the two-level Lean AST: a prefix of potentially recursive definitions, a terminal
  argument-taking `main`, and explicit closure construction followed by ordinary `app` nodes.
- `parse` is the inverse of `Freigen/Ast/Sexp.lean`.
- `interp` evaluates the pure fragment and passes operations to `Handler::op`. The handler receives
  the operation input and `BranchCalls`; each branch can be invoked with its dynamically bound
  input, ignored, or invoked more than once according to the target semantics.

The promoted object universe currently emits `Nat`, `Bool`, `Unit`, products, and Kleisli function
types. Additional runtime value variants remain reserved for future Lean representations.

## Tests

```sh
cargo test
```

The suite covers source annotations, expression conditionals, closures, level-one recursion,
main arguments, dynamic operation branches, and downstream Lean artifacts.
