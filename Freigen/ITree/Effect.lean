import Freigen.Ast.Tp

/-!
# The effect signature functor

An operation signature is `Op : TpF → TpF → Type` — `Op I R` is an operation taking an input
`I.denote` and returning an `R.denote`, with `I R` **first-order object types** (`TpF`): an
effect's payload cannot be a function.  That restriction is load-bearing twice over:

* it keeps the whole effect stack in `Type 0` — signatures quantify object-type *codes* (plain
  data), never host `Type`s, so nothing forces the trees into `Type 1`;
* `TpF.denote` is `Op`-independent, so the interaction-tree domain (whose event payloads live
  here) is definable *before* the full `Tp.denote`, whose `fn` denotation is Kleisli **into**
  that domain.

`Effect Op` is one event: an operation packaged with its input.  This is what a `Comp`'s `vis`
node carries; the node's children are indexed by the event's `arity` (the result type).
-/

namespace Freigen

/-- One effect event of a first-order signature: an operation together with its input. -/
structure Effect (Op : TpF → TpF → Type) : Type where
  {I : TpF}
  {R : TpF}
  op : Op I R
  input : I.denote

/-- The result arity of an effect event — what the `vis` node branches on. -/
@[reducible] def Effect.arity {Op : TpF → TpF → Type} (e : Effect Op) : Type := e.R.denote

end Freigen
