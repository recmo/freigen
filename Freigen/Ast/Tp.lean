import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# The object-type universe `Tp` and its reified primitive operations

A small, closed universe of the types the dumb AST may mention (`Bool`/`Nat`/`ZMod n`/`Unit`/`×`/
`Vector`/`Array`/`⊕`/`→`), denoted back into Lean by `Tp.denote`, together with the **reified**
primitive operations:

* `Un`/`Bin` — **total** unary/binary primitives (arithmetic, comparison, field ops, tupling,
  projection, injection), denoting to plain Lean functions;
* `POp` — **partial** (proof-erased) primitives (collection get/set, refinement upcasts), denoting
  to `Option`-valued functions — `none` is the erased proof obligation failing, which the single
  `Code.pop` node turns into a *failing* computation.

Reifying primitives into explicit op nodes — rather than embedding opaque Lean functions — is what
lets the AST spill *typed, inspectable* structure into a target.
-/

namespace Freigen

/-- The universe of object-language types the AST may mention. -/
inductive Tp : Type
  | bool : Tp
  | nat : Tp
  | zmod : Nat → Tp
  | unit : Tp
  | prod : Tp → Tp → Tp
  | fn : Tp → Tp → Tp
  | vec : Tp → Nat → Tp
  | array : Tp → Tp
  | sum : Tp → Tp → Tp
  | fin : Nat → Tp

/-- **First-order** object types — `Tp` minus `fn`.  This is the universe of *effect signatures*
    (`Op : TpF → TpF → Type`): an effect's input/output cannot be a function, which is exactly
    what breaks the `Tp.denote ↔ Comp` circularity — `TpF.denote` is `Op`-independent, so the
    interaction-tree domain (whose event payloads live here) can be defined *before* the full,
    Kleisli-valued `Tp.denote`.  It also keeps the whole effect stack in `Type 0`: signatures
    quantify `TpF` *codes* (data), never host `Type`s. -/
inductive TpF : Type
  | bool : TpF
  | nat : TpF
  | zmod : Nat → TpF
  | unit : TpF
  | prod : TpF → TpF → TpF
  | vec : TpF → Nat → TpF
  | array : TpF → TpF
  | sum : TpF → TpF → TpF
  | fin : Nat → TpF

/-- Denote a first-order object type into Lean (`Op`-independent). -/
@[reducible] def TpF.denote : TpF → Type
  | .bool     => Bool
  | .nat      => Nat
  | .zmod n   => ZMod n
  | .unit     => Unit
  | .prod a b => a.denote × b.denote
  | .vec a n  => Vector a.denote n
  | .array a  => Array a.denote
  | .sum a b  => a.denote ⊕ b.denote
  | .fin n    => Fin n

/-- Embed a first-order type into the full universe. -/
@[reducible] def TpF.tp : TpF → Tp
  | .bool     => .bool
  | .nat      => .nat
  | .zmod n   => .zmod n
  | .unit     => .unit
  | .prod a b => .prod a.tp b.tp
  | .vec a n  => .vec a.tp n
  | .array a  => .array a.tp
  | .sum a b  => .sum a.tp b.tp
  | .fin n    => .fin n

/-- A heterogeneous list: `HList β [i₀, i₁, …]` holds a `β i₀`, a `β i₁`, ….  Used for the
    argument tuples of (multi-argument) function definitions. -/
inductive HList {ι : Type} (β : ι → Type) : List ι → Type
  | nil : HList β []
  | cons {i is} : β i → HList β is → HList β (i :: is)

/-- The first element of a non-empty `HList`. -/
def HList.head {ι : Type} {β : ι → Type} {i is} : HList β (i :: is) → β i
  | .cons x _ => x
/-- All but the first element of a non-empty `HList`. -/
def HList.tail {ι : Type} {β : ι → Type} {i is} : HList β (i :: is) → HList β is
  | .cons _ xs => xs

/-- Unary primitive operations, indexed by (argument, result) object type. -/
inductive Un : Tp → Tp → Type
  | not : Un .bool .bool
  | fst {a b : Tp} : Un (.prod a b) a
  | snd {a b : Tp} : Un (.prod a b) b
  | inl {a b : Tp} : Un a (.sum a b)
  | inr {a b : Tp} : Un b (.sum a b)
  /-- **Total downcast** `v.toArray` : forget a vector's static length. -/
  | toArray {a : Tp} {n : Nat} : Un (.vec a n) (.array a)
  /-- **Total downcast** `i.val` : forget a `Fin`'s bound. -/
  | finVal {n : Nat} : Un (.fin n) .nat

/-- Binary primitive operations, indexed by (left, right, result) object type. -/
inductive Bin : Tp → Tp → Tp → Type
  | add : Bin .nat .nat .nat
  | sub : Bin .nat .nat .nat
  | mul : Bin .nat .nat .nat
  | pow : Bin .nat .nat .nat
  | eq  : Bin .nat .nat .bool
  | lt  : Bin .nat .nat .bool
  | ble : Bin .nat .nat .bool
  | and : Bin .bool .bool .bool
  | or  : Bin .bool .bool .bool
  | addZ {n : Nat} : Bin (.zmod n) (.zmod n) (.zmod n)
  | subZ {n : Nat} : Bin (.zmod n) (.zmod n) (.zmod n)
  | mulZ {n : Nat} : Bin (.zmod n) (.zmod n) (.zmod n)
  /-- Field power with a `Nat` exponent. -/
  | powZ {n : Nat} : Bin (.zmod n) .nat (.zmod n)
  | pair {a b : Tp} : Bin a b (.prod a b)
  /-- **Array push** `xs.push x` — append one element (total). -/
  | push {a : Tp} : Bin (.array a) a (.array a)

/-- **Partial** primitive operations, indexed by (argument list, result) object types.  These are
    the *proof-erased* primitives — collection get/set and refinement upcasts — whose Lean
    counterparts require a proof (an in-bounds index, a size equality) that the AST drops.  Their
    denotation is `Option`-valued (`none` = the erased obligation fails); the single `Code.pop`
    node turns `none` into a failing computation.  Adding a partial primitive = one constructor
    here + one `denote` arm + one `sexpName` arm + one `sc_*` bridging lemma. -/
inductive POp : List Tp → Tp → Type
  /-- **Vector get** `v[i]` (erased: `i < n`). -/
  | vget {a : Tp} {n : Nat} : POp [.vec a n, .nat] a
  /-- **Vector set** `v[i] := x` (erased: `i < n`). -/
  | vset {a : Tp} {n : Nat} : POp [.vec a n, .nat, a] (.vec a n)
  /-- **Array get** `a[i]` (erased: `i < a.size`). -/
  | aget {a : Tp} : POp [.array a, .nat] a
  /-- **Array set** `a[i] := x` (erased: `i < a.size`). -/
  | aset {a : Tp} : POp [.array a, .nat, a] (.array a)
  /-- **Upcast** `array a → vec a n` (erased: `arr.size = n`). -/
  | arrToVec {a : Tp} {n : Nat} : POp [.array a] (.vec a n)
  /-- **Upcast** `nat → fin n` (erased: `m < n`). -/
  | natToFin {n : Nat} : POp [.nat] (.fin n)
  /-- **Strict select** `c ? x : y` — both branches evaluated, the boolean picks.  Total (its
      denotation is always `some`); lives here so pure `if` needs no continuation duplication. -/
  | select {a : Tp} : POp [.bool, a, a] a

end Freigen
