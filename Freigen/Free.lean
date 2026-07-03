import Freigen.ITree.Effect
import Freigen.ITree.Basic

/-!
# `Free`: a free monad over an event signature, with an extensible scoped signature

Two orthogonal extension slots:

* an **event signature** `(ε, br)` — ordinary first-order effects: an event `e : ε` returns a
  `br e`.  Interpreters treat them opaquely (via a handler).  A DSL's events are `Effect Op` for
  a first-order signature `Op : TpF → TpF → Type`; the recursion machinery extends any event
  signature with a call event (`ε ⊕ σ`) — the same sum extension the denotation domain uses.
* `SOp : Type → Type` — **scoped constructs**: `SOp β` is the set of scoped operations whose
  *in-monad block* computes a `β`.  The block is a *positive* recursive occurrence — an ordinary
  inductive.

A `FreeE ε br SOp` value is the **source of truth**.  Its only generic interpreter is `run`:
fold the program into any monad `M`, given a handler for the events and a handler for the scoped
ops.  *How* a particular scoped construct is interpreted (run its block, erase it, …) is
entirely the handler's business — the examples supply their own.

`Free Op SOp` abbreviates the DSL instantiation, and `Free.op` restores the 3-argument surface
(`.op o i k`, packaging the op with its input).  `ofFree` embeds a program into the
interaction-tree domain — generically, so the same embedding serves DSL programs and
call-extended recursion bodies.
-/

namespace Freigen

/-- Free monad over an event signature `(ε, br)` and a scoped signature `SOp`.  `hop s b k`:
    scoped op `s : SOp β`, block `b : FreeE … β` (a full computation in the *same* monad,
    producing the witness), and continuation `k`.  The block is a *positive* recursive
    occurrence. -/
inductive FreeE (ε : Type) (br : ε → Type) (SOp : Type → Type) : Type → Type 1
  | pure {α} : α → FreeE ε br SOp α
  | op   {α} (e : ε) : (br e → FreeE ε br SOp α) → FreeE ε br SOp α
  | hop  {α β} : SOp β → FreeE ε br SOp β → (β → FreeE ε br SOp α) → FreeE ε br SOp α

/-- Free monad over a first-order DSL signature — the source-program surface. -/
abbrev Free (Op : TpF → TpF → Type) (SOp : Type → Type) : Type → Type 1 :=
  FreeE (Effect Op) Effect.arity SOp

/-- Perform op `o` on input `i`, continuing with `k` — the 3-argument surface over the packaged
    event. -/
@[match_pattern]
def Free.op {Op : TpF → TpF → Type} {SOp : Type → Type} {α : Type} {I R : TpF}
    (o : Op I R) (i : I.denote) (k : R.denote → Free Op SOp α) : Free Op SOp α :=
  FreeE.op (Effect.mk o i) k

namespace FreeE
variable {ε : Type} {br : ε → Type} {SOp : Type → Type}

/-- Monadic bind: extends the *continuation* (never the scoped block — binding after a scoped op
    sequences what happens with its result, not the in-block computation). -/
def bind {α γ} : FreeE ε br SOp α → (α → FreeE ε br SOp γ) → FreeE ε br SOp γ
  | .pure a,    f => f a
  | .op e k,    f => .op e (fun r => bind (k r) f)
  | .hop s b k, f => .hop s b (fun x => bind (k x) f)

instance : Monad (FreeE ε br SOp) where
  pure := .pure
  bind := bind

/-- Perform an event, binding its result. -/
def perform (e : ε) : FreeE ε br SOp (br e) := .op e .pure

/-- Right identity: `bind m pure = m`. -/
theorem bind_pure {α} (m : FreeE ε br SOp α) : bind m .pure = m := by
  induction m with
  | pure a => rfl
  | op e c ih => simp only [bind]; exact congrArg (FreeE.op e) (funext ih)
  | hop s b c _ ihc => simp only [bind]; exact congrArg (FreeE.hop s b) (funext ihc)

/-- **The generic interpreter.** Fold a program into a monad `M`, given a handler `ho` for the
    events and a handler `hs` for the scoped ops.  `hs` receives the scoped op *and its
    interpreted block* `M β`, and returns an `M β` — so it may run the block, ignore it, and so
    on; all of that logic lives in the handler, not here. -/
def run {M : Type → Type} [Monad M]
    (ho : (e : ε) → M (br e))
    (hs : {β : Type} → SOp β → M β → M β) :
    {α : Type} → FreeE ε br SOp α → M α
  | _, .pure a    => Pure.pure a
  | _, .op e k    => ho e >>= fun r => run ho hs (k r)
  | _, .hop s b k => hs s (run ho hs b) >>= fun x => run ho hs (k x)

end FreeE

namespace Free
export FreeE (pure hop perform)

/-- `bind` at the DSL surface. -/
abbrev bind {Op : TpF → TpF → Type} {SOp : Type → Type} {α γ}
    (m : Free Op SOp α) (f : α → Free Op SOp γ) : Free Op SOp γ := FreeE.bind m f

/-- Right identity at the DSL surface. -/
theorem bind_pure {Op : TpF → TpF → Type} {SOp : Type → Type} {α} (m : Free Op SOp α) :
    FreeE.bind m .pure = m := FreeE.bind_pure m

end Free

/-- The trivial scoped signature: *no* scoped operations — the plain first-order free monad. -/
abbrev NoScope : Type → Type := fun _ => PEmpty

/-- Embed a `Free` program into the interaction-tree domain: `pure ↦ ret`, an event ↦ `vis`, a
    scoped block runs inline (`bind`).  Generic in the event signature — the same embedding
    serves DSL programs and call-extended recursion bodies. -/
def ofFree {ε : Type} {br : ε → Type} {SOp : Type → Type} :
    {α : Type} → FreeE ε br SOp α → ITree.CompE ε br α
  | _, .pure a    => ITree.ret a
  | _, .op e k    => ITree.vis e (fun x => ofFree (k x))
  | _, .hop _ b k => ITree.bind (ofFree b) (fun x => ofFree (k x))

/-- `ofFree` is a **monad morphism**: it commutes with `bind`. -/
theorem ofFree_bind {ε : Type} {br : ε → Type} {SOp : Type → Type} {α γ : Type}
    (m : FreeE ε br SOp α) (f : α → FreeE ε br SOp γ) :
    ofFree (FreeE.bind m f) = ITree.bind (ofFree m) (fun a => ofFree (f a)) := by
  induction m with
  | pure a => simp only [FreeE.bind, ofFree, ITree.bind_ret]
  | op e c ih =>
      simp only [FreeE.bind, ofFree, ITree.bind_vis]
      exact congrArg _ (funext fun r => ih r f)
  | hop s b c _ ihc =>
      simp only [FreeE.bind, ofFree, ITree.bind_assoc]
      exact congrArg _ (funext fun x => ihc x f)

/-- `ofFree` distributes over a boolean branch. -/
theorem ofFree_cond {ε : Type} {br : ε → Type} {SOp : Type → Type} {α : Type}
    (c : Bool) (t e : FreeE ε br SOp α) :
    ofFree (cond c t e) = cond c (ofFree t) (ofFree e) := by cases c <;> rfl

end Freigen
