import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Defs
import Lean

inductive Free (F : Type u → Type v) (α : Type u): Type _
| Pure : α → Free F α
| Impure : ∀{x}, F x -> (x -> Free F α) -> Free F α

def freeBind {F : Type u → Type v} {α β : Type u} (a : Free F α) (f : α → Free F β) : Free F β :=
  match a with
  | Free.Pure x => f x
  | Free.Impure a f' => Free.Impure a (fun x => freeBind (f' x) f)

instance {F : Type u → Type v} : Monad (Free F) where
  pure := Free.Pure
  bind := freeBind

def foldFree [Functor F] [Monad M] (x : Free F α) (f : ∀{x}, F x → M x): M α := match x with
  | Free.Pure x => pure x
  | Free.Impure a f' => f a >>= fun x => foldFree (f' x) f

inductive CircuitF β
| Hint {α γ: Type} : α → (α → γ) → (γ -> β) -> CircuitF β
| Assert : Bool → β → CircuitF β

instance : Functor CircuitF where
  map f a := match a with
    | CircuitF.Hint a body k => CircuitF.Hint a body (f ∘ k)
    | CircuitF.Assert b c => CircuitF.Assert b (f c)

def Circuit := Free CircuitF

instance : Monad Circuit := inferInstanceAs $ Monad (Free CircuitF)

def Circuit.assert (b : Bool) : Circuit Unit := Free.Impure (CircuitF.Assert b ()) pure

def Circuit.hint {α β: Type} (a : α) (body: α → β) : Circuit β := Free.Impure (CircuitF.Hint a body id) pure

def ContProp (t : Type) : Type := (t → Prop) → Prop

instance : Monad ContProp where
  pure p := fun k => k p
  bind p f := fun g => p (fun x => f x g)

def Circuit.assignable {α} [DecidableEq α] (c : Circuit α) (k : α → Prop) : Prop := foldFree (M:=ContProp) c (fun a => match a with
  | CircuitF.Hint _ _ cont => fun k => ∃a, k (cont a)
  | CircuitF.Assert b c => fun k => b ∧ k c
) k

def exampleCircuit1 (a: BitVec 32) (as: Vector (BitVec 32) 32): Circuit Unit := do
  let idx ← Circuit.hint (a, as) fun (a, as) => as.finIdxOf? a |>.getD 0
  Circuit.assert (as[idx] = a)

def exampleCircuit2 (a b : Nat): Circuit Nat := do
  match a with
  | 0 => pure 0
  | Nat.succ a => do
    let rec ← exampleCircuit2 a b
    let rec2 ← exampleCircuit2 a b
    pure (rec + rec2)

def CompiledOf2 (_x : α → β → Circuit γ) : Type := Unit

open Lean Lean.Meta

/-- If `e` is `x >>= f` in monad `wantedM`, return `(x, f)`. -/
def matchBind? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match e.getAppFnArgs with
  | (``Bind.bind, #[_m, _inst, _α, _β, x, f]) =>
      return some (x, f)
  | _ => return none

open Lean Lean.Meta in
/-- Like `unfoldDefinition?`, but returns the *raw* stored value of the head
    constant (with `brecOn`/`WellFounded.fix` encoding intact, smart unfolding
    bypassed), beta-reduced against any arguments. `none` if the head isn't a
    constant carrying a value. -/
def unfoldRaw? (e : Expr) : MetaM (Option Expr) := do
  let .const name us := e.getAppFn | return none
  let some info := (← getEnv).find? name | return none
  let some val := info.value? | return none
  let val := val.instantiateLevelParams info.levelParams us
  return some (val.beta e.getAppArgs)

elab "compile" : tactic => Lean.Elab.Tactic.withMainContext do
  let goalType ← Lean.Elab.Tactic.getMainTarget
  dbg_trace f!"goal type: {goalType}"
  match_expr goalType with
  | CompiledOf2 in₁ in₂ out term => do
    dbg_trace f!"in₁: {←Lean.Meta.ppExpr in₁}"
    dbg_trace f!"in₂: {←Lean.Meta.ppExpr in₂}"
    dbg_trace f!"out: {←Lean.Meta.ppExpr out}"
    dbg_trace f!"term: {←Lean.Meta.ppExpr term}"
    let some term ← Lean.Meta.withTransparency .all (unfoldRaw? term)
      | throwError "could not unfold {←Lean.Meta.ppExpr term}"
    dbg_trace f!"unfolded: {←Lean.Meta.ppExpr term}"
    let (as, bs, body) ← Lean.Meta.lambdaMetaTelescope term
    dbg_trace f!"body: {←Lean.Meta.ppExpr body}"
    dbg_trace f!"body: {body}"
  | _ =>
    dbg_trace f!"not a CompiledOf2"

  dbg_trace f!"goal type: {←Lean.Meta.ppExpr goalType}"

#check Nat.brecOn

#print exampleCircuit2._f


-- WIP: the `compile` tactic doesn't yet close this goal (leaves an unsolved
-- goal), which breaks the build. Commented out for now.
-- def ex1 : CompiledOf2 exampleCircuit2 := by compile

#print Nat.below
