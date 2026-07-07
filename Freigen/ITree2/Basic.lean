import Freigen.ITree2.PFunctor

namespace Freigen
namespace ITree2

universe u uX uEff uEffIn uEffOut uEff₂
universe uBind uBindIn uBindOut uBranch

/-- One layer of the scoped interaction-tree polynomial. -/
abbrev Step (𝓔 : EffSig.{uEff,uEffIn,uEffOut})
    (𝓑 : BindSig.{u,uBind,uBindIn,uBindOut,uBranch})
    (X : Type u → Type uX) (α : Type u) :=
  (P 𝓔 𝓑).Obj X α

/-- The new indexed-polynomial computation domain. -/
abbrev CompE (𝓔 : EffSig.{uEff,uEffIn,uEffOut})
    (𝓑 : BindSig.{u,uBind,uBindIn,uBindOut,uBranch}) (α : Type u) :=
  (P 𝓔 𝓑).M α

namespace Step

variable {𝓔 : EffSig.{uEff,uEffIn,uEffOut}}
  {𝓑 : BindSig.{u,uBind,uBindIn,uBindOut,uBranch}} {X : Type u → Type uX}

/-- Return step: no recursive children. -/
def ret {α : Type u} (a : α) : Step 𝓔 𝓑 X α :=
  ⟨Pos.ret a, fun h => PEmpty.elim h⟩

/-- Silent step: one child at the ambient result type. -/
def tau {α : Type u} (t : X α) : Step 𝓔 𝓑 X α :=
  ⟨Pos.tau, fun
    | PUnit.unit => t⟩

/-- Failure step: no recursive children. -/
def fail {α : Type u} : Step 𝓔 𝓑 X α :=
  ⟨Pos.fail, fun h => PEmpty.elim h⟩

/-- Effect step: every output branch continues at the ambient result type. -/
def vis {α : Type u} (e : 𝓔.ε) (i : 𝓔.input e) (k : 𝓔.output e → X α) :
    Step 𝓔 𝓑 X α :=
  ⟨Pos.vis e i, fun o => k o.down⟩

/-- Scoped bind step: block children have branch-specific result types; operation-continuation
    children return the ambient result type. -/
def bindEff {α : Type u} (e : 𝓑.ε) (i : 𝓑.input e)
    (blocks : (b : 𝓑.branch e) → X (𝓑.branchOutput e b))
    (k : 𝓑.output e → X α) : Step 𝓔 𝓑 X α :=
  ⟨Pos.bindEff e i, fun
    | Sum.inl b => blocks b.down
    | Sum.inr o => k o.down⟩

end Step

namespace CompE

variable {𝓔 : EffSig.{uEff,uEffIn,uEffOut}}
  {𝓑 : BindSig.{u,uBind,uBindIn,uBindOut,uBranch}}

/-- Build a computation from one scoped interaction-tree step. -/
def mk {α : Type u} (x : Step 𝓔 𝓑 (CompE 𝓔 𝓑) α) : CompE 𝓔 𝓑 α :=
  IxPFunctor.M.ofStep x

/-- Destruct one layer of a computation. -/
def dest {α : Type u} (x : CompE 𝓔 𝓑 α) : Step 𝓔 𝓑 (CompE 𝓔 𝓑) α :=
  IxPFunctor.M.dest x

@[simp] theorem dest_mk {α : Type u} (x : Step 𝓔 𝓑 (CompE 𝓔 𝓑) α) :
    dest (mk x) = x :=
  IxPFunctor.M.dest_ofStep x

/-- Return a value. -/
def ret {α : Type u} (a : α) : CompE 𝓔 𝓑 α :=
  mk (Step.ret a)

/-- Silent step. -/
def tau {α : Type u} (t : CompE 𝓔 𝓑 α) : CompE 𝓔 𝓑 α :=
  mk (Step.tau t)

/-- Failure. -/
def fail {α : Type u} : CompE 𝓔 𝓑 α :=
  mk Step.fail

/-- Ordinary first-order effect. -/
def vis {α : Type u} (e : 𝓔.ε) (i : 𝓔.input e) (k : 𝓔.output e → CompE 𝓔 𝓑 α) :
    CompE 𝓔 𝓑 α :=
  mk (Step.vis e i k)

/-- Scoped bind node.  Blocks are children at their own result types; the operation
    continuation is at the ambient result type. -/
def bindEff {α : Type u} (e : 𝓑.ε) (i : 𝓑.input e)
    (blocks : (b : 𝓑.branch e) → CompE 𝓔 𝓑 (𝓑.branchOutput e b))
    (k : 𝓑.output e → CompE 𝓔 𝓑 α) : CompE 𝓔 𝓑 α :=
  mk (Step.bindEff e i blocks k)

@[simp] theorem dest_ret {α : Type u} (a : α) :
    dest (ret (𝓔 := 𝓔) (𝓑 := 𝓑) a) = Step.ret a := dest_mk _

@[simp] theorem dest_tau {α : Type u} (t : CompE 𝓔 𝓑 α) :
    dest (tau t) = Step.tau t := dest_mk _

@[simp] theorem dest_fail {α : Type u} :
    dest (fail (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α)) = Step.fail := dest_mk _

@[simp] theorem dest_vis {α : Type u} (e : 𝓔.ε) (i : 𝓔.input e)
    (k : 𝓔.output e → CompE 𝓔 𝓑 α) :
    dest (vis e i k) = Step.vis e i k := dest_mk _

@[simp] theorem dest_bindEff {α : Type u} (e : 𝓑.ε) (i : 𝓑.input e)
    (blocks : (b : 𝓑.branch e) → CompE 𝓔 𝓑 (𝓑.branchOutput e b))
    (k : 𝓑.output e → CompE 𝓔 𝓑 α) :
    dest (bindEff e i blocks k) = Step.bindEff e i blocks k := dest_mk _

theorem eq_of_dest_eq {α : Type u} {x y : CompE 𝓔 𝓑 α} (h : dest x = dest y) : x = y :=
  IxPFunctor.M.eq_of_dest_eq h

/-- A destructor view with a real equation for each constructor-headed case. -/
theorem cases_view {α : Type u} (x : CompE 𝓔 𝓑 α) :
    (∃ a, x = ret a) ∨
    x = fail ∨
    (∃ t, x = tau t) ∨
    (∃ (e : 𝓔.ε) (i : 𝓔.input e) (k : 𝓔.output e → CompE 𝓔 𝓑 α), x = vis e i k) ∨
    (∃ (e : 𝓑.ε) (i : 𝓑.input e)
      (blocks : (b : 𝓑.branch e) → CompE 𝓔 𝓑 (𝓑.branchOutput e b))
      (k : 𝓑.output e → CompE 𝓔 𝓑 α), x = bindEff e i blocks k) := by
  obtain ⟨p, c, hd⟩ : ∃ p c, dest x = ⟨p, c⟩ := ⟨_, _, rfl⟩
  match p, c, hd with
  | .ret a, c, hd =>
      exact Or.inl ⟨a, eq_of_dest_eq (by
        rw [hd, dest_ret]
        change (⟨Pos.ret a, c⟩ : Step 𝓔 𝓑 (CompE 𝓔 𝓑) α) =
          ⟨Pos.ret a, fun h => PEmpty.elim h⟩
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext h
        exact PEmpty.elim h)⟩
  | .fail, c, hd =>
      exact Or.inr (Or.inl (eq_of_dest_eq (by
        rw [hd, dest_fail]
        change (⟨Pos.fail, c⟩ : Step 𝓔 𝓑 (CompE 𝓔 𝓑) α) =
          ⟨Pos.fail, fun h => PEmpty.elim h⟩
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext h
        exact PEmpty.elim h)))
  | .tau, c, hd =>
      exact Or.inr (Or.inr (Or.inl ⟨c PUnit.unit, eq_of_dest_eq (by
        rw [hd, dest_tau]
        change (⟨Pos.tau, c⟩ : Step 𝓔 𝓑 (CompE 𝓔 𝓑) α) =
          ⟨Pos.tau, fun
            | PUnit.unit => c PUnit.unit⟩
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext u
        cases u
        rfl)⟩))
  | .vis e i, c, hd =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, i, (fun o => c (ULift.up o)),
        eq_of_dest_eq (by
        rw [hd, dest_vis]
        change (⟨Pos.vis e i, c⟩ : Step 𝓔 𝓑 (CompE 𝓔 𝓑) α) =
          ⟨Pos.vis e i, fun o => c (ULift.up o.down)⟩
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext o
        cases o
        rfl)⟩)))
  | .bindEff e i, c, hd =>
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e, i, (fun b => c (Sum.inl (ULift.up b))),
          (fun o => c (Sum.inr (ULift.up o))), eq_of_dest_eq (by
          rw [hd, dest_bindEff]
          change (⟨Pos.bindEff e i, c⟩ : Step 𝓔 𝓑 (CompE 𝓔 𝓑) α) =
            ⟨Pos.bindEff e i, fun
              | Sum.inl b => c (Sum.inl (ULift.up b.down))
              | Sum.inr o => c (Sum.inr (ULift.up o.down))⟩
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext a
          cases a with
          | inl b =>
              cases b
              rfl
          | inr o =>
              cases o
              rfl)⟩)))

/-- Corecursor specialized to the scoped computation polynomial. -/
def corec {X : Type u → Type uX} (f : (α : Type u) → X α → Step 𝓔 𝓑 X α)
    {α : Type u} (x : X α) : CompE 𝓔 𝓑 α :=
  IxPFunctor.M.corec (P := P 𝓔 𝓑) f x

@[simp] theorem dest_corec {X : Type u → Type uX}
    (f : (α : Type u) → X α → Step 𝓔 𝓑 X α) {α : Type u} (x : X α) :
    dest (corec f x) = (P 𝓔 𝓑).map (fun α => corec f (α := α)) (f α x) :=
  IxPFunctor.M.dest_corec f x

inductive BindState (𝓔 : EffSig.{uEff,uEffIn,uEffOut})
    (𝓑 : BindSig.{u,uBind,uBindIn,uBindOut,uBranch}) (α β : Type u) :
    Type u →
      Type (max (u+1) uEff uEffIn uEffOut uBind uBindIn uBindOut uBranch) where
  | bind : CompE 𝓔 𝓑 α → BindState 𝓔 𝓑 α β β
  | copy {γ : Type u} : CompE 𝓔 𝓑 γ → BindState 𝓔 𝓑 α β γ

def bindCo {α β : Type u} (k : α → CompE 𝓔 𝓑 β) :
    (γ : Type u) → BindState 𝓔 𝓑 α β γ → Step 𝓔 𝓑 (BindState 𝓔 𝓑 α β) γ
  | _, .copy t =>
      match CompE.dest t with
      | ⟨p, c⟩ => ⟨p, fun a => .copy (c a)⟩
  | _, .bind m =>
      match CompE.dest m with
      | ⟨.ret a, _⟩ =>
          match CompE.dest (k a) with
          | ⟨p, c⟩ => ⟨p, fun x => .copy (c x)⟩
      | ⟨.tau, c⟩ => Step.tau (.bind (c PUnit.unit))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.vis e i, c⟩ => Step.vis e i fun o => .bind (c (ULift.up o))
      | ⟨.bindEff e i, c⟩ =>
          Step.bindEff e i
            (fun b => .copy (c (Sum.inl (ULift.up b))))
            (fun o => .bind (c (Sum.inr (ULift.up o))))

/-- Monadic bind: graft at `ret` leaves and continue through operation continuations, but do not
    bind under scoped blocks. -/
def bind {α β : Type u} (m : CompE 𝓔 𝓑 α) (k : α → CompE 𝓔 𝓑 β) :
    CompE 𝓔 𝓑 β :=
  corec (bindCo k) (.bind m)

instance : Monad (CompE 𝓔 𝓑) where
  pure := ret
  bind := bind

@[simp] theorem pure_def {α : Type u} (a : α) : (pure a : CompE 𝓔 𝓑 α) = ret a := rfl

@[simp] theorem bind_def {α β : Type u} (m : CompE 𝓔 𝓑 α) (k : α → CompE 𝓔 𝓑 β) :
    m >>= k = bind m k := rfl

end CompE

/-! ## Effect sums, singleton calls, and guarded recursion

These operations are specialized to signatures whose effect input/output payloads live in the
same universe as computation result indices.  That is the fragment used by `Ast2`'s coded
first-order effects. -/

namespace EffSig

/-- Sum of independent first-order effect signatures. -/
abbrev sum (𝓔 : EffSig.{uEff,uEffIn,uEffOut})
    (𝓕 : EffSig.{uEff₂,uEffIn,uEffOut}) :
    EffSig.{max uEff uEff₂,uEffIn,uEffOut} where
  ε := 𝓔.ε ⊕ 𝓕.ε
  input
    | .inl e => 𝓔.input e
    | .inr e => 𝓕.input e
  output
    | .inl e => 𝓔.output e
    | .inr e => 𝓕.output e

end EffSig

/-- Sum of independent first-order effect signatures. -/
abbrev SumEff := EffSig.sum

/-- The singleton recursive-call effect: one operation, carrying an argument and returning the
    recursive result.  It does not know about the ambient effect signature. -/
abbrev CallEff (σ ρ : Type u) : EffSig.{0,u,u} where
  ε := Unit
  input := fun _ => σ
  output := fun _ => ρ

namespace CompE

variable {𝓔 : EffSig.{uEff,u,u}} {𝓕 : EffSig.{uEff₂,u,u}}
  {𝓑 : BindSig.{u,uBind,uBindIn,uBindOut,uBranch}}

/-- Coalgebra for relabelling effects into the left side of an effect sum. -/
def sumLCo :
    (α : Type u) → CompE 𝓔 𝓑 α → Step (SumEff 𝓔 𝓕) 𝓑 (CompE 𝓔 𝓑) α
  | _, t =>
      match CompE.dest t with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ => Step.tau (c PUnit.unit)
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.vis e i, c⟩ => Step.vis (Sum.inl e) i fun o => c (ULift.up o)
      | ⟨.bindEff e i, c⟩ =>
          Step.bindEff e i
            (fun b => c (Sum.inl (ULift.up b)))
            (fun o => c (Sum.inr (ULift.up o)))

/-- Embed a computation into the left side of an effect sum. -/
def sumL {α : Type u} (t : CompE 𝓔 𝓑 α) : CompE (SumEff 𝓔 𝓕) 𝓑 α :=
  corec sumLCo t

/-- Coalgebra for interpreting call events by rerunning the body behind one `tau`. -/
def interpCo {σ ρ : Type u} (body : σ → CompE (SumEff 𝓔 (CallEff σ ρ)) 𝓑 ρ) :
    (α : Type u) → CompE (SumEff 𝓔 (CallEff σ ρ)) 𝓑 α →
      Step 𝓔 𝓑 (CompE (SumEff 𝓔 (CallEff σ ρ)) 𝓑) α
  | _, t =>
      match CompE.dest t with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ => Step.tau (c PUnit.unit)
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.vis (Sum.inl e) i, c⟩ => Step.vis e i fun o => c (ULift.up o)
      | ⟨.vis (Sum.inr _) s, c⟩ =>
          Step.tau (body s >>= fun o => c (ULift.up o))
      | ⟨.bindEff e i, c⟩ =>
          Step.bindEff e i
            (fun b => c (Sum.inl (ULift.up b)))
            (fun o => c (Sum.inr (ULift.up o)))

/-- Interpret a call-summed computation back into the base signature. -/
def interp {σ ρ α : Type u} (body : σ → CompE (SumEff 𝓔 (CallEff σ ρ)) 𝓑 ρ)
    (t : CompE (SumEff 𝓔 (CallEff σ ρ)) 𝓑 α) : CompE 𝓔 𝓑 α :=
  corec (interpCo body) t

/-- Guarded general recursion by interpreting self-call events. -/
def mrec {σ ρ : Type u} (body : σ → CompE (SumEff 𝓔 (CallEff σ ρ)) 𝓑 ρ) :
    σ → CompE 𝓔 𝓑 ρ :=
  fun s => interp body (body s)

end CompE

end ITree2
end Freigen
