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

@[simp] theorem raw_dest_mk {α : Type u} (x : Step 𝓔 𝓑 (CompE 𝓔 𝓑) α) :
    IxPFunctor.M.dest (mk x) = x :=
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

theorem corec_copy {α β γ : Type u} (k : α → CompE 𝓔 𝓑 β) (t : CompE 𝓔 𝓑 γ) :
    IxPFunctor.M.corec (P := P 𝓔 𝓑) (bindCo k) (.copy t) = t := by
  refine IxPFunctor.M.bisim (P := P 𝓔 𝓑)
    (fun γ x y =>
      x = IxPFunctor.M.corec (P := P 𝓔 𝓑) (bindCo k)
        (.copy y : BindState 𝓔 𝓑 α β γ)) ?_ _ _ rfl
  intro γ x y hxy
  subst hxy
  obtain ⟨p, c, hy⟩ : ∃ p c, dest y = ⟨p, c⟩ := ⟨_, _, rfl⟩
  refine ⟨p, fun a => IxPFunctor.M.corec (P := P 𝓔 𝓑) (bindCo k) (.copy (c a)),
    c, ?_, hy, fun _ => rfl⟩
  rw [IxPFunctor.M.dest_corec]
  simp only [bindCo]
  rw [hy]
  rfl

@[simp] theorem bind_ret {α β : Type u} (a : α) (k : α → CompE 𝓔 𝓑 β) :
    bind (ret a) k = k a := by
  apply eq_of_dest_eq
  obtain ⟨p, c, hk⟩ : ∃ p c, dest (k a) = ⟨p, c⟩ := ⟨_, _, rfl⟩
  rw [bind, corec]
  change IxPFunctor.M.dest
      (IxPFunctor.M.corec (P := P 𝓔 𝓑) (bindCo k) (.bind (ret a))) = dest (k a)
  rw [IxPFunctor.M.dest_corec]
  simp only [bindCo, ret]
  rw [dest_mk]
  simp only [Step.ret, IxPFunctor.map, corec_copy]

@[simp] theorem bind_tau {α β : Type u} (t : CompE 𝓔 𝓑 α) (k : α → CompE 𝓔 𝓑 β) :
    bind (tau t) k = tau (bind t k) := by
  apply eq_of_dest_eq
  rw [bind, corec]
  change IxPFunctor.M.dest
      (IxPFunctor.M.corec (P := P 𝓔 𝓑) (bindCo k) (.bind (tau t))) =
    dest (tau (bind t k))
  rw [IxPFunctor.M.dest_corec]
  simp only [bindCo, tau]
  rw [dest_mk, dest_mk]
  simp only [Step.tau, IxPFunctor.map, bind, corec]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext x
  cases x
  rfl

@[simp] theorem bind_fail {α β : Type u} (k : α → CompE 𝓔 𝓑 β) :
    bind (fail : CompE 𝓔 𝓑 α) k = fail := by
  apply eq_of_dest_eq
  rw [bind, corec]
  change IxPFunctor.M.dest
      (IxPFunctor.M.corec (P := P 𝓔 𝓑) (bindCo k)
        (.bind (fail : CompE 𝓔 𝓑 α))) =
    dest (fail : CompE 𝓔 𝓑 β)
  rw [IxPFunctor.M.dest_corec]
  simp only [bindCo, fail]
  rw [dest_mk, dest_mk]
  simp only [Step.fail, IxPFunctor.map]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext h
  exact PEmpty.elim h

@[simp] theorem bind_vis {α β : Type u} (e : 𝓔.ε) (i : 𝓔.input e)
    (c : 𝓔.output e → CompE 𝓔 𝓑 α) (k : α → CompE 𝓔 𝓑 β) :
    bind (vis e i c) k = vis e i (fun o => bind (c o) k) := by
  apply eq_of_dest_eq
  rw [bind, corec]
  change IxPFunctor.M.dest
      (IxPFunctor.M.corec (P := P 𝓔 𝓑) (bindCo k) (.bind (vis e i c))) =
    dest (vis e i (fun o => bind (c o) k))
  rw [IxPFunctor.M.dest_corec]
  simp only [bindCo, vis]
  rw [dest_mk, dest_mk]
  simp only [Step.vis, IxPFunctor.map, bind, corec]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext x
  cases x
  rfl

@[simp] theorem bind_bindEff {α β : Type u} (e : 𝓑.ε) (i : 𝓑.input e)
    (blocks : (b : 𝓑.branch e) → CompE 𝓔 𝓑 (𝓑.branchOutput e b))
    (c : 𝓑.output e → CompE 𝓔 𝓑 α) (k : α → CompE 𝓔 𝓑 β) :
    bind (bindEff e i blocks c) k = bindEff e i blocks (fun o => bind (c o) k) := by
  apply eq_of_dest_eq
  rw [bind, corec]
  change IxPFunctor.M.dest
      (IxPFunctor.M.corec (P := P 𝓔 𝓑) (bindCo k)
        (.bind (bindEff e i blocks c))) =
    dest (bindEff e i blocks (fun o => bind (c o) k))
  rw [IxPFunctor.M.dest_corec]
  simp only [bindCo, bindEff]
  rw [dest_mk, dest_mk]
  simp only [Step.bindEff, IxPFunctor.map, bind, corec]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext x
  cases x with
  | inl b =>
      cases b
      exact corec_copy k (blocks _)
  | inr o =>
      cases o
      rfl

private def BindRightRel (γ : Type u) (x y : CompE 𝓔 𝓑 γ) : Prop :=
  (∃ m : CompE 𝓔 𝓑 γ, x = bind m ret ∧ y = m) ∨ x = y

theorem bind_ret_right {α : Type u} (m : CompE 𝓔 𝓑 α) : bind m ret = m := by
  refine IxPFunctor.M.bisim (P := P 𝓔 𝓑) BindRightRel ?_ _ _ (Or.inl ⟨m, rfl, rfl⟩)
  intro γ x y hxy
  rcases hxy with ⟨m, hx, hy⟩ | hxy
  ·
      rw [hx, hy]
      rcases cases_view m with
        ⟨a, hm⟩ | hm | ⟨t, hm⟩ | ⟨e, i, c, hm⟩ |
        ⟨e, i, blocks, c, hm⟩
      · rw [hm, bind_ret]
        exact ⟨Pos.ret a, _, _, by rw [ret, raw_dest_mk]; rfl, by rw [ret, raw_dest_mk]; rfl,
          fun h => PEmpty.elim h⟩
      · rw [hm, bind_fail]
        exact ⟨Pos.fail, _, _, by rw [fail, raw_dest_mk]; rfl, by rw [fail, raw_dest_mk]; rfl,
          fun h => PEmpty.elim h⟩
      · rw [hm, bind_tau]
        exact ⟨Pos.tau, _, _, dest_tau _, dest_tau _, fun _ => Or.inl ⟨t, rfl, rfl⟩⟩
      · rw [hm, bind_vis]
        exact ⟨Pos.vis e i, _, _, dest_vis _ _ _, dest_vis _ _ _,
          fun o => Or.inl ⟨c o.down, rfl, rfl⟩⟩
      · rw [hm, bind_bindEff]
        exact ⟨Pos.bindEff e i, _, _, dest_bindEff _ _ _ _, dest_bindEff _ _ _ _,
          fun
            | Sum.inl b => Or.inr rfl
            | Sum.inr o => Or.inl ⟨c o.down, rfl, rfl⟩⟩
  ·
      rw [hxy]
      obtain ⟨p, c, hd⟩ :
          ∃ (p : (P 𝓔 𝓑).Pos γ)
            (c : (a : (P 𝓔 𝓑).Ar p) → CompE 𝓔 𝓑 ((P 𝓔 𝓑).next p a)),
            dest y = ⟨p, c⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c, c, hd, hd, fun a => Or.inr rfl⟩

private inductive BindAssocRel {α β γ : Type u}
    (k : α → CompE 𝓔 𝓑 β) (h : β → CompE 𝓔 𝓑 γ) :
    (δ : Type u) → CompE 𝓔 𝓑 δ → CompE 𝓔 𝓑 δ → Prop where
  | root {x y : CompE 𝓔 𝓑 γ} (m : CompE 𝓔 𝓑 α)
      (hx : x = bind (bind m k) h)
      (hy : y = bind m fun a => bind (k a) h) : BindAssocRel k h γ x y
  | eq {δ : Type u} {x y : CompE 𝓔 𝓑 δ} (hxy : x = y) : BindAssocRel k h δ x y

theorem bind_assoc {α β γ : Type u} (m : CompE 𝓔 𝓑 α)
    (k : α → CompE 𝓔 𝓑 β) (h : β → CompE 𝓔 𝓑 γ) :
    bind (bind m k) h = bind m (fun a => bind (k a) h) := by
  refine IxPFunctor.M.bisim (P := P 𝓔 𝓑) (BindAssocRel k h) ?_ _ _ (.root m rfl rfl)
  intro δ x y hxy
  cases hxy with
  | root m hx hy =>
      cases hx
      cases hy
      rcases cases_view m with
        ⟨a, hm⟩ | hm | ⟨t, hm⟩ | ⟨e, i, c, hm⟩ |
        ⟨e, i, blocks, c, hm⟩
      · rw [hm, bind_ret, bind_ret]
        obtain ⟨p, c', hd'⟩ : ∃ p c', dest (bind (k a) h) = ⟨p, c'⟩ := ⟨_, _, rfl⟩
        exact ⟨p, c', c', hd', hd', fun a => .eq rfl⟩
      · rw [hm, bind_fail, bind_fail, bind_fail]
        exact ⟨Pos.fail, _, _, by rw [fail, raw_dest_mk]; rfl, by rw [fail, raw_dest_mk]; rfl,
          fun h => PEmpty.elim h⟩
      · rw [hm, bind_tau, bind_tau, bind_tau]
        exact ⟨Pos.tau, _, _, dest_tau _, dest_tau _, fun _ => .root t rfl rfl⟩
      · rw [hm, bind_vis, bind_vis, bind_vis]
        exact ⟨Pos.vis e i, _, _, dest_vis _ _ _, dest_vis _ _ _,
          fun o => .root (c o.down) rfl rfl⟩
      · rw [hm, bind_bindEff, bind_bindEff, bind_bindEff]
        exact ⟨Pos.bindEff e i, _, _, dest_bindEff _ _ _ _, dest_bindEff _ _ _ _,
          fun
            | Sum.inl b => .eq rfl
            | Sum.inr o => .root (c o.down) rfl rfl⟩
  | eq hxy =>
      cases hxy
      obtain ⟨p, c, hd⟩ :
          ∃ (p : (P 𝓔 𝓑).Pos δ)
            (c : (a : (P 𝓔 𝓑).Ar p) → CompE 𝓔 𝓑 ((P 𝓔 𝓑).next p a)),
            dest x = ⟨p, c⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c, c, hd, hd, fun a => .eq rfl⟩

instance : LawfulMonad (CompE 𝓔 𝓑) :=
  LawfulMonad.mk' _
    (fun m => bind_ret_right m)
    (fun a k => bind_ret a k)
    (fun m k h => bind_assoc m k h)

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
