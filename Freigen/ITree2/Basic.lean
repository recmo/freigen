import Freigen.ITree2.PFunctor

namespace Freigen
namespace ITree2

universe u v

/-- One layer of the scoped interaction-tree polynomial at internal result label `i`. -/
abbrev Step (𝓔 : EffSig.{u}) (𝓑 : BindSig.{u}) (α : Type u)
    (X : Ix 𝓑 → Type v) (i : Ix 𝓑) :=
  (P 𝓔 𝓑 α).Obj X i

/-- The internal tree family.  The public computation type is the `.normal` fiber. -/
abbrev Tree (𝓔 : EffSig.{u}) (𝓑 : BindSig.{u}) (α : Type u) (i : Ix 𝓑) :=
  (P 𝓔 𝓑 α).M i

/-- Public scoped interaction trees. -/
abbrev CompE (𝓔 : EffSig.{u}) (𝓑 : BindSig.{u}) (α : Type u) :=
  Tree 𝓔 𝓑 α .normal

/-- Internal block fiber for a scoped operation branch. -/
abbrev BlockE (𝓔 : EffSig.{u}) (𝓑 : BindSig.{u}) (α : Type u)
    (e : 𝓑.ε) (b : 𝓑.branch e) :=
  Tree 𝓔 𝓑 α (.block e b)

namespace Step

variable {𝓔 : EffSig.{u}} {𝓑 : BindSig.{u}} {α : Type u}
  {X : Ix 𝓑 → Type v}

/-- Return step: no recursive children. -/
def ret {i : Ix 𝓑} (a : result 𝓑 α i) : Step 𝓔 𝓑 α X i :=
  ⟨Pos.ret a, fun h => nomatch h⟩

/-- Silent step: one child at the ambient internal label. -/
def tau {i : Ix 𝓑} (t : X i) : Step 𝓔 𝓑 α X i :=
  ⟨Pos.tau, fun
    | Ar.tau => t⟩

/-- Failure step: no recursive children. -/
def fail {i : Ix 𝓑} : Step 𝓔 𝓑 α X i :=
  ⟨Pos.fail, fun h => nomatch h⟩

/-- Effect step: every output branch continues at the ambient internal label. -/
def vis {i : Ix 𝓑} (e : 𝓔.ε) (input : 𝓔.input e) (k : 𝓔.output e → X i) :
    Step 𝓔 𝓑 α X i :=
  ⟨Pos.vis e input, fun
    | Ar.vis o => k o⟩

/-- Scoped bind step: block children jump to their block labels; operation-continuation
    children stay at the ambient internal label. -/
def bindEff {i : Ix 𝓑} (e : 𝓑.ε) (input : 𝓑.input e)
    (blocks : (b : 𝓑.branch e) → X (.block e b))
    (k : 𝓑.output e → X i) : Step 𝓔 𝓑 α X i :=
  ⟨Pos.bindEff e input, fun
    | Ar.block b => blocks b
    | Ar.cont o => k o⟩

end Step

namespace CompE

variable {𝓔 : EffSig.{u}} {𝓑 : BindSig.{u}}

set_option backward.isDefEq.respectTransparency false

/-- Build an internal tree from one scoped interaction-tree step. -/
def mkAt {α : Type u} {i : Ix 𝓑} (x : Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) i) :
    Tree 𝓔 𝓑 α i :=
  IxPFunctor.M.ofStep x

/-- Destruct one layer of an internal tree. -/
def destAt {α : Type u} {i : Ix 𝓑} (x : Tree 𝓔 𝓑 α i) :
    Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) i :=
  IxPFunctor.M.dest x

/-- Build a public computation from one normal step. -/
def mk {α : Type u} (x : Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) .normal) : CompE 𝓔 𝓑 α :=
  mkAt x

/-- Destruct one layer of a public computation. -/
def dest {α : Type u} (x : CompE 𝓔 𝓑 α) :
    Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) .normal :=
  destAt x

@[simp] theorem dest_mkAt {α : Type u} {i : Ix 𝓑}
    (x : Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) i) : destAt (mkAt x) = x :=
  IxPFunctor.M.dest_ofStep x

@[simp] theorem raw_dest_mkAt {α : Type u} {i : Ix 𝓑}
    (x : Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) i) : IxPFunctor.M.dest (mkAt x) = x :=
  IxPFunctor.M.dest_ofStep x

@[simp] theorem dest_mk {α : Type u} (x : Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) .normal) :
    dest (mk x) = x :=
  dest_mkAt x

/-- Return a value at an internal result label. -/
def retAt {α : Type u} {i : Ix 𝓑} (a : result 𝓑 α i) : Tree 𝓔 𝓑 α i :=
  mkAt (Step.ret a)

/-- Return a public value. -/
def ret {α : Type u} (a : α) : CompE 𝓔 𝓑 α :=
  retAt (i := .normal) a

/-- Silent internal step. -/
def tauAt {α : Type u} {i : Ix 𝓑} (t : Tree 𝓔 𝓑 α i) : Tree 𝓔 𝓑 α i :=
  mkAt (Step.tau t)

/-- Silent public step. -/
def tau {α : Type u} (t : CompE 𝓔 𝓑 α) : CompE 𝓔 𝓑 α :=
  tauAt t

/-- Internal failure. -/
def failAt {α : Type u} {i : Ix 𝓑} : Tree 𝓔 𝓑 α i :=
  mkAt Step.fail

/-- Public failure. -/
def fail {α : Type u} : CompE 𝓔 𝓑 α :=
  failAt (i := .normal)

/-- Ordinary first-order effect at an internal result label. -/
def visAt {α : Type u} {i : Ix 𝓑} (e : 𝓔.ε) (input : 𝓔.input e)
    (k : 𝓔.output e → Tree 𝓔 𝓑 α i) : Tree 𝓔 𝓑 α i :=
  mkAt (Step.vis e input k)

/-- Ordinary first-order effect. -/
def vis {α : Type u} (e : 𝓔.ε) (input : 𝓔.input e)
    (k : 𝓔.output e → CompE 𝓔 𝓑 α) : CompE 𝓔 𝓑 α :=
  visAt e input k

/-- Internal scoped bind node. -/
def bindEffAt {α : Type u} {i : Ix 𝓑} (e : 𝓑.ε) (input : 𝓑.input e)
    (blocks : (b : 𝓑.branch e) → BlockE 𝓔 𝓑 α e b)
    (k : 𝓑.output e → Tree 𝓔 𝓑 α i) : Tree 𝓔 𝓑 α i :=
  mkAt (Step.bindEff e input blocks k)

@[simp] theorem dest_retAt {α : Type u} {i : Ix 𝓑} (a : result 𝓑 α i) :
    destAt (retAt (𝓔 := 𝓔) (𝓑 := 𝓑) a) = Step.ret a := dest_mkAt _

@[simp] theorem dest_ret {α : Type u} (a : α) :
    dest (ret (𝓔 := 𝓔) (𝓑 := 𝓑) a) = Step.ret a := dest_mkAt _

@[simp] theorem dest_tauAt {α : Type u} {i : Ix 𝓑} (t : Tree 𝓔 𝓑 α i) :
    destAt (tauAt t) = Step.tau t := dest_mkAt _

@[simp] theorem dest_tau {α : Type u} (t : CompE 𝓔 𝓑 α) :
    dest (tau t) = Step.tau t := dest_mkAt _

@[simp] theorem dest_failAt {α : Type u} {i : Ix 𝓑} :
    destAt (failAt (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (i := i)) = Step.fail := dest_mkAt _

@[simp] theorem dest_fail {α : Type u} :
    dest (fail (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α)) = Step.fail := dest_mkAt _

@[simp] theorem dest_visAt {α : Type u} {i : Ix 𝓑} (e : 𝓔.ε) (input : 𝓔.input e)
    (k : 𝓔.output e → Tree 𝓔 𝓑 α i) :
    destAt (visAt e input k) = Step.vis e input k := dest_mkAt _

@[simp] theorem dest_vis {α : Type u} (e : 𝓔.ε) (input : 𝓔.input e)
    (k : 𝓔.output e → CompE 𝓔 𝓑 α) :
    dest (vis e input k) = Step.vis e input k := dest_mkAt _

@[simp] theorem dest_bindEffAt {α : Type u} {i : Ix 𝓑} (e : 𝓑.ε) (input : 𝓑.input e)
    (blocks : (b : 𝓑.branch e) → BlockE 𝓔 𝓑 α e b)
    (k : 𝓑.output e → Tree 𝓔 𝓑 α i) :
    destAt (bindEffAt e input blocks k) = Step.bindEff e input blocks k := dest_mkAt _

theorem eq_of_destAt_eq {α : Type u} {i : Ix 𝓑} {x y : Tree 𝓔 𝓑 α i}
    (h : destAt x = destAt y) : x = y :=
  IxPFunctor.M.eq_of_dest_eq h

theorem eq_of_dest_eq {α : Type u} {x y : CompE 𝓔 𝓑 α} (h : dest x = dest y) : x = y :=
  eq_of_destAt_eq h

/-- Corecursor specialized to the scoped computation polynomial. -/
def corecAt {α : Type u} {X : Ix 𝓑 → Type v}
    (f : (i : Ix 𝓑) → X i → Step 𝓔 𝓑 α X i) {i : Ix 𝓑} (x : X i) :
    Tree 𝓔 𝓑 α i :=
  IxPFunctor.M.corec (P := P 𝓔 𝓑 α) f x

@[simp] theorem dest_corecAt {α : Type u} {X : Ix 𝓑 → Type v}
    (f : (i : Ix 𝓑) → X i → Step 𝓔 𝓑 α X i) {i : Ix 𝓑} (x : X i) :
    destAt (corecAt f x) = (P 𝓔 𝓑 α).map (fun i => corecAt f (i := i)) (f i x) :=
  IxPFunctor.M.dest_corec f x

@[simp] theorem raw_dest_corecAt {α : Type u} {X : Ix 𝓑 → Type v}
    (f : (i : Ix 𝓑) → X i → Step 𝓔 𝓑 α X i) {i : Ix 𝓑} (x : X i) :
    IxPFunctor.M.dest (corecAt f x) =
      (P 𝓔 𝓑 α).map (fun i => corecAt f (i := i)) (f i x) :=
  IxPFunctor.M.dest_corec f x

private inductive RelabelBlockState (𝓔 : EffSig.{u}) (𝓑 : BindSig.{u}) (α β : Type u) :
    Ix 𝓑 → Type u where
  | block {e : 𝓑.ε} {b : 𝓑.branch e} :
      BlockE 𝓔 𝓑 α e b → RelabelBlockState 𝓔 𝓑 α β (.block e b)

/-- Coalgebra relabelling a block fiber from ambient normal result `α` to `β`. -/
private def relabelBlockCo {α β : Type u} :
    (i : Ix 𝓑) → RelabelBlockState 𝓔 𝓑 α β i →
      Step 𝓔 𝓑 β (RelabelBlockState 𝓔 𝓑 α β) i
  | .block e₀ b₀, .block t =>
      match destAt t with
      | ⟨.ret a, _⟩ =>
          Step.ret (𝓔 := 𝓔) (𝓑 := 𝓑) (α := β) (i := .block e₀ b₀) a
      | ⟨.tau, c⟩ => Step.tau (.block (c Ar.tau : BlockE 𝓔 𝓑 α e₀ b₀))
      | ⟨.fail, _⟩ =>
          Step.fail (𝓔 := 𝓔) (𝓑 := 𝓑) (α := β) (i := .block e₀ b₀)
      | ⟨.vis e input, c⟩ =>
          Step.vis e input fun o => .block (c (Ar.vis o) : BlockE 𝓔 𝓑 α e₀ b₀)
      | ⟨.bindEff e input, c⟩ =>
          Step.bindEff e input
            (fun b => .block (c (Ar.block b) : BlockE 𝓔 𝓑 α e b))
            (fun o => .block (c (Ar.cont o) : BlockE 𝓔 𝓑 α e₀ b₀))

/-- Relabel a block tree across a change of the public normal result type. -/
def relabelBlock {α β : Type u} {e : 𝓑.ε} {b : 𝓑.branch e}
    (t : BlockE 𝓔 𝓑 α e b) : BlockE 𝓔 𝓑 β e b :=
  corecAt (𝓔 := 𝓔) (𝓑 := 𝓑) (α := β) (relabelBlockCo (α := α) (β := β))
    (RelabelBlockState.block t)

private inductive AsBlockState (𝓔 : EffSig.{u}) (𝓑 : BindSig.{u}) (α : Type u)
    (root : 𝓑.ε) (br : 𝓑.branch root) :
    Ix 𝓑 → Type u where
  | normal :
      CompE 𝓔 𝓑 (𝓑.branchOutput root br) → AsBlockState 𝓔 𝓑 α root br (.block root br)
  | block {e : 𝓑.ε} {b : 𝓑.branch e} :
      BlockE 𝓔 𝓑 (𝓑.branchOutput root br) e b → AsBlockState 𝓔 𝓑 α root br (.block e b)

/-- Coalgebra embedding a public computation as a scoped block. -/
private def asBlockCo {α : Type u} (root : 𝓑.ε) (br : 𝓑.branch root) :
    (i : Ix 𝓑) → AsBlockState 𝓔 𝓑 α root br i →
      Step 𝓔 𝓑 α (AsBlockState 𝓔 𝓑 α root br) i
  | .block _ _, .normal t =>
      match dest t with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ => Step.tau (.normal (c Ar.tau : CompE 𝓔 𝓑 (𝓑.branchOutput root br)))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.vis e input, c⟩ =>
          Step.vis e input fun o =>
            .normal (c (Ar.vis o) : CompE 𝓔 𝓑 (𝓑.branchOutput root br))
      | ⟨.bindEff e input, c⟩ =>
          Step.bindEff e input
            (fun b => .block (c (Ar.block b) : BlockE 𝓔 𝓑 (𝓑.branchOutput root br) e b))
            (fun o => .normal (c (Ar.cont o) : CompE 𝓔 𝓑 (𝓑.branchOutput root br)))
  | .block e₀ b₀, .block t =>
      match destAt t with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ =>
          Step.tau (.block (c Ar.tau : BlockE 𝓔 𝓑 (𝓑.branchOutput root br) e₀ b₀))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.vis e input, c⟩ =>
          Step.vis e input fun o =>
            .block (c (Ar.vis o) : BlockE 𝓔 𝓑 (𝓑.branchOutput root br) e₀ b₀)
      | ⟨.bindEff e input, c⟩ =>
          Step.bindEff e input
            (fun b => .block (c (Ar.block b) : BlockE 𝓔 𝓑 (𝓑.branchOutput root br) e b))
            (fun o => .block (c (Ar.cont o) : BlockE 𝓔 𝓑 (𝓑.branchOutput root br) e₀ b₀))

/-- Embed a public computation returning a branch result as the corresponding internal block. -/
def asBlock {α : Type u} {e : 𝓑.ε} {b : 𝓑.branch e}
    (t : CompE 𝓔 𝓑 (𝓑.branchOutput e b)) : BlockE 𝓔 𝓑 α e b :=
  corecAt (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (asBlockCo (α := α) e b)
    (AsBlockState.normal t)

/-- Public scoped bind node.  Public block computations are embedded into the corresponding
    internal block fibers. -/
def bindEff {α : Type u} (e : 𝓑.ε) (input : 𝓑.input e)
    (blocks : (b : 𝓑.branch e) → CompE 𝓔 𝓑 (𝓑.branchOutput e b))
    (k : 𝓑.output e → CompE 𝓔 𝓑 α) : CompE 𝓔 𝓑 α :=
  bindEffAt e input (fun b => asBlock (blocks b)) k

@[simp] theorem dest_bindEff {α : Type u} (e : 𝓑.ε) (input : 𝓑.input e)
    (blocks : (b : 𝓑.branch e) → CompE 𝓔 𝓑 (𝓑.branchOutput e b))
    (k : 𝓑.output e → CompE 𝓔 𝓑 α) :
    dest (bindEff e input blocks k) =
      Step.bindEff e input (fun b => asBlock (blocks b)) k := dest_mkAt _

/-- A destructor view for every internal result label.  At block labels, `ret` returns the
    branch result computed from the label. -/
theorem cases_viewAt {α : Type u} {i : Ix 𝓑} (x : Tree 𝓔 𝓑 α i) :
    (∃ a : result 𝓑 α i, x = retAt a) ∨
    x = failAt ∨
    (∃ t : Tree 𝓔 𝓑 α i, x = tauAt t) ∨
    (∃ (e : 𝓔.ε) (input : 𝓔.input e) (k : 𝓔.output e → Tree 𝓔 𝓑 α i),
      x = visAt e input k) ∨
    (∃ (e : 𝓑.ε) (input : 𝓑.input e)
      (blocks : (b : 𝓑.branch e) → BlockE 𝓔 𝓑 α e b)
      (k : 𝓑.output e → Tree 𝓔 𝓑 α i), x = bindEffAt e input blocks k) := by
  obtain ⟨p, c, hd⟩ : ∃ p c, destAt x = ⟨p, c⟩ := ⟨_, _, rfl⟩
  match p, c, hd with
  | .ret a, c, hd =>
      exact Or.inl ⟨a, eq_of_destAt_eq (by
        rw [hd, dest_retAt]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext h
        nomatch h)⟩
  | .fail, c, hd =>
      exact Or.inr (Or.inl (eq_of_destAt_eq (by
        rw [hd, dest_failAt]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext h
        nomatch h)))
  | .tau, c, hd =>
      exact Or.inr (Or.inr (Or.inl ⟨c Ar.tau, eq_of_destAt_eq (by
        rw [hd, dest_tauAt]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext h
        cases h
        rfl)⟩))
  | .vis e input, c, hd =>
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e, input, (fun o => c (Ar.vis o)), eq_of_destAt_eq (by
          rw [hd, dest_visAt]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext h
          cases h
          rfl)⟩)))
  | .bindEff e input, c, hd =>
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e, input, (fun b => (c (Ar.block b) : BlockE 𝓔 𝓑 α e b)),
          (fun o => c (Ar.cont o)),
          eq_of_destAt_eq (by
            rw [hd]
            change ⟨Pos.bindEff e input, c⟩ =
              destAt (bindEffAt e input
                (fun b => (c (Ar.block b) : BlockE 𝓔 𝓑 α e b))
                (fun o => c (Ar.cont o)))
            rw [dest_bindEffAt]
            refine Sigma.ext rfl ?_
            apply heq_of_eq
            funext h
            cases h <;> rfl)⟩)))

/-- A destructor view for public computations.  Scoped block children are exposed in the
    internal block fibers, which is the form used by the monad laws. -/
theorem cases_view {α : Type u} (x : CompE 𝓔 𝓑 α) :
    (∃ a, x = ret a) ∨
    x = fail ∨
    (∃ t, x = tau t) ∨
    (∃ (e : 𝓔.ε) (input : 𝓔.input e) (k : 𝓔.output e → CompE 𝓔 𝓑 α),
      x = vis e input k) ∨
    (∃ (e : 𝓑.ε) (input : 𝓑.input e)
      (blocks : (b : 𝓑.branch e) → BlockE 𝓔 𝓑 α e b)
      (k : 𝓑.output e → CompE 𝓔 𝓑 α), x = bindEffAt e input blocks k) := by
  obtain ⟨p, c, hd⟩ : ∃ p c, dest x = ⟨p, c⟩ := ⟨_, _, rfl⟩
  match p, c, hd with
  | .ret a, c, hd =>
      exact Or.inl ⟨a, eq_of_dest_eq (by
        rw [hd, dest_ret]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext h
        nomatch h)⟩
  | .fail, c, hd =>
      exact Or.inr (Or.inl (eq_of_dest_eq (by
        rw [hd, dest_fail]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext h
        nomatch h)))
  | .tau, c, hd =>
      exact Or.inr (Or.inr (Or.inl ⟨c Ar.tau, eq_of_dest_eq (by
        rw [hd, dest_tau]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext h
        cases h
        rfl)⟩))
  | .vis e input, c, hd =>
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e, input, (fun o => c (Ar.vis o)), eq_of_dest_eq (by
          rw [hd, dest_vis]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext h
          cases h
          rfl)⟩)))
  | .bindEff e input, c, hd =>
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e, input, (fun b => (c (Ar.block b) : BlockE 𝓔 𝓑 α e b)),
          (fun o => c (Ar.cont o)),
          eq_of_dest_eq (by
            rw [hd]
            change ⟨Pos.bindEff e input, c⟩ =
              destAt (bindEffAt e input
                (fun b => (c (Ar.block b) : BlockE 𝓔 𝓑 α e b))
                (fun o => c (Ar.cont o)))
            rw [dest_bindEffAt]
            refine Sigma.ext rfl ?_
            apply heq_of_eq
            funext h
            cases h <;> rfl)⟩)))

private inductive BindState (𝓔 : EffSig.{u}) (𝓑 : BindSig.{u}) (α β : Type u)
    (target : Ix 𝓑) :
    Ix 𝓑 → Type u where
  | bind : CompE 𝓔 𝓑 α → BindState 𝓔 𝓑 α β target target
  | copy {i : Ix 𝓑} : Tree 𝓔 𝓑 β i → BindState 𝓔 𝓑 α β target i

private def bindCo {α β : Type u} {target : Ix 𝓑}
    (k : α → Tree 𝓔 𝓑 β target) :
    (i : Ix 𝓑) → BindState 𝓔 𝓑 α β target i →
      Step 𝓔 𝓑 β (BindState 𝓔 𝓑 α β target) i
  | _, .copy t =>
      match destAt t with
      | ⟨p, c⟩ => ⟨p, fun a => .copy (c a)⟩
  | _, .bind m =>
      match dest m with
      | ⟨.ret a, _⟩ =>
          match destAt (k a) with
          | ⟨p, c⟩ => ⟨p, fun x => .copy (c x)⟩
      | ⟨.tau, c⟩ => Step.tau (.bind (c Ar.tau : CompE 𝓔 𝓑 α))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.vis e input, c⟩ =>
          Step.vis e input fun o => .bind (c (Ar.vis o) : CompE 𝓔 𝓑 α)
      | ⟨.bindEff e input, c⟩ =>
          Step.bindEff e input
            (fun b => .copy (relabelBlock (c (Ar.block b) : BlockE 𝓔 𝓑 α e b)))
            (fun o => .bind (c (Ar.cont o) : CompE 𝓔 𝓑 α))

@[simp] private theorem bindCo_bind_ret {α β : Type u} {target : Ix 𝓑}
    (k : α → Tree 𝓔 𝓑 β target) (a : α) :
    bindCo (𝓔 := 𝓔) (𝓑 := 𝓑) (target := target) k target (.bind (ret a)) =
      match destAt (k a) with
      | ⟨p, c⟩ => ⟨p, fun x => BindState.copy (𝓔 := 𝓔) (𝓑 := 𝓑) (target := target) (c x)⟩ := by
  rw [bindCo, dest_ret]
  rfl

@[simp] private theorem bindCo_bind_tau {α β : Type u} {target : Ix 𝓑}
    (k : α → Tree 𝓔 𝓑 β target) (t : CompE 𝓔 𝓑 α) :
    bindCo (𝓔 := 𝓔) (𝓑 := 𝓑) (target := target) k target (.bind (tau t)) =
      Step.tau (BindState.bind (𝓔 := 𝓔) (𝓑 := 𝓑) (β := β) (target := target) t) := by
  rw [bindCo, dest_tau]
  rfl

@[simp] private theorem bindCo_bind_fail {α β : Type u} {target : Ix 𝓑}
    (k : α → Tree 𝓔 𝓑 β target) :
    bindCo (𝓔 := 𝓔) (𝓑 := 𝓑) (target := target) k target
        (.bind (fail : CompE 𝓔 𝓑 α)) =
      Step.fail := by
  rw [bindCo, dest_fail]
  rfl

@[simp] private theorem bindCo_bind_vis {α β : Type u} {target : Ix 𝓑}
    (k : α → Tree 𝓔 𝓑 β target) (e : 𝓔.ε) (input : 𝓔.input e)
    (c : 𝓔.output e → CompE 𝓔 𝓑 α) :
    bindCo (𝓔 := 𝓔) (𝓑 := 𝓑) (target := target) k target
        (.bind (vis e input c)) =
      Step.vis e input fun o =>
        BindState.bind (𝓔 := 𝓔) (𝓑 := 𝓑) (β := β) (target := target) (c o) := by
  rw [bindCo, dest_vis]
  rfl

@[simp] private theorem bindCo_bind_bindEffAt {α β : Type u} {target : Ix 𝓑}
    (k : α → Tree 𝓔 𝓑 β target) (e : 𝓑.ε) (input : 𝓑.input e)
    (blocks : (b : 𝓑.branch e) → BlockE 𝓔 𝓑 α e b)
    (c : 𝓑.output e → CompE 𝓔 𝓑 α) :
    bindCo (𝓔 := 𝓔) (𝓑 := 𝓑) (target := target) k target
        (.bind (bindEffAt e input blocks c)) =
      Step.bindEff e input
        (fun b => BindState.copy (𝓔 := 𝓔) (𝓑 := 𝓑) (target := target)
          (relabelBlock (α := α) (β := β) (blocks b)))
        (fun o => BindState.bind (𝓔 := 𝓔) (𝓑 := 𝓑) (β := β) (target := target) (c o)) := by
  rw [bindCo]
  change (match destAt (bindEffAt e input blocks c) with
    | ⟨.ret a, _⟩ =>
        match destAt (k a) with
        | ⟨p, c⟩ => ⟨p, fun x => BindState.copy (𝓔 := 𝓔) (𝓑 := 𝓑) (target := target) (c x)⟩
    | ⟨.tau, c⟩ =>
        Step.tau (BindState.bind (𝓔 := 𝓔) (𝓑 := 𝓑) (β := β) (target := target)
          (c Ar.tau : CompE 𝓔 𝓑 α))
    | ⟨.fail, _⟩ => Step.fail
    | ⟨.vis e input, c⟩ =>
        Step.vis e input fun o =>
          BindState.bind (𝓔 := 𝓔) (𝓑 := 𝓑) (β := β) (target := target)
            (c (Ar.vis o) : CompE 𝓔 𝓑 α)
    | ⟨.bindEff e input, c⟩ =>
        Step.bindEff e input
          (fun b => BindState.copy (𝓔 := 𝓔) (𝓑 := 𝓑) (target := target)
            (relabelBlock (α := α) (β := β)
              (c (Ar.block b) : BlockE 𝓔 𝓑 α e b)))
          (fun o => BindState.bind (𝓔 := 𝓔) (𝓑 := 𝓑) (β := β) (target := target)
            (c (Ar.cont o) : CompE 𝓔 𝓑 α))) =
      Step.bindEff e input
        (fun b => BindState.copy (𝓔 := 𝓔) (𝓑 := 𝓑) (target := target)
          (relabelBlock (α := α) (β := β) (blocks b)))
        (fun o => BindState.bind (𝓔 := 𝓔) (𝓑 := 𝓑) (β := β) (target := target) (c o))
  rw [dest_bindEffAt]
  rfl

/-- Monadic bind: graft at `ret` leaves and continue through operation continuations, but do not
    bind under scoped blocks. -/
def bindAt {α β : Type u} {i : Ix 𝓑} (m : CompE 𝓔 𝓑 α)
    (k : α → Tree 𝓔 𝓑 β i) : Tree 𝓔 𝓑 β i :=
  corecAt (bindCo (target := i) k) (.bind m)

/-- Public monadic bind. -/
def bind {α β : Type u} (m : CompE 𝓔 𝓑 α) (k : α → CompE 𝓔 𝓑 β) :
    CompE 𝓔 𝓑 β :=
  bindAt m k

instance : Monad (CompE 𝓔 𝓑) where
  pure := ret
  bind := bind

@[simp] theorem pure_def {α : Type u} (a : α) : (pure a : CompE 𝓔 𝓑 α) = ret a := rfl

@[simp] theorem bind_def {α β : Type u} (m : CompE 𝓔 𝓑 α) (k : α → CompE 𝓔 𝓑 β) :
    m >>= k = bind m k := rfl

theorem corec_copy {α β : Type u} {i : Ix 𝓑}
    {target : Ix 𝓑} (k : α → Tree 𝓔 𝓑 β target)
    (t : Tree 𝓔 𝓑 β i) :
    IxPFunctor.M.corec (P := P 𝓔 𝓑 β) (bindCo (target := target) k)
      (.copy t : BindState 𝓔 𝓑 α β target i) = t := by
  refine IxPFunctor.M.bisim (P := P 𝓔 𝓑 β)
    (fun i x y =>
      x = IxPFunctor.M.corec (P := P 𝓔 𝓑 β) (bindCo (target := target) k)
        (.copy y : BindState 𝓔 𝓑 α β target i)) ?_ _ _ rfl
  intro i x y hxy
  subst hxy
  obtain ⟨p, c, hy⟩ : ∃ p c, destAt y = ⟨p, c⟩ := ⟨_, _, rfl⟩
  refine ⟨p,
    fun a => IxPFunctor.M.corec (P := P 𝓔 𝓑 β) (bindCo (target := target) k)
      (.copy (c a) : BindState 𝓔 𝓑 α β target ((P 𝓔 𝓑 β).next p a)),
    c, ?_, hy, fun a => rfl⟩
  rw [IxPFunctor.M.dest_corec]
  change (P 𝓔 𝓑 β).map
      (fun i => IxPFunctor.M.corec (P := P 𝓔 𝓑 β) (bindCo (target := target) k) (i := i))
      (bindCo (𝓔 := 𝓔) (𝓑 := 𝓑) (target := target) k i
        (.copy y : BindState 𝓔 𝓑 α β target i)) =
    ⟨p,
      fun a => IxPFunctor.M.corec (P := P 𝓔 𝓑 β) (bindCo (target := target) k)
        (.copy (c a) : BindState 𝓔 𝓑 α β target ((P 𝓔 𝓑 β).next p a))⟩
  rw [bindCo, hy]
  rfl

@[simp] theorem bind_ret {α β : Type u} (a : α) (k : α → CompE 𝓔 𝓑 β) :
    bind (ret a) k = k a := by
  apply eq_of_dest_eq
  change destAt (bind (ret a) k) = destAt (k a)
  obtain ⟨p, c, hk⟩ : ∃ p c, destAt (k a) = ⟨p, c⟩ := ⟨_, _, rfl⟩
  rw [bind, bindAt, dest_corecAt, bindCo_bind_ret, hk]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext x
  exact corec_copy (k := k) (c x)

@[simp] theorem bind_tau {α β : Type u} (t : CompE 𝓔 𝓑 α) (k : α → CompE 𝓔 𝓑 β) :
    bind (tau t) k = tau (bind t k) := by
  apply eq_of_dest_eq
  change destAt (bindAt (tau t) k) = destAt (tauAt (bindAt t k))
  rw [bindAt, dest_corecAt, bindCo_bind_tau, dest_tauAt]
  simp only [IxPFunctor.map, Step.tau]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext x
  cases x
  rfl

@[simp] theorem bind_fail {α β : Type u} (k : α → CompE 𝓔 𝓑 β) :
    bind (fail : CompE 𝓔 𝓑 α) k = fail := by
  apply eq_of_dest_eq
  change destAt (bindAt (fail : CompE 𝓔 𝓑 α) k) =
    destAt (failAt (𝓔 := 𝓔) (𝓑 := 𝓑) (α := β) (i := .normal))
  rw [bindAt, dest_corecAt, bindCo_bind_fail, dest_failAt]
  simp only [IxPFunctor.map, Step.fail]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext x
  nomatch x

@[simp] theorem bind_vis {α β : Type u} (e : 𝓔.ε) (input : 𝓔.input e)
    (c : 𝓔.output e → CompE 𝓔 𝓑 α) (k : α → CompE 𝓔 𝓑 β) :
    bind (vis e input c) k = vis e input (fun o => bind (c o) k) := by
  apply eq_of_dest_eq
  change destAt (bindAt (vis e input c) k) =
    destAt (visAt e input (fun o => bindAt (c o) k))
  rw [bindAt, dest_corecAt, bindCo_bind_vis, dest_visAt]
  simp only [IxPFunctor.map, Step.vis]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext x
  cases x
  rfl

@[simp] theorem bind_bindEffAt {α β : Type u} (e : 𝓑.ε) (input : 𝓑.input e)
    (blocks : (b : 𝓑.branch e) → BlockE 𝓔 𝓑 α e b)
    (c : 𝓑.output e → CompE 𝓔 𝓑 α) (k : α → CompE 𝓔 𝓑 β) :
    bind (bindEffAt e input blocks c) k =
      bindEffAt e input (fun b => relabelBlock (blocks b)) (fun o => bind (c o) k) := by
  apply eq_of_dest_eq
  change destAt (bind (bindEffAt e input blocks c) k) =
    destAt (bindEffAt e input (fun b => relabelBlock (blocks b)) (fun o => bind (c o) k))
  rw [bind, bindAt, dest_corecAt, bindCo_bind_bindEffAt, dest_bindEffAt]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext x
  cases x with
  | block b =>
      exact corec_copy (k := k) (relabelBlock (α := α) (β := β) (blocks b))
  | cont o =>
      rfl

private inductive RelabelIdRel {α : Type u} :
    (i : Ix 𝓑) → Tree 𝓔 𝓑 α i → Tree 𝓔 𝓑 α i → Prop where
  | block {e : 𝓑.ε} {b : 𝓑.branch e} (t : BlockE 𝓔 𝓑 α e b) :
      RelabelIdRel (.block e b) (relabelBlock (α := α) (β := α) t) t
  | eq {i : Ix 𝓑} {x y : Tree 𝓔 𝓑 α i} (hxy : x = y) : RelabelIdRel i x y

private theorem relabelBlock_id {α : Type u} {e : 𝓑.ε} {b : 𝓑.branch e}
    (t : BlockE 𝓔 𝓑 α e b) : relabelBlock (α := α) (β := α) t = t := by
  refine IxPFunctor.M.bisim (P := P 𝓔 𝓑 α) RelabelIdRel ?_ _ _ (.block t)
  intro i x y hxy
  cases hxy with
  | eq hxy =>
      cases hxy
      obtain ⟨p, c, hd⟩ : ∃ p c, IxPFunctor.M.dest x = ⟨p, c⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c, c, hd, hd, fun _ => .eq rfl⟩
  | block t =>
      rcases cases_viewAt t with
        ⟨a, ht⟩ | ht | ⟨t', ht⟩ | ⟨e, input, k, ht⟩ |
        ⟨e, input, blocks, k, ht⟩
      · cases ht
        refine ⟨(Step.ret a).1, (Step.ret a).2, (Step.ret a).2, ?_,
          raw_dest_mkAt (Step.ret a), fun h => nomatch h⟩
        rw [relabelBlock, raw_dest_corecAt]
        change (P 𝓔 𝓑 α).map
            (fun i => corecAt (relabelBlockCo (α := α) (β := α)) (i := i))
            (relabelBlockCo (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (β := α) _ (.block (retAt a))) =
          Step.ret a
        rw [relabelBlockCo, dest_retAt]
        simp only [IxPFunctor.map, Step.ret]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext x
        nomatch x
      · cases ht
        refine ⟨(Step.fail : Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) _).1,
          (Step.fail : Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) _).2,
          (Step.fail : Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) _).2, ?_,
          raw_dest_mkAt Step.fail, fun h => nomatch h⟩
        rw [relabelBlock, raw_dest_corecAt]
        change (P 𝓔 𝓑 α).map
            (fun i => corecAt (relabelBlockCo (α := α) (β := α)) (i := i))
            (relabelBlockCo (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (β := α) _ (.block failAt)) =
          Step.fail
        rw [relabelBlockCo, dest_failAt]
        simp only [IxPFunctor.map, Step.fail]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext x
        nomatch x
      · cases ht
        refine ⟨(Step.tau (relabelBlock (α := α) (β := α) t')).1,
          (Step.tau (relabelBlock (α := α) (β := α) t')).2,
          (Step.tau t').2, ?_, raw_dest_mkAt (Step.tau t'), ?_⟩
        · rw [relabelBlock, raw_dest_corecAt]
          change (P 𝓔 𝓑 α).map
              (fun i => corecAt (relabelBlockCo (α := α) (β := α)) (i := i))
              (relabelBlockCo (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (β := α) _ (.block (tauAt t'))) =
            Step.tau (relabelBlock (α := α) (β := α) t')
          rw [relabelBlockCo, dest_tauAt]
          simp only [IxPFunctor.map, Step.tau]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext x
          cases x
          rfl
        · intro x
          cases x
          exact .block t'
      · cases ht
        refine ⟨(Step.vis e input (fun o => relabelBlock (α := α) (β := α) (k o))).1,
          (Step.vis e input (fun o => relabelBlock (α := α) (β := α) (k o))).2,
          (Step.vis e input k).2, ?_, raw_dest_mkAt (Step.vis e input k), ?_⟩
        · rw [relabelBlock, raw_dest_corecAt]
          change (P 𝓔 𝓑 α).map
              (fun i => corecAt (relabelBlockCo (α := α) (β := α)) (i := i))
              (relabelBlockCo (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (β := α) _ (.block (visAt e input k))) =
            Step.vis e input (fun o => relabelBlock (α := α) (β := α) (k o))
          rw [relabelBlockCo, dest_visAt]
          simp only [IxPFunctor.map, Step.vis]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext x
          cases x
          rfl
        · intro x
          cases x with
          | vis o => exact .block (k o)
      · cases ht
        refine ⟨(Step.bindEff e input
            (fun b => relabelBlock (α := α) (β := α) (blocks b))
            (fun o => relabelBlock (α := α) (β := α) (k o))).1,
          (Step.bindEff e input
            (fun b => relabelBlock (α := α) (β := α) (blocks b))
            (fun o => relabelBlock (α := α) (β := α) (k o))).2,
          (Step.bindEff e input blocks k).2, ?_,
          raw_dest_mkAt (Step.bindEff e input blocks k), ?_⟩
        · rw [relabelBlock, raw_dest_corecAt]
          change (P 𝓔 𝓑 α).map
              (fun i => corecAt (relabelBlockCo (α := α) (β := α)) (i := i))
              (relabelBlockCo (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (β := α) _
                (.block (bindEffAt e input blocks k))) =
            Step.bindEff e input
              (fun b => relabelBlock (α := α) (β := α) (blocks b))
              (fun o => relabelBlock (α := α) (β := α) (k o))
          rw [relabelBlockCo, dest_bindEffAt]
          simp only [IxPFunctor.map, Step.bindEff]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext x
          cases x <;> rfl
        · intro x
          cases x with
          | block b => exact .block (blocks b)
          | cont o => exact .block (k o)

private theorem dest_relabelBlock {α β : Type u} {e₀ : 𝓑.ε} {b₀ : 𝓑.branch e₀}
    (t : BlockE 𝓔 𝓑 α e₀ b₀) :
    destAt (relabelBlock (α := α) (β := β) t) =
      match destAt t with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ =>
          Step.tau (relabelBlock (α := α) (β := β)
            (c Ar.tau : BlockE 𝓔 𝓑 α e₀ b₀))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.vis e input, c⟩ =>
          Step.vis e input fun o =>
            relabelBlock (α := α) (β := β)
              (c (Ar.vis o) : BlockE 𝓔 𝓑 α e₀ b₀)
      | ⟨.bindEff e input, c⟩ =>
          Step.bindEff e input
            (fun b => relabelBlock (α := α) (β := β)
              (c (Ar.block b) : BlockE 𝓔 𝓑 α e b))
            (fun o => relabelBlock (α := α) (β := β)
              (c (Ar.cont o) : BlockE 𝓔 𝓑 α e₀ b₀)) := by
  obtain ⟨p, c, ht⟩ : ∃ p c, destAt t = ⟨p, c⟩ := ⟨_, _, rfl⟩
  match p, c, ht with
  | .ret a, c, ht =>
      rw [ht, relabelBlock, dest_corecAt]
      change (P 𝓔 𝓑 β).map
          (fun i => corecAt (relabelBlockCo (α := α) (β := β)) (i := i))
          (relabelBlockCo (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (β := β) _ (.block t)) =
        Step.ret (𝓔 := 𝓔) (𝓑 := 𝓑) (α := β) (i := .block e₀ b₀) a
      rw [relabelBlockCo, ht]
      simp only [IxPFunctor.map, Step.ret]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext h
      nomatch h
  | .fail, c, ht =>
      rw [ht, relabelBlock, dest_corecAt]
      change (P 𝓔 𝓑 β).map
          (fun i => corecAt (relabelBlockCo (α := α) (β := β)) (i := i))
          (relabelBlockCo (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (β := β) _ (.block t)) =
        Step.fail (𝓔 := 𝓔) (𝓑 := 𝓑) (α := β) (i := .block e₀ b₀)
      rw [relabelBlockCo, ht]
      simp only [IxPFunctor.map, Step.fail]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext h
      nomatch h
  | .tau, c, ht =>
      rw [ht, relabelBlock, dest_corecAt]
      change (P 𝓔 𝓑 β).map
          (fun i => corecAt (relabelBlockCo (α := α) (β := β)) (i := i))
          (relabelBlockCo (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (β := β) _ (.block t)) =
        Step.tau (relabelBlock (α := α) (β := β)
          (c Ar.tau : BlockE 𝓔 𝓑 α e₀ b₀))
      rw [relabelBlockCo, ht]
      simp only [IxPFunctor.map, Step.tau]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext h
      cases h
      rfl
  | .vis e input, c, ht =>
      rw [ht, relabelBlock, dest_corecAt]
      change (P 𝓔 𝓑 β).map
          (fun i => corecAt (relabelBlockCo (α := α) (β := β)) (i := i))
          (relabelBlockCo (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (β := β) _ (.block t)) =
        Step.vis e input fun o =>
          relabelBlock (α := α) (β := β)
            (c (Ar.vis o) : BlockE 𝓔 𝓑 α e₀ b₀)
      rw [relabelBlockCo, ht]
      simp only [IxPFunctor.map, Step.vis]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext h
      cases h
      rfl
  | .bindEff e input, c, ht =>
      rw [ht, relabelBlock, dest_corecAt]
      change (P 𝓔 𝓑 β).map
          (fun i => corecAt (relabelBlockCo (α := α) (β := β)) (i := i))
          (relabelBlockCo (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (β := β) _ (.block t)) =
        Step.bindEff e input
          (fun b => relabelBlock (α := α) (β := β)
            (c (Ar.block b) : BlockE 𝓔 𝓑 α e b))
          (fun o => relabelBlock (α := α) (β := β)
            (c (Ar.cont o) : BlockE 𝓔 𝓑 α e₀ b₀))
      rw [relabelBlockCo, ht]
      simp only [IxPFunctor.map, Step.bindEff]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext h
      cases h <;> rfl

private inductive RelabelCompRel {α β γ : Type u} :
    (i : Ix 𝓑) → Tree 𝓔 𝓑 γ i → Tree 𝓔 𝓑 γ i → Prop where
  | block {e : 𝓑.ε} {b : 𝓑.branch e} (t : BlockE 𝓔 𝓑 α e b) :
      RelabelCompRel (.block e b)
        (relabelBlock (α := β) (β := γ) (relabelBlock (α := α) (β := β) t))
        (relabelBlock (α := α) (β := γ) t)
  | eq {i : Ix 𝓑} {x y : Tree 𝓔 𝓑 γ i} (hxy : x = y) : RelabelCompRel i x y

private theorem relabelBlock_comp {α β γ : Type u} {e : 𝓑.ε} {b : 𝓑.branch e}
    (t : BlockE 𝓔 𝓑 α e b) :
    relabelBlock (α := β) (β := γ) (relabelBlock (α := α) (β := β) t) =
      relabelBlock (α := α) (β := γ) t := by
  refine IxPFunctor.M.bisim (P := P 𝓔 𝓑 γ) RelabelCompRel ?_ _ _ (.block t)
  intro i x y hxy
  cases hxy with
  | eq hxy =>
      cases hxy
      obtain ⟨p, c, hd⟩ : ∃ p c, IxPFunctor.M.dest x = ⟨p, c⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c, c, hd, hd, fun _ => .eq rfl⟩
  | block t =>
      rcases cases_viewAt t with
        ⟨a, ht⟩ | ht | ⟨t', ht⟩ | ⟨e, input, k, ht⟩ |
        ⟨e, input, blocks, k, ht⟩
      · cases ht
        let lhs := relabelBlock (𝓔 := 𝓔) (𝓑 := 𝓑) (α := β) (β := γ)
          (relabelBlock (α := α) (β := β) (retAt a))
        let rhs := relabelBlock (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (β := γ) (retAt a)
        have hdest : IxPFunctor.M.dest lhs = IxPFunctor.M.dest rhs := by
          change destAt lhs = destAt rhs
          dsimp [lhs, rhs]
          rw [dest_relabelBlock, dest_relabelBlock, dest_retAt]
          rw [dest_relabelBlock, dest_retAt]
          simp only [Step.ret]
        obtain ⟨p, c, hy⟩ : ∃ p c, IxPFunctor.M.dest rhs = ⟨p, c⟩ := ⟨_, _, rfl⟩
        exact ⟨p, c, c, hdest.trans hy, hy, fun _ => .eq rfl⟩
      ·
        let lhs := relabelBlock (𝓔 := 𝓔) (𝓑 := 𝓑) (α := β) (β := γ)
          (relabelBlock (α := α) (β := β) t)
        let rhs := relabelBlock (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (β := γ)
          t
        have hdest : IxPFunctor.M.dest lhs = IxPFunctor.M.dest rhs := by
          cases ht
          change destAt lhs = destAt rhs
          dsimp [lhs, rhs]
          rw [dest_relabelBlock, dest_relabelBlock, dest_failAt]
          rw [dest_relabelBlock, dest_failAt]
          simp only [Step.fail]
        obtain ⟨p, c, hy⟩ : ∃ p c, IxPFunctor.M.dest rhs = ⟨p, c⟩ := ⟨_, _, rfl⟩
        exact ⟨p, c, c, hdest.trans hy, hy, fun _ => .eq rfl⟩
      · cases ht
        let sx : Step 𝓔 𝓑 γ (Tree 𝓔 𝓑 γ) _ :=
          Step.tau (relabelBlock (α := β) (β := γ)
            (relabelBlock (α := α) (β := β) t'))
        let sy : Step 𝓔 𝓑 γ (Tree 𝓔 𝓑 γ) _ :=
          Step.tau (relabelBlock (α := α) (β := γ) t')
        refine ⟨sx.1, sx.2, sy.2, ?_, ?_, ?_⟩
        · change destAt (relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (tauAt t'))) = sx
          rw [dest_relabelBlock, dest_relabelBlock, dest_tauAt]
          simp only [Step.tau]
          dsimp [sx, Step.tau]
        · change destAt (relabelBlock (α := α) (β := γ) (tauAt t')) = sy
          rw [dest_relabelBlock, dest_tauAt]
          simp only [Step.tau]
          dsimp [sy, Step.tau]
        · intro h
          cases h
          exact .block t'
      · cases ht
        let sx : Step 𝓔 𝓑 γ (Tree 𝓔 𝓑 γ) _ :=
          Step.vis e input fun o =>
            relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (k o))
        let sy : Step 𝓔 𝓑 γ (Tree 𝓔 𝓑 γ) _ :=
          Step.vis e input fun o => relabelBlock (α := α) (β := γ) (k o)
        refine ⟨sx.1, sx.2, sy.2, ?_, ?_, ?_⟩
        · change destAt (relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (visAt e input k))) = sx
          rw [dest_relabelBlock, dest_relabelBlock, dest_visAt]
          simp only [Step.vis]
          dsimp [sx, Step.vis]
        · change destAt (relabelBlock (α := α) (β := γ) (visAt e input k)) = sy
          rw [dest_relabelBlock, dest_visAt]
          simp only [Step.vis]
          dsimp [sy, Step.vis]
        · intro h
          cases h with
          | vis o => exact .block (k o)
      · cases ht
        let sx : Step 𝓔 𝓑 γ (Tree 𝓔 𝓑 γ) _ :=
          Step.bindEff e input
            (fun b => relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (blocks b)))
            (fun o => relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (k o)))
        let sy : Step 𝓔 𝓑 γ (Tree 𝓔 𝓑 γ) _ :=
          Step.bindEff e input
            (fun b => relabelBlock (α := α) (β := γ) (blocks b))
            (fun o => relabelBlock (α := α) (β := γ) (k o))
        refine ⟨sx.1, sx.2, sy.2, ?_, ?_, ?_⟩
        · change destAt (relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (bindEffAt e input blocks k))) = sx
          rw [dest_relabelBlock, dest_relabelBlock, dest_bindEffAt]
          simp only [Step.bindEff]
          dsimp [sx, Step.bindEff]
        · change destAt (relabelBlock (α := α) (β := γ) (bindEffAt e input blocks k)) = sy
          rw [dest_relabelBlock, dest_bindEffAt]
          simp only [Step.bindEff]
          dsimp [sy, Step.bindEff]
        · intro h
          cases h with
          | block b => exact .block (blocks b)
          | cont o => exact .block (k o)

private inductive BindRightRel {α : Type u} :
    (i : Ix 𝓑) → Tree 𝓔 𝓑 α i → Tree 𝓔 𝓑 α i → Prop where
  | root (m : CompE 𝓔 𝓑 α) : BindRightRel .normal (bind m ret) m
  | eq {i : Ix 𝓑} {x y : Tree 𝓔 𝓑 α i} (hxy : x = y) : BindRightRel i x y

theorem bind_ret_right {α : Type u} (m : CompE 𝓔 𝓑 α) : bind m ret = m := by
  refine IxPFunctor.M.bisim (P := P 𝓔 𝓑 α) BindRightRel ?_ _ _ (.root m)
  intro i x y hxy
  cases hxy with
  | eq hxy =>
      cases hxy
      obtain ⟨p, c, hd⟩ : ∃ p c, IxPFunctor.M.dest x = ⟨p, c⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c, c, hd, hd, fun _ => .eq rfl⟩
  | root m =>
      rcases cases_view m with
        ⟨a, hm⟩ | hm | ⟨t, hm⟩ | ⟨e, input, k, hm⟩ |
        ⟨e, input, blocks, k, hm⟩
      · cases hm
        rw [bind_ret]
        let s : Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) .normal := Step.ret a
        refine ⟨s.1, s.2, s.2, ?_, ?_, fun h => nomatch h⟩
        · exact raw_dest_mkAt s
        · exact raw_dest_mkAt s
      · cases hm
        rw [bind_fail]
        refine ⟨(Step.fail : Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) .normal).1,
          (Step.fail : Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) .normal).2,
          (Step.fail : Step 𝓔 𝓑 α (Tree 𝓔 𝓑 α) .normal).2,
          raw_dest_mkAt Step.fail, raw_dest_mkAt Step.fail, fun h => nomatch h⟩
      · cases hm
        rw [bind_tau]
        refine ⟨(Step.tau (bind t ret)).1, (Step.tau (bind t ret)).2,
          (Step.tau t).2, raw_dest_mkAt (Step.tau (bind t ret)),
          raw_dest_mkAt (Step.tau t), ?_⟩
        intro h
        cases h
        exact .root t
      · cases hm
        rw [bind_vis]
        refine ⟨(Step.vis e input (fun o => bind (k o) ret)).1,
          (Step.vis e input (fun o => bind (k o) ret)).2,
          (Step.vis e input k).2,
          raw_dest_mkAt (Step.vis e input (fun o => bind (k o) ret)),
          raw_dest_mkAt (Step.vis e input k), ?_⟩
        intro h
        cases h with
        | vis o => exact .root (k o)
      · cases hm
        rw [bind_bindEffAt]
        refine ⟨(Step.bindEff e input
            (fun b => relabelBlock (α := α) (β := α) (blocks b))
            (fun o => bind (k o) ret)).1,
          (Step.bindEff e input
            (fun b => relabelBlock (α := α) (β := α) (blocks b))
            (fun o => bind (k o) ret)).2,
          (Step.bindEff e input blocks k).2,
          raw_dest_mkAt (Step.bindEff e input
            (fun b => relabelBlock (α := α) (β := α) (blocks b))
            (fun o => bind (k o) ret)),
          raw_dest_mkAt (Step.bindEff e input blocks k), ?_⟩
        intro h
        cases h with
        | block b => exact .eq (relabelBlock_id (blocks b))
        | cont o => exact .root (k o)

private inductive BindAssocRel {α β γ : Type u}
    (k : α → CompE 𝓔 𝓑 β) (h : β → CompE 𝓔 𝓑 γ) :
    (i : Ix 𝓑) → Tree 𝓔 𝓑 γ i → Tree 𝓔 𝓑 γ i → Prop where
  | root (m : CompE 𝓔 𝓑 α) :
      BindAssocRel k h .normal
        (bind (bind m k) h)
        (bind m fun a => bind (k a) h)
  | eq {i : Ix 𝓑} {x y : Tree 𝓔 𝓑 γ i} (hxy : x = y) : BindAssocRel k h i x y

theorem bind_assoc {α β γ : Type u} (m : CompE 𝓔 𝓑 α)
    (k : α → CompE 𝓔 𝓑 β) (h : β → CompE 𝓔 𝓑 γ) :
    bind (bind m k) h = bind m (fun a => bind (k a) h) := by
  refine IxPFunctor.M.bisim (P := P 𝓔 𝓑 γ) (BindAssocRel k h) ?_ _ _ (.root m)
  intro i x y hxy
  cases hxy with
  | eq hxy =>
      cases hxy
      obtain ⟨p, c, hd⟩ : ∃ p c, IxPFunctor.M.dest x = ⟨p, c⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c, c, hd, hd, fun _ => .eq rfl⟩
  | root m =>
      rcases cases_view m with
        ⟨a, hm⟩ | hm | ⟨t, hm⟩ | ⟨e, input, c, hm⟩ |
        ⟨e, input, blocks, c, hm⟩
      · cases hm
        rw [bind_ret, bind_ret]
        obtain ⟨p, child, hd⟩ :
            ∃ p child, IxPFunctor.M.dest (bind (k a) h) = ⟨p, child⟩ := ⟨_, _, rfl⟩
        exact ⟨p, child, child, hd, hd, fun _ => .eq rfl⟩
      · cases hm
        rw [bind_fail, bind_fail, bind_fail]
        let s : Step 𝓔 𝓑 γ (Tree 𝓔 𝓑 γ) .normal := Step.fail
        refine ⟨s.1, s.2, s.2, ?_, ?_, fun h => nomatch h⟩
        · exact raw_dest_mkAt s
        · exact raw_dest_mkAt s
      · cases hm
        rw [bind_tau, bind_tau, bind_tau]
        refine ⟨(Step.tau (bind (bind t k) h)).1,
          (Step.tau (bind (bind t k) h)).2,
          (Step.tau (bind t fun a => bind (k a) h)).2,
          raw_dest_mkAt (Step.tau (bind (bind t k) h)),
          raw_dest_mkAt (Step.tau (bind t fun a => bind (k a) h)), ?_⟩
        intro h'
        cases h'
        exact .root t
      · cases hm
        rw [bind_vis, bind_vis, bind_vis]
        refine ⟨(Step.vis e input (fun o => bind (bind (c o) k) h)).1,
          (Step.vis e input (fun o => bind (bind (c o) k) h)).2,
          (Step.vis e input (fun o => bind (c o) fun a => bind (k a) h)).2,
          raw_dest_mkAt (Step.vis e input (fun o => bind (bind (c o) k) h)),
          raw_dest_mkAt (Step.vis e input (fun o => bind (c o) fun a => bind (k a) h)), ?_⟩
        intro h'
        cases h' with
        | vis o => exact .root (c o)
      · cases hm
        rw [bind_bindEffAt, bind_bindEffAt, bind_bindEffAt]
        refine ⟨(Step.bindEff e input
            (fun b => relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (blocks b)))
            (fun o => bind (bind (c o) k) h)).1,
          (Step.bindEff e input
            (fun b => relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (blocks b)))
            (fun o => bind (bind (c o) k) h)).2,
          (Step.bindEff e input
            (fun b => relabelBlock (α := α) (β := γ) (blocks b))
            (fun o => bind (c o) fun a => bind (k a) h)).2,
          raw_dest_mkAt (Step.bindEff e input
            (fun b => relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (blocks b)))
            (fun o => bind (bind (c o) k) h)),
          raw_dest_mkAt (Step.bindEff e input
            (fun b => relabelBlock (α := α) (β := γ) (blocks b))
            (fun o => bind (c o) fun a => bind (k a) h)), ?_⟩
        intro h'
        cases h' with
        | block b => exact .eq (relabelBlock_comp (blocks b))
        | cont o => exact .root (c o)

instance : LawfulMonad (CompE 𝓔 𝓑) :=
  LawfulMonad.mk' _
    (fun m => bind_ret_right m)
    (fun a k => bind_ret a k)
    (fun m k h => bind_assoc m k h)

end CompE

/-! ## Effect sums, singleton calls, and guarded recursion -/

namespace EffSig

/-- Sum of independent first-order effect signatures. -/
abbrev sum (𝓔 : EffSig.{u}) (𝓕 : EffSig.{u}) : EffSig.{u} where
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

/-- The singleton label for recursive-call events. -/
inductive CallOp : Type u where
  | call : CallOp

/-- The singleton recursive-call effect: one operation, carrying an argument and returning the
    recursive result.  It does not know about the ambient effect signature. -/
abbrev CallEff (σ ρ : Type u) : EffSig.{u} where
  ε := CallOp
  input := fun _ => σ
  output := fun _ => ρ

namespace CompE

variable {𝓔 𝓕 : EffSig.{u}} {𝓑 : BindSig.{u}}

/-- Coalgebra for relabelling effects into the left side of an effect sum. -/
def sumLCo :
    (i : Ix 𝓑) → Tree 𝓔 𝓑 α i →
      Step (SumEff 𝓔 𝓕) 𝓑 α (Tree 𝓔 𝓑 α) i
  | _, t =>
      match destAt t with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ => Step.tau (c Ar.tau)
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.vis e input, c⟩ => Step.vis (Sum.inl e) input fun o => c (Ar.vis o)
      | ⟨.bindEff e input, c⟩ =>
          Step.bindEff e input
            (fun b => c (Ar.block b))
            (fun o => c (Ar.cont o))

/-- Embed a computation into the left side of an effect sum. -/
def sumL {α : Type u} (t : CompE 𝓔 𝓑 α) : CompE (SumEff 𝓔 𝓕) 𝓑 α :=
  corecAt sumLCo t

/-- Coalgebra for interpreting call events by rerunning the body behind one `tau`. -/
def interpCo {σ ρ : Type u} (body : σ → CompE (SumEff 𝓔 (CallEff σ ρ)) 𝓑 ρ) :
    (i : Ix 𝓑) → Tree (SumEff 𝓔 (CallEff σ ρ)) 𝓑 α i →
      Step 𝓔 𝓑 α (Tree (SumEff 𝓔 (CallEff σ ρ)) 𝓑 α) i
  | _, t =>
      match destAt t with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ => Step.tau (c Ar.tau)
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.vis (Sum.inl e) input, c⟩ => Step.vis e input fun o => c (Ar.vis o)
      | ⟨.vis (Sum.inr _) s, c⟩ =>
          Step.tau (bindAt (body s) fun o => c (Ar.vis o))
      | ⟨.bindEff e input, c⟩ =>
          Step.bindEff e input
            (fun b => c (Ar.block b))
            (fun o => c (Ar.cont o))

/-- Interpret a call-summed computation back into the base signature. -/
def interp {σ ρ α : Type u} (body : σ → CompE (SumEff 𝓔 (CallEff σ ρ)) 𝓑 ρ)
    (t : CompE (SumEff 𝓔 (CallEff σ ρ)) 𝓑 α) : CompE 𝓔 𝓑 α :=
  corecAt (interpCo body) t

/-- Guarded general recursion by interpreting self-call events. -/
def mrec {σ ρ : Type u} (body : σ → CompE (SumEff 𝓔 (CallEff σ ρ)) 𝓑 ρ) :
    σ → CompE 𝓔 𝓑 ρ :=
  fun s => interp body (body s)

end CompE

end ITree2
end Freigen
