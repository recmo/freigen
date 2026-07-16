import Freigen.ITree.PFunctor

namespace Freigen
namespace ITree

universe u v w

/-- One layer of the scoped interaction-tree polynomial at internal result label `i`. -/
abbrev Step (H : HSig.{u, v}) (α : Type u)
    (X : Ix H → Type w) (i : Ix H) :=
  (P H α).Obj X i

/-- The internal tree family.  The public computation type is the `.normal` fiber. -/
abbrev Tree (H : HSig.{u, v}) (α : Type u) (i : Ix H) :=
  (P H α).M i

/-- Public scoped interaction trees. -/
abbrev CompE (H : HSig.{u, v}) (α : Type u) :=
  Tree H α .normal

/-- Internal block fiber for a higher-order operation branch. -/
abbrev BlockE (H : HSig.{u, v}) (α : Type u)
    (e : H.op) (b : H.Block e) :=
  Tree H α (.block e b)

namespace Step

variable {H : HSig.{u, v}} {α : Type u}
  {X : Ix H → Type w}

/-- Return step: no recursive children. -/
def ret {i : Ix H} (a : result H α i) : Step H α X i :=
  ⟨Pos.ret a, fun h => nomatch h⟩

/-- Silent step: one child at the ambient internal label. -/
def tau {i : Ix H} (t : X i) : Step H α X i :=
  ⟨Pos.tau, fun
    | Ar.tau => t⟩

/-- Failure step: no recursive children. -/
def fail {i : Ix H} : Step H α X i :=
  ⟨Pos.fail, fun h => nomatch h⟩
/-- Higher-order operation step: block children jump to their block labels; the continuation
    children stay at the ambient internal label. -/
def op {i : Ix H} (e : H.op) (input : H.input e)
    (blocks : (b : H.Block e) → X (.block e b))
    (k : H.output e → X i) : Step H α X i :=
  ⟨Pos.op e input, fun
    | Ar.block b => blocks b
    | Ar.cont o => k o⟩

end Step

namespace CompE

variable {H : HSig.{u, v}}

set_option backward.isDefEq.respectTransparency false

/-- Build an internal tree from one scoped interaction-tree step. -/
def mkAt {α : Type u} {i : Ix H} (x : Step H α (Tree H α) i) :
    Tree H α i :=
  IxPFunctor.M.ofStep x

/-- Destruct one layer of an internal tree. -/
def destAt {α : Type u} {i : Ix H} (x : Tree H α i) :
    Step H α (Tree H α) i :=
  IxPFunctor.M.dest x

/-- Build a public computation from one normal step. -/
def mk {α : Type u} (x : Step H α (Tree H α) .normal) : CompE H α :=
  mkAt x

/-- Destruct one layer of a public computation. -/
def dest {α : Type u} (x : CompE H α) :
    Step H α (Tree H α) .normal :=
  destAt x

@[simp] theorem dest_mkAt {α : Type u} {i : Ix H}
    (x : Step H α (Tree H α) i) : destAt (mkAt x) = x :=
  IxPFunctor.M.dest_ofStep x

@[simp] theorem raw_dest_mkAt {α : Type u} {i : Ix H}
    (x : Step H α (Tree H α) i) : IxPFunctor.M.dest (mkAt x) = x :=
  IxPFunctor.M.dest_ofStep x

@[simp] theorem dest_mk {α : Type u} (x : Step H α (Tree H α) .normal) :
    dest (mk x) = x :=
  dest_mkAt x

/-- Return a value at an internal result label. -/
def retAt {α : Type u} {i : Ix H} (a : result H α i) : Tree H α i :=
  mkAt (Step.ret a)

/-- Return a public value. -/
def ret {α : Type u} (a : α) : CompE H α :=
  retAt (i := .normal) a

/-- Silent internal step. -/
def tauAt {α : Type u} {i : Ix H} (t : Tree H α i) : Tree H α i :=
  mkAt (Step.tau t)

/-- Silent public step. -/
def tau {α : Type u} (t : CompE H α) : CompE H α :=
  tauAt t

/-- Internal failure. -/
def failAt {α : Type u} {i : Ix H} : Tree H α i :=
  mkAt Step.fail

/-- Public failure. -/
def fail {α : Type u} : CompE H α :=
  failAt (i := .normal)
/-- Internal higher-order operation node. -/
def opAt {α : Type u} {i : Ix H} (e : H.op) (input : H.input e)
    (blocks : (b : H.Block e) → BlockE H α e b)
    (k : H.output e → Tree H α i) : Tree H α i :=
  mkAt (Step.op e input blocks k)

@[simp] theorem dest_retAt {α : Type u} {i : Ix H} (a : result H α i) :
    destAt (retAt (H := H) a) = Step.ret a := dest_mkAt _

@[simp] theorem dest_ret {α : Type u} (a : α) :
    dest (ret (H := H) a) = Step.ret a := dest_mkAt _

@[simp] theorem dest_tauAt {α : Type u} {i : Ix H} (t : Tree H α i) :
    destAt (tauAt t) = Step.tau t := dest_mkAt _

@[simp] theorem dest_tau {α : Type u} (t : CompE H α) :
    dest (tau t) = Step.tau t := dest_mkAt _

@[simp] theorem dest_failAt {α : Type u} {i : Ix H} :
    destAt (failAt (H := H) (α := α) (i := i)) = Step.fail := dest_mkAt _

@[simp] theorem dest_fail {α : Type u} :
    dest (fail (H := H) (α := α)) = Step.fail := dest_mkAt _
@[simp] theorem dest_opAt {α : Type u} {i : Ix H} (e : H.op) (input : H.input e)
    (blocks : (b : H.Block e) → BlockE H α e b)
    (k : H.output e → Tree H α i) :
    destAt (opAt e input blocks k) = Step.op e input blocks k := dest_mkAt _

theorem eq_of_destAt_eq {α : Type u} {i : Ix H} {x y : Tree H α i}
    (h : destAt x = destAt y) : x = y :=
  IxPFunctor.M.eq_of_dest_eq h

theorem eq_of_dest_eq {α : Type u} {x y : CompE H α} (h : dest x = dest y) : x = y :=
  eq_of_destAt_eq h

/-- Corecursor specialized to the scoped computation polynomial. -/
def corecAt {α : Type u} {X : Ix H → Type w}
    (f : (i : Ix H) → X i → Step H α X i) {i : Ix H} (x : X i) :
    Tree H α i :=
  IxPFunctor.M.corec (P := P H α) f x

@[simp] theorem dest_corecAt {α : Type u} {X : Ix H → Type w}
    (f : (i : Ix H) → X i → Step H α X i) {i : Ix H} (x : X i) :
    destAt (corecAt f x) = (P H α).map (fun i => corecAt f (i := i)) (f i x) :=
  IxPFunctor.M.dest_corec f x

@[simp] theorem raw_dest_corecAt {α : Type u} {X : Ix H → Type w}
    (f : (i : Ix H) → X i → Step H α X i) {i : Ix H} (x : X i) :
    IxPFunctor.M.dest (corecAt f x) =
      (P H α).map (fun i => corecAt f (i := i)) (f i x) :=
  IxPFunctor.M.dest_corec f x

private inductive RelabelBlockState (H : HSig.{u, v}) (α β : Type u) :
    Ix H → Type (max u v) where
  | block {e : H.op} {b : H.Block e} :
      BlockE H α e b → RelabelBlockState H α β (.block e b)

/-- Coalgebra relabelling a block fiber from ambient normal result `α` to `β`. -/
private def relabelBlockCo {α β : Type u} :
    (i : Ix H) → RelabelBlockState H α β i →
      Step H β (RelabelBlockState H α β) i
  | .block e₀ b₀, .block t =>
      match destAt t with
      | ⟨.ret a, _⟩ =>
          Step.ret (H := H) (α := β) (i := .block e₀ b₀) a
      | ⟨.tau, c⟩ => Step.tau (.block (c Ar.tau : BlockE H α e₀ b₀))
      | ⟨.fail, _⟩ =>
          Step.fail (H := H) (α := β) (i := .block e₀ b₀)

      | ⟨.op e input, c⟩ =>
          Step.op e input
            (fun b => .block (c (Ar.block b) : BlockE H α e b))
            (fun o => .block (c (Ar.cont o) : BlockE H α e₀ b₀))

/-- Relabel a block tree across a change of the public normal result type. -/
def relabelBlock {α β : Type u} {e : H.op} {b : H.Block e}
    (t : BlockE H α e b) : BlockE H β e b :=
  corecAt (H := H) (α := β) (relabelBlockCo (α := α) (β := β))
    (RelabelBlockState.block t)

private inductive AsBlockState (H : HSig.{u, v}) (α : Type u)
    (root : H.op) (br : H.Block root) :
    Ix H → Type (max u v) where
  | root :
      CompE H (H.branchOutput root br.1) → AsBlockState H α root br (.block root br)
  | copy {i : Ix H} : Tree H α i → AsBlockState H α root br i

/-- Coalgebra embedding a public computation as a scoped block. -/
private def asBlockCo {α : Type u} (root : H.op) (br : H.Block root) :
    (i : Ix H) → AsBlockState H α root br i →
      Step H α (AsBlockState H α root br) i
  | .block _ _, .root t =>
      match dest t with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ => Step.tau (.root (c Ar.tau : CompE H (H.branchOutput root br.1)))
      | ⟨.fail, _⟩ => Step.fail

      | ⟨.op e input, c⟩ =>
          Step.op e input
            (fun b => .copy (relabelBlock
              (c (Ar.block b) : BlockE H (H.branchOutput root br.1) e b)))
            (fun o => .root (c (Ar.cont o) : CompE H (H.branchOutput root br.1)))
  | _, .copy t =>
      match destAt t with
      | ⟨position, children⟩ => ⟨position, fun ar => .copy (children ar)⟩

/-- Embed a public computation returning a branch result as the corresponding internal block. -/
def asBlock {α : Type u} {e : H.op} {b : H.Block e}
    (t : CompE H (H.branchOutput e b.1)) : BlockE H α e b :=
  corecAt (H := H) (α := α) (asBlockCo (α := α) e b)
    (AsBlockState.root t)

def rehomeBlock {α : Type u} {root : H.op} {rootBranch : H.Block root}
    {e : H.op} {branch : H.Block e}
    (tree : BlockE H (H.branchOutput root rootBranch.1) e branch) :
    BlockE H α e branch :=
  relabelBlock tree

private theorem asBlock_copy {α : Type u} (root : H.op) (rootBranch : H.Block root)
    {i : Ix H} (tree : Tree H α i) :
    corecAt (asBlockCo (α := α) root rootBranch)
      (.copy tree : AsBlockState H α root rootBranch i) = tree := by
  refine IxPFunctor.M.bisim (P := P H α)
    (fun i left right => left = corecAt (asBlockCo (α := α) root rootBranch)
      (.copy right : AsBlockState H α root rootBranch i)) ?_ _ _ rfl
  intro i left right related
  subst left
  obtain ⟨position, children, equation⟩ : ∃ p c, destAt right = ⟨p, c⟩ :=
    ⟨_, _, rfl⟩
  refine ⟨position,
    fun ar => corecAt (asBlockCo (α := α) root rootBranch)
      (.copy (children ar) : AsBlockState H α root rootBranch _),
    children, ?_, equation, fun _ => rfl⟩
  rw [raw_dest_corecAt, asBlockCo, equation]
  rfl


@[simp] theorem dest_asBlock {α : Type u} {e₀ : H.op} {b₀ : H.Block e₀}
    (tree : CompE H (H.branchOutput e₀ b₀.1)) :
    destAt (asBlock (α := α) tree) =
      match dest tree with
      | ⟨.ret value, _⟩ => Step.ret value
      | ⟨.tau, children⟩ => Step.tau (asBlock (α := α) (children Ar.tau))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.op e input, children⟩ => Step.op e input
          (fun branch => relabelBlock
            (α := H.branchOutput e₀ b₀.1) (β := α)
            (children (Ar.block branch)))
          (fun output => asBlock (α := α) (children (Ar.cont output))) := by
  rw [asBlock, dest_corecAt]
  obtain ⟨position, children, equation⟩ : ∃ p c, dest tree = ⟨p, c⟩ :=
    ⟨_, _, rfl⟩
  rw [asBlockCo, equation]
  cases position with
  | ret =>
      simp only [IxPFunctor.map, Step.ret]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext impossible
      nomatch impossible
  | tau =>
      simp only [IxPFunctor.map, Step.tau]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext ar
      cases ar
      rfl
  | fail =>
      simp only [IxPFunctor.map, Step.fail]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext impossible
      nomatch impossible
  | op operation input =>
      simp only [IxPFunctor.map, Step.op]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext ar
      cases ar with
      | block branch => exact asBlock_copy e₀ b₀ _
      | cont output => rfl

@[simp] theorem asBlock_ret {α : Type u} {e : H.op} {b : H.Block e}
    (value : H.branchOutput e b.1) :
    asBlock (α := α) (ret value) = retAt value := by
  apply eq_of_destAt_eq
  simp only [dest_asBlock, dest_ret, dest_retAt, Step.ret]

@[simp] theorem asBlock_tau {α : Type u} {e : H.op} {b : H.Block e}
    (tree : CompE H (H.branchOutput e b.1)) :
    asBlock (α := α) (tau tree) = tauAt (asBlock (α := α) tree) := by
  apply eq_of_destAt_eq
  simp only [dest_asBlock, dest_tau, dest_tauAt, Step.tau]

@[simp] theorem asBlock_fail {α : Type u} {e : H.op} {b : H.Block e} :
    asBlock (α := α) (fail : CompE H (H.branchOutput e b.1)) = failAt := by
  apply eq_of_destAt_eq
  simp only [dest_asBlock, dest_fail, dest_failAt, Step.fail]

theorem asBlock_opAt {α : Type u} {root : H.op} {rootBranch : H.Block root}
    (e : H.op) (input : H.input e)
    (blocks : (branch : H.Block e) →
      BlockE H (H.branchOutput root rootBranch.1) e branch)
    (continuation : H.output e → CompE H (H.branchOutput root rootBranch.1)) :
    asBlock (α := α) (opAt e input blocks continuation) =
      opAt e input
        (fun branch => relabelBlock
          (α := H.branchOutput root rootBranch.1) (β := α) (blocks branch))
        (fun output => asBlock (α := α) (continuation output)) := by
  apply eq_of_destAt_eq
  rw [dest_asBlock]
  rw [show dest (opAt e input blocks continuation) =
    Step.op e input blocks continuation from dest_opAt e input blocks continuation]
  rw [dest_opAt]
  simp only [Step.op]

/-- Public scoped bind node.  Public block computations are embedded into the corresponding
    internal block fibers. -/
def op {α : Type u} (e : H.op) (input : H.input e)
    (blocks : (b : H.Block e) → CompE H (H.branchOutput e b.1))
    (k : H.output e → CompE H α) : CompE H α :=
  opAt e input (fun b => asBlock (blocks b)) k

@[simp] theorem dest_op {α : Type u} (e : H.op) (input : H.input e)
    (blocks : (b : H.Block e) → CompE H (H.branchOutput e b.1))
    (k : H.output e → CompE H α) :
    dest (op e input blocks k) =
      Step.op e input (fun b => asBlock (blocks b)) k := dest_mkAt _

/-- A destructor view for every internal result label.  At block labels, `ret` returns the
    branch result computed from the label. -/
theorem cases_viewAt {α : Type u} {i : Ix H} (x : Tree H α i) :
    (∃ a : result H α i, x = retAt a) ∨
    x = failAt ∨
    (∃ t : Tree H α i, x = tauAt t) ∨
    (∃ (e : H.op) (input : H.input e)
      (blocks : (b : H.Block e) → BlockE H α e b)
      (k : H.output e → Tree H α i), x = opAt e input blocks k) := by
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

  | .op e input, c, hd =>
      exact Or.inr (Or.inr (Or.inr
        ⟨e, input, (fun b => (c (Ar.block b) : BlockE H α e b)),
          (fun o => c (Ar.cont o)),
          eq_of_destAt_eq (by
            rw [hd]
            change ⟨Pos.op e input, c⟩ =
              destAt (opAt e input
                (fun b => (c (Ar.block b) : BlockE H α e b))
                (fun o => c (Ar.cont o)))
            rw [dest_opAt]
            refine Sigma.ext rfl ?_
            apply heq_of_eq
            funext h
            cases h <;> rfl)⟩))

/-- A destructor view for public computations.  Scoped block children are exposed in the
    internal block fibers, which is the form used by the monad laws. -/
theorem cases_view {α : Type u} (x : CompE H α) :
    (∃ a, x = ret a) ∨
    x = fail ∨
    (∃ t, x = tau t) ∨
    (∃ (e : H.op) (input : H.input e)
      (blocks : (b : H.Block e) → BlockE H α e b)
      (k : H.output e → CompE H α), x = opAt e input blocks k) := by
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

  | .op e input, c, hd =>
      exact Or.inr (Or.inr (Or.inr
        ⟨e, input, (fun b => (c (Ar.block b) : BlockE H α e b)),
          (fun o => c (Ar.cont o)),
          eq_of_dest_eq (by
            rw [hd]
            change ⟨Pos.op e input, c⟩ =
              destAt (opAt e input
                (fun b => (c (Ar.block b) : BlockE H α e b))
                (fun o => c (Ar.cont o)))
            rw [dest_opAt]
            refine Sigma.ext rfl ?_
            apply heq_of_eq
            funext h
            cases h <;> rfl)⟩))

private inductive BindState (H : HSig.{u, v}) (α β : Type u)
    (target : Ix H) :
    Ix H → Type (max u v) where
  | bind : CompE H α → BindState H α β target target
  | copy {i : Ix H} : Tree H β i → BindState H α β target i

private def bindCo {α β : Type u} {target : Ix H}
    (k : α → Tree H β target) :
    (i : Ix H) → BindState H α β target i →
      Step H β (BindState H α β target) i
  | _, .copy t =>
      match destAt t with
      | ⟨p, c⟩ => ⟨p, fun a => .copy (c a)⟩
  | _, .bind m =>
      match dest m with
      | ⟨.ret a, _⟩ =>
          match destAt (k a) with
          | ⟨p, c⟩ => ⟨p, fun x => .copy (c x)⟩
      | ⟨.tau, c⟩ => Step.tau (.bind (c Ar.tau : CompE H α))
      | ⟨.fail, _⟩ => Step.fail

      | ⟨.op e input, c⟩ =>
          Step.op e input
            (fun b => .copy (relabelBlock (c (Ar.block b) : BlockE H α e b)))
            (fun o => .bind (c (Ar.cont o) : CompE H α))

@[simp] private theorem bindCo_bind_ret {α β : Type u} {target : Ix H}
    (k : α → Tree H β target) (a : α) :
    bindCo (H := H) (target := target) k target (.bind (ret a)) =
      match destAt (k a) with
      | ⟨p, c⟩ => ⟨p, fun x => BindState.copy (H := H) (target := target) (c x)⟩ := by
  rw [bindCo, dest_ret]
  rfl

@[simp] private theorem bindCo_bind_tau {α β : Type u} {target : Ix H}
    (k : α → Tree H β target) (t : CompE H α) :
    bindCo (H := H) (target := target) k target (.bind (tau t)) =
      Step.tau (BindState.bind (H := H) (β := β) (target := target) t) := by
  rw [bindCo, dest_tau]
  rfl

@[simp] private theorem bindCo_bind_fail {α β : Type u} {target : Ix H}
    (k : α → Tree H β target) :
    bindCo (H := H) (target := target) k target
        (.bind (fail : CompE H α)) =
      Step.fail := by
  rw [bindCo, dest_fail]
  rfl

@[simp] private theorem bindCo_bind_opAt {α β : Type u} {target : Ix H}
    (k : α → Tree H β target) (e : H.op) (input : H.input e)
    (blocks : (b : H.Block e) → BlockE H α e b)
    (c : H.output e → CompE H α) :
    bindCo (H := H) (target := target) k target
        (.bind (opAt e input blocks c)) =
      Step.op e input
        (fun b => BindState.copy (H := H) (target := target)
          (relabelBlock (α := α) (β := β) (blocks b)))
        (fun o => BindState.bind (H := H) (β := β) (target := target) (c o)) := by
  rw [bindCo]
  change (match destAt (opAt e input blocks c) with
    | ⟨.ret a, _⟩ =>
        match destAt (k a) with
        | ⟨p, c⟩ => ⟨p, fun x => BindState.copy (H := H) (target := target) (c x)⟩
    | ⟨.tau, c⟩ =>
        Step.tau (BindState.bind (H := H) (β := β) (target := target)
          (c Ar.tau : CompE H α))
    | ⟨.fail, _⟩ => Step.fail

    | ⟨.op e input, c⟩ =>
        Step.op e input
          (fun b => BindState.copy (H := H) (target := target)
            (relabelBlock (α := α) (β := β)
              (c (Ar.block b) : BlockE H α e b)))
          (fun o => BindState.bind (H := H) (β := β) (target := target)
            (c (Ar.cont o) : CompE H α))) =
      Step.op e input
        (fun b => BindState.copy (H := H) (target := target)
          (relabelBlock (α := α) (β := β) (blocks b)))
        (fun o => BindState.bind (H := H) (β := β) (target := target) (c o))
  rw [dest_opAt]
  rfl

/-- Monadic bind: graft at `ret` leaves and continue through operation continuations, but do not
    bind under scoped blocks. -/
def bindAt {α β : Type u} {i : Ix H} (m : CompE H α)
    (k : α → Tree H β i) : Tree H β i :=
  corecAt (bindCo (target := i) k) (.bind m)

/-- Public monadic bind. -/
def bind {α β : Type u} (m : CompE H α) (k : α → CompE H β) :
    CompE H β :=
  bindAt m k

instance : Monad (CompE H) where
  pure := ret
  bind := bind

@[simp] theorem pure_def {α : Type u} (a : α) : (pure a : CompE H α) = ret a := rfl

@[simp] theorem bind_def {α β : Type u} (m : CompE H α) (k : α → CompE H β) :
    m >>= k = bind m k := rfl

theorem corec_copy {α β : Type u} {i : Ix H}
    {target : Ix H} (k : α → Tree H β target)
    (t : Tree H β i) :
    IxPFunctor.M.corec (P := P H β) (bindCo (target := target) k)
      (.copy t : BindState H α β target i) = t := by
  refine IxPFunctor.M.bisim (P := P H β)
    (fun i x y =>
      x = IxPFunctor.M.corec (P := P H β) (bindCo (target := target) k)
        (.copy y : BindState H α β target i)) ?_ _ _ rfl
  intro i x y hxy
  subst hxy
  obtain ⟨p, c, hy⟩ : ∃ p c, destAt y = ⟨p, c⟩ := ⟨_, _, rfl⟩
  refine ⟨p,
    fun a => IxPFunctor.M.corec (P := P H β) (bindCo (target := target) k)
      (.copy (c a) : BindState H α β target ((P H β).next p a)),
    c, ?_, hy, fun a => rfl⟩
  rw [IxPFunctor.M.dest_corec]
  change (P H β).map
      (fun i => IxPFunctor.M.corec (P := P H β) (bindCo (target := target) k) (i := i))
      (bindCo (H := H) (target := target) k i
        (.copy y : BindState H α β target i)) =
    ⟨p,
      fun a => IxPFunctor.M.corec (P := P H β) (bindCo (target := target) k)
        (.copy (c a) : BindState H α β target ((P H β).next p a))⟩
  rw [bindCo, hy]
  rfl

@[simp] theorem bindAt_ret {α β : Type u} {i : Ix H} (a : α)
    (k : α → Tree H β i) : bindAt (ret a) k = k a := by
  apply eq_of_destAt_eq
  obtain ⟨p, c, hk⟩ : ∃ p c, destAt (k a) = ⟨p, c⟩ := ⟨_, _, rfl⟩
  rw [bindAt, dest_corecAt, bindCo_bind_ret, hk]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext x
  exact corec_copy (k := k) (c x)

@[simp] theorem bindAt_tau {α β : Type u} {i : Ix H} (t : CompE H α)
    (k : α → Tree H β i) : bindAt (tau t) k = tauAt (bindAt t k) := by
  apply eq_of_destAt_eq
  rw [bindAt, dest_corecAt, bindCo_bind_tau, dest_tauAt]
  simp only [IxPFunctor.map, Step.tau]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar
  rfl

@[simp] theorem bindAt_fail {α β : Type u} {i : Ix H}
    (k : α → Tree H β i) : bindAt (fail : CompE H α) k = failAt := by
  apply eq_of_destAt_eq
  rw [bindAt, dest_corecAt, bindCo_bind_fail, dest_failAt]
  simp only [IxPFunctor.map, Step.fail]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext impossible
  nomatch impossible

@[simp] theorem bindAt_opAt {α β : Type u} {i : Ix H}
    (e : H.op) (input : H.input e)
    (blocks : (b : H.Block e) → BlockE H α e b)
    (c : H.output e → CompE H α) (k : α → Tree H β i) :
    bindAt (opAt e input blocks c) k =
      opAt e input (fun b => relabelBlock (blocks b))
        (fun output => bindAt (c output) k) := by
  apply eq_of_destAt_eq
  rw [bindAt, dest_corecAt, bindCo_bind_opAt, dest_opAt]
  simp only [IxPFunctor.map, Step.op]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar with
  | block b => exact corec_copy (k := k) (relabelBlock (blocks b))
  | cont output => rfl

private inductive AsBlockBindRel {α : Type u} (root : H.op) (branch : H.Block root) :
    (i : Ix H) → Tree H α i → Tree H α i → Prop where
  | root (tree : CompE H (H.branchOutput root branch.1)) :
      AsBlockBindRel root branch (.block root branch)
        (asBlock (α := α) tree)
        (bindAt tree (fun value => retAt value))
  | eq {i : Ix H} {left right : Tree H α i} (equal : left = right) :
      AsBlockBindRel root branch i left right

/-- `asBlock` is the non-normal unit bind. This equation is the useful semantic interface;
the corecursor implementation above exists only to satisfy strict positivity. -/
theorem asBlock_eq_bindAt {α : Type u} {root : H.op} {branch : H.Block root}
    (tree : CompE H (H.branchOutput root branch.1)) :
    asBlock (α := α) tree = bindAt tree (fun value => retAt value) := by
  refine IxPFunctor.M.bisim (P := P H α) (AsBlockBindRel root branch) ?_
    _ _ (.root tree)
  intro i left right related
  cases related with
  | eq equal =>
      cases equal
      obtain ⟨position, children, equation⟩ : ∃ p c, destAt left = ⟨p, c⟩ :=
        ⟨_, _, rfl⟩
      exact ⟨position, children, children, equation, equation, fun _ => .eq rfl⟩
  | root tree =>
      rcases cases_view tree with
        ⟨value, rfl⟩ | rfl | ⟨child, rfl⟩ |
          ⟨operation, input, blocks, continuation, rfl⟩
      · rw [asBlock_ret, bindAt_ret]
        let step : Step H α (Tree H α) (.block root branch) := Step.ret value
        exact ⟨step.1, step.2, step.2, raw_dest_mkAt step, raw_dest_mkAt step,
          fun impossible => nomatch impossible⟩
      · rw [asBlock_fail, bindAt_fail]
        let step : Step H α (Tree H α) (.block root branch) := Step.fail
        exact ⟨step.1, step.2, step.2, raw_dest_mkAt step, raw_dest_mkAt step,
          fun impossible => nomatch impossible⟩
      · rw [asBlock_tau, bindAt_tau]
        let leftStep : Step H α (Tree H α) (.block root branch) :=
          Step.tau (asBlock (α := α) child)
        let rightStep : Step H α (Tree H α) (.block root branch) :=
          Step.tau (bindAt child (fun value => retAt value))
        exact ⟨.tau, leftStep.2, rightStep.2,
          raw_dest_mkAt leftStep, raw_dest_mkAt rightStep, fun ar => by
            cases ar
            exact .root child⟩
      · rw [asBlock_opAt, bindAt_opAt]
        let leftStep : Step H α (Tree H α) (.block root branch) :=
          Step.op operation input
            (fun b => relabelBlock (blocks b))
            (fun output => asBlock (α := α) (continuation output))
        let rightStep : Step H α (Tree H α) (.block root branch) :=
          Step.op operation input
            (fun b => relabelBlock (blocks b))
            (fun output => bindAt (continuation output) (fun value => retAt value))
        exact ⟨.op operation input, leftStep.2, rightStep.2,
          raw_dest_mkAt leftStep, raw_dest_mkAt rightStep, fun ar => by
            cases ar with
            | block b => exact .eq rfl
            | cont output => exact .root (continuation output)⟩

@[simp] theorem bind_ret {α β : Type u} (a : α) (k : α → CompE H β) :
    bind (ret a) k = k a := by
  apply eq_of_dest_eq
  change destAt (bind (ret a) k) = destAt (k a)
  obtain ⟨p, c, hk⟩ : ∃ p c, destAt (k a) = ⟨p, c⟩ := ⟨_, _, rfl⟩
  rw [bind, bindAt, dest_corecAt, bindCo_bind_ret, hk]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext x
  exact corec_copy (k := k) (c x)

@[simp] theorem bind_tau {α β : Type u} (t : CompE H α) (k : α → CompE H β) :
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

@[simp] theorem bind_fail {α β : Type u} (k : α → CompE H β) :
    bind (fail : CompE H α) k = fail := by
  apply eq_of_dest_eq
  change destAt (bindAt (fail : CompE H α) k) =
    destAt (failAt (H := H) (α := β) (i := .normal))
  rw [bindAt, dest_corecAt, bindCo_bind_fail, dest_failAt]
  simp only [IxPFunctor.map, Step.fail]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext x
  nomatch x

@[simp] theorem bind_opAt {α β : Type u} (e : H.op) (input : H.input e)
    (blocks : (b : H.Block e) → BlockE H α e b)
    (c : H.output e → CompE H α) (k : α → CompE H β) :
    bind (opAt e input blocks c) k =
      opAt e input (fun b => relabelBlock (blocks b)) (fun o => bind (c o) k) := by
  apply eq_of_dest_eq
  change destAt (bind (opAt e input blocks c) k) =
    destAt (opAt e input (fun b => relabelBlock (blocks b)) (fun o => bind (c o) k))
  rw [bind, bindAt, dest_corecAt, bindCo_bind_opAt, dest_opAt]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext x
  cases x with
  | block b =>
      exact corec_copy (k := k) (relabelBlock (α := α) (β := β) (blocks b))
  | cont o =>
      rfl

private inductive RelabelIdRel {α : Type u} :
    (i : Ix H) → Tree H α i → Tree H α i → Prop where
  | block {e : H.op} {b : H.Block e} (t : BlockE H α e b) :
      RelabelIdRel (.block e b) (relabelBlock (α := α) (β := α) t) t
  | eq {i : Ix H} {x y : Tree H α i} (hxy : x = y) : RelabelIdRel i x y

private theorem relabelBlock_id {α : Type u} {e : H.op} {b : H.Block e}
    (t : BlockE H α e b) : relabelBlock (α := α) (β := α) t = t := by
  refine IxPFunctor.M.bisim (P := P H α) RelabelIdRel ?_ _ _ (.block t)
  intro i x y hxy
  cases hxy with
  | eq hxy =>
      cases hxy
      obtain ⟨p, c, hd⟩ : ∃ p c, IxPFunctor.M.dest x = ⟨p, c⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c, c, hd, hd, fun _ => .eq rfl⟩
  | block t =>
      rcases cases_viewAt t with
        ⟨a, ht⟩ | ht | ⟨t', ht⟩ | ⟨e, input, blocks, k, ht⟩
      · cases ht
        refine ⟨(Step.ret a).1, (Step.ret a).2, (Step.ret a).2, ?_,
          raw_dest_mkAt (Step.ret a), fun h => nomatch h⟩
        rw [relabelBlock, raw_dest_corecAt]
        change (P H α).map
            (fun i => corecAt (relabelBlockCo (α := α) (β := α)) (i := i))
            (relabelBlockCo (H := H) (α := α) (β := α) _ (.block (retAt a))) =
          Step.ret a
        rw [relabelBlockCo, dest_retAt]
        simp only [IxPFunctor.map, Step.ret]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext x
        nomatch x
      · cases ht
        refine ⟨(Step.fail : Step H α (Tree H α) _).1,
          (Step.fail : Step H α (Tree H α) _).2,
          (Step.fail : Step H α (Tree H α) _).2, ?_,
          raw_dest_mkAt Step.fail, fun h => nomatch h⟩
        rw [relabelBlock, raw_dest_corecAt]
        change (P H α).map
            (fun i => corecAt (relabelBlockCo (α := α) (β := α)) (i := i))
            (relabelBlockCo (H := H) (α := α) (β := α) _ (.block failAt)) =
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
          change (P H α).map
              (fun i => corecAt (relabelBlockCo (α := α) (β := α)) (i := i))
              (relabelBlockCo (H := H) (α := α) (β := α) _ (.block (tauAt t'))) =
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
        refine ⟨(Step.op e input
            (fun b => relabelBlock (α := α) (β := α) (blocks b))
            (fun o => relabelBlock (α := α) (β := α) (k o))).1,
          (Step.op e input
            (fun b => relabelBlock (α := α) (β := α) (blocks b))
            (fun o => relabelBlock (α := α) (β := α) (k o))).2,
          (Step.op e input blocks k).2, ?_,
          raw_dest_mkAt (Step.op e input blocks k), ?_⟩
        · rw [relabelBlock, raw_dest_corecAt]
          change (P H α).map
              (fun i => corecAt (relabelBlockCo (α := α) (β := α)) (i := i))
              (relabelBlockCo (H := H) (α := α) (β := α) _
                (.block (opAt e input blocks k))) =
            Step.op e input
              (fun b => relabelBlock (α := α) (β := α) (blocks b))
              (fun o => relabelBlock (α := α) (β := α) (k o))
          rw [relabelBlockCo, dest_opAt]
          simp only [IxPFunctor.map, Step.op]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext x
          cases x <;> rfl
        · intro x
          cases x with
          | block b => exact .block (blocks b)
          | cont o => exact .block (k o)

theorem dest_relabelBlock {α β : Type u} {e₀ : H.op} {b₀ : H.Block e₀}
    (t : BlockE H α e₀ b₀) :
    destAt (relabelBlock (α := α) (β := β) t) =
      match destAt t with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ =>
          Step.tau (relabelBlock (α := α) (β := β)
            (c Ar.tau : BlockE H α e₀ b₀))
      | ⟨.fail, _⟩ => Step.fail

      | ⟨.op e input, c⟩ =>
          Step.op e input
            (fun b => relabelBlock (α := α) (β := β)
              (c (Ar.block b) : BlockE H α e b))
            (fun o => relabelBlock (α := α) (β := β)
              (c (Ar.cont o) : BlockE H α e₀ b₀)) := by
  obtain ⟨p, c, ht⟩ : ∃ p c, destAt t = ⟨p, c⟩ := ⟨_, _, rfl⟩
  match p, c, ht with
  | .ret a, c, ht =>
      rw [ht, relabelBlock, dest_corecAt]
      change (P H β).map
          (fun i => corecAt (relabelBlockCo (α := α) (β := β)) (i := i))
          (relabelBlockCo (H := H) (α := α) (β := β) _ (.block t)) =
        Step.ret (H := H) (α := β) (i := .block e₀ b₀) a
      rw [relabelBlockCo, ht]
      simp only [IxPFunctor.map, Step.ret]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext h
      nomatch h
  | .fail, c, ht =>
      rw [ht, relabelBlock, dest_corecAt]
      change (P H β).map
          (fun i => corecAt (relabelBlockCo (α := α) (β := β)) (i := i))
          (relabelBlockCo (H := H) (α := α) (β := β) _ (.block t)) =
        Step.fail (H := H) (α := β) (i := .block e₀ b₀)
      rw [relabelBlockCo, ht]
      simp only [IxPFunctor.map, Step.fail]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext h
      nomatch h
  | .tau, c, ht =>
      rw [ht, relabelBlock, dest_corecAt]
      change (P H β).map
          (fun i => corecAt (relabelBlockCo (α := α) (β := β)) (i := i))
          (relabelBlockCo (H := H) (α := α) (β := β) _ (.block t)) =
        Step.tau (relabelBlock (α := α) (β := β)
          (c Ar.tau : BlockE H α e₀ b₀))
      rw [relabelBlockCo, ht]
      simp only [IxPFunctor.map, Step.tau]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext h
      cases h
      rfl

  | .op e input, c, ht =>
      rw [ht, relabelBlock, dest_corecAt]
      change (P H β).map
          (fun i => corecAt (relabelBlockCo (α := α) (β := β)) (i := i))
          (relabelBlockCo (H := H) (α := α) (β := β) _ (.block t)) =
        Step.op e input
          (fun b => relabelBlock (α := α) (β := β)
            (c (Ar.block b) : BlockE H α e b))
          (fun o => relabelBlock (α := α) (β := β)
            (c (Ar.cont o) : BlockE H α e₀ b₀))
      rw [relabelBlockCo, ht]
      simp only [IxPFunctor.map, Step.op]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext h
      cases h <;> rfl

@[simp] theorem relabelBlock_retAt {α β : Type u} {e : H.op} {b : H.Block e}
    (value : H.branchOutput e b.1) :
    relabelBlock (α := α) (β := β)
      (retAt value : BlockE H α e b) = retAt value := by
  apply eq_of_destAt_eq
  simp only [dest_relabelBlock, dest_retAt, Step.ret]

@[simp] theorem relabelBlock_tauAt {α β : Type u} {e : H.op} {b : H.Block e}
    (tree : BlockE H α e b) :
    relabelBlock (α := α) (β := β) (tauAt tree) =
      tauAt (relabelBlock (α := α) (β := β) tree) := by
  apply eq_of_destAt_eq
  simp only [dest_relabelBlock, dest_tauAt, Step.tau]

@[simp] theorem relabelBlock_failAt {α β : Type u} {e : H.op} {b : H.Block e} :
    relabelBlock (α := α) (β := β) (failAt : BlockE H α e b) = failAt := by
  apply eq_of_destAt_eq
  simp only [dest_relabelBlock, dest_failAt, Step.fail]

theorem relabelBlock_opAt {α β : Type u} {root : H.op} {rootBranch : H.Block root}
    (operation : H.op) (input : H.input operation)
    (blocks : (branch : H.Block operation) → BlockE H α operation branch)
    (continuation : H.output operation → BlockE H α root rootBranch) :
    relabelBlock (α := α) (β := β)
        (opAt operation input blocks continuation) =
      opAt operation input
        (fun branch => relabelBlock (α := α) (β := β) (blocks branch))
        (fun output => relabelBlock (α := α) (β := β)
          (continuation output)) := by
  apply eq_of_destAt_eq
  rw [dest_relabelBlock, dest_opAt, dest_opAt]
  simp only [Step.op]

private inductive RelabelCompRel {α β γ : Type u} :
    (i : Ix H) → Tree H γ i → Tree H γ i → Prop where
  | block {e : H.op} {b : H.Block e} (t : BlockE H α e b) :
      RelabelCompRel (.block e b)
        (relabelBlock (α := β) (β := γ) (relabelBlock (α := α) (β := β) t))
        (relabelBlock (α := α) (β := γ) t)
  | eq {i : Ix H} {x y : Tree H γ i} (hxy : x = y) : RelabelCompRel i x y

private theorem relabelBlock_comp {α β γ : Type u} {e : H.op} {b : H.Block e}
    (t : BlockE H α e b) :
    relabelBlock (α := β) (β := γ) (relabelBlock (α := α) (β := β) t) =
      relabelBlock (α := α) (β := γ) t := by
  refine IxPFunctor.M.bisim (P := P H γ) RelabelCompRel ?_ _ _ (.block t)
  intro i x y hxy
  cases hxy with
  | eq hxy =>
      cases hxy
      obtain ⟨p, c, hd⟩ : ∃ p c, IxPFunctor.M.dest x = ⟨p, c⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c, c, hd, hd, fun _ => .eq rfl⟩
  | block t =>
      rcases cases_viewAt t with
        ⟨a, ht⟩ | ht | ⟨t', ht⟩ | ⟨e, input, blocks, k, ht⟩
      · cases ht
        let lhs := relabelBlock (H := H) (α := β) (β := γ)
          (relabelBlock (α := α) (β := β) (retAt a))
        let rhs := relabelBlock (H := H) (α := α) (β := γ) (retAt a)
        have hdest : IxPFunctor.M.dest lhs = IxPFunctor.M.dest rhs := by
          change destAt lhs = destAt rhs
          dsimp [lhs, rhs]
          rw [dest_relabelBlock, dest_relabelBlock, dest_retAt]
          rw [dest_relabelBlock, dest_retAt]
          simp only [Step.ret]
        obtain ⟨p, c, hy⟩ : ∃ p c, IxPFunctor.M.dest rhs = ⟨p, c⟩ := ⟨_, _, rfl⟩
        exact ⟨p, c, c, hdest.trans hy, hy, fun _ => .eq rfl⟩
      ·
        let lhs := relabelBlock (H := H) (α := β) (β := γ)
          (relabelBlock (α := α) (β := β) t)
        let rhs := relabelBlock (H := H) (α := α) (β := γ)
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
        let sx : Step H γ (Tree H γ) _ :=
          Step.tau (relabelBlock (α := β) (β := γ)
            (relabelBlock (α := α) (β := β) t'))
        let sy : Step H γ (Tree H γ) _ :=
          Step.tau (relabelBlock (α := α) (β := γ) t')
        refine ⟨sx.1, sx.2, sy.2, ?_, ?_, ?_⟩
        · change destAt (relabelBlock (relabelBlock (tauAt t'))) = sx
          rw [dest_relabelBlock, dest_relabelBlock, dest_tauAt]
          rfl
        · change destAt (relabelBlock (tauAt t')) = sy
          rw [dest_relabelBlock, dest_tauAt]
          rfl
        · intro h
          cases h
          exact .block t'
      · cases ht
        let sx : Step H γ (Tree H γ) _ :=
          Step.op e input
            (fun b => relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (blocks b)))
            (fun o => relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (k o)))
        let sy : Step H γ (Tree H γ) _ :=
          Step.op e input
            (fun b => relabelBlock (α := α) (β := γ) (blocks b))
            (fun o => relabelBlock (α := α) (β := γ) (k o))
        refine ⟨sx.1, sx.2, sy.2, ?_, ?_, ?_⟩
        · change destAt (relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (opAt e input blocks k))) = sx
          rw [dest_relabelBlock, dest_relabelBlock, dest_opAt]
          simp only [Step.op]
          dsimp [sx, Step.op]
        · change destAt (relabelBlock (α := α) (β := γ) (opAt e input blocks k)) = sy
          rw [dest_relabelBlock, dest_opAt]
          simp only [Step.op]
          dsimp [sy, Step.op]
        · intro h
          cases h with
          | block b => exact .block (blocks b)
          | cont o => exact .block (k o)

private inductive BindAtAssocRel {α β γ : Type u} {target : Ix H}
    (k : α → CompE H β) (h : β → Tree H γ target) :
    (i : Ix H) → Tree H γ i → Tree H γ i → Prop where
  | root (tree : CompE H α) :
      BindAtAssocRel k h target
        (bindAt (bind tree k) h)
        (bindAt tree fun value => bindAt (k value) h)
  | eq {i : Ix H} {left right : Tree H γ i} (equal : left = right) :
      BindAtAssocRel k h i left right

/-- Associativity when the final continuation returns into any internal result fiber. -/
theorem bindAt_assoc {α β γ : Type u} {target : Ix H} (tree : CompE H α)
    (k : α → CompE H β) (h : β → Tree H γ target) :
    bindAt (bind tree k) h = bindAt tree (fun value => bindAt (k value) h) := by
  refine IxPFunctor.M.bisim (P := P H γ) (BindAtAssocRel k h) ?_
    _ _ (.root tree)
  intro i left right related
  cases related with
  | eq equal =>
      cases equal
      obtain ⟨position, children, equation⟩ : ∃ p c, destAt left = ⟨p, c⟩ :=
        ⟨_, _, rfl⟩
      exact ⟨position, children, children, equation, equation, fun _ => .eq rfl⟩
  | root tree =>
      rcases cases_view tree with
        ⟨value, rfl⟩ | rfl | ⟨child, rfl⟩ |
          ⟨operation, input, blocks, continuation, rfl⟩
      · simp only [bind_ret, bindAt_ret]
        obtain ⟨position, children, equation⟩ :
            ∃ p c, destAt (bindAt (k value) h) = ⟨p, c⟩ := ⟨_, _, rfl⟩
        exact ⟨position, children, children, equation, equation, fun _ => .eq rfl⟩
      · simp only [bind_fail, bindAt_fail]
        let step : Step H γ (Tree H γ) target := Step.fail
        exact ⟨step.1, step.2, step.2, raw_dest_mkAt step, raw_dest_mkAt step,
          fun impossible => nomatch impossible⟩
      · simp only [bind_tau, bindAt_tau]
        let leftStep : Step H γ (Tree H γ) target :=
          Step.tau (bindAt (bind child k) h)
        let rightStep : Step H γ (Tree H γ) target :=
          Step.tau (bindAt child fun value => bindAt (k value) h)
        exact ⟨.tau, leftStep.2, rightStep.2,
          raw_dest_mkAt leftStep, raw_dest_mkAt rightStep, fun ar => by
            cases ar
            exact .root child⟩
      · simp only [bind_opAt, bindAt_opAt]
        let leftStep : Step H γ (Tree H γ) target :=
          Step.op operation input
            (fun branch => relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (blocks branch)))
            (fun output => bindAt (bind (continuation output) k) h)
        let rightStep : Step H γ (Tree H γ) target :=
          Step.op operation input
            (fun branch => relabelBlock (α := α) (β := γ) (blocks branch))
            (fun output => bindAt (continuation output)
              (fun value => bindAt (k value) h))
        exact ⟨.op operation input, leftStep.2, rightStep.2,
          raw_dest_mkAt leftStep, raw_dest_mkAt rightStep, fun ar => by
            cases ar with
            | block branch => exact .eq (relabelBlock_comp (blocks branch))
            | cont output => exact .root (continuation output)⟩

theorem asBlock_bind {α γ : Type u} {root : H.op} {branch : H.Block root}
    (tree : CompE H α)
    (k : α → CompE H (H.branchOutput root branch.1)) :
    asBlock (α := γ) (bind tree k) =
      bindAt tree (fun value => asBlock (α := γ) (k value)) := by
  rw [asBlock_eq_bindAt, bindAt_assoc]
  apply congrArg (bindAt tree)
  funext value
  exact (asBlock_eq_bindAt (k value)).symm

private inductive RelabelBindRel {α β γ : Type u}
    (root : H.op) (branch : H.Block root)
    (k : α → BlockE H β root branch) :
    (i : Ix H) → Tree H γ i → Tree H γ i → Prop where
  | root (tree : CompE H α) :
      RelabelBindRel root branch k (.block root branch)
        (relabelBlock (α := β) (β := γ) (bindAt tree k))
        (bindAt tree fun value => relabelBlock (α := β) (β := γ) (k value))
  | eq {i : Ix H} {left right : Tree H γ i} (equal : left = right) :
      RelabelBindRel root branch k i left right

theorem relabelBlock_bind {α β γ : Type u}
    {root : H.op} {branch : H.Block root} (tree : CompE H α)
    (k : α → BlockE H β root branch) :
    relabelBlock (α := β) (β := γ) (bindAt tree k) =
      bindAt tree (fun value => relabelBlock (α := β) (β := γ) (k value)) := by
  refine IxPFunctor.M.bisim (P := P H γ) (RelabelBindRel root branch k) ?_
    _ _ (.root tree)
  intro i left right related
  cases related with
  | eq equal =>
      cases equal
      obtain ⟨position, children, equation⟩ : ∃ p c, destAt left = ⟨p, c⟩ :=
        ⟨_, _, rfl⟩
      exact ⟨position, children, children, equation, equation, fun _ => .eq rfl⟩
  | root tree =>
      rcases cases_view tree with
        ⟨value, rfl⟩ | rfl | ⟨child, rfl⟩ |
          ⟨operation, input, blocks, continuation, rfl⟩
      · simp only [bindAt_ret]
        obtain ⟨position, children, equation⟩ : ∃ p c,
            destAt (relabelBlock (α := β) (β := γ) (k value)) = ⟨p, c⟩ :=
          ⟨_, _, rfl⟩
        exact ⟨position, children, children, equation, equation, fun _ => .eq rfl⟩
      · simp only [bindAt_fail]
        rw [show relabelBlock (α := β) (β := γ)
          (failAt : BlockE H β root branch) = failAt from by
            apply eq_of_destAt_eq
            rw [dest_relabelBlock, dest_failAt, dest_failAt]
            simp only [Step.fail]]
        let step : Step H γ (Tree H γ) (.block root branch) := Step.fail
        exact ⟨step.1, step.2, step.2, raw_dest_mkAt step, raw_dest_mkAt step,
          fun impossible => nomatch impossible⟩
      · simp only [bindAt_tau]
        rw [show relabelBlock (α := β) (β := γ)
          (tauAt (bindAt child k)) =
            tauAt (relabelBlock (α := β) (β := γ) (bindAt child k)) from by
              apply eq_of_destAt_eq
              rw [dest_relabelBlock, dest_tauAt, dest_tauAt]
              simp only [Step.tau]]
        let leftStep : Step H γ (Tree H γ) (.block root branch) :=
          Step.tau (relabelBlock (α := β) (β := γ) (bindAt child k))
        let rightStep : Step H γ (Tree H γ) (.block root branch) :=
          Step.tau (bindAt child fun value =>
            relabelBlock (α := β) (β := γ) (k value))
        exact ⟨.tau, leftStep.2, rightStep.2,
          raw_dest_mkAt leftStep, raw_dest_mkAt rightStep, fun ar => by
            cases ar
            exact .root child⟩
      · simp only [bindAt_opAt]
        let leftStep : Step H γ (Tree H γ) (.block root branch) :=
          Step.op operation input
            (fun nested => relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (blocks nested)))
            (fun output => relabelBlock (α := β) (β := γ)
              (bindAt (continuation output) k))
        let rightStep : Step H γ (Tree H γ) (.block root branch) :=
          Step.op operation input
            (fun nested => relabelBlock (α := α) (β := γ) (blocks nested))
            (fun output => bindAt (continuation output) fun value =>
              relabelBlock (α := β) (β := γ) (k value))
        refine ⟨.op operation input, leftStep.2, rightStep.2, ?_,
          raw_dest_mkAt rightStep, ?_⟩
        · change destAt (relabelBlock (opAt operation input _ _)) = leftStep
          rw [dest_relabelBlock, dest_opAt]
          rfl
        · intro ar
          cases ar with
                | block nested => exact .eq (relabelBlock_comp (blocks nested))
                | cont output => exact .root (continuation output)

/-- Re-embedding a public computation is independent of the ambient normal-result type. -/
theorem relabelBlock_asBlock {α β : Type u} {root : H.op}
    {branch : H.Block root}
    (tree : CompE H (H.branchOutput root branch.1)) :
    relabelBlock (α := α) (β := β) (asBlock (α := α) tree) =
      asBlock (α := β) tree := by
  rw [asBlock_eq_bindAt, relabelBlock_bind]
  rw [asBlock_eq_bindAt]
  apply congrArg (bindAt tree)
  funext value
  rw [relabelBlock_retAt]

/-- Binding a public operation changes only its ordinary continuation. Scoped branches do not
depend on the ambient result type. -/
theorem bind_op {α β : Type u} (operation : H.op) (input : H.input operation)
    (blocks : (branch : H.Block operation) →
      CompE H (H.branchOutput operation branch.1))
    (continuation : H.output operation → CompE H α) (k : α → CompE H β) :
    bind (op operation input blocks continuation) k =
      op operation input blocks (fun output => bind (continuation output) k) := by
  unfold op
  rw [bind_opAt]
  congr 1
  funext branch
  exact relabelBlock_asBlock (blocks branch)

private inductive BindRightRel {α : Type u} :
    (i : Ix H) → Tree H α i → Tree H α i → Prop where
  | root (m : CompE H α) : BindRightRel .normal (bind m ret) m
  | eq {i : Ix H} {x y : Tree H α i} (hxy : x = y) : BindRightRel i x y

theorem bind_ret_right {α : Type u} (m : CompE H α) : bind m ret = m := by
  refine IxPFunctor.M.bisim (P := P H α) BindRightRel ?_ _ _ (.root m)
  intro i x y hxy
  cases hxy with
  | eq hxy =>
      cases hxy
      obtain ⟨p, c, hd⟩ : ∃ p c, IxPFunctor.M.dest x = ⟨p, c⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c, c, hd, hd, fun _ => .eq rfl⟩
  | root m =>
      rcases cases_view m with
        ⟨a, hm⟩ | hm | ⟨t, hm⟩ | ⟨e, input, blocks, k, hm⟩
      · cases hm
        rw [bind_ret]
        let s : Step H α (Tree H α) .normal := Step.ret a
        refine ⟨s.1, s.2, s.2, ?_, ?_, fun h => nomatch h⟩
        · exact raw_dest_mkAt s
        · exact raw_dest_mkAt s
      · cases hm
        rw [bind_fail]
        refine ⟨(Step.fail : Step H α (Tree H α) .normal).1,
          (Step.fail : Step H α (Tree H α) .normal).2,
          (Step.fail : Step H α (Tree H α) .normal).2,
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
        rw [bind_opAt]
        refine ⟨(Step.op e input
            (fun b => relabelBlock (α := α) (β := α) (blocks b))
            (fun o => bind (k o) ret)).1,
          (Step.op e input
            (fun b => relabelBlock (α := α) (β := α) (blocks b))
            (fun o => bind (k o) ret)).2,
          (Step.op e input blocks k).2,
          raw_dest_mkAt (Step.op e input
            (fun b => relabelBlock (α := α) (β := α) (blocks b))
            (fun o => bind (k o) ret)),
          raw_dest_mkAt (Step.op e input blocks k), ?_⟩
        intro h
        cases h with
        | block b => exact .eq (relabelBlock_id (blocks b))
        | cont o => exact .root (k o)

private inductive BindAssocRel {α β γ : Type u}
    (k : α → CompE H β) (h : β → CompE H γ) :
    (i : Ix H) → Tree H γ i → Tree H γ i → Prop where
  | root (m : CompE H α) :
      BindAssocRel k h .normal
        (bind (bind m k) h)
        (bind m fun a => bind (k a) h)
  | eq {i : Ix H} {x y : Tree H γ i} (hxy : x = y) : BindAssocRel k h i x y

theorem bind_assoc {α β γ : Type u} (m : CompE H α)
    (k : α → CompE H β) (h : β → CompE H γ) :
    bind (bind m k) h = bind m (fun a => bind (k a) h) := by
  refine IxPFunctor.M.bisim (P := P H γ) (BindAssocRel k h) ?_ _ _ (.root m)
  intro i x y hxy
  cases hxy with
  | eq hxy =>
      cases hxy
      obtain ⟨p, c, hd⟩ : ∃ p c, IxPFunctor.M.dest x = ⟨p, c⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c, c, hd, hd, fun _ => .eq rfl⟩
  | root m =>
      rcases cases_view m with
        ⟨a, hm⟩ | hm | ⟨t, hm⟩ | ⟨e, input, blocks, c, hm⟩
      · cases hm
        rw [bind_ret, bind_ret]
        obtain ⟨p, child, hd⟩ :
            ∃ p child, IxPFunctor.M.dest (bind (k a) h) = ⟨p, child⟩ := ⟨_, _, rfl⟩
        exact ⟨p, child, child, hd, hd, fun _ => .eq rfl⟩
      · cases hm
        rw [bind_fail, bind_fail, bind_fail]
        let s : Step H γ (Tree H γ) .normal := Step.fail
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
        rw [bind_opAt, bind_opAt, bind_opAt]
        refine ⟨(Step.op e input
            (fun b => relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (blocks b)))
            (fun o => bind (bind (c o) k) h)).1,
          (Step.op e input
            (fun b => relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (blocks b)))
            (fun o => bind (bind (c o) k) h)).2,
          (Step.op e input
            (fun b => relabelBlock (α := α) (β := γ) (blocks b))
            (fun o => bind (c o) fun a => bind (k a) h)).2,
          raw_dest_mkAt (Step.op e input
            (fun b => relabelBlock (α := β) (β := γ)
              (relabelBlock (α := α) (β := β) (blocks b)))
            (fun o => bind (bind (c o) k) h)),
          raw_dest_mkAt (Step.op e input
            (fun b => relabelBlock (α := α) (β := γ) (blocks b))
            (fun o => bind (c o) fun a => bind (k a) h)), ?_⟩
        intro h'
        cases h' with
        | block b => exact .eq (relabelBlock_comp (blocks b))
        | cont o => exact .root (c o)

instance : LawfulMonad (CompE H) :=
  LawfulMonad.mk' _
    (fun m => bind_ret_right m)
    (fun a k => bind_ret a k)
    (fun m k h => bind_assoc m k h)

end CompE

/-! ## Higher-order signature sums and guarded recursion -/

namespace HSig

@[reducible] def sum (H F : HSig.{u, v}) : HSig.{u, v} where
  op := H.op ⊕ F.op
  input
    | .inl e => H.input e
    | .inr e => F.input e
  output
    | .inl e => H.output e
    | .inr e => F.output e
  branch
    | .inl e => H.branch e
    | .inr e => F.branch e
  branchInput
    | .inl e, b => H.branchInput e b
    | .inr e, b => F.branchInput e b
  branchOutput
    | .inl e, b => H.branchOutput e b
    | .inr e, b => F.branchOutput e b

end HSig

abbrev Sum := HSig.sum

inductive CallOp : Type v where
  | call

abbrev Call (σ ρ : Type u) : HSig.{u, v} where
  op := CallOp
  input := fun _ => σ
  output := fun _ => ρ
  branch := fun _ => PEmpty
  branchInput := fun _ b => nomatch b
  branchOutput := fun _ b => nomatch b

namespace CompE

variable {H F : HSig.{u, v}}

@[reducible] def sumIx : Ix H → Ix (Sum H F)
  | .normal => .normal
  | .block e bx => .block (.inl e) bx

private inductive SumState (H F : HSig.{u, v}) (α : Type u) : Ix (Sum H F) → Type (max u v) where
  | tree {i : Ix H} : Tree H α i → SumState H F α (sumIx i)

def sumCo : (i : Ix (Sum H F)) → SumState H F α i →
    Step (Sum H F) α (SumState H F α) i
  | _, @SumState.tree _ _ _ j t =>
      match destAt t with
      | ⟨.ret a, _⟩ => Step.ret (cast (by cases j <;> rfl) a)
      | ⟨.tau, c⟩ => Step.tau (.tree (c Ar.tau))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.op e input, c⟩ => Step.op (.inl e) input
          (fun bx => .tree (c (Ar.block bx)))
          (fun o => .tree (c (Ar.cont o)))

def sumL {α : Type u} (t : CompE H α) : CompE (Sum H F) α :=
  corecAt sumCo (.tree t)

set_option backward.isDefEq.respectTransparency true in
@[simp] theorem sumL_ret {α : Type u} (a : α) :
    sumL (F := F) (ret (H := H) a) = ret a := by
  change corecAt sumCo (SumState.tree (retAt (H := H) (i := .normal) a)) =
    retAt (H := Sum H F) (i := .normal) a
  apply eq_of_dest_eq
  change destAt (corecAt sumCo (SumState.tree (retAt (H := H) (i := .normal) a))) =
    destAt (retAt (H := Sum H F) (i := .normal) a)
  rw [dest_corecAt]
  simp only [sumIx]
  rw [dest_retAt]
  change (P (Sum H F) α).map _
      (sumCo (H := H) (F := F) .normal
        (SumState.tree (retAt (H := H) (i := .normal) a))) = Step.ret a
  change (P (Sum H F) α).map _
      (match destAt (retAt (H := H) (i := .normal) a) with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ => Step.tau (SumState.tree (c Ar.tau))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.op e input, c⟩ => Step.op (.inl e) input
          (fun bx => SumState.tree (c (Ar.block bx)))
          (fun o => SumState.tree (c (Ar.cont o)))) = Step.ret a
  rw [dest_retAt]
  simp only [IxPFunctor.map, Step.ret]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext h
  nomatch h

set_option backward.isDefEq.respectTransparency true in
@[simp] theorem sumL_tau {α : Type u} (t : CompE H α) :
    sumL (F := F) (tau t) = tau (sumL (F := F) t) := by
  apply eq_of_dest_eq
  change destAt (corecAt sumCo (SumState.tree (tauAt t))) =
    destAt (tauAt (corecAt sumCo (SumState.tree t)))
  rw [dest_corecAt]
  simp only [sumIx]
  rw [dest_tauAt]
  change (P (Sum H F) α).map _
      (match destAt (tauAt t) with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ => Step.tau (SumState.tree (c Ar.tau))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.op e input, c⟩ => Step.op (.inl e) input
          (fun bx => SumState.tree (c (Ar.block bx)))
          (fun o => SumState.tree (c (Ar.cont o)))) =
        Step.tau (corecAt sumCo (SumState.tree t))
  rw [dest_tauAt]
  simp only [IxPFunctor.map, Step.tau]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar
  rfl

set_option backward.isDefEq.respectTransparency true in
@[simp] theorem sumL_fail {α : Type u} :
    sumL (F := F) (fail : CompE H α) = fail := by
  apply eq_of_dest_eq
  change destAt (corecAt sumCo (SumState.tree (failAt (H := H)))) =
    destAt (failAt (H := Sum H F))
  rw [dest_corecAt]
  simp only [sumIx]
  rw [dest_failAt]
  change (P (Sum H F) α).map _
      (match destAt (failAt (H := H) (α := α) (i := .normal)) with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ => Step.tau (SumState.tree (c Ar.tau))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.op e input, c⟩ => Step.op (.inl e) input
          (fun bx => SumState.tree (c (Ar.block bx)))
          (fun o => SumState.tree (c (Ar.cont o)))) = Step.fail
  rw [dest_failAt]
  simp only [IxPFunctor.map, Step.fail]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext h
  nomatch h

set_option backward.isDefEq.respectTransparency true in
@[simp] theorem sumL_opAt {α : Type u} (e : H.op) (input : H.input e)
    (blocks : (b : H.Block e) → BlockE H α e b)
    (c : H.output e → CompE H α) :
    sumL (F := F) (opAt e input blocks c) =
      opAt (Sum.inl e) input
        (fun (bx : (Sum H F).Block (Sum.inl e)) =>
          corecAt (sumCo (H := H) (F := F)) (SumState.tree (blocks bx)))
        (fun o => sumL (F := F) (c o)) := by
  apply eq_of_dest_eq
  change destAt (corecAt sumCo (SumState.tree (opAt e input blocks c))) = _
  rw [dest_corecAt]
  simp only [sumIx]
  change (P (Sum H F) α).map _
      (sumCo (H := H) (F := F) .normal (SumState.tree (opAt e input blocks c))) =
    destAt (opAt (Sum.inl e) input
      (fun (bx : (Sum H F).Block (Sum.inl e)) =>
        corecAt sumCo (SumState.tree (blocks bx)))
      (fun o => corecAt sumCo (SumState.tree (c o))))
  rw [dest_opAt]
  change (P (Sum H F) α).map _
      (match destAt (opAt e input blocks c) with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, d⟩ => Step.tau (SumState.tree (d Ar.tau))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.op e input, d⟩ => Step.op (Sum.inl e) input
          (fun bx => SumState.tree (d (Ar.block bx)))
          (fun o => SumState.tree (d (Ar.cont o)))) =
        Step.op (Sum.inl e) input
          (fun (bx : (Sum H F).Block (Sum.inl e)) =>
            corecAt sumCo (SumState.tree (blocks bx)))
          (fun o => corecAt sumCo (SumState.tree (c o)))
  rw [dest_opAt]
  simp only [IxPFunctor.map, Step.op]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar <;> rfl

private theorem dest_sumAt {α : Type u} {i : Ix H} (t : Tree H α i) :
    destAt (corecAt (sumCo (H := H) (F := F)) (SumState.tree t)) =
      match destAt t with
      | ⟨.ret a, _⟩ => Step.ret (cast (by cases i <;> rfl) a)
      | ⟨.tau, c⟩ => Step.tau
          (corecAt (sumCo (H := H) (F := F)) (SumState.tree (c Ar.tau)))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.op e input, c⟩ => Step.op (Sum.inl e) input
          (fun bx => corecAt (sumCo (H := H) (F := F))
            (SumState.tree (c (Ar.block bx))))
          (fun o => corecAt (sumCo (H := H) (F := F))
            (SumState.tree (c (Ar.cont o)))) := by
  rw [dest_corecAt]
  obtain ⟨p, c, ht⟩ : ∃ p c, destAt t = ⟨p, c⟩ := ⟨_, _, rfl⟩
  cases i <;> cases p <;>
    simp only [sumCo, IxPFunctor.map] <;>
    rw [ht] <;>
    simp [Step.ret, Step.tau, Step.fail, Step.op]
  all_goals
    funext a
    cases a <;> rfl

private inductive SumRelabelRel {H F : HSig.{u, v}} {α β : Type u} :
    (i : Ix (Sum H F)) → Tree (Sum H F) β i → Tree (Sum H F) β i → Prop where
  | block {e : H.op} {bx : H.Block e} (t : BlockE H α e bx) :
      SumRelabelRel (.block (Sum.inl e) bx)
        (relabelBlock (H := Sum H F) (α := α) (β := β)
          (corecAt (sumCo (H := H) (F := F)) (SumState.tree t)))
        (corecAt (sumCo (H := H) (F := F))
          (SumState.tree (relabelBlock (H := H) (α := α) (β := β) t)))
  | eq {i : Ix (Sum H F)} {x y : Tree (Sum H F) β i} (h : x = y) :
      SumRelabelRel i x y

set_option backward.isDefEq.respectTransparency true in
private theorem sumAt_relabelBlock {α β : Type u} {e : H.op} {bx : H.Block e}
    (t : BlockE H α e bx) :
    relabelBlock (H := Sum H F) (α := α) (β := β)
        (corecAt (sumCo (H := H) (F := F)) (SumState.tree t)) =
      corecAt (sumCo (H := H) (F := F))
        (SumState.tree (relabelBlock (H := H) (α := α) (β := β) t)) := by
  refine IxPFunctor.M.bisim (P := P (Sum H F) β) SumRelabelRel ?_ _ _ (.block t)
  intro i x y hxy
  cases hxy with
  | eq hxy =>
      subst y
      obtain ⟨p, c, hd⟩ : ∃ p c, destAt x = ⟨p, c⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c, c, hd, hd, fun _ => .eq rfl⟩
  | @block root rootBx t =>
      rcases cases_viewAt t with
        ⟨a, rfl⟩ | rfl | ⟨t, rfl⟩ | ⟨e, input, blocks, c, rfl⟩
      · refine ⟨.ret a, (fun h => nomatch h), (fun h => nomatch h), ?_, ?_, ?_⟩
        · change destAt (relabelBlock (corecAt sumCo (SumState.tree (retAt a)))) = _
          rw [dest_relabelBlock, dest_sumAt, dest_retAt]
          simp [Step.ret]
          funext h
          nomatch h
        · change destAt (corecAt sumCo
            (SumState.tree (relabelBlock (retAt a)))) = _
          rw [dest_sumAt, dest_relabelBlock, dest_retAt]
          simp [Step.ret]
          funext h
          nomatch h
        · intro h
          nomatch h
      · refine ⟨.fail, (fun h => nomatch h), (fun h => nomatch h), ?_, ?_, ?_⟩
        · have hd := dest_relabelBlock (H := Sum H F) (β := β)
              (corecAt (sumCo (H := H) (F := F))
                (@SumState.tree H F α (Ix.block root rootBx)
                  (failAt (H := H) (α := α) (i := Ix.block root rootBx))))
          unfold destAt at hd
          rw [hd]
          have hs := dest_sumAt (H := H) (F := F)
            (failAt (H := H) (α := α) (i := Ix.block root rootBx))
          unfold destAt at hs
          rw [hs]
          have hf : IxPFunctor.M.dest
              (failAt (H := H) (α := α) (i := Ix.block root rootBx)) = Step.fail :=
            raw_dest_mkAt Step.fail
          rw [hf]
          simp [Step.fail]
          funext h
          nomatch h
        · have hd := dest_sumAt (H := H) (F := F)
              (relabelBlock (α := α) (β := β)
                (failAt (H := H) (α := α) (i := Ix.block root rootBx)))
          unfold destAt at hd
          rw [hd]
          have hr := dest_relabelBlock (H := H) (β := β)
            (failAt (H := H) (α := α) (i := Ix.block root rootBx))
          unfold destAt at hr
          rw [hr]
          have hf : IxPFunctor.M.dest
              (failAt (H := H) (α := α) (i := Ix.block root rootBx)) = Step.fail :=
            raw_dest_mkAt Step.fail
          rw [hf]
          simp [Step.fail]
          funext h
          nomatch h
        · intro h
          nomatch h
      · refine ⟨.tau,
          (fun a => match a with
            | Ar.tau => relabelBlock (H := Sum H F) (α := α) (β := β)
                (corecAt (sumCo (H := H) (F := F)) (SumState.tree t))),
          (fun a => match a with
            | Ar.tau => corecAt (sumCo (H := H) (F := F))
                (SumState.tree (relabelBlock (α := α) (β := β) t))), ?_, ?_, ?_⟩
        · change destAt (relabelBlock (corecAt sumCo
            (SumState.tree (tauAt t)))) = _
          rw [dest_relabelBlock, dest_sumAt, dest_tauAt]
          simp [Step.tau]
          funext a
          cases a
          rfl
        · change destAt (corecAt sumCo
            (SumState.tree (relabelBlock (tauAt t)))) = _
          rw [dest_sumAt, dest_relabelBlock, dest_tauAt]
          simp [Step.tau]
          funext a
          cases a
          rfl
        · intro a
          cases a
          exact .block t
      · refine ⟨.op (Sum.inl e) input,
          (fun (a : (P (Sum H F) β).Ar (Pos.op (Sum.inl e) input)) => by
            cases a with
            | block bx => exact (relabelBlock (H := Sum H F) (α := α) (β := β)
                (corecAt (sumCo (H := H) (F := F)) (SumState.tree (blocks bx))))
            | cont o => exact (relabelBlock (H := Sum H F) (α := α) (β := β)
                (corecAt (sumCo (H := H) (F := F)) (SumState.tree (c o))))),
          (fun (a : (P (Sum H F) β).Ar (Pos.op (Sum.inl e) input)) => by
            cases a with
            | block bx => exact (corecAt (sumCo (H := H) (F := F))
                (SumState.tree (relabelBlock (α := α) (β := β) (blocks bx))))
            | cont o => exact (corecAt (sumCo (H := H) (F := F))
                (SumState.tree (relabelBlock (α := α) (β := β) (c o))))), ?_, ?_, ?_⟩
        · change destAt (relabelBlock (corecAt sumCo
            (SumState.tree (opAt e input blocks c)))) = _
          rw [dest_relabelBlock, dest_sumAt, dest_opAt]
          simp [Step.op]
          funext a
          cases a <;> rfl
        · change destAt (corecAt sumCo
            (SumState.tree (relabelBlock (opAt e input blocks c)))) = _
          rw [dest_sumAt, dest_relabelBlock, dest_opAt]
          simp [Step.op]
          funext a
          cases a <;> rfl
        · intro a
          cases a with
          | block bx => exact .block (blocks bx)
          | cont o => exact .block (c o)

@[reducible] def sourceIx : Ix H → Ix (Sum H (Call σ ρ))
  | .normal => .normal
  | .block e bx => .block (.inl e) bx

abbrev InterpState (H : HSig.{u, v}) (σ ρ α : Type u) (i : Ix H) :=
  Tree (Sum H (Call σ ρ)) α (sourceIx i)

def interpCoNormal {σ ρ : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ)
    (t : CompE (Sum H (Call σ ρ)) α) :
    Step H α (InterpState H σ ρ α) .normal :=
  match dest t with
  | ⟨.ret a, _⟩ => Step.ret a
  | ⟨.tau, c⟩ => Step.tau (c Ar.tau)
  | ⟨.fail, _⟩ => Step.fail
  | ⟨.op (.inl e) input, c⟩ => Step.op e input
      (fun bx => c (Ar.block bx))
      (fun o => c (Ar.cont o))
  | ⟨.op (.inr .call) s, c⟩ => Step.tau
      (bindAt (body s) fun o => c (Ar.cont o))

def interpCo {σ ρ : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) :
    (i : Ix H) → InterpState H σ ρ α i →
      Step H α (InterpState H σ ρ α) i
  | .normal, t => interpCoNormal body t
  | i@(.block _ _), t =>
      match destAt t with
      | ⟨.ret a, _⟩ => Step.ret (cast (by cases i <;> rfl) a)
      | ⟨.tau, c⟩ => Step.tau (c Ar.tau)
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.op (.inl e) input, c⟩ => Step.op e input
          (fun bx => c (Ar.block bx))
          (fun o => c (Ar.cont o))
      | ⟨.op (.inr .call) s, c⟩ => Step.tau
          (bindAt (body s) fun o => c (Ar.cont o))

def interp {σ ρ α : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ)
    (t : CompE (Sum H (Call σ ρ)) α) : CompE H α :=
  corecAt (interpCo body) t

private theorem interpCo_sumAt {H : HSig.{u, v}} {σ ρ α : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) {i : Ix H} (t : Tree H α i) :
    interpCo body i
        (corecAt (sumCo (H := H) (F := Call σ ρ)) (SumState.tree t)) =
      (P H α).map
        (fun _ child =>
          corecAt (sumCo (H := H) (F := Call σ ρ)) (SumState.tree child))
        (destAt t) := by
  obtain ⟨p, c, ht⟩ : ∃ p c, destAt t = ⟨p, c⟩ := ⟨_, _, rfl⟩
  cases i <;> cases p <;>
    simp only [interpCo, interpCoNormal, dest, dest_corecAt, sumCo,
      IxPFunctor.map] <;>
    rw [ht] <;>
    simp [Step.ret, Step.tau, Step.fail, Step.op]
  all_goals
    funext a
    cases a <;> rfl

private def interpSumAt {H : HSig.{u, v}} {σ ρ α : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) {i : Ix H} (t : Tree H α i) :
    Tree H α i :=
  corecAt (interpCo body)
    (corecAt (sumCo (H := H) (F := Call σ ρ)) (SumState.tree t))

private theorem interpSumAt_eq {H : HSig.{u, v}} {σ ρ α : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) {i : Ix H} (t : Tree H α i) :
    interpSumAt body t = t := by
  refine IxPFunctor.M.bisim (P := P H α)
    (fun _ x y => x = interpSumAt body y) ?_ _ _ rfl
  intro i x y hxy
  subst x
  obtain ⟨p, c, ht⟩ : ∃ p c, destAt y = ⟨p, c⟩ := ⟨_, _, rfl⟩
  cases p with
  | ret a =>
      refine ⟨.ret a, (fun h => nomatch h), c, ?_, ht, ?_⟩
      · rw [interpSumAt, raw_dest_corecAt, interpCo_sumAt, ht]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext h
        cases h
      · intro h
        nomatch h
  | tau =>
      refine ⟨.tau,
        (fun a => match a with
          | Ar.tau => interpSumAt body (c Ar.tau)),
        c, ?_, ht, ?_⟩
      · rw [interpSumAt, raw_dest_corecAt, interpCo_sumAt, ht]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext a
        cases a
        rfl
      · intro a
        cases a
        rfl
  | fail =>
      refine ⟨.fail, (fun h => nomatch h), c, ?_, ht, ?_⟩
      · rw [interpSumAt, raw_dest_corecAt, interpCo_sumAt, ht]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext h
        cases h
      · intro h
        nomatch h
  | op e input =>
      refine ⟨.op e input,
        (fun a => match a with
          | Ar.block bx => interpSumAt body (c (Ar.block bx))
          | Ar.cont o => interpSumAt body (c (Ar.cont o))),
        c, ?_, ht, ?_⟩
      · rw [interpSumAt, raw_dest_corecAt, interpCo_sumAt, ht]
        refine Sigma.ext rfl ?_
        apply heq_of_eq
        funext a
        cases a <;> rfl
      · intro a
        cases a <;> rfl

/-- Interpreting a computation injected into the left side of the recursive signature recovers
    the original computation. -/
@[simp] theorem interp_sumL {σ ρ α : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) (t : CompE H α) :
    interp body (sumL (F := Call σ ρ) t) = t :=
  interpSumAt_eq body t

private inductive InterpBindSumLRel {H : HSig.{u, v}} {σ ρ α β : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ)
    (k : α → CompE (Sum H (Call σ ρ)) β) :
    (i : Ix H) → Tree H β i → Tree H β i → Prop where
  | root (t : CompE H α) : InterpBindSumLRel body k .normal
      (interp body (bind (sumL (F := Call σ ρ) t) k))
      (bind t (fun x => interp body (k x)))
  | eq {i : Ix H} {x y : Tree H β i} (h : x = y) :
      InterpBindSumLRel body k i x y

private theorem interp_tau_early {σ ρ : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) {α : Type u}
    (t : CompE (Sum H (Call σ ρ)) α) :
    interp body (tau t) = tau (interp body t) := by
  apply eq_of_dest_eq
  change destAt (interp body (tau t)) = destAt (tau (interp body t))
  rw [interp, dest_corecAt]
  have hn : interpCoNormal body (tau t) =
      @Step.tau H α (InterpState H σ ρ α) .normal t := by
    unfold interpCoNormal
    rw [dest_tau]
    rfl
  rw [show interpCo body .normal (tau t) =
    @Step.tau H α (InterpState H σ ρ α) .normal t from hn]
  dsimp [IxPFunctor.map]
  rw [show destAt (tau (interp body t)) = Step.tau (interp body t) from
    dest_tauAt (interp body t)]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar
  rfl

private theorem interp_fail_early {σ ρ : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) {α : Type u} :
    interp body (fail : CompE (Sum H (Call σ ρ)) α) = fail := by
  apply eq_of_dest_eq
  change destAt (interp body (fail : CompE (Sum H (Call σ ρ)) α)) =
    destAt (fail : CompE H α)
  rw [interp, dest_corecAt]
  have hn : interpCoNormal body
      (fail : CompE (Sum H (Call σ ρ)) α) = Step.fail := by
    unfold interpCoNormal
    rw [dest_fail]
    rfl
  rw [show interpCo body .normal
    (fail : CompE (Sum H (Call σ ρ)) α) = Step.fail from hn]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext h
  nomatch h

set_option backward.isDefEq.respectTransparency true in
theorem interp_bind_sumL {σ ρ α β : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) (t : CompE H α)
    (k : α → CompE (Sum H (Call σ ρ)) β) :
    interp body (bind (sumL (F := Call σ ρ) t) k) =
      bind t (fun x => interp body (k x)) := by
  refine IxPFunctor.M.bisim (P := P H β) (InterpBindSumLRel body k) ?_ _ _ (.root t)
  intro i x y hxy
  cases hxy with
  | eq hxy =>
      subst y
      obtain ⟨p, c, hd⟩ : ∃ p c, destAt x = ⟨p, c⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c, c, hd, hd, fun _ => .eq rfl⟩
  | root t =>
      rcases cases_view t with
        ⟨a, rfl⟩ | rfl | ⟨t, rfl⟩ | ⟨e, input, blocks, c, rfl⟩
      · simp only [sumL_ret, bind_ret]
        obtain ⟨p, d, hd⟩ : ∃ p d, destAt (interp body (k a)) = ⟨p, d⟩ :=
          ⟨_, _, rfl⟩
        exact ⟨p, d, d, hd, hd, fun _ => .eq rfl⟩
      · simp only [sumL_fail, bind_fail, interp_fail_early]
        refine ⟨.fail, (fun h => nomatch h), (fun h => nomatch h), ?_, ?_, ?_⟩
        · rw [show IxPFunctor.M.dest (fail : CompE H β) = Step.fail from
            raw_dest_mkAt Step.fail]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext h
          nomatch h
        · rw [show IxPFunctor.M.dest (fail : CompE H β) = Step.fail from
            raw_dest_mkAt Step.fail]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext h
          nomatch h
        · intro h
          nomatch h
      · simp only [sumL_tau, bind_tau, interp_tau_early]
        refine ⟨.tau,
          (fun a => match a with
            | Ar.tau => interp body (bind (sumL (F := Call σ ρ) t) k)),
          (fun a => match a with
            | Ar.tau => bind t (fun x => interp body (k x))),
          ?_, ?_, ?_⟩
        · rw [show IxPFunctor.M.dest
              (tau (interp body (bind (sumL (F := Call σ ρ) t) k))) =
              Step.tau (interp body (bind (sumL (F := Call σ ρ) t) k)) from
            raw_dest_mkAt _]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext a
          cases a
          rfl
        · rw [show IxPFunctor.M.dest
              (tau (bind t (fun x => interp body (k x)))) =
              Step.tau (bind t (fun x => interp body (k x))) from raw_dest_mkAt _]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext a
          cases a
          rfl
        · intro a
          cases a
          exact .root t
      · rw [sumL_opAt (F := Call σ ρ),
          bind_opAt (H := Sum H (Call σ ρ)), bind_opAt (H := H)]
        let leftBlocks : (bx : H.Block e) → BlockE H β e bx := fun bx =>
          corecAt (H := H) (α := β) (interpCo body)
            (relabelBlock (H := Sum H (Call σ ρ)) (α := α) (β := β)
              (corecAt (sumCo (H := H) (F := Call σ ρ))
                (SumState.tree (blocks bx))))
        let rightBlocks := fun (bx : H.Block e) =>
          relabelBlock (α := α) (β := β) (blocks bx)
        let leftK := fun o => interp body
          (bind (sumL (F := Call σ ρ) (c o)) k)
        let rightK := fun o => bind (c o) (fun x => interp body (k x))
        refine ⟨.op e input,
          (fun a => match a with
            | Ar.block bx => leftBlocks bx
            | Ar.cont o => leftK o),
          (fun a => match a with
            | Ar.block bx => rightBlocks bx
            | Ar.cont o => rightK o), ?_, ?_, ?_⟩
        · change destAt (interp body (opAt (Sum.inl e) input
              (fun bx => relabelBlock (H := Sum H (Call σ ρ))
                (corecAt (sumCo (H := H) (F := Call σ ρ))
                  (SumState.tree (blocks bx))))
              (fun o => bind (H := Sum H (Call σ ρ))
                (sumL (F := Call σ ρ) (c o)) k))) = _
          rw [interp, dest_corecAt]
          have hn : interpCo body .normal
              (opAt (Sum.inl e) input
                (fun bx => relabelBlock (H := Sum H (Call σ ρ))
                  (corecAt (sumCo (H := H) (F := Call σ ρ))
                    (SumState.tree (blocks bx))))
                (fun o => bind (H := Sum H (Call σ ρ))
                  (sumL (F := Call σ ρ) (c o)) k)) =
              Step.op e input
                (fun bx => relabelBlock (H := Sum H (Call σ ρ))
                  (corecAt (sumCo (H := H) (F := Call σ ρ))
                    (SumState.tree (blocks bx))))
                (fun o => bind (H := Sum H (Call σ ρ))
                  (sumL (F := Call σ ρ) (c o)) k) := by
            unfold interpCo
            unfold interpCoNormal
            simp only [dest, dest_opAt]
            rfl
          rw [hn]
          simp only [IxPFunctor.map, Step.op]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext a
          cases a <;> rfl
        · change destAt (opAt e input rightBlocks rightK) = _
          rw [dest_opAt]
          simp only [Step.op]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext a
          cases a <;> rfl
        · intro a
          cases a with
          | block bx =>
              apply InterpBindSumLRel.eq
              change corecAt (interpCo body)
                  (relabelBlock (H := Sum H (Call σ ρ)) (α := α) (β := β)
                    (corecAt (sumCo (H := H) (F := Call σ ρ))
                      (SumState.tree (blocks bx)))) =
                relabelBlock (α := α) (β := β) (blocks bx)
              rw [sumAt_relabelBlock]
              change interpSumAt body (relabelBlock (α := α) (β := β) (blocks bx)) = _
              rw [interpSumAt_eq]
          | cont o => exact .root (c o)

@[simp] theorem interp_ret {σ ρ : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) {α : Type u} (a : α) :
    interp body (ret a) = ret a := by
  apply eq_of_dest_eq
  change destAt (interp body (ret a)) = destAt (ret a)
  rw [interp, dest_corecAt]
  have hn : interpCoNormal body (ret a) = Step.ret a := by
    unfold interpCoNormal
    rw [dest_ret]
    rfl
  rw [show interpCo body .normal (ret a) = Step.ret a from hn]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext h
  nomatch h

@[simp] theorem interp_tau {σ ρ : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) {α : Type u}
    (t : CompE (Sum H (Call σ ρ)) α) :
    interp body (tau t) = tau (interp body t) := by
  apply eq_of_dest_eq
  change destAt (interp body (tau t)) = destAt (tau (interp body t))
  rw [interp, dest_corecAt]
  let targetStep : Step H α (InterpState H σ ρ α) .normal :=
    @Step.tau H α (InterpState H σ ρ α) .normal t
  have hn : interpCoNormal body (tau t) = targetStep := by
    unfold interpCoNormal
    rw [dest_tau]
    rfl
  rw [show interpCo body .normal (tau t) = targetStep from hn]
  dsimp [targetStep, IxPFunctor.map]
  rw [show destAt (tau (interp body t)) = Step.tau (interp body t) from
    dest_tauAt (interp body t)]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar
  rfl

@[simp] theorem interp_fail {σ ρ : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) {α : Type u} :
    interp body (fail : CompE (Sum H (Call σ ρ)) α) = fail := by
  apply eq_of_dest_eq
  change destAt (interp body (fail : CompE (Sum H (Call σ ρ)) α)) =
    destAt (fail : CompE H α)
  rw [interp, dest_corecAt]
  have hn : interpCoNormal body (fail : CompE (Sum H (Call σ ρ)) α) = Step.fail := by
    unfold interpCoNormal
    rw [dest_fail]
    rfl
  rw [show interpCo body .normal
    (fail : CompE (Sum H (Call σ ρ)) α) = Step.fail from hn]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext h
  nomatch h

@[simp] theorem bind_call {F : HSig.{u, v}} {σ ρ α : Type u}
    (s : σ)
    (blocks : (b : (Sum F (Call σ ρ)).Block (.inr CallOp.call)) →
      CompE (Sum F (Call σ ρ)) ((Sum F (Call σ ρ)).branchOutput (.inr CallOp.call) b.1))
    (k : ρ → CompE (Sum F (Call σ ρ)) α)
    {β : Type u} (h : α → CompE (Sum F (Call σ ρ)) β) :
    bind (op (Sum.inr CallOp.call) s blocks k) h =
      op (Sum.inr CallOp.call) s blocks
        (fun o => bind (k o) h) := by
  apply eq_of_dest_eq
  change destAt (bind (opAt (Sum.inr CallOp.call) s
    (fun b => asBlock (blocks b)) k) h) = _
  rw [bind_opAt]
  rw [dest_opAt]
  change _ = dest (op (Sum.inr CallOp.call) s
    blocks (fun o => bind (k o) h))
  rw [dest_op]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar with
  | block bx => exact nomatch bx.1
  | cont o => rfl

@[simp] theorem interp_call {σ ρ γ : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) (s : σ)
    (blocks : (b : (Sum H (Call σ ρ)).Block (.inr CallOp.call)) →
      CompE (Sum H (Call σ ρ)) ((Sum H (Call σ ρ)).branchOutput (.inr CallOp.call) b.1))
    (k : ρ → CompE (Sum H (Call σ ρ)) γ) :
    interp body
      (op (Sum.inr CallOp.call) s blocks k) =
      tau (interp body (bind (body s) k)) := by
  apply eq_of_dest_eq
  change destAt (interp body (op (Sum.inr CallOp.call) s
    blocks k)) = destAt (tau (interp body (bind (body s) k)))
  rw [interp, dest_corecAt]
  have hn : interpCoNormal body
      (op (Sum.inr CallOp.call) s blocks k) =
      @Step.tau H γ (InterpState H σ ρ γ) .normal (bind (body s) k) := by
    unfold interpCoNormal
    rw [dest_op]
    rfl
  rw [show interpCo body .normal
    (op (Sum.inr CallOp.call) s blocks k) =
      @Step.tau H γ (InterpState H σ ρ γ) .normal (bind (body s) k) from hn]
  dsimp [IxPFunctor.map]
  rw [show destAt (tau (interp body (bind (body s) k))) =
    Step.tau (interp body (bind (body s) k)) from
      dest_tauAt (interp body (bind (body s) k))]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar
  rfl

def mrec {σ ρ : Type u}
    (body : σ → CompE (Sum H (Call σ ρ)) ρ) : σ → CompE H ρ :=
  fun s => interp body (body s)

/-- The recursive arrow supplied to a fix body.  Kept as a named operation so clients can state
    local body equalities without unfolding the implementation of `mfix`. -/
def recursiveCall {σ ρ : Type u} : σ → CompE (Sum H (Call σ ρ)) ρ :=
  fun s => op (Sum.inr CallOp.call) s (fun bx => nomatch bx.1) ret

/-- Tie a recursive Kleisli arrow in the existing call-extended computation monad.

The body and its recursive argument have exactly the same type.  Recursive applications are
ordinary function applications; the private arrow supplied here emits a `Call`, and `mrec`
closes those calls while inserting the guarding `tau`. -/
def mfix {σ ρ : Type u}
    (body : (σ → CompE (Sum H (Call σ ρ)) ρ) →
    σ → CompE (Sum H (Call σ ρ)) ρ) :
    σ → CompE H ρ :=
  mrec (body recursiveCall)

/-! ### Heterogeneous effect interpretation -/

/-- Interpret the right side of a sum with a handler that runs in the same open sum.  The handler
receives every scoped block, so this operation is valid for arbitrary higher-order signatures, not
only zero-branch effects.  Each handled operation contributes one guarding `tau`. -/
abbrev Handler (H F : HSig.{u, v}) :=
  {α : Type u} → (e : F.op) → F.input e →
    ((b : F.branch e) → (bi : F.branchInput e b) →
      BlockE (Sum H F) α (.inr e) ⟨b, bi⟩) →
    CompE (Sum H F) (F.output e)

@[reducible] def handlerSourceIx {H F : HSig.{u, v}} : Ix H → Ix (Sum H F)
  | .normal => .normal
  | .block e bx => .block (.inl e) bx

@[reducible] def handlerResultIn {H F : HSig.{u, v}} {α : Type u} :
    (i : Ix H) → result H α i → result (Sum H F) α (handlerSourceIx i)
  | .normal, value => value
  | .block _ _, value => value

abbrev HandlerState (H F : HSig.{u, v}) (α : Type u) (i : Ix H) :=
  Tree (Sum H F) α (handlerSourceIx i)

def interpHandlerCoNormal {H F : HSig.{u, v}} (handler : Handler H F)
    (t : CompE (Sum H F) α) :
    Step H α (HandlerState H F α) .normal :=
  match dest t with
  | ⟨.ret a, _⟩ => Step.ret a
  | ⟨.tau, c⟩ => Step.tau (c Ar.tau)
  | ⟨.fail, _⟩ => Step.fail
  | ⟨.op (.inl e) input, c⟩ => Step.op e input
      (fun bx => c (Ar.block bx))
      (fun o => c (Ar.cont o))
  | ⟨.op (.inr e) input, c⟩ => Step.tau
      (bindAt
        (handler e input fun b bi => c (Ar.block ⟨b, bi⟩))
        fun o => c (Ar.cont o))

def interpHandlerCo {H F : HSig.{u, v}} (handler : Handler H F) :
    (i : Ix H) → HandlerState H F α i →
      Step H α (HandlerState H F α) i
  | .normal, t => interpHandlerCoNormal handler t
  | i@(.block _ _), t =>
      match destAt t with
      | ⟨.ret a, _⟩ => Step.ret (cast (by cases i <;> rfl) a)
      | ⟨.tau, c⟩ => Step.tau (c Ar.tau)
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.op (.inl e) input, c⟩ => Step.op e input
          (fun bx => c (Ar.block bx))
          (fun o => c (Ar.cont o))
      | ⟨.op (.inr e) input, c⟩ => Step.tau
          (bindAt
            (handler e input fun b bi => c (Ar.block ⟨b, bi⟩))
            fun o => c (Ar.cont o))

def interpHandlerAt {H F : HSig.{u, v}} (handler : Handler H F) {i : Ix H}
    (t : HandlerState H F α i) : Tree H α i :=
  corecAt (interpHandlerCo handler) t

def interpHandler {H F : HSig.{u, v}} (handler : Handler H F)
    (t : CompE (Sum H F) α) : CompE H α :=
  corecAt (interpHandlerCo handler) t

@[simp] theorem interpHandler_ret {H F : HSig.{u, v}} (handler : Handler H F)
    (value : α) : interpHandler handler (ret value) = ret value := by
  apply eq_of_dest_eq
  change destAt (interpHandler handler (ret value)) = destAt (ret value)
  rw [interpHandler, dest_corecAt]
  have step : interpHandlerCoNormal handler (ret value) = Step.ret value := by
    unfold interpHandlerCoNormal
    rw [dest_ret]
    rfl
  rw [show interpHandlerCo handler .normal (ret value) = Step.ret value from step]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext impossible
  nomatch impossible

@[simp] theorem interpHandler_tau {H F : HSig.{u, v}} (handler : Handler H F)
    (tree : CompE (Sum H F) α) :
    interpHandler handler (tau tree) = tau (interpHandler handler tree) := by
  apply eq_of_dest_eq
  change destAt (interpHandler handler (tau tree)) =
    destAt (tau (interpHandler handler tree))
  rw [interpHandler, dest_corecAt]
  let targetStep : Step H α (HandlerState H F α) .normal :=
    @Step.tau H α (HandlerState H F α) .normal tree
  have step : interpHandlerCoNormal handler (tau tree) = targetStep := by
    unfold interpHandlerCoNormal
    rw [dest_tau]
    rfl
  rw [show interpHandlerCo handler .normal (tau tree) = targetStep from step]
  dsimp [targetStep, IxPFunctor.map]
  rw [show destAt (tau (interpHandler handler tree)) =
    Step.tau (interpHandler handler tree) from dest_tauAt _]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar
  rfl

@[simp] theorem interpHandler_fail {H F : HSig.{u, v}} (handler : Handler H F) :
    interpHandler handler (fail : CompE (Sum H F) α) = fail := by
  apply eq_of_dest_eq
  change destAt (interpHandler handler (fail : CompE (Sum H F) α)) = destAt fail
  rw [interpHandler, dest_corecAt]
  have step : interpHandlerCoNormal handler
      (fail : CompE (Sum H F) α) = Step.fail := by
    unfold interpHandlerCoNormal
    rw [dest_fail]
    rfl
  rw [show interpHandlerCo handler .normal (fail : CompE (Sum H F) α) =
    Step.fail from step]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext impossible
  nomatch impossible

theorem interpHandler_op_right {H F : HSig.{u, v}} (handler : Handler H F)
    (e : F.op) (input : F.input e)
    (blocks : (b : F.Block e) → CompE (Sum H F) (F.branchOutput e b.1))
    (k : F.output e → CompE (Sum H F) α) :
    interpHandler handler (op (.inr e) input blocks k) =
      tau (interpHandler handler
        (bind
          (@handler α e input fun b bi =>
            asBlock (α := α) (blocks ⟨b, bi⟩))
          k)) := by
  apply eq_of_dest_eq
  change destAt (interpHandler handler (op (.inr e) input blocks k)) =
    destAt (tau (interpHandler handler
      (bind
        (@handler α e input fun b bi =>
          asBlock (α := α) (blocks ⟨b, bi⟩))
        k)))
  rw [interpHandler, dest_corecAt]
  let targetStep : Step H α (HandlerState H F α) .normal :=
    Step.tau
        (bindAt
          (@handler α e input fun b bi => asBlock (α := α) (blocks ⟨b, bi⟩))
          k)
  have step : interpHandlerCoNormal handler (op (.inr e) input blocks k) =
      targetStep := by
    unfold interpHandlerCoNormal
    rw [dest_op]
    rfl
  rw [show interpHandlerCo handler .normal (op (.inr e) input blocks k) =
    targetStep from step]
  dsimp [targetStep, IxPFunctor.map]
  rw [show destAt (tau (interpHandler handler
      (bind
        (@handler α e input fun b bi => asBlock (α := α) (blocks ⟨b, bi⟩))
        k))) =
    Step.tau (interpHandler handler
      (bind
        (@handler α e input fun b bi => asBlock (α := α) (blocks ⟨b, bi⟩))
        k)) from dest_tauAt _]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext ar
  cases ar
  rfl

/-! The indexed equations are the coalgebraic interface used by scoped simulations. They expose
the actual internal block children produced by the handler, rather than re-embedding public
computations and asking for an unnecessarily strong commuting equality. -/


end CompE

end ITree
end Freigen
