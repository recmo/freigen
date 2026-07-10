import Freigen.ITree2.PFunctor

namespace Freigen
namespace ITree2

universe u v

/-- One layer of the scoped interaction-tree polynomial at internal result label `i`. -/
abbrev Step (H : HSig.{u}) (α : Type u)
    (X : Ix H → Type v) (i : Ix H) :=
  (P H α).Obj X i

/-- The internal tree family.  The public computation type is the `.normal` fiber. -/
abbrev Tree (H : HSig.{u}) (α : Type u) (i : Ix H) :=
  (P H α).M i

/-- Public scoped interaction trees. -/
abbrev CompE (H : HSig.{u}) (α : Type u) :=
  Tree H α .normal

/-- Internal block fiber for a higher-order operation branch. -/
abbrev BlockE (H : HSig.{u}) (α : Type u)
    (e : H.op) (b : H.Block e) :=
  Tree H α (.block e b)

namespace Step

variable {H : HSig.{u}} {α : Type u}
  {X : Ix H → Type v}

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

variable {H : HSig.{u}}

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
def corecAt {α : Type u} {X : Ix H → Type v}
    (f : (i : Ix H) → X i → Step H α X i) {i : Ix H} (x : X i) :
    Tree H α i :=
  IxPFunctor.M.corec (P := P H α) f x

@[simp] theorem dest_corecAt {α : Type u} {X : Ix H → Type v}
    (f : (i : Ix H) → X i → Step H α X i) {i : Ix H} (x : X i) :
    destAt (corecAt f x) = (P H α).map (fun i => corecAt f (i := i)) (f i x) :=
  IxPFunctor.M.dest_corec f x

@[simp] theorem raw_dest_corecAt {α : Type u} {X : Ix H → Type v}
    (f : (i : Ix H) → X i → Step H α X i) {i : Ix H} (x : X i) :
    IxPFunctor.M.dest (corecAt f x) =
      (P H α).map (fun i => corecAt f (i := i)) (f i x) :=
  IxPFunctor.M.dest_corec f x

private inductive RelabelBlockState (H : HSig.{u}) (α β : Type u) :
    Ix H → Type u where
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

private inductive AsBlockState (H : HSig.{u}) (α : Type u)
    (root : H.op) (br : H.Block root) :
    Ix H → Type u where
  | normal :
      CompE H (H.branchOutput root br.1) → AsBlockState H α root br (.block root br)
  | block {e : H.op} {b : H.Block e} :
      BlockE H (H.branchOutput root br.1) e b → AsBlockState H α root br (.block e b)

/-- Coalgebra embedding a public computation as a scoped block. -/
private def asBlockCo {α : Type u} (root : H.op) (br : H.Block root) :
    (i : Ix H) → AsBlockState H α root br i →
      Step H α (AsBlockState H α root br) i
  | .block _ _, .normal t =>
      match dest t with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ => Step.tau (.normal (c Ar.tau : CompE H (H.branchOutput root br.1)))
      | ⟨.fail, _⟩ => Step.fail

      | ⟨.op e input, c⟩ =>
          Step.op e input
            (fun b => .block (c (Ar.block b) : BlockE H (H.branchOutput root br.1) e b))
            (fun o => .normal (c (Ar.cont o) : CompE H (H.branchOutput root br.1)))
  | .block e₀ b₀, .block t =>
      match destAt t with
      | ⟨.ret a, _⟩ => Step.ret a
      | ⟨.tau, c⟩ =>
          Step.tau (.block (c Ar.tau : BlockE H (H.branchOutput root br.1) e₀ b₀))
      | ⟨.fail, _⟩ => Step.fail

      | ⟨.op e input, c⟩ =>
          Step.op e input
            (fun b => .block (c (Ar.block b) : BlockE H (H.branchOutput root br.1) e b))
            (fun o => .block (c (Ar.cont o) : BlockE H (H.branchOutput root br.1) e₀ b₀))

/-- Embed a public computation returning a branch result as the corresponding internal block. -/
def asBlock {α : Type u} {e : H.op} {b : H.Block e}
    (t : CompE H (H.branchOutput e b.1)) : BlockE H α e b :=
  corecAt (H := H) (α := α) (asBlockCo (α := α) e b)
    (AsBlockState.normal t)

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

private inductive BindState (H : HSig.{u}) (α β : Type u)
    (target : Ix H) :
    Ix H → Type u where
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

private theorem dest_relabelBlock {α β : Type u} {e₀ : H.op} {b₀ : H.Block e₀}
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

@[reducible] def sum (H F : HSig.{u}) : HSig.{u} where
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

inductive CallOp : Type u where
  | call

abbrev Call (sigma rho : Type u) : HSig.{u} where
  op := CallOp
  input := fun _ => sigma
  output := fun _ => rho
  branch := fun _ => PEmpty
  branchInput := fun _ b => nomatch b
  branchOutput := fun _ b => nomatch b

namespace CompE

variable {H F : HSig.{u}}

@[reducible] def sumIx : Ix H → Ix (Sum H F)
  | .normal => .normal
  | .block e bx => .block (.inl e) bx

private inductive SumState (H F : HSig.{u}) (alpha : Type u) : Ix (Sum H F) → Type u where
  | tree {i : Ix H} : Tree H alpha i → SumState H F alpha (sumIx i)

def sumCo : (i : Ix (Sum H F)) → SumState H F alpha i →
    Step (Sum H F) alpha (SumState H F alpha) i
  | _, @SumState.tree _ _ _ j t =>
      match destAt t with
      | ⟨.ret a, _⟩ => Step.ret (cast (by cases j <;> rfl) a)
      | ⟨.tau, c⟩ => Step.tau (.tree (c Ar.tau))
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.op e input, c⟩ => Step.op (.inl e) input
          (fun bx => .tree (c (Ar.block bx)))
          (fun o => .tree (c (Ar.cont o)))

def sumL {alpha : Type u} (t : CompE H alpha) : CompE (Sum H F) alpha :=
  corecAt sumCo (.tree t)

@[reducible] def sourceIx : Ix H → Ix (Sum H (Call sigma rho))
  | .normal => .normal
  | .block e bx => .block (.inl e) bx

abbrev InterpState (H : HSig.{u}) (sigma rho alpha : Type u) (i : Ix H) :=
  Tree (Sum H (Call sigma rho)) alpha (sourceIx i)

def interpCo {sigma rho : Type u}
    (body : sigma → CompE (Sum H (Call sigma rho)) rho) :
    (i : Ix H) → InterpState H sigma rho alpha i →
      Step H alpha (InterpState H sigma rho alpha) i
  | i, t =>
      match destAt t with
      | ⟨.ret a, _⟩ => Step.ret (cast (by cases i <;> rfl) a)
      | ⟨.tau, c⟩ => Step.tau (c Ar.tau)
      | ⟨.fail, _⟩ => Step.fail
      | ⟨.op (.inl e) input, c⟩ => Step.op e input
          (fun bx => c (Ar.block bx))
          (fun o => c (Ar.cont o))
      | ⟨.op (.inr .call) s, c⟩ => Step.tau
          (bindAt (body s) fun o => c (Ar.cont o))

def interp {sigma rho alpha : Type u}
    (body : sigma → CompE (Sum H (Call sigma rho)) rho)
    (t : CompE (Sum H (Call sigma rho)) alpha) : CompE H alpha :=
  corecAt (interpCo body) t

def mrec {sigma rho : Type u}
    (body : sigma → CompE (Sum H (Call sigma rho)) rho) : sigma → CompE H rho :=
  fun s => interp body (body s)

end CompE

end ITree2
end Freigen
