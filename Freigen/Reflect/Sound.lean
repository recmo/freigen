import Freigen.Ast.Basic
import Freigen.ITree.Eutt

namespace Freigen
namespace Ast

universe u v

abbrev EvalM (H : Signature) (α : Type) := ITree.CompE H.spec α

structure ReflectionWitnessAt {S : ITree.HSig.{u, v}} {H : Signature}
    {r : Option (Tp × Tp)} (C : Signature.CompatAt S H r)
    (Φ : Prop) (α : Tp) {A : Type u}
    (result : A → α.denote (ITree.CompE H.spec) → Prop) (m : Free S A)
    (e : Expr H (Tp.denote (ITree.CompE H.spec)) r α) : Type (max u v + 2) where
  sound : Φ → ITree.CompE.Eutt C result (Free.toITree m) (Expr.denote e)

abbrev ReflectionWitness {S : ITree.HSig.{u, v}} {H : Signature}
    (C : Signature.Compat S H) (Φ : Prop) (α : Tp) {A : Type u}
    (result : A → α.denote (ITree.CompE H.spec) → Prop) (m : Free S A)
    (e : Expr H (Tp.denote (ITree.CompE H.spec)) none α) :=
  ReflectionWitnessAt C Φ α result m e

/-- Closed output of `reflect%`: parametric PHOAS code and its relational tree semantics. -/
def Reflected {S : ITree.HSig.{u, v}} {H : Signature}
    (C : Signature.Compat S H) (α : Tp) {A : Type u}
    (result : A → α.denote (ITree.CompE H.spec) → Prop) (m : Free S A) :
    Type 2 :=
  { code : Closed H α // ITree.CompE.Eutt C result (Free.toITree m)
    (Expr.denote (code (Tp.denote (ITree.CompE H.spec)))) }

def ReflectionRAt {S : ITree.HSig.{u, v}} {H : Signature}
    {r : Option (Tp × Tp)} (C : Signature.CompatAt S H r) (Φ : Prop) (α : Tp) {A : Type u}
    (result : A → α.denote (ITree.CompE H.spec) → Prop) (m : Free S A) : Type (max u v + 2) :=
  Σ e : Expr H (Tp.denote (ITree.CompE H.spec)) r α,
    ReflectionWitnessAt C Φ α result m e

/-- Continuation-strengthened soundness for an expression inside a recursive body.  Recursive
    calls consume the source function's induction hypothesis at the already-composed
    continuation, so no global `interp_bind` theorem is required. -/
structure RecReflectionWitness {S : ITree.HSig.{u, v}} {H : Signature}
    {a b : Tp} (C : Signature.Compat S H)
    (body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b)
    (Φ : Prop) (α : Tp) {A : Type u}
    (result : A → α.denote (ITree.CompE H.spec) → Prop)
    (m : Free S A)
    (e : Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) α) :
    Type (max u v + 2) where
  sound : Φ → ∀ {Z : Type u} {B : Type} (q : Z → B → Prop)
    (ks : A → Free S Z)
    (kt : α.denote (ITree.CompE H.spec) →
      ITree.CompE (DomSig H (some (a, b))) B),
    (∀ source target, result source target →
      ITree.CompE.Eutt C q (Free.toITree (ks source))
        (ITree.CompE.interp (fun x => Expr.denote (body x)) (kt target))) →
    ITree.CompE.Eutt C q (Free.toITree (m.bind ks))
      (ITree.CompE.interp (fun x => Expr.denote (body x))
        (ITree.CompE.bind (Expr.denote e) kt))

def RecReflectionR {S : ITree.HSig.{u, v}} {H : Signature}
    {a b : Tp} (C : Signature.Compat S H)
    (body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b)
    (Φ : Prop) (α : Tp) {A : Type u}
    (result : A → α.denote (ITree.CompE H.spec) → Prop) (m : Free S A) :=
  Σ e, RecReflectionWitness C body Φ α result m e

def RecCallAdequate {S : ITree.HSig.{u, v}} {H : Signature}
    {a b : Tp} (C : Signature.Compat S H)
    (body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b)
    (Φ : Prop) {A : Type u}
    (result : A → b.denote (ITree.CompE H.spec) → Prop)
    (m : Free S A) (targetArg : a.denote (ITree.CompE H.spec)) : Prop :=
  Φ → ∀ {Z : Type u} {B : Type} (q : Z → B → Prop)
    (ks : A → Free S Z)
    (kt : b.denote (ITree.CompE H.spec) →
      ITree.CompE (DomSig H (some (a, b))) B),
    (∀ source target, result source target →
      ITree.CompE.Eutt C q (Free.toITree (ks source))
        (ITree.CompE.interp (fun x => Expr.denote (body x)) (kt target))) →
    ITree.CompE.Eutt C q (Free.toITree (m.bind ks))
      (ITree.CompE.interp (fun x => Expr.denote (body x))
        (ITree.CompE.bind (Expr.denote (body targetArg)) kt))

abbrev ReflectionR {S : ITree.HSig.{u, v}} {H : Signature} (C : Signature.Compat S H)
    (Φ : Prop) (α : Tp) {A : Type u}
    (result : A → α.denote (ITree.CompE H.spec) → Prop) (m : Free S A) :=
  ReflectionRAt (r := none) C Φ α result m

abbrev Reflection {S : ITree.HSig.{0, v}} {H : Signature} (C : Signature.Compat S H)
    (Φ : Prop) (α : Tp)
    (m : Free S (α.denote (ITree.CompE H.spec))) :=
  ReflectionR C Φ α Eq m

/-- Soundness contract stored for a spilled helper specialization. -/
def Adequate {S : ITree.HSig.{u, v}} {H : Signature} (C : Signature.Compat S H)
    {A B : Type u} {a b : Tp}
    (argRel : A → a.denote (ITree.CompE H.spec) → Prop)
    (resultRel : B → b.denote (ITree.CompE H.spec) → Prop)
    (source : A → Free S B)
    (target : a.denote (ITree.CompE H.spec) →
      ITree.CompE H.spec (b.denote (ITree.CompE H.spec))) : Prop :=
  ∀ sourceArg targetArg, argRel sourceArg targetArg →
    ITree.CompE.Eutt C resultRel (Free.toITree (source sourceArg)) (target targetArg)

theorem related_of_eq {A B : Type} {rel : A → B → Prop} {source : A} {x y : B}
    (h : y = x) (hx : rel source x) : rel source y := by
  cases h
  exact hx

theorem natCases_eq {S : ITree.HSig.{u, v}} {A : Type u}
    (f : Nat → Free S A) (base : Free S A) (step : Nat → Free S A)
    (hbase : f 0 = base) (hstep : ∀ n, f (n + 1) = step n) (n : Nat) :
    (if n == 0 then base else step (n - 1)) = f n := by
  cases n with
  | zero => simpa using hbase.symm
  | succ n => simpa [Nat.succ_eq_add_one] using (hstep n).symm

theorem natPred_lt_of_rel {current target smaller : Nat}
    (hcurrent : current = target) (hsmaller : smaller = target - 1)
    (hnonzero : (target == 0) = false) : smaller < current := by
  have ht : target ≠ 0 := beq_eq_false_iff_ne.mp hnonzero
  omega

def Reflection.eutt {S : ITree.HSig.{0, v}} {H : Signature} {C : Signature.Compat S H}
    {Φ : Prop} {α : Tp} {m : Free S (α.denote (ITree.CompE H.spec))}
    (r : Reflection C Φ α m) : Φ →
      ITree.CompE.Eutt C Eq (Free.toITree m) (Expr.denote r.1) :=
  r.2.sound

/-- Attach source provenance without changing denotation or the synchronized soundness proof. -/
def Reflection.source {S : ITree.HSig.{u, v}} {H : Signature}
    {r : Option (Tp × Tp)} {C : Signature.CompatAt S H r}
    {Φ : Prop} {α : Tp} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (range : SourceRange) (reflection : ReflectionRAt C Φ α result m) :
    ReflectionRAt C Φ α result m :=
  ⟨.source range reflection.1, ⟨reflection.2.sound⟩⟩

/-- Recursive-body counterpart of `Reflection.source`. -/
def RecReflection.source {S : ITree.HSig.{u, v}} {H : Signature}
    {a b α : Tp} {C : Signature.Compat S H}
    {body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b}
    {Φ : Prop} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (range : SourceRange) (reflection : RecReflectionR C body Φ α result m) :
    RecReflectionR C body Φ α result m :=
  ⟨.source range reflection.1, ⟨reflection.2.sound⟩⟩

def Reflection.ret {S : ITree.HSig.{u, v}} {H : Signature} {r : Option (Tp × Tp)}
    {C : Signature.CompatAt S H r}
    {Φ : Prop} {α : Tp} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop}
    (v : α.denote (ITree.CompE H.spec)) {v' : A} (h : Φ → result v' v) :
    ReflectionRAt C Φ α result (.pure v') :=
  ⟨.ret v, ⟨fun hPhi => by
    cases r with
    | none => exact ITree.CompE.Eutt.of_step C (.ret result v' v (h hPhi))
    | some ab =>
        cases ab
        exact ITree.CompE.Eutt.of_step C (.ret result v' v (h hPhi))⟩⟩

def RecReflection.ret {S : ITree.HSig.{u, v}} {H : Signature}
    {a b α : Tp} {C : Signature.Compat S H}
    {body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b}
    {Φ : Prop} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop}
    (v : α.denote (ITree.CompE H.spec)) {v' : A}
    (h : Φ → result v' v) :
    RecReflectionR C body Φ α result (.pure v') :=
  ⟨.ret v, ⟨fun hΦ => by
    intro Z B q ks kt hk
    rw [Free.toITree_bind]
    change ITree.CompE.Eutt C q
      (ITree.CompE.bind (ITree.CompE.ret v') (fun x => Free.toITree (ks x)))
      (ITree.CompE.interp (fun x => Expr.denote (body x))
        (ITree.CompE.bind (ITree.CompE.ret v) kt))
    rw [ITree.CompE.bind_ret, ITree.CompE.bind_ret]
    exact hk v' v (h hΦ)⟩⟩

def RecReflection.congrSource {S : ITree.HSig.{u, v}} {H : Signature}
    {a b α : Tp} {C : Signature.Compat S H}
    {body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b}
    {Φ : Prop} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop}
    {source source' : Free S A} (h : source = source')
    (r : RecReflectionR C body Φ α result source) :
    RecReflectionR C body Φ α result source' :=
  ⟨r.1, ⟨fun hΦ => by
    rw [← h]
    exact r.2.sound hΦ⟩⟩

def RecReflection.selfCall {S : ITree.HSig.{u, v}} {H : Signature}
    {a b α : Tp} {C : Signature.Compat S H}
    {body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b}
    {Φ : Prop} {A Z : Type u}
    {callRel : A → b.denote (ITree.CompE H.spec) → Prop}
    {result : Z → α.denote (ITree.CompE H.spec) → Prop}
    (sourceCall : Free S A) (targetArg : a.denote (ITree.CompE H.spec))
    (ih : Φ → RecCallAdequate C body True callRel sourceCall targetArg)
    {sourceK : A → Free S Z}
    (k : ∀ target, Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) α)
    (kSound : ∀ target source, callRel source target →
      RecReflectionWitness C body Φ α result (sourceK source) (k target)) :
    RecReflectionR C body Φ α result (sourceCall.bind sourceK) :=
  ⟨.selfCall targetArg k, ⟨fun hΦ => by
    intro Y B q ks kt hk
    have sourceAssoc : (sourceCall.bind sourceK).bind ks =
        sourceCall.bind (fun source => (sourceK source).bind ks) :=
      LawfulMonad.bind_assoc sourceCall sourceK ks
    rw [sourceAssoc, Free.toITree_bind]
    let targetK := fun target =>
      ITree.CompE.bind (Expr.denote (k target)) kt
    have hcont : ∀ source target, callRel source target →
        ITree.CompE.Eutt C q
          (Free.toITree ((sourceK source).bind ks))
          (ITree.CompE.interp (fun x => Expr.denote (body x)) (targetK target)) := by
      intro source target hrel
      exact (kSound target source hrel).sound hΦ q ks kt hk
    have hcall := ih hΦ True.intro q
      (fun source => (sourceK source).bind ks) targetK hcont
    rw [Free.toITree_bind] at hcall
    change ITree.CompE.Eutt C q
      (ITree.CompE.bind (Free.toITree sourceCall)
        (fun source => Free.toITree ((sourceK source).bind ks)))
      (ITree.CompE.interp (fun x => Expr.denote (body x))
        (ITree.CompE.bind (Expr.denote (.selfCall targetArg k)) kt))
    simp only [Expr.denote, ITree.CompE.bind_assoc]
    rw [ITree.CompE.bind_call (F := H.spec)]
    simp only [ITree.CompE.bind_ret]
    rw [ITree.CompE.interp_call]
    exact ITree.CompE.Eutt.tauR C hcall⟩⟩

def RecReflection.natLit {S : ITree.HSig.{u, v}} {H : Signature}
    {a b α : Tp} {C : Signature.Compat S H}
    {body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b}
    {Φ : Prop} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (n : Nat) (k : ∀ n', RecReflectionR C body (Φ ∧ n' = n) α result m) :
    RecReflectionR C body Φ α result m :=
  let r := k n
  ⟨.natLit n fun n' => (k n').1, ⟨fun hΦ => by
    change ∀ {Z : Type u} {B : Type} (q : Z → B → Prop)
      (ks : A → Free S Z)
      (kt : α.denote (ITree.CompE H.spec) →
        ITree.CompE (DomSig H (some (a, b))) B), _ → _
    exact r.2.sound ⟨hΦ, rfl⟩⟩⟩

def RecReflection.boolLit {S : ITree.HSig.{u, v}} {H : Signature}
    {a b α : Tp} {C : Signature.Compat S H}
    {body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b}
    {Φ : Prop} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (value : Bool)
    (k : ∀ value', RecReflectionR C body (Φ ∧ value' = value) α result m) :
    RecReflectionR C body Φ α result m :=
  let r := k value
  ⟨.boolLit value fun value' => (k value').1, ⟨fun hΦ => by
    change ∀ {Z : Type u} {B : Type} (q : Z → B → Prop)
      (ks : A → Free S Z)
      (kt : α.denote (ITree.CompE H.spec) →
        ITree.CompE (DomSig H (some (a, b))) B), _ → _
    exact r.2.sound ⟨hΦ, rfl⟩⟩⟩

def RecReflection.unitLit {S : ITree.HSig.{u, v}} {H : Signature}
    {a b α : Tp} {C : Signature.Compat S H}
    {body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b}
    {Φ : Prop} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (k : RecReflectionR C body Φ α result m) :
    RecReflectionR C body Φ α result m :=
  ⟨.unitLit fun _ => k.1, ⟨k.2.sound⟩⟩

def RecReflection.bin {S : ITree.HSig.{u, v}} {H : Signature}
    {ra rb α : Tp} {C : Signature.Compat S H}
    {body : ra.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (ra, rb)) rb}
    {Φ : Prop} {x y z : Tp0} {A : Type u}
    (op : Bin x y z) (vx : x.denote) (vy : y.denote)
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (k : ∀ vz, RecReflectionR C body (Φ ∧ vz = op.denote vx vy) α result m) :
    RecReflectionR C body Φ α result m :=
  let r := k (op.denote vx vy)
  ⟨.bin op vx vy fun vz => (k vz).1, ⟨fun hΦ => by
    change ∀ {Z : Type u} {B : Type} (q : Z → B → Prop)
      (ks : A → Free S Z)
      (kt : α.denote (ITree.CompE H.spec) →
        ITree.CompE (DomSig H (some (ra, rb))) B), _ → _
    exact r.2.sound ⟨hΦ, rfl⟩⟩⟩

def RecReflection.ite {S : ITree.HSig.{u, v}} {H : Signature}
    {ra rb α β : Tp} {C : Signature.Compat S H}
    {body : ra.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (ra, rb)) rb}
    {Φ : Prop} {A Z : Type u}
    (condition : Bool)
    {branchRel : A → β.denote (ITree.CompE H.spec) → Prop}
    {result : Z → α.denote (ITree.CompE H.spec) → Prop}
    {sourceThen sourceElse : Free S A}
    (thenBranch : RecReflectionR C body (Φ ∧ condition = true)
      β branchRel sourceThen)
    (elseBranch : RecReflectionR C body (Φ ∧ condition = false)
      β branchRel sourceElse)
    {sourceK : A → Free S Z}
    (k : ∀ target, Expr H (Tp.denote (ITree.CompE H.spec))
      (some (ra, rb)) α)
    (kSound : ∀ target source, branchRel source target →
      RecReflectionWitness C body Φ α result (sourceK source) (k target)) :
    RecReflectionR C body Φ α result
      ((if condition then sourceThen else sourceElse).bind sourceK) :=
  ⟨.ite condition thenBranch.1 elseBranch.1 k, ⟨fun hΦ => by
    intro Y B q ks kt hk
    let sourceCont := fun source => (sourceK source).bind ks
    let targetCont := fun target =>
      ITree.CompE.bind (Expr.denote (k target)) kt
    have hcont : ∀ source target, branchRel source target →
        ITree.CompE.Eutt C q (Free.toITree (sourceCont source))
          (ITree.CompE.interp (fun x => Expr.denote (body x))
            (targetCont target)) := by
      intro source target hrel
      exact (kSound target source hrel).sound hΦ q ks kt hk
    cases condition <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
        Expr.denote, cond, Free.bind_assoc]
    · have hb := elseBranch.2.sound ⟨hΦ, rfl⟩ q sourceCont targetCont hcont
      apply ITree.CompE.Eutt.congr C rfl _ hb
      exact congrArg (ITree.CompE.interp (fun x => Expr.denote (body x)))
        (ITree.CompE.bind_assoc (Expr.denote elseBranch.1)
          (fun v => Expr.denote (k v)) kt).symm
    · have hb := thenBranch.2.sound ⟨hΦ, rfl⟩ q sourceCont targetCont hcont
      apply ITree.CompE.Eutt.congr C rfl _ hb
      exact congrArg (ITree.CompE.interp (fun x => Expr.denote (body x)))
        (ITree.CompE.bind_assoc (Expr.denote thenBranch.1)
          (fun v => Expr.denote (k v)) kt).symm⟩⟩

def RecReflection.opNoBranches {S : ITree.HSig.{u, v}} {H : Signature}
    {ra rb α : Tp} {C : Signature.Compat S H}
    {body : ra.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (ra, rb)) rb}
    {Φ : Prop} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop}
    (e : S.op) (h : H.op) (w : C.opRel e h)
    (sourceEmpty : ∀ b : S.branch e, False)
    (targetEmpty : ∀ b : H.branch h, False)
    (input : (H.input h).denote) {sourceInput : S.input e}
    (hi : Φ → C.input w sourceInput input)
    {sourceBlocks : (br : S.branch e) → S.branchInput e br →
      Free S (S.branchOutput e br)}
    {sourceK : S.output e → Free S A}
    (k : ∀ target, Expr H (Tp.denote (ITree.CompE H.spec))
      (some (ra, rb)) α)
    (kSound : ∀ target source, C.output w source target →
      RecReflectionWitness C body Φ α result (sourceK source) (k target)) :
    RecReflectionR C body Φ α result (.op e sourceInput sourceBlocks sourceK) :=
  ⟨.op h input (fun bt => nomatch targetEmpty bt)
      k,
    ⟨fun hΦ => by
      intro Z B q ks kt hk
      rw [Free.toITree_bind]
      rw [Free.toITree_op]
      rw [ITree.CompE.bind_assoc]
      simp only [Expr.denote, DomR.perform, DomR.bind]
      rw [ITree.CompE.bind_assoc]
      rw [ITree.CompE.bind_op_no_branches
        (H := DomSig H (some (ra, rb))) (Sum.inl h)
        targetEmpty]
      simp only [ITree.CompE.bind_ret]
      rw [ITree.CompE.interp_op_no_branches
        (empty := targetEmpty)]
      rw [ITree.CompE.op_eq_bind_no_branches (H := H.spec) h targetEmpty]
      apply ITree.CompE.Eutt.of_step C
      exact .op q w sourceInput input (hi hΦ)
        (fun bs xs => Free.toITree (sourceBlocks bs xs))
        (fun os => ITree.CompE.bind (Free.toITree (sourceK os))
          (fun source => Free.toITree (ks source)))
        (fun bt xt => nomatch targetEmpty bt)
        (fun ot => ITree.CompE.interp (fun x => Expr.denote (body x))
          (ITree.CompE.bind (Expr.denote (k ot)) kt))
        (fun bs => nomatch sourceEmpty bs)
        (fun os ot ho => by
          rw [← Free.toITree_bind]
          exact (kSound ot os ho).sound hΦ q ks kt hk)⟩⟩

theorem RecReflection.wellFounded {S : ITree.HSig.{u, v}} {H : Signature}
    {a b : Tp} {C : Signature.Compat S H} {A B : Type u}
    (argRel : A → a.denote (ITree.CompE H.spec) → Prop)
    (resultRel : B → b.denote (ITree.CompE H.spec) → Prop)
    (source : A → Free S B)
    (body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b)
    (order : A → A → Prop) (wf : WellFounded order)
    (bodySound : ∀ sourceArg targetArg, argRel sourceArg targetArg →
      (∀ smaller targetSmaller, argRel smaller targetSmaller →
        order smaller sourceArg →
        RecCallAdequate C body True resultRel (source smaller) targetSmaller) →
      RecReflectionWitness C body True b resultRel
        (source sourceArg) (body targetArg)) :
    ∀ sourceArg targetArg, argRel sourceArg targetArg →
      RecCallAdequate C body True resultRel (source sourceArg) targetArg := by
  intro sourceArg
  induction sourceArg using wf.induction with
  | h sourceArg ih =>
      intro targetArg hrel
      exact (bodySound sourceArg targetArg hrel
        (fun smaller targetSmaller hsmall hlt =>
          ih smaller hlt targetSmaller hsmall)).sound

theorem RecReflection.adequate {S : ITree.HSig.{u, v}} {H : Signature}
    {a b : Tp} {C : Signature.Compat S H} {A B : Type u}
    (argRel : A → a.denote (ITree.CompE H.spec) → Prop)
    (resultRel : B → b.denote (ITree.CompE H.spec) → Prop)
    (source : A → Free S B)
    (body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b)
    (order : A → A → Prop) (wf : WellFounded order)
    (bodySound : ∀ sourceArg targetArg, argRel sourceArg targetArg →
      (∀ smaller targetSmaller, argRel smaller targetSmaller →
        order smaller sourceArg →
        RecCallAdequate C body True resultRel (source smaller) targetSmaller) →
      RecReflectionWitness C body True b resultRel
        (source sourceArg) (body targetArg)) :
    Adequate C argRel resultRel source
      (ITree.CompE.mrec fun x => Expr.denote (body x)) := by
  intro sourceArg targetArg hrel
  have hcps : RecCallAdequate C body True resultRel
      (source sourceArg) targetArg :=
    wellFounded argRel resultRel source body order wf bodySound
      sourceArg targetArg hrel
  have h := hcps (Z := B) (B := b.denote (ITree.CompE H.spec))
    True.intro resultRel (fun source => .pure source) ITree.CompE.ret (by
    intro source target hresult
    simp only [Free.toITree, Free.eval, ITree.CompE.interp_ret]
    exact ITree.CompE.Eutt.of_step C (.ret resultRel source target hresult))
  simp only [Free.bind_pure, ITree.CompE.bind_ret_right] at h
  exact h

def Reflection.natLit {S : ITree.HSig.{u, v}} {H : Signature} {r : Option (Tp × Tp)}
    {C : Signature.CompatAt S H r} {Φ : Prop} {α : Tp} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (n : Nat) (k : ∀ n', ReflectionRAt C (Φ ∧ n' = n) α result m) :
    ReflectionRAt C Φ α result m :=
  let r := k n
  ⟨.natLit n fun n' => (k n').1,
    ⟨fun hΦ => by
      change ITree.CompE.Eutt C result (Free.toITree m) (Expr.denote r.1)
      exact r.2.sound ⟨hΦ, rfl⟩⟩⟩

def Reflection.boolLit {S : ITree.HSig.{u, v}} {H : Signature} {r : Option (Tp × Tp)}
    {C : Signature.CompatAt S H r} {Φ : Prop} {α : Tp} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (b : Bool) (k : ∀ b', ReflectionRAt C (Φ ∧ b' = b) α result m) :
    ReflectionRAt C Φ α result m :=
  let r := k b
  ⟨.boolLit b fun b' => (k b').1,
    ⟨fun hΦ => by
      change ITree.CompE.Eutt C result (Free.toITree m) (Expr.denote r.1)
      exact r.2.sound ⟨hΦ, rfl⟩⟩⟩

def Reflection.encodedNat {S : ITree.HSig.{u, v}} {H : Signature}
    {C : Signature.Compat S H} {A : Type u} (source : A) (target : Nat)
    (rel : A → Nat → Prop) (h : rel source target) :
    ReflectionR C True .nat rel (.pure source) := by
  apply Reflection.natLit target
  intro target'
  apply Reflection.ret target'
  rintro ⟨-, rfl⟩
  exact h

def Reflection.encodedBool {S : ITree.HSig.{u, v}} {H : Signature}
    {C : Signature.Compat S H} {A : Type u} (source : A) (target : Bool)
    (rel : A → Bool → Prop) (h : rel source target) :
    ReflectionR C True .bool rel (.pure source) := by
  apply Reflection.boolLit target
  intro target'
  apply Reflection.ret target'
  rintro ⟨-, rfl⟩
  exact h

def Reflection.unitLit {S : ITree.HSig.{u, v}} {H : Signature} {r : Option (Tp × Tp)}
    {C : Signature.CompatAt S H r} {Φ : Prop} {α : Tp} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (k : ReflectionRAt C Φ α result m) : ReflectionRAt C Φ α result m :=
  ⟨.unitLit fun _ => k.1, ⟨k.2.sound⟩⟩

def Reflection.encodedUnit {S : ITree.HSig.{u, v}} {H : Signature}
    {C : Signature.Compat S H} {A : Type u} (source : A)
    (rel : A → Unit → Prop) (h : rel source ()) :
    ReflectionR C True .unit rel (.pure source) := by
  apply Reflection.unitLit
  apply Reflection.ret ()
  intro _
  exact h

def Reflection.un {S : ITree.HSig.{u, v}} {H : Signature} {r : Option (Tp × Tp)}
    {C : Signature.CompatAt S H r} {Φ : Prop} {a b : Tp0} {α : Tp} {A : Type u}
    (o : Un a b) (va : a.denote)
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (k : ∀ vb, ReflectionRAt C (Φ ∧ vb = o.denote va) α result m) :
    ReflectionRAt C Φ α result m :=
  let r := k (o.denote va)
  ⟨.un o va fun vb => (k vb).1,
    ⟨fun hΦ => by
      change ITree.CompE.Eutt C result (Free.toITree m) (Expr.denote r.1)
      exact r.2.sound ⟨hΦ, rfl⟩⟩⟩

def Reflection.bin {S : ITree.HSig.{u, v}} {H : Signature} {r : Option (Tp × Tp)}
    {C : Signature.CompatAt S H r}
    {Φ : Prop} {a b c : Tp0} {α : Tp} {A : Type u}
    (o : Bin a b c) (va : a.denote) (vb : b.denote)
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (k : ∀ vc, ReflectionRAt C (Φ ∧ vc = o.denote va vb) α result m) :
    ReflectionRAt C Φ α result m :=
  let r := k (o.denote va vb)
  ⟨.bin o va vb fun vc => (k vc).1,
    ⟨fun hPhi => by
      change ITree.CompE.Eutt C result (Free.toITree m) (Expr.denote r.1)
      exact r.2.sound ⟨hPhi, rfl⟩⟩⟩

def Reflection.app {S : ITree.HSig.{u, v}} {H : Signature}
    {C : Signature.Compat S H} {Φ : Prop} {a b α : Tp} {A Z : Type u}
    {argRel : A → b.denote (ITree.CompE H.spec) → Prop}
    {result : Z → α.denote (ITree.CompE H.spec) → Prop}
    (f : a.denote (ITree.CompE H.spec) →
      ITree.CompE H.spec (b.denote (ITree.CompE H.spec)))
    (x : a.denote (ITree.CompE H.spec)) {m : Free S A}
    (hm : Φ → ITree.CompE.Eutt C argRel (Free.toITree m) (f x))
    {ks : A → Free S Z}
    (k : ∀ target, Σ e : Expr H (Tp.denote (ITree.CompE H.spec)) none α,
      ∀ source, argRel source target → ReflectionWitness C Φ α result (ks source) e) :
    ReflectionR C Φ α result (m.bind ks) :=
  ⟨.app f x fun target => (k target).1,
    ⟨fun hΦ => by
      rw [Free.toITree_bind]
      apply ITree.CompE.Eutt.bind C (hm hΦ)
      exact fun source target h => (k target).2 source h |>.sound hΦ⟩⟩

def Reflection.call {S : ITree.HSig.{u, v}} {H : Signature}
    {C : Signature.Compat S H} {Φ : Prop} {a b : Tp} {A : Type u}
    {result : A → b.denote (ITree.CompE H.spec) → Prop}
    (f : a.denote (ITree.CompE H.spec) →
      ITree.CompE H.spec (b.denote (ITree.CompE H.spec)))
    (x : a.denote (ITree.CompE H.spec)) {m : Free S A}
    (hm : Φ → ITree.CompE.Eutt C result (Free.toITree m) (f x)) :
    ReflectionR C Φ b result m :=
  ⟨.app f x .ret,
    ⟨fun hΦ => by
      change ITree.CompE.Eutt C result (Free.toITree m)
        (ITree.CompE.bind (f x) ITree.CompE.ret)
      rw [ITree.CompE.bind_ret_right]
      exact hm hΦ⟩⟩

def Reflection.lam {S : ITree.HSig.{u, v}} {H : Signature}
    {C : Signature.Compat S H} {Φ : Prop} {a b α : Tp} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) none b)
    (k : (a.denote (ITree.CompE H.spec) →
        ITree.CompE H.spec (b.denote (ITree.CompE H.spec))) →
      Expr H (Tp.denote (ITree.CompE H.spec)) none α)
    (kSound : ReflectionWitness C Φ α result m
      (k (fun x => Expr.denote (body x)))) : ReflectionR C Φ α result m :=
  let f := fun x => Expr.denote (body x)
  ⟨.lam body k,
    ⟨fun hΦ => by
      change ITree.CompE.Eutt C result (Free.toITree m) (Expr.denote (k f))
      exact kSound.sound hΦ⟩⟩

def Reflection.letrec {S : ITree.HSig.{u, v}} {H : Signature}
    {C : Signature.Compat S H} {Φ : Prop} {a b α : Tp} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b)
    (k : (a.denote (ITree.CompE H.spec) →
        ITree.CompE H.spec (b.denote (ITree.CompE H.spec))) →
      Expr H (Tp.denote (ITree.CompE H.spec)) none α)
    (kSound : ReflectionWitness C Φ α result m
      (k (ITree.CompE.mrec fun x => Expr.denote (body x)))) :
    ReflectionR C Φ α result m :=
  let f := ITree.CompE.mrec fun x => Expr.denote (body x)
  ⟨.letrec body k,
    ⟨fun hΦ => by
      change ITree.CompE.Eutt C result (Free.toITree m) (Expr.denote (k f))
      exact kSound.sound hΦ⟩⟩

def Reflection.op {S : ITree.HSig.{u, v}} {H : Signature} (C : Signature.Compat S H)
    {Φ : Prop} {α : Tp} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop}
    (e : S.op) (h : H.op) (w : C.opRel e h)
    (input : (H.input h).denote) {sourceInput : S.input e}
    (hi : Φ → C.input w sourceInput input)
    {sourceBlocks : (b : S.branch e) → S.branchInput e b →
      Free S (S.branchOutput e b)}
    (blocks : ∀ bt xt, Expr H (Tp.denote (ITree.CompE H.spec)) none
      (.base (H.branchOutput h bt)))
    (blockSound : ∀ bt xt bs, (hbr : C.branch w bs bt) →
      ∀ xs, C.branchInput w hbr xs xt →
        ReflectionWitness C Φ (.base (H.branchOutput h bt))
          (C.branchOutput w hbr) (sourceBlocks bs xs) (blocks bt xt))
    {ks : S.output e → Free S A}
    (k : ∀ ot, Expr H (Tp.denote (ITree.CompE H.spec)) none α)
    (kSound : ∀ ot os, C.output w os ot →
      ReflectionWitness C Φ α result (ks os) (k ot)) :
    ReflectionR C Φ α result (.op e sourceInput sourceBlocks ks) :=
  ⟨.op h input blocks k,
    ⟨fun hPhi => by
      simp only [Expr.denote, DomR.perform, DomR.bind, Free.toITree]
      apply ITree.CompE.Eutt.of_step C
      exact .op result w sourceInput input (hi hPhi)
        (fun b x => Free.toITree (sourceBlocks b x))
        (fun o => Free.toITree (ks o))
        (fun b x => Expr.denote (blocks b x))
        (fun o => Expr.denote (k o))
        (fun bs bt hbr xs xt hx => blockSound bt xt bs hbr xs hx |>.sound hPhi)
        (fun os ot ho => kSound ot os ho |>.sound hPhi)⟩⟩

def Reflection.opRec {S : ITree.HSig.{u, v}} {H : Signature} {a b : Tp}
    (C : Signature.CompatAt S H (some (a, b)))
    {Φ : Prop} {α : Tp} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop}
    (e : S.op) (h : H.op) (w : C.opRel e (.inl h))
    (input : (H.input h).denote) {sourceInput : S.input e}
    (hi : Φ → C.input w sourceInput input)
    {sourceBlocks : (br : S.branch e) → S.branchInput e br →
      Free S (S.branchOutput e br)}
    (blocks : ∀ bt xt, Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b))
      (.base (H.branchOutput h bt)))
    (blockSound : ∀ bt xt bs, (hbr : C.branch w bs bt) →
      ∀ xs, C.branchInput w hbr xs xt →
        ReflectionWitnessAt C Φ (.base (H.branchOutput h bt))
          (C.branchOutput w hbr) (sourceBlocks bs xs) (blocks bt xt))
    {ks : S.output e → Free S A}
    (k : ∀ ot, Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) α)
    (kSound : ∀ ot os, C.output w os ot →
      ReflectionWitnessAt C Φ α result (ks os) (k ot)) :
    ReflectionRAt C Φ α result (.op e sourceInput sourceBlocks ks) :=
  ⟨.op h input blocks k,
    ⟨fun hΦ => by
      simp only [Expr.denote, DomR.perform, DomR.bind, Free.toITree]
      apply ITree.CompE.Eutt.of_step C
      exact .op result w sourceInput input (hi hΦ)
        (fun br x => Free.toITree (sourceBlocks br x))
        (fun o => Free.toITree (ks o))
        (fun br x => Expr.denote (blocks br x))
        (fun o => Expr.denote (k o))
        (fun bs bt hbr xs xt hx => blockSound bt xt bs hbr xs hx |>.sound hΦ)
        (fun os ot ho => kSound ot os ho |>.sound hΦ)⟩⟩

end Ast
end Freigen
