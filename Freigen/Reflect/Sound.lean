import Freigen.Ast.Basic
import Freigen.ITree.Eutt

namespace Freigen
namespace Ast

universe u v

/-! ## Reflection contracts -/

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

def Adequate.congrTarget {S : ITree.HSig.{u, v}} {H : Signature}
    {C : Signature.Compat S H} {A B : Type u} {a b : Tp}
    {argRel : A → a.denote (ITree.CompE H.spec) → Prop}
    {resultRel : B → b.denote (ITree.CompE H.spec) → Prop}
    {source : A → Free S B}
    {target target' : a.denote (ITree.CompE H.spec) →
      ITree.CompE H.spec (b.denote (ITree.CompE H.spec))}
    (h : target = target') (sound : Adequate C argRel resultRel source target) :
    Adequate C argRel resultRel source target' := by
  subst target'
  exact sound

theorem related_of_eq {A B : Type} {rel : A → B → Prop} {source : A} {x y : B}
    (h : y = x) (hx : rel source x) : rel source y := by
  cases h
  exact hx

/-! ## Leaf constructors -/

/-- Attach source provenance without changing denotation or the synchronized soundness proof. -/
def Reflection.source {S : ITree.HSig.{u, v}} {H : Signature}
    {r : Option (Tp × Tp)} {C : Signature.CompatAt S H r}
    {Φ : Prop} {α : Tp} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (code : Expr H (Tp.denote (ITree.CompE H.spec)) r α)
    (range : SourceRange) (sound : ReflectionWitnessAt C Φ α result m code) :
    ReflectionWitnessAt C Φ α result m (.source range code) :=
  ⟨sound.sound⟩

def Reflection.ret {S : ITree.HSig.{u, v}} {H : Signature} {r : Option (Tp × Tp)}
    {C : Signature.CompatAt S H r}
    {Φ : Prop} {α : Tp} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop}
    (v : α.denote (ITree.CompE H.spec)) {v' : A} (h : Φ → result v' v) :
    ReflectionWitnessAt C Φ α result (.pure v') (.ret v) :=
  ⟨fun hPhi => by
    cases r with
    | none => exact ITree.CompE.Eutt.of_step C (.ret result v' v (h hPhi))
    | some ab =>
        cases ab
        exact ITree.CompE.Eutt.of_step C (.ret result v' v (h hPhi))⟩

/-! ## Recursive-body constructors -/

def RecReflection.ret {S : ITree.HSig.{u, v}} {H : Signature}
    {a b α : Tp} {C : Signature.Compat S H}
    {body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (a, b)) b}
    {Φ : Prop} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop}
    (v : α.denote (ITree.CompE H.spec)) {v' : A}
    (h : Φ → result v' v) :
    RecReflectionWitness C body Φ α result (.pure v') (.ret v) :=
  ⟨fun hΦ => by
    intro Z B q ks kt hk
    rw [Free.toITree_bind]
    change ITree.CompE.Eutt C q
      (ITree.CompE.bind (ITree.CompE.ret v') (fun x => Free.toITree (ks x)))
      (ITree.CompE.interp (fun x => Expr.denote (body x))
        (ITree.CompE.bind (ITree.CompE.ret v) kt))
    rw [ITree.CompE.bind_ret, ITree.CompE.bind_ret]
    exact hk v' v (h hΦ)⟩

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
    RecReflectionWitness C body Φ α result (sourceCall.bind sourceK)
      (.selfCall targetArg k) :=
  ⟨fun hΦ => by
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
    exact ITree.CompE.Eutt.tauR C hcall⟩

/-- A spilled nonrecursive helper call inside a recursive body. -/
def RecReflection.bindCall {S : ITree.HSig.{u, v}} {H : Signature}
    {ra rb arg resultTp α : Tp} {C : Signature.Compat S H}
    {body : ra.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (ra, rb)) rb}
    {Φ : Prop} {A Z : Type u}
    {argRel : A → resultTp.denote (ITree.CompE H.spec) → Prop}
    {result : Z → α.denote (ITree.CompE H.spec) → Prop}
    (f : arg.denote (ITree.CompE H.spec) →
      ITree.CompE H.spec (resultTp.denote (ITree.CompE H.spec)))
    (x : arg.denote (ITree.CompE H.spec)) {m : Free S A}
    (hm : Φ → ITree.CompE.Eutt C argRel (Free.toITree m) (f x))
    {sourceK : A → Free S Z}
    (k : resultTp.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) (some (ra, rb)) α)
    (kSound : ∀ target source, argRel source target →
      RecReflectionWitness C body Φ α result (sourceK source) (k target)) :
    RecReflectionWitness C body Φ α result (m.bind sourceK) (.app f x k) :=
  ⟨fun hΦ => by
    intro Y B q ks kt hk
    have sourceAssoc : (m.bind sourceK).bind ks =
        m.bind (fun source => (sourceK source).bind ks) :=
      LawfulMonad.bind_assoc m sourceK ks
    rw [sourceAssoc, Free.toITree_bind]
    change ITree.CompE.Eutt C q
      (ITree.CompE.bind (Free.toITree m)
        (fun source => Free.toITree ((sourceK source).bind ks)))
      (ITree.CompE.interp (fun x => Expr.denote (body x))
        (ITree.CompE.bind (Expr.denote (.app f x k)) kt))
    simp only [Expr.denote, DomR.bind, DomR.lift, ITree.CompE.bind_assoc]
    rw [ITree.CompE.interp_bind_sumL]
    apply ITree.CompE.Eutt.bind C (hm hΦ)
    intro source target hrel
    exact (kSound target source hrel).sound hΦ q ks kt hk⟩

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
    RecReflectionWitness C body Φ α result (.op e sourceInput sourceBlocks sourceK)
      (.op h input (fun bt => nomatch targetEmpty bt) k) :=
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
          exact (kSound ot os ho).sound hΦ q ks kt hk)⟩

/-! ## Generic recursion adequacy -/

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

/-! ## Ordinary computation constructors -/

/-- Soundness of a helper call followed by a source continuation. -/
def Reflection.bindCall {S : ITree.HSig.{u, v}} {H : Signature}
    {C : Signature.Compat S H} {Φ : Prop} {a b α : Tp} {A Z : Type u}
    {argRel : A → b.denote (ITree.CompE H.spec) → Prop}
    {result : Z → α.denote (ITree.CompE H.spec) → Prop}
    (f : a.denote (ITree.CompE H.spec) →
      ITree.CompE H.spec (b.denote (ITree.CompE H.spec)))
    (x : a.denote (ITree.CompE H.spec)) {m : Free S A}
    (hm : Φ → ITree.CompE.Eutt C argRel (Free.toITree m) (f x))
    {ks : A → Free S Z}
    (k : b.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) none α)
    (kSound : ∀ target source, argRel source target →
      ReflectionWitness C Φ α result (ks source) (k target)) :
    ReflectionWitness C Φ α result (m.bind ks) (.app f x k) := by
  constructor
  intro hΦ
  rw [Free.toITree_bind]
  apply ITree.CompE.Eutt.bind C (hm hΦ)
  exact fun source target h => (kSound target source h).sound hΦ

def Reflection.call {S : ITree.HSig.{u, v}} {H : Signature}
    {C : Signature.Compat S H} {Φ : Prop} {a b : Tp} {A : Type u}
    {result : A → b.denote (ITree.CompE H.spec) → Prop}
    (f : a.denote (ITree.CompE H.spec) →
      ITree.CompE H.spec (b.denote (ITree.CompE H.spec)))
    (x : a.denote (ITree.CompE H.spec)) {m : Free S A}
    (hm : Φ → ITree.CompE.Eutt C result (Free.toITree m) (f x)) :
    ReflectionWitness C Φ b result m (.app f x .ret) :=
  ⟨fun hΦ => by
      change ITree.CompE.Eutt C result (Free.toITree m)
        (ITree.CompE.bind (f x) ITree.CompE.ret)
      rw [ITree.CompE.bind_ret_right]
      exact hm hΦ⟩

def Reflection.lam {S : ITree.HSig.{u, v}} {H : Signature}
    {C : Signature.Compat S H} {Φ : Prop} {a b α : Tp} {A : Type u}
    {result : A → α.denote (ITree.CompE H.spec) → Prop} {m : Free S A}
    (body : a.denote (ITree.CompE H.spec) →
      Expr H (Tp.denote (ITree.CompE H.spec)) none b)
    (k : (a.denote (ITree.CompE H.spec) →
        ITree.CompE H.spec (b.denote (ITree.CompE H.spec))) →
      Expr H (Tp.denote (ITree.CompE H.spec)) none α)
    (kSound : ReflectionWitness C Φ α result m
      (k (fun x => Expr.denote (body x)))) :
    ReflectionWitness C Φ α result m (.lam body k) :=
  let f := fun x => Expr.denote (body x)
  ⟨fun hΦ => by
      change ITree.CompE.Eutt C result (Free.toITree m) (Expr.denote (k f))
      exact kSound.sound hΦ⟩

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
    ReflectionWitness C Φ α result m (.letrec body k) :=
  let f := ITree.CompE.mrec fun x => Expr.denote (body x)
  ⟨fun hΦ => by
      change ITree.CompE.Eutt C result (Free.toITree m) (Expr.denote (k f))
      exact kSound.sound hΦ⟩

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
    ReflectionWitness C Φ α result (.op e sourceInput sourceBlocks ks)
      (.op h input blocks k) :=
  ⟨fun hPhi => by
      simp only [Expr.denote, DomR.perform, DomR.bind, Free.toITree]
      apply ITree.CompE.Eutt.of_step C
      exact .op result w sourceInput input (hi hPhi)
        (fun b x => Free.toITree (sourceBlocks b x))
        (fun o => Free.toITree (ks o))
        (fun b x => Expr.denote (blocks b x))
        (fun o => Expr.denote (k o))
        (fun bs bt hbr xs xt hx => blockSound bt xt bs hbr xs hx |>.sound hPhi)
        (fun os ot ho => kSound ot os ho |>.sound hPhi)⟩

end Ast
end Freigen
