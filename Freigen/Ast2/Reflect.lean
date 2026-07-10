import Freigen.Ast2.Basic
import Freigen.ITree2.Eutt

namespace Freigen
namespace Ast2

universe u v

abbrev EvalM (H : Signature) (α : Type) := ITree2.CompE H.spec α

structure ReflectionWitness {S : ITree2.HSig.{u, v}} {H : Signature}
    (C : Signature.Compat S H) (Φ : Prop) (α : Tp) {A : Type u}
    (result : A → α.denote (ITree2.CompE H.spec) → Prop) (m : Freek S A)
    (e : Expr H (Tp.denote (ITree2.CompE H.spec)) none α) : Type (max u v + 2) where
  sound : Φ → ITree2.CompE.Eutt C result (Freek.toITree m) (Expr.denote e)

def ReflectionR {S : ITree2.HSig.{u, v}} {H : Signature} (C : Signature.Compat S H)
    (Φ : Prop) (α : Tp) {A : Type u}
    (result : A → α.denote (ITree2.CompE H.spec) → Prop) (m : Freek S A) : Type (max u v + 2) :=
  Σ e : Expr H (Tp.denote (ITree2.CompE H.spec)) none α,
    ReflectionWitness C Φ α result m e

abbrev Reflection {S : ITree2.HSig.{0, v}} {H : Signature} (C : Signature.Compat S H)
    (Φ : Prop) (α : Tp)
    (m : Freek S (α.denote (ITree2.CompE H.spec))) :=
  ReflectionR C Φ α Eq m

def Reflection.eutt {S : ITree2.HSig.{0, v}} {H : Signature} {C : Signature.Compat S H}
    {Φ : Prop} {α : Tp} {m : Freek S (α.denote (ITree2.CompE H.spec))}
    (r : Reflection C Φ α m) : Φ →
      ITree2.CompE.Eutt C Eq (Freek.toITree m) (Expr.denote r.1) :=
  r.2.sound

def Reflection.ret {S : ITree2.HSig.{u, v}} {H : Signature} {C : Signature.Compat S H}
    {Φ : Prop} {α : Tp} {A : Type u}
    {result : A → α.denote (ITree2.CompE H.spec) → Prop}
    (v : α.denote (ITree2.CompE H.spec)) {v' : A} (h : Φ → result v' v) :
    ReflectionR C Φ α result (.pure v') :=
  ⟨.ret v, ⟨fun hPhi => by
    exact ITree2.CompE.Eutt.of_step C (.ret result v' v (h hPhi))⟩⟩

def Reflection.bin {S : ITree2.HSig.{u, v}} {H : Signature} {C : Signature.Compat S H}
    {Φ : Prop} {a b c : Tp0} {α : Tp} {A : Type u}
    (o : Bin a b c) (va : a.denote) (vb : b.denote)
    {result : A → α.denote (ITree2.CompE H.spec) → Prop} {m : Freek S A}
    (k : ∀ vc, ReflectionR C (Φ ∧ vc = o.denote va vb) α result m) :
    ReflectionR C Φ α result m :=
  let r := k (o.denote va vb)
  ⟨.bin o va vb fun vc => (k vc).1,
    ⟨fun hPhi => by
      change ITree2.CompE.Eutt C result (Freek.toITree m) (Expr.denote r.1)
      exact r.2.sound ⟨hPhi, rfl⟩⟩⟩

def Reflection.op {S : ITree2.HSig.{u, v}} {H : Signature} (C : Signature.Compat S H)
    {Φ : Prop} {α : Tp} {A : Type u}
    {result : A → α.denote (ITree2.CompE H.spec) → Prop}
    (e : S.op) (h : H.op) (w : C.opRel e h)
    (input : (H.input h).denote) {sourceInput : S.input e}
    (hi : Φ → C.input w sourceInput input)
    {sourceBlocks : (b : S.branch e) → S.branchInput e b →
      Freek S (S.branchOutput e b)}
    (blocks : ∀ bt xt, Σ eb : Expr H (Tp.denote (ITree2.CompE H.spec)) none
        (.base (H.branchOutput h bt)),
      ∀ bs, (hbr : C.branch w bs bt) → ∀ xs, C.branchInput w hbr xs xt →
        ReflectionWitness C Φ (.base (H.branchOutput h bt))
          (C.branchOutput w hbr) (sourceBlocks bs xs) eb)
    {ks : S.output e → Freek S A}
    (k : ∀ ot, Σ ek : Expr H (Tp.denote (ITree2.CompE H.spec)) none α,
      ∀ os, C.output w os ot → ReflectionWitness C Φ α result (ks os) ek) :
    ReflectionR C Φ α result (.op e sourceInput sourceBlocks ks) :=
  ⟨.op h input (fun b x => (blocks b x).1) (fun o => (k o).1),
    ⟨fun hPhi => by
      simp only [Expr.denote, DomR.perform, DomR.bind, Freek.toITree]
      apply ITree2.CompE.Eutt.of_step C
      exact .op result w sourceInput input (hi hPhi)
        (fun b x => Freek.toITree (sourceBlocks b x))
        (fun o => Freek.toITree (ks o))
        (fun b x => Expr.denote (blocks b x).1)
        (fun o => Expr.denote (k o).1)
        (fun bs bt hbr xs xt hx => (blocks bt xt).2 bs hbr xs hx |>.sound hPhi)
        (fun os ot ho => (k ot).2 os ho |>.sound hPhi)⟩⟩

end Ast2
end Freigen
