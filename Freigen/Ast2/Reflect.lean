import Freigen.Ast2.Basic
import Freigen.ITree2.Eutt

/-!
# Ast2 reflection combinators

This is the target surface for the Ast2 reflector: a reflection is a packed concrete AST plus a
soundness proof against the source `Freek` program. The combinators are the pack-returning API:
applying one emits exactly one AST node and extends the pending equation context when needed.
-/

namespace Freigen
namespace Ast2

/-! ## Unified higher-order reflection -/

abbrev EvalM (H : Signature) (α : Type) := ITree2.HComp H.spec α

/-- Reflection package used during construction.  Exact equality is retained locally because
    primitive and higher-order nodes are reflected one-for-one; the public contract is exposed
    as `Eutt`, allowing recursive reflection to insert guarding `tau` steps. -/
def Reflection {H : Signature} (Φ : Prop) (α : Tp)
    (m : Freek H.spec (α.denote (ITree2.HComp H.spec))) : Type 2 :=
  { e : Expr H (Tp.denote (ITree2.HComp H.spec)) none α //
    Φ → Expr.denote e = Freek.toITree m }

def Reflection.eutt {H : Signature} {Φ : Prop} {α : Tp}
    {m : Freek H.spec (α.denote (ITree2.HComp H.spec))} (r : Reflection Φ α m) :
    Φ → ITree2.CompE.Eutt (Expr.denote r.1) (Freek.toITree m) :=
  fun h => ITree2.CompE.Eutt.of_eq (r.2 h)

def Reflection.ret {H : Signature} {Φ : Prop} {α : Tp}
    (v : α.denote (ITree2.HComp H.spec))
    {v' : α.denote (ITree2.HComp H.spec)} (h : Φ → v = v') :
    Reflection (H := H) Φ α (Freek.pure (H := H.spec) v') :=
  ⟨.ret v, fun hΦ => by rw [h hΦ]; rfl⟩

def Reflection.bin {H : Signature} {Φ : Prop} {a b c : Tp0} {α : Tp}
    (o : Bin a b c) (va : a.denote) (vb : b.denote)
    {m : Freek H.spec (α.denote (ITree2.HComp H.spec))}
    (k : ∀ vc, Reflection (Φ ∧ vc = o.denote va vb) α m) : Reflection Φ α m :=
  ⟨.bin o va vb fun vc => (k vc).1, fun hΦ => (k _).2 ⟨hΦ, rfl⟩⟩

def Reflection.op {H : Signature} {Φ : Prop} {α : Tp}
    (e : H.op) (i : (H.input e).denote) {i' : (H.input e).denote} (hi : Φ → i = i')
    {srcBlocks : (b : H.branch e) → (H.branchInput e b).denote →
      Freek H.spec (H.branchOutput e b).denote}
    (blocks : ∀ b x, Reflection Φ (.base (H.branchOutput e b)) (srcBlocks b x))
    {ks : (H.output e).denote →
      Freek H.spec (α.denote (ITree2.HComp H.spec))}
    (k : ∀ o, Reflection Φ α (ks o)) :
    Reflection Φ α (.op e i' srcBlocks ks) :=
  ⟨.op e i (fun b x => (blocks b x).1) (fun o => (k o).1), fun hΦ => by
    rw [hi hΦ]
    simp only [Expr.denote, DomR.perform, DomR.bind, Freek.toITree, Freek.eval]
    congr 1
    · apply congrArg (fun bs : ((bx : H.spec.toBindSig.branch e) →
          ITree2.HComp H.spec (H.spec.toBindSig.branchOutput e bx)) =>
          ITree2.CompE.bindEff (𝓔 := ITree2.NoEff) (𝓑 := H.spec.toBindSig)
            (α := (H.output e).denote) e i' bs ITree2.CompE.ret)
      funext bx
      exact (blocks bx.1 bx.2).2 hΦ
    · funext o
      exact (k o).2 hΦ⟩


end Ast2
end Freigen
