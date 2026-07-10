import Freigen.Ast2.Basic

/-!
# Ast2 reflection combinators

This is the target surface for the Ast2 reflector: a reflection is a packed concrete AST plus a
soundness proof against the source `Freek` program.  The combinators are the "third style" API:
applying one emits exactly one AST node and extends the pending equation context when needed.
-/

namespace Freigen
namespace Ast2

/-- The base `ITree2` domain for a coded Ast2 signature. -/
abbrev EvalM (𝓔 : EffSig) (𝓑 : BindSig) (α : Type) : Type :=
  ITree2.CompE 𝓔.spec 𝓑.spec α

/-- A reflection of source `m`, conditional on pending defining equations `Φ`. -/
def Reflection {𝓔 : EffSig} {𝓑 : BindSig} (Φ : Prop) (α : Tp0)
    (m : Freek 𝓔.spec 𝓑.spec α.denote) : Type 2 :=
  { e : Expr 𝓔 𝓑 Tp0.denote none α //
    Φ → Expr.denote e = Freek.toITree m }

/-! ## Top-down theorem form -/

/-- Reflect `pure`: emit `ret` on an atom whose defining equation matches the source value. -/
theorem reflect_ret {𝓔 : EffSig} {𝓑 : BindSig} {α : Tp0}
    (v : α.denote) {v' : α.denote} (h : v = v') :
    Expr.denote (.ret v : Expr 𝓔 𝓑 Tp0.denote none α) =
      Freek.toITree (.pure v') := by
  rw [h]
  rfl

/-- Reflect a primitive: emit a `bin` node binding a fresh atom `vc` with its defining equation. -/
theorem reflect_bin {𝓔 : EffSig} {𝓑 : BindSig} {a b c α : Tp0}
    (o : Bin a b c) (va : a.denote) (vb : b.denote)
    {k : c.denote → Expr 𝓔 𝓑 Tp0.denote none α}
    {t : EvalM 𝓔 𝓑 α.denote}
    (ih : ∀ vc, vc = o.denote va vb → Expr.denote (k vc) = t) :
    Expr.denote (.bin o va vb k) = t :=
  ih _ rfl

/-- Reflect an effect node. -/
theorem reflect_eff {𝓔 : EffSig} {𝓑 : BindSig} {α : Tp0}
    (e : 𝓔.ε) (i : (𝓔.𝓘 e).denote) {i' : (𝓔.𝓘 e).denote}
    {k : (𝓔.𝓞 e).denote → Expr 𝓔 𝓑 Tp0.denote none α}
    {ks : (𝓔.𝓞 e).denote → Freek 𝓔.spec 𝓑.spec α.denote}
    (hi : i = i') (ih : ∀ o, Expr.denote (k o) = Freek.toITree (ks o)) :
    Expr.denote (.eff e i k) =
      Freek.toITree (Freek.eff e i' ks) := by
  subst hi
  show ITree2.CompE.bind (EffSig.trigger (𝓑 := 𝓑) e i) (fun o => Expr.denote (k o)) =
    ITree2.CompE.bind (EffSig.trigger (𝓑 := 𝓑) e i) (fun o => Freek.toITree (ks o))
  exact congrArg (ITree2.CompE.bind (EffSig.trigger (𝓑 := 𝓑) e i)) (funext ih)

/-! ## Pack-returning form -/

/-- Reflect `pure`: the pack's node is `ret v`; the value condition may assume `Φ`. -/
def Reflection.ret {𝓔 : EffSig} {𝓑 : BindSig} {Φ : Prop} {α : Tp0}
    (v : α.denote) {v' : α.denote} (h : Φ → v = v') :
    Reflection (𝓔 := 𝓔) (𝓑 := 𝓑) Φ α (.pure v') :=
  ⟨.ret v, fun hΦ => by
    rw [h hΦ]
    rfl⟩

/-- Reflect a primitive.  The continuation works under the extended equation context. -/
def Reflection.bin {𝓔 : EffSig} {𝓑 : BindSig} {Φ : Prop} {a b c α : Tp0}
    (o : Bin a b c) (va : a.denote) (vb : b.denote)
    {m : Freek 𝓔.spec 𝓑.spec α.denote}
    (k : ∀ vc, Reflection (𝓔 := 𝓔) (𝓑 := 𝓑)
      (Φ ∧ vc = o.denote va vb) α m) :
    Reflection (𝓔 := 𝓔) (𝓑 := 𝓑) Φ α m :=
  ⟨.bin o va vb fun vc => (k vc).1,
    fun hΦ => (k _).2 ⟨hΦ, rfl⟩⟩

/-- Reflect an effect node. -/
def Reflection.eff {𝓔 : EffSig} {𝓑 : BindSig} {Φ : Prop} {α : Tp0}
    (e : 𝓔.ε) (i : (𝓔.𝓘 e).denote) {i' : (𝓔.𝓘 e).denote}
    (hi : Φ → i = i') {ks : (𝓔.𝓞 e).denote → Freek 𝓔.spec 𝓑.spec α.denote}
    (k : ∀ o, Reflection (𝓔 := 𝓔) (𝓑 := 𝓑) Φ α (ks o)) :
    Reflection (𝓔 := 𝓔) (𝓑 := 𝓑) Φ α (Freek.eff e i' ks) :=
  ⟨.eff e i fun o => (k o).1, fun hΦ => by
    rw [hi hΦ]
    show ITree2.CompE.bind (EffSig.trigger (𝓑 := 𝓑) e i') (fun o =>
        Expr.denote ((k o).1)) =
      ITree2.CompE.bind (EffSig.trigger (𝓑 := 𝓑) e i') (fun o => Freek.toITree (ks o))
    exact congrArg (ITree2.CompE.bind (EffSig.trigger (𝓑 := 𝓑) e i'))
      (funext fun o => (k o).2 hΦ)⟩

/-- Reflect a helper application using the target monad laws. -/
def Reflection.app {𝓔 : EffSig} {𝓑 : BindSig} {Φ : Prop} {α a b : Tp0}
    (f : a.denote → EvalM 𝓔 𝓑 b.denote) (x : a.denote)
    {fSrc : a.denote → Freek 𝓔.spec 𝓑.spec b.denote}
    (hf : Φ → f x = Freek.toITree (fSrc x))
    {ks : b.denote → Freek 𝓔.spec 𝓑.spec α.denote}
    (k : ∀ o, Reflection (𝓔 := 𝓔) (𝓑 := 𝓑) Φ α (ks o)) :
    Reflection (𝓔 := 𝓔) (𝓑 := 𝓑) Φ α (Freek.bind (fSrc x) ks) :=
  ⟨.app f x fun o => (k o).1, fun hΦ => by
    calc
      ITree2.CompE.bind (f x) (fun o => Expr.denote ((k o).1))
          = ITree2.CompE.bind (Freek.toITree (fSrc x)) (fun o => Expr.denote ((k o).1)) := by
              rw [hf hΦ]
      _ = ITree2.CompE.bind (Freek.toITree (fSrc x)) (fun o => Freek.toITree (ks o)) := by
              exact congrArg (ITree2.CompE.bind (Freek.toITree (fSrc x)))
                (funext fun o => (k o).2 hΦ)
      _ = Freek.toITree (Freek.bind (fSrc x) ks) := (Freek.toITree_bind (fSrc x) ks).symm⟩

end Ast2
end Freigen
