import Freigen.ITree2.Basic

namespace Freigen
namespace ITree2

universe u uEff uEffIn uEffOut uBind uBindIn uBindOut uBranch

namespace CompE

variable {𝓔 : EffSig.{uEff,uEffIn,uEffOut}}
  {𝓑 : BindSig.{u,uBind,uBindIn,uBindOut,uBranch}}

/-- One weak-bisimulation step for the indexed scoped tree.  The relation is indexed because
    scoped-bind block children can return branch-specific result types. -/
inductive EuttF
    (R : (α : Type u) → CompE 𝓔 𝓑 α → CompE 𝓔 𝓑 α → Prop) :
    {α : Type u} → CompE 𝓔 𝓑 α → CompE 𝓔 𝓑 α → Prop where
  | ret {α : Type u} (a : α) : EuttF R (ret a) (ret a)
  | fail {α : Type u} : EuttF R (fail : CompE 𝓔 𝓑 α) fail
  | tau {α : Type u} (tx ty : CompE 𝓔 𝓑 α) (h : R α tx ty) :
      EuttF R (tau tx) (tau ty)
  | tauL {α : Type u} {y : CompE 𝓔 𝓑 α} (tx : CompE 𝓔 𝓑 α)
      (h : EuttF R tx y) : EuttF R (tau tx) y
  | tauR {α : Type u} {x : CompE 𝓔 𝓑 α} (ty : CompE 𝓔 𝓑 α)
      (h : EuttF R x ty) : EuttF R x (tau ty)
  | vis {α : Type u} (e : 𝓔.ε) (i : 𝓔.input e)
      (kx ky : 𝓔.output e → CompE 𝓔 𝓑 α)
      (h : ∀ o, R α (kx o) (ky o)) :
      EuttF R (vis e i kx) (vis e i ky)
  | bindEff {α : Type u} (e : 𝓑.ε) (i : 𝓑.input e)
      (blocksx blocksy : (b : 𝓑.branch e) → CompE 𝓔 𝓑 (𝓑.branchOutput e b))
      (kx ky : 𝓑.output e → CompE 𝓔 𝓑 α)
      (hb : ∀ b, R (𝓑.branchOutput e b) (blocksx b) (blocksy b))
      (hk : ∀ o, R α (kx o) (ky o)) :
      EuttF R (bindEff e i blocksx kx) (bindEff e i blocksy ky)

/-- Equivalence up to finite `tau` steps, as the existence of a closed indexed bisimulation. -/
def Eutt {α : Type u} (x y : CompE 𝓔 𝓑 α) : Prop :=
  ∃ R : (α : Type u) → CompE 𝓔 𝓑 α → CompE 𝓔 𝓑 α → Prop,
    (∀ α x y, R α x y → EuttF R x y) ∧ R α x y

theorem euttF_diag
    {R : (α : Type u) → CompE 𝓔 𝓑 α → CompE 𝓔 𝓑 α → Prop}
    (hR : ∀ α (x : CompE 𝓔 𝓑 α), R α x x) {α : Type u}
    (x : CompE 𝓔 𝓑 α) : EuttF R x x := by
  rcases cases_view x with
    ⟨a, rfl⟩ | rfl | ⟨t, rfl⟩ | ⟨e, i, k, rfl⟩ | ⟨e, i, blocks, k, rfl⟩
  · exact .ret a
  · exact .fail
  · exact .tau t t (hR α t)
  · exact .vis e i k k (fun o => hR α (k o))
  · exact .bindEff e i blocks blocks k k
      (fun b => hR (𝓑.branchOutput e b) (blocks b))
      (fun o => hR α (k o))

theorem eutt_refl {α : Type u} (x : CompE 𝓔 𝓑 α) : Eutt x x :=
  ⟨fun α x y => x = y, by
    intro α x y h
    subst h
    exact euttF_diag (fun _ _ => rfl) x, rfl⟩

theorem Eutt.of_eq {α : Type u} {x y : CompE 𝓔 𝓑 α} (h : x = y) : Eutt x y := by
  subst h
  exact eutt_refl x

theorem EuttF.mono
    {R R' : (α : Type u) → CompE 𝓔 𝓑 α → CompE 𝓔 𝓑 α → Prop}
    (h : ∀ α x y, R α x y → R' α x y)
    {α : Type u} {x y : CompE 𝓔 𝓑 α} (he : EuttF R x y) : EuttF R' x y := by
  induction he with
  | ret a => exact .ret a
  | fail => exact .fail
  | tau tx ty ht => exact .tau tx ty (h _ _ _ ht)
  | tauL tx _ ih => exact .tauL tx ih
  | tauR ty _ ih => exact .tauR ty ih
  | vis e i kx ky hk => exact .vis e i kx ky (fun o => h _ _ _ (hk o))
  | bindEff e i blocksx blocksy kx ky hb hk =>
      exact .bindEff e i blocksx blocksy kx ky
        (fun b => h _ _ _ (hb b))
        (fun o => h _ _ _ (hk o))

theorem eutt_closed {α : Type u} {x y : CompE 𝓔 𝓑 α} (h : Eutt x y) :
    EuttF (fun _ x y => Eutt (𝓔 := 𝓔) (𝓑 := 𝓑) x y) x y := by
  obtain ⟨R, hR, hxy⟩ := h
  exact (hR α x y hxy).mono (fun _ _ _ hxy => ⟨R, hR, hxy⟩)

theorem eutt_tau {α : Type u} (t : CompE 𝓔 𝓑 α) : Eutt (tau t) t := by
  refine ⟨fun α x y => x = tau y ∨ x = y, ?_, Or.inl rfl⟩
  intro α x y h
  rcases h with rfl | rfl
  · exact .tauL y (euttF_diag (fun _ z => Or.inr rfl) y)
  · exact euttF_diag (fun _ z => Or.inr rfl) x

theorem eutt_tau_left {α : Type u} {x y : CompE 𝓔 𝓑 α} (h : Eutt x y) :
    Eutt (tau x) y := by
  refine ⟨fun α a b => (∃ x y : CompE 𝓔 𝓑 α, a = tau x ∧ b = y ∧ Eutt x y) ∨
      Eutt a b, ?_, Or.inl ⟨x, y, rfl, rfl, h⟩⟩
  intro α a b hab
  rcases hab with ⟨x, y, rfl, rfl, hxy⟩ | hab
  · exact .tauL x ((eutt_closed hxy).mono (fun _ _ _ h => Or.inr h))
  · exact (eutt_closed hab).mono (fun _ _ _ h => Or.inr h)

end CompE

end ITree2
end Freigen
