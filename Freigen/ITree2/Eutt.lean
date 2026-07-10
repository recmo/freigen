import Freigen.ITree2.Basic

namespace Freigen
namespace ITree2

universe u

namespace CompE

variable {𝓔 : EffSig.{u}} {𝓑 : BindSig.{u}}

/-- One weak-bisimulation step for the indexed scoped tree.  The relation is indexed by the
    internal label, because scoped-bind blocks live in `.block e b` fibers, not in the public
    `.normal` fiber. -/
inductive EuttF
    (R : (α : Type u) → (i : Ix 𝓑) → Tree 𝓔 𝓑 α i → Tree 𝓔 𝓑 α i → Prop) :
    {α : Type u} → {i : Ix 𝓑} → Tree 𝓔 𝓑 α i → Tree 𝓔 𝓑 α i → Prop where
  | ret {α : Type u} {i : Ix 𝓑} (a : result 𝓑 α i) :
      EuttF R (retAt a) (retAt a)
  | fail {α : Type u} {i : Ix 𝓑} :
      EuttF R (failAt (𝓔 := 𝓔) (𝓑 := 𝓑) (α := α) (i := i)) failAt
  | tau {α : Type u} {i : Ix 𝓑} (tx ty : Tree 𝓔 𝓑 α i)
      (h : R α i tx ty) :
      EuttF R (tauAt tx) (tauAt ty)
  | tauL {α : Type u} {i : Ix 𝓑} {y : Tree 𝓔 𝓑 α i} (tx : Tree 𝓔 𝓑 α i)
      (h : EuttF R tx y) : EuttF R (tauAt tx) y
  | tauR {α : Type u} {i : Ix 𝓑} {x : Tree 𝓔 𝓑 α i} (ty : Tree 𝓔 𝓑 α i)
      (h : EuttF R x ty) : EuttF R x (tauAt ty)
  | vis {α : Type u} {i : Ix 𝓑} (e : 𝓔.ε) (input : 𝓔.input e)
      (kx ky : 𝓔.output e → Tree 𝓔 𝓑 α i)
      (h : ∀ o, R α i (kx o) (ky o)) :
      EuttF R (visAt e input kx) (visAt e input ky)
  | bindEff {α : Type u} {i : Ix 𝓑} (e : 𝓑.ε) (input : 𝓑.input e)
      (blocksx blocksy : (b : 𝓑.branch e) → BlockE 𝓔 𝓑 α e b)
      (kx ky : 𝓑.output e → Tree 𝓔 𝓑 α i)
      (hb : ∀ b, R α (.block e b) (blocksx b) (blocksy b))
      (hk : ∀ o, R α i (kx o) (ky o)) :
      EuttF R (bindEffAt e input blocksx kx) (bindEffAt e input blocksy ky)

/-- Indexed equivalence up to finite `tau` steps. -/
def EuttAt {α : Type u} {i : Ix 𝓑} (x y : Tree 𝓔 𝓑 α i) : Prop :=
  ∃ R : (α : Type u) → (i : Ix 𝓑) → Tree 𝓔 𝓑 α i → Tree 𝓔 𝓑 α i → Prop,
    (∀ α i x y, R α i x y → EuttF R x y) ∧ R α i x y

/-- Public equivalence up to finite `tau` steps. -/
def Eutt {α : Type u} (x y : CompE 𝓔 𝓑 α) : Prop :=
  EuttAt x y

theorem euttF_diag
    {R : (α : Type u) → (i : Ix 𝓑) → Tree 𝓔 𝓑 α i → Tree 𝓔 𝓑 α i → Prop}
    (hR : ∀ α i (x : Tree 𝓔 𝓑 α i), R α i x x) {α : Type u} {i : Ix 𝓑}
    (x : Tree 𝓔 𝓑 α i) : EuttF R x x := by
  rcases cases_viewAt x with
    ⟨a, rfl⟩ | rfl | ⟨t, rfl⟩ | ⟨e, input, k, rfl⟩ | ⟨e, input, blocks, k, rfl⟩
  · exact .ret a
  · exact .fail
  · exact .tau t t (hR α i t)
  · exact .vis e input k k (fun o => hR α i (k o))
  · exact .bindEff e input blocks blocks k k
      (fun b => hR α (.block e b) (blocks b))
      (fun o => hR α i (k o))

theorem eutt_refl_at {α : Type u} {i : Ix 𝓑} (x : Tree 𝓔 𝓑 α i) : EuttAt x x :=
  ⟨fun α i x y => x = y, by
    intro α i x y h
    subst h
    exact euttF_diag (fun _ _ _ => rfl) x, rfl⟩

theorem eutt_refl {α : Type u} (x : CompE 𝓔 𝓑 α) : Eutt x x :=
  eutt_refl_at x

theorem Eutt.of_eq {α : Type u} {x y : CompE 𝓔 𝓑 α} (h : x = y) : Eutt x y := by
  subst h
  exact eutt_refl x

theorem EuttF.mono
    {R R' : (α : Type u) → (i : Ix 𝓑) → Tree 𝓔 𝓑 α i → Tree 𝓔 𝓑 α i → Prop}
    (h : ∀ α i x y, R α i x y → R' α i x y)
    {α : Type u} {i : Ix 𝓑} {x y : Tree 𝓔 𝓑 α i} (he : EuttF R x y) :
    EuttF R' x y := by
  induction he with
  | ret a => exact .ret a
  | fail => exact .fail
  | tau tx ty ht => exact .tau tx ty (h _ _ _ _ ht)
  | tauL tx _ ih => exact .tauL tx ih
  | tauR ty _ ih => exact .tauR ty ih
  | vis e input kx ky hk => exact .vis e input kx ky (fun o => h _ _ _ _ (hk o))
  | bindEff e input blocksx blocksy kx ky hb hk =>
      exact .bindEff e input blocksx blocksy kx ky
        (fun b => h _ _ _ _ (hb b))
        (fun o => h _ _ _ _ (hk o))

theorem eutt_closed_at {α : Type u} {i : Ix 𝓑} {x y : Tree 𝓔 𝓑 α i}
    (h : EuttAt x y) :
    EuttF (fun _ _ x y => EuttAt (𝓔 := 𝓔) (𝓑 := 𝓑) x y) x y := by
  obtain ⟨R, hR, hxy⟩ := h
  exact (hR α i x y hxy).mono (fun _ _ _ _ hxy => ⟨R, hR, hxy⟩)

theorem eutt_closed {α : Type u} {x y : CompE 𝓔 𝓑 α} (h : Eutt x y) :
    EuttF (fun _ _ x y => EuttAt (𝓔 := 𝓔) (𝓑 := 𝓑) x y) x y :=
  eutt_closed_at h

theorem eutt_tau {α : Type u} (t : CompE 𝓔 𝓑 α) : Eutt (tau t) t := by
  refine ⟨fun α i x y => x = tauAt y ∨ x = y, ?_, Or.inl rfl⟩
  intro α i x y h
  rcases h with rfl | rfl
  · exact .tauL y (euttF_diag (fun _ _ z => Or.inr rfl) y)
  · exact euttF_diag (fun _ _ z => Or.inr rfl) x

theorem eutt_tau_left {α : Type u} {x y : CompE 𝓔 𝓑 α} (h : Eutt x y) :
    Eutt (tau x) y := by
  refine ⟨fun α i a b =>
      (∃ x y : Tree 𝓔 𝓑 α i, a = tauAt x ∧ b = y ∧ EuttAt x y) ∨
      EuttAt a b, ?_, Or.inl ⟨x, y, rfl, rfl, h⟩⟩
  intro α i a b hab
  rcases hab with ⟨x, y, rfl, rfl, hxy⟩ | hab
  · exact .tauL x ((eutt_closed_at hxy).mono (fun _ _ _ _ h => Or.inr h))
  · exact (eutt_closed_at hab).mono (fun _ _ _ _ h => Or.inr h)

end CompE

end ITree2
end Freigen
