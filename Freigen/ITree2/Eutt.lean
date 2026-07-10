import Freigen.ITree2.Basic

namespace Freigen
namespace ITree2

universe u

namespace CompE

variable {H : HSig.{u}}

/-- One weak-bisimulation step for the indexed scoped tree.  The relation is indexed by the
    internal label, because scoped-bind blocks live in `.block e b` fibers, not in the public
    `.normal` fiber. -/
inductive EuttF
    (R : (α : Type u) → (i : Ix H) → Tree H α i → Tree H α i → Prop) :
    {α : Type u} → {i : Ix H} → Tree H α i → Tree H α i → Prop where
  | ret {α : Type u} {i : Ix H} (a : result H α i) :
      EuttF R (retAt a) (retAt a)
  | fail {α : Type u} {i : Ix H} :
      EuttF R (failAt (H := H) (α := α) (i := i)) failAt
  | tau {α : Type u} {i : Ix H} (tx ty : Tree H α i)
      (h : R α i tx ty) :
      EuttF R (tauAt tx) (tauAt ty)
  | tauL {α : Type u} {i : Ix H} {y : Tree H α i} (tx : Tree H α i)
      (h : EuttF R tx y) : EuttF R (tauAt tx) y
  | tauR {α : Type u} {i : Ix H} {x : Tree H α i} (ty : Tree H α i)
      (h : EuttF R x ty) : EuttF R x (tauAt ty)
  | op {α : Type u} {i : Ix H} (e : H.op) (input : H.input e)
      (blocksx blocksy : (b : H.Block e) → BlockE H α e b)
      (kx ky : H.output e → Tree H α i)
      (hb : ∀ b, R α (.block e b) (blocksx b) (blocksy b))
      (hk : ∀ o, R α i (kx o) (ky o)) :
      EuttF R (opAt e input blocksx kx) (opAt e input blocksy ky)

/-- Indexed equivalence up to finite `tau` steps. -/
def EuttAt {α : Type u} {i : Ix H} (x y : Tree H α i) : Prop :=
  ∃ R : (α : Type u) → (i : Ix H) → Tree H α i → Tree H α i → Prop,
    (∀ α i x y, R α i x y → EuttF R x y) ∧ R α i x y

/-- Public equivalence up to finite `tau` steps. -/
def Eutt {α : Type u} (x y : CompE H α) : Prop :=
  EuttAt x y

theorem euttF_diag
    {R : (α : Type u) → (i : Ix H) → Tree H α i → Tree H α i → Prop}
    (hR : ∀ α i (x : Tree H α i), R α i x x) {α : Type u} {i : Ix H}
    (x : Tree H α i) : EuttF R x x := by
  rcases cases_viewAt x with
    ⟨a, rfl⟩ | rfl | ⟨t, rfl⟩ | ⟨e, input, blocks, k, rfl⟩
  · exact .ret a
  · exact .fail
  · exact .tau t t (hR α i t)
  · exact .op e input blocks blocks k k
      (fun b => hR α (.block e b) (blocks b))
      (fun o => hR α i (k o))

theorem eutt_refl_at {α : Type u} {i : Ix H} (x : Tree H α i) : EuttAt x x :=
  ⟨fun α i x y => x = y, by
    intro α i x y h
    subst h
    exact euttF_diag (fun _ _ _ => rfl) x, rfl⟩

theorem eutt_refl {α : Type u} (x : CompE H α) : Eutt x x :=
  eutt_refl_at x

theorem Eutt.of_eq {α : Type u} {x y : CompE H α} (h : x = y) : Eutt x y := by
  subst h
  exact eutt_refl x

theorem EuttF.mono
    {R R' : (α : Type u) → (i : Ix H) → Tree H α i → Tree H α i → Prop}
    (h : ∀ α i x y, R α i x y → R' α i x y)
    {α : Type u} {i : Ix H} {x y : Tree H α i} (he : EuttF R x y) :
    EuttF R' x y := by
  induction he with
  | ret a => exact .ret a
  | fail => exact .fail
  | tau tx ty ht => exact .tau tx ty (h _ _ _ _ ht)
  | tauL tx _ ih => exact .tauL tx ih
  | tauR ty _ ih => exact .tauR ty ih
  | op e input blocksx blocksy kx ky hb hk =>
      exact .op e input blocksx blocksy kx ky
        (fun b => h _ _ _ _ (hb b))
        (fun o => h _ _ _ _ (hk o))

theorem eutt_closed_at {α : Type u} {i : Ix H} {x y : Tree H α i}
    (h : EuttAt x y) :
    EuttF (fun _ _ x y => EuttAt (H := H) x y) x y := by
  obtain ⟨R, hR, hxy⟩ := h
  exact (hR α i x y hxy).mono (fun _ _ _ _ hxy => ⟨R, hR, hxy⟩)

theorem eutt_closed {α : Type u} {x y : CompE H α} (h : Eutt x y) :
    EuttF (fun _ _ x y => EuttAt (H := H) x y) x y :=
  eutt_closed_at h

theorem eutt_tau {α : Type u} (t : CompE H α) : Eutt (tau t) t := by
  refine ⟨fun α i x y => x = tauAt y ∨ x = y, ?_, Or.inl rfl⟩
  intro α i x y h
  rcases h with rfl | rfl
  · exact .tauL y (euttF_diag (fun _ _ z => Or.inr rfl) y)
  · exact euttF_diag (fun _ _ z => Or.inr rfl) x

theorem eutt_tau_left {α : Type u} {x y : CompE H α} (h : Eutt x y) :
    Eutt (tau x) y := by
  refine ⟨fun α i a b =>
      (∃ x y : Tree H α i, a = tauAt x ∧ b = y ∧ EuttAt x y) ∨
      EuttAt a b, ?_, Or.inl ⟨x, y, rfl, rfl, h⟩⟩
  intro α i a b hab
  rcases hab with ⟨x, y, rfl, rfl, hxy⟩ | hab
  · exact .tauL x ((eutt_closed_at hxy).mono (fun _ _ _ _ h => Or.inr h))
  · exact (eutt_closed_at hab).mono (fun _ _ _ _ h => Or.inr h)

theorem EuttF.symm
    {R : (α : Type u) → (i : Ix H) → Tree H α i → Tree H α i → Prop}
    {α : Type u} {i : Ix H} {x y : Tree H α i} (h : EuttF R x y) :
    EuttF (fun α i x y => R α i y x) y x := by
  induction h with
  | ret a => exact .ret a
  | fail => exact .fail
  | tau tx ty ht => exact .tau ty tx ht
  | tauL tx _ ih => exact .tauR tx ih
  | tauR ty _ ih => exact .tauL ty ih
  | op e input blocksx blocksy kx ky hb hk =>
      exact .op e input blocksy blocksx ky kx hb hk

theorem eutt_symm_at {α : Type u} {i : Ix H} {x y : Tree H α i}
    (h : EuttAt x y) : EuttAt y x := by
  obtain ⟨R, hR, hxy⟩ := h
  refine ⟨(fun α i x y => R α i y x), ?_, hxy⟩
  intro α i a b hab
  exact (hR α i b a hab).symm

theorem eutt_symm {α : Type u} {x y : CompE H α} (h : Eutt x y) : Eutt y x :=
  eutt_symm_at h

theorem eutt_tau_right {α : Type u} {x y : CompE H α} (h : Eutt x y) :
    Eutt x (tau y) :=
  eutt_symm (eutt_tau_left (eutt_symm h))

end CompE

end ITree2
end Freigen
