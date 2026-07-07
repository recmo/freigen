namespace Freigen
namespace ITree2

universe u uι uPos uAr uX uY uZ uEff uEffIn uEffOut
universe uBind uBindIn uBindOut uBranch

/-!
# Indexed polynomial functor for scoped interaction-tree steps

This module only defines the polynomial functor layer.  A scoped bind is not an ordinary
univariate `vis`: its block subcomputations return their own result types, while the operation
continuation returns the ambient result type.  The legal one-step shape is therefore an indexed
polynomial functor:

```
P.Obj X α := Σ p : P.Pos α, (i : P.Ar p) → X (P.next p i)
```

The carrier below is the indexed M-type used by the scoped computation layer.
-/

/-- An indexed polynomial functor over an index type `ι`. -/
structure IxPFunctor.{vι,vPos,vAr} (ι : Type vι) where
  Pos : ι → Type vPos
  Ar : {i : ι} → Pos i → Type vAr
  next : {i : ι} → (p : Pos i) → Ar p → ι

namespace IxPFunctor

/-- Apply an indexed polynomial functor to a family `X`. -/
@[reducible] def Obj {ι : Type uι} (P : IxPFunctor.{uι,uPos,uAr} ι)
    (X : ι → Type uX) (i : ι) : Type (max uPos uAr uX) :=
  Σ p : P.Pos i, (a : P.Ar p) → X (P.next p a)

/-- Map a family morphism over an indexed polynomial functor. -/
def map {ι : Type uι} (P : IxPFunctor.{uι,uPos,uAr} ι) {X : ι → Type uX}
    {Y : ι → Type uY}
    (f : (i : ι) → X i → Y i) {i : ι} : P.Obj X i → P.Obj Y i
  | ⟨p, child⟩ => ⟨p, fun a => f (P.next p a) (child a)⟩

@[simp] theorem map_id {ι : Type uι} (P : IxPFunctor.{uι,uPos,uAr} ι)
    {X : ι → Type uX} {i : ι}
    (x : P.Obj X i) :
    P.map (fun _ x => x) x = x := by
  cases x
  rfl

@[simp] theorem map_comp {ι : Type uι} (P : IxPFunctor.{uι,uPos,uAr} ι)
    {X : ι → Type uX} {Y : ι → Type uY} {Z : ι → Type uZ}
    (f : (i : ι) → X i → Y i) (g : (i : ι) → Y i → Z i)
    {i : ι} (x : P.Obj X i) :
    P.map (fun i x => g i (f i x)) x = P.map g (P.map f x) := by
  cases x
  rfl

/-! ## Indexed M-type -/

/-- `Approx P n i` is the depth-`n` approximation to the final coalgebra of `P` at index `i`. -/
inductive Approx {ι : Type uι} (P : IxPFunctor.{uι,uPos,uAr} ι) :
    Nat → ι → Type (max uι uPos uAr) where
  | continue {i : ι} : Approx P 0 i
  | intro {n : Nat} {i : ι} (p : P.Pos i) :
      ((a : P.Ar p) → Approx P n (P.next p a)) → Approx P (n + 1) i

namespace Approx

variable {ι : Type uι} {P : IxPFunctor.{uι,uPos,uAr} ι}

/-- The root position of a non-trivial approximation. -/
def head {n : Nat} {i : ι} : Approx P (n + 1) i → P.Pos i
  | .intro p _ => p

/-- The children of the root of a non-trivial approximation. -/
def children {n : Nat} {i : ι} (x : Approx P (n + 1) i) :
    (a : P.Ar (head x)) → Approx P n (P.next (head x) a) :=
  match x with
  | .intro _ child => child

end Approx

/-- Adjacent approximants agree when they expose the same finite prefix. -/
inductive Agree {ι : Type uι} (P : IxPFunctor.{uι,uPos,uAr} ι) :
    {n : Nat} → {i : ι} → Approx P n i → Approx P (n + 1) i → Prop where
  | continue {i : ι} (x : Approx P 0 i) (y : Approx P 1 i) :
      Agree P x y
  | intro {n : Nat} {i : ι} {p : P.Pos i}
      {x : (a : P.Ar p) → Approx P n (P.next p a)}
      {y : (a : P.Ar p) → Approx P (n + 1) (P.next p a)}
      (h : ∀ a, Agree P (x a) (y a)) :
      Agree P (Approx.intro p x) (Approx.intro p y)

namespace Approx

variable {ι : Type uι} {P : IxPFunctor.{uι,uPos,uAr} ι}

theorem agree_children {n : Nat} {i : ι}
    {x : Approx P (n + 1) i} {y : Approx P (n + 1 + 1) i}
    (h : Agree P x y) : head x = head y := by
  cases h
  rfl

def childrenAt {n : Nat} {i : ι} (x : Approx P (n + 1) i)
    (p : P.Pos i) (hp : head x = p) (a : P.Ar p) :
    Approx P n (P.next p a) :=
  let a' : P.Ar (head x) := cast (congrArg P.Ar hp).symm a
  have hnext : P.next (head x) a' = P.next p a := by
    cases hp
    rfl
  cast (congrArg (Approx P n) hnext) (children x a')

@[simp] theorem childrenAt_intro {n : Nat} {i : ι} (p : P.Pos i)
    (child : (a : P.Ar p) → Approx P n (P.next p a))
    (hp : head (Approx.intro p child) = p) (a : P.Ar p) :
    childrenAt (Approx.intro p child) p hp a = child a := by
  cases hp
  rfl

theorem childrenAt_eq_intro {n : Nat} {i : ι} {x : Approx P (n + 1) i}
    {p : P.Pos i} {child : (a : P.Ar p) → Approx P n (P.next p a)}
    (h : x = Approx.intro p child) (hp : head x = p) (a : P.Ar p) :
    childrenAt x p hp a = child a := by
  cases h
  exact childrenAt_intro p child hp a

theorem agree_childrenAt {n : Nat} {i : ι}
    {x : Approx P (n + 1) i} {y : Approx P (n + 1 + 1) i}
    (h : Agree P x y) {p : P.Pos i}
    (hx : head x = p) (hy : head y = p) (a : P.Ar p) :
    Agree P (childrenAt x p hx a) (childrenAt y p hy a) := by
  cases h with
  | intro hchild =>
      cases hx
      cases hy
      exact hchild a

theorem head_succ (n m : Nat) {i : ι} (x : (n : Nat) → Approx P n i)
    (h : ∀ n, Agree P (x n) (x (n + 1))) :
    head (x (n + 1)) = head (x (m + 1)) := by
  suffices ∀ n, head (x (n + 1)) = head (x 1) by
    rw [this n, this m]
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hs : head (x (n + 1 + 1)) = head (x (n + 1)) := by
        exact (agree_children (h (n + 1))).symm
      exact hs.trans ih

end Approx

/-- The indexed M-type/final-coalgebra carrier for an indexed polynomial functor. -/
structure M {ι : Type uι} (P : IxPFunctor.{uι,uPos,uAr} ι) (i : ι) :
    Type (max uι uPos uAr) where
  approx : (n : Nat) → Approx P n i
  consistent : ∀ n, Agree P (approx n) (approx (n + 1))

namespace M

variable {ι : Type uι} {P : IxPFunctor.{uι,uPos,uAr} ι}

theorem ext {i : ι} (x y : M P i) (h : ∀ n, x.approx n = y.approx n) : x = y := by
  cases x
  cases y
  congr
  funext n
  exact h n

def head {i : ι} (x : M P i) : P.Pos i :=
  Approx.head (x.approx 1)

def children {i : ι} (x : M P i) (a : P.Ar (head x)) : M P (P.next (head x) a) where
  approx
    | 0 => .continue
    | n + 1 =>
        Approx.childrenAt (x.approx (n + 1 + 1)) (head x)
          (by
            dsimp only [head]
            exact Approx.head_succ (n + 1) 0 x.approx x.consistent)
          a
  consistent := by
    intro n
    cases n with
    | zero =>
        exact .continue _ _
    | succ n =>
        exact Approx.agree_childrenAt (x.consistent (n + 1 + 1))
          (by
            dsimp only [head]
            exact Approx.head_succ (n + 1) 0 x.approx x.consistent)
          (by
            dsimp only [head]
            exact Approx.head_succ (n + 1 + 1) 0 x.approx x.consistent)
          a

/-- Destruct one layer of an indexed M-tree. -/
def dest {i : ι} (x : M P i) : P.Obj (M P) i :=
  ⟨head x, children x⟩

/-- Constructor from one indexed-polynomial layer whose children are already M-trees. -/
def ofStep {i : ι} (x : P.Obj (M P) i) : M P i where
  approx
    | 0 => .continue
    | n + 1 => .intro x.1 fun a => (x.2 a).approx n
  consistent
    | 0 => .continue _ _
    | n + 1 => by
        rcases x with ⟨p, child⟩
        exact Agree.intro (fun a => (child a).consistent n)

@[simp] theorem dest_ofStep {i : ι} (x : P.Obj (M P) i) :
    dest (ofStep x) = x := by
  rcases x with ⟨p, child⟩
  refine Sigma.ext (show (dest (ofStep (⟨p, child⟩ : P.Obj (M P) i))).1 = p from rfl) ?_
  dsimp only [dest, head, ofStep]
  apply heq_of_eq
  change (fun a : P.Ar p => children (ofStep (⟨p, child⟩ : P.Obj (M P) i)) a) = child
  funext a
  apply ext
  intro n
  cases n with
  | zero =>
      cases (child a).approx 0
      rfl
  | succ n =>
      dsimp only [dest, children, ofStep, head]
      change Approx.childrenAt (Approx.intro p (fun a => (child a).approx (n + 1))) p _ a =
        (child a).approx (n + 1)
      rw [Approx.childrenAt_intro]

set_option backward.isDefEq.respectTransparency false in
theorem ofStep_dest {i : ι} (x : M P i) : ofStep (dest x) = x := by
  apply ext
  intro n
  dsimp only [ofStep]
  induction n with
  | zero =>
      cases x.approx 0
      rfl
  | succ n =>
      dsimp only [dest, head]
      rcases happrox : x.approx (n + 1) with - | ⟨hd, child⟩
      have hhead : hd = Approx.head (x.approx 1) := by
        rw [← Approx.head_succ n 0 x.approx x.consistent, happrox]
        rfl
      revert child
      rw [hhead]
      intro child happrox
      congr
      funext a
      cases n with
      | zero =>
          cases child a
          rfl
      | succ n =>
          dsimp only [children, head]
          exact Approx.childrenAt_eq_intro happrox _ a

theorem eq_of_dest_eq {i : ι} {x y : M P i} (h : dest x = dest y) : x = y := by
  rw [← ofStep_dest x, ← ofStep_dest y, h]

def sCorec {X : ι → Type uX} (f : (i : ι) → X i → P.Obj X i) :
    {i : ι} → X i → (n : Nat) → Approx P n i
  | _, _, 0 => .continue
  | i, x, n + 1 =>
      match f i x with
      | ⟨p, child⟩ => .intro p fun a => sCorec f (child a) n

theorem sCorec_consistent {X : ι → Type uX} (f : (i : ι) → X i → P.Obj X i) :
    {i : ι} → (x : X i) → ∀ n, Agree P (sCorec f x n) (sCorec f x (n + 1)) := by
  intro i x n
  induction n generalizing i x with
  | zero =>
      exact .continue _ _
  | succ n ih =>
      simp only [sCorec]
      rcases f i x with ⟨p, child⟩
      exact Agree.intro (fun a => ih (child a))

/-- Indexed corecursor for the indexed M-type. -/
def corec {X : ι → Type uX} (f : (i : ι) → X i → P.Obj X i) {i : ι}
    (x : X i) : M P i where
  approx := sCorec f x
  consistent := sCorec_consistent f x

theorem corec_def {X : ι → Type uX} (f : (i : ι) → X i → P.Obj X i)
    {i : ι} (x : X i) :
    corec f x = ofStep (P.map (fun i => corec f (i := i)) (f i x)) := by
  apply ext
  intro n
  cases n with
  | zero => rfl
  | succ n =>
      dsimp only [corec, ofStep, sCorec]
      rcases f i x with ⟨p, child⟩
      rfl

theorem dest_corec {X : ι → Type uX} (f : (i : ι) → X i → P.Obj X i)
    {i : ι} (x : X i) :
    dest (corec f x) = P.map (fun i => corec f (i := i)) (f i x) := by
  rw [corec_def, dest_ofStep]

theorem bisim (R : (i : ι) → M P i → M P i → Prop)
    (h : ∀ i (x y : M P i), R i x y →
      ∃ (p : P.Pos i) (fx fy : (a : P.Ar p) → M P (P.next p a)),
        dest x = ⟨p, fx⟩ ∧ dest y = ⟨p, fy⟩ ∧
          ∀ a, R (P.next p a) (fx a) (fy a)) :
    ∀ {i : ι} (x y : M P i), R i x y → x = y := by
  intro i x y hxy
  apply ext
  intro n
  induction n generalizing i x y with
  | zero =>
      cases x.approx 0
      cases y.approx 0
      rfl
  | succ n ih =>
      obtain ⟨p, fx, fy, hx, hy, hchild⟩ := h i x y hxy
      have hxmk : x = ofStep (⟨p, fx⟩ : P.Obj (M P) i) := by
        rw [← ofStep_dest x, hx]
      have hymk : y = ofStep (⟨p, fy⟩ : P.Obj (M P) i) := by
        rw [← ofStep_dest y, hy]
      rw [hxmk, hymk]
      dsimp only [ofStep]
      congr
      funext a
      exact ih (fx a) (fy a) (hchild a)

end M

end IxPFunctor

/-- First-order effect signature: operation names, input payload, and output payload. -/
structure EffSig.{vEff,vEffIn,vEffOut} where
  ε : Type vEff
  input : ε → Type vEffIn
  output : ε → Type vEffOut

/-- First-order scoped-bind signature: an operation has an input, an output, and a family of
    block branches, each with its own result type. -/
structure BindSig.{v,vBind,vBindIn,vBindOut,vBranch} where
  ε : Type vBind
  input : ε → Type vBindIn
  output : ε → Type vBindOut
  branch : ε → Type vBranch
  branchOutput : (e : ε) → branch e → Type v

/-- Positions of one scoped interaction-tree step at ambient result type `α`. -/
inductive Pos (𝓔 : EffSig.{uEff,uEffIn,uEffOut})
    (𝓑 : BindSig.{u,uBind,uBindIn,uBindOut,uBranch}) :
    Type u → Type (max u uEff uEffIn uBind uBindIn) where
  | ret {α : Type u} : α → Pos 𝓔 𝓑 α
  | tau {α : Type u} : Pos 𝓔 𝓑 α
  | fail {α : Type u} : Pos 𝓔 𝓑 α
  | vis {α : Type u} (e : 𝓔.ε) : 𝓔.input e → Pos 𝓔 𝓑 α
  | bindEff {α : Type u} (e : 𝓑.ε) : 𝓑.input e → Pos 𝓔 𝓑 α

/-- Child names for one position. -/
@[reducible] def Ar {𝓔 : EffSig.{uEff,uEffIn,uEffOut}}
    {𝓑 : BindSig.{u,uBind,uBindIn,uBindOut,uBranch}} {α : Type u} :
    Pos 𝓔 𝓑 α → Type (max uEffOut uBranch uBindOut)
  | .ret _ => PEmpty
  | .tau => PUnit
  | .fail => PEmpty
  | .vis e _ => ULift.{max uEffOut uBranch uBindOut, uEffOut} (𝓔.output e)
  | .bindEff e _ =>
      ULift.{max uEffOut uBranch uBindOut, uBranch} (𝓑.branch e) ⊕
        ULift.{max uEffOut uBranch uBindOut, uBindOut} (𝓑.output e)

/-- Result type of each child.  For `bindEff`, left children are scoped blocks and right
    children are the ordinary continuation. -/
@[reducible] def next {𝓔 : EffSig.{uEff,uEffIn,uEffOut}}
    {𝓑 : BindSig.{u,uBind,uBindIn,uBindOut,uBranch}} {α : Type u} :
    (p : Pos 𝓔 𝓑 α) → Ar p → Type u
  | .ret _, h => nomatch h
  | .tau, _ => α
  | .fail, h => nomatch h
  | .vis _ _, _ => α
  | .bindEff e _, Sum.inl b => 𝓑.branchOutput e b.down
  | .bindEff _ _, Sum.inr _ => α

/-- The indexed polynomial functor for scoped interaction-tree steps. -/
def P (𝓔 : EffSig.{uEff,uEffIn,uEffOut})
    (𝓑 : BindSig.{u,uBind,uBindIn,uBindOut,uBranch}) :
    IxPFunctor.{u+1, max u uEff uEffIn uBind uBindIn, max uEffOut uBranch uBindOut}
      (Type u) where
  Pos := Pos 𝓔 𝓑
  Ar := Ar
  next := next

end ITree2
end Freigen
