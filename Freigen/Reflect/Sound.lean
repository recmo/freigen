import Batteries.Data.Fin.Fold
import Freigen.Ast.Basic
import Freigen.Free
import Freigen.ITree.Eutt

/-!
# Compositional soundness lemmas for the reflector

The reflector builds its `≈`-soundness proof **structurally**, mirroring the source term: as it walks
a `Free` program it emits, at every node, an equation

```
denote C = ITree.bind (ofFree e) Kf          -- (★)
```

(`Kf` = the denotation of the reflected continuation), assembled from the equation of the sub-terms
by the congruence lemma for that node.  This is what lets a proof-erased `vget`/`vset`/`aget`/`aset`
carry the *actual* in-bounds proof from the source (`sc_vget … (h : i < n)` is literally `dif_pos h`)
— no `simp`, no decidability, no reachability of a hypothesis: the proof term mirrors the term.

Each `sc_*` is one node's step of (★); every other `Code` node's step is definitional (`rfl`).  The
whole per-program proof is a tree of these applied to each other, `Eutt.of_eq`-lifted at the very top.
-/

namespace Freigen
open Freigen.ITree

variable {Op : Type → Type → Type 1} {SOp : Type → Type}

/-- `ITree.bind` distributes over a boolean branch. -/
theorem bind_cond {α β : Type} (c : Bool) (a b : Comp Op α) (k : α → Comp Op β) :
    ITree.bind (cond c a b) k = cond c (ITree.bind a k) (ITree.bind b k) := by cases c <;> rfl

/-! ## Pure-atom steps: the reflected partial-op nodes carry the source's proof

`sc_pop` is the one generic step; each per-op `sc_*` bridges the source's proof (`h : i < n`, …) to
`POp.denote … = some v` (a `dif_pos`).  A new `POp` needs exactly one bridging lemma here. -/

/-- Generic **partial-op step**: when the op's denotation succeeds, the `pop` node steps to its
    continuation — the erased `fail` branch is closed by `h`. -/
theorem sc_pop {α b : Tp} {as : List Tp} (o : POp as b) (args : HList Tp.denote as)
    {v : b.denote} (kk : b.denote → Code Op SOp (KC Op) Tp.denote α)
    (h : POp.denote o args = some v) :
    denote (Code.pop o args kk) = denote (kk v) := by
  simp only [denote]
  rw [h]

/-- **Vector get**, in bounds by the *source's* proof `h`. -/
theorem sc_vget {α a : Tp} {n : Nat} (v : Vector a.denote n) (i : Nat)
    (kk : a.denote → Code Op SOp (KC Op) Tp.denote α) (h : i < n) :
    denote (Code.pop .vget (.cons v (.cons i .nil)) kk) = denote (kk (v[i]'h)) :=
  sc_pop .vget (.cons v (.cons i .nil)) kk (by exact dif_pos h)

/-- **Vector set**, in bounds by the source's proof `h`. -/
theorem sc_vset {α a : Tp} {n : Nat} (v : Vector a.denote n) (i : Nat) (x : a.denote)
    (kk : Vector a.denote n → Code Op SOp (KC Op) Tp.denote α) (h : i < n) :
    denote (Code.pop .vset (.cons v (.cons i (.cons x .nil))) kk) = denote (kk (v.set i x h)) :=
  sc_pop .vset (.cons v (.cons i (.cons x .nil))) kk (by exact dif_pos h)

/-- **Array get**, in bounds by the source's proof `h`. -/
theorem sc_aget {α a : Tp} (v : Array a.denote) (i : Nat)
    (kk : a.denote → Code Op SOp (KC Op) Tp.denote α) (h : i < v.size) :
    denote (Code.pop .aget (.cons v (.cons i .nil)) kk) = denote (kk (v[i]'h)) :=
  sc_pop .aget (.cons v (.cons i .nil)) kk (by exact dif_pos h)

/-- **Array set**, in bounds by the source's proof `h`. -/
theorem sc_aset {α a : Tp} (v : Array a.denote) (i : Nat) (x : a.denote)
    (kk : Array a.denote → Code Op SOp (KC Op) Tp.denote α) (h : i < v.size) :
    denote (Code.pop .aset (.cons v (.cons i (.cons x .nil))) kk) = denote (kk (v.set i x h)) :=
  sc_pop .aset (.cons v (.cons i (.cons x .nil))) kk (by exact dif_pos h)

/-- **Upcast `array → vec n`**, valid by the source's length proof `h : arr.size = n`. -/
theorem sc_arrToVec {α a : Tp} {n : Nat} (arr : Array a.denote)
    (kk : Vector a.denote n → Code Op SOp (KC Op) Tp.denote α) (h : arr.size = n) :
    denote (Code.pop .arrToVec (.cons arr .nil) kk) = denote (kk ⟨arr, h⟩) :=
  sc_pop .arrToVec (.cons arr .nil) kk (by exact dif_pos h)

/-- **Upcast `nat → fin n`**, valid by the source's bound proof `h : m < n`. -/
theorem sc_natToFin {α : Tp} {n : Nat} (m : Nat)
    (kk : Fin n → Code Op SOp (KC Op) Tp.denote α) (h : m < n) :
    denote (Code.pop .natToFin (.cons m .nil) kk) = denote (kk ⟨m, h⟩) :=
  sc_pop .natToFin (.cons m .nil) kk (by exact dif_pos h)

/-- **Strict select** — total (`POp.denote` is always `some`), so no source proof is needed. -/
theorem sc_select {α a : Tp} (c : Bool) (x y : a.denote)
    (kk : a.denote → Code Op SOp (KC Op) Tp.denote α) :
    denote (Code.pop .select (.cons c (.cons x (.cons y .nil))) kk)
      = denote (kk (bif c then x else y)) :=
  sc_pop .select (.cons c (.cons x (.cons y .nil))) kk rfl

/-! ## Pure `if` bridges — a decidable `ite` equals a strict boolean select -/

/-- A decidable `if` is the `bif` of its `decide` — bridges a source `ite` to the reflected
    `select`'s boolean (whose `Bin.denote` is `decide`-shaped). -/
theorem ite_decide {p : Prop} [Decidable p] {X : Type} (t e : X) :
    (if p then t else e) = bif decide p then t else e := by
  by_cases h : p <;> simp [h]

/-- `Nat` equality: the source's `decide (x = y)` is bridged to the reflected `==` (`Nat.beq`). -/
theorem ite_nat_eq (x y : Nat) {X : Type} (t e : X) :
    (if x = y then t else e) = bif x == y then t else e := by
  cases hb : x == y with
  | true  => rw [cond_true, if_pos (eq_of_beq hb)]
  | false => rw [cond_false, if_neg (ne_of_beq_false hb)]

/-- A `Bool`-coerced `if` (`if b then …` elaborating to `ite (b = true)`) is its own `bif`. -/
theorem ite_bool (b : Bool) {X : Type} (t e : X) :
    (if b = true then t else e) = bif b then t else e := by cases b <;> rfl

/-! ## Bounded folds — the loop node's step, by induction over the index list -/

/-- A pure-bodied `foldComp` is the `ret` of the plain list fold. -/
theorem foldComp_pure {ι X : Type} (body : ι → X → Comp Op X) (f : X → ι → X)
    (hb : ∀ i acc, body i acc = ret (f acc i)) :
    ∀ (is : List ι) (acc : X), foldComp body is acc = ret (is.foldl f acc) := by
  intro is
  induction is with
  | nil => intro acc; rfl
  | cons i is ih => intro acc; simp only [foldComp, List.foldl, hb, bind_ret, ih]

/-- **Bounded fold, pure body** (`Code.fold` vs the source's `Fin.foldl`, in atom position): a pure
    loop body (its denotation is `ret` of the source's step, pointwise — `hb`, the reflected body's
    own equations) makes the loop node's denotation *equal* to the source fold. -/
theorem sc_fold {α a : Tp} {n : Nat} (init : a.denote) (f : a.denote → Fin n → a.denote)
    (body : Fin n → a.denote → Code Op SOp (KC Op) Tp.denote a)
    (kk : a.denote → Code Op SOp (KC Op) Tp.denote α)
    (hb : ∀ i acc, denote (body i acc) = ret (f acc i)) :
    denote (Code.fold init body kk) = denote (kk (Fin.foldl n f init)) := by
  show ITree.bind (foldComp (fun i acc => denote (body i acc)) (List.finRange n) init)
        (fun r => denote (kk r)) = _
  rw [foldComp_pure _ f hb, bind_ret, ← Fin.foldl_eq_foldl_finRange]

/-- `ofFree` of a `List.foldlM` over `Free` is the effect-sequencing `foldComp` (a monad-morphism
    fold, by induction on the index list). -/
theorem ofFree_foldlM {X ι : Type} (f : X → ι → Free Op SOp X) :
    ∀ (is : List ι) (acc : X),
      ofFree (List.foldlM f acc is) = foldComp (fun i a => ofFree (f a i)) is acc := by
  intro is
  induction is with
  | nil => intro acc; rfl
  | cons i is ih =>
      intro acc
      show ofFree (Free.bind (f acc i) (fun a => List.foldlM f a is)) = _
      rw [ofFree_bind]
      exact congrArg _ (funext fun a => ih a)

/-- A pure-bodied `vgenComp` is the `ret` of `Vector.ofFn` (induction on the count, one
    `Vector.ofFn_succ` per step). -/
theorem vgenComp_pure {X : Type} :
    ∀ (n : Nat) (body : Fin n → Comp Op X) (f : Fin n → X),
      (∀ i, body i = ret (f i)) → vgenComp n body = ret (Vector.ofFn f) := by
  intro n
  induction n with
  | zero => intro body f _; rfl
  | succ n ih =>
      intro body f hb
      show ITree.bind (vgenComp n fun i => body i.castSucc) _ = _
      rw [ih _ (fun i => f i.castSucc) (fun i => hb i.castSucc), bind_ret, hb (Fin.last n),
          bind_ret, Vector.ofFn_succ]
      rfl

/-- **Bounded generator, pure body** (`Code.vgen` vs the source's `Vector.ofFn`, in atom position):
    the lanes' own equations (`hb`) make the generator node's denotation *equal* to the source
    vector. -/
theorem sc_vgen {α a : Tp} {n : Nat} (f : Fin n → a.denote)
    (body : Fin n → Code Op SOp (KC Op) Tp.denote a)
    (kk : Vector a.denote n → Code Op SOp (KC Op) Tp.denote α)
    (hb : ∀ i, denote (body i) = ret (f i)) :
    denote (Code.vgen body kk) = denote (kk (Vector.ofFn f)) := by
  show ITree.bind (vgenComp n (fun i => denote (body i))) (fun r => denote (kk r)) = _
  rw [vgenComp_pure n _ f hb, bind_ret]

/-- **Bounded fold, any body** (`Code.fold` vs the source's `Fin.foldlM`, in walk position — the
    loop construct is body-agnostic): each reflected body block `ofFree`-adequate pointwise (`hb`,
    the blocks' own `walkTop` equations) gives the node's (★) step against the monadic fold. -/
theorem sc_foldM {α a : Tp} {n : Nat} (init : a.denote)
    (f : a.denote → Fin n → Free Op SOp a.denote)
    (body : Fin n → a.denote → Code Op SOp (KC Op) Tp.denote a)
    (K' : a.denote → Code Op SOp (KC Op) Tp.denote α)
    (hb : ∀ i acc, denote (body i acc) = ofFree (f acc i)) :
    denote (Code.fold init body K')
      = ITree.bind (ofFree (Fin.foldlM n f init)) (fun r => denote (K' r)) := by
  show ITree.bind (foldComp (fun i acc => denote (body i acc)) (List.finRange n) init)
        (fun r => denote (K' r)) = _
  rw [show (fun i acc => denote (body i acc)) = (fun i acc => ofFree (f acc i)) from
        funext fun i => funext fun acc => hb i acc,
      Fin.foldlM_eq_foldlM_finRange, ofFree_foldlM]

/-! ## Node steps of the invariant (★) -/

/-- A `pure a` reflected via its continuation: `Kf a`, un-bound by `bind_ret`. -/
theorem sc_pure {X : Type} {α : Tp} (a : X) (C : Comp Op α.denote) (Kf : X → Comp Op α.denote)
    (hC : C = Kf a) : C = ITree.bind (ofFree (@Free.pure Op SOp X a)) Kf := by
  rw [show (ofFree (@Free.pure Op SOp X a) : Comp Op X) = ret a from rfl, ITree.bind_ret]; exact hC

/-- An effect `op`: `vis`-congruence, its continuation given by the IH. -/
theorem sc_op {I R α : Tp} {X : Type} (o : Op I.denote R.denote) (i : I.denote)
    (c : R.denote → Free Op SOp X) (kbody : R.denote → Code Op SOp (KC Op) Tp.denote α)
    (Kf : X → Comp Op α.denote)
    (ih : ∀ r, denote (kbody r) = ITree.bind (ofFree (c r)) Kf) :
    denote (Code.op o i kbody) = ITree.bind (ofFree (Free.op o i c)) Kf := by
  show vis (Effect.mk o i) (fun r => denote (kbody r)) = ITree.bind (ofFree (Free.op o i c)) Kf
  rw [show ofFree (Free.op o i c) = vis (Effect.mk o i) (fun r => ofFree (c r)) from rfl, bind_vis]
  exact congrArg _ (funext ih)

/-- A `ITree.bind x f`: the walk's fused form `C` matched to the source's `ITree.bind`-`ITree.bind`, via
    `ofFree_bind` + associativity. -/
theorem sc_bind {X Y : Type} {α : Tp} (x : Free Op SOp Y) (f : Y → Free Op SOp X)
    (Kf : X → Comp Op α.denote) (C : Comp Op α.denote)
    (hC : C = ITree.bind (ofFree x) (fun r => ITree.bind (ofFree (f r)) Kf)) :
    C = ITree.bind (ofFree (Free.bind x f)) Kf := by
  rw [hC, ofFree_bind, bind_assoc]

/-- A boolean branch: `ITree.bind` distributes over `cond`, each arm given by its IH. -/
theorem sc_cond {X : Type} {α : Tp} (c : Bool) (t e : Free Op SOp X)
    (T E : Code Op SOp (KC Op) Tp.denote α) (Kf : X → Comp Op α.denote)
    (iht : denote T = ITree.bind (ofFree t) Kf) (ihe : denote E = ITree.bind (ofFree e) Kf) :
    denote (Code.ite c T E) = ITree.bind (ofFree (cond c t e)) Kf := by
  show cond c (denote T) (denote E) = ITree.bind (ofFree (cond c t e)) Kf
  rw [ofFree_cond, bind_cond, iht, ihe]

/-- A scoped block `hop s b cont`: the block runs inline (`hB : denote B = ofFree b`), the tail by
    the IH; assembled by associativity. -/
theorem sc_scope {β α : Tp} {X : Type} (s : SOp β.denote) (b : Free Op SOp β.denote)
    (cont : β.denote → Free Op SOp X) (B : Code Op SOp (KC Op) Tp.denote β)
    (K' : β.denote → Code Op SOp (KC Op) Tp.denote α) (Kf : X → Comp Op α.denote)
    (hB : denote B = ofFree b)
    (ih : ∀ x, denote (K' x) = ITree.bind (ofFree (cont x)) Kf) :
    denote (Code.scope s B K') = ITree.bind (ofFree (Free.hop s b cont)) Kf := by
  show ITree.bind (denote B) (fun x => denote (K' x)) = ITree.bind (ofFree (Free.hop s b cont)) Kf
  rw [show ofFree (Free.hop s b cont) = ITree.bind (ofFree b) (fun x => ofFree (cont x)) from rfl,
      bind_assoc, hB]
  exact congrArg _ (funext ih)

/-- A call to a helper subroutine: the subroutine's denotation `cf args` is equal to the source's
    `ofFree` by the helper's own (★)-proof (`hcf`); the continuation passes through `ITree.bind`. -/
theorem sc_call {as : List Tp} {b α : Tp}
    (cf : HList Tp.denote as → Comp Op b.denote) (args : HList Tp.denote as)
    (K' : b.denote → Code Op SOp (KC Op) Tp.denote α) (m : Comp Op b.denote) (hcf : cf args = m) :
    denote (Code.call cf args K') = ITree.bind m (fun r => denote (K' r)) := by
  show ITree.bind (cf args) (fun r => denote (K' r)) = ITree.bind m (fun r => denote (K' r))
  rw [hcf]

/-- A call to a **pure** helper (spilled as a `def_` to keep definitions folded): its subroutine
    returns (`hcf : cf args = ret v`, the helper's own memoized equation), so the call node steps
    straight to its continuation at the value. -/
theorem sc_callPure {as : List Tp} {b α : Tp}
    (cf : HList Tp.denote as → Comp Op b.denote) (args : HList Tp.denote as) {v : b.denote}
    (kk : b.denote → Code Op SOp (KC Op) Tp.denote α) (hcf : cf args = ret v) :
    denote (Code.call cf args kk) = denote (kk v) := by
  show ITree.bind (cf args) (fun r => denote (kk r)) = denote (kk v)
  rw [hcf, bind_ret]

/-! ## Eutt twins of the (★) steps

A call to a **recursive** helper is only `≈` its source (`mrec` adequacy inserts `tau`s), so from
such a call site upward the invariant weakens to

```
denote C ≈ ITree.bind (ofFree e) Kf          -- (★≈)
```

Each `sc_*E` is the eutt-hypothesis twin of its `sc_*`; a sub-proof still in `Eq`-mode lifts by
`Eutt.of_eq` at the composition site, so programs without recursive helpers keep their
equality proofs untouched. -/

open Freigen.ITree in
/-- `sc_pure`, eutt continuation. -/
theorem sc_pureE {X : Type} {α : Tp} (a : X) (C : Comp Op α.denote) (Kf : X → Comp Op α.denote)
    (hC : Eutt C (Kf a)) : Eutt C (ITree.bind (ofFree (@Free.pure Op SOp X a)) Kf) := by
  rw [show (ofFree (@Free.pure Op SOp X a) : Comp Op X) = ret a from rfl, ITree.bind_ret]
  exact hC

open Freigen.ITree in
/-- `sc_op`, eutt continuation (a `vis`-congruence up to taus). -/
theorem sc_opE {I R α : Tp} {X : Type} (o : Op I.denote R.denote) (i : I.denote)
    (c : R.denote → Free Op SOp X) (kbody : R.denote → Code Op SOp (KC Op) Tp.denote α)
    (Kf : X → Comp Op α.denote)
    (ih : ∀ r, Eutt (denote (kbody r)) (ITree.bind (ofFree (c r)) Kf)) :
    Eutt (denote (Code.op o i kbody)) (ITree.bind (ofFree (Free.op o i c)) Kf) := by
  show Eutt (vis (Effect.mk o i) fun r => denote (kbody r)) _
  rw [show ofFree (Free.op o i c) = vis (Effect.mk o i) (fun r => ofFree (c r)) from rfl, bind_vis]
  exact eutt_vis_cong _ ih

open Freigen.ITree in
/-- `sc_bind`, eutt — taken apart into the walked computation's step and the continuation's
    pointwise steps (the eutt-mode composition can't fuse them by `funext` first). -/
theorem sc_bindE {X Y : Type} {α : Tp} (x : Free Op SOp Y) (f : Y → Free Op SOp X)
    (K1 : Y → Comp Op α.denote) (Kf : X → Comp Op α.denote) (C : Comp Op α.denote)
    (hC : Eutt C (ITree.bind (ofFree x) K1))
    (hK : ∀ r, Eutt (K1 r) (ITree.bind (ofFree (f r)) Kf)) :
    Eutt C (ITree.bind (ofFree (Free.bind x f)) Kf) := by
  rw [ofFree_bind, bind_assoc]
  exact hC.trans (eutt_bind_cong (eutt_refl _) hK)

open Freigen.ITree in
/-- `sc_cond`, eutt arms. -/
theorem sc_condE {X : Type} {α : Tp} (c : Bool) (t e : Free Op SOp X)
    (T E : Code Op SOp (KC Op) Tp.denote α) (Kf : X → Comp Op α.denote)
    (iht : Eutt (denote T) (ITree.bind (ofFree t) Kf))
    (ihe : Eutt (denote E) (ITree.bind (ofFree e) Kf)) :
    Eutt (denote (Code.ite c T E)) (ITree.bind (ofFree (cond c t e)) Kf) := by
  cases c
  · exact ihe
  · exact iht

open Freigen.ITree in
/-- `sc_scope`, eutt block and tail. -/
theorem sc_scopeE {β α : Tp} {X : Type} (s : SOp β.denote) (b : Free Op SOp β.denote)
    (cont : β.denote → Free Op SOp X) (B : Code Op SOp (KC Op) Tp.denote β)
    (K' : β.denote → Code Op SOp (KC Op) Tp.denote α) (Kf : X → Comp Op α.denote)
    (hB : Eutt (denote B) (ofFree b))
    (ih : ∀ x, Eutt (denote (K' x)) (ITree.bind (ofFree (cont x)) Kf)) :
    Eutt (denote (Code.scope s B K')) (ITree.bind (ofFree (Free.hop s b cont)) Kf) := by
  show Eutt (ITree.bind (denote B) fun x => denote (K' x)) _
  rw [show ofFree (Free.hop s b cont) = ITree.bind (ofFree b) (fun x => ofFree (cont x)) from rfl,
      bind_assoc]
  exact eutt_bind_cong hB ih

open Freigen.ITree in
/-- `sc_call`, eutt subroutine (this is the recursive-helper case: `hcf` is `mrec` adequacy). -/
theorem sc_callE {as : List Tp} {b α : Tp}
    (cf : HList Tp.denote as → Comp Op b.denote) (args : HList Tp.denote as)
    (K' : b.denote → Code Op SOp (KC Op) Tp.denote α) (m : Comp Op b.denote)
    (hcf : Eutt (cf args) m) :
    Eutt (denote (Code.call cf args K')) (ITree.bind m (fun r => denote (K' r))) := by
  show Eutt (ITree.bind (cf args) fun r => denote (K' r)) _
  exact eutt_bind_cong hcf (fun _ => eutt_refl _)

open Freigen.ITree in
/-- `sc_callPure`, eutt subroutine — a call to a **pure recursive** helper: its `mrec`
    denotation is `≈ ret v` (adequacy + the totalization bridge), so the call node steps to its
    continuation up to taus. -/
theorem sc_callPureE {as : List Tp} {b α : Tp}
    (cf : HList Tp.denote as → Comp Op b.denote) (args : HList Tp.denote as) {v : b.denote}
    (kk : b.denote → Code Op SOp (KC Op) Tp.denote α) (hcf : Eutt (cf args) (ret v)) :
    Eutt (denote (Code.call cf args kk)) (denote (kk v)) := by
  show Eutt (ITree.bind (cf args) fun r => denote (kk r)) _
  exact (eutt_bind_cong hcf (fun _ => eutt_refl _)).trans (Eutt.of_eq (by rw [bind_ret]))

open Freigen.ITree in
/-- `foldComp` congruence up to taus (pointwise eutt bodies). -/
theorem foldComp_congE {ι X : Type} (b1 b2 : ι → X → Comp Op X)
    (hb : ∀ i acc, Eutt (b1 i acc) (b2 i acc)) :
    ∀ (is : List ι) (acc : X), Eutt (foldComp b1 is acc) (foldComp b2 is acc) := by
  intro is
  induction is with
  | nil => intro acc; exact eutt_refl _
  | cons i is ih => intro acc; exact eutt_bind_cong (hb i acc) (fun acc' => ih acc')

open Freigen.ITree in
/-- `sc_fold`, eutt body lanes. -/
theorem sc_foldE {α a : Tp} {n : Nat} (init : a.denote) (f : a.denote → Fin n → a.denote)
    (body : Fin n → a.denote → Code Op SOp (KC Op) Tp.denote a)
    (kk : a.denote → Code Op SOp (KC Op) Tp.denote α)
    (hb : ∀ i acc, Eutt (denote (body i acc)) (ret (f acc i))) :
    Eutt (denote (Code.fold init body kk)) (denote (kk (Fin.foldl n f init))) := by
  show Eutt (ITree.bind (foldComp (fun i acc => denote (body i acc)) (List.finRange n) init)
        (fun r => denote (kk r))) _
  refine ((eutt_bind_cong
      (foldComp_congE _ (fun i acc => ret (f acc i)) hb (List.finRange n) init)
      (fun _ => eutt_refl _)).trans ?_)
  exact Eutt.of_eq (by rw [foldComp_pure _ f (fun _ _ => rfl), bind_ret,
                           ← Fin.foldl_eq_foldl_finRange])

open Freigen.ITree in
/-- `sc_vgen`, eutt body lanes. -/
theorem sc_vgenE {α a : Tp} {n : Nat} (f : Fin n → a.denote)
    (body : Fin n → Code Op SOp (KC Op) Tp.denote a)
    (kk : Vector a.denote n → Code Op SOp (KC Op) Tp.denote α)
    (hb : ∀ i, Eutt (denote (body i)) (ret (f i))) :
    Eutt (denote (Code.vgen body kk)) (denote (kk (Vector.ofFn f))) := by
  show Eutt (ITree.bind (vgenComp n (fun i => denote (body i))) (fun r => denote (kk r))) _
  have congE : ∀ (m : Nat) (b1 b2 : Fin m → Comp Op a.denote),
      (∀ i, Eutt (b1 i) (b2 i)) → Eutt (vgenComp m b1) (vgenComp m b2) := by
    intro m
    induction m with
    | zero => intro _ _ _; exact eutt_refl _
    | succ m ih =>
        intro b1 b2 h
        exact eutt_bind_cong (ih _ _ (fun i => h i.castSucc))
          (fun v => eutt_bind_cong (h (Fin.last m)) (fun _ => eutt_refl _))
  refine ((eutt_bind_cong (congE n _ (fun i => ret (f i)) hb) (fun _ => eutt_refl _)).trans ?_)
  exact Eutt.of_eq (by rw [vgenComp_pure n _ f (fun _ => rfl), bind_ret])

open Freigen.ITree in
/-- `sc_foldM`, eutt body blocks. -/
theorem sc_foldME {α a : Tp} {n : Nat} (init : a.denote)
    (f : a.denote → Fin n → Free Op SOp a.denote)
    (body : Fin n → a.denote → Code Op SOp (KC Op) Tp.denote a)
    (K' : a.denote → Code Op SOp (KC Op) Tp.denote α)
    (hb : ∀ i acc, Eutt (denote (body i acc)) (ofFree (f acc i))) :
    Eutt (denote (Code.fold init body K'))
      (ITree.bind (ofFree (Fin.foldlM n f init)) (fun r => denote (K' r))) := by
  show Eutt (ITree.bind (foldComp (fun i acc => denote (body i acc)) (List.finRange n) init)
        (fun r => denote (K' r))) _
  rw [Fin.foldlM_eq_foldlM_finRange, ofFree_foldlM]
  exact eutt_bind_cong
    (foldComp_congE _ (fun i acc => ofFree (f acc i)) hb (List.finRange n) init)
    (fun _ => eutt_refl _)

/-! ## Recursion adequacy — `mrec` vs the source, at a decreasing measure -/

section RecAdequacy
open Freigen.ITree
variable {σ ρ : Type}

/-- Run a call-body with the source `e` plugged in at each `call` (external `base` effects relabelled
    back to `Op`; a scoped block's own calls are plugged too). -/
def runSrc (e : σ → Free Op SOp ρ) :
    {γ : Type} → Free (CallOp Op σ ρ) SOp γ → Free Op SOp γ
  | _, .pure a => .pure a
  | _, .op (.base o) i c => .op o i (fun x => runSrc e (c x))
  | _, .op .call i c => Free.bind (e i) (fun v => runSrc e (c v))
  | _, .hop s b c => .hop s (runSrc e b) (fun x => runSrc e (c x))

/-- Every `call` argument in the body has measure `μ` strictly below `bound`. -/
def callsLt (μ : σ → Nat) (bound : Nat) : {γ : Type} → Free (CallOp Op σ ρ) SOp γ → Prop
  | _, .pure _ => True
  | _, .op (.base _) _ c => ∀ x, callsLt μ bound (c x)
  | _, .op .call i c => μ i < bound ∧ ∀ x, callsLt μ bound (c x)
  | _, .hop _ b c => callsLt μ bound b ∧ ∀ x, callsLt μ bound (c x)

/-- **The adequacy step.** Interpreting a call-body is `≈` to running it with the source plugged in,
    given the source is adequate below `bound` and the body only calls below `bound`. -/
theorem adeqBody (body : σ → Comp (CallOp Op σ ρ) ρ) (e : σ → Free Op SOp ρ) (μ : σ → Nat)
    (bound : Nat) (Ho : ∀ k, μ k < bound → mrec body k ≈ ofFree (e k)) :
    ∀ {γ : Type} (t : Free (CallOp Op σ ρ) SOp γ), callsLt μ bound t →
      interp body (ofFree t) ≈ ofFree (runSrc e t) := by
  intro γ t
  induction t with
  | pure a => intro _; simp only [ofFree, runSrc, interp_ret]; exact eutt_refl _
  | op o i c ih =>
      cases o with
      | base o' =>
          intro h
          simp only [ofFree, runSrc, interp_vis_base]
          exact eutt_vis_cong _ (fun x => ih x (h x))
      | call =>
          intro h
          simp only [ofFree, runSrc, interp_vis_call, interp_bind, ofFree_bind]
          refine eutt_tau_left ?_
          exact eutt_bind_cong (Ho i h.1) (fun x => ih x (h.2 x))
  | hop s b c ihb ihc =>
      intro h
      simp only [ofFree, runSrc, interp_bind]
      exact eutt_bind_cong (ihb h.1) (fun x => ihc x (h.2 x))

/-- **`mrec` adequacy (strong-induction shell on the measure)** over `ofFree`: the whole reflected
    recursion is `≈` its source, given each step is adequate using the adequacy of all
    measure-smaller arguments. -/
theorem mrec_adequacy (body : σ → Comp (CallOp Op σ ρ) ρ) (e : σ → Free Op SOp ρ) (μ : σ → Nat)
    (Hstep : ∀ N, (∀ k, μ k < μ N → mrec body k ≈ ofFree (e k)) → mrec body N ≈ ofFree (e N)) :
    ∀ N, mrec body N ≈ ofFree (e N) := by
  suffices H : ∀ n N, μ N ≤ n → mrec body N ≈ ofFree (e N) from fun N => H (μ N) N (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro N hN
      exact Hstep N (fun k hk => absurd (Nat.lt_of_lt_of_le hk hN) (Nat.not_lt_zero _))
  | succ n ih =>
      intro N hN
      exact Hstep N (fun k hk => ih k (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hk hN)))

/-- `adeqBody` with the `runSrc = e` bridge folded in — one step discharged against the source. -/
theorem adeqBody' (body : σ → Comp (CallOp Op σ ρ) ρ) (e : σ → Free Op SOp ρ) (μ : σ → Nat)
    (N : σ) (t : Free (CallOp Op σ ρ) SOp ρ)
    (IH : ∀ k, μ k < μ N → mrec body k ≈ ofFree (e k)) (hcl : callsLt μ (μ N) t)
    (hrun : runSrc e t = e N) :
    interp body (ofFree t) ≈ ofFree (e N) := by
  rw [← hrun]; exact adeqBody body e μ (μ N) IH t hcl

/-- **Generic recursion soundness** — what `reflect%` emits.  Given the reflected call-body
    `body` (a `Code` over the call-extended signature) and the source `f`, provided each call's
    measure is below its argument's (`hcl`) and running the body with `f` plugged in recovers `f`
    (`hrun`), the `mrec` denotation is `≈ ofFree ∘ f`.  Packages `mrec_adequacy` + `adeqBody'`. -/
theorem recSound {σT ρT : Tp} (μ : σT.denote → Nat)
    (body : σT.denote →
      Code (CallOp Op σT.denote ρT.denote) SOp (KC (CallOp Op σT.denote ρT.denote)) Tp.denote ρT)
    (cb : σT.denote → Free (CallOp Op σT.denote ρT.denote) SOp ρT.denote)
    (f : σT.denote → Free Op SOp ρT.denote)
    (hspec : ∀ N, denote (body N) = ofFree (cb N))
    (hrun : ∀ N, runSrc f (cb N) = f N)
    (hcl : ∀ N, callsLt μ (μ N) (cb N)) :
    ∀ N, mrec (fun s => denote (body s)) N ≈ ofFree (f N) := by
  have hbody : (fun s => denote (body s)) = fun s => ofFree (cb s) := funext hspec
  intro N
  rw [hbody]
  refine mrec_adequacy _ f μ ?_ N
  intro M IH
  exact adeqBody' _ _ μ _ _ IH (hcl M) (hrun M)

end RecAdequacy

end Freigen
