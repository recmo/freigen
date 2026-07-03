import Batteries.Data.Fin.Fold
import Freigen.Ast.Basic
import Freigen.Free
import Freigen.ITree.Eutt

/-!
# Compositional soundness lemmas for the reflector

The reflector builds its `≈`-soundness proof **structurally**, mirroring the source term: as it
walks a `Free` program it emits, at every node, an equation

```
denote C = ITree.bind (ofFree e) Kf          -- (★)
```

(`Kf` = the denotation of the reflected continuation), assembled from the equation of the
sub-terms by the congruence lemma for that node.  This is what lets a proof-erased
`vget`/`vset`/`aget`/`aset` carry the *actual* in-bounds proof from the source (`sc_vget … (h :
i < n)` is literally `dif_pos h`) — no `simp`, no decidability, no reachability of a hypothesis:
the proof term mirrors the term.

Each `sc_*` is one node's step of (★); every other `Code` node's step is definitional (`rfl`).
The whole per-program proof is a tree of these applied to each other, `Eutt.of_eq`-lifted at the
very top.  Past a recursive helper call the invariant weakens to `≈` (the `sc_*E` twins).

The `sc_op` step carries the `TpF.denote_tp` casts of the DSL injection — they reduce to `rfl`
at every concrete operation, so instantiated steps keep their definitional character.
-/

namespace Freigen
open Freigen.ITree

variable {X : TpF → TpF → Type} {SOp : Type → Type}

/-- `ITree.bind` distributes over a boolean branch. -/
theorem bind_cond {ε : Type} {br : ε → Type} {α β : Type} (c : Bool) (a b : CompE ε br α)
    (k : α → CompE ε br β) :
    ITree.bind (cond c a b) k = cond c (ITree.bind a k) (ITree.bind b k) := by cases c <;> rfl

/-! ## Pure-atom steps: the reflected partial-op nodes carry the source's proof -/

/-- Generic **partial-op step**: when the op's denotation succeeds, the `pop` node steps to its
    continuation — the erased `fail` branch is closed by `h`. -/
theorem sc_pop {α b : Tp} {as : List Tp} (o : POp as b) (args : HList (Tp.denote X) as)
    {v : Tp.denote X b} (kk : Tp.denote X b → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (h : POp.denote o args = some v) :
    denote (Code.pop o args kk) = denote (kk v) := by
  simp only [denote, denoteI]
  rw [h]

/-- **Vector get**, in bounds by the *source's* proof `h`. -/
theorem sc_vget {α a : Tp} {n : Nat} (v : Vector (Tp.denote X a) n) (i : Nat)
    (kk : Tp.denote X a → Code X (OpT X) SOp (KC X) (Tp.denote X) α) (h : i < n) :
    denote (Code.pop .vget (.cons v (.cons i .nil)) kk) = denote (kk (v[i]'h)) :=
  sc_pop .vget (.cons v (.cons i .nil)) kk (by exact dif_pos h)

/-- **Vector set**, in bounds by the source's proof `h`. -/
theorem sc_vset {α a : Tp} {n : Nat} (v : Vector (Tp.denote X a) n) (i : Nat) (x : Tp.denote X a)
    (kk : Vector (Tp.denote X a) n → Code X (OpT X) SOp (KC X) (Tp.denote X) α) (h : i < n) :
    denote (Code.pop .vset (.cons v (.cons i (.cons x .nil))) kk) = denote (kk (v.set i x h)) :=
  sc_pop .vset (.cons v (.cons i (.cons x .nil))) kk (by exact dif_pos h)

/-- **Array get**, in bounds by the source's proof `h`. -/
theorem sc_aget {α a : Tp} (v : Array (Tp.denote X a)) (i : Nat)
    (kk : Tp.denote X a → Code X (OpT X) SOp (KC X) (Tp.denote X) α) (h : i < v.size) :
    denote (Code.pop .aget (.cons v (.cons i .nil)) kk) = denote (kk (v[i]'h)) :=
  sc_pop .aget (.cons v (.cons i .nil)) kk (by exact dif_pos h)

/-- **Array set**, in bounds by the source's proof `h`. -/
theorem sc_aset {α a : Tp} (v : Array (Tp.denote X a)) (i : Nat) (x : Tp.denote X a)
    (kk : Array (Tp.denote X a) → Code X (OpT X) SOp (KC X) (Tp.denote X) α) (h : i < v.size) :
    denote (Code.pop .aset (.cons v (.cons i (.cons x .nil))) kk) = denote (kk (v.set i x h)) :=
  sc_pop .aset (.cons v (.cons i (.cons x .nil))) kk (by exact dif_pos h)

/-- **Upcast `array → vec n`**, valid by the source's length proof `h : arr.size = n`. -/
theorem sc_arrToVec {α a : Tp} {n : Nat} (arr : Array (Tp.denote X a))
    (kk : Vector (Tp.denote X a) n → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (h : arr.size = n) :
    denote (Code.pop .arrToVec (.cons arr .nil) kk) = denote (kk ⟨arr, h⟩) :=
  sc_pop .arrToVec (.cons arr .nil) kk (by exact dif_pos h)

/-- **Upcast `nat → fin n`**, valid by the source's bound proof `h : m < n`. -/
theorem sc_natToFin {α : Tp} {n : Nat} (m : Nat)
    (kk : Fin n → Code X (OpT X) SOp (KC X) (Tp.denote X) α) (h : m < n) :
    denote (Code.pop .natToFin (.cons m .nil) kk) = denote (kk ⟨m, h⟩) :=
  sc_pop .natToFin (.cons m .nil) kk (by exact dif_pos h)

/-- **Strict select** — total (`POp.denote` is always `some`), so no source proof is needed. -/
theorem sc_select {α a : Tp} (c : Bool) (x y : Tp.denote X a)
    (kk : Tp.denote X a → Code X (OpT X) SOp (KC X) (Tp.denote X) α) :
    denote (Code.pop .select (.cons c (.cons x (.cons y .nil))) kk)
      = denote (kk (bif c then x else y)) :=
  sc_pop .select (.cons c (.cons x (.cons y .nil))) kk rfl

/-! ## Pure `if` bridges — a decidable `ite` equals a strict boolean select -/

/-- A decidable `if` is the `bif` of its `decide` — bridges a source `ite` to the reflected
    `select`'s boolean (whose `Bin.denote` is `decide`-shaped). -/
theorem ite_decide {p : Prop} [Decidable p] {A : Type} (t e : A) :
    (if p then t else e) = bif decide p then t else e := by
  by_cases h : p <;> simp [h]

/-- `Nat` equality: the source's `decide (x = y)` is bridged to the reflected `==` (`Nat.beq`). -/
theorem ite_nat_eq (x y : Nat) {A : Type} (t e : A) :
    (if x = y then t else e) = bif x == y then t else e := by
  cases hb : x == y with
  | true  => rw [cond_true, if_pos (eq_of_beq hb)]
  | false => rw [cond_false, if_neg (ne_of_beq_false hb)]

/-- A `Bool`-coerced `if` (`if b then …` elaborating to `ite (b = true)`) is its own `bif`. -/
theorem ite_bool (b : Bool) {A : Type} (t e : A) :
    (if b = true then t else e) = bif b then t else e := by cases b <;> rfl

/-! ## Bounded folds — the loop node's step, by induction over the index list -/

/-- A pure-bodied `foldComp` is the `ret` of the plain list fold. -/
theorem foldComp_pure {ε : Type} {br : ε → Type} {ι A : Type} (body : ι → A → CompE ε br A)
    (f : A → ι → A) (hb : ∀ i acc, body i acc = ret (f acc i)) :
    ∀ (is : List ι) (acc : A), foldComp body is acc = ret (is.foldl f acc) := by
  intro is
  induction is with
  | nil => intro acc; rfl
  | cons i is ih => intro acc; simp only [foldComp, List.foldl, hb, bind_ret, ih]

/-- **Bounded fold, pure body** (`Code.fold` vs the source's `Fin.foldl`, in atom position). -/
theorem sc_fold {α a : Tp} {n : Nat} (init : Tp.denote X a)
    (f : Tp.denote X a → Fin n → Tp.denote X a)
    (body : Fin n → Tp.denote X a → Code X (OpT X) SOp (KC X) (Tp.denote X) a)
    (kk : Tp.denote X a → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (hb : ∀ i acc, denote (body i acc) = ret (f acc i)) :
    denote (Code.fold init body kk) = denote (kk (Fin.foldl n f init)) := by
  show ITree.bind (foldComp (fun i acc => denoteI (injD X) (body i acc)) (List.finRange n) init)
        (fun r => denoteI (injD X) (kk r)) = _
  rw [foldComp_pure _ f hb, bind_ret, ← Fin.foldl_eq_foldl_finRange]

/-- `ofFree` of a `List.foldlM` over `Free` is the effect-sequencing `foldComp` (a monad-morphism
    fold, by induction on the index list). -/
theorem ofFree_foldlM {ε : Type} {br : ε → Type} {A ι : Type}
    (f : A → ι → FreeE ε br SOp A) :
    ∀ (is : List ι) (acc : A),
      ofFree (List.foldlM f acc is) = foldComp (fun i a => ofFree (f a i)) is acc := by
  intro is
  induction is with
  | nil => intro acc; rfl
  | cons i is ih =>
      intro acc
      show ofFree (FreeE.bind (f acc i) (fun a => List.foldlM f a is)) = _
      rw [ofFree_bind]
      exact congrArg _ (funext fun a => ih a)

/-- A pure-bodied `vgenComp` is the `ret` of `Vector.ofFn` (induction on the count, one
    `Vector.ofFn_succ` per step). -/
theorem vgenComp_pure {ε : Type} {br : ε → Type} {A : Type} :
    ∀ (n : Nat) (body : Fin n → CompE ε br A) (f : Fin n → A),
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

/-- **Bounded generator, pure body** (`Code.vgen` vs the source's `Vector.ofFn`). -/
theorem sc_vgen {α a : Tp} {n : Nat} (f : Fin n → Tp.denote X a)
    (body : Fin n → Code X (OpT X) SOp (KC X) (Tp.denote X) a)
    (kk : Vector (Tp.denote X a) n → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (hb : ∀ i, denote (body i) = ret (f i)) :
    denote (Code.vgen body kk) = denote (kk (Vector.ofFn f)) := by
  show ITree.bind (vgenComp n (fun i => denoteI (injD X) (body i)))
        (fun r => denoteI (injD X) (kk r)) = _
  rw [vgenComp_pure n _ f hb, bind_ret]

/-- **Bounded fold, any body** (`Code.fold` vs the source's `Fin.foldlM`, in walk position). -/
theorem sc_foldM {α a : Tp} {n : Nat} (init : Tp.denote X a)
    (f : Tp.denote X a → Fin n → Free X SOp (Tp.denote X a))
    (body : Fin n → Tp.denote X a → Code X (OpT X) SOp (KC X) (Tp.denote X) a)
    (K' : Tp.denote X a → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (hb : ∀ i acc, denote (body i acc) = ofFree (f acc i)) :
    denote (Code.fold init body K')
      = ITree.bind (ofFree (Fin.foldlM n f init)) (fun r => denote (K' r)) := by
  show ITree.bind (foldComp (fun i acc => denoteI (injD X) (body i acc)) (List.finRange n) init)
        (fun r => denoteI (injD X) (K' r)) = _
  rw [show (fun i acc => denoteI (injD X) (body i acc)) = (fun i acc => ofFree (f acc i)) from
        funext fun i => funext fun acc => hb i acc,
      Fin.foldlM_eq_foldlM_finRange, ofFree_foldlM]

/-! ## Node steps of the invariant (★) -/

/-- A `pure a` reflected via its continuation: `Kf a`, un-bound by `bind_ret`. -/
theorem sc_pure {Y : Type} {α : Tp} (a : Y) (C : Comp X (Tp.denote X α))
    (Kf : Y → Comp X (Tp.denote X α)) (hC : C = Kf a) :
    C = ITree.bind (ofFree (.pure a : Free X SOp Y)) Kf := by
  rw [show (ofFree (.pure a : Free X SOp Y) : Comp X Y) = ret a from rfl, ITree.bind_ret]
  exact hC

/-- An effect `op`: `vis`-congruence, its continuation given by the IH.  The `denote_tp` casts
    are the DSL injection's — they reduce to `rfl` at every concrete operation. -/
theorem sc_op {I R : TpF} {α : Tp} {Y : Type} (o : X I R) (i : Tp.denote X I.tp)
    (c : R.denote → Free X SOp Y)
    (kbody : Tp.denote X R.tp → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (Kf : Y → Comp X (Tp.denote X α))
    (ih : ∀ r : R.denote, denote (kbody (cast (TpF.denote_tp X R).symm r))
            = ITree.bind (ofFree (c r)) Kf) :
    denote (Code.op (OpT.mk o) i kbody)
      = ITree.bind (ofFree (FreeE.op (Effect.mk o (cast (TpF.denote_tp X I) i)) c)) Kf := by
  show vis (Effect.mk o (cast (TpF.denote_tp X I) i))
        (fun r => denoteI (injD X) (kbody (cast (TpF.denote_tp X R).symm r))) = _
  rw [show ofFree (FreeE.op (Effect.mk o (cast (TpF.denote_tp X I) i)) c)
        = vis (Effect.mk o (cast (TpF.denote_tp X I) i)) (fun r => ofFree (c r)) from rfl,
      bind_vis]
  exact congrArg _ (funext ih)

/-- A `bind x f`: the walk's fused form `C` matched to the source's bind-bind, via `ofFree_bind`
    + associativity. -/
theorem sc_bind {Y Z : Type} {α : Tp} (x : Free X SOp Z) (f : Z → Free X SOp Y)
    (Kf : Y → Comp X (Tp.denote X α)) (C : Comp X (Tp.denote X α))
    (hC : C = ITree.bind (ofFree x) (fun r => ITree.bind (ofFree (f r)) Kf)) :
    C = ITree.bind (ofFree (FreeE.bind x f)) Kf := by
  rw [hC, ofFree_bind, bind_assoc]

/-- A boolean branch: `ITree.bind` distributes over `cond`, each arm given by its IH. -/
theorem sc_cond {Y : Type} {α : Tp} (c : Bool) (t e : Free X SOp Y)
    (T E : Code X (OpT X) SOp (KC X) (Tp.denote X) α) (Kf : Y → Comp X (Tp.denote X α))
    (iht : denote T = ITree.bind (ofFree t) Kf) (ihe : denote E = ITree.bind (ofFree e) Kf) :
    denote (Code.ite c T E) = ITree.bind (ofFree (cond c t e)) Kf := by
  show cond c (denote T) (denote E) = ITree.bind (ofFree (cond c t e)) Kf
  rw [ofFree_cond, bind_cond, iht, ihe]

/-- A scoped block `hop s b cont`: the block runs inline (`hB : denote B = ofFree b`), the tail
    by the IH; assembled by associativity. -/
theorem sc_scope {β α : Tp} {Y : Type} (s : SOp (Tp.denote X β))
    (b : Free X SOp (Tp.denote X β)) (cont : Tp.denote X β → Free X SOp Y)
    (B : Code X (OpT X) SOp (KC X) (Tp.denote X) β)
    (K' : Tp.denote X β → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (Kf : Y → Comp X (Tp.denote X α))
    (hB : denote B = ofFree b)
    (ih : ∀ x, denote (K' x) = ITree.bind (ofFree (cont x)) Kf) :
    denote (Code.scope s B K') = ITree.bind (ofFree (FreeE.hop s b cont)) Kf := by
  show ITree.bind (denote B) (fun x => denoteI (injD X) (K' x))
        = ITree.bind (ofFree (FreeE.hop s b cont)) Kf
  rw [show ofFree (FreeE.hop s b cont)
        = ITree.bind (ofFree b) (fun x => ofFree (cont x)) from rfl,
      bind_assoc, hB]
  exact congrArg _ (funext ih)

/-- A call to a helper subroutine: the subroutine's denotation `cf args` is equal to the
    source's `ofFree` by the helper's own (★)-proof (`hcf`); the continuation passes through
    `ITree.bind`. -/
theorem sc_call {as : List Tp} {b α : Tp}
    (cf : KC X as b) (args : HList (Tp.denote X) as)
    (K' : Tp.denote X b → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (m : Comp X (Tp.denote X b)) (hcf : cf args = m) :
    denote (Code.call cf args K') = ITree.bind m (fun r => denote (K' r)) := by
  show ITree.bind (cf args) (fun r => denoteI (injD X) (K' r)) = _
  rw [hcf]

/-- A call to a **pure** helper (spilled as a `def_` to keep definitions folded): its subroutine
    returns (`hcf : cf args = ret v`, the helper's own memoized equation), so the call node
    steps straight to its continuation at the value. -/
theorem sc_callPure {as : List Tp} {b α : Tp}
    (cf : KC X as b) (args : HList (Tp.denote X) as) {v : Tp.denote X b}
    (kk : Tp.denote X b → Code X (OpT X) SOp (KC X) (Tp.denote X) α) (hcf : cf args = ret v) :
    denote (Code.call cf args kk) = denote (kk v) := by
  show ITree.bind (cf args) (fun r => denoteI (injD X) (kk r)) = denoteI (injD X) (kk v)
  rw [hcf, bind_ret]

/-- A **function value**: the suspended body's own (pointwise) equations identify the Kleisli
    arrow with the source's embedding (`ofFree ∘ f` — a *pure* source lambda embeds with
    `f := fun x => .pure (fsrc x)`).  The body proofs must be equalities: a value baked into a
    continuation admits no up-to-tau congruence. -/
theorem sc_lam {a b α : Tp} (f : Tp.denote X a → Free X SOp (Tp.denote X b))
    (body : Tp.denote X a → Code X (OpT X) SOp (KC X) (Tp.denote X) b)
    (kk : Tp.denote X (.fn a b) → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (hb : ∀ x, denote (body x) = ofFree (f x)) :
    denote (Code.lam body kk) = denote (kk (fun x => ofFree (f x))) := by
  show denoteI (injD X) (kk (fun x => denoteI (injD X) (body x))) = _
  rw [show (fun x => denoteI (injD X) (body x)) = (fun x => ofFree (f x)) from funext hb]

/-- **Apply**, walk position: the arrow's computation is the source's by `hf`; the continuation
    passes through `ITree.bind` (mirrors `sc_call`). -/
theorem sc_appM {a b α : Tp} (f : Tp.denote X (.fn a b)) (x : Tp.denote X a)
    (K' : Tp.denote X b → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (m : Comp X (Tp.denote X b)) (hf : f x = m) :
    denote (Code.app f x K') = ITree.bind m (fun r => denote (K' r)) := by
  show ITree.bind (f x) (fun r => denoteI (injD X) (K' r)) = _
  rw [hf]

/-- **Apply**, atom position (a pure source application): the arrow returns (`hf : f x = ret v`
    — for an embedded pure lambda this is `rfl`), so the node steps to its continuation
    (mirrors `sc_callPure`). -/
theorem sc_app {a b α : Tp} (f : Tp.denote X (.fn a b)) (x : Tp.denote X a) {v : Tp.denote X b}
    (kk : Tp.denote X b → Code X (OpT X) SOp (KC X) (Tp.denote X) α) (hf : f x = ret v) :
    denote (Code.app f x kk) = denote (kk v) := by
  show ITree.bind (f x) (fun r => denoteI (injD X) (kk r)) = denoteI (injD X) (kk v)
  rw [hf, bind_ret]

/-! ## Eutt twins of the (★) steps — for proofs that passed through a recursive helper call -/

open Freigen.ITree in
/-- `sc_pure`, eutt continuation. -/
theorem sc_pureE {Y : Type} {α : Tp} (a : Y) (C : Comp X (Tp.denote X α))
    (Kf : Y → Comp X (Tp.denote X α)) (hC : Eutt C (Kf a)) :
    Eutt C (ITree.bind (ofFree (.pure a : Free X SOp Y)) Kf) := by
  rw [show (ofFree (.pure a : Free X SOp Y) : Comp X Y) = ret a from rfl, ITree.bind_ret]
  exact hC

open Freigen.ITree in
/-- `sc_op`, eutt continuation (a `vis`-congruence up to taus). -/
theorem sc_opE {I R : TpF} {α : Tp} {Y : Type} (o : X I R) (i : Tp.denote X I.tp)
    (c : R.denote → Free X SOp Y)
    (kbody : Tp.denote X R.tp → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (Kf : Y → Comp X (Tp.denote X α))
    (ih : ∀ r : R.denote, Eutt (denote (kbody (cast (TpF.denote_tp X R).symm r)))
            (ITree.bind (ofFree (c r)) Kf)) :
    Eutt (denote (Code.op (OpT.mk o) i kbody))
      (ITree.bind (ofFree (FreeE.op (Effect.mk o (cast (TpF.denote_tp X I) i)) c)) Kf) := by
  show Eutt (vis (Effect.mk o (cast (TpF.denote_tp X I) i))
        (fun r => denoteI (injD X) (kbody (cast (TpF.denote_tp X R).symm r)))) _
  rw [show ofFree (FreeE.op (Effect.mk o (cast (TpF.denote_tp X I) i)) c)
        = vis (Effect.mk o (cast (TpF.denote_tp X I) i)) (fun r => ofFree (c r)) from rfl,
      bind_vis]
  exact eutt_vis_cong _ ih

open Freigen.ITree in
/-- `sc_bind`, eutt — taken apart into the walked computation's step and the continuation's
    pointwise steps. -/
theorem sc_bindE {Y Z : Type} {α : Tp} (x : Free X SOp Z) (f : Z → Free X SOp Y)
    (K1 : Z → Comp X (Tp.denote X α)) (Kf : Y → Comp X (Tp.denote X α))
    (C : Comp X (Tp.denote X α))
    (hC : Eutt C (ITree.bind (ofFree x) K1))
    (hK : ∀ r, Eutt (K1 r) (ITree.bind (ofFree (f r)) Kf)) :
    Eutt C (ITree.bind (ofFree (FreeE.bind x f)) Kf) := by
  rw [ofFree_bind, bind_assoc]
  exact hC.trans (eutt_bind_cong (eutt_refl _) hK)

open Freigen.ITree in
/-- `sc_cond`, eutt arms. -/
theorem sc_condE {Y : Type} {α : Tp} (c : Bool) (t e : Free X SOp Y)
    (T E : Code X (OpT X) SOp (KC X) (Tp.denote X) α) (Kf : Y → Comp X (Tp.denote X α))
    (iht : Eutt (denote T) (ITree.bind (ofFree t) Kf))
    (ihe : Eutt (denote E) (ITree.bind (ofFree e) Kf)) :
    Eutt (denote (Code.ite c T E)) (ITree.bind (ofFree (cond c t e)) Kf) := by
  cases c
  · exact ihe
  · exact iht

open Freigen.ITree in
/-- `sc_scope`, eutt block and tail. -/
theorem sc_scopeE {β α : Tp} {Y : Type} (s : SOp (Tp.denote X β))
    (b : Free X SOp (Tp.denote X β)) (cont : Tp.denote X β → Free X SOp Y)
    (B : Code X (OpT X) SOp (KC X) (Tp.denote X) β)
    (K' : Tp.denote X β → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (Kf : Y → Comp X (Tp.denote X α))
    (hB : Eutt (denote B) (ofFree b))
    (ih : ∀ x, Eutt (denote (K' x)) (ITree.bind (ofFree (cont x)) Kf)) :
    Eutt (denote (Code.scope s B K')) (ITree.bind (ofFree (FreeE.hop s b cont)) Kf) := by
  show Eutt (ITree.bind (denote B) fun x => denoteI (injD X) (K' x)) _
  rw [show ofFree (FreeE.hop s b cont)
        = ITree.bind (ofFree b) (fun x => ofFree (cont x)) from rfl,
      bind_assoc]
  exact eutt_bind_cong hB ih

open Freigen.ITree in
/-- `sc_call`, eutt subroutine (the recursive-helper case: `hcf` is `mrec` adequacy). -/
theorem sc_callE {as : List Tp} {b α : Tp}
    (cf : KC X as b) (args : HList (Tp.denote X) as)
    (K' : Tp.denote X b → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (m : Comp X (Tp.denote X b)) (hcf : Eutt (cf args) m) :
    Eutt (denote (Code.call cf args K')) (ITree.bind m (fun r => denote (K' r))) := by
  show Eutt (ITree.bind (cf args) fun r => denoteI (injD X) (K' r)) _
  exact eutt_bind_cong hcf (fun _ => eutt_refl _)

open Freigen.ITree in
/-- `sc_callPure`, eutt subroutine — a call to a **pure recursive** helper. -/
theorem sc_callPureE {as : List Tp} {b α : Tp}
    (cf : KC X as b) (args : HList (Tp.denote X) as) {v : Tp.denote X b}
    (kk : Tp.denote X b → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (hcf : Eutt (cf args) (ret v)) :
    Eutt (denote (Code.call cf args kk)) (denote (kk v)) := by
  show Eutt (ITree.bind (cf args) fun r => denoteI (injD X) (kk r)) _
  exact (eutt_bind_cong hcf (fun _ => eutt_refl _)).trans (Eutt.of_eq (by rw [bind_ret]))

open Freigen.ITree in
/-- `sc_appM`, eutt arrow. -/
theorem sc_appME {a b α : Tp} (f : Tp.denote X (.fn a b)) (x : Tp.denote X a)
    (K' : Tp.denote X b → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (m : Comp X (Tp.denote X b)) (hf : Eutt (f x) m) :
    Eutt (denote (Code.app f x K')) (ITree.bind m (fun r => denote (K' r))) := by
  show Eutt (ITree.bind (f x) fun r => denoteI (injD X) (K' r)) _
  exact eutt_bind_cong hf (fun _ => eutt_refl _)

open Freigen.ITree in
/-- `sc_app`, eutt arrow. -/
theorem sc_appE {a b α : Tp} (f : Tp.denote X (.fn a b)) (x : Tp.denote X a) {v : Tp.denote X b}
    (kk : Tp.denote X b → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (hf : Eutt (f x) (ret v)) :
    Eutt (denote (Code.app f x kk)) (denote (kk v)) := by
  show Eutt (ITree.bind (f x) fun r => denoteI (injD X) (kk r)) _
  exact (eutt_bind_cong hf (fun _ => eutt_refl _)).trans (Eutt.of_eq (by rw [bind_ret]))

open Freigen.ITree in
/-- `foldComp` congruence up to taus (pointwise eutt bodies). -/
theorem foldComp_congE {ε : Type} {br : ε → Type} {ι A : Type} (b1 b2 : ι → A → CompE ε br A)
    (hb : ∀ i acc, Eutt (b1 i acc) (b2 i acc)) :
    ∀ (is : List ι) (acc : A), Eutt (foldComp b1 is acc) (foldComp b2 is acc) := by
  intro is
  induction is with
  | nil => intro acc; exact eutt_refl _
  | cons i is ih => intro acc; exact eutt_bind_cong (hb i acc) (fun acc' => ih acc')

open Freigen.ITree in
/-- `sc_fold`, eutt body lanes. -/
theorem sc_foldE {α a : Tp} {n : Nat} (init : Tp.denote X a)
    (f : Tp.denote X a → Fin n → Tp.denote X a)
    (body : Fin n → Tp.denote X a → Code X (OpT X) SOp (KC X) (Tp.denote X) a)
    (kk : Tp.denote X a → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (hb : ∀ i acc, Eutt (denote (body i acc)) (ret (f acc i))) :
    Eutt (denote (Code.fold init body kk)) (denote (kk (Fin.foldl n f init))) := by
  show Eutt (ITree.bind (foldComp (fun i acc => denoteI (injD X) (body i acc))
        (List.finRange n) init) (fun r => denoteI (injD X) (kk r))) _
  refine ((eutt_bind_cong
      (foldComp_congE _ (fun i acc => ret (f acc i)) hb (List.finRange n) init)
      (fun _ => eutt_refl _)).trans ?_)
  exact Eutt.of_eq (by rw [foldComp_pure _ f (fun _ _ => rfl), bind_ret,
                           ← Fin.foldl_eq_foldl_finRange])

open Freigen.ITree in
/-- `sc_vgen`, eutt body lanes. -/
theorem sc_vgenE {α a : Tp} {n : Nat} (f : Fin n → Tp.denote X a)
    (body : Fin n → Code X (OpT X) SOp (KC X) (Tp.denote X) a)
    (kk : Vector (Tp.denote X a) n → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (hb : ∀ i, Eutt (denote (body i)) (ret (f i))) :
    Eutt (denote (Code.vgen body kk)) (denote (kk (Vector.ofFn f))) := by
  show Eutt (ITree.bind (vgenComp n (fun i => denoteI (injD X) (body i)))
        (fun r => denoteI (injD X) (kk r))) _
  have congE : ∀ (m : Nat) (b1 b2 : Fin m → Comp X (Tp.denote X a)),
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
theorem sc_foldME {α a : Tp} {n : Nat} (init : Tp.denote X a)
    (f : Tp.denote X a → Fin n → Free X SOp (Tp.denote X a))
    (body : Fin n → Tp.denote X a → Code X (OpT X) SOp (KC X) (Tp.denote X) a)
    (K' : Tp.denote X a → Code X (OpT X) SOp (KC X) (Tp.denote X) α)
    (hb : ∀ i acc, Eutt (denote (body i acc)) (ofFree (f acc i))) :
    Eutt (denote (Code.fold init body K'))
      (ITree.bind (ofFree (Fin.foldlM n f init)) (fun r => denote (K' r))) := by
  show Eutt (ITree.bind (foldComp (fun i acc => denoteI (injD X) (body i acc))
        (List.finRange n) init) (fun r => denoteI (injD X) (K' r))) _
  rw [Fin.foldlM_eq_foldlM_finRange, ofFree_foldlM]
  exact eutt_bind_cong
    (foldComp_congE _ (fun i acc => ofFree (f acc i)) hb (List.finRange n) init)
    (fun _ => eutt_refl _)

/-! ## Recursion adequacy — `mrec` vs the source, at a decreasing measure -/

section RecAdequacy
open Freigen.ITree
variable {σ ρ : Type}

/-- A **leaf-wise plugging derivation**: the lifted body `t` (call events at its leaves) is
    related to the source tree `u` obtained by replacing every call event with a source
    computation *already known adequate at that state*.  No measure and no invariant appear:
    the per-leaf adequacy facts arrive from the source function's own induction principle
    (`fun_induction`), which quantifies them exactly at the recursive-call states — proofs
    included. -/
inductive Plug (body : σ → CompC X σ ρ ρ) :
    {γ : Type} → FreeC X σ ρ SOp γ → Free X SOp γ → Prop
  | pure {γ : Type} (a : γ) : Plug body (FreeE.pure a) (FreeE.pure a)
  | op {γ : Type} (ev : Effect X) {c : _ → FreeC X σ ρ SOp γ} {c' : _ → Free X SOp γ} :
      (∀ x, Plug body (c x) (c' x)) → Plug body (FreeE.op (.inl ev) c) (FreeE.op ev c')
  | call {γ : Type} (s : σ) {m : Free X SOp ρ} {c : ρ → FreeC X σ ρ SOp γ}
      {c' : ρ → Free X SOp γ} :
      ITree.mrec body s ≈ ofFree m → (∀ x, Plug body (c x) (c' x)) →
      Plug body (FreeE.op (.inr s) c) (FreeE.bind m c')
  | hop {γ β : Type} (so : SOp β) {b : FreeC X σ ρ SOp β} {b' : Free X SOp β}
      {c : β → FreeC X σ ρ SOp γ} {c' : β → Free X SOp γ} :
      Plug body b b' → (∀ x, Plug body (c x) (c' x)) → Plug body (FreeE.hop so b c) (FreeE.hop so b' c')

/-- A **tail** call: the call's value is returned directly. -/
theorem Plug.callTail {body : σ → CompC X σ ρ ρ} (s : σ) {m : Free X SOp ρ}
    (hm : ITree.mrec body s ≈ ofFree m) : Plug body (FreeE.op (.inr s) FreeE.pure) m :=
  Free.bind_pure m ▸ Plug.call s hm (fun x => Plug.pure x)

/-- **The plugging adequacy step**: interpreting a lifted body is `≈` to any leaf-wise
    plugging of it. -/
theorem adeqPlug {body : σ → CompC X σ ρ ρ} {γ : Type}
    {t : FreeC X σ ρ SOp γ} {u : Free X SOp γ} (h : Plug body t u) :
    interp body (ofFree t) ≈ ofFree u := by
  induction h with
  | pure a => simp only [ofFree, interp_ret]; exact eutt_refl _
  | op ev _ ih =>
      simp only [ofFree, interp_vis_base]
      exact eutt_vis_cong _ ih
  | call s hm _ ih =>
      simp only [ofFree, interp_vis_call, interp_bind, ofFree_bind]
      exact eutt_tau_left (eutt_bind_cong hm ih)
  | hop so _ _ ihb ihc =>
      simp only [ofFree, interp_bind]
      exact eutt_bind_cong ihb ihc

end RecAdequacy

/-! ## Rec-body steps — the (★) lemma set at the call-extended vocabulary

A `rec_` body's code lives over `CallOp (OpT X) σT ρT` and denotes by `denoteC` into the
call-extended events; its walk-built specification (`hspec`) is stated against `ofFree` of the
`FreeC` intermediary.  These are the mirrors of the base `sc_*` set (no eutt twins — a rec
body's proof is always an equality; no `lam`/`app` — v1 mono-bakes function arguments of
recursive helpers). -/

section RecBody
variable {σT ρT : Tp}

/-- Partial-op step (rec body). -/
theorem sc_popC {α b : Tp} {as : List Tp} (o : POp as b) (args : HList (Tp.denote X) as)
    {v : Tp.denote X b}
    (kk : Tp.denote X b → Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α)
    (h : POp.denote o args = some v) :
    denoteC ((injD X).withCall σT ρT) (Code.pop o args kk)
      = denoteC ((injD X).withCall σT ρT) (kk v) := by
  simp only [denoteC]
  rw [h]

theorem sc_vgetC {α a : Tp} {n : Nat} (v : Vector (Tp.denote X a) n) (i : Nat)
    (kk : Tp.denote X a → Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α)
    (h : i < n) :
    denoteC ((injD X).withCall σT ρT) (Code.pop .vget (.cons v (.cons i .nil)) kk)
      = denoteC ((injD X).withCall σT ρT) (kk (v[i]'h)) :=
  sc_popC .vget (.cons v (.cons i .nil)) kk (by exact dif_pos h)

theorem sc_vsetC {α a : Tp} {n : Nat} (v : Vector (Tp.denote X a) n) (i : Nat)
    (x : Tp.denote X a)
    (kk : Vector (Tp.denote X a) n →
      Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α) (h : i < n) :
    denoteC ((injD X).withCall σT ρT) (Code.pop .vset (.cons v (.cons i (.cons x .nil))) kk)
      = denoteC ((injD X).withCall σT ρT) (kk (v.set i x h)) :=
  sc_popC .vset (.cons v (.cons i (.cons x .nil))) kk (by exact dif_pos h)

theorem sc_agetC {α a : Tp} (v : Array (Tp.denote X a)) (i : Nat)
    (kk : Tp.denote X a → Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α)
    (h : i < v.size) :
    denoteC ((injD X).withCall σT ρT) (Code.pop .aget (.cons v (.cons i .nil)) kk)
      = denoteC ((injD X).withCall σT ρT) (kk (v[i]'h)) :=
  sc_popC .aget (.cons v (.cons i .nil)) kk (by exact dif_pos h)

theorem sc_asetC {α a : Tp} (v : Array (Tp.denote X a)) (i : Nat) (x : Tp.denote X a)
    (kk : Array (Tp.denote X a) →
      Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α) (h : i < v.size) :
    denoteC ((injD X).withCall σT ρT) (Code.pop .aset (.cons v (.cons i (.cons x .nil))) kk)
      = denoteC ((injD X).withCall σT ρT) (kk (v.set i x h)) :=
  sc_popC .aset (.cons v (.cons i (.cons x .nil))) kk (by exact dif_pos h)

theorem sc_arrToVecC {α a : Tp} {n : Nat} (arr : Array (Tp.denote X a))
    (kk : Vector (Tp.denote X a) n →
      Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α) (h : arr.size = n) :
    denoteC ((injD X).withCall σT ρT) (Code.pop .arrToVec (.cons arr .nil) kk)
      = denoteC ((injD X).withCall σT ρT) (kk ⟨arr, h⟩) :=
  sc_popC .arrToVec (.cons arr .nil) kk (by exact dif_pos h)

theorem sc_natToFinC {α : Tp} {n : Nat} (m : Nat)
    (kk : Fin n → Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α)
    (h : m < n) :
    denoteC ((injD X).withCall σT ρT) (Code.pop .natToFin (.cons m .nil) kk)
      = denoteC ((injD X).withCall σT ρT) (kk ⟨m, h⟩) :=
  sc_popC .natToFin (.cons m .nil) kk (by exact dif_pos h)

theorem sc_selectC {α a : Tp} (c : Bool) (x y : Tp.denote X a)
    (kk : Tp.denote X a → Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α) :
    denoteC ((injD X).withCall σT ρT) (Code.pop .select (.cons c (.cons x (.cons y .nil))) kk)
      = denoteC ((injD X).withCall σT ρT) (kk (bif c then x else y)) :=
  sc_popC .select (.cons c (.cons x (.cons y .nil))) kk rfl

/-- `pure` (rec body). -/
theorem sc_pureC {Y : Type} {α : Tp} (a : Y)
    (C : CompC X (Tp.denote X σT) (Tp.denote X ρT) (Tp.denote X α))
    (Kf : Y → CompC X (Tp.denote X σT) (Tp.denote X ρT) (Tp.denote X α)) (hC : C = Kf a) :
    C = ITree.bind
      (ofFree (.pure a : FreeC X (Tp.denote X σT) (Tp.denote X ρT) SOp Y)) Kf := by
  rw [show (ofFree (.pure a : FreeC X (Tp.denote X σT) (Tp.denote X ρT) SOp Y)
        : CompC X (Tp.denote X σT) (Tp.denote X ρT) Y) = ret a from rfl, ITree.bind_ret]
  exact hC

/-- `bind` (rec body). -/
theorem sc_bindC {Y Z : Type} {α : Tp}
    (x : FreeC X (Tp.denote X σT) (Tp.denote X ρT) SOp Z)
    (f : Z → FreeC X (Tp.denote X σT) (Tp.denote X ρT) SOp Y)
    (Kf : Y → CompC X (Tp.denote X σT) (Tp.denote X ρT) (Tp.denote X α))
    (C : CompC X (Tp.denote X σT) (Tp.denote X ρT) (Tp.denote X α))
    (hC : C = ITree.bind (ofFree x) (fun r => ITree.bind (ofFree (f r)) Kf)) :
    C = ITree.bind (ofFree (FreeE.bind x f)) Kf := by
  rw [hC, ofFree_bind, bind_assoc]

/-- Boolean branch (rec body). -/
theorem sc_condC {Y : Type} {α : Tp} (c : Bool)
    (t e : FreeC X (Tp.denote X σT) (Tp.denote X ρT) SOp Y)
    (T E : Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α)
    (Kf : Y → CompC X (Tp.denote X σT) (Tp.denote X ρT) (Tp.denote X α))
    (iht : denoteC ((injD X).withCall σT ρT) T = ITree.bind (ofFree t) Kf)
    (ihe : denoteC ((injD X).withCall σT ρT) E = ITree.bind (ofFree e) Kf) :
    denoteC ((injD X).withCall σT ρT) (Code.ite c T E)
      = ITree.bind (ofFree (cond c t e)) Kf := by
  show cond c (denoteC ((injD X).withCall σT ρT) T) (denoteC ((injD X).withCall σT ρT) E) = _
  rw [ofFree_cond, bind_cond, iht, ihe]

/-- A scoped block (rec body). -/
theorem sc_scopeC {β α : Tp} {Y : Type} (s : SOp (Tp.denote X β))
    (b : FreeC X (Tp.denote X σT) (Tp.denote X ρT) SOp (Tp.denote X β))
    (cont : Tp.denote X β → FreeC X (Tp.denote X σT) (Tp.denote X ρT) SOp Y)
    (B : Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) β)
    (K' : Tp.denote X β → Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α)
    (Kf : Y → CompC X (Tp.denote X σT) (Tp.denote X ρT) (Tp.denote X α))
    (hB : denoteC ((injD X).withCall σT ρT) B = ofFree b)
    (ih : ∀ x, denoteC ((injD X).withCall σT ρT) (K' x) = ITree.bind (ofFree (cont x)) Kf) :
    denoteC ((injD X).withCall σT ρT) (Code.scope s B K')
      = ITree.bind (ofFree (FreeE.hop s b cont)) Kf := by
  show ITree.bind (denoteC ((injD X).withCall σT ρT) B)
        (fun x => denoteC ((injD X).withCall σT ρT) (K' x)) = _
  rw [show ofFree (FreeE.hop s b cont)
        = ITree.bind (ofFree b) (fun x => ofFree (cont x)) from rfl,
      bind_assoc, hB]
  exact congrArg _ (funext ih)

/-- A **base effect** inside a rec body: emits `Sum.inl` of the packaged event. -/
theorem sc_opBaseC {I R : TpF} {α : Tp} {Y : Type} (o : X I R) (i : Tp.denote X I.tp)
    (c : R.denote → FreeC X (Tp.denote X σT) (Tp.denote X ρT) SOp Y)
    (kbody : Tp.denote X R.tp →
      Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α)
    (Kf : Y → CompC X (Tp.denote X σT) (Tp.denote X ρT) (Tp.denote X α))
    (ih : ∀ r : R.denote,
        denoteC ((injD X).withCall σT ρT) (kbody (cast (TpF.denote_tp X R).symm r))
          = ITree.bind (ofFree (c r)) Kf) :
    denoteC ((injD X).withCall σT ρT) (Code.op (CallOp.base (OpT.mk o)) i kbody)
      = ITree.bind
          (ofFree (FreeE.op (Sum.inl (Effect.mk o (cast (TpF.denote_tp X I) i))) c)) Kf := by
  show vis (Sum.inl (Effect.mk o (cast (TpF.denote_tp X I) i)))
        (fun r => denoteC ((injD X).withCall σT ρT)
          (kbody (cast (TpF.denote_tp X R).symm r))) = _
  rw [show ofFree (FreeE.op (Sum.inl (Effect.mk o (cast (TpF.denote_tp X I) i))) c)
        = vis (Sum.inl (Effect.mk o (cast (TpF.denote_tp X I) i)))
            (fun r => ofFree (c r)) from rfl,
      bind_vis]
  exact congrArg _ (funext ih)

/-- The **self-call** inside a rec body: emits `Sum.inr` of the state. -/
theorem sc_opCallC {α : Tp} {Y : Type} (i : Tp.denote X σT)
    (c : Tp.denote X ρT → FreeC X (Tp.denote X σT) (Tp.denote X ρT) SOp Y)
    (kbody : Tp.denote X ρT →
      Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α)
    (Kf : Y → CompC X (Tp.denote X σT) (Tp.denote X ρT) (Tp.denote X α))
    (ih : ∀ r : Tp.denote X ρT,
        denoteC ((injD X).withCall σT ρT) (kbody r) = ITree.bind (ofFree (c r)) Kf) :
    denoteC ((injD X).withCall σT ρT) (Code.op CallOp.call i kbody)
      = ITree.bind (ofFree (FreeE.op (Sum.inr i) c)) Kf := by
  show vis (Sum.inr i) (fun r => denoteC ((injD X).withCall σT ρT) (kbody r)) = _
  rw [show ofFree (FreeE.op (Sum.inr i) c)
        = vis (Sum.inr i) (fun r => ofFree (c r)) from rfl,
      bind_vis]
  exact congrArg _ (funext ih)

/-- **Apply** inside a rec body: the function value (a state projection, tied to an embedded
    pure function by the recursion invariant) returns, so the node steps to its continuation —
    through the `sumL` embedding. -/
theorem sc_appC {a b α : Tp} (f : Tp.denote X (.fn a b)) (x : Tp.denote X a)
    {v : Tp.denote X b}
    (kk : Tp.denote X b → Code X (CallOp (OpT X) σT ρT) SOp (KCC X σT ρT) (Tp.denote X) α)
    (hf : f x = ret v) :
    denoteC ((injD X).withCall σT ρT) (Code.app f x kk)
      = denoteC ((injD X).withCall σT ρT) (kk v) := by
  show ITree.bind (sumL (f x)) (fun r => denoteC ((injD X).withCall σT ρT) (kk r)) = _
  rw [hf, sumL_ret, bind_ret]

end RecBody


end Freigen
