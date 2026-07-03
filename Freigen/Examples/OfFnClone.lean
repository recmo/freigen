import Freigen.Reflect.Basic
import Freigen.Compile
import Freigen.Examples.Recursion

/-! # Recursion-over-`push` example: a `Vector.ofFn` clone reflected structurally

`MyVector.ofFn` is implemented **exactly** like core's `Vector.ofFn` — via an `Array.ofFn` twin
whose worker `go` is a structural `0`/`succ` recursion over `Array.push`, carrying an `i ≤ n`
hypothesis.  Because it is *not named* `Vector.ofFn`, the reflector's `vgen` arm does not fire:
instead the recursion itself reflects — `go` spills as a **`rec_` definition over `push`**
(the hypothesis erased, `f`/`n`/`α` monomorphised, the state `(acc, i)` tupled, adequacy by
the source's own functional induction + `adeqPlug`), and the size proof carries into the
`arr-to-vec` upcast. -/

namespace Freigen

/-- Exactly core's `Array.ofFn` implementation, under a different name. -/
def MyArray.ofFn {α : Type} {n : Nat} (f : Fin n → α) : Array α :=
  go (Array.emptyWithCapacity n) n (Nat.le_refl n) where
  go (acc : Array α) : (i : Nat) → i ≤ n → Array α
  | i + 1, h =>
     have w : n - i - 1 < n :=
       Nat.lt_of_lt_of_le (Nat.sub_one_lt (Nat.sub_ne_zero_iff_lt.mpr h)) (Nat.sub_le n i)
     go (acc.push (f ⟨n - i - 1, w⟩)) i (Nat.le_of_succ_le h)
  | 0, _ => acc

theorem MyArray.size_go {α : Type} {n : Nat} (f : Fin n → α) :
    ∀ (i : Nat) (acc : Array α) (h : i ≤ n), (MyArray.ofFn.go f acc i h).size = acc.size + i := by
  intro i
  induction i with
  | zero => intro acc h; rfl
  | succ m ih => intro acc h; rw [MyArray.ofFn.go, ih]; simp; omega

theorem MyArray.size_ofFn {α : Type} {n : Nat} (f : Fin n → α) : (MyArray.ofFn f).size = n := by
  simp [MyArray.ofFn, MyArray.size_go]

/-- Exactly core's `Vector.ofFn` implementation, under a different name. -/
def MyVector.ofFn {α : Type} {n : Nat} (f : Fin n → α) : Vector α n :=
  ⟨MyArray.ofFn f, MyArray.size_ofFn f⟩

/-- Index (by a program input) into a vector built by the clone: the whole chain reflects
    structurally — **every source definition survives, fully generic**: `go` as a recursive
    definition over `push` whose state *carries the function* (`f` is invariant through the
    recursion, so the adequacy is relativized to embedded states), the wrappers as `def`s with
    real `(fn …)` parameters, and `main` building the lambda once. -/
def useOfFn (i : Fin 4) : Free NoOp NoScope Nat :=
  pure ((MyVector.ofFn (fun j => j.val * 2))[i])

reflect_def useOfFnC := useOfFn
/-- info: Freigen.useOfFnC_sound (i : Fin 4) :
  ITree.Eutt (denoteProg (useOfFnC (KC NoOp) (Tp.denote NoOp)) (HList.cons i HList.nil)) (ofFree (useOfFn i)) -/
#guard_msgs (whitespace := lax) in
#check useOfFnC_sound

/-- info: (program
  (rec go ((x0 (prod (fn (fin 4) nat) (prod (array nat) nat)))) (array nat)
    (block
      (let v1 (fn (fin 4) nat) (fst x0))
      (let v2 (prod (array nat) nat) (snd x0))
      (let v3 nat (snd v2))
      (let v4 nat (lit 0))
      (let v5 bool (eq v3 v4))
      (if v5
        (block
          (let v6 (prod (array nat) nat) (snd x0))
          (let v7 (array nat) (fst v6))
          (ret v7))
        (block
          (let v8 (prod (array nat) nat) (snd x0))
          (let v9 (array nat) (fst v8))
          (let v10 nat (lit 4))
          (let v11 (prod (array nat) nat) (snd x0))
          (let v12 nat (snd v11))
          (let v13 nat (lit 1))
          (let v14 nat (sub v12 v13))
          (let v15 nat (sub v10 v14))
          (let v16 nat (lit 1))
          (let v17 nat (sub v15 v16))
          (let v18 (fin 4) (nat-to-fin 4 v17))
          (let v19 nat (app v1 v18))
          (let v20 (array nat) (push v9 v19))
          (let v21 (prod (array nat) nat) (snd x0))
          (let v22 nat (snd v21))
          (let v23 nat (lit 1))
          (let v24 nat (sub v22 v23))
          (let v25 (prod (array nat) nat) (pair v20 v24))
          (let v26 (prod (fn (fin 4) nat) (prod (array nat) nat)) (pair v1 v25))
          (let v27 (array nat) (self v26))
          (ret v27)))))
  (def ofFn ((x28 (fn (fin 4) nat))) (array nat)
    (block
      (let v29 (array nat) (lit ()))
      (let v30 nat (lit 4))
      (let v31 (prod (array nat) nat) (pair v29 v30))
      (let v32 (prod (fn (fin 4) nat) (prod (array nat) nat)) (pair x28 v31))
      (let v33 (array nat) (call go v32))
      (ret v33)))
  (def ofFn_2 ((x34 (fn (fin 4) nat))) (vec nat 4)
    (block
      (let v35 (array nat) (call ofFn x34))
      (let v36 (vec nat 4) (arr-to-vec 4 v35))
      (ret v36)))
  (main ((x37 (fin 4))) nat
    (block
      (let v42 (fn (fin 4) nat) (lam ((x38 (fin 4)))
        (block
          (let v39 nat (fin-val x38))
          (let v40 nat (lit 2))
          (let v41 nat (mul v39 v40))
          (ret v41))))
      (let v43 (vec nat 4) (call ofFn_2 v42))
      (let v44 nat (fin-val x37))
      (let v45 nat (vget v43 v44))
      (ret v45))))
-/
#guard_msgs (whitespace := lax) in #eval IO.println (serialize useOfFnC)

/-- The worker called directly with an **input-dependent accumulator** — non-closed state
    threading through the recursion. -/
def pushLoop (x : Nat) : Free NoOp NoScope (Array Nat) :=
  pure (MyArray.ofFn.go (n := 4) (fun j => j.val * 2) #[x] 4 (Nat.le_refl 4))

reflect_def pushLoopC := pushLoop
/-- info: Freigen.pushLoopC_sound (x : ℕ) :
  ITree.Eutt (denoteProg (pushLoopC (KC NoOp) (Tp.denote NoOp)) (HList.cons x HList.nil)) (ofFree (pushLoop x)) -/
#guard_msgs (whitespace := lax) in
#check pushLoopC_sound

/-- info: (program
  (rec go ((x0 (prod (fn (fin 4) nat) (prod (array nat) nat)))) (array nat)
    (block
      (let v1 (fn (fin 4) nat) (fst x0))
      (let v2 (prod (array nat) nat) (snd x0))
      (let v3 nat (snd v2))
      (let v4 nat (lit 0))
      (let v5 bool (eq v3 v4))
      (if v5
        (block
          (let v6 (prod (array nat) nat) (snd x0))
          (let v7 (array nat) (fst v6))
          (ret v7))
        (block
          (let v8 (prod (array nat) nat) (snd x0))
          (let v9 (array nat) (fst v8))
          (let v10 nat (lit 4))
          (let v11 (prod (array nat) nat) (snd x0))
          (let v12 nat (snd v11))
          (let v13 nat (lit 1))
          (let v14 nat (sub v12 v13))
          (let v15 nat (sub v10 v14))
          (let v16 nat (lit 1))
          (let v17 nat (sub v15 v16))
          (let v18 (fin 4) (nat-to-fin 4 v17))
          (let v19 nat (app v1 v18))
          (let v20 (array nat) (push v9 v19))
          (let v21 (prod (array nat) nat) (snd x0))
          (let v22 nat (snd v21))
          (let v23 nat (lit 1))
          (let v24 nat (sub v22 v23))
          (let v25 (prod (array nat) nat) (pair v20 v24))
          (let v26 (prod (fn (fin 4) nat) (prod (array nat) nat)) (pair v1 v25))
          (let v27 (array nat) (self v26))
          (ret v27)))))
  (main ((x28 nat)) (array nat)
    (block
      (let v33 (fn (fin 4) nat) (lam ((x29 (fin 4)))
        (block
          (let v30 nat (fin-val x29))
          (let v31 nat (lit 2))
          (let v32 nat (mul v30 v31))
          (ret v32))))
      (let v34 (array nat) (arr x28))
      (let v35 nat (lit 4))
      (let v36 (prod (array nat) nat) (pair v34 v35))
      (let v37 (prod (fn (fin 4) nat) (prod (array nat) nat)) (pair v33 v36))
      (let v38 (array nat) (call go v37))
      (ret v38))))
-/
#guard_msgs (whitespace := lax) in #eval IO.println (serialize pushLoopC)

end Freigen
