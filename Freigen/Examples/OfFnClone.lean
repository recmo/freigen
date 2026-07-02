import Freigen.Reflect.Basic
import Freigen.Compile
import Freigen.Examples.Recursion

/-! # Recursion-over-`push` example: a `Vector.ofFn` clone reflected structurally

`MyVector.ofFn` is implemented **exactly** like core's `Vector.ofFn` — via an `Array.ofFn` twin
whose worker `go` is a structural `0`/`succ` recursion over `Array.push`, carrying an `i ≤ n`
hypothesis.  Because it is *not named* `Vector.ofFn`, the reflector's `vgen` arm does not fire:
instead the recursion itself reflects — `go` spills as a **`rec_` definition over `push`**
(the hypothesis erased, `f`/`n`/`α` monomorphised, the state `(acc, i)` tupled, adequacy by
`recSound` + the totalization bridge), and the size proof carries into the `arr-to-vec` upcast. -/

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

/-- Index (by a program input) into a vector built by the clone: the whole chain —
    `MyVector.ofFn → Vector.mk → arr-to-vec ∘ MyArray.ofFn → go` — reflects structurally, `go`
    spilling as a recursive definition over `push` (never unrolled, never evaluated into a
    literal). -/
def useOfFn (i : Fin 4) : Free NoOp NoScope Nat :=
  pure ((MyVector.ofFn (fun j => j.val * 2))[i])

reflect_def useOfFnC := useOfFn
/-- info: Freigen.useOfFnC_sound (i : Fin 4) :
  ITree.Eutt (denoteProg (useOfFnC (KC NoOp) Tp.denote) (HList.cons i HList.nil)) (ofFree (useOfFn i)) -/
#guard_msgs (whitespace := lax) in
#check useOfFnC_sound

/-- info:
(program
  (rec go ((x0 (prod (array nat) nat))) (array nat)
    (block
      (let v1 nat (snd x0))
      (let v2 nat (lit 0))
      (let v3 bool (eq v1 v2))
      (if v3
        (block
          (let v4 (array nat) (fst x0))
          (ret v4))
        (block
          (let v5 (array nat) (fst x0))
          (let v6 nat (lit 4))
          (let v7 nat (snd x0))
          (let v8 nat (lit 1))
          (let v9 nat (sub v7 v8))
          (let v10 nat (sub v6 v9))
          (let v11 nat (lit 1))
          (let v12 nat (sub v10 v11))
          (let v13 (fin 4) (nat-to-fin 4 v12))
          (let v14 nat (fin-val v13))
          (let v15 nat (lit 2))
          (let v16 nat (mul v14 v15))
          (let v17 (array nat) (push v5 v16))
          (let v18 nat (snd x0))
          (let v19 nat (lit 1))
          (let v20 nat (sub v18 v19))
          (let v21 (prod (array nat) nat) (pair v17 v20))
          (let v22 (array nat) (self v21))
          (ret v22)))))
  (main ((x23 (fin 4))) nat
    (block
      (let v24 (array nat) (lit ()))
      (let v25 nat (lit 4))
      (let v26 (prod (array nat) nat) (pair v24 v25))
      (let v27 (array nat) (call go v26))
      (let v28 (vec nat 4) (arr-to-vec 4 v27))
      (let v29 nat (fin-val x23))
      (let v30 nat (vget v28 v29))
      (ret v30))))
-/
#guard_msgs (whitespace := lax) in #eval IO.println (serialize useOfFnC)

/-- The worker called directly with an **input-dependent accumulator** — non-closed state
    threading through the recursion. -/
def pushLoop (x : Nat) : Free NoOp NoScope (Array Nat) :=
  pure (MyArray.ofFn.go (n := 4) (fun j => j.val * 2) #[x] 4 (Nat.le_refl 4))

reflect_def pushLoopC := pushLoop
/-- info: Freigen.pushLoopC_sound (x : ℕ) :
  ITree.Eutt (denoteProg (pushLoopC (KC NoOp) Tp.denote) (HList.cons x HList.nil)) (ofFree (pushLoop x)) -/
#guard_msgs (whitespace := lax) in
#check pushLoopC_sound

/-- info:
(program
  (rec go ((x0 (prod (array nat) nat))) (array nat)
    (block
      (let v1 nat (snd x0))
      (let v2 nat (lit 0))
      (let v3 bool (eq v1 v2))
      (if v3
        (block
          (let v4 (array nat) (fst x0))
          (ret v4))
        (block
          (let v5 (array nat) (fst x0))
          (let v6 nat (lit 4))
          (let v7 nat (snd x0))
          (let v8 nat (lit 1))
          (let v9 nat (sub v7 v8))
          (let v10 nat (sub v6 v9))
          (let v11 nat (lit 1))
          (let v12 nat (sub v10 v11))
          (let v13 (fin 4) (nat-to-fin 4 v12))
          (let v14 nat (fin-val v13))
          (let v15 nat (lit 2))
          (let v16 nat (mul v14 v15))
          (let v17 (array nat) (push v5 v16))
          (let v18 nat (snd x0))
          (let v19 nat (lit 1))
          (let v20 nat (sub v18 v19))
          (let v21 (prod (array nat) nat) (pair v17 v20))
          (let v22 (array nat) (self v21))
          (ret v22)))))
  (main ((x23 nat)) (array nat)
    (block
      (let v24 (array nat) (arr x23))
      (let v25 nat (lit 4))
      (let v26 (prod (array nat) nat) (pair v24 v25))
      (let v27 (array nat) (call go v26))
      (ret v27))))
-/
#guard_msgs (whitespace := lax) in #eval IO.println (serialize pushLoopC)

end Freigen
