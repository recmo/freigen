import Freigen.Reflect.Basic
import Freigen.Compile
import Freigen.Examples.Recursion

/-! # First-class functions: `(fn …)` parameters, `lam` values, `app` — nothing inlined

`applyTwice` takes a function and applies it twice.  It reflects as a `def` with a **real
`(fn nat nat)` parameter** — the function value is *passed*, not baked in — and its body uses
the `app` node.  `main` builds the argument as a `lam` value (an ordinary code block, here
**capturing the program input `x`**) and passes it.  One `applyTwice` serves every caller.

A recursion whose state carries a function **invariantly** (every self-call passes it
unchanged) is also first-class — see `OfFnClone`.  Only a recursion that *modifies* its
function state falls back to specialization (demotion). -/

namespace Freigen

/-- A higher-order helper: apply `f` twice. -/
def applyTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

/-- Pass a *capturing* lambda to `twice`: `fun y => y + x` closes over the program input. -/
def useTwice (x : Nat) : Free NoOp NoScope Nat :=
  pure (applyTwice (fun y => y + x) x)

reflect_def useTwiceC := useTwice
/-- info: Freigen.useTwiceC_sound (x : ℕ) :
  ITree.Eutt (denoteProg (useTwiceC (KC NoOp) (Tp.denote NoOp)) (HList.cons x HList.nil)) (ofFree (useTwice x)) -/
#guard_msgs (whitespace := lax) in
#check useTwiceC_sound

/-- info: (program
  (def applyTwice ((x0 (fn nat nat)) (x1 nat)) nat
    (block
      (let v2 nat (app x0 x1))
      (let v3 nat (app x0 v2))
      (ret v3)))
  (main ((x4 nat)) nat
    (block
      (let v7 (fn nat nat) (lam ((x5 nat))
        (block
          (let v6 nat (add x5 x4))
          (ret v6))))
      (let v8 nat (call applyTwice v7 x4))
      (ret v8))))
-/
#guard_msgs (whitespace := lax) in #eval IO.println (serialize useTwiceC)

end Freigen
