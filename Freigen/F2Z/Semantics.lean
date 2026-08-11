import Freigen.F2Z.Defs
import Freigen.Wheels

namespace Freigen.F2Z.Semantics

structure R1C F [Semiring F] where
  a : LC F
  b : LC F
  c : LC F
deriving Repr

def R1C.satisfies [Semiring F] [DecidableEq F]
    (r1c : R1C F) (witness : Nat → F): Prop :=
  r1c.a.eval witness * r1c.b.eval witness = r1c.c.eval witness

def R1C.satisfies' [Semiring F] [DecidableEq F]
    (r1c : R1C F) (witness : Nat → F): Bool :=
  r1c.a.eval witness * r1c.b.eval witness = r1c.c.eval witness

structure CS where
  r1cs : Array (R1C ℤ)
  m : Array (LC Bool)
deriving Inhabited, Repr

def CS.satisfies' (cs : CS) (witness : Nat → Bool): Bool :=
  let mw := cs.m.map (Bool.toInt ∘ LC.eval witness)
  let mw := fun i => mw[i]!
  cs.r1cs.all (fun r1c => r1c.satisfies' mw)

def CS.satisfies (cs : CS) (witness : Nat → Bool): Prop :=
  let mw := cs.m.map (Bool.toInt ∘ LC.eval witness)
  let mw := fun i => mw[i]!
  ∀ r1c ∈ cs.r1cs, r1c.satisfies mw

def CS.intWitness (cs : CS) (witness : Nat → Bool) : Nat → ℤ :=
  let mw := cs.m.map (Bool.toInt ∘ LC.eval witness)
  fun i => mw[i]!

structure CSBuilder where
  result : CS
  nextWit : Nat
deriving Inhabited

namespace CSBuilder

def fresh : StateM CSBuilder (LC Bool) := do
  modifyGet (fun s => ({ s.nextWit }, { s with nextWit := s.nextWit + 1 }))

def NoMonad : Type → Type u := fun _ => PUnit

instance : Monad NoMonad where
  pure _ := PUnit.unit
  bind _ _ := PUnit.unit

instance : LawfulMonad NoMonad := LawfulMonad.mk' _
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)


abbrev RunnerM : Eff.Scope → Type → Type
| .constraint => StateM CSBuilder
| .hint => NoMonad

instance : (γ : Eff.Scope) → Monad (RunnerM γ)
| .constraint => inferInstance
| .hint       => inferInstance

def run' {α} (circ : Circuit α): StateM CSBuilder α := do
  Free.interp (M := RunnerM) (@fun
    | .constraint, .assertR1C a b c, _ => do
        let cs ← get
        let r1c : R1C ℤ := { a := a, b := b, c := c }
        set { cs with result := { cs.result with r1cs := cs.result.r1cs.push r1c } }
    | .constraint, .f2z a, _ => do
        let cs ← get
        let nextIdx := cs.result.m.size
        let lc : LC ℤ := { nextIdx }
        set { cs with result := { cs.result with m := cs.result.m.push a } }
        pure lc
    | .constraint, .hint _ _ _, _ => Vector.ofFnM (fun _ => CSBuilder.fresh)
    | .hint, .fail _, _ => ()
  ) circ

def run {α} (circ : Circuit α) (initial : CSBuilder): (α × CS) :=
  let (a, csb) := StateT.run (run' circ) initial
  (a, csb.result)

end CSBuilder

namespace Witgen

structure State where
  bools : Array Bool := #[]
deriving Inhabited

def evalArgs : {argTps : List Eff.WitnessSide} →
    HList Eff.WitnessSide.denoteW argTps →
    HList Eff.WitnessSide.denoteF argTps
  | [], .nil => .nil
  | .z :: _, .cons x xs =>
      .cons x.constant (evalArgs xs)
  | .f₂ :: _, .cons x xs =>
      .cons x.constant (evalArgs xs)

abbrev RunnerM : Eff.Scope → Type → Type
| .constraint => StateM State
| .hint => Option

instance : (γ : Eff.Scope) → Monad (RunnerM γ)
| .constraint => inferInstance
| .hint       => inferInstance

def run' (circ : Vector (LC Bool) n → Circuit Unit) (inp : Vector Bool n) : StateM State Unit := do
  set ({ bools := inp.toArray } : State)
  let inputValues := inp.map LC.ofConst
  Free.interp (M := RunnerM) (@fun
    | .constraint, .assertR1C _ _ _, _ => pure ()
    | .constraint, .f2z a, _ =>
      pure (LC.ofConst a.constant.toInt)
    | .constraint, .hint _ args n, blkO => do
      let r := (blkO () (evalArgs args)).getD (Vector.replicate n false)
      let s ← get
      set { s with bools := s.bools ++ r.toArray }
      pure (r.map LC.ofConst)
    | .hint, .fail _, _ => none
  ) (circ inputValues)

def run (circ : Vector (LC Bool) n → Circuit Unit) (inp : Vector Bool n) : Array Bool :=
  (StateT.run (run' circ inp) default).2.bools

end Witgen

namespace Ex

def fromBits {n : Nat} (r : Vector (LC Bool) n) :
    Circuit (LC ℤ) :=
  match n with
  | 0 => pure 0
  | _ + 1 => do
    let i ← fromBits r.tail
    let b ← f2z r.head
    pure (b + 2 • i)

def toBits (n : ℕ) (i : LC ℤ) :
    Circuit (Vector (LC Bool) n) := do
  let r ← hint (argTps := [.z]) h![i] fun h![i] =>
    let rawBits := i.toNat.bits.toArray
    let padded := rawBits.take n ++ Array.replicate (n - rawBits.size) false
    let paddedVec : Vector Bool n := ⟨padded, by grind⟩
    paddedVec
  let sum ← fromBits r
  assertR1C sum 1 i
  return r

def smol (inp : Vector (LC Bool) 8) : Circuit Unit := do
  let a ← fromBits inp
  let _ ← toBits 4 a

end Ex

-- open scoped CSBuilder in
-- def smolCS := CSBuilder.run Ex.smol

def smolWit := Witgen.run Ex.smol (#v[true, false, true, true, false, false, false, false])

-- #eval CS.satisfies' smolCS (fun i => smolWit[i]!)

end Freigen.F2Z.Semantics
