import Freigen.CompM.Basic
import Freigen.CompM.Examples.Nondet.Defs
import Freigen.CompM.Examples.Nondet.SamePrints
import Freigen.ITree.Basic

namespace Freigen.CompM.Examples.Nondet

def scaryLoop : Nondet Unit := do
  while true do
    let x ← Nondet.rand
    Nondet.print (x*x)

def scaryLoopDet : Nondet Unit := do
  while true do
    let x ← Nondet.rand
    Nondet.print (x - x)

#eval approxWith Int.ofNat scaryLoop 1000
example : approxWith Int.ofNat scaryLoop 20 = [0, 1, 4, 9, 16, 25, 36] := by rfl
example : approxWith Int.ofNat scaryLoopDet 20 = [0, 0, 0, 0, 0, 0, 0] := by rfl


def Deterministic {α} (t : Nondet α) : Prop := SamePrints Eq t t

-- theorem scaryLoopDet_deterministic : Deterministic scaryLoopDet := by
--   apply SamePrints.bind
--   · apply SamePrints.loop
--     grind [SamePrints.bind, SamePrints.rand, SamePrints.print, SamePrints.ret]
--   · simp [SamePrints.ret]

theorem scaryLoopDet_deterministic : Deterministic scaryLoopDet := by
  apply SamePrints.bind
  · apply SamePrints.loop_coind (I := Eq) (RR := Eq) rfl
    rintro ⟨⟩ _ rfl
    conv =>
      congr
      · skip
      · skip
      · rw [loop_def]
      · rw [loop_def]
    simp only [↓reduceIte, Int.sub_self, bind_pure_comp, bind_assoc, bind_map_left]
    apply SamePrints.Step.silent
    · apply SamePrints.Silent.rand
    · apply SamePrints.Silent.rand
    intros
    apply SamePrints.Steps.step (SamePrints.Step.print _)
    apply SamePrints.Steps.step
    apply SamePrints.Step.silent
    · apply SamePrints.Silent.tick
    · apply SamePrints.Silent.tick
    intros
    apply SamePrints.Steps.recur
    simp [SamePrints.LoopPair]
  · simp [SamePrints.ret]

def printAllInts : Nondet Unit := do
  let mut curr := 0
  while true do
    Nondet.print curr
    curr := curr + 1

def printAllIntsBy2 : Nondet Unit := do
  let mut curr := 0
  while true do
    Nondet.print curr
    Nondet.print (curr + 1)
    curr := curr + 2

#eval approxWith Int.ofNat printAllInts 20
#eval approxWith Int.ofNat printAllIntsBy2 20

example : SamePrints Eq printAllInts printAllIntsBy2 := by
  apply SamePrints.bind
  · apply SamePrints.loop_coind Eq (RR := Eq) (by simp)
    rintro s _ rfl
    conv =>
      congr
      · skip
      · skip
      · rw [loop_def]
        simp only [↓reduceIte, bind_pure_comp, map_pure, bind_map_left]
        rw [loop_def]
      · rw [loop_def]
    simp only [↓reduceIte, bind_pure_comp, map_pure, bind_map_left, bind_assoc]
    apply SamePrints.Step.print
    apply SamePrints.Steps.step
    apply SamePrints.Step.silentL
    · apply SamePrints.Silent.tick
    intros
    apply SamePrints.Step.print
    apply SamePrints.Steps.step
    apply SamePrints.Step.silent
    · apply SamePrints.Silent.tick
    · apply SamePrints.Silent.tick
    intros
    apply SamePrints.Steps.recur
    grind [SamePrints.LoopPair]
  · simp [SamePrints.ret]

end Freigen.CompM.Examples.Nondet
