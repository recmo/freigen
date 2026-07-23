import Freigen.IxPoly.Defs
import Freigen.ExactCodensity
import Freigen.Eff

namespace Freigen

variable {E : Type u} [eS: Eff.Spec E] {α β : Type}

def wBind {α β} (a : IxPoly.W (Eff.Step E) α) (f : α → IxPoly.W (Eff.Step E) β): IxPoly.W (Eff.Step E) β := match a with
  | IxPoly.W.mk i p g => match p with
    | .ret a => f a
    | .op e inp => IxPoly.W.mk (F := Eff.Step E) _ (Eff.NodeTag.op e inp) (fun
      | .inl a => wBind (g (.inl a)) f
      | .inr b => g (.inr b)
    )

instance : Monad (IxPoly.W (Eff.Step E)) where
  pure a := IxPoly.W.roll (Eff.Step.ret a)
  bind x f := wBind x f

instance : LawfulMonad (IxPoly.W (Eff.Step E)) := LawfulMonad.mk' _
  (by
    intro _ x
    change wBind x (fun a => IxPoly.W.roll (Eff.Step.ret a)) = x
    induction x with
    | mk i p g ih =>
      cases p
      · simp [wBind, IxPoly.W.roll, Eff.Step.ret]
        ext a
        cases a
      · simp only [wBind]
        congr
        ext x
        cases x
        · simp only
          apply_assumption
        · rfl
  )
  (by intros; rfl)
  (by
    intro _ _ _ a f g
    induction a with
    | mk i p g ih =>
      cases p
      · rfl
      · simp only [Bind.bind, wBind]
        congr
        ext x; cases x
        · simp only
          apply ih
        · rfl
  )

def Free (E : Type u) [Eff.Spec E] (α : Type) : Type _ :=
    ExactCodensity (IxPoly.W (Eff.Step E)) α

instance : Monad (Free E) :=
  inferInstanceAs (Monad (ExactCodensity (IxPoly.W (Eff.Step E))))
instance : LawfulMonad (Free E) :=
  inferInstanceAs (LawfulMonad (ExactCodensity (IxPoly.W (Eff.Step E))))

end Freigen
