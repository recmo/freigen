import Freigen.IxPoly.Defs
import Freigen.ExactCodensity
import Freigen.Eff

namespace Freigen

def wBind {α β} {E} (a : IxPoly.W (Eff.Step E) α) (f : α → IxPoly.W (Eff.Step E) β): IxPoly.W (Eff.Step E) β := match a with
  | IxPoly.W.mk i p g => match p with
    | .ret a => f a
    | .tau => IxPoly.W.roll (Eff.Step.tau $ wBind (g ()) f)
    | .fail => IxPoly.W.roll (Eff.Step.fail)
    | .op e inp => IxPoly.W.mk (F := Eff.Step E) _ (Eff.NodeTag.op e inp) (fun
      | .inl a => wBind (g (.inl a)) f
      | .inr b => g (.inr b)
    )

instance {E} : Monad (IxPoly.W (Eff.Step E)) where
  pure a := IxPoly.W.roll (Eff.Step.ret a)
  bind x f := wBind x f

instance {E} : LawfulMonad (IxPoly.W (Eff.Step E)) := LawfulMonad.mk' _
  (by
    intro _ x
    change wBind x (fun a => IxPoly.W.roll (Eff.Step.ret a)) = x
    induction x with
    | mk i p g ih =>
      cases p
      · simp [wBind, IxPoly.W.roll, Eff.Step.ret]
        ext a
        cases a
      · have := ih ()
        simp only [wBind, IxPoly.W.roll, Eff.Step.tau]
        simp only [IxPoly.W.roll] at this
        simp only [IxPoly.W.mk.injEq, heq_eq_eq, true_and]
        ext x; cases x
        simp only
        exact this
      · simp [wBind, IxPoly.W.roll, Eff.Step.fail]
        ext x; cases x;
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
      · simp only [Bind.bind, wBind, Eff.Step.tau, IxPoly.W.roll]
        congr 1
        ext x; cases x
        simp only
        apply ih
      · simp only [Bind.bind, wBind, Eff.Step.fail, IxPoly.W.roll]
      · simp only [Bind.bind, wBind]
        congr
        ext x; cases x
        · simp only
          apply ih
        · rfl
  )

def Free (E : Eff.Spec) (α : Type) : Type _ := ExactCodensity (IxPoly.W (Eff.Step E)) α

instance {E} : Monad (Free E) :=
  inferInstanceAs (Monad (ExactCodensity (IxPoly.W (Eff.Step E))))
instance {E} : LawfulMonad (Free E) :=
  inferInstanceAs (LawfulMonad (ExactCodensity (IxPoly.W (Eff.Step E))))

end Freigen
