import Freigen.Reflect.Sound

namespace Freigen
namespace Ast

universe v

/-! ## The one source-recursion shape recognized by the reflector -/

def Expr.natBrecBody {H : Signature} {scope : DefCtx} {V : Tp → Type} {b : Tp}
    (range? : Option SourceRange) (base : Expr H scope V b)
    (step : V .nat → Expr H scope V b) (n : V .nat) : Expr H scope V b :=
  let core := .natLit 0 fun zero =>
    .bin .eq n zero fun isZero =>
      .ite isZero base
        (.natLit 1 fun one => .bin .sub n one step)
        fun result => .ret result
  match range? with
  | none => core
  | some range => .source range core

def Expr.natBrecSemantic {H : Signature} {scope ctx : DefCtx} {b : Tp}
    (range? : Option SourceRange) (base : Expr H scope (Tp.denote ctx) b)
    (step : Nat → Expr H scope (Tp.denote ctx) b) (n : Nat) :
    Expr H scope (Tp.denote ctx) b :=
  let core := .ite (n == 0) base (step (n - 1)) fun result => .ret result
  match range? with
  | none => core
  | some range => .source range core

theorem Expr.denote_natBrecBody {H : Signature} {scope ctx : DefCtx} {b : Tp}
    (extension : Extension scope ctx) (range? : Option SourceRange)
    (base : Expr H scope (Tp.denote ctx) b)
    (step : Nat → Expr H scope (Tp.denote ctx) b) (n : Nat) :
    (Expr.natBrecBody range? base step n).denote extension =
      (Expr.natBrecSemantic range? base step n).denote extension := by
  cases range? <;>
    simp [Expr.natBrecBody, Expr.natBrecSemantic, Expr.denote, Bin.denote]

/-! `Nat.brecOn` adequacy is stated directly for a definition in the final telescope. The
metaprogram supplies the lookup equation; the theorem supplies the well-founded argument. -/
theorem RecReflection.natBrecOnAdequate {S : ITree.HSig.{0, v}} {H : Signature}
    {ctx scope : DefCtx} (C : Signature.Compat S H ctx)
    (defs : Defs H (Tp.denote ctx) ctx) (extension : Extension scope ctx)
    {captures b : Tp} (self : DefRef scope captures .nat b)
    (captured : captures.denote ctx)
    {B : Type} (resultRel : B → b.denote ctx → Prop)
    (source : Nat → Free S B)
    (F : (n : Nat) → @Nat.below (fun _ => Free S B) n → Free S B)
    (source_eq : source = fun n => @Nat.brecOn (fun _ => Free S B) n F)
    (range? : Option SourceRange)
    (base : Expr H scope (Tp.denote ctx) b)
    (step : Nat → Expr H scope (Tp.denote ctx) b)
    (dispatch : ∀ argument,
      defs.denote .refl (self.lift extension) captured argument =
        (Expr.natBrecSemantic range? base step argument).denote extension)
    (baseSound : ReflectionWitness C defs extension True b resultRel
      (F 0 PUnit.unit) base)
    (stepSound : ∀ n,
      RecCallAdequate C defs resultRel
        (@Nat.brecOn (fun _ => Free S B) n F)
        (.mk (self.lift extension) (.pack captured)) n →
      ReflectionWitness C defs extension True b resultRel
        (F (n + 1) ⟨@Nat.brecOn (fun _ => Free S B) n F,
          (@Nat.brecOn.go (fun _ => Free S B) n F).2⟩) (step n)) :
    Adequate C defs Eq resultRel source
      (fun argument => invoke (.mk (self.lift extension) (.pack captured)) argument) := by
  subst source
  apply RecReflection.wellFounded defs extension self captured Eq resultRel
    (fun n => @Nat.brecOn (fun _ => Free S B) n F)
    (fun _ n => Expr.natBrecSemantic range? base step n) dispatch Nat.lt Nat.lt_wfRel.wf
  intro sourceArg targetArg related ih
  subst targetArg
  cases sourceArg with
  | zero =>
      have denotation :
          (Expr.natBrecSemantic range? base step 0).denote extension =
            base.denote extension := by
        cases range? <;>
          simp [Expr.natBrecSemantic, Expr.denote, ITree.CompE.ret, cond] <;>
          exact ITree.CompE.bind_ret_right _
      exact baseSound.congrTargetDenote denotation.symm
  | succ n =>
      have recursive : RecCallAdequate C defs resultRel
          (@Nat.brecOn (fun _ => Free S B) n F)
          (.mk (self.lift extension) (.pack captured)) n :=
        ih n n rfl (Nat.lt_succ_self n)
      have sound := stepSound n recursive
      have sourceReduction :
          @Nat.brecOn (fun _ => Free S B) (n + 1) F =
            F (n + 1) ⟨@Nat.brecOn (fun _ => Free S B) n F,
              (@Nat.brecOn.go (fun _ => Free S B) n F).2⟩ := by
        change F (n + 1) (@Nat.brecOn.go (fun _ => Free S B) n F) = _
        congr 1
      rw [sourceReduction]
      have denotation :
          (Expr.natBrecSemantic range? base step (n + 1)).denote extension =
            (step n).denote extension := by
        cases range? <;>
          simp [Expr.natBrecSemantic, Expr.denote, ITree.CompE.ret, cond] <;>
          exact ITree.CompE.bind_ret_right _
      exact sound.congrTargetDenote denotation.symm

end Ast
end Freigen
