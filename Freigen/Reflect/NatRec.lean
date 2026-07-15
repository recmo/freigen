import Freigen.Reflect.Sound

namespace Freigen
namespace Ast

universe v

/-! ## Nat-recursion syntax bridge -/

/-- The semantic AST body corresponding to the zero/successor view exposed by `Nat.brecOn`'s
    generated functional. -/
def Expr.natBrecBody {H : Signature} {b : Tp}
    (range? : Option SourceRange)
    (base : Expr H (Tp.denote (ITree.CompE H.spec)) (some (.nat, b)) b)
    (step : Nat → Expr H (Tp.denote (ITree.CompE H.spec)) (some (.nat, b)) b)
    (n : Nat) : Expr H (Tp.denote (ITree.CompE H.spec)) (some (.nat, b)) b :=
  let core := .ite (n == 0) base (step (n - 1)) fun result => .ret result
  match range? with
  | none => core
  | some range => .source range core

/-- The parametric PHOAS spelling of `natBrecBody`.  Keeping this constructor next to its
    semantic counterpart makes the one non-structural correspondence used by the reflector
    explicit, rather than recovering it by normalizing a completed program. -/
def Expr.natBrecCode {H : Signature} {V : Tp → Type} {b : Tp}
    (range? : Option SourceRange)
    (base : Expr H V (some (.nat, b)) b)
    (step : V .nat → Expr H V (some (.nat, b)) b)
    (n : V .nat) : Expr H V (some (.nat, b)) b :=
  let core := .natLit 0 fun zero =>
    .bin .eq n zero fun isZero =>
      .ite isZero base
        (.natLit 1 fun one => .bin .sub n one step)
        fun result => .ret result
  match range? with
  | none => core
  | some range => .source range core

/-- At the semantic PHOAS carrier, `natBrecCode` is exactly `natBrecBody`. -/
theorem Expr.denote_natBrecCode {H : Signature} {b : Tp}
    (range? : Option SourceRange)
    (base : Expr H (Tp.denote (ITree.CompE H.spec)) (some (.nat, b)) b)
    (step : Nat → Expr H (Tp.denote (ITree.CompE H.spec)) (some (.nat, b)) b)
    (n : Nat) :
    Expr.denote (Expr.natBrecCode range? base step n) =
      Expr.denote (Expr.natBrecBody range? base step n) := by
  cases range? <;>
    simp [Expr.natBrecCode, Expr.natBrecBody, Expr.denote, Bin.denote]

/-- The local denotation fact lifted through the recursion interpreter. -/
theorem Expr.mrec_natBrecBody_eq_code {H : Signature} {b : Tp}
    (range? : Option SourceRange)
    (base : Expr H (Tp.denote (ITree.CompE H.spec)) (some (.nat, b)) b)
    (step : Nat → Expr H (Tp.denote (ITree.CompE H.spec)) (some (.nat, b)) b) :
    ITree.CompE.mrec (fun n => Expr.denote (Expr.natBrecBody range? base step n)) =
      ITree.CompE.mrec (fun n => Expr.denote (Expr.natBrecCode range? base step n)) := by
  congr 1
  funext n
  exact (Expr.denote_natBrecCode range? base step n).symm



/-! ## Nat.brecOn adequacy -/

/-- A `Nat.brecOn` source functional and the corresponding recursive PHOAS body denote related
    functions.  This packages the zero/successor reduction of `brecOn` and the well-founded
    interpretation of `selfCall`; the reflector only has to translate the generated functional's
    zero and successor applications. -/
theorem RecReflection.natBrecOnAdequate {S : ITree.HSig.{0, v}} {H : Signature}
    {C : Signature.Compat S H} {B : Type} {b : Tp}
    (resultRel : B → b.denote (ITree.CompE H.spec) → Prop)
    (source : Nat → Free S B)
    (F : (n : Nat) → @Nat.below (fun _ => Free S B) n → Free S B)
    (source_eq : source = fun n => @Nat.brecOn (fun _ => Free S B) n F)
    (range? : Option SourceRange)
    (base : Expr H (Tp.denote (ITree.CompE H.spec)) (some (.nat, b)) b)
    (step : Nat → Expr H (Tp.denote (ITree.CompE H.spec)) (some (.nat, b)) b)
    (baseSound : RecReflectionWitness C (Expr.natBrecBody range? base step) True b resultRel
      (F 0 PUnit.unit) base)
    (stepSound : ∀ n,
      RecCallAdequate (a := .nat) (b := b) C (Expr.natBrecBody range? base step) True resultRel
        (@Nat.brecOn (fun _ => Free S B) n F) n →
      RecReflectionWitness C (Expr.natBrecBody range? base step) True b resultRel
        (F (n + 1) ⟨@Nat.brecOn (fun _ => Free S B) n F,
          (@Nat.brecOn.go (fun _ => Free S B) n F).2⟩) (step n)) :
    Adequate (A := Nat) (a := .nat) C Eq resultRel source
      (ITree.CompE.mrec fun n => Expr.denote (Expr.natBrecBody range? base step n)) := by
  subst source
  apply RecReflection.adequate (a := .nat) (b := b) (C := C) Eq resultRel
    (fun n : Nat => @Nat.brecOn (fun _ => Free S B) n F)
    (Expr.natBrecBody range? base step) Nat.lt Nat.lt_wfRel.wf
  intro sourceArg targetArg hrel ih
  subst targetArg
  cases sourceArg with
  | zero =>
      constructor
      intro _ Z Y q ks kt hk
      have hbody : Expr.denote (Expr.natBrecBody range? base step 0) =
          Expr.denote base := by
        cases range? <;>
          simp [Expr.natBrecBody, Expr.denote, DomR.ret, cond] <;>
          exact ITree.CompE.bind_ret_right _
      rw [hbody]
      exact baseSound.sound True.intro q ks kt hk
  | succ n =>
      have hcall := ih n n rfl (Nat.lt_succ_self n)
      have hs := stepSound n hcall
      constructor
      intro _ Z Y q ks kt hk
      have hbody : Expr.denote (Expr.natBrecBody range? base step (n + 1)) =
          Expr.denote (step n) := by
        cases range? <;>
          simp [Expr.natBrecBody, Expr.denote, DomR.ret, cond] <;>
          exact ITree.CompE.bind_ret_right _
      rw [hbody]
      have hsource :
          @Nat.brecOn (fun _ => Free S B) (n + 1) F =
            F (n + 1) ⟨@Nat.brecOn (fun _ => Free S B) n F,
              (@Nat.brecOn.go (fun _ => Free S B) n F).2⟩ := by
        change F (n + 1) (@Nat.brecOn.go (fun _ => Free S B) n F) = _
        congr 1
      rw [hsource]
      exact hs.sound True.intro q ks kt hk



end Ast
end Freigen
