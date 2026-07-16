import Freigen.Ast.Run

namespace Freigen
namespace Ast

universe u v

/-- A continuation-strengthened correspondence for an expression in a completed definition
table. Keeping the continuation inside the open call computation avoids requiring a global
`interpHandler_bind` law. -/
structure ReflectionWitness {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} (C : Signature.Compat S H ctx)
    (defs : Defs H (Tp.denote ctx) ctx) (extension : Extension scope ctx)
    (Φ : Prop) (α : Tp) {A : Type u}
    (result : A → α.denote ctx → Prop) (source : Free S A)
    (target : Expr H scope (Tp.denote ctx) α) : Type (max u v + 2) where
  sound : Φ → ∀ {Z : Type u} {B : Type} (q : Z → B → Prop)
    (sourceK : A → Free S Z) (targetK : α.denote ctx → OpenM H ctx B),
    (∀ sourceResult targetResult, result sourceResult targetResult →
      ITree.CompE.Eutt C q (Free.toITree (sourceK sourceResult))
        (defs.run (targetK targetResult))) →
    ITree.CompE.Eutt C q (Free.toITree (source.bind sourceK))
      (defs.run (ITree.CompE.bind (target.denote extension) targetK))

def ReflectionWitness.close {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} {C : Signature.Compat S H ctx}
    {defs : Defs H (Tp.denote ctx) ctx} {extension : Extension scope ctx}
    {α : Tp} {A : Type u} {result : A → α.denote ctx → Prop}
    {source : Free S A} {target : Expr H scope (Tp.denote ctx) α}
    (witness : ReflectionWitness C defs extension True α result source target) :
    ITree.CompE.Eutt C result (Free.toITree source)
      (defs.run (target.denote extension)) := by
  have sound := witness.sound True.intro result
    (fun value => .pure value) ITree.CompE.ret (by
      intro sourceResult targetResult related
      change ITree.CompE.Eutt C result (ITree.CompE.ret sourceResult)
        (defs.run (ITree.CompE.ret targetResult))
      rw [Defs.run, ITree.CompE.interpHandler_ret]
      exact ITree.CompE.Eutt.of_step C
        (.ret result sourceResult targetResult related))
  simpa only [Free.bind_pure, ITree.CompE.bind_ret_right,
    Defs.run, ITree.CompE.interpHandler_ret] using sound

/-- Closed output of `reflect%`. Compatibility and the result relation are polymorphic in the
program context because the definition telescope is stored inside the code package. -/
def Reflected {S : ITree.HSig.{u, v}} {H : Signature}
    (C : ∀ ctx, Signature.Compat S H ctx) (α : Tp) {A : Type u}
    (result : ∀ {ctx}, A → α.denote ctx → Prop) (source : Free S A) : Type 2 :=
  { code : Closed H α //
    ITree.CompE.Eutt (C code.ctx) (@result code.ctx)
      (Free.toITree source) (Closed.denote code) }

/-- CPS adequacy of one open target computation. -/
def Adequate {S : ITree.HSig.{u, v}} {H : Signature} {ctx : DefCtx}
    (C : Signature.Compat S H ctx) (defs : Defs H (Tp.denote ctx) ctx)
    {A B : Type u} {input output : Tp}
    (argRel : A → input.denote ctx → Prop)
    (resultRel : B → output.denote ctx → Prop)
    (source : A → Free S B)
    (target : input.denote ctx → OpenM H ctx (output.denote ctx)) : Prop :=
  ∀ sourceArg targetArg, argRel sourceArg targetArg →
    ∀ {Z : Type u} {R : Type} (q : Z → R → Prop)
      (sourceK : B → Free S Z) (targetK : output.denote ctx → OpenM H ctx R),
      (∀ sourceResult targetResult, resultRel sourceResult targetResult →
        ITree.CompE.Eutt C q (Free.toITree (sourceK sourceResult))
          (defs.run (targetK targetResult))) →
      ITree.CompE.Eutt C q (Free.toITree ((source sourceArg).bind sourceK))
        (defs.run (ITree.CompE.bind (target targetArg) targetK))

theorem Defs.run_bind_invoke {H : Signature} {ctx : DefCtx}
    (defs : Defs H (Tp.denote ctx) ctx)
    (ref : DefRef ctx captures input output) (captured : Packed ctx captures)
    (argument : input.denote ctx) (k : output.denote ctx → OpenM H ctx α) :
    defs.run (ITree.CompE.bind (invoke (.mk ref captured) argument) k) =
      ITree.CompE.tau
        (defs.run (ITree.CompE.bind
          (defs.denote .refl ref captured.unpack argument) k)) := by
  rw [bind_invoke]
  unfold Defs.run
  rw [ITree.CompE.interpHandler_op_right]
  rfl

theorem related_of_eq {A B : Type} {rel : A → B → Prop} {source : A} {x y : B}
    (h : y = x) (hx : rel source x) : rel source y := by
  cases h
  exact hx

/-! ## Structural expression constructors -/

def Reflection.source {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} {C : Signature.Compat S H ctx}
    {defs : Defs H (Tp.denote ctx) ctx} {extension : Extension scope ctx}
    {Φ : Prop} {α : Tp} {A : Type u} {result : A → α.denote ctx → Prop}
    {source : Free S A} (target : Expr H scope (Tp.denote ctx) α)
    (range : SourceRange)
    (sound : ReflectionWitness C defs extension Φ α result source target) :
    ReflectionWitness C defs extension Φ α result source (.source range target) :=
  ⟨sound.sound⟩

def Reflection.ret {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} {C : Signature.Compat S H ctx}
    {defs : Defs H (Tp.denote ctx) ctx} {extension : Extension scope ctx}
    {Φ : Prop} {α : Tp} {A : Type u} {result : A → α.denote ctx → Prop}
    (targetValue : α.denote ctx) {sourceValue : A}
    (related : Φ → result sourceValue targetValue) :
    ReflectionWitness C defs extension Φ α result (.pure sourceValue) (.ret targetValue) :=
  ⟨fun hΦ => by
    intro Z R q sourceK targetK continuation
    rw [Free.toITree_bind]
    change ITree.CompE.Eutt C q
      (ITree.CompE.bind (ITree.CompE.ret sourceValue)
        (fun value => Free.toITree (sourceK value)))
      (defs.run (ITree.CompE.bind (ITree.CompE.ret targetValue) targetK))
    rw [ITree.CompE.bind_ret, ITree.CompE.bind_ret]
    exact continuation sourceValue targetValue (related hΦ)⟩

def Reflection.discharge {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} {C : Signature.Compat S H ctx}
    {defs : Defs H (Tp.denote ctx) ctx} {extension : Extension scope ctx}
    {Φ : Prop} {α : Tp} {A : Type u} {result : A → α.denote ctx → Prop}
    {source : Free S A} {target : Expr H scope (Tp.denote ctx) α}
    (h : Φ) (sound : ReflectionWitness C defs extension Φ α result source target) :
    ReflectionWitness C defs extension True α result source target :=
  ⟨fun _ => sound.sound h⟩

def ReflectionWitness.congrTargetDenote {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} {C : Signature.Compat S H ctx}
    {defs : Defs H (Tp.denote ctx) ctx} {extension : Extension scope ctx}
    {Φ : Prop} {α : Tp} {A : Type u} {result : A → α.denote ctx → Prop}
    {source : Free S A} {left right : Expr H scope (Tp.denote ctx) α}
    (equal : left.denote extension = right.denote extension)
    (sound : ReflectionWitness C defs extension Φ α result source left) :
    ReflectionWitness C defs extension Φ α result source right := by
  constructor
  intro hΦ Z R q sourceK targetK continuation
  rw [← equal]
  exact sound.sound hΦ q sourceK targetK continuation

/-! ## Calls -/

def Reflection.bindCall {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} {C : Signature.Compat S H ctx}
    {defs : Defs H (Tp.denote ctx) ctx} {extension : Extension scope ctx}
    {Φ : Prop} {input output α : Tp} {A Z : Type u}
    {callRel : A → output.denote ctx → Prop}
    {result : Z → α.denote ctx → Prop}
    (fn : Closure ctx input output) (argument : input.denote ctx)
    {sourceCall : Free S A}
    (callSound : Φ → ∀ {Y : Type u} {R : Type} (q : Y → R → Prop)
      (sourceK : A → Free S Y) (targetK : output.denote ctx → OpenM H ctx R),
      (∀ sourceResult targetResult, callRel sourceResult targetResult →
        ITree.CompE.Eutt C q (Free.toITree (sourceK sourceResult))
          (defs.run (targetK targetResult))) →
      ITree.CompE.Eutt C q (Free.toITree (sourceCall.bind sourceK))
        (defs.run (ITree.CompE.bind (invoke fn argument) targetK)))
    {sourceK : A → Free S Z}
    (k : output.denote ctx → Expr H scope (Tp.denote ctx) α)
    (kSound : ∀ target source, callRel source target →
      ReflectionWitness C defs extension Φ α result (sourceK source) (k target)) :
    ReflectionWitness C defs extension Φ α result (sourceCall.bind sourceK)
      (.app fn argument k) :=
  ⟨fun hΦ => by
    intro Y R q sourceRest targetRest restSound
    have sourceAssoc : (sourceCall.bind sourceK).bind sourceRest =
        sourceCall.bind (fun source => (sourceK source).bind sourceRest) :=
      LawfulMonad.bind_assoc sourceCall sourceK sourceRest
    rw [sourceAssoc]
    change ITree.CompE.Eutt C q _
      (defs.run (ITree.CompE.bind
        (ITree.CompE.bind (invoke fn argument)
          (fun target => (k target).denote extension)) targetRest))
    rw [ITree.CompE.bind_assoc]
    exact callSound hΦ q
      (fun source => (sourceK source).bind sourceRest)
      (fun target => ITree.CompE.bind ((k target).denote extension) targetRest)
      (fun source target related =>
        (kSound target source related).sound hΦ q sourceRest targetRest restSound)⟩

def Reflection.call {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} {C : Signature.Compat S H ctx}
    {defs : Defs H (Tp.denote ctx) ctx} {extension : Extension scope ctx}
    {Φ : Prop} {input output : Tp} {A : Type u}
    {result : A → output.denote ctx → Prop}
    (fn : Closure ctx input output) (argument : input.denote ctx)
    {source : Free S A}
    (sound : Φ → ∀ {Y : Type u} {R : Type} (q : Y → R → Prop)
      (sourceK : A → Free S Y) (targetK : output.denote ctx → OpenM H ctx R),
      (∀ sourceResult targetResult, result sourceResult targetResult →
        ITree.CompE.Eutt C q (Free.toITree (sourceK sourceResult))
          (defs.run (targetK targetResult))) →
      ITree.CompE.Eutt C q (Free.toITree (source.bind sourceK))
        (defs.run (ITree.CompE.bind (invoke fn argument) targetK))) :
    ReflectionWitness C defs extension Φ output result source
      (.app fn argument .ret) :=
  by
    simpa only [Free.bind_pure] using
      (Reflection.bindCall (extension := extension) fn argument sound .ret
        fun target source related => Reflection.ret target (fun _ => related))

def Reflection.closure {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} {C : Signature.Compat S H ctx}
    {defs : Defs H (Tp.denote ctx) ctx} {extension : Extension scope ctx}
    {Φ : Prop} {captures input output α : Tp} {A : Type u}
    {result : A → α.denote ctx → Prop} (ref : DefRef scope captures input output)
    (captured : captures.denote ctx)
    (body : Closure ctx input output → Expr H scope (Tp.denote ctx) α)
    {source : Free S A}
    (sound : ReflectionWitness C defs extension Φ α result source
      (body (.mk (ref.lift extension) (.pack captured)))) :
    ReflectionWitness C defs extension Φ α result source (.closure ref captured body) := by
  exact ReflectionWitness.congrTargetDenote
    (left := body (.mk (ref.lift extension) (.pack captured)))
    (right := .closure ref captured body) rfl sound

/-! ## Higher-order operations -/

def Reflection.op {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} (C : Signature.Compat S H ctx)
    {defs : Defs H (Tp.denote ctx) ctx} {extension : Extension scope ctx}
    {Φ : Prop} {α : Tp} {A : Type u}
    {result : A → α.denote ctx → Prop}
    (sourceOp : S.op) (targetOp : H.op) (witness : C.opRel sourceOp targetOp)
    (targetInput : (H.input targetOp).denote ctx) {sourceInput : S.input sourceOp}
    (inputRelated : Φ → C.input witness sourceInput targetInput)
    {sourceBlocks : (branch : S.branch sourceOp) → S.branchInput sourceOp branch →
      Free S (S.branchOutput sourceOp branch)}
    (targetBlocks : (branch : H.branch targetOp) →
      (H.branchInput targetOp branch).denote ctx →
        Expr H scope (Tp.denote ctx) (H.branchOutput targetOp branch))
    (blockSound : ∀ targetBranch targetValue sourceBranch,
      (branchRelated : C.branch witness sourceBranch targetBranch) →
      ∀ sourceValue, C.branchInput witness branchRelated sourceValue targetValue →
        ReflectionWitness C defs extension Φ (H.branchOutput targetOp targetBranch)
          (C.branchOutput witness branchRelated)
          (sourceBlocks sourceBranch sourceValue) (targetBlocks targetBranch targetValue))
    {sourceContinuation : S.output sourceOp → Free S A}
    (targetContinuation : (H.output targetOp).denote ctx →
      Expr H scope (Tp.denote ctx) α)
    (continuationSound : ∀ targetValue sourceValue,
      C.output witness sourceValue targetValue →
        ReflectionWitness C defs extension Φ α result
          (sourceContinuation sourceValue) (targetContinuation targetValue)) :
    ReflectionWitness C defs extension Φ α result
      (.op sourceOp sourceInput sourceBlocks sourceContinuation)
      (.op targetOp targetInput targetBlocks targetContinuation) := by
  constructor
  intro hΦ Z R q sourceK targetK restSound
  let sourceBlocks' := fun (branch : S.branch sourceOp)
      (input : S.branchInput sourceOp branch) =>
    Free.toITree (sourceBlocks branch input)
  let sourceContinuation' := fun output =>
    ITree.CompE.bind (Free.toITree (sourceContinuation output))
      (fun value => Free.toITree (sourceK value))
  let targetBlocks' := fun (branch : H.branch targetOp)
      (input : (H.branchInput targetOp branch).denote ctx) =>
    defs.run ((targetBlocks branch input).denote extension)
  let targetContinuation' := fun output =>
    defs.run (ITree.CompE.bind
      ((targetContinuation output).denote extension) targetK)
  have matched : ITree.CompE.Eutt C q
      (ITree.CompE.bind
        (ITree.CompE.op sourceOp sourceInput
          (fun branch => sourceBlocks' branch.1 branch.2) ITree.CompE.ret)
        sourceContinuation')
      (ITree.CompE.bind
        (ITree.CompE.op targetOp targetInput
          (fun branch => targetBlocks' branch.1 branch.2) ITree.CompE.ret)
        targetContinuation') :=
    ITree.CompE.Eutt.of_step C
      (.op q witness sourceInput targetInput (inputRelated hΦ)
        sourceBlocks' sourceContinuation' targetBlocks' targetContinuation'
        (fun sourceBranch targetBranch branchRelated sourceValue targetValue
            branchInput =>
          (Reflection.discharge hΦ
            (blockSound targetBranch targetValue sourceBranch branchRelated
              sourceValue branchInput)).close)
        (fun sourceValue targetValue output => by
          simpa only [sourceContinuation', targetContinuation', Free.toITree_bind]
            using (continuationSound targetValue sourceValue output).sound
              hΦ q sourceK targetK restSound))
  apply ITree.CompE.Eutt.congr C _ _ matched
  · rw [Free.toITree_bind, Free.toITree_op, ITree.CompE.bind_assoc]
  · change ITree.CompE.bind
        (ITree.CompE.op targetOp targetInput
          (fun branch => targetBlocks' branch.1 branch.2) ITree.CompE.ret)
        targetContinuation' =
      defs.run (ITree.CompE.bind
        ((Expr.op targetOp targetInput targetBlocks targetContinuation).denote extension)
        targetK)
    rw [ITree.CompE.bind_op]
    simp only [ITree.CompE.bind_ret]
    change ITree.CompE.op targetOp targetInput
        (fun branch => defs.run
          ((targetBlocks branch.1 branch.2).denote extension))
        (fun output => defs.run (ITree.CompE.bind
          ((targetContinuation output).denote extension) targetK)) = _
    change _ = defs.run (ITree.CompE.bind
      (ITree.CompE.bind
        (ITree.CompE.op (.inl targetOp) targetInput
          (fun branch =>
            (targetBlocks branch.1 branch.2).denote extension)
          ITree.CompE.ret)
        (fun output => (targetContinuation output).denote extension))
      targetK)
    rw [ITree.CompE.bind_assoc, ITree.CompE.bind_op]
    simp only [ITree.CompE.bind_ret]
    rw [Defs.run_op]

/-! ## Definition adequacy and recursion -/

def RecCallAdequate {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx : DefCtx} (C : Signature.Compat S H ctx)
    (defs : Defs H (Tp.denote ctx) ctx)
    {B : Type u} {input output : Tp}
    (resultRel : B → output.denote ctx → Prop)
    (sourceCall : Free S B) (targetFn : Closure ctx input output)
    (targetArg : input.denote ctx) : Prop :=
  ∀ {Z : Type u} {R : Type} (q : Z → R → Prop)
    (sourceK : B → Free S Z) (targetK : output.denote ctx → OpenM H ctx R),
    (∀ sourceResult targetResult, resultRel sourceResult targetResult →
      ITree.CompE.Eutt C q (Free.toITree (sourceK sourceResult))
        (defs.run (targetK targetResult))) →
    ITree.CompE.Eutt C q (Free.toITree (sourceCall.bind sourceK))
      (defs.run (ITree.CompE.bind (invoke targetFn targetArg) targetK))

def Reflection.recursiveCall {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} {C : Signature.Compat S H ctx}
    {defs : Defs H (Tp.denote ctx) ctx} {extension : Extension scope ctx}
    {Φ : Prop} {input output α : Tp} {A Z : Type u}
    {callRel : A → output.denote ctx → Prop}
    {result : Z → α.denote ctx → Prop}
    (sourceCall : Free S A) (targetFn : Closure ctx input output)
    (targetArg : input.denote ctx)
    (ih : Φ → RecCallAdequate C defs callRel sourceCall targetFn targetArg)
    {sourceK : A → Free S Z}
    (k : output.denote ctx → Expr H scope (Tp.denote ctx) α)
    (kSound : ∀ target source, callRel source target →
      ReflectionWitness C defs extension Φ α result (sourceK source) (k target)) :
    ReflectionWitness C defs extension Φ α result (sourceCall.bind sourceK)
      (.app targetFn targetArg k) :=
  Reflection.bindCall targetFn targetArg ih k kSound

theorem RecReflection.wellFounded {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} {C : Signature.Compat S H ctx}
    (defs : Defs H (Tp.denote ctx) ctx) (extension : Extension scope ctx)
    {captures input output : Tp} (self : DefRef scope captures input output)
    (captured : captures.denote ctx)
    {A B : Type u}
    (argRel : A → input.denote ctx → Prop)
    (resultRel : B → output.denote ctx → Prop)
    (source : A → Free S B)
    (body : captures.denote ctx → input.denote ctx →
      Expr H scope (Tp.denote ctx) output)
    (dispatch : ∀ argument,
      defs.denote .refl (self.lift extension) captured argument =
        (body captured argument).denote extension)
    (order : A → A → Prop) (wf : WellFounded order)
    (bodySound : ∀ sourceArg targetArg, argRel sourceArg targetArg →
      (∀ smaller targetSmaller, argRel smaller targetSmaller →
        order smaller sourceArg →
        RecCallAdequate C defs resultRel (source smaller)
          (.mk (self.lift extension) (.pack captured)) targetSmaller) →
      ReflectionWitness C defs extension True output resultRel
        (source sourceArg) (body captured targetArg)) :
    Adequate C defs argRel resultRel source
      (fun argument => invoke (.mk (self.lift extension) (.pack captured)) argument) := by
  intro sourceArg
  induction sourceArg using wf.induction with
  | h sourceArg ih =>
      intro targetArg related Z R q sourceK targetK continuation
      have bodyWitness := bodySound sourceArg targetArg related
        (fun smaller targetSmaller smallerRelated smallerOrder =>
          ih smaller smallerOrder targetSmaller smallerRelated)
      have bodyAdequate := bodyWitness.sound True.intro q sourceK targetK continuation
      rw [Defs.run_bind_invoke, Packed.unpack_pack, dispatch targetArg]
      exact ITree.CompE.Eutt.tauR C bodyAdequate

theorem RecReflection.nonrecursiveAdequate
    {S : ITree.HSig.{u, v}} {H : Signature}
    {ctx scope : DefCtx} {C : Signature.Compat S H ctx}
    (defs : Defs H (Tp.denote ctx) ctx) (extension : Extension scope ctx)
    {captures input output : Tp} (self : DefRef scope captures input output)
    (captured : captures.denote ctx)
    {A B : Type u}
    (argRel : A → input.denote ctx → Prop)
    (resultRel : B → output.denote ctx → Prop)
    (source : A → Free S B)
    (body : captures.denote ctx → input.denote ctx →
      Expr H scope (Tp.denote ctx) output)
    (dispatch : ∀ argument,
      defs.denote .refl (self.lift extension) captured argument =
        (body captured argument).denote extension)
    (bodySound : ∀ sourceArg targetArg, argRel sourceArg targetArg →
      ReflectionWitness C defs extension True output resultRel
        (source sourceArg) (body captured targetArg)) :
    Adequate C defs argRel resultRel source
      (fun argument => invoke (.mk (self.lift extension) (.pack captured)) argument) := by
  let order := fun _ _ : A => False
  have wf : WellFounded order :=
    ⟨fun value => .intro value fun _ impossible => False.elim impossible⟩
  apply RecReflection.wellFounded defs extension self captured argRel resultRel
    source body dispatch order wf
  intro sourceArg targetArg related _
  exact bodySound sourceArg targetArg related

end Ast
end Freigen
