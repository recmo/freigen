import Freigen.Eff
import Freigen.Free.Basic
import Freigen.CompM.Basic
import Freigen.CompM.WF

namespace Freigen.Ast

/-- Object-language types. -/
inductive Tp
| uInt32
| int32
| bool
| array (tp : Tp)
| unit
| prod (fst : Tp) (snd : Tp)
| fn (inp : Tp) (out : Tp)
deriving BEq, ReflBEq, LawfulBEq, DecidableEq

def FnRef : Type := Nat

abbrev Tp.denote : Tp → Type
| .uInt32 => UInt32
| .int32 => Int32
| .bool => Bool
| .array tp => Array (Tp.denote tp)
| .unit => Unit
| .prod l r => l.denote × r.denote
| .fn _ _ => FnRef

def Tp.listProd : List Tp → Tp
| [] => .unit
| tp :: tps => .prod tp (Tp.listProd tps)

inductive IsAbiTp : Tp → Prop
| uInt32 : IsAbiTp .uInt32
| int32 : IsAbiTp .int32
| bool : IsAbiTp .bool
| array {tp} : IsAbiTp tp → IsAbiTp (Tp.array tp)
| prod {fst snd} : IsAbiTp fst → IsAbiTp snd → IsAbiTp (Tp.prod fst snd)

abbrev AbiTp := {tp : Tp // IsAbiTp tp}

abbrev AbiTp.uInt32 : AbiTp := ⟨.uInt32, .uInt32⟩
abbrev AbiTp.int32 : AbiTp := ⟨.int32, .int32⟩
abbrev AbiTp.bool : AbiTp := ⟨.bool, .bool⟩
abbrev AbiTp.array (tp : AbiTp) : AbiTp :=
  ⟨.array tp.val, .array tp.property⟩
abbrev AbiTp.prod (fst snd : AbiTp) : AbiTp :=
  ⟨.prod fst.val snd.val, .prod fst.property snd.property⟩

structure EffSig where
  Ctx : Type u
  [decidableEqCtx : DecidableEq Ctx]
  tag : Ctx → Type u
  input : (γ : Ctx) → tag γ → AbiTp
  output : (γ : Ctx) → tag γ → AbiTp
  blockTag : (γ : Ctx) → tag γ → Type u
  blockCtx : (γ : Ctx) → (e : tag γ) → blockTag γ e → Ctx
  blockInputs : (γ : Ctx) → (e : tag γ) → blockTag γ e → AbiTp
  blockOutputs : (γ : Ctx) → (e : tag γ) → blockTag γ e → AbiTp

attribute [instance] EffSig.decidableEqCtx

/-- Pull the syntactic signature back along `Tp.denote`; inputs live in tags. -/
def EffSig.denote (s : EffSig) : s.Ctx → Type u :=
  fun γ => Σ e : s.tag γ, (s.input γ e).val.denote

instance EffSig.denoteSpec (s : EffSig) : Eff.Spec s.denote where
  output := fun γ ⟨e, _⟩ => (s.output γ e).val.denote
  blockTag := fun γ ⟨e, _⟩ => s.blockTag γ e
  blockCtx := fun γ ⟨e, _⟩ => s.blockCtx γ e
  blockInputs := fun γ ⟨e, _⟩ b => (s.blockInputs γ e b).val.denote
  blockOutputs := fun γ ⟨e, _⟩ b => (s.blockOutputs γ e b).val.denote

abbrev SourceM (eff : EffSig) (γ : eff.Ctx) (α : Type) :=
  Free eff.denote γ α

abbrev EvalEff (eff : EffSig) : eff.Ctx → Type u :=
  Eff.Tau ⊕ₑ (Eff.Fail ⊕ₑ eff.denote)

abbrev EvalM (eff : EffSig) (γ : eff.Ctx) (α : Type) :=
  CompM (EvalEff eff) γ α

inductive Builtin : List Tp → Tp → Type
| uAdd : Builtin [.uInt32, .uInt32] .uInt32
| uSub : Builtin [.uInt32, .uInt32] .uInt32
| uMul : Builtin [.uInt32, .uInt32] .uInt32
| uDiv : Builtin [.uInt32, .uInt32] .uInt32

| uEq : Builtin [.uInt32, .uInt32] .bool
| uLt : Builtin [.uInt32, .uInt32] .bool

inductive Expr
    (eff : EffSig) (Var : Tp → Type) :
    (γ : eff.Ctx) → Tp → Type where
| ret {γ tp} : Var tp → Expr eff Var γ tp
| lit {γ outK} : (tp : AbiTp) → (v : tp.val.denote) →
    (Var tp → Expr eff Var γ outK) → Expr eff Var γ outK
| builtin {γ inp out outK} :
    (b : Builtin inp out) → Var (Tp.listProd inp) →
    (Var out → Expr eff Var γ outK) → Expr eff Var γ outK
| lam {γ inp out outK} : (Var inp → Expr eff Var γ out) →
    (Var (.fn inp out) → Expr eff Var γ outK) → Expr eff Var γ outK
| app {γ inp out outK} : (f : Var (.fn inp out)) → (x : Var inp) →
    (Var out → Expr eff Var γ outK) → Expr eff Var γ outK
| ite {γ out outK} : (c : Var .bool) → (t e : Expr eff Var γ out) →
    (Var out → Expr eff Var γ outK) → Expr eff Var γ outK
| loop {γ c outK} :
    (body : Var c → Expr eff Var γ (Tp.prod c .bool)) →
    (init : Var c) →
    (Var c → Expr eff Var γ outK) → Expr eff Var γ outK
| op {γ outK} : (e : eff.tag γ) → (inp : Var (eff.input γ e)) →
    (blocks :
      (b : eff.blockTag γ e) →
      Var (eff.blockInputs γ e b) →
      Expr eff Var (eff.blockCtx γ e b) (eff.blockOutputs γ e b)) →
    (Var (eff.output γ e) → Expr eff Var γ outK) →
    Expr eff Var γ outK

inductive Program
    (eff : EffSig)
    (mainCtx : eff.Ctx)
    (mainInput mainOutput : AbiTp)
    (Var : Tp → Type) : Type where
| define {γ inp out} :
    (Var (.fn inp out) → Var inp → Expr eff Var γ out) →
    (Var (.fn inp out) →
      Program eff mainCtx mainInput mainOutput Var) →
    Program eff mainCtx mainInput mainOutput Var
| main :
    (Var mainInput.val → Expr eff Var mainCtx mainOutput.val) →
    Program eff mainCtx mainInput mainOutput Var

structure ProgramState (eff : EffSig) where
  next : Nat
  env :
    Std.HashMap Nat
      (Σ γ : eff.Ctx,
        Σ i : Tp,
        Σ o : Tp,
          Tp.denote i → Expr eff Tp.denote γ o)

def ProgramState.empty (eff : EffSig) : ProgramState eff where
  next := 0
  env := default

def ProgramState.alloc
    {eff : EffSig} {γ : eff.Ctx} {i o : Tp}
    (s : ProgramState eff)
    (f :
      Tp.denote (.fn i o) →
      Tp.denote i →
      Expr eff Tp.denote γ o) :
    ProgramState eff × FnRef :=
  let id := s.next
  let s' : ProgramState eff := {
    s with
    next := id + 1
    env := s.env.insert id ⟨γ, i, o, f id⟩
  }
  (s', id)

def ProgramState.lookup
    {eff : EffSig} {γ : eff.Ctx} {i o : Tp}
    (s : ProgramState eff) :
    Tp.denote (.fn i o) →
    Option (Tp.denote i → Expr eff Tp.denote γ o) := fun x => do
  let x ← s.env.get? x
  match x with
  | ⟨γ', i', o', body⟩ =>
    if h : γ = γ' ∧ i = i' ∧ o = o' then
      pure $ h.1 ▸ h.2.1 ▸ h.2.2 ▸ body
    else
      none

inductive ExprCont
    (eff : EffSig) (γ : eff.Ctx) :
    Tp → Tp → Type where
| pure :
    (i.denote → Expr eff Tp.denote γ o) →
    ExprCont eff γ i o
| bind :
    (i.denote → Expr eff Tp.denote γ o') →
    ExprCont eff γ o' o →
    ExprCont eff γ i o

-- abbrev EvalState
--     (eff : EffSig) (γ : eff.Ctx) (o : Tp) :=
--   ProgramState eff ×
--     (Σ i : Tp, Tp.denote i ×
--       (Tp.denote i → Expr eff Tp.denote γ o))

inductive EvalState (eff : EffSig): eff.Ctx × Type → Type _ where
| done {γ} {R}: R → EvalState eff (γ, R)
| cont {γ} {R} {i : Tp}: ProgramState eff → Expr eff Tp.denote γ i →
    (ProgramState eff → Tp.denote i → EvalState eff (γ, R)) → EvalState eff (γ, R)

def Expr.denoteCo {eff} (i : eff.Ctx × Type) : EvalState eff i → Eff.Step eff.Ctx (Eff.Fail ⊕ₑ Eff.Tau ⊕ₑ eff.denote) (EvalState eff) i
| .done v => Eff.Step.ret v
| .cont s e k => match e with
  | .ret v => Eff.Step.tau (k s v)
  | .lit _ v k' => Eff.Step.tau (EvalState.cont s (k' v) k)
  | .builtin b i k' => match b, i with
    | .uAdd, ⟨x, y, ()⟩ => Eff.Step.tau (EvalState.cont s (k' (x + y)) k)
    | .uSub, ⟨x, y, ()⟩ => Eff.Step.tau (EvalState.cont s (k' (x - y)) k)
    | .uMul, ⟨x, y, ()⟩ => Eff.Step.tau (EvalState.cont s (k' (x * y)) k)
    | .uDiv, ⟨x, y, ()⟩ => Eff.Step.tau (EvalState.cont s (k' (x / y)) k)
    | .uEq, ⟨x, y, ()⟩ => Eff.Step.tau (EvalState.cont s (k' (x = y)) k)
    | .uLt, ⟨x, y, ()⟩ => Eff.Step.tau (EvalState.cont s (k' (x < y)) k)
  | .lam b k' =>
    let (s', l) := s.alloc (fun _ x => b x)
    Eff.Step.tau (EvalState.cont s' (k' l) k)
  | .app f x k' => match s.lookup f with
    | none => Eff.Step.fail
    | some f => Eff.Step.tau (EvalState.cont s (f x) fun s' r => EvalState.cont s' (k' r) k)
  | .ite c t e k' => Eff.Step.tau (EvalState.cont s (if c then t else e) fun s' r => EvalState.cont s' (k' r) k)
  | .loop body init k' =>
    -- `true` means "keep going"
    Eff.Step.tau (EvalState.cont s (body init) fun s' r => match r with
      | (next, true) => EvalState.cont s' (Expr.loop body next k') k
      | (next, false) => EvalState.cont s' (k' next) k
    )
  | .op e inp blocks k' =>
    Eff.Step.op (.inr $ .inr ⟨e, inp⟩) (fun tag inp =>
      EvalState.cont s (blocks tag inp) fun _ r => EvalState.done r
    ) fun o => EvalState.cont s (k' o) k

def Expr.denote {eff} {γ : eff.Ctx} {o : Tp} (state : ProgramState eff) (expr : Expr eff Tp.denote γ o) :
    CompM (Eff.Fail ⊕ₑ Eff.Tau ⊕ₑ eff.denote) γ (ProgramState eff × o.denote) :=
  CompM.corec denoteCo (EvalState.cont state expr fun s r => EvalState.done (s, r))

def Program.denote' {eff} {γ} {iT oT} (p: Program eff γ iT oT Tp.denote) (i: iT.val.denote):
    CompM (Eff.Fail ⊕ₑ Eff.Tau ⊕ₑ eff.denote) γ (ProgramState eff × oT.val.denote) :=
  go (ProgramState.empty _) p where
  go : ProgramState eff → Program eff γ iT oT Tp.denote →
    CompM (Eff.Fail ⊕ₑ Eff.Tau ⊕ₑ eff.denote) γ (ProgramState eff × oT.val.denote) := fun s => fun
  | .define body k =>
    let (s', f) := s.alloc (fun f x => body f x)
    go s' (k f)
  | .main body => Expr.denote s (body i)

def Program.denote {eff} {γ} {iT oT} (p: Program eff γ iT oT Tp.denote) (i: iT.val.denote):
    CompM (Eff.Fail ⊕ₑ Eff.Tau ⊕ₑ eff.denote) γ oT.val.denote :=
  (·.2) <$> Program.denote' p i

structure ProgramCert {srcEff : EffSig} {tgtEff : srcEff.Ctx → Type} [Eff.Spec tgtEff]
    (handler : Eff.Handler srcEff.denote (Free tgtEff))
    {iTp oTp : AbiTp} {γ : srcEff.Ctx}
    (p : ∀{V}, Program srcEff γ iTp oTp V)
    (t : iTp.val.denote → Free tgtEff γ oTp.val.denote) where
  wf : ∀ i, CompM.WF (p.denote i)
  nofail : ∀ i, Free.UnusedL ((p.denote i).toFree $ wf i)
  correct : ∀ i, (
    p.denote i
    |>.toFree (wf i)
    |>.elideL (nofail i)
    |>.interpL (fun _ _ => pure ())
    |>.interp handler
  ) = t i

end Freigen.Ast
