-- import Freigen.Eff
-- import Freigen.CompM.Basic

-- namespace Freigen.Ast

-- inductive Tp
-- | uInt32
-- | int32
-- | bool
-- | array (tp : Tp)
-- | unit
-- | prod (fst : Tp) (snd : Tp)
-- | fn (inp : Tp) (out : Tp)
-- deriving BEq, ReflBEq, LawfulBEq, DecidableEq

-- def FnRef : Type := Nat

-- abbrev Tp.denote : Tp → Type
-- | .uInt32 => UInt32
-- | .int32 => Int32
-- | .bool => Bool
-- | .array tp => Array (Tp.denote tp)
-- | .unit => Unit
-- | .prod l r => l.denote × r.denote
-- | .fn _ _ => Nat

-- def Tp.listProd : List Tp → Tp
-- | [] => .unit
-- | tp :: tps => .prod tp (Tp.listProd tps)

-- inductive IsAbiTp : Tp → Prop
-- | uInt32 : IsAbiTp Tp.uInt32
-- | int32 : IsAbiTp Tp.int32
-- | bool : IsAbiTp Tp.bool
-- | array {tp} : IsAbiTp tp → IsAbiTp (Tp.array tp)
-- | prod {fst snd} : IsAbiTp fst → IsAbiTp snd → IsAbiTp (Tp.prod fst snd)

-- abbrev AbiTp := {tp : Tp // IsAbiTp tp}

-- abbrev AbiTp.uInt32 : AbiTp := ⟨.uInt32, .uInt32⟩
-- abbrev AbiTp.int32 : AbiTp := ⟨.int32, .int32⟩
-- abbrev AbiTp.bool : AbiTp := ⟨.bool, .bool⟩
-- abbrev AbiTp.array (tp : AbiTp) : AbiTp := ⟨.array tp.val, .array tp.property⟩
-- abbrev AbiTp.prod (fst snd : AbiTp) : AbiTp := ⟨.prod fst.val snd.val, .prod fst.property snd.property⟩

-- structure EffSig where
--   tag : Type u
--   input : tag → AbiTp
--   output : tag → AbiTp
--   blockTag : tag → Type u
--   blockInputs : (t : tag) → blockTag t → AbiTp
--   blockOutputs : (t : tag) → blockTag t → AbiTp

-- instance EffSig.denote (s : EffSig) : Eff.Spec s.tag where
--   input := fun t => (s.input t).val.denote
--   output := fun t => (s.output t).val.denote
--   blockTag := s.blockTag
--   blockInputs := fun t b => (s.blockInputs t b).val.denote
--   blockOutputs := fun t b => (s.blockOutputs t b).val.denote

-- inductive Builtin : List Tp → Tp → Type
-- | uAdd : Builtin [.uInt32, .uInt32] .uInt32
-- | uSub : Builtin [.uInt32, .uInt32] .uInt32
-- | uMul : Builtin [.uInt32, .uInt32] .uInt32
-- | uDiv : Builtin [.uInt32, .uInt32] .uInt32

-- | uEq : Builtin [.uInt32, .uInt32] .bool
-- | uLt : Builtin [.uInt32, .uInt32] .bool

-- inductive Expr (eff : EffSig) (Var : Tp → Type) : Tp → Type where
-- | ret {tp} : Var tp → Expr eff Var tp
-- | lit {outK} : (tp : AbiTp) → (v : tp.val.denote) →
--     (Var tp → Expr eff Var outK) → Expr eff Var outK
-- | builtin {inp out outK} : (b : Builtin inp out) → Var (Tp.listProd inp) →
--     (Var out → Expr eff Var outK) → Expr eff Var outK
-- | lam {inp out outK} : (Var inp → Expr eff Var out) →
--     (Var (.fn inp out) → Expr eff Var outK) → Expr eff Var outK
-- | app {inp out outK} : (f : Var (.fn inp out)) → (x : Var inp) →
--     (Var out → Expr eff Var outK) → Expr eff Var outK
-- | ite {outK} : (c : Var Tp.bool) → (t e : Expr eff Var outK) →
--     (Var outK → Expr eff Var outK) → Expr eff Var outK
-- | loop {c outK} : (body : Var c → Expr eff Var (Tp.prod c Tp.bool)) →
--     (init : Var c) →
--     (Var c → Expr eff Var outK) → Expr eff Var outK
-- | op {outK} : (e : eff.tag) → (inp : Var (eff.input e)) →
--     (blocks : (b : eff.blockTag e) → Var (eff.blockInputs e b) → Expr eff Var (eff.blockOutputs e b)) →
--     (Var (eff.output e) → Expr eff Var outK) → Expr eff Var outK

-- inductive Program (eff : EffSig) (mainInput : AbiTp) (mainOutput : AbiTp) (Var : Tp → Type) : Type where
-- | define {inp out} : (Var (.fn inp out) → Var inp → Expr eff Var out) →
--     (Var (.fn inp out) → Program eff mainInput mainOutput Var) → Program eff mainInput mainOutput Var
-- | main : (Var mainInput.val → Expr eff Var mainOutput.val) → Program eff mainInput mainOutput Var

-- structure ProgramState (eff : EffSig) where
--   next : Nat
--   env : Std.HashMap Nat (Σ i o, Tp.denote i → Expr eff Tp.denote o)

-- def ProgramState.empty (eff : EffSig) : ProgramState eff where
--   next := 0
--   env := default

-- def ProgramState.alloc {eff : EffSig} {i o : Tp} (s : ProgramState eff)
--     (f : Tp.denote (.fn i o) → Tp.denote i → Expr eff Tp.denote o) : (ProgramState eff × Nat) :=
--   let id := s.next
--   let s' : ProgramState eff := { s with next := id + 1, env := s.env.insert id ⟨i, o, f id⟩ }
--   (s', id)

-- def ProgramState.lookup {E : Type u} [Eff.Spec E] [Eff.Has Eff.Fail E] {eff : EffSig} {i o : Tp} (s : ProgramState eff):
--     Tp.denote (.fn i o) → CompM E (Tp.denote i → Expr eff Tp.denote o) := fun f => match s.env.get? f with
--   | none => CompM.fail
--   | some ⟨i', o', f⟩ => if h: i = i' ∧ o = o' then pure $ h.1 ▸ h.2 ▸ f else CompM.fail

-- inductive ExprCont (eff : EffSig) : Tp → Tp → Type where
-- | pure : (i.denote → Expr eff Tp.denote o) → ExprCont eff i o
-- | bind : (i.denote → Expr eff Tp.denote o') → ExprCont eff o' o → ExprCont eff i o

-- abbrev EvalState (eff : EffSig) (o : Tp) := ProgramState eff × (Σ i, Tp.denote i × (Tp.denote i → Expr eff Tp.denote o))

-- def Builtin.denote {i o} {eff : EffSig}: Builtin i o → Tp.denote (Tp.listProd i) → CompM (Eff.Tau ⊕ Eff.Fail ⊕ eff.tag) (Tp.denote o)
-- | uAdd, ⟨x, y, ()⟩ => pure (x + y)
-- | uSub, ⟨x, y, ()⟩ => pure (x - y)
-- | uMul, ⟨x, y, ()⟩ => pure (x * y)
-- | uDiv, ⟨x, y, ()⟩ => if y = 0 then pure 0 else pure (x / y)
-- | uEq, ⟨x, y, ()⟩ => pure (x = y)
-- | uLt, ⟨x, y, ()⟩ => pure (x < y)

-- mutual

-- def Expr.denote {o} {eff : EffSig}: EvalState eff o →
--     CompM (Eff.Tau ⊕ Eff.Fail ⊕ eff.tag) (Tp.denote o) :=
--   CompM.loop (fun (heap, ⟨iT, inp, k⟩) => do
--     Expr.denoteUntilTau heap (k inp)
--   )

-- def Expr.denoteUntilTau {tp} {eff : EffSig}: ProgramState eff → Expr eff Tp.denote tp →
--     CompM (Eff.Tau ⊕ Eff.Fail ⊕ eff.tag) (EvalState eff tp ⊕ tp.denote)
-- | s, ret v => pure (.inr v)
-- | s, lit tp v k => Expr.denoteUntilTau s (k v)
-- | s, builtin b args k => b.denote args >>= fun v => Expr.denoteUntilTau s (k v)
-- | s, lam f k =>
--   let (s, l) := s.alloc (fun id x => f x)
--   Expr.denoteUntilTau s (k l)
-- | s, app f x k => do
--   let f ← s.lookup f
--   pure $ .inl ⟨s, ⟨_, x, fun r => ⟩⟩
-- | s, ite c t e k => if c then Expr.denoteUntilTau s t else Expr.denoteUntilTau s e
-- | s, loop body init k => do sorry


-- end

--   -- let


-- def Program.denote {eff : EffSig} {i o : AbiTp} (state := ProgramState.empty eff) (p : Program eff i o Tp.denote) :
--     Tp.denote i → CompM (Eff.Tau ⊕ Eff.Fail ⊕ eff.tag) (Tp.denote o) := match p with
--   | .define f k =>
--     let (state', id) := state.alloc f
--     Program.denote state' (k id)
--   | .main f =>
--     fun x => do
--       let initialState : EvalState eff := (state, ⟨i, o, x, f⟩)
--       CompM.loop (fun (heap, ⟨iT, oT, inp, k⟩) => do
--         match k inp with
--         | .lit tp v k => pure $ .inl $ ⟨heap, ⟨tp, oT, v, k⟩⟩

--       ) initialState




-- end Freigen.Ast
