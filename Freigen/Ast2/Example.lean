import Freigen.Ast2.Basic
import Freigen.ITree.Eutt

/-!
# A hand-reflected circuit and its soundness

A dry run for the reflector, with no metaprogramming: a source circuit — written in the plain,
**host-level** `Circuit` monad from `Ast2.Basic` (the author never sees `Tp`), with a helper
definition, a recursive definition, an `assert` effect, and a `hint` block at a host type — is
mirrored *by hand* into an `Expr` over the *coded* signatures, node for node, the way the
reflector would emit it, and the two are proved equivalent **for every choice of `bindEff`
interpreter**, with first-order effects left as ITree events:

```
∀ hB,  Eutt (Expr.denote (rB hB) (mainAst _)) (evalC hB mainSrc)
```

The two sides meet by hoisting the host `circuitEff` operation into the coded `CircE.Event`
ITree domain.  `CircB` still realizes the representable fragment of the host `circuitBlock`:
for the hint, `φ M := Tp.denote M` maps the code to the host operation at its denotation.
Only the host `bindEff` interpreter is restricted across `CircB_realizes`.

The proof shape is the template for reflector soundness:

* a non-recursive helper (`lam`) is sound **by `rfl`** — its denotation and the source's
  evaluation are *definitionally* the same tree;
* a recursive definition (`letrec`) is sound **up to `≈`, by induction** on its argument: one
  `mrec` unfolding (`interp_vis_call`) produces the `tau` that `≈` absorbs, and
  `eutt_bind_cong` stitches the induction hypothesis to the helper's equality;
* the main body composes by `eutt_bind_cong` + `eutt_refl` (everything after the recursive
  call is again definitionally equal).
-/

namespace Freigen
namespace Ast2
namespace Example

open ITree

/-! ## The source circuit

Written in the **`Circuit` monad** from `Ast2.Basic` — host-level `circuitEff`/`circuitBlock`:
an `assert : Bool → Unit` effect, and a `hint` block *indexed by an arbitrary host type*.  No
`Tp`, no coded signature, no target monad in sight. -/

/-- Assert a boolean. -/
abbrev Circuit.assert (b : Bool) : Circuit Unit :=
  Freek.eff (𝓔 := circuitEff) (𝓑 := circuitBlock) () b Freek.pure

/-- Helper definition: assert `x ≤ x²`, return `x²`. -/
def sqAssertSrc (x : Nat) : Circuit Nat := do
  let y := x * x
  let _ ← Circuit.assert (decide (x ≤ y))
  pure y

/-- Recursive definition: `Σ_{i=1..n} i²`, each square produced by the helper. -/
def sumSqSrc : Nat → Circuit Nat
  | 0 => pure 0
  | n + 1 => do
    let s ← sumSqSrc n
    let y ← sqAssertSrc (n + 1)
    pure (s + y)

/-- A source term exposing the `Nat.brecOn` shape Lean's equation compiler uses for natural
    recursive definitions over `Nat`.  This is for structural reflection theorems; source
    programs can still be written by equations. -/
def natBRecSource {α : Type} (base : Circuit α) (step : Nat → α → Circuit α) :
    Nat → Circuit α :=
  fun n => Nat.brecOn (motive := fun _ => Circuit α) n fun
    | 0, _ => base
    | n + 1, prev => Freek.bind prev.1 fun s => step (n + 1) s

/-- The base equation of `natBRecSource` is definitional. -/
theorem natBRecSource_zero {α : Type} (base : Circuit α) (step : Nat → α → Circuit α) :
    natBRecSource base step 0 = base := rfl

/-- The successor equation of `natBRecSource` is definitional. -/
theorem natBRecSource_succ {α : Type} (base : Circuit α) (step : Nat → α → Circuit α)
    (n : Nat) :
    natBRecSource base step (n + 1)
      = Freek.bind (natBRecSource base step n) fun s => step (n + 1) s := rfl

/-- Relate an equation-style primitive recursive source to the explicit `Nat.brecOn` source.
    The `base` and `step` are inferred from the generated equation lemmas at use sites. -/
theorem natBRecSource_eq_of_eqns {α : Type} {F : Nat → Circuit α}
    {base : Circuit α} {step : Nat → α → Circuit α}
    (hzero : F 0 = base)
    (hsucc : ∀ n, F (n + 1) = Freek.bind (F n) fun s => step (n + 1) s) :
    ∀ n, F n = natBRecSource base step n := by
  intro n
  induction n with
  | zero =>
      rw [hzero]
      rfl
  | succ n ih =>
      rw [hsucc n]
      rw [ih]
      rfl

/-- The circuit: sum of squares up to 3, passed through a `hint` block (at the *host type*
    `Nat`; the block recomputes the value), then asserted equal to the computed value. -/
def mainSrc : Circuit Nat := do
  let s ← sumSqSrc 3
  let h ← Circuit.hint (pure s)
  let _ ← Circuit.assert (h == s)
  pure h

/-! ## The reflector-side coded signatures, and the bridge

`CircE` is the coded first-order effect event signature.  `CircB` names the **representable
fragment** of `circuitBlock`'s (`Type`-many!) operations — one per `Tp` code, mapped by the
realization to the host operation at its denotation (`φ M := Tp.denote M`).  All payload
equations are `rfl`, so the `restrict`-ed interpreters compute definitionally. -/

abbrev CircE : EffSig := ⟨Unit, fun _ => .bool, fun _ => .unit⟩

abbrev CircB : BindSig := ⟨Tp, fun _ => .unit, fun t => t, fun _ => Unit, fun t _ => t⟩

/-- `CircB` realizes the representable fragment of `circuitBlock`: the coded operation `t : Tp`
    names the host hint at the type `t.denote M`. -/
def CircB_realizes : CircB.Realizes circuitBlock where
  φ M := Tp.denote M
  input_eq _ _ := rfl
  output_eq _ _ := rfl
  br_eq _ _ := rfl
  brTp_eq _ _ _ := rfl

/-! ## The hand-reflected AST

Node for node what a reflector should emit: the helper spills as a `lam`, the recursive
definition as a `letrec` (the source's structural `match` becomes `n == 0` / `ite` /
`selfCall (n - 1)`, and its call to the helper an `app` of the captured `lam` atom), host
literals become `natLit`s, host primitives become `bin` nodes, and the `bindEff` block is
carried verbatim as a sub-computation. -/

section Ast
variable {V : Tp → Type}

/-- The reflection of `sqAssertSrc` — the body of the `lam` bound to it. -/
def sqAssertAst (x : V .nat) : Expr CircE CircB V none .nat :=
  .bin .mul x x fun y =>
  .bin .le x y fun c =>
  .eff () c fun _ =>
  .ret y

/-- The reflection of `sumSqSrc` — the `letrec` body. -/
def sumSqAst (sq : V (.fn .nat .nat)) (n : V .nat) :
    Expr CircE CircB V (some (.nat, .nat)) .nat :=
  .natLit 0 fun z =>
  .bin .eq n z fun c =>
  .ite c
    (.ret z)
    (.natLit 1 fun one =>
     .bin .sub n one fun n' =>
     .selfCall n' fun s =>
     .app sq n fun y =>
     .bin .add s y fun r =>
     .ret r)
    fun v => .ret v

/-- The reflection of `mainSrc` — the whole closed program. -/
def mainAst : Closed CircE CircB .nat := fun _ =>
  .lam sqAssertAst fun sq =>
  .letrec (sumSqAst sq) fun sumSq =>
  .natLit 3 fun three =>
  .app sumSq three fun s =>
  .unitLit fun u =>
  .bindEff .nat u (fun _ => .ret s) fun h =>
  .bin .eq h s fun c =>
  .eff () c fun _ =>
  .ret h

end Ast

/-! ## Soundness, parametric in the `bindEff` interpreter -/

section Sound
variable (hB : circuitBlock.Interp CircE.Event EffSig.Event.arity)

/-- The base tree domain for this example: circuit effects are ITree events. -/
abbrev M : Type → Type := CompE CircE.Event EffSig.Event.arity

/-- Hoist the host circuit effect into the coded effect event domain. -/
abbrev evalEffC (e : circuitEff.ε) (i : circuitEff.𝓘 e) : M (circuitEff.𝓞 e) :=
  EffSig.trigger (𝓔 := CircE) e i

/-- The coded `bindEff` interpreter induced by the **host** one across the realization. -/
abbrev rB (hB : circuitBlock.Interp CircE.Event EffSig.Event.arity) :
    BindInterp CircB CircE.Event EffSig.Event.arity :=
  CircB_realizes.restrict hB

/-- Evaluate a user-level `Circuit` program in the tree domain, hoisting first-order effects as
    ITree events and interpreting only `bindEff`. -/
abbrev evalC (hB : circuitBlock.Interp CircE.Event EffSig.Event.arity) {α : Type}
    (p : Circuit α) : CompE CircE.Event EffSig.Event.arity α :=
  Freek.eval (𝓔 := circuitEff) (𝓑 := circuitBlock) evalEffC hB p

/-- The denoted helper: a base-domain Kleisli arrow (what the `lam` atom stands for). -/
def sqD : Nat → CompE CircE.Event EffSig.Event.arity Nat := fun x =>
  Expr.denote (rB hB) (sqAssertAst x)

/-- The denoted `letrec` body: a tree over the call-extended signature (what `mrec` ties). -/
def bd : Nat → CompE (CircE.Event ⊕ Nat) (callBr EffSig.Event.arity Nat) Nat := fun n =>
  Expr.denote (rB hB) (sumSqAst (sqD hB) n)

/-- **Helper soundness** — definitional: the denoted `lam` body *is* the evaluated source
    helper, for any `bindEff` interpreter. -/
theorem sq_sound (x : Nat) :
    sqD hB x = evalC hB (sqAssertSrc x) := rfl

/-- **Recursive-definition soundness**, by induction on the argument: the `mrec`-tied `letrec`
    body is `≈` (not `=` — each unfolding spends one `tau`) to the source's structural
    recursion, for any `bindEff` interpreter. -/
theorem sumSq_sound (n : Nat) :
    Eutt (mrec (bd hB) n) (evalC hB (sumSqSrc n)) := by
  induction n with
  | zero =>
    apply Eutt.of_eq
    show interp (bd hB) (ITree.bind (ITree.ret 0) fun v => ITree.ret v) = _
    rw [bind_ret, interp_ret]
    rfl
  | succ n ih =>
    -- One unfolding of the knot: `bd (n+1)` is *definitionally* a self-call `vis` followed by
    -- the helper's (`sumL`-embedded) computation; `interp` turns the call into a `tau`-guarded
    -- re-run of the body on `n`.
    have hunf : mrec (bd hB) (n + 1)
        = tau (ITree.bind (mrec (bd hB) n) fun s =>
            ITree.bind (sqD hB (n + 1)) fun y => ITree.ret (s + y)) := by
      show interp (bd hB)
          (ITree.bind
            (vis (Sum.inr n) fun (s : Nat) =>
              ITree.bind (sumL (sqD hB (n + 1))) fun y => ITree.ret (s + y))
            (fun v => ITree.ret v)) = _
      simp only [bind_vis, interp_vis_call, interp_bind, bind_assoc, bind_ret, interp_sumL,
                 interp_ret]
      rfl
    -- With `Freek.bind` computed by grafting, `eval` no longer distributes over a bind on an
    -- *opaque* prefix definitionally — `eval_bind` rewrites the source into bind form.
    have hsrc : evalC hB (sumSqSrc (n + 1))
        = ITree.bind (evalC hB (sumSqSrc n)) fun s =>
            ITree.bind (evalC hB (sqAssertSrc (n + 1))) fun y => ITree.ret (s + y) := by
      show Freek.eval (𝓔 := circuitEff) (𝓑 := circuitBlock) evalEffC hB
          (Freek.bind (sumSqSrc n) fun s =>
            Freek.bind (sqAssertSrc (n + 1)) fun y => Freek.pure (s + y)) = _
      rw [Freek.eval_bind]
      exact congrArg (ITree.bind (evalC hB (sumSqSrc n)))
        (funext fun s => Freek.eval_bind evalEffC hB _ _)
    rw [hunf, hsrc]
    exact eutt_tau_left (eutt_bind_cong ih fun s =>
      eutt_bind_cong (Eutt.of_eq (sq_sound hB (n + 1))) fun y => eutt_refl _)

/-- **Program soundness**: the hand-reflected AST and the source circuit are weakly bisimilar
    under *every* `bindEff` interpreter, with effects hoisted as ITree events.  Everything around the
    recursive call — the `lam`, the literals, the `bindEff` with its block, the final assert —
    is definitionally equal on both sides, so the proof is one `bind`-congruence around
    `sumSq_sound`. -/
theorem main_sound :
    Eutt (Expr.denote (rB hB) (mainAst _)) (evalC hB mainSrc) := by
  -- Split the source at the recursive call (`eval_bind`); the hint/assert legs are
  -- constructor-headed, so their binds graft and everything after is definitional.
  have hsrc : evalC hB mainSrc
      = ITree.bind (evalC hB (sumSqSrc 3)) fun s =>
          ITree.bind (hB Nat () fun _ => ITree.ret s) fun (h : Nat) =>
            ITree.bind (EffSig.trigger (𝓔 := CircE) () (h == s)) fun _ => ITree.ret h := by
    show Freek.eval (𝓔 := circuitEff) (𝓑 := circuitBlock) evalEffC hB
        (Freek.bind (sumSqSrc 3) fun s =>
          Freek.bind (Circuit.hint (pure s)) fun h =>
            Freek.bind (Circuit.assert (h == s)) fun _ => Freek.pure h) = _
    rw [Freek.eval_bind]
    exact congrArg (ITree.bind (evalC hB (sumSqSrc 3))) (funext fun s => rfl)
  rw [hsrc]
  exact eutt_bind_cong (sumSq_sound hB 3) fun s => eutt_refl _

/-! ## Top-down reflection: discovering the AST by `apply`

Instead of writing the AST and proving it sound after the fact, construct — for a given source
computation — *the pair* of an AST and its soundness proof, top-down: the AST component is a
metavariable, and each `apply` of a `reflect_*` lemma emits one AST node while consuming one
source node.  Two disciplines make the trace work:

* a **pure node binds a fresh atom together with its defining equation**
  (`∀ vc, vc = … → _`): after `intro`, every continuation metavariable is only ever applied to
  *variables*, so unification stays in the higher-order pattern fragment and `apply` keeps
  assigning continuations correctly;
* **value side-conditions** (an effect's input, a returned value must match the source's host
  value) are discharged by rewriting with the accumulated defining equations.

This is the manual prototype of the reflector's soundness-carrying walk. -/

/-- Reflect `pure`: emit `ret` on an atom whose defining equation matches the source value. -/
theorem reflect_ret {α : Tp} (v : Tp.denote M α) {v' : Tp.denote M α}
    (h : v = v') :
    Eutt (Expr.denote (rB hB)
        (.ret v : Expr CircE CircB (Tp.denote M) none α))
      (evalC hB (.pure v')) :=
  Eutt.of_eq (by rw [h]; rfl)

/-- Reflect a host primitive: emit a `bin` node binding a fresh atom `vc` with its defining
    equation; the source is untouched (`t` is arbitrary — a pure step costs nothing). -/
theorem reflect_bin {a b c α : Tp} (o : Bin a b c)
    (va : Tp.denote M a) (vb : Tp.denote M b)
    {k : Tp.denote M c → Expr CircE CircB (Tp.denote M) none α}
    {t : M (Tp.denote M α)}
    (ih : ∀ vc, vc = o.denote va vb → Eutt (Expr.denote (rB hB) (k vc)) t) :
    Eutt (Expr.denote (rB hB) (.bin o va vb k)) t :=
  ih _ rfl

/-- Reflect `eff e i' ks` (with the grafting `bind`, every source effect arrives with its
    continuation already attached): emit an `eff` node — its input atom must equal the source's
    input (side condition `hi`, discharged from the defining equations) — and continue
    pointwise under the bound result. -/
theorem reflect_eff {α : Tp} (e : CircE.ε) (i : Tp0.denote (CircE.𝓘 e))
    {i' : Tp0.denote (CircE.𝓘 e)}
    {k : Tp0.denote (CircE.𝓞 e) →
      Expr CircE CircB (Tp.denote M) none α}
    {ks : Tp0.denote (CircE.𝓞 e) → Circuit (Tp.denote M α)}
    (hi : i = i')
    (ih : ∀ o, Eutt (Expr.denote (rB hB) (k o)) (evalC hB (ks o))) :
    Eutt (Expr.denote (rB hB) (.eff e i k)) (evalC hB (Freek.eff e i' ks)) := by
  subst hi
  show Eutt (ITree.bind (EffSig.trigger (𝓔 := CircE) e i) fun o => Expr.denote (rB hB) (k o))
            (ITree.bind (EffSig.trigger (𝓔 := CircE) e i) fun o => evalC hB (ks o))
  exact eutt_bind_cong (eutt_refl _) ih

/-- `sqAssertSrc`, reflected **top-down**: the AST component is the `_` — it is *discovered*
    by the `apply`-trace along the source circuit, one lemma per source node. -/
def sqAssertReflected (x : Nat) :
    { e : Expr CircE CircB (Tp.denote M) none .nat //
      Eutt (Expr.denote (rB hB) e) (evalC hB (sqAssertSrc x)) } :=
  ⟨_, by
    unfold sqAssertSrc
    apply reflect_bin hB .mul x x    -- y := x * x
    intro y hy
    apply reflect_bin hB .le x y     -- c := decide (x ≤ y)
    intro c hc
    apply reflect_eff hB () c        -- assert c   (side goal: c = decide (x ≤ x*x))
    · rw [hy] at hc
      exact hc
    · intro o
      apply reflect_ret hB y         -- return y   (side goal: y = x*x)
      exact hy⟩

/-- The trace reconstructs exactly the hand-written AST. -/
example (x : Nat) : (sqAssertReflected hB x).1 = sqAssertAst x := rfl

/-! ## Third style: pack-returning combinators

Same top-down trace, but the `reflect_*` *theorems* become *functions returning packed
`(AST, proof)` values*: each `apply` now invokes a function whose result literally contains the
emitted node (`⟨.bin o va vb (fun vc => (k vc).1), …⟩`) — the term component is built by the
combinators themselves, not reconstructed by the unifier from a proof trace.

The intermediate objects are richer than `Expr`/`Eutt`, as they must be:

* a continuation argument is a *function* `∀ vc, Reflection … m` — syntax total in the bound
  atom, so the data component never depends on a proof;
* the atom's defining equation therefore cannot ride along as a hypothesis *before* the data —
  it moves *inside* the property: `Reflection Φ m` carries its soundness **conditionally on
  `Φ`**, the conjunction of all pending defining equations, and each `bin` extends `Φ` for its
  continuation (`Φ ∧ vc = …`) while discharging it at the knot with `⟨hΦ, rfl⟩`;
* value side-conditions (`eff` input, returned value) are `Φ → _ = _` functions, closed by
  projecting and rewriting with the accumulated equations. -/

/-- A reflection of source `m`, **conditional on pending defining equations `Φ`**: an AST
    together with a soundness proof that may assume `Φ`. -/
def Reflection (Φ : Prop) (α : Tp)
    (m : Circuit (Tp.denote M α)) : Type :=
  { e : Expr CircE CircB (Tp.denote M) none α //
    Φ → Eutt (Expr.denote (rB hB) e) (evalC hB m) }

/-- Reflect `pure`: the pack's node is `ret v`; the value condition may assume `Φ`. -/
def Reflection.ret {Φ : Prop} {α : Tp} (v : Tp.denote M α)
    {v' : Tp.denote M α} (h : Φ → v = v') :
    Reflection hB Φ α (.pure v') :=
  ⟨.ret v, fun hΦ => Eutt.of_eq (by rw [h hΦ]; rfl)⟩

/-- Reflect a host primitive: the pack's node is `bin o va vb` with the continuation's syntax
    components spliced in; the continuation works under the *extended* equation context
    `Φ ∧ vc = o.denote va vb`, discharged here at the actual value with `⟨hΦ, rfl⟩`. -/
def Reflection.bin {Φ : Prop} {a b c α : Tp} (o : Bin a b c)
    (va : Tp.denote M a) (vb : Tp.denote M b)
    {m : Circuit (Tp.denote M α)}
    (k : ∀ vc, Reflection hB (Φ ∧ vc = o.denote va vb) α m) :
    Reflection hB Φ α m :=
  ⟨.bin o va vb fun vc => (k vc).1, fun hΦ => (k _).2 ⟨hΦ, rfl⟩⟩

/-- Reflect `eff e i' ks`: the pack's node is `eff e i` around the continuation packs;
    the input condition `i = i'` may assume `Φ`. -/
def Reflection.eff {Φ : Prop} {α : Tp} (e : CircE.ε) (i : Tp0.denote (CircE.𝓘 e))
    {i' : Tp0.denote (CircE.𝓘 e)} (hi : Φ → i = i')
    {ks : Tp0.denote (CircE.𝓞 e) → Circuit (Tp.denote M α)}
    (k : ∀ o, Reflection hB Φ α (ks o)) :
    Reflection hB Φ α (Freek.eff e i' ks) :=
  ⟨.eff e i fun o => (k o).1, fun hΦ => by
    rw [← hi hΦ]
    show Eutt (ITree.bind (EffSig.trigger (𝓔 := CircE) e i) fun o => Expr.denote (rB hB) ((k o).1))
              (ITree.bind (EffSig.trigger (𝓔 := CircE) e i) fun o => evalC hB (ks o))
    exact eutt_bind_cong (eutt_refl _) fun o => (k o).2 hΦ⟩

/-- `sqAssertSrc` reflected in the third style: the same `apply`-trace, but every `apply` calls
    a pack-returning *function* — the goal is `Type`-valued (data!), and the AST is assembled
    by the combinators, node by node, as the trace walks the source. -/
def sqAssertReflected' (x : Nat) :
    Reflection hB True .nat (sqAssertSrc x) := by
  unfold sqAssertSrc
  apply Reflection.bin hB .mul x x    -- y := x * x
  intro y
  apply Reflection.bin hB .le x y     -- c := decide (x ≤ y)
  intro c
  apply Reflection.eff hB () c        -- assert c
  · rintro ⟨⟨-, hy⟩, hc⟩                 --   side goal: Φ → c = decide (x ≤ x*x)
    rw [hy] at hc
    exact hc
  · intro o
    apply Reflection.ret hB y         -- return y
    rintro ⟨⟨-, hy⟩, -⟩                  --   side goal: Φ → y = x*x
    exact hy

/-- The third style, too, reconstructs exactly the hand-written AST. -/
example (x : Nat) : (sqAssertReflected' hB x).1 = sqAssertAst x := rfl

/-! ## Tying the recursion knot

The reflect lemma for structural `Nat` recursion — the reusable core that `sumSq_sound` proved
by hand.  It relates the **`mrec`-tied `letrec` body** to a source recursive function, given:

* two **AST-side** facts about the body denotation `bd` — it computes `base` at `0`, and at
  `n+1` performs *one* guarded self-call (the `tau`) whose result feeds a base-domain
  continuation `cont n` (this is exactly the shape the `letrec`/`selfCall` scaffolding denotes
  to, via `interp_vis_call`/`interp_sumL`);
* two **source-side** facts — the source folds the same way (`hsrcBase`/`hsrcStep`, discharged
  from `eval`/`eval_bind`).

The `tau` each unfolding spends is absorbed by `≈`.  Everything specific to *this* recursion —
the step continuation `cont` — is supplied as an approach-#3 reflection pack, so applying the
lemma leaves the recursion's AST to be *derived*, not guessed. -/
theorem reflect_natRec {R : Type}
    (bd : Nat → CompE (CircE.Event ⊕ Nat) (callBr EffSig.Event.arity R) R) (src : Nat → M R)
    (base : M R) (cont : Nat → R → M R)
    (hbase : Eutt (mrec bd 0) base)
    (hstep : ∀ n, Eutt (mrec bd (n + 1)) (tau (ITree.bind (mrec bd n) (cont n))))
    (hsrcBase : Eutt (src 0) base)
    (hsrcStep : ∀ n, Eutt (src (n + 1)) (ITree.bind (src n) (cont n))) :
    ∀ n, Eutt (mrec bd n) (src n) := by
  intro n
  induction n with
  | zero => exact (hbase).trans hsrcBase.symm
  | succ n ih =>
      refine (hstep n).trans ?_
      exact (eutt_tau_left (eutt_bind_cong ih fun s => eutt_refl _)).trans (hsrcStep n).symm

/-- Reflect a **function application** `bind (fSrc x) ks`: emit an `app` node on the function
    atom `f` (whose per-argument soundness `hf` witnesses that `f x` reflects the helper call),
    then continue pointwise.  The approach-#3 combinator for a `letrec`-helper call. -/
def Reflection.app {Φ : Prop} {α aT bT : Tp} (f : Tp.denote M (.fn aT bT))
    (x : Tp.denote M aT)
    {fSrc : Tp.denote M aT → Circuit (Tp.denote M bT)}
    (hf : Φ → Eutt (f x) (evalC hB (fSrc x)))
    {ks : Tp.denote M bT → Circuit (Tp.denote M α)}
    (k : ∀ o, Reflection hB Φ α (ks o)) :
    Reflection hB Φ α (Freek.bind (fSrc x) ks) :=
  ⟨.app f x fun o => (k o).1, fun hΦ => by
    have hexp : evalC hB (Freek.bind (fSrc x) ks)
        = ITree.bind (evalC hB (fSrc x)) fun o => evalC hB (ks o) :=
      Freek.eval_bind (𝓔 := circuitEff) (𝓑 := circuitBlock) evalEffC hB (fSrc x) ks
    show Eutt (ITree.bind (f x) fun o => Expr.denote (rB hB) ((k o).1))
              (evalC hB (Freek.bind (fSrc x) ks))
    rw [hexp]
    exact eutt_bind_cong (hf hΦ) fun o => (k o).2 hΦ⟩

/-- The **step continuation** of `sumSqSrc`, apply-derived (approach #3): reflect
    `do let y ← sqAssertSrc (n+1); pure (s + y)` — an `app` of the helper (sound by
    `sq_sound`) then a `bin .add` and `ret`.  Its denotation is the `cont` the knot lemma
    consumes. -/
def sumSqStep (n s : Nat) :
    Reflection hB True .nat (Freek.bind (sqAssertSrc (n + 1)) fun y => pure (s + y)) := by
  refine Reflection.app hB (aT := .nat) (bT := .nat) (sqD hB) (n + 1)
    (fSrc := sqAssertSrc) (fun _ => Eutt.of_eq (sq_sound hB (n + 1))) ?_
  intro y
  apply Reflection.bin hB .add s y
  intro r
  apply Reflection.ret hB r
  rintro ⟨-, hr⟩
  exact hr

/-- The derived step denotes to exactly the base-domain continuation `sumSq_sound` used — the
    apply-derived pack and the hand unfolding meet. -/
theorem sumSqStep_denote (n s : Nat) :
    Expr.denote (rB hB) (sumSqStep hB n s).1
      = ITree.bind (sqD hB (n + 1)) fun y => ITree.ret (s + y) := rfl

/-- **`sumSqSrc` reflected via the knot lemma.**  The recursion's soundness, re-established
    principledly: `reflect_natRec` supplies the induction/`tau`-absorption once; its `cont` is
    the *apply-derived* `sumSqStep`; the two body facts are the definitional `letrec`/`selfCall`
    unfoldings, and the source facts come from `eval_bind`. -/
theorem sumSqRec : ∀ n, Eutt (mrec (bd hB) n) (evalC hB (sumSqSrc n)) := by
  apply reflect_natRec (bd hB) (fun n => evalC hB (sumSqSrc n)) (ITree.ret 0)
    (fun n s => ITree.bind (sqD hB (n + 1)) fun y => ITree.ret (s + y))
  · -- hbase: the body at 0 computes `ret 0`
    apply Eutt.of_eq
    show interp (bd hB) (ITree.bind (ITree.ret 0) fun v => ITree.ret v) = _
    rw [bind_ret, interp_ret]
  · -- hstep: one guarded self-call, result fed to the step continuation
    intro n
    apply Eutt.of_eq
    show interp (bd hB)
        (ITree.bind (vis (Sum.inr n) fun (s : Nat) =>
          ITree.bind (sumL (sqD hB (n + 1))) fun y => ITree.ret (s + y))
          (fun v => ITree.ret v)) = _
    simp only [bind_vis, interp_vis_call, interp_bind, bind_assoc, bind_ret, interp_sumL,
               interp_ret]
    rfl
  · -- hsrcBase: `eval (pure 0) = ret 0`
    exact Eutt.of_eq rfl
  · -- hsrcStep: the source folds through the step, matched by the *apply-derived* step pack
    intro n
    have hexp : evalC hB (sumSqSrc (n + 1))
        = ITree.bind (evalC hB (sumSqSrc n)) fun s =>
            evalC hB (Freek.bind (sqAssertSrc (n + 1)) fun y => pure (s + y)) :=
      Freek.eval_bind (𝓔 := circuitEff) (𝓑 := circuitBlock) evalEffC hB (sumSqSrc n)
        (fun s => Freek.bind (sqAssertSrc (n + 1)) fun y => Freek.pure (s + y))
    rw [hexp]
    refine eutt_bind_cong (eutt_refl _) fun s => ?_
    rw [← sumSqStep_denote hB n s]
    exact ((sumSqStep hB n s).2 True.intro).symm

/-! ## A constructive `Reflection` for recursion

`reflect_natRec` above is the *engine* (a plain `≈` statement); here it is repackaged so it
fits the apply-style.  The pieces:

* **`ReflectionS`** — a reflection at the *recursion slot* `some (.nat, R)`: a call-free body
  fragment `e` reflecting a source `m`, carrying the **equality** `denote e = sumL (eval m)`
  (call-free ⇒ no `tau`, so `=` not just `≈`).  Combinators `ret`/`bin`/`app` mirror the
  none-slot ones, discharged by the `sumL` monad-morphism laws.
* **`RecReflection`** — the reflection of a whole recursive function `F : Nat → Circuit R`: the
  `letrec` **body** together with the proof that its `mrec` knot is `≈ eval ∘ F`.
* **`Reflection.natRec`** — the constructive combinator for `natBRecSource`, the explicit
  `Nat.brecOn`-shaped source recursor that natural recursive definitions can be related to by
  their generated equations.  Given a reflection of the base and a reflection of the step body,
  it **emits the natural `letrec` body** (`n==0 ? base : selfCall (n-1) >>= step`) and proves it
  reflects — the induction/`tau`-absorption handled once by `reflect_natRec`.  Applying it
  leaves the base and step *bodies* as reflection goals, apply-derivable like any others.
* **`Reflection.letrec`** — uses a `RecReflection` at a call site (`bind (F N) ks`): emits
  `letrec … (app · N …)` and continues. -/

/-- A reflection of source `m` at the **recursion slot** — a call-free body fragment, sound as
    an *equality* against the `sumL`-embedded source. -/
def ReflectionS (Φ : Prop) (R α : Tp) (m : Circuit (Tp.denote M α)) : Type :=
  { e : Expr CircE CircB (Tp.denote M) (some (.nat, R)) α //
    Φ → Expr.denote (rB hB) e = sumL (evalC hB m) }

/-- Reflect `pure` at the recursion slot. -/
def ReflectionS.ret {Φ : Prop} {R α : Tp} (v : Tp.denote M α)
    {v' : Tp.denote M α} (h : Φ → v = v') :
    ReflectionS hB Φ R α (.pure v') :=
  ⟨.ret v, fun hΦ => by rw [h hΦ]; exact (sumL_ret v').symm⟩

/-- Reflect a host primitive at the recursion slot (the source is untouched). -/
def ReflectionS.bin {Φ : Prop} {R a b c α : Tp} (o : Bin a b c)
    (va : Tp.denote M a) (vb : Tp.denote M b)
    {m : Circuit (Tp.denote M α)}
    (k : ∀ vc, ReflectionS hB (Φ ∧ vc = o.denote va vb) R α m) :
    ReflectionS hB Φ R α m :=
  ⟨.bin o va vb fun vc => (k vc).1, fun hΦ => (k _).2 ⟨hΦ, rfl⟩⟩

/-- Reflect a helper application at the recursion slot (`sumL`-lifted). -/
def ReflectionS.app {Φ : Prop} {R α aT bT : Tp} (f : Tp.denote M (.fn aT bT))
    (x : Tp.denote M aT)
    {fSrc : Tp.denote M aT → Circuit (Tp.denote M bT)}
    (hf : Φ → f x = evalC hB (fSrc x))
    {ks : Tp.denote M bT → Circuit (Tp.denote M α)}
    (k : ∀ o, ReflectionS hB Φ R α (ks o)) :
    ReflectionS hB Φ R α (Freek.bind (fSrc x) ks) :=
  ⟨.app f x fun o => (k o).1, fun hΦ => by
    have hexp : evalC hB (Freek.bind (fSrc x) ks)
        = ITree.bind (evalC hB (fSrc x)) fun o => evalC hB (ks o) :=
      Freek.eval_bind (𝓔 := circuitEff) (𝓑 := circuitBlock) evalEffC hB (fSrc x) ks
    show ITree.bind (sumL (f x)) (fun o => Expr.denote (rB hB) ((k o).1))
        = sumL (evalC hB (Freek.bind (fSrc x) ks))
    rw [hexp, hf hΦ, sumL_bind]
    exact congrArg (ITree.bind (sumL (evalC hB (fSrc x))))
      (funext fun o => (k o).2 hΦ)⟩

/-- A reflection of a structurally-recursive function `F : Nat → Circuit R`: the `letrec`
    body, sound (`≈`) against `eval ∘ F` under the `mrec` knot. -/
def RecReflection (Φ : Prop) (R : Tp) (F : Nat → Circuit (Tp.denote M R)) : Type :=
  { body : Tp.denote M .nat →
      Expr CircE CircB (Tp.denote M) (some (.nat, R)) R //
    Φ → ∀ n, Eutt (mrec (fun s => Expr.denote (rB hB) (body s)) n) (evalC hB (F n)) }

/-- Reindex a recursive reflection along pointwise equality of source functions. -/
def RecReflection.congr {Φ : Prop} {R : Tp}
    {F G : Nat → Circuit (Tp.denote M R)}
    (rec : RecReflection hB Φ R F) (h : Φ → ∀ n, G n = F n) :
    RecReflection hB Φ R G :=
  ⟨rec.1, fun hΦ n => by
    rw [h hΦ n]
    exact rec.2 hΦ n⟩

/-- The natural `letrec` body for structural `Nat` recursion:
    `n == 0 ? base : selfCall (n-1) >>= step`. -/
def natRecBody {R : Tp}
    (baseE : Expr CircE CircB (Tp.denote M) (some (.nat, R)) R)
    (stepE : Nat → Tp.denote M R →
      Expr CircE CircB (Tp.denote M) (some (.nat, R)) R)
    (m : Nat) : Expr CircE CircB (Tp.denote M) (some (.nat, R)) R :=
  .natLit 0 fun z =>
  .bin .eq m z fun c =>
  .ite c baseE
    (.natLit 1 fun one => .bin .sub m one fun m' => .selfCall m' fun s => stepE m s)
    fun v => .ret v

/-- Body-at-`0` denotes to the base branch (the `n==0` guard reduces). -/
theorem natRecBody_zero {R : Tp} (baseE) (stepE) :
    Expr.denote (rB hB) (natRecBody (R := R) baseE stepE 0)
      = ITree.bind (Expr.denote (rB hB) baseE) fun v => ITree.ret v := rfl

/-- Body-at-`n+1` denotes to one self-call feeding the step branch. -/
theorem natRecBody_succ {R : Tp} (baseE) (stepE) (n : Nat) :
    Expr.denote (rB hB) (natRecBody (R := R) baseE stepE (n + 1))
      = ITree.bind (vis (Sum.inr n) fun s =>
          Expr.denote (rB hB) (stepE (n + 1) s)) fun v => ITree.ret v := rfl

/-- **The constructive knot combinator for the explicit source recursor.**  For
    `natBRecSource`, emit the natural `letrec` body (`natRecBody`) from reflections of the base
    and step *bodies*, and prove it reflects — the induction/`tau`-absorption delegated to
    `reflect_natRec`. -/
def Reflection.natBRec {Φ : Prop} {R : Tp}
    (base : Circuit (Tp.denote M R))
    (step : Nat → Tp.denote M R → Circuit (Tp.denote M R))
    (base0 : ReflectionS hB Φ R R base)
    (stepBody : ∀ (m : Nat) (s : Tp.denote M R),
      ReflectionS hB Φ R R (step m s)) :
    RecReflection hB Φ R (natBRecSource base step) :=
  ⟨natRecBody base0.1 fun m s => (stepBody m s).1,
   fun hΦ => by
    refine reflect_natRec _ (fun n => evalC hB (natBRecSource base step n))
      (evalC hB base)
      (fun n t => evalC hB (step (n + 1) t)) ?_ ?_ (eutt_refl _) ?_
    · -- hbase: body at 0 = base ⇒ mrec = eval base
      apply Eutt.of_eq
      rw [show mrec (fun s => Expr.denote (rB hB)
            (natRecBody base0.1 (fun m s => (stepBody m s).1) s)) 0
          = interp _ (ITree.bind (Expr.denote (rB hB) base0.1) fun v => ITree.ret v)
        from congrArg (interp _) (natRecBody_zero hB _ _)]
      rw [base0.2 hΦ, interp_bind, interp_sumL]
      simp only [interp_ret]
      exact bind_ret_right _
    · -- hstep: body at n+1 = one self-call feeding the reflected step
      intro n
      apply Eutt.of_eq
      rw [show mrec (fun s => Expr.denote (rB hB)
            (natRecBody base0.1 (fun m s => (stepBody m s).1) s)) (n + 1)
          = interp _ (ITree.bind (vis (Sum.inr n) fun s =>
              Expr.denote (rB hB) ((stepBody (n + 1) s).1)) fun v => ITree.ret v)
        from congrArg (interp _) (natRecBody_succ hB _ _ n)]
      rw [bind_vis, interp_vis_call, interp_bind]
      refine congrArg tau (congrArg (ITree.bind (mrec _ n)) (funext fun t => ?_))
      rw [(stepBody (n + 1) t).2 hΦ, interp_bind, interp_sumL]
      simp only [interp_ret]
      exact bind_ret_right _
    · -- hsrcStep
      intro n
      apply Eutt.of_eq
      exact Freek.eval_bind (𝓔 := circuitEff) (𝓑 := circuitBlock) evalEffC hB
        (natBRecSource base step n) (fun s => step (n + 1) s)⟩

/-- **The constructive knot combinator.**  Given a source function that has been identified as
    a `natBRecSource`, emit the natural `letrec` body (`natRecBody`) from reflections of the
    base and step *bodies*, and prove it reflects.  The base and step may be inferred from a
    generic `natBRecSource_eq_of_eqns` proof over the source's generated equations. -/
def Reflection.natRec {Φ : Prop} {R : Tp}
    (F : Nat → Circuit (Tp.denote M R))
    {base : Circuit (Tp.denote M R)}
    {step : Nat → Tp.denote M R → Circuit (Tp.denote M R)}
    (base0 : ReflectionS hB Φ R R base)
    (stepBody : ∀ (m : Nat) (s : Tp.denote M R),
      ReflectionS hB Φ R R (step m s))
    (hshape : Φ → ∀ n, F n = natBRecSource base step n) :
    RecReflection hB Φ R F :=
  RecReflection.congr hB (Reflection.natBRec hB base step base0 stepBody) hshape

/-- Reflect a **recursive call site** `bind (F N) ks` from a `RecReflection` of `F`: emit
    `letrec` (binding the recursive function), `app` it to `N`, and continue.  This is where the
    apply-derived recursion pack plugs into an ordinary trace. -/
def Reflection.letrec {Φ : Prop} {R α : Tp}
    {F : Nat → Circuit (Tp.denote M R)} (Frec : RecReflection hB Φ R F)
    (N : Nat) {ks : Tp.denote M R → Circuit (Tp.denote M α)}
    (k : ∀ s, Reflection hB Φ α (ks s)) :
    Reflection hB Φ α (Freek.bind (F N) ks) :=
  ⟨.letrec Frec.1 fun f => .app f N fun s => (k s).1, fun hΦ => by
    have hexp : evalC hB (Freek.bind (F N) ks)
        = ITree.bind (evalC hB (F N)) fun s => evalC hB (ks s) :=
      Freek.eval_bind (𝓔 := circuitEff) (𝓑 := circuitBlock) evalEffC hB (F N) ks
    show Eutt (ITree.bind (mrec (fun s => Expr.denote (rB hB) (Frec.1 s)) N)
          fun s => Expr.denote (rB hB) ((k s).1))
        (evalC hB (Freek.bind (F N) ks))
    rw [hexp]
    exact eutt_bind_cong (Frec.2 hΦ N) fun s => (k s).2 hΦ⟩

/-! ## Apply-deriving the recursion

`sumSqSrc` reflected through the constructive combinator: `apply Reflection.natRec` emits the
`letrec` body and leaves the base and step *bodies* as `ReflectionS` goals, discharged by the
`ret`/`bin`/`app` combinators — a trace that walks the source recursion, no hand-written body. -/
def sumSqRecPack : RecReflection hB True .nat sumSqSrc := by
  refine Reflection.natRec hB (R := .nat) sumSqSrc
    (base := ?baseSrc) (step := ?stepSrc) ?base ?step ?shape
  case base =>                     -- base branch: `pure 0`
    show ReflectionS hB True .nat .nat (pure 0)
    exact ReflectionS.ret hB 0 (fun _ => rfl)
  case step =>                     -- step branch: ad-hoc helper atom; bin add; ret
    intro m s
    show ReflectionS hB True .nat .nat
      (Freek.bind (sqAssertSrc m) fun y => pure (s + y))
    refine ReflectionS.app hB (aT := .nat) (bT := .nat)
      (fun x => evalC hB (sqAssertSrc x)) m (fSrc := sqAssertSrc) (fun _ => rfl) ?_
    intro y
    apply ReflectionS.bin hB .add s y
    intro r
    apply ReflectionS.ret hB r
    rintro ⟨-, hr⟩
    exact hr
  case shape =>
    intro _
    exact natBRecSource_eq_of_eqns sumSqSrc.eq_1 sumSqSrc.eq_2

/-- The apply-derived recursion body's *step* matches the hand-written one node-for-node (the
    helper atom `sq` instantiated to its denotation): the derived and hand `selfCall`/`app`/`bin`
    scaffolding agree.  (The bases differ only cosmetically — `.ret 0` vs a `natLit`-bound `0`.) -/
example (m : Nat) :
    Expr.denote (rB hB) ((sumSqRecPack hB).1 m)
      = Expr.denote (rB hB) (sumSqAst (sqD hB) m) := rfl

/-- `sumSqRecPack` re-establishes the recursion soundness through the constructive combinator —
    the derived body's `mrec` knot is `≈ eval ∘ sumSqSrc`. -/
example (n : Nat) :
    Eutt (mrec (fun s => Expr.denote (rB hB) ((sumSqRecPack hB).1 s)) n)
      (evalC hB (sumSqSrc n)) :=
  (sumSqRecPack hB).2 True.intro n

end Sound

end Example
end Ast2
end Freigen
