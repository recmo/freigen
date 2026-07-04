import Freigen.Ast2.Basic
import Freigen.ITree.Eutt

/-!
# A hand-reflected circuit and its soundness

A dry run for the reflector, with no metaprogramming: a source circuit — written in the plain,
**host-level** `Circuit` monad from `Ast2.Basic` (the author never sees `Tp`), with a helper
definition, a recursive definition, an `assert` effect, and a `hint` block at a host type — is
mirrored *by hand* into an `Expr` over the *coded* signatures, node for node, the way the
reflector would emit it, and the two are proved equivalent **for every choice of host effect
and `bindEff` interpreters**:

```
∀ ε br hE hB,  Eutt (Expr.denote (rE hE) (rB hB) (mainAst _)) (evalC hE hB mainSrc)
```

The two sides meet through the **signature bridge**: the coded `CircE`/`CircB` realize the
representable fragments of the host `circuitEff`/`circuitBlock` (`Realizes` — an operation-name
map `φ` with, here, `rfl` payload equations; for the hint, `φ M := Tp.denote M` maps the code
to the host operation at its denotation).  The statement quantifies over **host** interpreters,
and the AST denotes under their `Realizes.restrict`-ions.

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

/-- The circuit: sum of squares up to 3, passed through a `hint` block (at the *host type*
    `Nat`; the block recomputes the value), then asserted equal to the computed value. -/
def mainSrc : Circuit Nat := do
  let s ← sumSqSrc 3
  let h ← Circuit.hint (pure s)
  let _ ← Circuit.assert (h == s)
  pure h

/-! ## The reflector-side coded signatures, and the bridge

`CircE` names `circuitEff`'s single operation; `CircB` names the **representable fragment** of
`circuitBlock`'s (`Type`-many!) operations — one per `Tp` code, mapped by the realization to
the host operation at its denotation (`φ M := Tp.denote M`).  All payload equations are `rfl`,
so the `restrict`-ed interpreters compute definitionally. -/

abbrev CircE : EffSig := ⟨Unit, fun _ => .bool, fun _ => .unit⟩

abbrev CircB : BindSig := ⟨Tp, fun _ => .unit, fun t => t, fun _ => Unit, fun t _ => t⟩

/-- `CircE` realizes `circuitEff` (on the nose — `φ` is the identity on the one operation). -/
def CircE_realizes : CircE.Realizes circuitEff where
  φ _ := id
  input_eq _ _ := rfl
  output_eq _ _ := rfl

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

/-! ## Soundness, parametric in the interpreters -/

section Sound
variable {ε : Type} {br : ε → Type}
variable (hE : circuitEff.Interp ε br) (hB : circuitBlock.Interp ε br)

/-- The coded interpreters induced by the **host** ones across the realizations — what the
    reflected AST denotes under. -/
abbrev rE (hE : circuitEff.Interp ε br) : EffInterp CircE ε br := CircE_realizes.restrict hE

/-- See `rE`. -/
abbrev rB (hB : circuitBlock.Interp ε br) : BindInterp CircB ε br := CircB_realizes.restrict hB

/-- Evaluate a user-level `Circuit` program in the tree domain under the host interpreters
    (the coded signatures never appear on this side). -/
abbrev evalC (hE : circuitEff.Interp ε br) (hB : circuitBlock.Interp ε br) {α : Type}
    (p : Circuit α) : CompE ε br α :=
  Freek.eval (𝓔 := circuitEff) (𝓑 := circuitBlock) hE hB p

/-- The denoted helper: a base-domain Kleisli arrow (what the `lam` atom stands for). -/
def sqD : Nat → CompE ε br Nat := fun x => Expr.denote (rE hE) (rB hB) (sqAssertAst x)

/-- The denoted `letrec` body: a tree over the call-extended signature (what `mrec` ties). -/
def bd : Nat → CompE (ε ⊕ Nat) (callBr br Nat) Nat := fun n =>
  Expr.denote (rE hE) (rB hB) (sumSqAst (sqD hE hB) n)

/-- **Helper soundness** — definitional: the denoted `lam` body *is* the evaluated source
    helper, for any interpreters. -/
theorem sq_sound (x : Nat) :
    sqD hE hB x = evalC hE hB (sqAssertSrc x) := rfl

/-- **Recursive-definition soundness**, by induction on the argument: the `mrec`-tied `letrec`
    body is `≈` (not `=` — each unfolding spends one `tau`) to the source's structural
    recursion, for any interpreters. -/
theorem sumSq_sound (n : Nat) :
    Eutt (mrec (bd hE hB) n) (evalC hE hB (sumSqSrc n)) := by
  induction n with
  | zero =>
    apply Eutt.of_eq
    show interp (bd hE hB) (ITree.bind (ITree.ret 0) fun v => ITree.ret v) = _
    rw [bind_ret, interp_ret]
    rfl
  | succ n ih =>
    -- One unfolding of the knot: `bd (n+1)` is *definitionally* a self-call `vis` followed by
    -- the helper's (`sumL`-embedded) computation; `interp` turns the call into a `tau`-guarded
    -- re-run of the body on `n`.
    have hunf : mrec (bd hE hB) (n + 1)
        = tau (ITree.bind (mrec (bd hE hB) n) fun s =>
            ITree.bind (sqD hE hB (n + 1)) fun y => ITree.ret (s + y)) := by
      show interp (bd hE hB)
          (ITree.bind
            (vis (Sum.inr n) fun (s : Nat) =>
              ITree.bind (sumL (sqD hE hB (n + 1))) fun y => ITree.ret (s + y))
            (fun v => ITree.ret v)) = _
      simp only [bind_vis, interp_vis_call, interp_bind, bind_assoc, bind_ret, interp_sumL,
                 interp_ret]
      rfl
    -- With `Freek.bind` computed by grafting, `eval` no longer distributes over a bind on an
    -- *opaque* prefix definitionally — `eval_bind` rewrites the source into bind form.
    have hsrc : evalC hE hB (sumSqSrc (n + 1))
        = ITree.bind (evalC hE hB (sumSqSrc n)) fun s =>
            ITree.bind (evalC hE hB (sqAssertSrc (n + 1))) fun y => ITree.ret (s + y) := by
      show Freek.eval (𝓔 := circuitEff) (𝓑 := circuitBlock) hE hB
          (Freek.bind (sumSqSrc n) fun s =>
            Freek.bind (sqAssertSrc (n + 1)) fun y => Freek.pure (s + y)) = _
      rw [Freek.eval_bind]
      exact congrArg (ITree.bind (evalC hE hB (sumSqSrc n)))
        (funext fun s => Freek.eval_bind hE hB _ _)
    rw [hunf, hsrc]
    exact eutt_tau_left (eutt_bind_cong ih fun s =>
      eutt_bind_cong (Eutt.of_eq (sq_sound hE hB (n + 1))) fun y => eutt_refl _)

/-- **Program soundness**: the hand-reflected AST and the source circuit are weakly bisimilar
    under *every* effect interpreter and *every* `bindEff` interpreter.  Everything around the
    recursive call — the `lam`, the literals, the `bindEff` with its block, the final assert —
    is definitionally equal on both sides, so the proof is one `bind`-congruence around
    `sumSq_sound`. -/
theorem main_sound :
    Eutt (Expr.denote (rE hE) (rB hB) (mainAst _)) (evalC hE hB mainSrc) := by
  -- Split the source at the recursive call (`eval_bind`); the hint/assert legs are
  -- constructor-headed, so their binds graft and everything after is definitional.
  have hsrc : evalC hE hB mainSrc
      = ITree.bind (evalC hE hB (sumSqSrc 3)) fun s =>
          ITree.bind (hB Nat () fun _ => ITree.ret s) fun (h : Nat) =>
            ITree.bind (hE () (h == s)) fun _ => ITree.ret h := by
    show Freek.eval (𝓔 := circuitEff) (𝓑 := circuitBlock) hE hB
        (Freek.bind (sumSqSrc 3) fun s =>
          Freek.bind (Circuit.hint (pure s)) fun h =>
            Freek.bind (Circuit.assert (h == s)) fun _ => Freek.pure h) = _
    rw [Freek.eval_bind]
    exact congrArg (ITree.bind (evalC hE hB (sumSqSrc 3))) (funext fun s => rfl)
  rw [hsrc]
  show Eutt
    (ITree.bind (mrec (bd hE hB) 3) fun s =>
      ITree.bind (hB Nat () fun _ => ITree.ret s) fun (h : Nat) =>
        ITree.bind (hE () (h == s)) fun _ => ITree.ret h)
    (ITree.bind (evalC hE hB (sumSqSrc 3)) fun s =>
      ITree.bind (hB Nat () fun _ => ITree.ret s) fun (h : Nat) =>
        ITree.bind (hE () (h == s)) fun _ => ITree.ret h)
  exact eutt_bind_cong (sumSq_sound hE hB 3) fun s => eutt_refl _

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
theorem reflect_ret {α : Tp} (v : Tp.denote (CompE ε br) α) {v' : Tp.denote (CompE ε br) α}
    (h : v = v') :
    Eutt (Expr.denote (rE hE) (rB hB)
        (.ret v : Expr CircE CircB (Tp.denote (CompE ε br)) none α))
      (evalC hE hB (.pure v')) :=
  Eutt.of_eq (by rw [h]; rfl)

/-- Reflect a host primitive: emit a `bin` node binding a fresh atom `vc` with its defining
    equation; the source is untouched (`t` is arbitrary — a pure step costs nothing). -/
theorem reflect_bin {a b c α : Tp} (o : Bin a b c)
    (va : Tp.denote (CompE ε br) a) (vb : Tp.denote (CompE ε br) b)
    {k : Tp.denote (CompE ε br) c → Expr CircE CircB (Tp.denote (CompE ε br)) none α}
    {t : CompE ε br (Tp.denote (CompE ε br) α)}
    (ih : ∀ vc, vc = o.denote va vb → Eutt (Expr.denote (rE hE) (rB hB) (k vc)) t) :
    Eutt (Expr.denote (rE hE) (rB hB) (.bin o va vb k)) t :=
  ih _ rfl

/-- Reflect `eff e i' ks` (with the grafting `bind`, every source effect arrives with its
    continuation already attached): emit an `eff` node — its input atom must equal the source's
    input (side condition `hi`, discharged from the defining equations) — and continue
    pointwise under the bound result. -/
theorem reflect_eff {α : Tp} (e : CircE.ε) (i : Tp.denote (CompE ε br) (CircE.𝓘 e))
    {i' : Tp.denote (CompE ε br) (CircE.𝓘 e)}
    {k : Tp.denote (CompE ε br) (CircE.𝓞 e) →
      Expr CircE CircB (Tp.denote (CompE ε br)) none α}
    {ks : Tp.denote (CompE ε br) (CircE.𝓞 e) → Circuit (Tp.denote (CompE ε br) α)}
    (hi : i = i')
    (ih : ∀ o, Eutt (Expr.denote (rE hE) (rB hB) (k o)) (evalC hE hB (ks o))) :
    Eutt (Expr.denote (rE hE) (rB hB) (.eff e i k)) (evalC hE hB (Freek.eff e i' ks)) := by
  subst hi
  show Eutt (ITree.bind (hE e i) fun o => Expr.denote (rE hE) (rB hB) (k o))
            (ITree.bind (hE e i) fun o => evalC hE hB (ks o))
  exact eutt_bind_cong (eutt_refl _) ih

/-- `sqAssertSrc`, reflected **top-down**: the AST component is the `_` — it is *discovered*
    by the `apply`-trace along the source circuit, one lemma per source node. -/
def sqAssertReflected (x : Nat) :
    { e : Expr CircE CircB (Tp.denote (CompE ε br)) none .nat //
      Eutt (Expr.denote (rE hE) (rB hB) e) (evalC hE hB (sqAssertSrc x)) } :=
  ⟨_, by
    unfold sqAssertSrc
    apply reflect_bin hE hB .mul x x    -- y := x * x
    intro y hy
    apply reflect_bin hE hB .le x y     -- c := decide (x ≤ y)
    intro c hc
    apply reflect_eff hE hB () c        -- assert c   (side goal: c = decide (x ≤ x*x))
    · simp only [hc, hy, Bin.denote]
    · intro o
      apply reflect_ret hE hB y         -- return y   (side goal: y = x*x)
      simp only [hy, Bin.denote]⟩

/-- The trace reconstructs exactly the hand-written AST. -/
example (x : Nat) : (sqAssertReflected hE hB x).1 = sqAssertAst x := rfl

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
  `rintro` + `simp` over the accumulated equations. -/

/-- A reflection of source `m`, **conditional on pending defining equations `Φ`**: an AST
    together with a soundness proof that may assume `Φ`. -/
def Reflection (Φ : Prop) (α : Tp)
    (m : Circuit (Tp.denote (CompE ε br) α)) : Type :=
  { e : Expr CircE CircB (Tp.denote (CompE ε br)) none α //
    Φ → Eutt (Expr.denote (rE hE) (rB hB) e) (evalC hE hB m) }

/-- Reflect `pure`: the pack's node is `ret v`; the value condition may assume `Φ`. -/
def Reflection.ret {Φ : Prop} {α : Tp} (v : Tp.denote (CompE ε br) α)
    {v' : Tp.denote (CompE ε br) α} (h : Φ → v = v') :
    Reflection hE hB Φ α (.pure v') :=
  ⟨.ret v, fun hΦ => Eutt.of_eq (by rw [h hΦ]; rfl)⟩

/-- Reflect a host primitive: the pack's node is `bin o va vb` with the continuation's syntax
    components spliced in; the continuation works under the *extended* equation context
    `Φ ∧ vc = o.denote va vb`, discharged here at the actual value with `⟨hΦ, rfl⟩`. -/
def Reflection.bin {Φ : Prop} {a b c α : Tp} (o : Bin a b c)
    (va : Tp.denote (CompE ε br) a) (vb : Tp.denote (CompE ε br) b)
    {m : Circuit (Tp.denote (CompE ε br) α)}
    (k : ∀ vc, Reflection hE hB (Φ ∧ vc = o.denote va vb) α m) :
    Reflection hE hB Φ α m :=
  ⟨.bin o va vb fun vc => (k vc).1, fun hΦ => (k _).2 ⟨hΦ, rfl⟩⟩

/-- Reflect `eff e i' ks`: the pack's node is `eff e i` around the continuation packs;
    the input condition `i = i'` may assume `Φ`. -/
def Reflection.eff {Φ : Prop} {α : Tp} (e : CircE.ε) (i : Tp.denote (CompE ε br) (CircE.𝓘 e))
    {i' : Tp.denote (CompE ε br) (CircE.𝓘 e)} (hi : Φ → i = i')
    {ks : Tp.denote (CompE ε br) (CircE.𝓞 e) → Circuit (Tp.denote (CompE ε br) α)}
    (k : ∀ o, Reflection hE hB Φ α (ks o)) :
    Reflection hE hB Φ α (Freek.eff e i' ks) :=
  ⟨.eff e i fun o => (k o).1, fun hΦ => by
    rw [← hi hΦ]
    show Eutt (ITree.bind (hE e i) fun o => Expr.denote (rE hE) (rB hB) ((k o).1))
              (ITree.bind (hE e i) fun o => evalC hE hB (ks o))
    exact eutt_bind_cong (eutt_refl _) fun o => (k o).2 hΦ⟩

/-- `sqAssertSrc` reflected in the third style: the same `apply`-trace, but every `apply` calls
    a pack-returning *function* — the goal is `Type`-valued (data!), and the AST is assembled
    by the combinators, node by node, as the trace walks the source. -/
def sqAssertReflected' (x : Nat) :
    Reflection hE hB True .nat (sqAssertSrc x) := by
  unfold sqAssertSrc
  apply Reflection.bin hE hB .mul x x    -- y := x * x
  intro y
  apply Reflection.bin hE hB .le x y     -- c := decide (x ≤ y)
  intro c
  apply Reflection.eff hE hB () c        -- assert c
  · rintro ⟨⟨-, hy⟩, hc⟩                 --   side goal: Φ → c = decide (x ≤ x*x)
    simp only [hy, hc, Bin.denote]
  · intro o
    apply Reflection.ret hE hB y         -- return y
    rintro ⟨⟨-, hy⟩, -⟩                  --   side goal: Φ → y = x*x
    simp only [hy, Bin.denote]

/-- The third style, too, reconstructs exactly the hand-written AST. -/
example (x : Nat) : (sqAssertReflected' hE hB x).1 = sqAssertAst x := rfl

end Sound

end Example
end Ast2
end Freigen
