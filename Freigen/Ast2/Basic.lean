import Freigen.ITree.Basic
import Freigen.Free
import Freigen.Ast.Tp

namespace Freigen

structure EffSpec : Type _ where
  ε : Type _
  𝓘 : ε → Type _
  𝓞 : ε → Type _

structure BindSpec : Type _ where
  ε : Type u
  𝓘 : ε → Type v
  𝓞 : ε → Type w
  𝓑 : ε → Type x
  𝓑τ : (e: ε) → 𝓑 e → Type y

inductive Freek (𝓔 : EffSpec) (𝓑 : BindSpec) : Type _ → Type _ where
| pure {α} : α → Freek 𝓔 𝓑 α
| bind {α β} : Freek 𝓔 𝓑 α → (α → Freek 𝓔 𝓑 β) → Freek 𝓔 𝓑 β
| eff : (e : 𝓔.ε) → 𝓔.𝓘 e → Freek 𝓔 𝓑 (𝓔.𝓞 e)
| bindEff : (e : 𝓑.ε) → 𝓑.𝓘 e → ((b: 𝓑.𝓑 e) → Freek 𝓔 𝓑 (𝓑.𝓑τ e b)) → Freek 𝓔 𝓑 (𝓑.𝓞 e)

instance {𝓔 𝓑} : Monad (Freek 𝓔 𝓑) where
  pure := Freek.pure
  bind := Freek.bind

def Freek.eval {M} [Monad M] {𝓔 𝓑 α}
    (evalEff : (e : 𝓔.ε) → 𝓔.𝓘 e → M (𝓔.𝓞 e))
    (evalBind : (e : 𝓑.ε) → 𝓑.𝓘 e → ((b: 𝓑.𝓑 e) → M (𝓑.𝓑τ e b)) → M (𝓑.𝓞 e))
    : Freek 𝓔 𝓑 α → M α
| .pure a => Pure.pure a
| .bind a f => do
    let a' ← Freek.eval evalEff evalBind a
    Freek.eval evalEff evalBind (f a')
| .eff e i => evalEff e i
| .bindEff e i k => evalBind e i (fun b => Freek.eval evalEff evalBind (k b))

abbrev circuitEff : EffSpec where
  ε := Unit
  𝓘 := fun _ => Bool
  𝓞 := fun _ => Unit

abbrev circuitBlock : BindSpec where
  ε := Type
  𝓘 := fun _ => Unit
  𝓞 := id
  𝓑 := fun _ => Unit
  𝓑τ := fun e _ => e

def Circuit (α : Type _) : Type _ := Freek circuitEff circuitBlock α

instance : Monad Circuit := inferInstanceAs (Monad (Freek _ _))

def Circuit.hint {β : Type} (f : Circuit β) : Circuit β :=
  Freek.bindEff (𝓔 := circuitEff) (𝓑 := circuitBlock) β () (fun _ => f)

def Circuit.eval_with_hints : Circuit α → Option α := Freek.eval
  (fun _ i => if i then some () else none)
  (fun _ _ k => k ())

def ConstraintM (α : Type _) := (α → Prop) → Prop

instance : Monad ConstraintM where
  pure a := fun k => k a
  bind m f := fun k => m (fun a => f a k)

def Circuit.eval_constraints : Circuit α → ConstraintM α := Freek.eval
  (fun _ i => fun k => i ∧ k ())
  (fun _ _ _ => fun k => ∃ x, k x)

open ITree in
def Freek.toITree {α} {𝓔: EffSpec} {𝓑: BindSpec}
    (evalBind :  (e : 𝓑.ε) → 𝓑.𝓘 e → ((b: 𝓑.𝓑 e) → CompE 𝓔.ε 𝓔.𝓞 (𝓑.𝓑τ e b)) → CompE 𝓔.ε 𝓔.𝓞 (𝓑.𝓞 e)):
  Freek 𝓔 𝓑 α → CompE 𝓔.ε 𝓔.𝓞 α := Freek.eval (fun e _ => ITree.vis e (fun o => ITree.ret o)) evalBind

end Freigen
