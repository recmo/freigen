import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Freigen.Circuit

open scoped BigOperators

structure Valuation
    (F W : Type) [Semiring F] [AddCommMonoid W] [One W] [Module F W] where
  toFun : W →ₗ[F] F
  one_map : toFun 1 = 1

instance {F W} [Semiring F] [AddCommMonoid W] [One W] [Module F W] : CoeFun (Valuation F W) fun _ => W → F where
  coe v := v.toFun

abbrev Assertion
    (F W : Type) [Semiring F] [AddCommMonoid W] [One W] [Module F W] :=
  Valuation F W → Prop

class CertLogic {World : Type} (Cert : (World → Prop) → Sort u) where
  derive
      {ι : Type}
      {P : ι → World → Prop}
      {Q : World → Prop} :
    (∀ world, (∀ i, P i world) → Q world) →
    ((i : ι) → Cert (P i)) →
    Cert Q

class Context (F : Type) where
  W : Type
  [fieldF : Field F]
  [addGroupW : AddCommGroup W]
  [oneW: One W]
  [moduleW : Module F W]
  Cert : Assertion F W → Sort u
  [certLogic : CertLogic Cert]

attribute [implicit_reducible]
  Context.fieldF
  Context.addGroupW
  Context.moduleW
  Context.certLogic
  Context.oneW

attribute [instance]
  Context.fieldF
  Context.addGroupW
  Context.moduleW
  Context.certLogic
  Context.oneW

abbrev Cert {F : Type} [ctx : Context F]
    (P : Assertion F ctx.W) :=
  ctx.Cert P

def Cert.map {F : Type} [ctx : Context F]
    {P Q : Assertion F ctx.W}
    (f : ∀ ρ, P ρ → Q ρ)
    (cert : Cert P) :
    Cert Q :=
  ctx.certLogic.derive (ι := Unit) (fun _ f' => f _ (f' ()) ) (fun _ => cert)

structure CertW {F : Type} [ctx : Context F]
    (P : ctx.W → Assertion F ctx.W) where
  val : ctx.W
  cert : Cert (P val)

instance {F : Type} [ctx : Context F] {P : ctx.W → Assertion F ctx.W} : CoeOut (CertW (F:=F) P) ctx.W where
  coe c := c.val

namespace Cert

def derive {F : Type} [ctx : Context F]
    {ι : Type}
    {P : ι → Assertion F ctx.W}
    {Q : Assertion F ctx.W}
    (rule : ∀ ρ, (∀ i, P i ρ) → Q ρ)
    (premises : (i : ι) → Cert (P i)) :
    Cert Q :=
  CertLogic.derive rule premises

end Cert

def IsInRange {F : Type} [ctx : Context F] (n : Nat) (x : F) : Prop :=
  ∃ k : Nat, k < 2 ^ n ∧ x = (k : F)

def RangeAssertion {F : Type} [ctx : Context F]
    (n : Nat) (x : ctx.W) : Assertion F ctx.W :=
  fun ρ => IsInRange n (ρ x)

def R1CSAssertion {F : Type} [ctx : Context F]
    (a b c : ctx.W) : Assertion F ctx.W :=
  fun ρ => ρ a * ρ b = ρ c

def SpreadAssertion {F : Type} [ctx : Context F]
    (n : Nat) (a b : ctx.W) : Assertion F ctx.W :=
  fun ρ =>
    ∃ bits : Fin n → Bool,
      ρ a = (∑ i, if bits i then (2 : F) ^ i.val else 0) ∧
      ρ b = (∑ i, if bits i then (2 : F) ^ (2 * i.val) else 0)

def ValueAssertion {F : Type} [ctx : Context F]
    (a : F) (x : ctx.W) : Assertion F ctx.W :=
  fun ρ => ρ x = a

abbrev WUInt (F : Type) [ctx : Context F] (n : Nat) :=
  CertW $ RangeAssertion (F:=F) n

abbrev WU32 (F : Type) [Context F] := WUInt F 32

end Freigen.Circuit
