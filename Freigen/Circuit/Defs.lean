import Freigen.CompM.Basic
import Freigen.Eff
import Freigen.Free

namespace Freigen.Circuit

inductive Eff : Type _
| assert
| hint (tp : Type)

def Eff.input : Eff → Type _
| .assert => Bool
| .hint _ => Unit

def Eff.output : Eff → Type
| .assert => Unit
| .hint tp => tp

def Eff.blockTag : Eff → Type _
| .assert => PEmpty
| .hint _ => PUnit

def Eff.blockInputs : (t : Eff) → Eff.blockTag t → Type
| assert => nofun
| hint _ => fun _ => Unit

def Eff.blockOutputs : (t : Eff) → Eff.blockTag t → Type
| assert => nofun
| hint tp => fun _ => tp

instance : Freigen.Eff.Spec Eff where
  input := Eff.input
  output := Eff.output
  blockTag := Eff.blockTag
  blockInputs := Eff.blockInputs
  blockOutputs := Eff.blockOutputs

end Circuit

def Circuit : Type → Type _ := Free Circuit.Eff

namespace Circuit

def assert (b : Bool) : Circuit Unit :=
  Free.op (E := Circuit.Eff) Eff.assert b nofun

def hint {α : Type} : Circuit α → Circuit α := fun hint =>
  Free.op (E := Circuit.Eff) (Eff.hint α) () fun _ _ => hint

end Freigen.Circuit
