import Mathlib.Data.ZMod.Defs
import Freigen.Compile

namespace Freigen.Examples.ZModCompatibility

open Freigen Ast

example (n : Nat) : ZMod n = ZModCarrier n := rfl

inductive NoOp : Type

abbrev Source : ITree.HSig where
  op := NoOp
  input e := nomatch e
  output e := nomatch e
  branch e := nomatch e
  branchInput e := nomatch e
  branchOutput e := nomatch e

abbrev Target : Signature where
  op := NoOp
  input e := nomatch e
  output e := nomatch e
  branch e := nomatch e
  branchInput e := nomatch e
  branchOutput e := nomatch e

@[ast_compat] def noOpCompat : Signature.Compat Source Target where
  opRel e := nomatch e
  input {e} := nomatch e
  output {e} := nomatch e
  branch {e} := nomatch e
  branchInput {e} := nomatch e
  branchOutput {e} := nomatch e

abbrev Circuit := Free Source

def actualZModSource : Circuit (ZMod 7) :=
  pure 3

def actualZModReflected := reflect% actualZModSource

example : Closed Target (.base (.zmod 7)) :=
  actualZModReflected.1

def addActualZMod (x : ZMod 7) : Circuit (ZMod 7) :=
  pure (x + 1)

def actualZModArithmeticSource : Circuit (ZMod 7) :=
  addActualZMod 2

def actualZModArithmeticReflected := reflect% actualZModArithmeticSource

example : Closed Target (.base (.zmod 7)) :=
  actualZModArithmeticReflected.1

end Freigen.Examples.ZModCompatibility
