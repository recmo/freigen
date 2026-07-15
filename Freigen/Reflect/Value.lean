import Freigen.Reflect.Resolve

namespace Freigen
namespace Ast
namespace Reflector

open Lean Meta

structure ReifiedAtom where
  semantic : Lean.Expr
  code : Lean.Expr

private def genericAtom? (atoms : Array ReifiedAtom) (semantic : Lean.Expr) : Option Lean.Expr :=
  (atoms.find? (·.semantic == semantic)).map (·.code)

private def boolValue? (e : Lean.Expr) : MetaM (Option Bool) := do
  let saved ← get
  if ← isDefEq e (mkConst ``true) then
    set saved
    return some true
  set saved
  if ← isDefEq e (mkConst ``false) then
    set saved
    return some false
  set saved
  return none

private def intValue? (e : Lean.Expr) : MetaM (Option Int) := do
  if let some value ← getIntValue? e then return some value
  match e with
  | .app (.const ``Int.negSucc _) (.lit (.natVal n)) => return some (Int.negSucc n)
  | _ => return none

/-! ## Match semantic values -/

private inductive ValueNode where
  | atom (code : Lean.Expr)
  | natLit (value : Nat)
  | intLit (value : Int)
  | boolLit (value : Bool)
  | unitLit
  | unary (inputTp input op resultTp : Lean.Expr)
  | binary (leftTp left rightTp right op resultTp : Lean.Expr)

private def matchBinary? (tp value : Lean.Expr) : MetaM (Option ValueNode) := do
  let fn := value.getAppFn.constName?
  let args := value.getAppArgs
  let isAdd := fn == some ``Nat.add || fn == some ``HAdd.hAdd
  let isSub := fn == some ``Nat.sub || fn == some ``HSub.hSub
  let isMul := fn == some ``Nat.mul || fn == some ``HMul.hMul
  let isEq := fn == some ``BEq.beq
  unless isAdd || isSub || isMul || isEq do return none
  let left := args[args.size - 2]!
  let right := args[args.size - 1]!
  let operandTp ← if isEq then
    let repr ← resolveRepr (← inferType left)
    whnf (← mkAppM ``ReprSpec.code #[repr])
  else
    whnf tp
  let op? ←
    if ← isDefEq operandTp (mkConst ``Tp0.nat) then
      pure <| some (Lean.mkConst (if isAdd then ``Bin.add else if isSub then ``Bin.sub
        else if isMul then ``Bin.mul else ``Bin.eq))
    else if ← isDefEq operandTp (mkConst ``Tp0.int) then
      pure <| some (Lean.mkConst (if isAdd then ``Bin.intAdd else if isSub then ``Bin.intSub
        else if isMul then ``Bin.intMul else ``Bin.intEq))
    else match operandTp with
      | _ => pure none
  let some op := op? | return none
  return some (.binary operandTp left operandTp right op (← mkAppM ``Tp.base #[tp]))

private def matchValue (tp value : Lean.Expr) (atoms : Array ReifiedAtom) :
    MetaM ValueNode := do
  let tp ← whnf tp
  if let some code := genericAtom? atoms value then return .atom code
  let reduced ← whnf value
  if let some code := genericAtom? atoms reduced then return .atom code
  if ← isDefEq tp (mkConst ``Tp0.nat) then
    if let some n ← getNatValue? reduced then return .natLit n
  if ← isDefEq tp (mkConst ``Tp0.int) then
    if let some n ← intValue? reduced then return .intLit n
  if ← isDefEq tp (mkConst ``Tp0.bool) then
    if let some b ← boolValue? reduced then return .boolLit b
  if ← isDefEq tp (mkConst ``Tp0.unit) then return .unitLit
  let fn := value.getAppFn.constName?
  let args := value.getAppArgs
  if fn == some ``Prod.fst || fn == some ``Prod.snd then
    let pair := args[args.size - 1]!
    let .app (.app (.const ``Prod _) leftType) rightType ← whnf (← inferType pair)
      | throwError "reflect%: malformed product projection"
    let leftCode ← mkAppM ``ReprSpec.code #[← resolveRepr leftType]
    let rightCode ← mkAppM ``ReprSpec.code #[← resolveRepr rightType]
    let pairTp ← mkAppM ``Tp0.prod #[leftCode, rightCode]
    let op ← mkAppOptM (if fn == some ``Prod.fst then ``Un.fst else ``Un.snd)
      #[some leftCode, some rightCode]
    return .unary pairTp pair op (← mkAppM ``Tp.base #[tp])
  if fn == some ``Prod.mk then
    let .app (.app (.const ``Tp0.prod _) leftTp) rightTp := tp
      | throwError "reflect%: product constructor used at a non-product object type"
    let left := args[args.size - 2]!
    let right := args[args.size - 1]!
    let pairOp ← mkAppOptM ``Bin.pair #[some leftTp, some rightTp]
    return .binary leftTp left rightTp right pairOp (← mkAppM ``Tp.base #[tp])
  if let some node ← matchBinary? tp value then return node
  if fn == some ``Decidable.decide then
    let proposition := args[args.size - 2]!
    let pfn := proposition.getAppFn.constName?
    let pargs := proposition.getAppArgs
    let opName? := if pfn == some ``LE.le then some ``Bin.le
      else if pfn == some ``LT.lt then some ``Bin.lt else none
    if let some opName := opName? then
      let left := pargs[pargs.size - 2]!
      let right := pargs[pargs.size - 1]!
      return .binary (mkConst ``Tp0.nat) left (mkConst ``Tp0.nat) right
        (mkConst opName) (mkConst ``Tp.bool)
  throwError "reflect%: cannot emit semantic value as generic PHOAS{indentExpr value}"

/-! ## Construct generic value code -/

partial def emitGenericValue (H V r tp value : Lean.Expr)
    (atoms : Array ReifiedAtom) (k : Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr := do
  let withResult (name : Name) (resultTp : Lean.Expr)
      (mk : Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr :=
    withLocalDeclD name (mkApp V resultTp) fun result => do
      mk (← mkLambdaFVars #[result] (← k result))
  match ← matchValue tp value atoms with
  | .atom code => k code
  | .natLit n => withResult `n (mkConst ``Tp.nat) fun cont => do
      mkAppOptM ``Expr.natLit #[some H, some V, some r, none, some (mkNatLit n), some cont]
  | .intLit n => withResult `n (mkConst ``Tp.int) fun cont => do
      mkAppOptM ``Expr.intLit
        #[some H, some V, some r, none, some (Lean.mkIntLit n), some cont]
  | .boolLit b => withResult `b (mkConst ``Tp.bool) fun cont => do
      mkAppOptM ``Expr.boolLit #[some H, some V, some r, none,
        some (mkConst (if b then ``true else ``false)), some cont]
  | .unitLit => withResult `unit (mkConst ``Tp.unit) fun cont => do
      mkAppOptM ``Expr.unitLit #[some H, some V, some r, none, some cont]
  | .unary inputTp input op resultTp =>
      emitGenericValue H V r inputTp input atoms fun inputCode => do
        withResult `result resultTp fun cont => do
          mkAppOptM ``Expr.un #[some H, some V, some r, none, none, none,
            some op, some inputCode, some cont]
  | .binary leftTp left rightTp right op resultTp =>
      emitGenericValue H V r leftTp left atoms fun leftCode => do
        emitGenericValue H V r rightTp right atoms fun rightCode => do
          withResult `result resultTp fun cont => do
            mkAppOptM ``Expr.bin #[some H, some V, some r, none, none, none, none,
              some op, some leftCode, some rightCode, some cont]

end Reflector
end Ast
end Freigen
