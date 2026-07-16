import Freigen.Reflect.Registry
import Lean.Elab.SyntheticMVars

namespace Freigen
namespace Ast
namespace Reflector

open Lean Meta Elab Term

private def registryEntries (attr : TagAttribute) : CoreM (Array Name) := do
  let env ← getEnv
  let state := attr.ext.toEnvExtension.getState env
  let mut entries := state.state.toArray
  for imported in state.importedEntries do
    entries := entries ++ imported
  return entries

/-! ## Registry resolution -/

private partial def instantiateRegistered (decl : Name)
    (expected : Lean.Expr) : MetaM Lean.Expr := do
  let c ← mkConstWithFreshMVarLevels decl
  let ⟨xs, _, body⟩ ← forallMetaTelescope (← inferType c)
  unless ← isDefEq body expected do
    throwError "result type does not match"
  for x in xs do
    let m := x.mvarId!
    unless (← m.isAssigned) do
      let ty ← instantiateMVars (← m.getType)
      if ty.isAppOfArity ``ReprSpec 1 then
        m.assign (← resolve astReprAttr ty)
      else
        throwError "unresolved registry parameter{indentExpr ty}"
  pure (← instantiateMVars (mkAppN c xs))
where
  resolve (attr : TagAttribute) (expected : Lean.Expr) : MetaM Lean.Expr := do
    let saved ← get
    for candidate in ← registryEntries attr do
      try
        return ← instantiateRegistered candidate expected
      catch _ =>
        set saved
    throwError "reflect%: no registered declaration produces{indentExpr expected}"

private def resolveRegistered (attr : TagAttribute) (expected : Lean.Expr) : MetaM Lean.Expr := do
  let saved ← get
  for candidate in ← registryEntries attr do
    try return ← instantiateRegistered candidate expected
    catch _ => set saved
  throwError "no matching registered declaration"

/-- Resolve an explicit representation declaration for a host type. -/
def resolveRepr (α : Lean.Expr) : MetaM Lean.Expr := do
  let expected ← mkAppM ``ReprSpec #[α]
  let candidates ← registryEntries astReprAttr
  try resolveRegistered astReprAttr expected
  catch _ => throwError
    "reflect%: type has no registered AST representation{indentExpr α}\nregistered: {candidates}"

/-- Select a representation that agrees with the target type and relation imposed by the current
    computation boundary.  A host type can have a preferred precise representation while an
    operation compatibility deliberately exposes its erased carrier. -/
def resolveReprFor (ctx α targetTp relates : Lean.Expr) : MetaM Lean.Expr := do
  let expected ← mkAppM ``ReprSpec #[α]
  let agrees (repr : Lean.Expr) : MetaM Bool := do
    unless ← isDefEq (← inferType repr) expected do return false
    let code ← mkAppM ``ReprSpec.code #[repr]
    unless ← isDefEq code targetTp do return false
    let reprRel ← mkAppOptM ``ReprSpec.relates #[none, some repr, some ctx]
    isDefEq reprRel relates
  let saved ← get
  try
    let preferred ← resolveRepr α
    if ← agrees preferred then return preferred
  catch _ => pure ()
  set saved
  for candidate in ← registryEntries astReprAttr do
    let candidateState ← get
    try
      let repr ← instantiateRegistered candidate expected
      if ← agrees repr then return repr
    catch _ => pure ()
    set candidateState
  throwError "reflect%: no representation of{indentExpr α}\nmatches target type{indentExpr targetTp}\nand relation{indentExpr relates}"

/-- Resolve the source/target signature compatibility selected for `S`. -/
def resolveCompat (S : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let H ← mkFreshExprMVar (mkConst ``Signature)
  let ctxType := Lean.mkConst ``DefCtx
  let expected ← withLocalDeclD `ctx ctxType fun ctx => do
    mkForallFVars #[ctx] (← mkAppM ``Signature.Compat #[S, H, ctx])
  let saved ← get
  for candidate in ← registryEntries astCompatAttr do
    try
      let compat ← mkConstWithFreshMVarLevels candidate
      unless ← isDefEq (← inferType compat) expected do throwError "type mismatch"
      return (← instantiateMVars H, ← instantiateMVars compat)
    catch _ => set saved
  throwError "reflect%: source signature has no registered AST compatibility{indentExpr S}"

/-- Resolve the exact target operation and compatibility witness for one source operation. -/
def resolveOp (C e : Lean.Expr) : MetaM Lean.Expr := do
  let expected ← mkAppM ``OpSpec #[C, e]
  try resolveRegistered astOpAttr expected
  catch _ => throwError
    "reflect%: source operation is not representable by the target signature{indentExpr e}"


end Reflector
end Ast
end Freigen
