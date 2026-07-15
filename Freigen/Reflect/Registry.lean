import Freigen.Ast.Basic
import Freigen.Reflect.Attributes

namespace Freigen
namespace Ast

universe u v

/-- Explicit representation data consumed by the reflector macro.  This is registry data, not a
    typeclass: pass 1 selects a declaration and pass 2 uses that exact term. -/
structure ReprSpec (α : Type) where
  code : Tp0
  relates : α → code.denote → Prop
  encode : α → code.denote
  encode_related : ∀ source, relates source (encode source)

/-- Explicit target operation and compatibility witness for one source operation. -/
structure OpSpec {S : ITree.HSig.{u, v}} {H : Signature}
    (C : Signature.Compat S H) (e : S.op) where
  target : H.op
  witness : C.opRel e target

@[ast_repr] def natRepr : ReprSpec Nat where
  code := .nat
  relates := Eq
  encode := id
  encode_related := fun _ => rfl

@[ast_repr] def intRepr : ReprSpec Int where
  code := .int
  relates := Eq
  encode := id
  encode_related := fun _ => rfl

@[ast_repr] def boolRepr : ReprSpec Bool where
  code := .bool
  relates := Eq
  encode := id
  encode_related := fun _ => rfl

@[ast_repr] def unitRepr : ReprSpec Unit where
  code := .unit
  relates := Eq
  encode := id
  encode_related := fun _ => rfl

@[ast_repr] def prodRepr (a : ReprSpec α) (b : ReprSpec β) : ReprSpec (α × β) where
  code := .prod a.code b.code
  relates source target := a.relates source.1 target.1 ∧ b.relates source.2 target.2
  encode source := (a.encode source.1, b.encode source.2)
  encode_related source := ⟨a.encode_related source.1, b.encode_related source.2⟩

end Ast
end Freigen
