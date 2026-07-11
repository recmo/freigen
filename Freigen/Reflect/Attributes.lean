import Lean.Elab.Term

namespace Freigen.Ast

open Lean

initialize astCompatAttr : TagAttribute ←
  registerTagAttribute `ast_compat "AST source/target signature compatibility used by reflect%"

initialize astReprAttr : TagAttribute ←
  registerTagAttribute `ast_repr "AST host-type representation used by reflect%"

initialize astOpAttr : TagAttribute ←
  registerTagAttribute `ast_op "AST source-operation mapping used by reflect%"

initialize astInlineAttr : TagAttribute ←
  registerTagAttribute `ast_inline "AST helper that reflect% must unfold instead of spill"

initialize astRenderAttr : TagAttribute ←
  registerTagAttribute `ast_render "AST signature renderer selected explicitly by #compile"

end Freigen.Ast
