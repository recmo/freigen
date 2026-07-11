import Lean.Elab.Term

namespace Freigen.Ast2

open Lean

initialize ast2CompatAttr : TagAttribute ←
  registerTagAttribute `ast2_compat "AST2 source/target signature compatibility used by reflect%"

initialize ast2ReprAttr : TagAttribute ←
  registerTagAttribute `ast2_repr "AST2 host-type representation used by reflect%"

initialize ast2OpAttr : TagAttribute ←
  registerTagAttribute `ast2_op "AST2 source-operation mapping used by reflect%"

initialize ast2InlineAttr : TagAttribute ←
  registerTagAttribute `ast2_inline "AST2 helper that reflect% must unfold instead of spill"

initialize ast2RenderAttr : TagAttribute ←
  registerTagAttribute `ast2_render "AST2 signature renderer selected explicitly by #compile"

end Freigen.Ast2
