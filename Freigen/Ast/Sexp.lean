import Freigen.Ast.Basic

namespace Freigen.Ast

/-- Explicit serialization data for a target signature.  Branch enumeration is data because
    higher-order operations may expose dynamically bound blocks. -/
structure RenderSpec (H : Signature) where
  opName : H.op → String
  branches : (e : H.op) → List (H.branch e)

def Tp0.sexp : Tp0 → String
  | .nat => "nat"
  | .int => "int"
  | .bool => "bool"
  | .unit => "unit"
  | .prod a b => s!"(prod {a.sexp} {b.sexp})"

def Tp.sexp : Tp → String
  | .base a => a.sexp
  | .fn a b => s!"(fn {a.sexp} {b.sexp})"

def Un.sexp : Un a b → String
  | .not => "not"
  | .fst => "fst"
  | .snd => "snd"

def Bin.sexp : Bin a b c → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .intAdd => "add"
  | .intSub => "sub"
  | .intMul => "mul"
  | .eq => "eq"
  | .intEq => "eq"
  | .lt => "lt"
  | .le => "le"
  | .and => "and"
  | .or => "or"
  | .pair => "pair"

abbrev SexpV : Tp → Type := fun _ => String

private def fresh (stem : String) (n : Nat) : String := stem ++ toString n

private def spaces (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

private def indent (n : Nat) (text : String) : String :=
  String.intercalate "\n" <| (text.splitOn "\n").map fun line => spaces n ++ line

private def block (body : String) : String :=
  s!"(block\n{indent 2 body}\n)"

private partial def renderExpr {H : Signature} (render : RenderSpec H) :
    {r : Option (Tp × Tp)} → {α : Tp} → Expr H SexpV r α → Nat → String × Nat
  | _, _, .source range body, n =>
      let (bodyText, next) := renderExpr render body n
      (s!"(source {range.module} {range.startLine} {range.startColumn} " ++
        s!"{range.endLine} {range.endColumn}\n{indent 2 (block bodyText)}\n)", next)
  | _, _, .ret value, n => (s!"(ret {value})", n)
  | r, α, .natLit value k, n =>
      let name := fresh "v" n
      let (rest, next) := renderExpr render (k name) (n + 1)
      (s!"(let {name} nat (lit {value}))\n{rest}", next)
  | r, α, .intLit value k, n =>
      let name := fresh "v" n
      let (rest, next) := renderExpr render (k name) (n + 1)
      (s!"(let {name} int (lit {value}))\n{rest}", next)
  | r, α, .boolLit value k, n =>
      let name := fresh "v" n
      let (rest, next) := renderExpr render (k name) (n + 1)
      (s!"(let {name} bool (lit {value}))\n{rest}", next)
  | r, α, .unitLit k, n =>
      let name := fresh "v" n
      let (rest, next) := renderExpr render (k name) (n + 1)
      (s!"(let {name} unit (lit unit))\n{rest}", next)
  | r, α, .un (b := b) op value k, n =>
      let name := fresh "v" n
      let (rest, next) := renderExpr render (k name) (n + 1)
      (s!"(let {name} {b.sexp} ({op.sexp} {value}))\n{rest}", next)
  | r, α, .bin (c := c) op left right k, n =>
      let name := fresh "v" n
      let (rest, next) := renderExpr render (k name) (n + 1)
      (s!"(let {name} {c.sexp} ({op.sexp} {left} {right}))\n{rest}", next)
  | r, α, .ite (β := β) condition yes no k, n =>
      let result := fresh "v" n
      let (yesText, n₁) := renderExpr render yes (n + 1)
      let (noText, n₂) := renderExpr render no n₁
      let (rest, n₃) := renderExpr render (k result) n₂
      (s!"(let {result} {β.sexp} (if {condition}\n" ++
        s!"{indent 2 (block yesText)}\n{indent 2 (block noText)}\n))\n{rest}", n₃)
  | r, α, .lam (a := a) (b := b) body k, n =>
      let arg := fresh "x" n
      let (bodyText, n₁) := renderExpr render (body arg) (n + 1)
      let fn := fresh "f" n₁
      let (rest, n₂) := renderExpr render (k fn) (n₁ + 1)
      (s!"(let {fn} {(Tp.fn a b).sexp} (lam ({arg} {a.sexp})\n" ++
        s!"{indent 2 (block bodyText)}\n))\n{rest}", n₂)
  | r, α, .app (b := b) fn arg k, n =>
      let result := fresh "v" n
      let (rest, next) := renderExpr render (k result) (n + 1)
      (s!"(let {result} {b.sexp} (app {fn} {arg}))\n{rest}", next)
  | r, α, .letrec (a := a) (b := b) body k, n =>
      let arg := fresh "x" n
      let (bodyText, n₁) := renderExpr render (body arg) (n + 1)
      let fn := fresh "rec" n₁
      let (rest, n₂) := renderExpr render (k fn) (n₁ + 1)
      (s!"(letrec {fn} ({arg} {a.sexp}) {b.sexp}\n" ++
        s!"{indent 2 (block bodyText)}\n)\n{rest}", n₂)
  | _, _, .selfCall (b := b) arg k, n =>
      let result := fresh "v" n
      let (rest, next) := renderExpr render (k result) (n + 1)
      (s!"(let {result} {b.sexp} (self {arg}))\n{rest}", next)
  | r, α, .op op input blocks k, n =>
      let renderedBlocks := (render.branches op).foldl (init := ("", n)) fun (text, next) branch =>
        let arg := fresh "b" next
        let (body, after) := renderExpr render (blocks branch arg) (next + 1)
        let rendered := s!"(branch {arg}\n{indent 2 (block body)}\n)"
        (if text.isEmpty then rendered else text ++ "\n" ++ rendered, after)
      let result := fresh "v" renderedBlocks.2
      let (rest, next) := renderExpr render (k result) (renderedBlocks.2 + 1)
      let operation := if renderedBlocks.1.isEmpty then
          s!"(op {render.opName op} {input})"
        else
          s!"(op {render.opName op} {input}\n{indent 2 renderedBlocks.1}\n)"
      (s!"(let {result} {(H.output op).sexp}\n{indent 2 operation}\n)\n{rest}", next)

def serialize {H : Signature} (render : RenderSpec H) {α : Tp} (code : Closed H α) : String :=
  let (body, _) := renderExpr render (code SexpV) 0
  s!"(program {α.sexp}\n{indent 2 body}\n)\n"

end Freigen.Ast
