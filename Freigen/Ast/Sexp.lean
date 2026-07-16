import Freigen.Ast.Basic

namespace Freigen.Ast

structure RenderSpec (H : Signature) where
  opName : H.op → String
  branches : (e : H.op) → List (H.branch e)

def Tp.sexp : Tp → String
  | .nat => "nat"
  | .int => "int"
  | .bool => "bool"
  | .unit => "unit"
  | .prod left right => s!"(prod {left.sexp} {right.sexp})"
  | .fn input output => s!"(fn {input.sexp} {output.sexp})"

def Un.sexp : Un input output → String
  | .not => "not"
  | .fst => "fst"
  | .snd => "snd"

def Bin.sexp : Bin left right output → String
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

private inductive DefNames : DefCtx → Type
  | nil : DefNames []
  | cons : String → DefNames ctx → DefNames (decl :: ctx)

private def renderRef : DefRef scope captures input output → DefNames scope → String
  | .here, .cons name _ => name
  | .there ref, .cons _ names => renderRef ref names

private partial def renderExpr {H : Signature} (render : RenderSpec H)
    (names : DefNames scope) :
    {α : Tp} → Expr H scope SexpV α → Nat → String × Nat
  | _, .source range body, n =>
      let (bodyText, next) := renderExpr render names body n
      (s!"(source {range.module} {range.startLine} {range.startColumn} " ++
        s!"{range.endLine} {range.endColumn}\n{indent 2 (block bodyText)}\n)", next)
  | _, .ret value, n => (s!"(ret {value})", n)
  | _, .natLit value k, n =>
      let name := fresh "v" n
      let (rest, next) := renderExpr render names (k name) (n + 1)
      (s!"(let {name} nat (lit {value}))\n{rest}", next)
  | _, .intLit value k, n =>
      let name := fresh "v" n
      let (rest, next) := renderExpr render names (k name) (n + 1)
      (s!"(let {name} int (lit {value}))\n{rest}", next)
  | _, .boolLit value k, n =>
      let name := fresh "v" n
      let (rest, next) := renderExpr render names (k name) (n + 1)
      (s!"(let {name} bool (lit {value}))\n{rest}", next)
  | _, .unitLit k, n =>
      let name := fresh "v" n
      let (rest, next) := renderExpr render names (k name) (n + 1)
      (s!"(let {name} unit (lit unit))\n{rest}", next)
  | _, .un (output := output) operation value k, n =>
      let name := fresh "v" n
      let (rest, next) := renderExpr render names (k name) (n + 1)
      (s!"(let {name} {output.sexp} ({operation.sexp} {value}))\n{rest}", next)
  | _, .bin (output := output) operation left right k, n =>
      let name := fresh "v" n
      let (rest, next) := renderExpr render names (k name) (n + 1)
      (s!"(let {name} {output.sexp} ({operation.sexp} {left} {right}))\n{rest}", next)
  | _, .ite (β := resultTp) condition yes no k, n =>
      let result := fresh "v" n
      let (yesText, n₁) := renderExpr render names yes (n + 1)
      let (noText, n₂) := renderExpr render names no n₁
      let (rest, n₃) := renderExpr render names (k result) n₂
      (s!"(let {result} {resultTp.sexp} (if {condition}\n" ++
        s!"{indent 2 (block yesText)}\n{indent 2 (block noText)}\n))\n{rest}", n₃)
  | _, .closure (input := input) (output := output) ref captured k, n =>
      let closure := fresh "f" n
      let (rest, next) := renderExpr render names (k closure) (n + 1)
      (s!"(let {closure} {(Tp.fn input output).sexp} " ++
        s!"(closure {renderRef ref names} {captured}))\n{rest}", next)
  | _, .app (output := output) fn arg k, n =>
      let result := fresh "v" n
      let (rest, next) := renderExpr render names (k result) (n + 1)
      (s!"(let {result} {output.sexp} (app {fn} {arg}))\n{rest}", next)
  | _, .op operation input blocks k, n =>
      let renderedBlocks := (render.branches operation).foldl (init := ("", n))
        fun (text, next) branch =>
          let arg := fresh "b" next
          let (body, after) := renderExpr render names (blocks branch arg) (next + 1)
          let rendered := s!"(branch {arg}\n{indent 2 (block body)}\n)"
          (if text.isEmpty then rendered else text ++ "\n" ++ rendered, after)
      let result := fresh "v" renderedBlocks.2
      let (rest, next) := renderExpr render names (k result) (renderedBlocks.2 + 1)
      let operationText := if renderedBlocks.1.isEmpty then
          s!"(op {render.opName operation} {input})"
        else
          s!"(op {render.opName operation} {input}\n{indent 2 renderedBlocks.1}\n)"
      (s!"(let {result} {(H.output operation).sexp}\n" ++
        s!"{indent 2 operationText}\n)\n{rest}", next)

private def renderMainArgs : (args : List Tp) → Nat →
    MainArgs SexpV args × String × Nat
  | [], n => (.nil, "", n)
  | argTp :: args, n =>
      let name := fresh "arg" n
      let (values, binders, next) := renderMainArgs args (n + 1)
      let binder := s!"({name} {argTp.sexp})"
      (.cons name values, if binders.isEmpty then binder else binder ++ " " ++ binders, next)

private def renderDefs {H : Signature} (render : RenderSpec H) :
    {ctx : DefCtx} → Defs H SexpV ctx → Nat → String × DefNames ctx × Nat
  | [], .nil, n => ("", .nil, n)
  | _ :: _, .add (decl := decl) prior body, n =>
      let (priorText, priorNames, n₁) := renderDefs render prior n
      let fn := fresh "def" n₁
      let captured := fresh "env" (n₁ + 1)
      let input := fresh "x" (n₁ + 2)
      let (bodyText, next) := renderExpr render (.cons fn priorNames)
        (body captured input) (n₁ + 3)
      let definition :=
        s!"(def {fn} ({captured} {decl.captures.sexp}) " ++
          s!"({input} {decl.input.sexp}) {decl.output.sexp}\n" ++
          s!"{indent 2 (block bodyText)}\n)"
      (if priorText.isEmpty then definition else priorText ++ "\n" ++ definition,
        .cons fn priorNames, next)

def serialize {H : Signature} (render : RenderSpec H) {args : List Tp} {output : Tp}
    (code : Code H args output) : String :=
  let program := code.program SexpV
  let (definitions, names, next) := renderDefs render program.defs 0
  let (values, binders, afterArgs) := renderMainArgs args next
  let (mainBody, _) := renderExpr render names (program.main values) afterArgs
  let main := s!"(main ({binders})\n{indent 2 (block mainBody)}\n)"
  let body := if definitions.isEmpty then main else definitions ++ "\n" ++ main
  s!"(program {output.sexp}\n{indent 2 body}\n)\n"

end Freigen.Ast
