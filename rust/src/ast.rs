//! Typed client-side image of the Lean `Ast.Expr` grammar.

use crate::value::Value;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tp {
    Bool,
    Nat,
    Int,
    Unit,
    Prod(Box<Tp>, Box<Tp>),
    Fn(Box<Tp>, Box<Tp>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Fst,
    Snd,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Eq,
    Lt,
    Le,
    And,
    Or,
    Pair,
}

pub type Var = String;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceRange {
    pub module: String,
    pub start_line: u64,
    pub start_column: u64,
    pub end_line: u64,
    pub end_column: u64,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Branch {
    pub binder: Var,
    pub body: Block,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Lit(Value),
    Un(UnOp, Var),
    Bin(BinOp, Var, Var),
    If {
        cond: Var,
        then_: Block,
        else_: Block,
    },
    Closure { definition: Var, captured: Var },
    App {
        function: Var,
        argument: Var,
    },
    Op {
        name: String,
        input: Var,
        branches: Vec<Branch>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum Command {
    Let { var: Var, tp: Tp, value: Expr },
    Source { range: SourceRange, body: Block },
    Ret(Var),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Block {
    pub commands: Vec<Command>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Definition {
    pub name: Var,
    pub captured: Var,
    pub captured_tp: Tp,
    pub param: Var,
    pub param_tp: Tp,
    pub result_tp: Tp,
    pub body: Block,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Main {
    pub params: Vec<(Var, Tp)>,
    pub body: Block,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    pub result: Tp,
    pub definitions: Vec<Definition>,
    pub main: Main,
}
