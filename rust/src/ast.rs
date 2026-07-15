//! Typed client-side image of the Lean `Ast.Expr` grammar.

use crate::value::Value;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tp {
    Bool,
    Nat,
    Unit,
    Prod(Box<Tp>, Box<Tp>),
    Fn(Box<Tp>, Box<Tp>),
    Array(Box<Tp>),
    Sum(Box<Tp>, Box<Tp>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Fst,
    Snd,
    Inl,
    Inr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Pow,
    Eq,
    Lt,
    Le,
    And,
    Or,
    Pair,
    Push,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum POp {
    AGet,
    ASet,
    Select,
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
    Pop(POp, Vec<Var>),
    MkArr(Vec<Var>),
    If {
        cond: Var,
        then_: Block,
        else_: Block,
    },
    Lam {
        param: Var,
        param_tp: Tp,
        body: Block,
    },
    App {
        function: Var,
        argument: Var,
    },
    SelfCall(Var),
    Op {
        name: String,
        input: Var,
        branches: Vec<Branch>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum Command {
    Let {
        var: Var,
        tp: Tp,
        value: Expr,
    },
    LetRec {
        var: Var,
        param: Var,
        param_tp: Tp,
        result_tp: Tp,
        body: Block,
    },
    Source {
        range: SourceRange,
        body: Block,
    },
    Ret(Var),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Block {
    pub commands: Vec<Command>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    pub result: Tp,
    pub body: Block,
}
