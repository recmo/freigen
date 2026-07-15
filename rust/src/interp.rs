//! Canonical interpreter for the promoted higher-order AST.

use std::collections::HashMap;

use num_bigint::BigUint;
use num_traits::{ToPrimitive, Zero};

use crate::ast::*;
use crate::value::Value;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Fail,
    Op { name: String, message: String },
    CallDepth,
    Malformed(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Fail => write!(f, "computation failed"),
            Error::Op { name, message } => write!(f, "op `{name}` failed: {message}"),
            Error::CallDepth => write!(f, "call depth exceeded"),
            Error::Malformed(message) => write!(f, "malformed program: {message}"),
        }
    }
}

impl std::error::Error for Error {}

type Result<T> = std::result::Result<T, Error>;
type Env = HashMap<Var, Value>;

fn malformed<T>(message: impl Into<String>) -> Result<T> {
    Err(Error::Malformed(message.into()))
}

/// A target-signature interpreter. Branches are ordered exactly as the signature renderer emits
/// them; running a branch supplies the dynamically bound branch input.
pub trait Handler {
    fn op(&mut self, name: &str, input: Value, branches: &mut BranchCalls<'_, '_>)
        -> Result<Value>;
}

pub struct NoCustomOps;

impl Handler for NoCustomOps {
    fn op(
        &mut self,
        name: &str,
        _input: Value,
        _branches: &mut BranchCalls<'_, '_>,
    ) -> Result<Value> {
        Err(Error::Op {
            name: name.to_owned(),
            message: "no denotation injected".into(),
        })
    }
}

/// Runnable closures for one higher-order operation's branches.
pub struct BranchCalls<'a, 'p> {
    interp: &'a Interpreter<'p>,
    branches: &'a [Branch],
    env: Env,
    recursive: Option<Value>,
    depth: usize,
}

impl BranchCalls<'_, '_> {
    pub fn len(&self) -> usize {
        self.branches.len()
    }

    pub fn is_empty(&self) -> bool {
        self.branches.is_empty()
    }

    pub fn run<H: Handler>(
        &mut self,
        handler: &mut H,
        index: usize,
        argument: Value,
    ) -> Result<Value> {
        let branch = self
            .branches
            .get(index)
            .ok_or_else(|| Error::Malformed(format!("operation has no branch at index {index}")))?;
        let mut env = self.env.clone();
        env.insert(branch.binder.clone(), argument);
        self.interp.eval_block(
            handler,
            &mut env,
            self.recursive.clone(),
            self.depth,
            &branch.body,
        )
    }
}

pub struct Interpreter<'p> {
    program: &'p Program,
    pub max_call_depth: usize,
}

impl<'p> Interpreter<'p> {
    pub fn new(program: &'p Program) -> Self {
        Self {
            program,
            max_call_depth: 128,
        }
    }

    pub fn run<H: Handler>(&self, handler: &mut H) -> Result<Value> {
        self.eval_block(handler, &mut Env::new(), None, 0, &self.program.body)
    }

    /// Compatibility spelling for callers of the previous SDK. Promoted programs are closed.
    pub fn run_main<H: Handler>(&self, handler: &mut H, args: Vec<Value>) -> Result<Value> {
        if !args.is_empty() {
            return malformed("promoted programs are closed and take no main arguments");
        }
        self.run(handler)
    }

    fn eval_block<H: Handler>(
        &self,
        handler: &mut H,
        env: &mut Env,
        recursive: Option<Value>,
        depth: usize,
        block: &Block,
    ) -> Result<Value> {
        for command in &block.commands {
            match command {
                Command::Let { var, value, .. } => {
                    let value = self.eval_expr(handler, env, recursive.clone(), depth, value)?;
                    env.insert(var.clone(), value);
                }
                Command::LetRec {
                    var, param, body, ..
                } => {
                    env.insert(
                        var.clone(),
                        Value::Closure {
                            param: param.clone(),
                            body: body.clone(),
                            env: env.clone(),
                            recursive: true,
                        },
                    );
                }
                Command::Source { body, .. } => {
                    return self.eval_block(handler, env, recursive, depth, body);
                }
                Command::Ret(var) => return lookup(env, var),
            }
        }
        malformed("block has no return")
    }

    fn apply<H: Handler>(
        &self,
        handler: &mut H,
        closure: Value,
        argument: Value,
        depth: usize,
    ) -> Result<Value> {
        if depth >= self.max_call_depth {
            return Err(Error::CallDepth);
        }
        match closure {
            Value::Closure {
                param,
                body,
                mut env,
                recursive,
            } => {
                let self_closure = recursive.then(|| Value::Closure {
                    param: param.clone(),
                    body: body.clone(),
                    env: env.clone(),
                    recursive: true,
                });
                env.insert(param, argument);
                self.eval_block(handler, &mut env, self_closure, depth + 1, &body)
            }
            other => malformed(format!("application of non-function `{other}`")),
        }
    }

    fn eval_expr<H: Handler>(
        &self,
        handler: &mut H,
        env: &mut Env,
        recursive: Option<Value>,
        depth: usize,
        expr: &Expr,
    ) -> Result<Value> {
        match expr {
            Expr::Lit(value) => Ok(value.clone()),
            Expr::Un(op, value) => eval_un(*op, lookup(env, value)?),
            Expr::Bin(op, left, right) => eval_bin(*op, lookup(env, left)?, lookup(env, right)?),
            Expr::Pop(op, args) => {
                let args = args
                    .iter()
                    .map(|arg| lookup(env, arg))
                    .collect::<Result<Vec<_>>>()?;
                eval_pop(op, args)
            }
            Expr::MkArr(values) => Ok(Value::Array(
                values
                    .iter()
                    .map(|value| lookup(env, value))
                    .collect::<Result<Vec<_>>>()?,
            )),
            Expr::If { cond, then_, else_ } => {
                let chosen = if as_bool(lookup(env, cond)?)? {
                    then_
                } else {
                    else_
                };
                self.eval_block(handler, &mut env.clone(), recursive, depth, chosen)
            }
            Expr::Lam { param, body, .. } => Ok(Value::Closure {
                param: param.clone(),
                body: body.clone(),
                env: env.clone(),
                recursive: false,
            }),
            Expr::App { function, argument } => self.apply(
                handler,
                lookup(env, function)?,
                lookup(env, argument)?,
                depth,
            ),
            Expr::SelfCall(argument) => {
                let closure =
                    recursive.ok_or_else(|| Error::Malformed("self-call outside letrec".into()))?;
                self.apply(handler, closure, lookup(env, argument)?, depth)
            }
            Expr::Op {
                name,
                input,
                branches,
            } => {
                let input = lookup(env, input)?;
                let mut calls = BranchCalls {
                    interp: self,
                    branches,
                    env: env.clone(),
                    recursive,
                    depth,
                };
                handler.op(name, input, &mut calls)
            }
        }
    }
}

fn lookup(env: &Env, var: &Var) -> Result<Value> {
    env.get(var)
        .cloned()
        .ok_or_else(|| Error::Malformed(format!("unbound variable `{var}`")))
}

fn as_nat(value: Value) -> Result<BigUint> {
    match value {
        Value::Nat(value) => Ok(value),
        other => malformed(format!("expected nat, got `{other}`")),
    }
}

fn as_bool(value: Value) -> Result<bool> {
    match value {
        Value::Bool(value) => Ok(value),
        other => malformed(format!("expected bool, got `{other}`")),
    }
}

fn eval_un(op: UnOp, value: Value) -> Result<Value> {
    match (op, value) {
        (UnOp::Not, Value::Bool(value)) => Ok(Value::Bool(!value)),
        (UnOp::Fst, Value::Pair(left, _)) => Ok(*left),
        (UnOp::Snd, Value::Pair(_, right)) => Ok(*right),
        (UnOp::Inl, value) => Ok(Value::Inl(Box::new(value))),
        (UnOp::Inr, value) => Ok(Value::Inr(Box::new(value))),
        (op, value) => malformed(format!("unary op {op:?} applied to `{value}`")),
    }
}

fn eval_bin(op: BinOp, left: Value, right: Value) -> Result<Value> {
    match op {
        BinOp::Pair => Ok(Value::Pair(Box::new(left), Box::new(right))),
        BinOp::And => Ok(Value::Bool(as_bool(left)? && as_bool(right)?)),
        BinOp::Or => Ok(Value::Bool(as_bool(left)? || as_bool(right)?)),
        BinOp::Add => Ok(Value::Nat(as_nat(left)? + as_nat(right)?)),
        BinOp::Sub => {
            let (left, right) = (as_nat(left)?, as_nat(right)?);
            Ok(Value::Nat(if left >= right {
                left - right
            } else {
                BigUint::zero()
            }))
        }
        BinOp::Mul => Ok(Value::Nat(as_nat(left)? * as_nat(right)?)),
        BinOp::Eq => Ok(Value::Bool(as_nat(left)? == as_nat(right)?)),
        BinOp::Lt => Ok(Value::Bool(as_nat(left)? < as_nat(right)?)),
        BinOp::Le => Ok(Value::Bool(as_nat(left)? <= as_nat(right)?)),
        BinOp::Push => match left {
            Value::Array(mut values) => {
                values.push(right);
                Ok(Value::Array(values))
            }
            other => malformed(format!("push on `{other}`")),
        },
        unsupported => malformed(format!("unsupported primitive {unsupported:?}")),
    }
}

fn eval_pop(op: &POp, mut args: Vec<Value>) -> Result<Value> {
    match op {
        POp::Select if args.len() == 3 => {
            let else_ = args.pop().unwrap();
            let then_ = args.pop().unwrap();
            Ok(if as_bool(args.pop().unwrap())? {
                then_
            } else {
                else_
            })
        }
        POp::AGet if args.len() == 2 => {
            let index = as_nat(args.pop().unwrap())?.to_usize().ok_or(Error::Fail)?;
            match args.pop().unwrap() {
                Value::Array(values) => values.get(index).cloned().ok_or(Error::Fail),
                other => malformed(format!("indexing `{other}`")),
            }
        }
        _ => malformed(format!("unsupported partial primitive {op:?}")),
    }
}
