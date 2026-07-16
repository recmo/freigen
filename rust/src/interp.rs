//! Canonical interpreter for the promoted higher-order AST.

use std::collections::HashMap;

use num_bigint::BigUint;
use num_traits::Zero;

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
type Definitions = HashMap<Var, Definition>;

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
    definitions: Definitions,
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
            &mut self.definitions.clone(),
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
        self.run_main(handler, Vec::new())
    }

    pub fn run_main<H: Handler>(&self, handler: &mut H, args: Vec<Value>) -> Result<Value> {
        if args.len() != self.program.main.params.len() {
            return malformed(format!(
                "main expects {} arguments, got {}",
                self.program.main.params.len(),
                args.len()
            ));
        }
        let mut definitions = Definitions::new();
        for definition in &self.program.definitions {
            definitions.insert(definition.name.clone(), definition.clone());
        }
        let mut env = Env::new();
        for ((name, _), value) in self.program.main.params.iter().zip(args) {
            env.insert(name.clone(), value);
        }
        self.eval_block(
            handler,
            &mut env,
            &mut definitions,
            0,
            &self.program.main.body,
        )
    }

    fn eval_block<H: Handler>(
        &self,
        handler: &mut H,
        env: &mut Env,
        definitions: &mut Definitions,
        depth: usize,
        block: &Block,
    ) -> Result<Value> {
        for command in &block.commands {
            match command {
                Command::Let { var, value, .. } => {
                    let value = self.eval_expr(handler, env, definitions, depth, value)?;
                    env.insert(var.clone(), value);
                }
                Command::Source { body, .. } => {
                    return self.eval_block(handler, env, definitions, depth, body);
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
                mut definitions,
            } => {
                env.insert(param, argument);
                self.eval_block(handler, &mut env, &mut definitions, depth + 1, &body)
            }
            other => malformed(format!("application of non-function `{other}`")),
        }
    }

    fn eval_expr<H: Handler>(
        &self,
        handler: &mut H,
        env: &mut Env,
        definitions: &mut Definitions,
        depth: usize,
        expr: &Expr,
    ) -> Result<Value> {
        match expr {
            Expr::Lit(value) => Ok(value.clone()),
            Expr::Un(op, value) => eval_un(*op, lookup(env, value)?),
            Expr::Bin(op, left, right) => eval_bin(*op, lookup(env, left)?, lookup(env, right)?),
            Expr::If { cond, then_, else_ } => {
                let chosen = if as_bool(lookup(env, cond)?)? {
                    then_
                } else {
                    else_
                };
                self.eval_block(
                    handler,
                    &mut env.clone(),
                    &mut definitions.clone(),
                    depth,
                    chosen,
                )
            }
            Expr::Closure {
                definition,
                captured,
            } => {
                let definition = definitions.get(definition).cloned().ok_or_else(|| {
                    Error::Malformed(format!("unknown definition `{definition}`"))
                })?;
                let mut closure_env = Env::new();
                closure_env.insert(definition.captured, lookup(env, captured)?);
                Ok(Value::Closure {
                    param: definition.param,
                    body: definition.body,
                    env: closure_env,
                    definitions: definitions.clone(),
                })
            }
            Expr::App { function, argument } => self.apply(
                handler,
                lookup(env, function)?,
                lookup(env, argument)?,
                depth,
            ),
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
                    definitions: definitions.clone(),
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
        (op, value) => malformed(format!("unary op {op:?} applied to `{value}`")),
    }
}

fn eval_bin(op: BinOp, left: Value, right: Value) -> Result<Value> {
    match op {
        BinOp::Pair => Ok(Value::Pair(Box::new(left), Box::new(right))),
        BinOp::And => Ok(Value::Bool(as_bool(left)? && as_bool(right)?)),
        BinOp::Or => Ok(Value::Bool(as_bool(left)? || as_bool(right)?)),
        BinOp::Add => match (left, right) {
            (Value::Nat(left), Value::Nat(right)) => Ok(Value::Nat(left + right)),
            (Value::Int(left), Value::Int(right)) => Ok(Value::Int(left + right)),
            (left, right) => malformed(format!("add applied to `{left}` and `{right}`")),
        },
        BinOp::Sub => {
            match (left, right) {
                (Value::Nat(left), Value::Nat(right)) => Ok(Value::Nat(if left >= right {
                    left - right
                } else {
                    BigUint::zero()
                })),
                (Value::Int(left), Value::Int(right)) => Ok(Value::Int(left - right)),
                (left, right) => malformed(format!("sub applied to `{left}` and `{right}`")),
            }
        }
        BinOp::Mul => match (left, right) {
            (Value::Nat(left), Value::Nat(right)) => Ok(Value::Nat(left * right)),
            (Value::Int(left), Value::Int(right)) => Ok(Value::Int(left * right)),
            (left, right) => malformed(format!("mul applied to `{left}` and `{right}`")),
        },
        BinOp::Eq => match (left, right) {
            (Value::Nat(left), Value::Nat(right)) => Ok(Value::Bool(left == right)),
            (Value::Int(left), Value::Int(right)) => Ok(Value::Bool(left == right)),
            (Value::Bool(left), Value::Bool(right)) => Ok(Value::Bool(left == right)),
            (Value::Unit, Value::Unit) => Ok(Value::Bool(true)),
            (left, right) => malformed(format!("eq applied to `{left}` and `{right}`")),
        },
        BinOp::Lt => match (left, right) {
            (Value::Nat(left), Value::Nat(right)) => Ok(Value::Bool(left < right)),
            (Value::Int(left), Value::Int(right)) => Ok(Value::Bool(left < right)),
            (left, right) => malformed(format!("lt applied to `{left}` and `{right}`")),
        },
        BinOp::Le => match (left, right) {
            (Value::Nat(left), Value::Nat(right)) => Ok(Value::Bool(left <= right)),
            (Value::Int(left), Value::Int(right)) => Ok(Value::Bool(left <= right)),
            (left, right) => malformed(format!("le applied to `{left}` and `{right}`")),
        },
    }
}
