//! Parse the uniform `.prog` S-expression format into the typed AST.
//!
//! The grammar is pinned in `Freigen/Ast/Sexp.lean` (the emitter); this module is its inverse.
//! Numeric literals are parsed *type-directed* from the binder annotation (`nat`, `(zmod p)`,
//! `(fin n)`), so a parsed [`Value`] is always fully typed — a field element knows its modulus.

use std::fmt;

use num_bigint::BigUint;

use crate::ast::*;
use crate::sexp::{parse_sexp, Sexp, SexpError};
use crate::value::Value;

/// A parse error: either malformed S-expression syntax or a well-formed S-expression that does
/// not match the `.prog` grammar.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseError {
    Sexp(SexpError),
    Grammar(String),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::Sexp(e) => write!(f, "{e}"),
            ParseError::Grammar(m) => write!(f, "grammar error: {m}"),
        }
    }
}

impl std::error::Error for ParseError {}

impl From<SexpError> for ParseError {
    fn from(e: SexpError) -> Self {
        ParseError::Sexp(e)
    }
}

type Result<T> = std::result::Result<T, ParseError>;

fn err<T>(msg: impl Into<String>) -> Result<T> {
    Err(ParseError::Grammar(msg.into()))
}

fn as_list<'a>(s: &'a Sexp, what: &str) -> Result<&'a [Sexp]> {
    match s {
        Sexp::List(items) => Ok(items),
        _ => err(format!("expected {what} (a list), got `{s}`")),
    }
}

fn as_atom<'a>(s: &'a Sexp, what: &str) -> Result<&'a str> {
    match s {
        Sexp::Atom(a) => Ok(a),
        _ => err(format!("expected {what} (an atom), got `{s}`")),
    }
}

/// Modules and operation names are bare tokens; their grammatical position disambiguates them.
fn as_name<'a>(s: &'a Sexp, what: &str) -> Result<&'a str> {
    as_atom(s, what)
}

fn as_u64(s: &Sexp, what: &str) -> Result<u64> {
    as_atom(s, what)?
        .parse()
        .map_err(|_| ParseError::Grammar(format!("expected {what} (a u64), got `{s}`")))
}

fn as_biguint(s: &Sexp, what: &str) -> Result<BigUint> {
    as_atom(s, what)?
        .parse()
        .map_err(|_| ParseError::Grammar(format!("expected {what} (a numeral), got `{s}`")))
}

fn as_var(s: &Sexp) -> Result<Var> {
    Ok(as_atom(s, "a variable")?.to_owned())
}

/// Parse an object type.
fn parse_tp(s: &Sexp) -> Result<Tp> {
    match s {
        Sexp::Atom(a) => match a.as_str() {
            "bool" => Ok(Tp::Bool),
            "nat" => Ok(Tp::Nat),
            "unit" => Ok(Tp::Unit),
            _ => err(format!("unknown type `{a}`")),
        },
        Sexp::List(items) => {
            let head = as_atom(
                items
                    .first()
                    .ok_or_else(|| ParseError::Grammar("empty list is not a type".into()))?,
                "a type head",
            )?;
            match (head, &items[1..]) {
                ("zmod", [p]) => Ok(Tp::ZMod(as_biguint(p, "a modulus")?)),
                ("fin", [n]) => Ok(Tp::Fin(as_u64(n, "a Fin bound")?)),
                ("vec", [a, n]) => Ok(Tp::Vec(
                    Box::new(parse_tp(a)?),
                    as_u64(n, "a vector length")?,
                )),
                ("array", [a]) => Ok(Tp::Array(Box::new(parse_tp(a)?))),
                ("prod", [a, b]) => Ok(Tp::Prod(Box::new(parse_tp(a)?), Box::new(parse_tp(b)?))),
                ("sum", [a, b]) => Ok(Tp::Sum(Box::new(parse_tp(a)?), Box::new(parse_tp(b)?))),
                ("fn", [a, b]) => Ok(Tp::Fn(Box::new(parse_tp(a)?), Box::new(parse_tp(b)?))),
                _ => err(format!("malformed type `{s}`")),
            }
        }
        Sexp::Str(_) => err(format!("expected a type, got string `{s}`")),
    }
}

/// Parse a literal value, directed by its object type.
fn parse_value(tp: &Tp, s: &Sexp) -> Result<Value> {
    match tp {
        Tp::Bool => match as_atom(s, "a bool literal")? {
            "true" => Ok(Value::Bool(true)),
            "false" => Ok(Value::Bool(false)),
            other => err(format!("expected a bool literal, got `{other}`")),
        },
        Tp::Nat => Ok(Value::Nat(as_biguint(s, "a nat literal")?)),
        Tp::Unit => match as_atom(s, "a unit literal")? {
            "unit" => Ok(Value::Unit),
            other => err(format!("expected `unit`, got `{other}`")),
        },
        Tp::ZMod(p) => {
            let v = as_biguint(s, "a field literal")?;
            Ok(Value::Field {
                val: v % p,
                modulus: p.clone(),
            })
        }
        Tp::Fin(n) => {
            let v = as_u64(s, "a fin literal")?;
            if v < *n {
                Ok(Value::Fin { val: v, bound: *n })
            } else {
                err(format!("fin literal {v} out of bound {n}"))
            }
        }
        Tp::Vec(a, n) => {
            let elems = as_list(s, "a vec literal")?;
            if elems.len() as u64 != *n {
                return err(format!(
                    "vec literal has {} elements, type says {n}",
                    elems.len()
                ));
            }
            Ok(Value::Vec(
                elems
                    .iter()
                    .map(|e| parse_value(a, e))
                    .collect::<Result<Vec<_>>>()?,
            ))
        }
        Tp::Array(a) => {
            let elems = as_list(s, "an array literal")?;
            Ok(Value::Array(
                elems
                    .iter()
                    .map(|e| parse_value(a, e))
                    .collect::<Result<Vec<_>>>()?,
            ))
        }
        Tp::Prod(a, b) => {
            let items = as_list(s, "a pair literal")?;
            match items {
                [x, y] => Ok(Value::Pair(
                    Box::new(parse_value(a, x)?),
                    Box::new(parse_value(b, y)?),
                )),
                _ => err(format!("expected a two-element pair literal, got `{s}`")),
            }
        }
        Tp::Sum(a, b) => {
            let items = as_list(s, "a sum literal")?;
            match items {
                [head, x] if as_atom(head, "a literal head")? == "inl" => {
                    Ok(Value::Inl(Box::new(parse_value(a, x)?)))
                }
                [head, x] if as_atom(head, "a literal head")? == "inr" => {
                    Ok(Value::Inr(Box::new(parse_value(b, x)?)))
                }
                _ => err(format!("expected `(inl …)`/`(inr …)`, got `{s}`")),
            }
        }
        Tp::Fn(_, _) => match as_atom(s, "an opaque literal")? {
            "opaque" => Ok(Value::Opaque),
            other => err(format!("expected `opaque` for a fn literal, got `{other}`")),
        },
    }
}

/// A primitive op is its own expression head — the names are disjoint from the structural
/// keywords (`lit`, `call`, `fold`, …), so no `un`/`bin`/`pop` class tag is needed.
fn un_op(head: &str) -> Option<UnOp> {
    Some(match head {
        "not" => UnOp::Not,
        "fst" => UnOp::Fst,
        "snd" => UnOp::Snd,
        "inl" => UnOp::Inl,
        "inr" => UnOp::Inr,
        "to-array" => UnOp::ToArray,
        "fin-val" => UnOp::FinVal,
        _ => return None,
    })
}

fn bin_op(head: &str) -> Option<BinOp> {
    Some(match head {
        "add" => BinOp::Add,
        "sub" => BinOp::Sub,
        "mul" => BinOp::Mul,
        "pow" => BinOp::Pow,
        "eq" => BinOp::Eq,
        "lt" => BinOp::Lt,
        "le" => BinOp::Le,
        "and" => BinOp::And,
        "or" => BinOp::Or,
        "addf" => BinOp::AddF,
        "subf" => BinOp::SubF,
        "mulf" => BinOp::MulF,
        "powf" => BinOp::PowF,
        "pair" => BinOp::Pair,
        "push" => BinOp::Push,
        _ => return None,
    })
}

fn pop_op(head: &str) -> Option<POp> {
    Some(match head {
        "vget" => POp::VGet,
        "vset" => POp::VSet,
        "aget" => POp::AGet,
        "aset" => POp::ASet,
        "select" => POp::Select,
        _ => return None,
    })
}

fn parse_branch(s: &Sexp) -> Result<Branch> {
    let items = as_list(s, "an operation branch")?;
    match items {
        [head, binder, body] if as_atom(head, "a branch head")? == "branch" => Ok(Branch {
            binder: as_var(binder)?,
            body: parse_body(body)?,
        }),
        _ => err(format!("expected `(branch binder body)`, got `{s}`")),
    }
}

/// Parse a let-bound expression; `tp` directs literal parsing.
fn parse_expr(tp: &Tp, s: &Sexp) -> Result<Expr> {
    let items = as_list(s, "an expression")?;
    let head = as_atom(
        items
            .first()
            .ok_or_else(|| ParseError::Grammar("empty expression".into()))?,
        "an expression head",
    )?;
    match (head, &items[1..]) {
        ("lit", [v]) => Ok(Expr::Lit(parse_value(tp, v)?)),
        ("arr-to-vec", [n, a]) => Ok(Expr::Pop(
            POp::ArrToVec(as_u64(n, "a vector length")?),
            vec![as_var(a)?],
        )),
        ("nat-to-fin", [n, a]) => Ok(Expr::Pop(
            POp::NatToFin(as_u64(n, "a Fin bound")?),
            vec![as_var(a)?],
        )),
        ("vec", args) => Ok(Expr::MkVec(
            args.iter().map(as_var).collect::<Result<Vec<_>>>()?,
        )),
        ("arr", args) => Ok(Expr::MkArr(
            args.iter().map(as_var).collect::<Result<Vec<_>>>()?,
        )),
        ("if", [cond, then_, else_]) => Ok(Expr::If {
            cond: as_var(cond)?,
            then_: parse_body(then_)?,
            else_: parse_body(else_)?,
        }),
        ("op", [name, input, branches @ ..]) => Ok(Expr::Op {
            name: as_name(name, "an op name")?.to_owned(),
            input: as_var(input)?,
            branches: branches
                .iter()
                .map(parse_branch)
                .collect::<Result<Vec<_>>>()?,
        }),
        ("self", [arg]) => Ok(Expr::SelfCall(as_var(arg)?)),
        ("lam", [binder, body]) => {
            let binder = as_list(binder, "a lambda binder")?;
            let [v, param_tp] = binder else {
                return err(format!("lam binder expects (var type), got `{s}`"));
            };
            Ok(Expr::Lam {
                param: as_var(v)?,
                param_tp: parse_tp(param_tp)?,
                body: parse_body(body)?,
            })
        }
        ("app", [function, argument]) => Ok(Expr::App {
            function: as_var(function)?,
            argument: as_var(argument)?,
        }),
        (head, args) => {
            if let Some(o) = un_op(head) {
                let [a] = args else {
                    return err(format!("unary op `{head}` expects one argument, got `{s}`"));
                };
                Ok(Expr::Un(o, as_var(a)?))
            } else if let Some(o) = bin_op(head) {
                let [a, b] = args else {
                    return err(format!(
                        "binary op `{head}` expects two arguments, got `{s}`"
                    ));
                };
                Ok(Expr::Bin(o, as_var(a)?, as_var(b)?))
            } else if let Some(o) = pop_op(head) {
                Ok(Expr::Pop(
                    o,
                    args.iter().map(as_var).collect::<Result<Vec<_>>>()?,
                ))
            } else {
                err(format!("malformed expression `{s}`"))
            }
        }
    }
}

fn parse_block(s: &Sexp) -> Result<Block> {
    let items = as_list(s, "a block")?;
    match items.split_first() {
        Some((head, rest)) if as_atom(head, "a block head")? == "block" && !rest.is_empty() => {
            Ok(Block {
                commands: rest.iter().map(parse_command).collect::<Result<Vec<_>>>()?,
            })
        }
        _ => err(format!("expected `(block …)`, got `{s}`")),
    }
}

fn parse_source(items: &[Sexp], original: &Sexp) -> Result<Command> {
    let [module, start_line, start_column, end_line, end_column, body] = items else {
        return err(format!("malformed source annotation `{original}`"));
    };
    Ok(Command::Source {
        range: SourceRange {
            module: as_name(module, "a source module")?.to_owned(),
            start_line: as_u64(start_line, "a source line")?,
            start_column: as_u64(start_column, "a source column")?,
            end_line: as_u64(end_line, "a source line")?,
            end_column: as_u64(end_column, "a source column")?,
        },
        body: parse_body(body)?,
    })
}

fn parse_command(s: &Sexp) -> Result<Command> {
    let items = as_list(s, "a statement")?;
    let Some((head, args)) = items.split_first() else {
        return err("empty statement");
    };
    match (as_atom(head, "a statement head")?, args) {
        ("let", [var, tp, expr]) => {
            let tp = parse_tp(tp)?;
            Ok(Command::Let {
                var: as_var(var)?,
                value: parse_expr(&tp, expr)?,
                tp,
            })
        }
        ("letrec", [var, binder, result_tp, body]) => {
            let binder = as_list(binder, "a letrec binder")?;
            let [param, param_tp] = binder else {
                return err(format!("letrec binder expects (var type), got `{s}`"));
            };
            Ok(Command::LetRec {
                var: as_var(var)?,
                param: as_var(param)?,
                param_tp: parse_tp(param_tp)?,
                result_tp: parse_tp(result_tp)?,
                body: parse_body(body)?,
            })
        }
        ("source", args) => parse_source(args, s),
        ("ret", [var]) => Ok(Command::Ret(as_var(var)?)),
        _ => err(format!("malformed statement `{s}`")),
    }
}

fn parse_body(s: &Sexp) -> Result<Block> {
    let items = as_list(s, "a body")?;
    let Some((head, args)) = items.split_first() else {
        return err("empty body");
    };
    match as_atom(head, "a body head")? {
        "block" => parse_block(s),
        "source" => Ok(Block {
            commands: vec![parse_source(args, s)?],
        }),
        _ => err(format!("expected a block or source annotation, got `{s}`")),
    }
}

/// Parse a whole `.prog` artifact.
pub fn parse_program(src: &str) -> Result<Program> {
    let sexp = parse_sexp(src)?;
    let items = as_list(&sexp, "a program")?;
    match items {
        [head, result, body] if as_atom(head, "the program head")? == "program" => Ok(Program {
            result: parse_tp(result)?,
            body: parse_body(body)?,
        }),
        _ => err(format!("expected `(program type body)`, got `{sexp}`")),
    }
}
