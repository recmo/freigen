//! Parse the uniform `.prog` S-expression format into the typed AST.
//!
//! The grammar is pinned in `Freigen/Ast/Sexp.lean` (the emitter); this module is its inverse.
//! Numeric literals are parsed *type-directed* from their binder annotations.

use std::fmt;

use num_bigint::{BigInt, BigUint};

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
            "int" => Ok(Tp::Int),
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
                ("prod", [a, b]) => Ok(Tp::Prod(Box::new(parse_tp(a)?), Box::new(parse_tp(b)?))),
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
        Tp::Int => Ok(Value::Int(
            as_atom(s, "an int literal")?
                .parse::<BigInt>()
                .map_err(|_| ParseError::Grammar(format!("expected an int literal, got `{s}`")))?,
        )),
        Tp::Unit => match as_atom(s, "a unit literal")? {
            "unit" => Ok(Value::Unit),
            other => err(format!("expected `unit`, got `{other}`")),
        },
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
        _ => return None,
    })
}

fn bin_op(head: &str) -> Option<BinOp> {
    Some(match head {
        "add" => BinOp::Add,
        "sub" => BinOp::Sub,
        "mul" => BinOp::Mul,
        "eq" => BinOp::Eq,
        "lt" => BinOp::Lt,
        "le" => BinOp::Le,
        "and" => BinOp::And,
        "or" => BinOp::Or,
        "pair" => BinOp::Pair,
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
        ("closure", [definition, captured]) => Ok(Expr::Closure {
            definition: as_var(definition)?,
            captured: as_var(captured)?,
        }),
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
    let [head, result, level @ ..] = items else {
        return err(format!("expected `(program type def* main)`, got `{sexp}`"));
    };
    if as_atom(head, "the program head")? != "program" || level.is_empty() {
        return err(format!("expected `(program type def* main)`, got `{sexp}`"));
    }
    let mut definitions = Vec::new();
    for item in &level[..level.len() - 1] {
        let fields = as_list(item, "a definition")?;
        let [def, name, captured_binder, binder, result_tp, body] = fields else {
            return err(format!(
                "expected `(def name (captured type) (arg type) type body)`, got `{item}`"
            ));
        };
        if as_atom(def, "a definition head")? != "def" {
            return err(format!("expected a definition before main, got `{item}`"));
        }
        let captured_binder = as_list(captured_binder, "a captured-value binder")?;
        let [captured, captured_tp] = captured_binder else {
            return err(format!(
                "captured-value binder expects (var type), got `{item}`"
            ));
        };
        let binder = as_list(binder, "a definition binder")?;
        let [param, param_tp] = binder else {
            return err(format!(
                "definition binder expects (var type), got `{item}`"
            ));
        };
        definitions.push(Definition {
            name: as_var(name)?,
            captured: as_var(captured)?,
            captured_tp: parse_tp(captured_tp)?,
            param: as_var(param)?,
            param_tp: parse_tp(param_tp)?,
            result_tp: parse_tp(result_tp)?,
            body: parse_body(body)?,
        });
    }
    let main = level.last().unwrap();
    let fields = as_list(main, "main")?;
    let [main_head, params, body] = fields else {
        return err(format!(
            "expected `(main ((arg type) …) body)`, got `{main}`"
        ));
    };
    if as_atom(main_head, "the main head")? != "main" {
        return err(format!("program must end in main, got `{main}`"));
    }
    let params = as_list(params, "main parameters")?
        .iter()
        .map(|binder| {
            let fields = as_list(binder, "a main binder")?;
            let [name, tp] = fields else {
                return err(format!("main binder expects (var type), got `{binder}`"));
            };
            Ok((as_var(name)?, parse_tp(tp)?))
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(Program {
        result: parse_tp(result)?,
        definitions,
        main: Main {
            params,
            body: parse_body(body)?,
        },
    })
}
