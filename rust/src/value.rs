//! Runtime values — the Rust image of `Tp.denote`.

use std::fmt;

use num_bigint::BigUint;

/// A runtime value of some object type.
///
/// Natural numbers are arbitrary-precision.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Bool(bool),
    Nat(BigUint),
    Unit,
    Pair(Box<Value>, Box<Value>),
    Array(Vec<Value>),
    Inl(Box<Value>),
    Inr(Box<Value>),
    /// The image of a literal with no serializable payload (a function-typed literal).  Inspecting
    /// it in any primitive is a runtime error.
    Opaque,
    /// A **function value**: a suspended block closing over its captured environment; applying
    /// it binds `param` and runs `body`.
    Closure {
        param: String,
        body: crate::ast::Block,
        env: std::collections::HashMap<String, Value>,
        recursive: bool,
    },
}

impl Value {
    /// A `Nat` from anything convertible to a `BigUint`.
    pub fn nat(n: impl Into<BigUint>) -> Value {
        Value::Nat(n.into())
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{b}"),
            Value::Nat(n) => write!(f, "{n}"),
            Value::Unit => write!(f, "unit"),
            Value::Pair(a, b) => write!(f, "({a} {b})"),
            Value::Array(xs) => {
                write!(f, "(")?;
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
            Value::Inl(x) => write!(f, "(inl {x})"),
            Value::Inr(x) => write!(f, "(inr {x})"),
            Value::Opaque => write!(f, "opaque"),
            Value::Closure { .. } => write!(f, "<closure>"),
        }
    }
}
