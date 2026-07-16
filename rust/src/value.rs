//! Runtime values — the Rust image of `Tp.denote`.

use std::fmt;

use num_bigint::{BigInt, BigUint};

/// A runtime value of some object type.
///
/// Natural numbers are arbitrary-precision.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Bool(bool),
    Nat(BigUint),
    Int(BigInt),
    Unit,
    Pair(Box<Value>, Box<Value>),
    /// The image of a literal with no serializable payload (a function-typed literal).  Inspecting
    /// it in any primitive is a runtime error.
    Opaque,
    /// A definition reference paired with its explicitly captured value.
    Closure {
        param: String,
        body: crate::ast::Block,
        env: std::collections::HashMap<String, Value>,
        definitions: std::collections::HashMap<String, crate::ast::Definition>,
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
            Value::Int(n) => write!(f, "{n}"),
            Value::Unit => write!(f, "unit"),
            Value::Pair(a, b) => write!(f, "({a} {b})"),
            Value::Opaque => write!(f, "opaque"),
            Value::Closure { .. } => write!(f, "<closure>"),
        }
    }
}
