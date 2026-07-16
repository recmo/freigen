//! Rust consumer for Freigen's typed higher-order AST artifacts.
//!
//! [`parse_program`] preserves level-one definitions, dynamically bound operation branches,
//! function values, and source annotations. [`interp::Interpreter`] executes artifacts using a
//! client-supplied higher-order operation handler.

pub mod ast;
pub mod interp;
pub mod parse;
pub mod sexp;
pub mod value;

pub use parse::{parse_program, ParseError};

#[cfg(test)]
mod tests {
    use crate::interp::{BranchCalls, Error, Handler, Interpreter, NoCustomOps};
    use crate::parse_program;
    use crate::value::Value;

    fn run(src: &str) -> Result<Value, Error> {
        let program = parse_program(src).expect("parse");
        Interpreter::new(&program).run(&mut NoCustomOps)
    }

    #[test]
    fn arithmetic_and_expression_if() {
        let src = r#"
          (program nat
            (main () (block
              (let v0 nat (lit 7))
              (let v1 nat (lit 5))
              (let v2 bool (lt v1 v0))
              (let v5 nat (if v2
                (block (let v3 nat (add v0 v1)) (ret v3))
                (block (let v4 nat (lit 0)) (ret v4))))
              (ret v5))))"#;
        assert_eq!(run(src).unwrap(), Value::nat(12u32));
    }

    #[test]
    fn explicit_closure_and_application() {
        let src = r#"
          (program nat
            (def twice (captured unit) (x0 nat) nat
              (block
                (let v1 nat (add x0 x0))
                (ret v1)))
            (main () (block
              (let v0 unit (lit unit))
              (let f2 (fn nat nat) (closure twice v0))
              (let v3 nat (lit 9))
              (let v4 nat (app f2 v3))
              (ret v4))))"#;
        assert_eq!(run(src).unwrap(), Value::nat(18u32));
    }

    #[test]
    fn level_one_recursion_and_source_ranges() {
        let src = r#"
          (program nat
            (def def0 (captured unit) (x0 nat) nat
              (source Demo 1 0 9 1
              (block
                (let v1 nat (lit 0))
                (let v2 bool (eq x0 v1))
                (let v6 nat (if v2
                  (block (let v3 nat (lit 0)) (ret v3))
                  (block
                    (let v4 nat (lit 1))
                    (let v5 nat (sub x0 v4))
                    (let v6u unit (lit unit))
                    (let f7 (fn nat nat) (closure def0 v6u))
                    (let v7 nat (app f7 v5))
                    (let v8 nat (add v7 v4))
                    (ret v8))))
                (ret v6))))
            (main ()
              (block
                (let v9 nat (lit 7))
                (let v9u unit (lit unit))
                (let f10 (fn nat nat) (closure def0 v9u))
                (let v10 nat (app f10 v9))
                (ret v10))))"#;
        assert_eq!(run(src).unwrap(), Value::nat(7u32));
    }

    struct Circuit;

    impl Handler for Circuit {
        fn op(
            &mut self,
            name: &str,
            input: Value,
            branches: &mut BranchCalls<'_, '_>,
        ) -> Result<Value, Error> {
            match (name, input) {
                ("assert", Value::Bool(true)) if branches.is_empty() => Ok(Value::Unit),
                ("assert", Value::Bool(false)) => Err(Error::Op {
                    name: name.into(),
                    message: "assertion failed".into(),
                }),
                ("hint", Value::Unit) if branches.len() == 1 => branches.run(self, 0, Value::Unit),
                ("withNat", Value::Unit) if branches.len() == 1 => {
                    branches.run(self, 0, Value::nat(42u32))
                }
                (_, input) => Err(Error::Op {
                    name: name.into(),
                    message: format!("unsupported input `{input}`"),
                }),
            }
        }
    }

    #[test]
    fn dynamically_bound_operation_branch() {
        let src = r#"
          (program nat
            (main () (block
              (let v0 unit (lit unit))
              (let v3 nat (op withNat v0
                (branch b1
                  (block
                    (ret b1)))))
              (ret v3))))"#;
        let program = parse_program(src).unwrap();
        assert_eq!(
            Interpreter::new(&program).run(&mut Circuit).unwrap(),
            Value::nat(42u32)
        );
    }

    #[test]
    fn main_arguments() {
        let src = "(program nat (main ((x nat)) (block (ret x))))";
        let program = parse_program(src).unwrap();
        assert_eq!(
            Interpreter::new(&program)
                .run_main(&mut NoCustomOps, vec![Value::nat(23u32)])
                .unwrap(),
            Value::nat(23u32)
        );
    }
}
