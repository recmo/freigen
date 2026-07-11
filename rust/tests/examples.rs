//! End-to-end tests over the goldens project (`examples/client/`).
//!
//! The client project `#compile`s its programs into `.prog` artifacts; CI pins them as goldens in
//! `examples/client/expected/`.  These tests close the loop: parse each golden with the SDK and
//! **execute** it with the canonical interpreter under the circuit DSL's witness-generation
//! denotation.

use std::fs;
use std::path::PathBuf;

use freigen::interp::{BranchCalls, Error, Handler, Interpreter};
use freigen::parse_program;
use freigen::value::Value;

fn goldens_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../examples/client/expected")
}

fn read_golden(name: &str) -> String {
    let path = goldens_dir().join(name);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()))
}

/// Circuit witness generation: assertions are checked and a hint runs its sole branch.
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
            (_, input) => Err(Error::Op {
                name: name.into(),
                message: format!("no denotation for input {input}"),
            }),
        }
    }
}

/// Every golden artifact must parse with the SDK.
#[test]
fn all_goldens_parse() {
    let mut count = 0;
    for entry in fs::read_dir(goldens_dir()).expect("goldens directory") {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|e| e == "prog") {
            let src = fs::read_to_string(&path).unwrap();
            parse_program(&src)
                .unwrap_or_else(|e| panic!("{} does not parse: {e}", path.display()));
            count += 1;
        }
    }
    assert!(
        count >= 1,
        "expected at least one client artifact, found {count}"
    );
}

/// `myProgram`: hint x = 15, hint y = 2·x, assert (y == 30) — witness generation succeeds.
#[test]
fn my_program_runs() {
    let prog = parse_program(&read_golden("myProgram.prog")).unwrap();
    let out = Interpreter::new(&prog)
        .run_main(&mut Circuit, vec![])
        .unwrap();
    assert_eq!(out, Value::Unit);
}
