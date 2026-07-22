// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression coverage for regex elaboration arity/sort checks.

use ay_frontend::{parse, Context, ElaborateError};

fn elaborate_script(input: &str) -> Result<(), ElaborateError> {
    let commands = parse(input).expect("test SMT-LIB should parse");
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command)?;
    }
    Ok(())
}

#[test]
fn regex_membership_smoke_elaborates() {
    let smt = r#"
        (declare-const x String)
        (assert (str.in_re x (re.* (str.to_re "a"))))
    "#;
    let result = elaborate_script(smt);
    assert!(
        result.is_ok(),
        "regex smoke formula should elaborate, got: {result:?}"
    );
}

#[test]
fn regex_concat_rejects_string_argument() {
    let smt = r#"
        (declare-const x String)
        (assert (str.in_re x (re.++ (str.to_re "a") x)))
    "#;
    let err = elaborate_script(smt).expect_err("re.++ argument sort mismatch must fail");
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "expected sort mismatch, got: {err:?}"
    );
}

#[test]
fn regex_range_rejects_wrong_arity() {
    let smt = r#"
        (declare-const x String)
        (assert (str.in_re x (re.range "a")))
    "#;
    let err = elaborate_script(smt).expect_err("re.range arity mismatch must fail");
    assert!(
        matches!(err, ElaborateError::InvalidConstant(_)),
        "expected arity error, got: {err:?}"
    );
}
