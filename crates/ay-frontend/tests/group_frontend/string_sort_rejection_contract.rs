// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Contract tests for frontend sort checking on string/regex applications.

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
fn well_typed_string_and_regex_smoke_elaborates() {
    let smt = r#"
        (set-logic QF_SLIA)
        (assert (= (str.replace_all "ababa" "a" "x") "xbxbx"))
        (assert (str.in_re "ab" (re.++ (str.to_re "a") (str.to_re "b"))))
    "#;
    let result = elaborate_script(smt);
    assert!(
        result.is_ok(),
        "well-typed string/regex script should elaborate, got: {result:?}"
    );
}

#[test]
fn ill_typed_string_and_regex_apps_are_rejected() {
    let cases = [
        (
            "str.replace_all haystack must be String",
            r#"
                (set-logic QF_SLIA)
                (assert (= (str.replace_all 0 "a" "b") "b"))
            "#,
        ),
        (
            "str.in_re first arg must be String",
            r#"
                (set-logic QF_S)
                (assert (str.in_re 0 (str.to_re "a")))
            "#,
        ),
        (
            "str.in_re second arg must be RegLan",
            r#"
                (set-logic QF_S)
                (assert (str.in_re "a" "b"))
            "#,
        ),
        (
            "str.to_re argument must be String",
            r#"
                (set-logic QF_S)
                (assert (str.in_re "a" (str.to_re 1)))
            "#,
        ),
        (
            "re.union arguments must be RegLan",
            r#"
                (set-logic QF_S)
                (assert (str.in_re "a" (re.union (str.to_re "a") "b")))
            "#,
        ),
        (
            "str.len arity must be 1",
            r#"
                (set-logic QF_SLIA)
                (assert (= (str.len "ab" "cd") 2))
            "#,
        ),
        (
            "str.replace_all arity must be 3",
            r#"
                (set-logic QF_SLIA)
                (assert (= (str.replace_all "ab" "a") "x"))
            "#,
        ),
    ];

    for (name, smt) in cases {
        let err = elaborate_script(smt).expect_err(name);
        assert!(
            matches!(
                err,
                ElaborateError::SortMismatch { .. } | ElaborateError::InvalidConstant(_)
            ),
            "expected sort/arity rejection for `{name}`, got: {err:?}"
        );
    }
}
