// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for parse_sexp() full-input contract.

use ay_frontend::sexp::{parse_sexp, SExpr};

#[test]
fn parse_sexp_allows_trailing_comments_and_whitespace() {
    let parsed =
        parse_sexp("(a)  ; trailing comment\n   ").expect("single S-expression should parse");
    assert_eq!(parsed, SExpr::List(vec![SExpr::Symbol("a".to_string())]));
}

#[test]
fn parse_sexp_reports_trailing_expression_position() {
    let err = parse_sexp("(a) (b)").expect_err("trailing expression must be rejected");
    assert!(
        err.message.contains("trailing input"),
        "Expected trailing-input error, got: {err}"
    );
    assert_eq!(err.position, Some(4));
}
