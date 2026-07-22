// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for the `ay::Error` / `ay::Result<T>` error facade (#3039).
//!
//! Verifies that:
//! 1. `ay::Error` wraps both `ParseError` and `SolverError` via `?`
//! 2. Display output is preserved for both error types
//! 3. The facade is accessible through `ay::api` and `ay::prelude`

#![allow(deprecated)]
#![allow(unused_qualifications)]

use ay::{Command, Error, Logic, ParseError, Result, SolveResult, Solver, Sort};

// ---- Packet B: root error facade ----

#[test]
fn test_root_error_wraps_parse_error() {
    // Invalid SMT-LIB triggers a ParseError; `?` converts it into ay::Error.
    fn inner() -> Result<Vec<Command>> {
        Ok(ay::parse("(invalid !! bad syntax")?)
    }

    let err = inner().unwrap_err();
    match &err {
        Error::Parse(_) => {}
        other => panic!("expected Error::Parse, got: {other}"),
    }
    // Display should contain the original ParseError text
    let msg = err.to_string();
    assert!(
        msg.contains("Parse error"),
        "error display should include 'Parse error', got: {msg}"
    );
}

#[test]
fn test_root_result_wraps_try_check_sat() {
    // Uses try_check_sat() through ay::Result to verify SolverError conversion.
    fn inner() -> Result<SolveResult> {
        let mut solver = Solver::new(Logic::QfLia);
        let x = solver.declare_const("x", Sort::Int);
        let zero = solver.int_const(0);
        let c = solver.gt(x, zero);
        solver.assert_term(c);
        Ok(solver.try_check_sat()?.result().clone())
    }

    let result = inner().expect("try_check_sat should succeed on a trivial SAT problem");
    assert_eq!(result, SolveResult::Sat);
}

#[test]
fn test_error_from_parse_error() {
    let pe = ParseError::new("bad input");
    let err: Error = pe.into();
    assert!(matches!(err, Error::Parse(_)));
    assert_eq!(err.to_string(), "Parse error: bad input");
}

#[test]
fn test_error_display_is_transparent() {
    // With #[error(transparent)], Error::Parse display delegates to ParseError
    let pe = ParseError::with_position("unexpected token", 42);
    let expected = pe.to_string();
    let err: Error = pe.into();
    assert_eq!(err.to_string(), expected);
    assert_eq!(
        err.to_string(),
        "Parse error at position 42: unexpected token"
    );
}

// ---- Packet C: api and prelude mirror the facade ----

#[test]
fn test_api_module_exports_error_facade() {
    fn _assert_types() {
        fn _inner() -> ay::api::Result<Vec<ay::api::Command>> {
            Ok(ay::api::parse("(declare-const x Int)")?)
        }
        let _: ay::api::Error = ay::api::ParseError::new("test").into();
    }
}

#[test]
fn test_prelude_exports_error_facade() {
    use ay::prelude::*;

    fn _inner() -> Result<Vec<Command>> {
        Ok(parse("(declare-const x Int)")?)
    }
    let _: Error = ParseError::new("test").into();
}

// ---- Packet D: display format regressions ----

#[test]
fn test_parse_error_display_preserved() {
    // Lock the two parse error message formats
    let e1 = ParseError::new("unexpected end of input");
    assert_eq!(e1.to_string(), "Parse error: unexpected end of input");

    let e2 = ParseError::with_position("unexpected ')'", 37);
    assert_eq!(e2.to_string(), "Parse error at position 37: unexpected ')'");
}

// SortError display regression is in crates/ay-bindings/src/error.rs tests (#3039)
