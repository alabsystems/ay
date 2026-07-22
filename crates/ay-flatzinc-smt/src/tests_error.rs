// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Tests for TranslateError variants and Display formatting.
// Extracted from tests.rs to keep files under 500 lines.

use super::*;

fn translate_fzn_err(input: &str) -> TranslateError {
    let model = ay_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).unwrap_err()
}

// --- WrongArgCount ---

#[test]
fn test_error_wrong_arg_count() {
    // int_eq expects 2 args, give it 1 → WrongArgCount
    let err = translate_fzn_err("var int: x;\nconstraint int_eq(x);\nsolve satisfy;\n");
    assert!(
        matches!(err, TranslateError::WrongArgCount { ref name, expected, got }
            if name == "=" && expected == 2 && got == 1),
        "expected WrongArgCount(=, 2, 1), got: {err}"
    );
}

#[test]
fn test_error_wrong_arg_count_display() {
    let err = TranslateError::WrongArgCount {
        name: "int_plus".into(),
        expected: 3,
        got: 2,
    };
    let msg = format!("{err}");
    assert!(
        msg.contains("int_plus"),
        "should mention constraint name: {msg}"
    );
    assert!(msg.contains("3"), "should mention expected count: {msg}");
    assert!(msg.contains("2"), "should mention actual count: {msg}");
}

// --- UnknownIdentifier ---

#[test]
fn test_error_unknown_identifier() {
    let err = translate_fzn_err("var int: x;\nconstraint int_eq(x, ghost);\nsolve satisfy;\n");
    assert!(
        matches!(err, TranslateError::UnknownIdentifier(ref name) if name == "ghost"),
        "expected UnknownIdentifier(ghost), got: {err}"
    );
}

#[test]
fn test_error_unknown_identifier_display() {
    let err = TranslateError::UnknownIdentifier("phantom_var".into());
    assert_eq!(format!("{err}"), "unknown identifier: phantom_var");
}

// --- UnsupportedConstraint ---

#[test]
fn test_error_unsupported_constraint_display() {
    let err = TranslateError::UnsupportedConstraint("fzn_magic".into());
    assert_eq!(format!("{err}"), "unsupported constraint: fzn_magic");
}

// --- ExpectedIntLiteral ---

#[test]
fn test_error_expected_int_literal_display() {
    let err = TranslateError::ExpectedIntLiteral("not_a_number".into());
    assert_eq!(
        format!("{err}"),
        "expected integer literal, got: not_a_number"
    );
}

// --- ExpectedArray ---

#[test]
fn test_error_expected_array_display() {
    let err = TranslateError::ExpectedArray;
    assert_eq!(format!("{err}"), "expected array expression, got scalar");
}

// --- ArrayIndexOutOfBounds ---

#[test]
fn test_error_array_index_out_of_bounds_display() {
    let err = TranslateError::ArrayIndexOutOfBounds {
        name: "arr".into(),
        index: 99,
    };
    assert_eq!(format!("{err}"), "array index out of bounds: arr[99]");
}

// --- UnsupportedType ---

#[test]
fn test_error_unsupported_type_display() {
    let err = TranslateError::UnsupportedType("Float".into());
    assert_eq!(
        format!("{err}"),
        "unsupported type for SMT translation: Float"
    );
}
