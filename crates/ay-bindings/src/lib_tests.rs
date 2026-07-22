// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_format_symbol_simple() {
    assert_eq!(format_symbol("x"), "x");
    assert_eq!(format_symbol("foo_bar"), "foo_bar");
    assert_eq!(format_symbol("x123"), "x123");
}

#[test]
fn test_format_symbol_needs_quoting() {
    assert_eq!(format_symbol("foo::bar"), "|foo::bar|");
    assert_eq!(
        format_symbol("test_function::local_1_0"),
        "|test_function::local_1_0|"
    );
    assert_eq!(format_symbol("a:b"), "|a:b|");
}

#[test]
fn test_format_symbol_reserved_words() {
    // Reserved words get quoted to avoid parser confusion
    assert_eq!(format_symbol("true"), "|true|");
    assert_eq!(format_symbol("false"), "|false|");
    assert_eq!(format_symbol("let"), "|let|");
    assert_eq!(format_symbol("forall"), "|forall|");
    assert_eq!(format_symbol("exists"), "|exists|");
    assert_eq!(format_symbol("assert"), "|assert|");
    assert_eq!(format_symbol("check-sat"), "|check-sat|");
}

#[test]
fn test_format_symbol_sanitizes_pipe() {
    assert_eq!(format_symbol("foo|bar"), "|foo_bar|");
    assert_eq!(format_symbol("foo\\bar"), "|foo_bar|");
}

/// Test the exact failing case from issue #91:
/// `(declare-const test_constant_extraction::local_3_0 Bool)` was rejected.
#[test]
fn test_issue_91_exact_case() {
    use crate::constraint::Constraint;
    use crate::sort::Sort;

    // The exact identifier that was failing
    let c = Constraint::declare_const("test_constant_extraction::local_3_0", Sort::bool());
    let smt = c.to_string();

    // Must now be quoted
    assert_eq!(
        smt,
        "(declare-const |test_constant_extraction::local_3_0| Bool)"
    );

    // Verify it doesn't contain unquoted :: which would fail SMT parsing
    assert!(!smt.contains(" test_constant_extraction::"));
}

#[test]
fn test_panic_payload_to_string_reexport() {
    // Verify the re-export works and handles both &str and String payloads
    let str_payload: Box<dyn std::any::Any + Send> = Box::new("sort mismatch");
    assert_eq!(panic_payload_to_string(&*str_payload), "sort mismatch");

    let string_payload: Box<dyn std::any::Any + Send> =
        Box::new(String::from("invalid bitvector width"));
    assert_eq!(
        panic_payload_to_string(&*string_payload),
        "invalid bitvector width"
    );

    let other_payload: Box<dyn std::any::Any + Send> = Box::new(42i32);
    assert_eq!(panic_payload_to_string(&*other_payload), "unknown panic");
}
