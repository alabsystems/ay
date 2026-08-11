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

/// `|` and `\` are rendered LOSSLESSLY, not substituted away.
///
/// This used to pin `format_symbol("foo|bar") == "|foo_bar|"` AND
/// `format_symbol("foo\\bar") == "|foo_bar|"` — i.e. it asserted that two
/// DISTINCT user symbols collapse onto the same output, which is the bug
/// rather than the contract: a solver that renders `foo|bar` and `foo\bar`
/// identically prints two different declarations as one.
///
/// `ay_core::quote_symbol` switched to the backslash escapes Z3 5.0.0 accepts,
/// which AY's own reader round-trips. Following the same correction made in
/// ay-chc (`aa1cb1608`), this pins the PROPERTY — pipe-quoted and injective —
/// rather than a spelling that can drift again.
#[test]
fn test_format_symbol_renders_pipe_and_backslash_losslessly() {
    for name in ["foo|bar", "foo\\bar"] {
        let rendered = format_symbol(name);
        assert_eq!(
            rendered,
            ay_core::quote_symbol(name),
            "format_symbol must delegate to ay_core for {name:?}"
        );
        assert!(
            rendered.starts_with('|') && rendered.ends_with('|'),
            "{name:?} must stay pipe-quoted, got {rendered}"
        );
    }

    // Injective: none of these three distinct names may share a rendering, and
    // in particular none may collapse onto the substituted spelling.
    let piped = format_symbol("foo|bar");
    let escaped = format_symbol("foo\\bar");
    let underscored = format_symbol("foo_bar");
    assert_ne!(
        piped, escaped,
        "`foo|bar` and `foo\\bar` must stay distinct"
    );
    assert_ne!(
        piped, underscored,
        "`foo|bar` must not collapse onto `foo_bar`"
    );
    assert_ne!(
        escaped, underscored,
        "`foo\\bar` must not collapse onto `foo_bar`"
    );
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
