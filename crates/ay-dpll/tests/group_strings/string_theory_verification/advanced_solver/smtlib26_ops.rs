// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ===================================================================
// str.to_code and str.from_code (SMT-LIB 2.6 code point operations)
// ===================================================================

/// str.to_code("a") = 97 (ASCII 'a').
#[test]
#[timeout(10_000)]
fn str_to_code_single_char_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_code "a") 97))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.to_code(\"a\") = 97 should be SAT"
    );
}

/// str.to_code("a") = 98 is UNSAT (97 != 98).
#[test]
#[timeout(10_000)]
fn str_to_code_wrong_value_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_code "a") 98))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "str.to_code(\"a\") = 98 should be UNSAT"
    );
}

/// str.to_code("") = -1 (empty string returns -1).
#[test]
#[timeout(10_000)]
fn str_to_code_empty_returns_minus_one() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_code "") (- 1)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.to_code(\"\") = -1 should be SAT"
    );
}

/// str.to_code("ab") = -1 (multi-char string returns -1).
#[test]
#[timeout(10_000)]
fn str_to_code_multichar_returns_minus_one() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_code "ab") (- 1)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.to_code(\"ab\") = -1 should be SAT"
    );
}

/// str.from_code(97) = "a".
#[test]
#[timeout(10_000)]
fn str_from_code_valid_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.from_code 97) "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.from_code(97) = \"a\" should be SAT"
    );
}

/// str.from_code(-1) = "" (negative code point returns empty string).
#[test]
#[timeout(10_000)]
fn str_from_code_negative_returns_empty() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.from_code (- 1)) ""))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.from_code(-1) = \"\" should be SAT"
    );
}

/// str.from_code(str.to_code("z")) = "z" (round-trip).
#[test]
#[timeout(10_000)]
fn str_to_code_from_code_roundtrip() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.from_code (str.to_code "z")) "z"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.from_code(str.to_code(\"z\")) = \"z\" (roundtrip) should be SAT"
    );
}

/// NOT(str.from_code(str.to_code("z")) = "z") is UNSAT.
#[test]
#[timeout(10_000)]
fn str_to_code_from_code_roundtrip_negated_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (not (= (str.from_code (str.to_code "z")) "z")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "NOT(roundtrip) should be UNSAT"
    );
}

/// str.to_code of character outside SMT-LIB universe (U+30000 = 196608) must
/// return -1, not the raw code point. SMT-LIB character universe is [0, 196607].
/// Regression: eval_str_to_code returned 196608 instead of -1 for out-of-range chars.
#[test]
#[timeout(10_000)]
fn str_to_code_outside_smtlib_universe_returns_minus_one() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_code "\u{30000}") (- 1)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.to_code of char outside SMT-LIB universe (U+30000) should return -1"
    );
}

/// str.to_code at the SMT-LIB boundary (U+2FFFF = 196607) should return 196607.
#[test]
#[timeout(10_000)]
fn str_to_code_at_smtlib_boundary_returns_196607() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_code "\u{2FFFF}") 196607))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.to_code at SMT-LIB boundary (U+2FFFF) should return 196607"
    );
}

/// str.to_code of out-of-range char should NOT equal 196608 (the raw code point).
#[test]
#[timeout(10_000)]
fn str_to_code_outside_smtlib_universe_not_raw_codepoint() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_code "\u{30000}") 196608))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "str.to_code of out-of-range char should NOT return raw code point 196608"
    );
}

/// str.to_code rejects Int argument (expects String).
#[test]
#[timeout(10_000)]
fn str_to_code_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (= (str.to_code n) 0))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.to_code with Int arg should be rejected, got: {result:?}"
    );
}

/// str.from_code rejects String argument (expects Int).
#[test]
#[timeout(10_000)]
fn str_from_code_rejects_string_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.from_code x) "a"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.from_code with String arg should be rejected, got: {result:?}"
    );
}

/// str.replace_re rejects String as regex argument (expects RegLan).
#[test]
#[timeout(10_000)]
fn str_replace_re_rejects_string_regex_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.replace_re x "a" "b") "b"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.replace_re with String as regex arg should be rejected, got: {result:?}"
    );
}

/// str.replace_re_all rejects String as regex argument (expects RegLan).
#[test]
#[timeout(10_000)]
fn str_replace_re_all_rejects_string_regex_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.replace_re_all x "a" "b") "b"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.replace_re_all with String as regex arg should be rejected, got: {result:?}"
    );
}

/// str.replace_re rejects Int as first argument (expects String).
#[test]
#[timeout(10_000)]
fn str_replace_re_rejects_int_first_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (= (str.replace_re n (str.to_re "a") "b") "b"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.replace_re with Int first arg should be rejected, got: {result:?}"
    );
}

// ── str.replace_re and str.replace_re_all (SMT-LIB 2.6 regex replace) ──

/// str.replace_re("hello", (str.to_re "l"), "r") = "herlo".
/// First occurrence of "l" replaced.
#[test]
#[timeout(10_000)]
fn str_replace_re_first_match_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.replace_re "hello" (str.to_re "l") "r") "herlo"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.replace_re first match should be SAT"
    );
}

/// str.replace_re("hello", (str.to_re "l"), "r") != "herlo" is UNSAT.
#[test]
#[timeout(10_000)]
fn str_replace_re_first_match_negated_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (not (= (str.replace_re "hello" (str.to_re "l") "r") "herlo")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "negated str.replace_re should be UNSAT"
    );
}

/// str.replace_re("hello", (str.to_re "x"), "r") = "hello" (no match).
#[test]
#[timeout(10_000)]
fn str_replace_re_no_match_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.replace_re "hello" (str.to_re "x") "r") "hello"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.replace_re no match should return original string"
    );
}

/// str.replace_re_all("hello", (str.to_re "l"), "r") = "herro".
#[test]
#[timeout(10_000)]
fn str_replace_re_all_basic_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.replace_re_all "hello" (str.to_re "l") "r") "herro"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.replace_re_all should replace all matches"
    );
}

/// str.replace_re_all("hello", (str.to_re "l"), "r") != "herro" is UNSAT.
#[test]
#[timeout(10_000)]
fn str_replace_re_all_negated_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (not (= (str.replace_re_all "hello" (str.to_re "l") "r") "herro")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "negated str.replace_re_all should be UNSAT"
    );
}

/// str.replace_re with regex union: replace first digit.
#[test]
#[timeout(10_000)]
fn str_replace_re_regex_union_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.replace_re "a1b2c" (re.union (str.to_re "1") (str.to_re "2")) "X") "aXb2c"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.replace_re with union regex should replace first match"
    );
}

/// str.replace_re_all with regex union: replace all digits.
#[test]
#[timeout(10_000)]
fn str_replace_re_all_regex_union_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.replace_re_all "a1b2c" (re.union (str.to_re "1") (str.to_re "2")) "X") "aXbXc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.replace_re_all with union should replace all matches"
    );
}

// ── str.to_lower and str.to_upper (SMT-LIB 2.6 case conversion) ──

/// str.to_lower("Hello") = "hello".
#[test]
#[timeout(10_000)]
fn str_to_lower_basic_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_lower "Hello") "hello"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.to_lower basic should be SAT"
    );
}

/// str.to_lower("Hello") != "hello" is UNSAT.
#[test]
#[timeout(10_000)]
fn str_to_lower_negated_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (not (= (str.to_lower "Hello") "hello")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "negated str.to_lower should be UNSAT"
    );
}

/// str.to_lower on already-lowercase string is identity.
#[test]
#[timeout(10_000)]
fn str_to_lower_already_lowercase_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_lower "abc123") "abc123"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.to_lower on lowercase should be identity"
    );
}

/// str.to_lower("") = "".
#[test]
#[timeout(10_000)]
fn str_to_lower_empty_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_lower "") ""))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.to_lower on empty string should be SAT"
    );
}

/// str.to_upper("Hello") = "HELLO".
#[test]
#[timeout(10_000)]
fn str_to_upper_basic_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_upper "Hello") "HELLO"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.to_upper basic should be SAT"
    );
}

/// str.to_upper("Hello") != "HELLO" is UNSAT.
#[test]
#[timeout(10_000)]
fn str_to_upper_negated_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (not (= (str.to_upper "Hello") "HELLO")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "negated str.to_upper should be UNSAT"
    );
}

/// str.to_upper on already-uppercase string is identity.
#[test]
#[timeout(10_000)]
fn str_to_upper_already_uppercase_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_upper "ABC123") "ABC123"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.to_upper on uppercase should be identity"
    );
}

/// str.to_lower and str.to_upper are inverses on ASCII letters.
#[test]
#[timeout(10_000)]
fn str_to_lower_upper_roundtrip_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_upper (str.to_lower "HeLLo")) "HELLO"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "to_upper(to_lower(x)) should produce all uppercase"
    );
}

/// str.to_lower rejects Int argument.
#[test]
#[timeout(10_000)]
fn str_to_lower_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (= (str.to_lower n) "a"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.to_lower with Int arg should be rejected, got: {result:?}"
    );
}

/// str.to_upper rejects Int argument.
#[test]
#[timeout(10_000)]
fn str_to_upper_rejects_int_argument() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun n () Int)
(assert (= (str.to_upper n) "A"))
(check-sat)
"#;
    let result = solve_or_error(smt);
    assert!(
        result.is_err(),
        "str.to_upper with Int arg should be rejected, got: {result:?}"
    );
}
