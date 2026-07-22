// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ── re.^ (re.power): syntactic sugar for (_ re.loop n n) ──

/// (_ re.^ 3) (str.to_re "ab") matches "ababab".
#[test]
#[timeout(10_000)]
fn re_power_exact_repetition_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.in_re "ababab" ((_ re.^ 3) (str.to_re "ab"))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "re.^ 3 should match exactly 3 repetitions"
    );
}

/// (_ re.^ 3) (str.to_re "ab") does NOT match "abab" (only 2 reps).
#[test]
#[timeout(10_000)]
fn re_power_wrong_count_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.in_re "abab" ((_ re.^ 3) (str.to_re "ab"))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "re.^ 3 should not match 2 repetitions"
    );
}

/// (_ re.^ 0) matches only the empty string.
#[test]
#[timeout(10_000)]
fn re_power_zero_matches_empty_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.in_re "" ((_ re.^ 0) (str.to_re "ab"))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "re.^ 0 should match empty string"
    );
}

/// (_ re.^ 1) is identity — matches the regex itself.
#[test]
#[timeout(10_000)]
fn re_power_one_is_identity_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.in_re "ab" ((_ re.^ 1) (str.to_re "ab"))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "re.^ 1 should be identity"
    );
}

// ── str.< and str.<= (lexicographic string ordering) ──

/// "abc" str.< "abd" is SAT (lexicographic comparison).
#[test]
#[timeout(10_000)]
fn str_lt_ground_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.< "abc" "abd"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "\"abc\" < \"abd\" should be SAT"
    );
}

/// "abd" str.< "abc" is UNSAT.
#[test]
#[timeout(10_000)]
fn str_lt_ground_wrong_order_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.< "abd" "abc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "\"abd\" < \"abc\" should be UNSAT"
    );
}

/// "abc" str.< "abc" is UNSAT (strict less-than, not <=).
#[test]
#[timeout(10_000)]
fn str_lt_equal_strings_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.< "abc" "abc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "\"abc\" < \"abc\" should be UNSAT (strict)"
    );
}

/// "abc" str.<= "abc" is SAT.
#[test]
#[timeout(10_000)]
fn str_le_equal_strings_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.<= "abc" "abc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "\"abc\" <= \"abc\" should be SAT"
    );
}

/// "" str.< "a" is SAT (empty string is less than any non-empty string).
#[test]
#[timeout(10_000)]
fn str_lt_empty_vs_nonempty_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.< "" "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "empty string should be less than any non-empty string"
    );
}

/// "" str.<= "" is SAT.
#[test]
#[timeout(10_000)]
fn str_le_empty_empty_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.<= "" ""))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "\"\" <= \"\" should be SAT"
    );
}

// ── str.is_digit (single-character digit predicate) ──

/// str.is_digit("5") is SAT.
#[test]
#[timeout(10_000)]
fn str_is_digit_true_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.is_digit "5"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "str.is_digit(\"5\") should be SAT"
    );
}

/// (not (str.is_digit "5")) is UNSAT.
#[test]
#[timeout(10_000)]
fn str_is_digit_true_negated_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (not (str.is_digit "5")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "negated str.is_digit(\"5\") should be UNSAT"
    );
}

/// str.is_digit("a") is UNSAT (not a digit).
#[test]
#[timeout(10_000)]
fn str_is_digit_non_digit_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.is_digit "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "str.is_digit(\"a\") should be UNSAT"
    );
}

/// str.is_digit("") is UNSAT (empty string is not a digit).
#[test]
#[timeout(10_000)]
fn str_is_digit_empty_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.is_digit ""))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "str.is_digit(\"\") should be UNSAT"
    );
}

/// str.is_digit("12") is UNSAT (multi-char string is not a digit).
#[test]
#[timeout(10_000)]
fn str_is_digit_multichar_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.is_digit "12"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "str.is_digit(\"12\") should be UNSAT (multi-char)"
    );
}
