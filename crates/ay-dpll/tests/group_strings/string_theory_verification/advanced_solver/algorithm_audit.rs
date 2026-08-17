// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// Prover algorithm audit: QF_S→QF_SLIA upgrade coverage
//
// The QF_S→QF_SLIA upgrade must trigger on ALL Int-sorted string operations,
// not just str.len. These tests verify str.to_int and str.from_int also
// trigger the upgrade when the user specifies QF_S.
// =============================================================================

/// QF_S with str.to_int: auto-upgrade must detect the Int-sorted term.
///
/// x = "42" ∧ to_int(x) = 43 is UNSAT. If QF_S doesn't upgrade to SLIA,
/// the integer constraint is silently dropped and AY returns sat (wrong).
#[test]
#[timeout(10_000)]
fn audit_qf_s_to_int_triggers_slia_upgrade() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "42"))
(assert (= (str.to_int x) 43))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("sat"),
        "QF_S with str.to_int must not silently drop the integer constraint"
    );
}

/// QF_S with str.from_int: auto-upgrade must detect the Int-sorted term.
#[test]
#[timeout(10_000)]
fn audit_qf_s_from_int_triggers_slia_upgrade() {
    let smt = r#"
(set-logic QF_S)
(assert (= (str.from_int 42) "43"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("sat"),
        "QF_S with str.from_int must not silently drop the integer constraint"
    );
}

/// QF_S with str.indexof: the third argument is Int, triggering upgrade.
#[test]
#[timeout(10_000)]
fn audit_qf_s_indexof_triggers_slia_upgrade() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "hello world"))
(assert (= (str.indexof x "world" 0) 99))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("sat"),
        "QF_S with str.indexof must not silently drop the integer constraint"
    );
}

// =============================================================================
// Prover algorithm audit: cycle detection + Z3 differential
// =============================================================================

/// Three-step cycle: x = "a"++y, y = "b"++z, z = "c"++x is UNSAT.
#[test]
#[timeout(10_000)]
fn audit_three_step_cycle_detected() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= x (str.++ "a" y)))
(assert (= y (str.++ "b" z)))
(assert (= z (str.++ "c" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "three-step cycle with non-empty constants is UNSAT"
    );
    if z3_available() {
        let z3_output = solve_with_z3(smt).unwrap_or_else(|e| panic!("z3 failed: {e}"));
        let z3_result = crate::common::sat_result(&z3_output)
            .unwrap_or_else(|| panic!("z3 produced no result"));
        assert_eq!(
            z3_result, "unsat",
            "z3 must agree: three-step cycle is UNSAT"
        );
    }
}

/// Differential: str.replace constant evaluation matches Z3.
#[test]
#[timeout(10_000)]
fn audit_replace_constant_eval_matches_z3() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.replace "hello world" "world" "ay")))
(assert (= x "hello ay"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "replace(\"hello world\",\"world\",\"ay\") = \"hello ay\""
    );
    if z3_available() {
        let z3_output = solve_with_z3(smt).unwrap_or_else(|e| panic!("z3 failed: {e}"));
        let z3_result = crate::common::sat_result(&z3_output)
            .unwrap_or_else(|| panic!("z3 produced no result"));
        assert_eq!(z3_result, "sat", "z3 must agree");
    }
}

/// Differential: str.replace_all constant evaluation matches Z3.
#[test]
#[timeout(10_000)]
fn audit_replace_all_constant_eval_matches_z3() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.replace_all "aabaa" "a" "x")))
(assert (= x "xxbxx"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "replace_all(\"aabaa\",\"a\",\"x\") = \"xxbxx\""
    );
    if z3_available() {
        let z3_output = solve_with_z3(smt).unwrap_or_else(|e| panic!("z3 failed: {e}"));
        let z3_result = crate::common::sat_result(&z3_output)
            .unwrap_or_else(|| panic!("z3 produced no result"));
        assert_eq!(z3_result, "sat", "z3 must agree");
    }
}

/// Differential: regex membership (positive) matches Z3.
#[test]
#[timeout(10_000)]
fn audit_regex_membership_positive_matches_z3() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "abc"))
(assert (str.in_re x (re.++ (str.to_re "a") (re.* (re.range "a" "z")))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(ay, Some("sat"), "\"abc\" in a·[a-z]* is SAT");
    if z3_available() {
        let z3_output = solve_with_z3(smt).unwrap_or_else(|e| panic!("z3 failed: {e}"));
        let z3_result = crate::common::sat_result(&z3_output)
            .unwrap_or_else(|| panic!("z3 produced no result"));
        assert_eq!(z3_result, "sat", "z3 must agree");
    }
}

/// Differential: regex membership (negative) matches Z3.
#[test]
#[timeout(10_000)]
fn audit_regex_membership_negative_matches_z3() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "123"))
(assert (str.in_re x (re.+ (re.range "a" "z"))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(ay, Some("unsat"), "\"123\" in [a-z]+ is UNSAT");
    if z3_available() {
        let z3_output = solve_with_z3(smt).unwrap_or_else(|e| panic!("z3 failed: {e}"));
        let z3_result = crate::common::sat_result(&z3_output)
            .unwrap_or_else(|| panic!("z3 produced no result"));
        assert_eq!(z3_result, "unsat", "z3 must agree");
    }
}
