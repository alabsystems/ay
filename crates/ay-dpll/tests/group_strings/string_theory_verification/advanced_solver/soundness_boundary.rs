// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ── Prover: differential soundness boundary tests ───────────────────

/// Chain of transitive equalities through a constant should be SAT.
///
/// x=y, y=z, z="hello", x="hello" — all consistent.
#[test]
#[timeout(10_000)]
fn soundness_chain_eq_transitive_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= x y))
(assert (= y z))
(assert (= z "hello"))
(assert (= x "hello"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&result), Some("sat"));
}

/// Chain of transitive equalities to contradictory constants is UNSAT.
///
/// x=y, y=z, z="hello", x="world" — z and x are in the same EQC
/// but "hello" != "world".
#[test]
#[timeout(10_000)]
fn soundness_chain_eq_contradiction_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= x y))
(assert (= y z))
(assert (= z "hello"))
(assert (= x "world"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&result), Some("unsat"));
}

/// Triple concat with all parts resolved should be SAT.
#[test]
#[timeout(10_000)]
fn soundness_triple_concat_resolved_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= (str.++ x y z) "abc"))
(assert (= x "a"))
(assert (= y "b"))
(assert (= z "c"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&result), Some("sat"));
}

/// Triple concat with wrong third part should be UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_triple_concat_mismatch_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= (str.++ x y z) "abc"))
(assert (= x "a"))
(assert (= y "b"))
(assert (= z "d"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&result), Some("unsat"));
}

/// str.at constant evaluation matches Z3.
#[test]
#[timeout(10_000)]
fn soundness_str_at_first_char() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.at "hello" 0) "h"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&result), Some("sat"));
}

/// str.at with wrong character is UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_str_at_wrong_char_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.at "hello" 0) "e"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&result), Some("unsat"));
}

/// str.replace with constant evaluation matches Z3.
#[test]
#[timeout(10_000)]
fn soundness_str_replace_constant_match() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.replace "hello" "ell" "ELL")))
(assert (= x "hELLo"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&result), Some("sat"));
}

/// str.replace where pattern not found — identity.
#[test]
#[timeout(10_000)]
fn soundness_str_replace_no_match_identity() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.replace "hello" "xyz" "abc")))
(assert (= x "hello"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&result), Some("sat"));
}

/// Negated contains with non-substring is SAT.
/// "hello" does not contain "xyz", so not(contains("hello","xyz")) is sat.
#[test]
#[timeout(10_000)]
fn soundness_negated_contains_non_substring_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (str.contains "hello" x)))
(assert (= x "xyz"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&result), Some("sat"));
}

/// Negated contains with actual substring is UNSAT.
/// "hello" contains "ell", so not(contains("hello","ell")) is unsat.
#[test]
#[timeout(10_000)]
fn soundness_negated_contains_actual_substring_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (str.contains "hello" x)))
(assert (= x "ell"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "negated contains actual substring: got {ay:?}"
    );
}

// ==========================================================================
// QF_S + str.len soundness regression tests
//
// BUG: QF_S solver ignores str.len constraints because solve_strings()
// has no LIA integration. str.len assertions are silently dropped,
// leading to SAT results on UNSAT formulas.
//
// SLIA variants confirm the solver handles these correctly when
// length reasoning is available via the combined Strings+LIA solver.
// ==========================================================================

/// QF_S with len(x)=3 and x="ab" is UNSAT (len mismatch).
///
/// The QF_S→QF_SLIA auto-upgrade detects the Int-sorted str.len term
/// and routes through the combined Strings+LIA solver.
#[test]
#[timeout(10_000)]
fn soundness_qf_s_strlen_constant_contradiction() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.len x) 3))
(assert (= x "ab"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "len(x)=3 ∧ x=\"ab\" is UNSAT"
    );
    // Verify SLIA path handles it correctly.
    let slia_smt = smt.replace("QF_S", "QF_SLIA");
    let slia_result = crate::common::solve(&slia_smt);
    assert_eq!(
        crate::common::sat_result(&slia_result),
        Some("unsat"),
        "SLIA path must detect len(x)=3 ∧ x=\"ab\" contradiction"
    );
}

/// QF_S with len(x)=0 and x!="" is UNSAT.
///
/// The QF_S→QF_SLIA auto-upgrade detects Int-sorted str.len term.
#[test]
#[timeout(10_000)]
fn soundness_qf_s_strlen_zero_neq_empty() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.len x) 0))
(assert (not (= x "")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "len(x)=0 ∧ x≠\"\" is UNSAT"
    );
    // Verify SLIA path handles it correctly.
    let slia_smt = smt.replace("QF_S", "QF_SLIA");
    let slia_result = crate::common::solve(&slia_smt);
    assert_eq!(
        crate::common::sat_result(&slia_result),
        Some("unsat"),
        "SLIA path must detect len(x)=0 ∧ x≠\"\" contradiction"
    );
}

/// Auto-detection correctly upgrades to SLIA when str.len is present.
///
/// Without explicit set-logic, the features system detects has_strings
/// && has_int and routes to QF_SLIA, getting the correct answer.
#[test]
#[timeout(10_000)]
fn soundness_auto_detect_upgrades_strlen_to_slia() {
    // No set-logic — auto-detection should route to SLIA.
    let smt = r#"
(declare-fun x () String)
(assert (= (str.len x) 3))
(assert (= x "ab"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "auto-detected logic should handle str.len (route to SLIA)"
    );
}

/// #3375 regression: duplicate LengthSplit detection prevents infinite loop.
///
/// `(str.++ x "c") = (str.++ y "c")` with variable-variable alignment.
///
/// Previously caused 10,000 iterations of LengthSplit lemmas with no progress.
/// Fixed: apply_string_lemma now handles NOT(atom) correctly (#3375).
/// Z3 returns sat. AY returns unknown (completeness gap, sound).
#[test]
#[timeout(10_000)]
fn regression_3375_length_split_no_hang() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "c") (str.++ y "c")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "#3375: expected sat or unknown, got {ay:?}"
    );
}

/// #3375 regression in SLIA mode: same formula under QF_SLIA.
///
/// Fixed: apply_string_lemma negation handling (#3375).
/// AY returns unknown (completeness gap, sound).
#[test]
#[timeout(10_000)]
fn regression_3375_length_split_no_hang_slia() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "c") (str.++ y "c")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "#3375 SLIA: expected sat or unknown, got {ay:?}"
    );
}

/// #3375 regression: variable-variable prefix pattern.
///
/// After "a"="a" prefix match, x vs y triggers LengthSplit.
/// Fixed: apply_string_lemma negation handling (#3375).
/// AY returns unknown (completeness gap, sound).
#[test]
#[timeout(10_000)]
fn regression_3375_prefix_pattern_no_hang() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ "a" x) (str.++ "a" y)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "#3375 prefix: expected sat or unknown, got {ay:?}"
    );
}

/// Two-step cycle: x = "a" ++ y, y = "b" ++ x is UNSAT.
///
/// Substituting gives x = "a" ++ "b" ++ x = "ab" ++ x, requiring x to be
/// infinite. Multi-hop cycle detection (recursive DFS) catches this.
#[test]
#[timeout(10_000)]
fn soundness_two_step_cycle_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ "a" y)))
(assert (= y (str.++ "b" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "two-step cycle is UNSAT"
    );
}

/// Two-step cycle in SLIA mode is also detected.
#[test]
#[timeout(10_000)]
fn soundness_two_step_cycle_slia_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ "a" y)))
(assert (= y (str.++ "b" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "two-step cycle is UNSAT"
    );
}

/// Single-step cycle is correctly detected.
#[test]
#[timeout(10_000)]
fn soundness_single_step_cycle_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.++ "a" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "direct cycle x = \"a\" ++ x is UNSAT"
    );
}

/// Empty concat cycle is SAT (not a real cycle).
#[test]
#[timeout(10_000)]
fn soundness_empty_concat_cycle_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.++ "" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    // x = str.++ "" x simplifies to x = x, which is trivially SAT.
    assert!(
        matches!(answer, Some("sat") | Some("unknown")),
        "x = \"\" ++ x must not be unsat; got {answer:?}"
    );
}

/// Nelson-Oppen: strings Unknown should not block LIA contradictions.
///
/// Verifies the combined_solvers.rs change: when strings returns Unknown
/// (unresolved variables), the N-O loop still runs LIA to detect
/// length contradictions.
#[test]
#[timeout(10_000)]
fn soundness_nelson_oppen_strings_unknown_lia_detects_contradiction() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.len x) 5))
(assert (= (str.len y) 3))
(assert (= x y))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "x=y with len(x)=5, len(y)=3 is UNSAT via N-O length propagation"
    );
}
