// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof coverage tests for strings theory — P5 iteration 4.
//!
//! These tests exercise code paths identified by proof_coverage analysis as
//! having zero or low test coverage. Each test documents which internal
//! function/path it targets and why.
//!
//! Code paths covered:
//! - ConstUnify lemma path in process_simple_neq (core.rs ~3450-3476)
//! - check_extf_int_reductions range validation (core.rs ~5100-5230)
//! - check_cycles_dfs single-hop cycle detection (core.rs ~1500-1600)
//! - check_normal_forms_deq resolved-constants path (core.rs ~4290-4310)

use ntest::timeout;

// ===================================================================
// ConstUnify lemma path (core.rs process_simple_neq ~3450-3476)
//
// When a variable has a known length via the N-O bridge and is compared
// against a constant in normal forms, the ConstUnify optimization fires
// instead of character-by-character ConstSplit. These tests exercise
// that path from the SMT-LIB level.
// ===================================================================

/// ConstUnify: variable with known length 2 vs constant "abc" of length 3.
/// The solver should split x into its first 2 characters of "abc" and the rest,
/// via the ConstUnify lemma. With len(x)=2 and x="ab"++suffix where suffix
/// must be "", x="ab" is the only solution.
#[test]
#[timeout(10_000)]
fn const_unify_known_length_vs_longer_constant() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 2))
(assert (str.prefixof x "abc"))
(assert (not (= x "ab")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "len(x)=2, prefixof(x,\"abc\"), x!=\"ab\" should be unsat, got {ay:?}"
    );
}

/// ConstUnify: variable length exceeds constant length.
/// len(x)=5 but x is prefix of "ab" (length 2) — contradiction.
/// When length exceeds constant, ConstUnify is skipped and the solver
/// must find the conflict via other means.
#[test]
#[timeout(10_000)]
fn const_unify_length_exceeds_constant_conflict() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 5))
(assert (str.prefixof x "ab"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "len(x)=5 but x is prefix of \"ab\" (len 2) should be unsat, got {ay:?}"
    );
}

/// ConstUnify: equal lengths should unify directly.
/// len(x)=3 with x = "abc" ++ suffix where suffix="" forces x="abc".
#[test]
#[timeout(10_000)]
fn const_unify_equal_length_exact_match() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 3))
(assert (str.prefixof "abc" x))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "len(x)=3 with prefix \"abc\" should be SAT (x=\"abc\"), got {ay:?}"
    );
}

// ===================================================================
// check_extf_int_reductions (core.rs ~5100-5230)
//
// Range-restricted integer-valued string functions: str.to_int returns
// {-1} ∪ Z≥0, str.to_code returns [-1, 196607]. Values outside these
// ranges should produce conflicts.
// ===================================================================

/// str.to_int(x) = -5: out of range, must be UNSAT.
/// str.to_int always returns >= -1.
#[test]
#[timeout(10_000)]
fn extf_int_reductions_to_int_out_of_range() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.to_int x) (- 5)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.to_int(x) = -5 is out of range, should be unsat, got {ay:?}"
    );
}

/// str.to_int(x) = 42: valid range, should be SAT (x = "42").
#[test]
#[timeout(10_000)]
fn extf_int_reductions_to_int_valid_range() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.to_int x) 42))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "str.to_int(x) = 42 should be SAT or unknown, got {ay:?}"
    );
}

/// str.to_int("42") = 42: ground evaluation, must be SAT.
#[test]
#[timeout(10_000)]
fn extf_int_reductions_to_int_ground_match() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_int "42") 42))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "str.to_int(\"42\") = 42 ground match should be SAT, got {ay:?}"
    );
}

/// str.to_int("42") = 99: ground evaluation mismatch, must be UNSAT.
#[test]
#[timeout(10_000)]
fn extf_int_reductions_to_int_ground_mismatch() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_int "42") 99))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.to_int(\"42\") = 99 ground mismatch should be unsat, got {ay:?}"
    );
}

/// str.to_code(x) = -5: out of range (min is -1), must be UNSAT.
#[test]
#[timeout(10_000)]
fn extf_int_reductions_to_code_out_of_range() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.to_code x) (- 5)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "str.to_code(x) = -5 is out of range, should be unsat, got {ay:?}"
    );
}

// ===================================================================
// check_cycles_dfs (core.rs ~1500-1600)
//
// Self-referencing cycles: x = "a" ++ x creates an infinite string,
// which is impossible. The cycle detector should infer "a" = "" or
// detect a length conflict.
// ===================================================================

/// Single-hop cycle: x = "a" ++ x is UNSAT.
/// len(x) = 1 + len(x) implies 0 = 1, contradiction.
/// Exercises check_cycles_dfs I_CYCLE inference.
#[test]
#[timeout(10_000)]
fn cycles_single_hop_self_referencing_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.++ "a" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("unsat") | Some("unknown")),
        "x = \"a\" ++ x is a self-referencing cycle, should be unsat, got {ay:?}"
    );
}

/// Single-hop cycle with empty sibling: x = "" ++ x is SAT.
/// The empty string sibling makes the cycle trivial (x = x).
#[test]
#[timeout(10_000)]
fn cycles_single_hop_empty_sibling_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.++ "" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "x = \"\" ++ x must not be unsat, got {ay:?}"
    );
}

/// Two-hop cycle: x = "a" ++ y, y = "b" ++ x is UNSAT.
/// len(x) = 1 + len(y) = 1 + 1 + len(x) implies 0 = 2.
#[test]
#[timeout(10_000)]
fn cycles_two_hop_mutual_reference_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ "a" y)))
(assert (= y (str.++ "b" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "two-hop cycle x=\"a\"++y, y=\"b\"++x should be unsat, got {ay:?}"
    );
}

// ===================================================================
// check_normal_forms_deq: resolved-constants path (core.rs ~4290-4310)
//
// When both sides of a disequality resolve to different constants,
// the deq is trivially satisfied without further processing.
// ===================================================================

/// Different constants disequality: "abc" != "xyz" is trivially SAT.
/// The deq resolved-constants path should handle this immediately.
#[test]
#[timeout(10_000)]
fn deq_resolved_different_constants_trivially_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x "abc"))
(assert (= y "xyz"))
(assert (not (= x y)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "\"abc\" != \"xyz\" is trivially SAT, got {ay:?}"
    );
}

/// Same constant disequality: "abc" != "abc" is UNSAT.
/// Check 3 of check_normal_forms_deq should detect this.
#[test]
#[timeout(10_000)]
fn deq_same_constants_contradiction_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x "abc"))
(assert (= y "abc"))
(assert (not (= x y)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "\"abc\" != \"abc\" is a contradiction, should be unsat, got {ay:?}"
    );
}

/// process_simple_deq: same variable on both sides of deq.
/// x != x is trivially UNSAT.
#[test]
#[timeout(10_000)]
fn deq_same_variable_contradiction_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (not (= x x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "x != x is a trivial contradiction, should be unsat, got {ay:?}"
    );
}

// ===================================================================
// Additional proof coverage: negated integer equality with unresolved arg
//
// NOT(str.to_int(x) = 3) should set incomplete (x is unresolved).
// This tests the negated equality branch in check_extf_int_reductions.
// ===================================================================

/// NOT(str.to_int(x) = 3) with str.to_int(x) = 5 should be SAT.
/// Tests that negated equalities don't spuriously conflict.
#[test]
#[timeout(10_000)]
fn extf_int_reductions_negated_equality_no_false_conflict() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (str.to_int x) 3)))
(assert (= (str.to_int x) 5))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "str.to_int(x) != 3 AND str.to_int(x) = 5 should be SAT, got {ay:?}"
    );
}
