// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// =============================================================================
// Prover P19: str.to_lower / str.to_upper soundness
// =============================================================================

/// str.to_upper("abc") ≠ "ABC" is UNSAT.
#[test]
fn to_upper_constant_wrong_value_unsat() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.to_upper "abc") "ABC")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "to_upper wrong value: expected unsat, got {ay:?}"
    );
}

/// str.to_lower("ABC") ≠ "abc" is UNSAT.
#[test]
fn to_lower_constant_wrong_value_unsat() {
    let smt = r#"
(set-logic QF_S)
(assert (not (= (str.to_lower "ABC") "abc")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "to_lower wrong value: expected unsat, got {ay:?}"
    );
}

/// str.to_lower(str.to_upper(x)) = str.to_lower(x) for constant x.
///
/// Idempotence: lowering an uppercased string gives the same as lowering directly.
/// AY currently returns unknown (incompleteness, not soundness bug).
#[test]
fn to_lower_of_to_upper_equals_to_lower() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "Hello World"))
(assert (= (str.to_lower (str.to_upper x)) (str.to_lower x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "to_lower(to_upper(x))==to_lower(x): expected sat or unknown, got {ay:?}"
    );
}

// =============================================================================
// Prover P19: str.to_code / str.from_code boundary conditions
// =============================================================================

/// str.from_code of a negative value returns empty string.
/// str.from_code(-1) = "" should be SAT.
#[test]
fn from_code_negative_returns_empty() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.from_code (- 1)) ""))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "from_code negative: expected sat, got {ay:?}"
    );
}

/// str.from_code above 196607 (SMT-LIB unicode max) returns empty string.
#[test]
fn from_code_above_smtlib_max_returns_empty() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.from_code 196608) ""))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "from_code above max: expected sat, got {ay:?}"
    );
}

/// str.to_code(str.from_code(65)) = 65 should be SAT (roundtrip).
#[test]
fn to_code_from_code_roundtrip_65() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.to_code (str.from_code 65)) 65))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "to_code(from_code(65)): expected sat, got {ay:?}"
    );
}

// =============================================================================
// Prover P19: mixed string-integer reasoning soundness
// =============================================================================

/// str.len(str.++ x y) = str.len(x) + str.len(y) for concrete strings.
#[test]
fn len_concat_equals_sum_of_lens_concrete() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x "abc"))
(assert (= y "de"))
(assert (not (= (str.len (str.++ x y)) (+ (str.len x) (str.len y)))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "len(x++y) = len(x) + len(y): expected unsat, got {ay:?}"
    );
}

/// Negative length is always unsat.
/// str.len(x) = -1 should be UNSAT.
#[test]
fn negative_length_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) (- 1)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "negative length: expected unsat, got {ay:?}"
    );
}

// ===================================================================
// Inequality range check regression tests (#3695 audit)
//
// Verify that check_extf_int_reductions correctly rejects impossible
// inequality constraints on range-restricted functions. Before the fix,
// only equality assertions were scanned.
// ===================================================================

/// str.to_int(x) < -1: UNSAT.
/// Minimum of str.to_int is -1, so no value is < -1.
/// Boundary test: -1 is valid, < -1 is not.
#[test]
fn inequality_str_to_int_lt_minus_one_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (< (str.to_int x) (- 1)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        ay == Some("unsat") || ay == Some("unknown"),
        "str.to_int(x) < -1: expected unsat or unknown, got {ay:?}"
    );
}

/// str.to_int(x) <= -2: UNSAT.
/// Range is {-1} ∪ Z≥0; -2 is below minimum.
#[test]
fn inequality_str_to_int_le_minus_two_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (<= (str.to_int x) (- 2)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        ay == Some("unsat") || ay == Some("unknown"),
        "str.to_int(x) <= -2: expected unsat or unknown, got {ay:?}"
    );
}

/// str.to_int(x) >= -1: SAT (positive control).
/// -1 is a valid output (non-numeric strings).
#[test]
fn inequality_str_to_int_ge_minus_one_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (>= (str.to_int x) (- 1)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "str.to_int(x) >= -1 is a tautology, expected sat, got {ay:?}"
    );
}

/// str.to_code(x) > 196607: UNSAT.
/// Maximum codepoint in SMT-LIB is 196607.
#[test]
fn inequality_str_to_code_gt_max_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (> (str.to_code x) 196607))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        ay == Some("unsat") || ay == Some("unknown"),
        "str.to_code(x) > 196607: expected unsat or unknown, got {ay:?}"
    );
}

/// str.to_code(x) >= 196608: UNSAT.
/// Boundary: 196607 is valid, 196608 is not.
#[test]
fn inequality_str_to_code_ge_196608_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (>= (str.to_code x) 196608))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        ay == Some("unsat") || ay == Some("unknown"),
        "str.to_code(x) >= 196608: expected unsat or unknown, got {ay:?}"
    );
}

/// str.to_code(x) <= 196607: SAT (positive control).
/// The full valid range is [-1, 196607].
#[test]
fn inequality_str_to_code_le_max_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (<= (str.to_code x) 196607))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "str.to_code(x) <= 196607 must not be unsat, got {ay:?}"
    );
}

/// str.indexof(x, "a", 0) < -1: UNSAT.
/// Minimum of str.indexof is -1 (not found).
#[test]
fn inequality_str_indexof_lt_minus_one_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (< (str.indexof x "a" 0) (- 1)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        ay == Some("unsat") || ay == Some("unknown"),
        "str.indexof(x, \"a\", 0) < -1: expected unsat or unknown, got {ay:?}"
    );
}

// ===================================================================
// str.from_code CEGAR convergence tests (#3737 related)
//
// Ground nested function applications involving str.from_code should
// converge. The CEGAR bridge currently lacks axiom generation for
// str.from_code, causing non-convergence on some ground formulas.
// ===================================================================

/// str.from_code(122) = "z": SAT (ground constant).
/// This should converge because "z" has code 122.
#[test]
fn from_code_ground_constant_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.from_code 122) "z"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "str.from_code(122) = \"z\" should be SAT, got {ay:?}"
    );
}

/// str.from_code(-1) = "": SAT (negative → empty).
/// SMT-LIB semantics: str.from_code of negative number returns "".
#[test]
fn from_code_negative_returns_empty_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(assert (= (str.from_code (- 1)) ""))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "str.from_code(-1) = \"\" should be SAT, got {ay:?}"
    );
}

/// Concatenation associativity: tautology.
#[test]
fn concat_associativity_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (not (= (str.++ (str.++ x y) z) (str.++ x (str.++ y z)))))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "concat associativity should be unsat, got {ay:?}"
    );
}

/// str.contains(x, x) is always true.
#[test]
fn contains_self_tautology_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (not (str.contains x x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "str.contains(x, x) is always true, negation should be unsat, got {ay:?}"
    );
}

/// Empty string is a prefix of everything.
#[test]
fn empty_prefix_tautology_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (not (str.prefixof "" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "str.prefixof(\"\", x) is always true, negation should be unsat, got {ay:?}"
    );
}
