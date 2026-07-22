// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// Cycle detection regression tests (P2 iteration 3)
//
// Multi-hop cycle detection fixed: check_cycles() uses recursive DFS
// (ported from CVC5 core_solver.cpp:442-549) to detect transitive
// containment cycles through chains of concat terms across EQCs.
// =============================================================================

/// Three-step cycle: x = "a"++y, y = "b"++z, z = "c"++x.
///
/// Substituting gives x = "abc"++x, requiring x to be infinite. UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_three_step_cycle_unsat() {
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
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "three-step containment cycle is UNSAT"
    );
}

/// Four-step cycle: x="a"++y, y="b"++z, z="c"++w, w="d"++x.
///
/// Substituting gives x = "abcd"++x, requiring x to be infinite. UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_four_step_cycle_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(assert (= x (str.++ "a" y)))
(assert (= y (str.++ "b" z)))
(assert (= z (str.++ "c" w)))
(assert (= w (str.++ "d" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "four-step containment cycle is UNSAT"
    );
}

/// Suffix-based two-step cycle: x = y++"a", y = x++"b".
///
/// Substituting gives x = x++"ba", requiring x to be infinite. UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_suffix_two_step_cycle_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ y "a")))
(assert (= y (str.++ x "b")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "suffix two-step containment cycle is UNSAT"
    );
}

/// Mixed prefix/suffix two-step cycle: x = "a"++y, y = x++"b".
///
/// Substituting gives x = "a"++x++"b", requiring x to be infinite. UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_mixed_cycle_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ "a" y)))
(assert (= y (str.++ x "b")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "mixed prefix/suffix containment cycle is UNSAT"
    );
}

/// Equality-based cycle correctly reduced to 1-step.
///
/// x = y ∧ y = "a"++x merges x,y into same EQC, then detects
/// the 1-step cycle rep = "a"++rep.
#[test]
#[timeout(10_000)]
fn soundness_eq_reduces_to_single_step_cycle() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x y))
(assert (= y (str.++ "a" x)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "x=y ∧ y=\"a\"++x reduces to 1-step cycle (UNSAT)"
    );
}

/// Self-referential concat on both sides is correctly detected.
///
/// x = "a" ++ x ++ "b" requires x to contain itself as a proper
/// substring, which is impossible for finite strings.
#[test]
#[timeout(10_000)]
fn soundness_self_concat_both_sides_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.++ "a" x "b")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "x = \"a\"++x++\"b\" is UNSAT (self-referential)"
    );
}

// =============================================================================
// Differential testing coverage (P2 iteration 3)
//
// Additional tests from 30-case AY-vs-Z3 differential suite.
// Tests below verify AY matches Z3 on resolved cases.
// =============================================================================

/// Length of concat equals sum of lengths.
///
/// len(x++y) = 5 ∧ len(x) = 2 ∧ len(y) = 4 is UNSAT (2+4=6≠5).
#[test]
#[timeout(10_000)]
fn soundness_len_concat_sum_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.len (str.++ x y)) 5))
(assert (= (str.len x) 2))
(assert (= (str.len y) 4))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "len(x++y)=5 ∧ len(x)=2 ∧ len(y)=4 is UNSAT"
    );
}

/// Length negative is always UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_len_negative_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (< (str.len x) 0))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "len(x) < 0 is always UNSAT"
    );
}

/// Length transitivity: x=y implies len(x)=len(y).
#[test]
#[timeout(10_000)]
fn soundness_len_transitivity_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x y))
(assert (= (str.len x) 3))
(assert (not (= (str.len y) 3)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "x=y ∧ len(x)=3 ∧ len(y)≠3 is UNSAT"
    );
}

/// Disequality with resolved constants.
#[test]
#[timeout(10_000)]
fn soundness_diseq_resolved_constants_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x "abc"))
(assert (= y "abc"))
(assert (not (= x y)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "x=\"abc\" ∧ y=\"abc\" ∧ x≠y is UNSAT"
    );
}

/// Prefix implies contains: prefix("hel", x) ∧ ¬contains(x, "hel") is UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_prefix_implies_contains() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= x "hello"))
(assert (str.prefixof "hel" x))
(assert (not (str.contains x "hel")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(ay, Some("unsat"), "prefix implies contains: got {ay:?}");
}

/// Variable with concat and length: sat case.
///
/// x = y++"!" ∧ len(x)=4 ∧ len(y)=3 is SAT (e.g., y="abc", x="abc!").
#[test]
#[timeout(10_000)]
fn soundness_var_concat_len_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ y "!")))
(assert (= (str.len x) 4))
(assert (= (str.len y) 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let answer = crate::common::sat_result(&result);
    // x=y++"!" with len(x)=4, len(y)=3 is SAT (e.g., y="abc", x="abc!").
    // AY currently returns unknown (SLIA incompleteness).
    assert!(
        matches!(answer, Some("sat") | Some("unknown")),
        "x=y++\"!\" ∧ len(x)=4 ∧ len(y)=3 must be sat or unknown; got {answer:?}"
    );
}

/// Disequality with same-length resolved strings is UNSAT.
#[test]
#[timeout(10_000)]
fn soundness_diseq_same_value_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= x y)))
(assert (= (str.len x) 1))
(assert (= (str.len y) 1))
(assert (= x "a"))
(assert (= y "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "x≠y ∧ x=\"a\" ∧ y=\"a\" is UNSAT"
    );
}

// =============================================================================
// Cycle detection soundness regression: variable-concat-suffix (#3375 related)
//
// check_cycles must use is_known_nonempty (not !is_empty_string) to avoid
// false cycle conflicts when a variable sibling has unknown emptiness.
// =============================================================================

/// Soundness: str.++(x, "a") = "a" is SAT (x = "").
///
/// Previously returned unsat because check_cycles treated variable x as
/// non-empty (using !is_empty_string instead of is_known_nonempty).
/// The cycle check saw "a" as a child with the same EQC representative,
/// x as a "non-empty" sibling, and reported a false containment cycle.
#[test]
#[timeout(10_000)]
fn soundness_variable_concat_suffix_equals_constant_is_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x "a") "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // Must NOT be unsat — this is SAT with x = "".
    assert_ne!(
        ay,
        Some("unsat"),
        "str.++(x,\"a\") = \"a\" must NOT be unsat (it's SAT with x=\"\")"
    );
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "expected sat or unknown, got {ay:?}"
    );
}

/// Soundness: str.++("a", x) = "a" is SAT (x = "").
///
/// Same pattern but with the variable on the right.
#[test]
#[timeout(10_000)]
fn soundness_variable_concat_prefix_equals_constant_is_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ "a" x) "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("unsat"),
        "str.++(\"a\",x) = \"a\" must NOT be unsat (it's SAT with x=\"\")"
    );
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "expected sat or unknown, got {ay:?}"
    );
}

/// Soundness: str.++(x, y) = "a" is SAT (e.g., x="a", y="" or x="", y="a").
///
/// Both variables could be empty, so no cycle conflict.
#[test]
#[timeout(10_000)]
fn soundness_two_variable_concat_equals_constant_is_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(ay, Some("unsat"), "str.++(x,y) = \"a\" must NOT be unsat");
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "expected sat or unknown, got {ay:?}"
    );
}

/// Variable concat suffix equals constant: str.++(x, "a") = "a".
///
/// SAT with x = "". The solver must not report unsound Unsat.
/// Tests that the process_nf_against_constant fallthrough to
/// process_simple_neq doesn't produce a spurious conflict when the
/// concat NF [x, "a"] is compared against constant NF ["a"].
#[test]
#[timeout(10_000)]
fn soundness_var_concat_suffix_equals_constant_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.++ x "a") "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // Returns sat when empty string is pre-registered in executor (see #3387).
    // Forbid unsound unsat regardless.
    assert_ne!(
        ay,
        Some("unsat"),
        "str.++(x,\"a\") = \"a\" must NOT be unsat (it's SAT with x=\"\")"
    );
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "expected sat or unknown, got {ay:?}"
    );
}

/// Variable concat prefix equals constant: str.++("a", x) = "a".
///
/// SAT with x = "". Similar to suffix case above.
#[test]
#[timeout(10_000)]
fn soundness_var_concat_prefix_equals_constant_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.++ "a" x) "a"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    // Returns sat when empty string is pre-registered in executor.
    // Forbid unsound unsat regardless.
    assert_ne!(
        ay,
        Some("unsat"),
        "str.++(\"a\",x) = \"a\" must NOT be unsat (it's SAT with x=\"\")"
    );
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "expected sat or unknown, got {ay:?}"
    );
}
