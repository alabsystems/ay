// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// =============================================================================
// Regression: flatten_concat EQC walking soundness (#3794)
// =============================================================================

/// Regression for #3794: str.contains(x, "hello") ∧ x = "goodbye" must be UNSAT.
///
/// The unsound flatten_concat (commit d848802e3) walked EQC members and found
/// the Skolem decomposition str.++(sk_pre, "hello", sk_suf) as a component of
/// x's EQC. This made concat_contains_constant return true, masking the
/// contradiction with x = "goodbye". The fix restricts flatten_concat to
/// syntactic-only traversal.
///
/// Bug 1: Stack overflow (no cycle detection in EQC walk)
/// Bug 2: Incorrect true result prevents conflict detection
#[test]
fn regression_3794_contains_constant_contradiction_not_masked() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (str.contains x "hello"))
(assert (= x "goodbye"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("sat"),
        "#3794 regression: contains(x,\"hello\") ∧ x=\"goodbye\" must NOT be sat, got {ay:?}"
    );
}

/// Same pattern but with a prefix instead of a different word.
/// str.contains(x, "abc") ∧ x = "xyz" must be UNSAT.
#[test]
fn regression_3794_contains_constant_no_overlap() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (str.contains x "abc"))
(assert (= x "xyz"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("sat"),
        "#3794 regression: contains(x,\"abc\") ∧ x=\"xyz\" must NOT be sat, got {ay:?}"
    );
}

/// Positive control: str.contains(x, "llo") ∧ x = "hello" IS SAT.
/// Ensures the fix doesn't over-restrict containment checking.
#[test]
fn regression_3794_contains_constant_positive_control() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (str.contains x "llo"))
(assert (= x "hello"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "#3794 positive control: contains(x,\"llo\") ∧ x=\"hello\" should be sat, got {ay:?}"
    );
}

// ===================================================================
// Memory verification: push/pop correctness, deep nesting, RAII
// ===================================================================

/// Memory verification: nested str.++ equality doesn't stack overflow.
/// Uses pure equality (no str.contains) so no CEGAR needed.
/// Tests that deeply nested concat terms are handled correctly in
/// the string solver's normal-form and flatten operations.
#[test]
fn memory_deep_concat_nesting_no_stack_overflow() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x (str.++ (str.++ (str.++ (str.++ "a" "b") "c") "d") "e")))
(assert (= x "abcde"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "Deep constant concat = literal equality: should be sat, got {ay:?}"
    );
}

/// Memory verification: push/pop scope isolation for string solver.
/// After pop, conflicting assertions from the pushed scope must not leak.
/// Validates RAII correctness of SolverState trail-based backtracking.
#[test]
fn memory_push_pop_scope_isolation() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(push 1)
(assert (= x "hello"))
(assert (= x "world"))
(check-sat)
(pop 1)
(assert (= x "hello"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let results: Vec<&str> = result
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .collect();
    assert_eq!(
        results.len(),
        2,
        "Expected 2 check-sat results, got {results:?}"
    );
    assert_eq!(
        results[0], "unsat",
        "x=\"hello\" ∧ x=\"world\" in pushed scope must be unsat, got {}",
        results[0]
    );
    assert_eq!(
        results[1], "sat",
        "x=\"hello\" after pop must be sat, got {}",
        results[1]
    );
}

/// Memory verification: multiple push/pop cycles don't leak state.
/// Each cycle asserts a contradiction, pops, then asserts a satisfiable formula.
#[test]
fn memory_repeated_push_pop_no_state_leak() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(push 1)
(assert (= x "a"))
(assert (= x "b"))
(check-sat)
(pop 1)
(push 1)
(assert (= x "c"))
(assert (= x "d"))
(check-sat)
(pop 1)
(assert (= x "hello"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let results: Vec<&str> = result
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .collect();
    assert_eq!(
        results.len(),
        3,
        "Expected 3 check-sat results, got {results:?}"
    );
    assert_eq!(
        results[0], "unsat",
        "First scope contradiction: {}",
        results[0]
    );
    assert_eq!(
        results[1], "unsat",
        "Second scope contradiction: {}",
        results[1]
    );
    assert_eq!(
        results[2], "sat",
        "After all pops, x=\"hello\" is sat: {}",
        results[2]
    );
}

/// Memory verification: contains decomposition doesn't create unbounded
/// Skolem terms on a trivial formula. The solver may report `unknown` for
/// incomplete contains reasoning, but must not derive a false contradiction.
#[test]
fn memory_contains_cegar_converges_quickly() {
    // This formula is trivially SAT: x can be anything containing "ab".
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "ab"))
(assert (>= (str.len x) 5))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "Trivial contains with length bound must not be unsat, got {ay:?}"
    );
}

/// Concat length contradiction: x++y = "ab" with len(x) = 3 is UNSAT.
#[test]
fn concat_length_contradiction_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "ab"))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("unsat"),
        "x++y = \"ab\" with len(x)=3: UNSAT, got {ay:?}"
    );
}

// ===================================================================
// P5 iteration 2: multiple str.contains interaction false-UNSAT
// ===================================================================

/// Two str.contains with different patterns on a ground-assigned variable.
/// x = "ab" with contains(x, "a") and contains(x, "b") is trivially SAT.
/// Regression: AY returned false UNSAT because multiple contains decompositions
/// (via eager preregistration) create conflicting Skolem constraints.
/// Tracked as #3919.
#[test]
fn soundness_multiple_contains_ground_variable_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "a"))
(assert (str.contains x "b"))
(assert (= x "ab"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "multiple contains on x=\"ab\" must be SAT, got {ay:?}"
    );
}

/// Two str.contains with different patterns on a 3-char string.
/// x = "abc" with contains(x, "a") and contains(x, "b") is SAT.
#[test]
fn soundness_multiple_contains_ground_3char_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "a"))
(assert (str.contains x "b"))
(assert (= x "abc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "multiple contains on x=\"abc\" must be SAT, got {ay:?}"
    );
}

/// Overlapping contains patterns: contains(x, "ab") AND contains(x, "bc")
/// with x = "abc" is SAT.
#[test]
fn soundness_overlapping_contains_patterns_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "ab"))
(assert (str.contains x "bc"))
(assert (= x "abc"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "overlapping contains on x=\"abc\" must be SAT, got {ay:?}"
    );
}

/// QF_S variant of #3919 reproducer.
#[test]
fn soundness_multiple_contains_ground_variable_qf_s_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (str.contains x "a"))
(assert (str.contains x "b"))
(assert (= x "ab"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "QF_S multiple contains on x=\"ab\" must be SAT, got {ay:?}"
    );
}

/// Single str.contains with ground assignment: sanity check (should be SAT).
/// This case works correctly — only the interaction of multiple contains fails.
#[test]
fn soundness_single_contains_ground_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "a"))
(assert (= x "ab"))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "single contains with ground assignment must be SAT, got {ay:?}"
    );
}

// ===================================================================
// P5 iteration 2: woorpje false-UNSAT scope measurement
// ===================================================================

/// Minimal woorpje-style word equation: x++y = "ab" with x != "" and y != "".
/// Previously false UNSAT (#3826). Soundness: must not return unsat.
/// Full completeness (returning sat) requires ConstSplit CEGAR loop.
#[test]
fn soundness_woorpje_minimal_concat_nonempty_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "ab"))
(assert (not (= x "")))
(assert (not (= y "")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "x++y=\"ab\" with x!=\"\" and y!=\"\" must not be unsat, got: {ay:?}"
    );
}

/// x++y = "abc" with x != "" and y != "" is SAT (e.g. x="a", y="bc").
/// Previously false UNSAT (#3826). Soundness: must not return unsat.
/// Full completeness (returning sat) requires ConstSplit CEGAR loop.
#[test]
fn soundness_woorpje_concat_3char_nonempty_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "abc"))
(assert (not (= x "")))
(assert (not (= y "")))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "x++y=\"abc\" with x!=\"\" and y!=\"\" must not be unsat, got: {ay:?}"
    );
}
