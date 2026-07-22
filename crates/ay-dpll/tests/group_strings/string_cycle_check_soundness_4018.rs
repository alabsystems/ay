// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #4018: cycle check explanation soundness.
//!
//! When the string theory's `check_cycles_dfs` detects a cycle like
//! `x = str.++(sk_pre, x, sk_post)` with a non-empty sibling, the conflict
//! explanation must include the non-emptiness evidence. Without it, the SAT
//! solver learns an over-general clause that blocks satisfying assignments,
//! causing false UNSAT.
//!
//! The concat+length false-UNSAT cases (x++y="ab" & len(x)>=1) have a
//! different root cause (#3820: DPLL interface explanation leaking) and are
//! covered in string_theory_verification.rs.

use ntest::timeout;

/// Minimal reproducer: `str.contains(x, x)` is always true (every string
/// contains itself). The contains decomposition creates `x = str.++(sk_pre, x, sk_post)`,
/// and the cycle checker must not over-generalize the conflict when sk_pre/sk_post
/// are constrained to be empty.
#[test]
#[timeout(30_000)]
fn self_contains_is_sat_issue_4018() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x x))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&output),
        Some("sat"),
        "str.contains(x, x) must be SAT. Got: {output}"
    );
}

/// `str.contains(x, x)` with a length constraint. This combines the cycle
/// check with LIA constraints via Nelson-Oppen.
#[test]
#[timeout(30_000)]
fn self_contains_with_length_is_sat_issue_4018() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x x))
(assert (= (str.len x) 5))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&output),
        Some("sat"),
        "str.contains(x, x) with len(x)=5 must be SAT. Got: {output}"
    );
}

/// Two overlapping contains on the same variable with tight length.
/// Reference: `soundness_multi_contains_overlapping_needles_sat` in
/// string_theory_verification.rs — failed with false UNSAT before the fix.
#[test]
#[timeout(30_000)]
fn overlapping_contains_with_length_is_sat_issue_4018() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "ab"))
(assert (str.contains x "bc"))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&output),
        Some("sat"),
        "contains(x,\"ab\") & contains(x,\"bc\") & len(x)=3 must be SAT. Got: {output}"
    );
}

/// Two non-overlapping contains with exact-fit length (SAT).
/// x = "abcd" satisfies contains(x,"ab") ∧ contains(x,"cd") ∧ len(x)=4.
#[test]
#[timeout(30_000)]
fn non_overlapping_contains_exact_fit_sat_issue_4018() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "ab"))
(assert (str.contains x "cd"))
(assert (= (str.len x) 4))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    assert!(
        matches!(
            crate::common::sat_result(&output),
            Some("sat") | Some("unknown")
        ),
        "contains(x,\"ab\") & contains(x,\"cd\") & len(x)=4 must not be UNSAT. Got: {output}"
    );
}

/// Two non-overlapping contains with insufficient length (UNSAT).
/// "ab" and "cd" have no overlap, so min length is 4. len(x)=3 is impossible.
#[test]
#[timeout(30_000)]
fn non_overlapping_contains_too_short_unsat_issue_4018() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "ab"))
(assert (str.contains x "cd"))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&output),
        Some("unsat"),
        "contains(x,\"ab\") & contains(x,\"cd\") & len(x)=3 must be UNSAT. Got: {output}"
    );
}

/// Three contains on the same variable — all decompositions must fire.
/// x = "abcde" satisfies all three: contains "ab", "cd", "de".
#[test]
#[timeout(30_000)]
fn three_contains_same_var_sat_issue_4018() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "ab"))
(assert (str.contains x "cd"))
(assert (str.contains x "de"))
(assert (= (str.len x) 5))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    assert!(
        matches!(
            crate::common::sat_result(&output),
            Some("sat") | Some("unknown")
        ),
        "contains(x,\"ab\") & contains(x,\"cd\") & contains(x,\"de\") & len(x)=5 must not be UNSAT. Got: {output}"
    );
}
