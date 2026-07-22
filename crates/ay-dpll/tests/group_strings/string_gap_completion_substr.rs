// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for gate-verified String GAP completion (#str-gap).
//!
//! A String-sorted variable pinned only by its `(str.len x) = N` LIA proxy
//! (and the substr/concat reduction skolems bridged to it) left the string
//! model incomplete: the reduced bridge equalities (`(= (str.substr x 0 3)
//! sk_res)`) could not be evaluated, degrading a genuine SAT to Unknown. The
//! fix adds a `Sort::String` arm to `GapStrategy::Derived` in
//! `fill_constrained_gap_vars` (derive from SAT-true string equalities, else
//! pad to the model length with a per-variable DISTINCT filler char) and
//! invokes the SAME snapshot-and-retract `complete_constrained_gaps` pass from
//! `finalize_sat_model_validation` (where the strings solver validates in-loop,
//! before the outer `emit_sat_verdict` sweep would run). Every completion is
//! re-checked by the strict + independent gates and RETRACTED on any
//! refutation, so this can only turn a today-Unknown string model into a
//! gate-validated SAT — never a wrong SAT (all the `..._not_sat` twins below).

/// Extract the quoted string value reported for `var` in a get-value line like
/// `((x "AAA"))`. Panics (failing the test) when the pair is missing.
fn extract_string_value(output: &str, var: &str) -> String {
    let needle = format!("({var} \"");
    let start = output
        .find(&needle)
        .unwrap_or_else(|| panic!("no get-value pair for {var} in: {output}"))
        + needle.len();
    let rest = &output[start..];
    let end = rest
        .find('"')
        .unwrap_or_else(|| panic!("unterminated string value for {var} in: {output}"));
    rest[..end].to_string()
}

/// Target probe 1 (substr-equals-whole): `(str.len x) = 3` and
/// `(str.substr x 0 3) = x`. z3: sat. Was unknown; the length-pad completes `x`
/// to a length-3 witness and derives the substr-result skolem from it.
#[test]
fn test_substr_equals_whole_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 3))
(assert (= (str.substr x 0 3) x))
(check-sat)
(get-value ((str.len x)))
"#;
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    // The emitted witness must have length 3 (the whole point — a `""` default
    // would violate `(str.len x) = 3`).
    assert!(
        output.contains(r#"((str.len x) 3)"#),
        "x must be a length-3 witness satisfying (str.len x)=3: {output}"
    );
}

/// The substr-equals-whole model must genuinely satisfy the formula: `x` of
/// length 3 makes `(str.substr x 0 3) = x` hold for any characters.
#[test]
fn test_substr_equals_whole_model_valid() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 3))
(assert (= (str.substr x 0 3) x))
(check-sat)
(get-value (x))
"#;
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    let x = extract_string_value(&output, "x");
    assert_eq!(x.chars().count(), 3, "x must have length 3: {output}");
    // `(str.substr x 0 3)` over a length-3 string is the whole string.
    let sub: String = x.chars().take(3).collect();
    assert_eq!(sub, x, "substr(x,0,3) must equal x: {output}");
}

/// The refutation twin: pin `x = "ab"` (length 2) alongside `(str.len x) = 3`.
/// A blind length-pad must NOT manufacture a SAT — the constraints are
/// contradictory (z3: unsat), so the completion is retracted.
#[test]
fn test_substr_equals_whole_pinned_conflict_not_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 3))
(assert (= (str.substr x 0 3) x))
(assert (= x "ab"))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    assert_ne!(
        crate::common::sat_result(&output),
        Some("sat"),
        "len(x)=3 with x=\"ab\" (len 2) is contradictory — must not be SAT: {output}"
    );
}

/// Target probe 2 (disequality-pad): two length-1 vars forced distinct,
/// `(str.len a)=1`, `(str.len b)=1`, `(not (= a b))`. z3: sat. Was unknown; a
/// blind uniform pad would make `a = b` and be retracted, so the per-variable
/// DISTINCT filler char is what lets this land as SAT.
///
/// Documented outcome: SAT with `a` and `b` distinct length-1 witnesses.
#[test]
fn test_disequality_pad_distinct_witnesses_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun a () String)
(declare-fun b () String)
(assert (= (str.len a) 1))
(assert (= (str.len b) 1))
(assert (not (= a b)))
(check-sat)
(get-value (a b))
"#;
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    let a = extract_string_value(&output, "a");
    let b = extract_string_value(&output, "b");
    assert_eq!(a.chars().count(), 1, "a must be length 1: {output}");
    assert_eq!(b.chars().count(), 1, "b must be length 1: {output}");
    assert_ne!(a, b, "a and b must be distinct witnesses: {output}");
}

/// The refutation twin: the same length-1 vars forced BOTH distinct AND equal
/// is contradictory (z3: unsat). The distinct-char pad must never make this
/// SAT.
#[test]
fn test_disequality_pad_contradiction_not_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun a () String)
(declare-fun b () String)
(assert (= (str.len a) 1))
(assert (= (str.len b) 1))
(assert (not (= a b)))
(assert (= a b))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    assert_ne!(
        crate::common::sat_result(&output),
        Some("sat"),
        "a=b and a!=b is contradictory — must not be SAT: {output}"
    );
}

/// Length-only control: `(str.len x) = 3` alone stays SAT with a length-3
/// witness (must not regress).
#[test]
fn test_len_only_control_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 3))
(check-sat)
(get-value ((str.len x)))
"#;
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    assert!(
        output.contains(r#"((str.len x) 3)"#),
        "length-only control must model a length-3 witness: {output}"
    );
}

/// Wrong-output guard: `(str.substr x 1 2) = "bc"` with `(str.len x) = 1` is
/// unsatisfiable (z3: unsat) — a length-1 string has no length-2 substring at
/// offset 1. The completion machinery must never emit SAT here.
#[test]
fn test_flat_substr_len_conflict_not_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.substr x 1 2) "bc"))
(assert (= (str.len x) 1))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    assert_ne!(
        crate::common::sat_result(&output),
        Some("sat"),
        "substr(x,1,2)=\"bc\" needs len(x)>=3, conflicting with len(x)=1: {output}"
    );
}
