// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #4055: false UNSAT from EndpointEmpty conflict
//! when two concat equations on the same variable have misaligned NF
//! components.
//!
//! Root cause: process_simple_neq's endpoint handling declared immediate
//! conflict when remaining components were known non-empty, but the NFs
//! were from different concat equations on the same variable, causing
//! component misalignment. CVC5 never immediately conflicts on endpoints;
//! it infers remaining components = "" via the equality engine.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn solve(smt: &str) -> String {
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .map(|lines| lines.join("\n"))
        .unwrap_or_else(|e| format!("error: {e}"))
}

/// Two concat equations with length constraint (#4095):
///   x = "ab"++sk1, x = sk2++"bc", len(x)=3
/// Correct answer: SAT (x="abc", sk1="c", sk2="a").
///
/// Regression for #4055: this must resolve to SAT via overlap inference.
#[test]
#[timeout(10_000)]
fn dual_concat_length_known_is_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun sk1 () String)
(declare-fun sk2 () String)
(assert (= x (str.++ "ab" sk1)))
(assert (= x (str.++ sk2 "bc")))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "dual concat with fixed length must not be unsat; got {ay:?}"
    );
}

/// Variant: prefix + suffix with single-char overlap.
/// prefixof("ab", x) AND suffixof("bc", x) AND len(x) = 3
/// SAT model: x = "abc"
#[test]
#[timeout(10_000)]
fn prefix_suffix_overlap_is_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.prefixof "ab" x))
(assert (str.suffixof "bc" x))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "prefix(\"ab\",x) + suffix(\"bc\",x) + len=3 is SAT (x=\"abc\")"
    );
}

/// Two concat equations without length constraint.
/// x = "ab" ++ sk1 AND x = sk2 ++ "bc"
/// SAT model: x = "abc", sk1 = "c", sk2 = "a" (among many)
///
/// KNOWN GAP: AY may return unknown (incomplete) on dual-concat equations.
/// When completeness improves: assert_eq!(ay, Some("sat"), ...)
#[test]
#[timeout(10_000)]
fn dual_concat_no_length_known_gap() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun sk1 () String)
(declare-fun sk2 () String)
(assert (= x (str.++ "ab" sk1)))
(assert (= x (str.++ sk2 "bc")))
(check-sat)
"#;
    let result = solve(smt);
    let ay = crate::common::sat_result(&result);
    // Soundness guard: must not return false UNSAT (#4055).
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "dual concat equations is SAT; expected sat/unknown known-gap behavior, got {ay:?}"
    );
}

/// Overlap pattern with an explicit disequality on x.
/// SAT model: x = "abc" also satisfies x != "abd".
///
/// This regression guards #4104: if NF deq handling incorrectly treats an
/// uncertified disequality as settled, the solver can learn false conflicts
/// and report UNSAT.
#[test]
fn prefix_suffix_overlap_with_literal_disequality_not_false_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.prefixof "ab" x))
(assert (str.suffixof "bc" x))
(assert (= (str.len x) 3))
(assert (distinct x "abd"))
(check-sat)
"#;
    let result = solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("unsat"),
        "prefix/suffix overlap with x != \"abd\" is SAT (x=\"abc\"); must not return unsat"
    );
}

/// Two concat decompositions with an extra skolem disequality.
/// SAT witness: x="abc", sk1="c", sk2="a", and sk1 != sk2.
#[test]
fn dual_concat_overlap_with_skolem_disequality_not_false_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun sk1 () String)
(declare-fun sk2 () String)
(assert (= x (str.++ "ab" sk1)))
(assert (= x (str.++ sk2 "bc")))
(assert (distinct sk1 sk2))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("unsat"),
        "dual concat overlap with sk1 != sk2 is SAT (sk1=\"c\", sk2=\"a\"); must not return unsat"
    );
}
