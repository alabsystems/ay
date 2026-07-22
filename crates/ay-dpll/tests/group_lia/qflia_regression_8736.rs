// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! QF_LIA regression guard for #8736 and related "model-equality round
//! counter" completeness bugs.
//!
//! Background: #8727 closed the `ring_2exp16_5vars_cascade_v2_unsat`
//! benchmark. A subsequent audit (#8736) reported that it regressed to
//! `(:reason-unknown incomplete)` in ~22ms via the model-equality round
//! counter at
//! `crates/ay-dpll/src/pipeline_incremental_split_eager_macros.rs:450`.
//!
//! Re-verification at HEAD showed both `cascade_v2_unsat` and the
//! sibling 3-var pigeon conformance test resolve correctly to `unsat`
//! in well under a second. The Priority-1 fix landed in
//! `ea91c009d` (`note_theory_progress` resets the round counter on
//! learned theory conflicts) plus the per-pipeline model-equality dedup
//! (#8594) together cover the cascade_v2 and small-pigeon paths.
//!
//! The tests below pin both working paths so any future regression
//! triggers a fast, targeted failure instead of silently reopening the
//! audit finding.

use ntest::timeout;

/// #8736: `ring_2exp16_5vars_cascade_v2_unsat` must resolve to UNSAT.
///
/// This benchmark is a 16-bit ring cascade whose UNSAT proof requires
/// the LIA solver to observe "sum divisible by 3 vs. residue 1 (mod
/// 65536)" via the `NeedModelEqualities` handler plus integer-var
/// splitting. Previously it hit `UnknownReason::Incomplete` when the
/// model-equality round counter capped out before the SAT solver
/// learned theory conflicts. The #8727 + #8594 fixes ensure the round
/// counter resets on real progress, so the solver reaches UNSAT in
/// ~20ms.
///
/// The SMT2 below is copied verbatim from
/// `benchmarks/smt/QF_LIA/ring_2exp16_5vars_cascade_v2_unsat.smt2`.
/// Keep the assertions byte-identical to the benchmark; if the
/// benchmark changes, update both.
#[test]
#[timeout(5_000)]
fn test_8736_cascade_v2_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x1 Int) (declare-const x2 Int) (declare-const x3 Int)
        (declare-const x4 Int) (declare-const x5 Int)
        (declare-const s1 Int) (declare-const s2 Int) (declare-const s3 Int)
        (declare-const s4 Int)
        (declare-const c1 Int) (declare-const c2 Int) (declare-const c3 Int)
        (declare-const c4 Int)

        (assert (>= x1 0)) (assert (<= x1 65535))
        (assert (>= x2 0)) (assert (<= x2 65535))
        (assert (>= x3 0)) (assert (<= x3 65535))
        (assert (>= x4 0)) (assert (<= x4 65535))
        (assert (>= x5 0)) (assert (<= x5 65535))
        (assert (>= s1 0)) (assert (<= s1 65535))
        (assert (>= s2 0)) (assert (<= s2 65535))
        (assert (>= s3 0)) (assert (<= s3 65535))
        (assert (>= s4 0)) (assert (<= s4 65535))

        (assert (>= c1 0)) (assert (<= c1 1))
        (assert (>= c2 0)) (assert (<= c2 1))
        (assert (>= c3 0)) (assert (<= c3 1))
        (assert (>= c4 0)) (assert (<= c4 1))

        (assert (= (+ x1 x2) (+ (* 65536 c1) s1)))
        (assert (= (+ s1 x3) (+ (* 65536 c2) s2)))
        (assert (= (+ s2 x4) (+ (* 65536 c3) s3)))
        (assert (= (+ s3 x5) (+ (* 65536 c4) s4)))

        (assert (= (mod x1 3) 0))
        (assert (= (mod x2 3) 0))
        (assert (= (mod x3 3) 0))
        (assert (= (mod x4 3) 0))
        (assert (= (mod x5 3) 0))

        (assert (>= x1 40000)) (assert (<= x1 60000))
        (assert (>= x2 40000)) (assert (<= x2 60000))
        (assert (>= x3 40000)) (assert (<= x3 60000))
        (assert (>= x4 40000)) (assert (<= x4 60000))
        (assert (>= x5 40000)) (assert (<= x5 60000))

        (assert (= s4 1))

        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "#8736 / #8727: ring_2exp16_5vars_cascade_v2_unsat must be UNSAT. \
         If this fails with 'unknown (:reason-unknown incomplete)' the \
         model-equality round counter in \
         crates/ay-dpll/src/pipeline_incremental_split_eager_macros.rs \
         has regressed — the `note_theory_progress` reset or the \
         `_islp_seen_model_eq_requests` dedup is no longer firing."
    );
}

/// #8736 (audit comment on #8707): the 3-pigeons / 2-holes conformance
/// benchmark exits the same model-equality pipeline path as
/// `cascade_v2`. A 22ms `incomplete` result here means the UNSAT proof
/// via integer splits + distinct chain was cut off before convergence.
///
/// The SMT2 below is copied verbatim from
/// `benchmarks/conformance/QF_LIA/unsat_pigeon_3_2.smt2`.
#[test]
#[timeout(5_000)]
fn test_8736_pigeon_3_2_unsat() {
    let smt = r#"
        (set-info :status unsat)
        (set-logic QF_LIA)
        (declare-const p1 Int)
        (declare-const p2 Int)
        (declare-const p3 Int)
        (assert (>= p1 1))
        (assert (<= p1 2))
        (assert (>= p2 1))
        (assert (<= p2 2))
        (assert (>= p3 1))
        (assert (<= p3 2))
        (assert (distinct p1 p2 p3))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "#8736 / #8707: 3-pigeon 2-hole distinct must be UNSAT. \
         If this fails with 'unknown (:reason-unknown incomplete)' the \
         same model-equality round-counter regression as \
         test_8736_cascade_v2_unsat has fired on a much smaller formula."
    );
}
