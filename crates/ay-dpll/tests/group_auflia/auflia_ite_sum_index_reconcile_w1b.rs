// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final-assignment array-cell reconciliation regression
//! (#qf-auflia-final-index-reconcile, model-checker-consumer parity wishlist item 1,
//! second trigger — the QF_AUFLIA lane, distinct from the ABV lane bug).
//!
//! Shape: the ay-chc BMC executor lane lowers a wide-BV table index to
//! per-bit Bools recombined as `(+ (ite b0 1 0) (* (ite b1 1 0) 2) ... K)`
//! over an `(Array Int Int)`, and asserts a distinctness between two reads
//! whose ite-sum indices differ only in fixed +16/+32 tag bits. The formula
//! is trivially SAT (the two indices can never coincide), but the AUFLIA
//! combined lane extracted the array interpretation keyed by SPECULATIVE
//! LIA values of the composite indices (the LIA solver never sees the SAT
//! Bool assignment), so under the final assignment both asserted reads hit
//! ABSENT cells, model completion collapsed them to one default, and the
//! independent soundness gate refused the model — `unknown` instead of
//! `sat`, with the "[AY SOUNDNESS GATE] caught an INVALID model" banner
//! re-manufactured on every CHC portfolio probe.
//!
//! Since every emitted `sat` passes the strict + independent +
//! authoritative-failclosed gate funnel (#sat-chokepoint), asserting the
//! verdict IS `sat` asserts both halves of the fix: the model construction
//! is valid AND the gate did not fire (a gate rejection surfaces as
//! `unknown`).

/// The minimized gate-firing sub-query (from w1_min.smt2's BMC lane): two
/// ite-sum reads under a distinctness constraint. Must be SAT with a model
/// in which the two reads really differ.
#[test]
fn ite_sum_index_distinct_reads_sat_with_valid_model() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-const v1 (Array Int Int))
(declare-const b0 Bool)
(declare-const b1 Bool)
(declare-const b2 Bool)
(declare-const b3 Bool)
(declare-const b4 Bool)
(declare-const b5 Bool)
(declare-const b6 Bool)
(declare-const b7 Bool)
(assert (or (and (not b0) (not b1) (not b2) (not b3) (not b4) (not b5) (not b6) (not b7))
            (and (not b0) (not b1) (not b2) (not b3) (not b4) (not b5) (not b6))))
(assert (not (= (select v1 (+ (ite b0 1 0) (* (ite b1 1 0) 2) (* (ite b2 1 0) 4) (* (ite b3 1 0) 8) (* (ite b5 1 0) 32) (* (ite b6 1 0) 64) (* (ite b7 1 0) 128) 16))
                (select v1 (+ (ite b0 1 0) (* (ite b1 1 0) 2) (* (ite b2 1 0) 4) (* (ite b3 1 0) 8) (* (ite b4 1 0) 16) (* (ite b6 1 0) 64) (* (ite b7 1 0) 128) 32)))))
(check-sat)
"#,
    );
    assert_eq!(
        outputs.first().map(|s| s.trim()),
        Some("sat"),
        "ite-sum-index distinct-reads query is trivially SAT (indices can \
         never coincide); `unknown` means the invalid-model construction \
         regressed (gate fired) — got: {outputs:?}"
    );
}

/// Genuine-SAT preservation: the same reads asserted EQUAL must stay `sat`
/// (guards against the reconcile pass over-degrading via spurious cell
/// conflicts).
#[test]
fn ite_sum_index_equal_reads_stays_sat() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-const v1 (Array Int Int))
(declare-const b0 Bool)
(declare-const b1 Bool)
(assert (= (select v1 (+ (ite b0 1 0) (* (ite b1 1 0) 2) 16))
           (select v1 (+ (ite b0 1 0) (* (ite b1 1 0) 2) 32))))
(check-sat)
"#,
    );
    assert_eq!(
        outputs.first().map(|s| s.trim()),
        Some("sat"),
        "equal-reads variant is genuinely SAT and must not degrade: {outputs:?}"
    );
}

/// Verdict-flip guard: a self-distinctness over ONE ite-sum read is UNSAT
/// and must never become `sat` (the reconcile pass adds cells forced by the
/// model's own committed reads — it must not manufacture a witness).
#[test]
fn ite_sum_index_self_distinct_read_stays_unsat() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-const v1 (Array Int Int))
(declare-const b0 Bool)
(declare-const b1 Bool)
(assert (not (= (select v1 (+ (ite b0 1 0) (* (ite b1 1 0) 2) 16))
                (select v1 (+ (ite b0 1 0) (* (ite b1 1 0) 2) 16)))))
(check-sat)
"#,
    );
    assert_eq!(
        outputs.first().map(|s| s.trim()),
        Some("unsat"),
        "self-distinct read is UNSAT and must stay so: {outputs:?}"
    );
}
