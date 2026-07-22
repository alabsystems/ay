// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness regression tests for #6282: store base decomposition axioms and
//! store value injectivity propagation.
//!
//! These tests exercise the axioms from `add_store_store_base_decomposition_axioms`
//! in euf.rs and the value injectivity propagation in arrays/lib.rs.

use ntest::timeout;

/// Store value injectivity: if store(A,i,v1) = store(B,i,v2) then v1 = v2.
///
/// Without value injectivity propagation, the solver could miss that the
/// stored values must be equal when two stores at the same index are equated.
#[test]
#[timeout(10_000)]
fn store_value_injectivity_same_index_6282() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
; Assert the two stores are equal
(assert (= (store a i v1) (store b i v2)))
; Assert v1 != v2 — this contradicts value injectivity
(assert (not (= v1 v2)))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).expect("expected sat/unsat/unknown output");
    assert_ne!(
        result, "sat",
        "store(A,i,v1) = store(B,i,v2) must imply v1 = v2 (value injectivity)",
    );
}

/// Store value injectivity: with arithmetic values to ensure the propagation
/// reaches the LIA solver through the Nelson-Oppen bridge.
///
/// Z3 solves `store(a,i,x) = store(b,i,x+1)` as unsat instantly via value
/// injectivity + LIA. AY currently times out — the value injectivity
/// propagation doesn't route arithmetic equalities through the N-O bridge
/// effectively. This test guards against false SAT (soundness) while allowing
/// unknown/timeout (incompleteness, tracked under #6282).
#[test]
fn store_value_injectivity_arith_values_6282() {
    use crate::common::SolverOutcome;

    let smt = r#"
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun x () Int)
(assert (= (store a i x) (store b i (+ x 1))))
(check-sat)
"#;
    let outcome =
        crate::common::run_executor_smt_with_timeout(smt, 5).expect("executor should not error");
    match outcome {
        SolverOutcome::Sat => {
            panic!("store(A,i,x) = store(B,i,x+1) is unsat by value injectivity + LIA");
        }
        SolverOutcome::Unsat | SolverOutcome::Unknown | SolverOutcome::Timeout => {
            // Unsat: correct. Unknown/Timeout: incompleteness, not unsoundness.
        }
        SolverOutcome::Error(e) => {
            panic!("unexpected error: {e}");
        }
    }
}

/// Store base decomposition: two stores at same index with X = Y forces A = B
/// when the Skolem diff point is not the stored index.
///
/// This tests the transitive decomposition path (Phase 2b of the axiom generator).
#[test]
#[timeout(10_000)]
fn store_base_decomposition_transitive_6282() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i () Int)
(declare-fun v () Int)
(declare-fun sk () Int)
; v0 = store(a1, i, v), v1 = store(a2, i, v)
(declare-fun v0 () (Array Int Int))
(declare-fun v1 () (Array Int Int))
(assert (= v0 (store a1 i v)))
(assert (= v1 (store a2 i v)))
; Assert v0 = v1 (the two stores are equal)
(assert (= v0 v1))
; Assert a1 != a2 via Skolem witness
(assert (not (= (select a1 sk) (select a2 sk))))
; Assert sk != i (so the store overwrite doesn't hide the difference)
(assert (not (= sk i)))
(check-sat)
"#;
    // If v0 = v1, then store(a1,i,v) = store(a2,i,v).
    // For any index j != i: select(store(a1,i,v), j) = a1[j] and
    //                        select(store(a2,i,v), j) = a2[j].
    // Since v0 = v1, a1[j] = a2[j] for all j != i.
    // Since sk != i, a1[sk] = a2[sk], contradicting the Skolem.
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).expect("expected sat/unsat/unknown output");
    assert_ne!(
        result, "sat",
        "base decomposition: store(a1,i,v) = store(a2,i,v) with sk != i must imply a1[sk] = a2[sk]",
    );
}

/// Mixed array sorts on the same store index must not generate cross-sort
/// decomposition equalities.
///
/// The model-checker-consumer harder array benchmark routes both `(Array Int Bool)` and
/// `(Array Int Int)` stores through the same symbolic index after BV-to-Int
/// abstraction. Before the sort guard in `add_store_store_base_decomposition_axioms`,
/// the transitive pair logic tried to build `(= xb yi)` and panicked.
#[test]
#[timeout(10_000)]
fn store_base_decomposition_skips_mixed_array_sorts_1753() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-fun ab () (Array Int Bool))
(declare-fun ai () (Array Int Int))
(declare-fun i () Int)
(declare-fun xb () (Array Int Bool))
(declare-fun yi () (Array Int Int))
(assert (= xb (store ab i true)))
(assert (= yi (store ai i 42)))
(check-sat)
"#;

    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).expect("expected sat/unsat/unknown output");
    assert_eq!(
        result, "sat",
        "mixed array sorts sharing a store index must not trigger cross-sort decomposition",
    );
}

/// Storeinv flat-form size 2: the simplest cross-swap pattern.
/// This is a known benchmark; including it here as a regression gate.
/// AY cannot yet solve this within 30s (deep store chain reasoning needed).
/// Uses manual timeout to guard soundness without failing on incompleteness.
#[test]
fn storeinv_sf_size2_soundness_6282() {
    use crate::common::SolverOutcome;

    let smt = r#"
(set-logic QF_AUFLIA)
(set-info :status unsat)
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
; Step 1: cross-swap at i1
(declare-fun v0 () (Array Int Int))
(declare-fun v1 () (Array Int Int))
(assert (= v0 (store a2 i1 (select a1 i1))))
(assert (= v1 (store a1 i1 (select a2 i1))))
; Step 2: assert equality of final cross-swap at i2
(assert (= (store v1 i2 (select v0 i2))
           (store v0 i2 (select v1 i2))))
; Assert a1 != a2 via Skolem
(assert (let ((?v_0 (sk a1 a2))) (not (= (select a1 ?v_0) (select a2 ?v_0)))))
(check-sat)
"#;
    let outcome =
        crate::common::run_executor_smt_with_timeout(smt, 30).expect("executor should not error");
    match outcome {
        SolverOutcome::Sat => {
            panic!("storeinv sf size 2 must not return false SAT");
        }
        SolverOutcome::Unsat | SolverOutcome::Unknown | SolverOutcome::Timeout => {
            // Unsat: correct. Unknown/Timeout: incompleteness, not unsoundness.
        }
        SolverOutcome::Error(e) => {
            panic!("unexpected error: {e}");
        }
    }
}

/// Direct store-store equality decomposition (Phase 2a of axiom generator).
///
/// When (= store(A,i,v1) store(B,j,v2)) appears directly (not via named
/// intermediaries), the decomposition axiom should still fire.
#[test]
#[timeout(10_000)]
fn direct_store_store_equality_decomposition_6282() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(declare-fun sk () Int)
; Direct store-store equality
(assert (= (store a i v1) (store b j v2)))
; a != b at Skolem point
(assert (not (= (select a sk) (select b sk))))
; Skolem is not at either stored index
(assert (not (= sk i)))
(assert (not (= sk j)))
(check-sat)
"#;
    // If store(a,i,v1) = store(b,j,v2), then for any k != i and k != j:
    //   select(store(a,i,v1), k) = a[k]
    //   select(store(b,j,v2), k) = b[k]
    // So a[k] = b[k] for all k not in {i,j}.
    // Since sk != i and sk != j, a[sk] = b[sk], contradicting the Skolem.
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).expect("expected sat/unsat/unknown output");
    assert_ne!(
        result, "sat",
        "direct store-store equality with distinct Skolem must be unsat",
    );
}

#[test]
fn storeinv_nf_size5_unsat_6282() {
    use crate::common::SolverOutcome;

    // 5-level nested store cross-swap. Z3 solves in <1s. AY now solves after
    // #6546 event-driven ROW axioms + #6820 lazy ROW2 final check.
    let smt = r#"
(set-logic QF_AUFLIA)
(set-info :status unsat)
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
(declare-fun i4 () Int)
(declare-fun i5 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (let ((?v_0 (store a2 i1 (select a1 i1)))
              (?v_1 (store a1 i1 (select a2 i1))))
          (let ((?v_2 (store ?v_0 i2 (select ?v_1 i2)))
                (?v_3 (store ?v_1 i2 (select ?v_0 i2))))
            (let ((?v_4 (store ?v_2 i3 (select ?v_3 i3)))
                  (?v_5 (store ?v_3 i3 (select ?v_2 i3))))
              (let ((?v_6 (store ?v_4 i4 (select ?v_5 i4)))
                    (?v_7 (store ?v_5 i4 (select ?v_4 i4))))
                (= (store ?v_7 i5 (select ?v_6 i5))
                   (store ?v_6 i5 (select ?v_7 i5))))))))
(assert (let ((?v_0 (sk a1 a2))) (not (= (select a1 ?v_0) (select a2 ?v_0)))))
(check-sat)
"#;
    let outcome =
        crate::common::run_executor_smt_with_timeout(smt, 10).expect("executor should not error");
    assert_eq!(
        outcome,
        SolverOutcome::Unsat,
        "storeinv nf size 5 must return unsat (was intractable before #6546/#6367 fixes)",
    );
}
