// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn nested_resize() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(
        "(declare-datatype Vec ((mkVec (ptr (_ BitVec 64)) (len (_ BitVec 64))
           (cap (_ BitVec 64)) (data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-datatype Wrapper ((mkWrapper (items Vec) (tag Bool))))
         (declare-var v Wrapper)(declare-var w Wrapper)
         (declare-var b (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-var old (_ BitVec 64))(declare-var new (_ BitVec 64))
         (declare-var fill (_ BitVec 8))(declare-var j (_ BitVec 64))
         (declare-rel P (Wrapper (_ BitVec 64) (_ BitVec 8)))
         (declare-rel error ())
         (rule (=> (and (= old (len (items v))) (bvult old new)
           (= w (mkWrapper (mkVec (ptr (items v)) new (cap (items v)) b) (tag v)))
           (forall ((i (_ BitVec 64)))
             (and (=> (bvult i old) (= (select (data (items w)) i) (select (data (items v)) i)))
               (=> (and (bvuge i old) (bvult i new)) (= (select (data (items w)) i) fill)))))
           (P w old fill)))
         (rule (=> (and (P w old fill) (bvuge j old) (bvult j (len (items w)))
           (bvuge j (_ bv32 64)) (not (= (select (data (items w)) j) fill))) error))
         (query error)",
    )
    .expect("nested original resize source")
}

#[test]
fn nested_symbolic_resize_batch_keeps_original_quantified_replay() {
    // Native solver integration, not the scheduler's injected runner. The
    // same 60-second total allowance includes decomposition and fresh replay.
    let problem = nested_resize();
    let token = CancellationToken::new();
    let report = solve_quantified_query_obligations_with_cancellation(
        &problem,
        Duration::from_secs(60),
        Some(128 * 1024 * 1024),
        &token,
    )
    .expect("bounded quantified batch");
    assert_eq!(report.verdict(), QuantifiedQueryBatchVerdict::Safe);
    assert_eq!(report.source_smtlib(), problem.source_smtlib());
    assert_eq!(report.source_sha256(), problem.source_sha256());
    let [row] = report.rows() else {
        panic!("one original property")
    };
    let QuantifiedQueryOutcome::CheckedSafe(evidence) = row.outcome() else {
        panic!("freshly rechecked original-source safety")
    };
    assert_eq!(evidence.source_smtlib(), row.problem().source_smtlib());
    assert_eq!(row.id().aggregate_source_sha256(), report.source_sha256());
    assert!(evidence.replay_obligations().iter().any(|obligation| {
        obligation.smtlib.contains("(declare-datatypes")
            && obligation.smtlib.contains("(forall")
            && obligation.smtlib.contains("((as items Vec)")
            && obligation.smtlib.contains("bvult")
    }));
    assert!(
        !evidence.recheck(&problem, Duration::from_secs(1), &token),
        "a slice certificate must not become aggregate-source evidence"
    );
}

#[test]
fn original_quantified_counterexample_batch_requires_fresh_full_path_sat() {
    // Both finite BV1 array cells satisfy the original premise. The query is
    // deliberately reachable, not a counterexample to a finite weakening.
    let problem = QuantifiedChcProblem::parse_smtlib(
        "(declare-var a (Array (_ BitVec 1) Bool))
         (declare-rel P ((Array (_ BitVec 1) Bool)))
         (declare-rel error ())
         (rule (=> (forall ((i (_ BitVec 1))) (select a i)) (P a)))
         (rule (=> (and (P a) (select a (_ bv0 1))) error))
         (query error)",
    )
    .expect("reachable original quantified query");
    let token = CancellationToken::new();
    let report = solve_quantified_query_obligations_with_cancellation(
        &problem,
        Duration::from_secs(60),
        Some(128 * 1024 * 1024),
        &token,
    )
    .expect("bounded source counterexample batch");
    assert_eq!(report.verdict(), QuantifiedQueryBatchVerdict::Unsafe);
    let [row] = report.rows() else {
        panic!("one complete original property row")
    };
    let QuantifiedQueryOutcome::CheckedUnsafe(evidence) = row.outcome() else {
        panic!("freshly rechecked original-source SAT path")
    };
    assert_eq!(evidence.source_smtlib(), row.problem().source_smtlib());
    assert_eq!(row.id().aggregate_source_sha256(), report.source_sha256());
    assert!(!evidence.clause_indices().is_empty());
    assert!(evidence.replay_obligation().contains("(forall"));
    assert!(!evidence.recheck(&problem, Duration::from_secs(1), &token));
}
