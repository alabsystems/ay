// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn source(comparison: &str) -> QuantifiedChcProblem {
    // Authored bounded integration, not a compiler-exported harness. Both
    // occurrences use the same original summary with different fill values.
    QuantifiedChcProblem::parse_smtlib(&format!(
        "(set-logic HORN)
         (declare-fun P ((Array (_ BitVec 1) Bool) Bool) Bool)
         (assert (forall ((a (Array (_ BitVec 1) Bool)) (f Bool))
           (=> (and (= a ((as const (Array (_ BitVec 1) Bool)) f))
                    (forall ((i (_ BitVec 1))) (= (select a i) f))) (P a f))))
         (assert (forall ((a (Array (_ BitVec 1) Bool)) (b (Array (_ BitVec 1) Bool)))
           (=> (and (P a true) (P b false)
                    ({comparison} (select a (_ bv0 1)) (select b (_ bv0 1)))) false)))
         (assert (=> false false))
         (check-sat)"
    ))
    .expect("two original quantified properties")
}

#[test]
fn branching_unsafe_row_keeps_complete_membership_and_original_tree_topology() {
    let problem = source("distinct");
    let token = CancellationToken::new();
    let report = solve_quantified_query_obligations_with_cancellation(
        &problem,
        Duration::from_secs(60),
        Some(128 * 1024 * 1024),
        &token,
    )
    .expect("bounded tree query batch");
    assert_eq!(report.verdict(), QuantifiedQueryBatchVerdict::Unsafe);
    assert_eq!(report.rows().len(), 2);
    assert_eq!(report.source_smtlib(), problem.source_smtlib());
    let first = &report.rows()[0];
    let QuantifiedQueryOutcome::CheckedUnsafe(evidence) = first.outcome() else {
        panic!("original branching query must have fresh checked SAT evidence");
    };
    assert_eq!(evidence.clause_indices(), &[0, 0, 1]);
    assert_eq!(evidence.premise_steps(), &[vec![], vec![], vec![0, 1]]);
    assert_eq!(evidence.replay_obligation().matches("(forall ").count(), 2);
    assert_eq!(evidence.source_smtlib(), first.problem().source_smtlib());
    assert_eq!(first.id().aggregate_source_sha256(), report.source_sha256());
    assert!(!evidence.recheck(&problem, Duration::from_secs(1), &token));
    assert!(report
        .rows()
        .iter()
        .all(|row| { row.id().aggregate_source_sha256() == report.source_sha256() }));
    assert!(!matches!(
        report.rows()[1].outcome(),
        QuantifiedQueryOutcome::CheckedUnsafe(_)
    ));
}

#[test]
fn a_false_branching_query_cannot_be_reported_as_unsafe() {
    let problem = source("=");
    let report = solve_quantified_query_obligations_with_cancellation(
        &problem,
        Duration::from_secs(30),
        Some(128 * 1024 * 1024),
        &CancellationToken::new(),
    )
    .expect("bounded false-tree batch");
    assert_ne!(report.verdict(), QuantifiedQueryBatchVerdict::Unsafe);
    assert_eq!(report.rows().len(), 2);
    assert!(report
        .rows()
        .iter()
        .all(|row| { !matches!(row.outcome(), QuantifiedQueryOutcome::CheckedUnsafe(_)) }));
}

#[test]
fn branching_row_exposes_complete_typed_trace_only_for_its_original_slice() {
    let problem = source("distinct");
    let token = CancellationToken::new();
    let report = solve_quantified_query_obligations_with_cancellation(
        &problem,
        Duration::from_secs(60),
        Some(128 * 1024 * 1024),
        &token,
    )
    .expect("complete quantified batch");
    assert_eq!(report.rows().len(), 2);
    let first = &report.rows()[0];
    let QuantifiedQueryOutcome::CheckedUnsafe(evidence) = first.outcome() else {
        panic!("checked first original row");
    };
    let trace = evidence
        .concrete_trace(first.problem(), Duration::from_secs(45), &token)
        .expect("all six branching locals decode and replay");
    assert_eq!(trace.bindings().len(), 6);
    assert_eq!(trace.source_smtlib(), first.problem().source_smtlib());
    assert_eq!(trace.clause_indices(), &[0, 0, 1]);
    assert_eq!(trace.premise_steps(), &[vec![], vec![], vec![0, 1]]);
    assert_eq!(trace.replay_obligation().matches("(forall ").count(), 2);
    assert!(trace.recheck(first.problem(), Duration::from_secs(45), &token));
    // The trace proves this property slice, never a different row or a batch
    // whose extra source clauses merely happen not to change the SAT answer.
    assert!(!trace.recheck(&problem, Duration::from_secs(1), &token));
    assert!(!trace.recheck(report.rows()[1].problem(), Duration::from_secs(1), &token));
    assert_eq!(first.id().aggregate_source_sha256(), report.source_sha256());
    assert_eq!(report.rows().len(), 2);
}
