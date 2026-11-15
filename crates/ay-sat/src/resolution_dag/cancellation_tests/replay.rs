// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

fn fixture() -> ResolutionDag {
    ResolutionDag {
        num_vars: 2,
        original_clauses: vec![
            (1, vec![positive(0), positive(1)]),
            (2, vec![negative(0)]),
            (3, vec![negative(1)]),
        ],
        derived: vec![RupStep {
            id: 4,
            clause: vec![],
            rup_hints: vec![1, 2, 3],
        }],
        empty_clause_id: 4,
    }
}

#[test]
fn independent_fixpoint_replay_uses_same_terminal_cancellation() {
    let limits = limits();
    let dag = fixture();
    assert_eq!(dag.validate_with_limits(&limits.validation), Ok(()));
    every_poll(|control| validate_dag_controlled(&dag, &limits, control));
    let mut mutated = dag.clone();
    mutated.derived[0].rup_hints = vec![u64::MAX];
    let expected = ResolutionProofError::Validation(ResolutionValidationError::Invalid(
        crate::ResolutionDagValidateError::UnknownHint {
            step: 4,
            hint: u64::MAX,
        },
    ));
    every_poll(|control| validate_dag_controlled(&mutated, &limits, control));
    assert_eq!(
        validate_dag_controlled(&mutated, &limits, &ProofControl::new(&mut || true)),
        Err(expected)
    );
    assert_eq!(dag, fixture(), "cancellation never mutates the input DAG");
}

#[test]
fn independent_replay_keeps_existing_work_bytes_and_earliest_deadline() {
    let dag = fixture();
    let mut limits = limits();
    limits.validation.deadline = Some(Instant::now());
    assert_eq!(
        validate_dag_controlled(&dag, &limits, &ProofControl::new(&mut || true)),
        Err(ResolutionProofError::DeadlineExceeded {
            phase: ResolutionProofPhase::Validate
        })
    );
    limits.validation.deadline = None;
    limits.validation.max_work = 0;
    let expected = dag.validate_with_limits(&limits.validation).unwrap_err();
    assert_eq!(
        validate_dag_controlled(&dag, &limits, &ProofControl::new(&mut || true)),
        Err(ResolutionProofError::Validation(expected))
    );
    limits.validation.max_work = u64::MAX;
    limits.validation.max_bytes = 0;
    let expected = dag.validate_with_limits(&limits.validation).unwrap_err();
    assert_eq!(
        validate_dag_controlled(&dag, &limits, &ProofControl::new(&mut || true)),
        Err(ResolutionProofError::Validation(expected))
    );
}

#[test]
fn final_admission_keeps_the_original_phase_deadline_after_callback_work() {
    let mut limits = limits();
    limits.validation.deadline = Some(Instant::now());
    assert_eq!(
        admit_controlled_outcome(Ok(ResolutionSolveOutcome::Unsat(fixture())), &limits),
        Err(ResolutionProofError::DeadlineExceeded {
            phase: ResolutionProofPhase::Validate
        }),
    );
    // A validation-only deadline must not reclassify an already checked SAT
    // model, or replace an ordinary malformed-proof error while still live.
    assert_eq!(
        admit_controlled_outcome(Ok(ResolutionSolveOutcome::Sat(vec![true])), &limits),
        Ok(ResolutionSolveOutcome::Sat(vec![true]))
    );
    assert_eq!(
        admit_controlled_outcome(Err(ResolutionProofError::NoEmptyClause), &limits),
        Err(ResolutionProofError::NoEmptyClause)
    );
    limits.deadline = Some(Instant::now());
    assert_eq!(
        admit_controlled_outcome(Ok(ResolutionSolveOutcome::Sat(vec![true])), &limits),
        Err(ResolutionProofError::DeadlineExceeded {
            phase: ResolutionProofPhase::Solve
        })
    );
    assert_eq!(
        admit_controlled_outcome(Err(ResolutionProofError::Cancelled), &limits),
        Err(ResolutionProofError::Cancelled)
    );
}

#[test]
fn reached_independent_replay_error_has_no_new_callback() {
    let limits = limits();
    let mut dag = fixture();
    dag.derived[0].rup_hints = vec![u64::MAX];
    let mut reached = 0;
    let expected = dag
        .validate_with_limits_interruptible(&limits.validation, &[], 0, 0, &mut || {
            reached += 1;
            false
        })
        .unwrap_err();
    let mut calls = 0;
    let mut progress = || {
        calls += 1;
        calls <= reached
    };
    let control = ProofControl::new(&mut progress);
    assert_eq!(
        validate_dag_controlled(&dag, &limits, &control),
        Err(ResolutionProofError::Validation(expected))
    );
    drop(control);
    assert_eq!(calls, reached);
}
