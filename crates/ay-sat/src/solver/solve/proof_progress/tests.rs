// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::proof::ProofOutput;
use crate::proof_manager::ProofManager;
use crate::solver::backward_proof::BackwardProofLimits;
use crate::solver::types::SatResult;
use crate::{Literal, Variable};
use std::cell::Cell;
use std::time::Duration;

mod routing;

fn bounded_empty_solver() -> Solver {
    let mut solver = Solver::with_proof_output(0, ProofOutput::lrat_binary(Vec::new(), 1));
    solver.set_bounded_in_memory_proof_posture();
    solver.set_backward_proof_limits(BackwardProofLimits {
        deadline: Some(ay_core::time::Instant::now() + Duration::from_secs(60)),
        max_steps: 100,
        max_literals: 100,
        max_hints: 100,
        max_bytes: 0,
    });
    solver.add_clause(vec![]);
    assert!(solver.cold.empty_clause_in_proof);
    solver
}

fn proof_bytes(mut solver: Solver) -> Vec<u8> {
    solver
        .take_proof_writer_without_artifact()
        .unwrap()
        .into_inner()
        .unwrap()
        .into_vec()
        .unwrap()
}

/// A unit falsified by a file-visible level-0 unit is an input-time terminal:
/// its refutation has a fixed two-hint chain, so the bounded posture emits it
/// at detection and the postsolve walk has nothing to reconstruct.
#[test]
fn complementary_units_emit_the_terminal_at_startup_and_reconstruct_nothing() {
    let mut solver = Solver::with_proof_output(1, ProofOutput::lrat_binary(Vec::new(), 2));
    solver.set_bounded_in_memory_proof_posture();
    // Every meter budget is zero: any reconstruction at all would fail, so
    // an UNSAT here proves the terminal was emitted before postsolve.
    solver.set_backward_proof_limits(BackwardProofLimits {
        deadline: Some(ay_core::time::Instant::now() + Duration::from_secs(60)),
        max_steps: 0,
        max_literals: 0,
        max_hints: 0,
        max_bytes: 0,
    });
    solver.set_preprocess_enabled(false);
    solver.disable_all_inprocessing();
    let x = Literal::positive(Variable(0));
    assert!(solver.add_clause(vec![x]));
    assert!(solver.add_clause(vec![x.negated()]));
    assert!(!solver.has_empty_clause);
    assert!(!solver.cold.empty_clause_in_proof);
    assert!(matches!(solver.init_solve(), Some(SatResult::Unsat(_))));
    assert!(solver.cold.empty_clause_in_proof);
    assert_eq!(solver.cold.empty_clause_lrat_id, Some(3));
    assert_eq!(solver.cold.backward_proof_failure, None);
    // Exactly one step reached the writer: the terminal itself, at detection.
    assert_eq!(
        solver.proof_manager.as_ref().map(ProofManager::added_count),
        Some(1)
    );
}

#[test]
fn refusal_is_latched_and_clears_terminal_markers_without_poisoning_legacy_noop() {
    let mut solver = bounded_empty_solver();
    let calls = Cell::new(0);
    assert!(!solver.poll_unsat_proof_progress(Some(&|| {
        calls.set(calls.get() + 1);
        false
    })));
    assert_eq!(calls.get(), 1);
    assert_eq!(
        solver.cold.backward_proof_failure,
        Some(BackwardProofFailure::Cancelled)
    );
    assert!(!solver.cold.empty_clause_in_proof);
    assert_eq!(solver.cold.empty_clause_lrat_id, None);
    assert!(!solver.poll_unsat_proof_progress(Some(&|| panic!("already refused"))));
    assert!(solver.poll_unsat_proof_progress(None));
    assert_eq!(
        solver.bounded_proof_unknown_reason(),
        SatUnknownReason::Interrupted
    );
}

#[test]
fn a_caught_callback_panic_cannot_revive_the_attempt() {
    let mut solver = bounded_empty_solver();
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.poll_unsat_proof_progress(Some(&|| panic!("proof callback")))
    }))
    .is_err());
    assert_eq!(
        solver.cold.backward_proof_failure,
        Some(BackwardProofFailure::Cancelled)
    );
    assert!(!solver.poll_unsat_proof_progress(Some(&|| panic!("must not retry"))));
    assert!(matches!(
        solver.declare_unsat_with_proof_progress(Some(&|| true)),
        SatResult::Unknown
    ));
}

#[test]
fn original_deadline_is_distinct_and_an_existing_failure_gets_no_new_callback() {
    let mut solver = bounded_empty_solver();
    solver.cold.backward_proof_limits.as_mut().unwrap().deadline =
        Some(ay_core::time::Instant::now());
    assert!(!solver.poll_unsat_proof_progress(Some(&|| panic!("deadline already reached"))));
    assert_eq!(
        solver.cold.backward_proof_failure,
        Some(BackwardProofFailure::Deadline)
    );
    assert_eq!(
        solver.bounded_proof_unknown_reason(),
        SatUnknownReason::ProofFinalizationFailure
    );
    assert!(!solver.poll_unsat_proof_progress(Some(&|| panic!("preserve reached error"))));
}

#[test]
fn arbitrary_interrupted_io_and_error_text_are_not_caller_cancellation() {
    let mut solver = bounded_empty_solver();
    for kind in [std::io::ErrorKind::Interrupted, std::io::ErrorKind::Other] {
        solver.record_bounded_emission_failure(&std::io::Error::new(
            kind,
            "bounded LRAT emission cancelled",
        ));
        assert_eq!(solver.cold.backward_proof_failure, None);
    }
    solver.record_bounded_emission_failure(&std::io::Error::new(
        std::io::ErrorKind::TimedOut,
        "deadline",
    ));
    assert_eq!(
        solver.cold.backward_proof_failure,
        Some(BackwardProofFailure::Deadline)
    );
}

#[test]
fn authenticated_empty_fast_path_keeps_legacy_bytes_and_refuses_every_finalizer_poll() {
    let mut legacy = bounded_empty_solver();
    assert!(matches!(legacy.declare_unsat(), SatResult::Unsat(_)));
    let expected = proof_bytes(legacy);
    let mut live = bounded_empty_solver();
    let total = Cell::new(0);
    assert!(matches!(
        live.declare_unsat_with_proof_progress(Some(&|| {
            total.set(total.get() + 1);
            true
        })),
        SatResult::Unsat(_)
    ));
    assert_eq!(proof_bytes(live), expected);
    assert!(total.get() >= 2);
    for stop in 1..=total.get() {
        let mut solver = bounded_empty_solver();
        let calls = Cell::new(0);
        assert!(matches!(
            solver.declare_unsat_with_proof_progress(Some(&|| {
                calls.set(calls.get() + 1);
                calls.get() != stop
            })),
            SatResult::Unknown
        ));
        assert_eq!(calls.get(), stop);
        assert_eq!(
            solver.cold.backward_proof_failure,
            Some(BackwardProofFailure::Cancelled)
        );
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::Interrupted)
        );
        assert!(!solver.cold.empty_clause_in_proof);
        assert_eq!(solver.cold.empty_clause_lrat_id, None);
    }
}

#[test]
fn existing_unsat_poison_precedes_new_proof_polls() {
    let mut solver = bounded_empty_solver();
    solver.cold.oversized_clause_poison = true;
    assert!(matches!(
        solver.declare_unsat_with_proof_progress(Some(&|| panic!("poison already rejected"))),
        SatResult::Unknown
    ));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::Unspecified)
    );
    assert_eq!(solver.cold.backward_proof_failure, None);
}

#[test]
fn private_entry_refuses_scoped_or_unbounded_routes_without_dropping_control() {
    let mut unbounded = Solver::new(0);
    let mut scoped = bounded_empty_solver();
    scoped.push();
    for solver in [&mut unbounded, &mut scoped] {
        assert!(solver
            .solve_interruptible_without_artifact_with_proof_progress(
                || panic!("unsupported route must not solve"),
                &|| panic!("unsupported route must not finalize"),
            )
            .is_unknown());
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::UnsupportedConfig)
        );
    }
}

#[test]
fn controlled_noartifact_entry_preserves_the_legacy_none_lane() {
    let mut legacy = bounded_empty_solver();
    assert!(legacy
        .solve_interruptible_without_artifact(|| false)
        .is_unsat());
    let expected = proof_bytes(legacy);
    let mut live = bounded_empty_solver();
    let calls = Cell::new(0);
    assert!(live
        .solve_interruptible_without_artifact_with_proof_progress(|| false, &|| {
            calls.set(calls.get() + 1);
            true
        })
        .is_unsat());
    assert!(calls.get() > 0);
    assert_eq!(proof_bytes(live), expected);
    let mut cancelled = bounded_empty_solver();
    assert!(cancelled
        .solve_interruptible_without_artifact_with_proof_progress(|| false, &|| false,)
        .is_unknown());
    assert_eq!(
        cancelled.cold.backward_proof_failure,
        Some(BackwardProofFailure::Cancelled)
    );
}
