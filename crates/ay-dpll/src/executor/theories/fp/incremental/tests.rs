// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use ay_fp::FpBuildStage;
use ay_frontend::parse;

use super::*;

mod decode;
mod lifecycle;
mod publication;

fn setup(body: &str) -> Executor {
    let mut executor = Executor::new();
    executor
        .execute_all(
            &parse(&format!(
                "(set-logic QF_FP)
         (declare-const x (_ FloatingPoint 5 11))
         (declare-const y (_ FloatingPoint 5 11))
         (declare-const b Bool)
         {body}
         (push 1)"
            ))
            .unwrap(),
        )
        .unwrap();
    assert_eq!(executor.incr_fp_state.as_ref().unwrap().scope_depth, 1);
    executor
}

fn simple() -> Executor {
    setup("(assert (fp.isZero x))")
}

fn shell(executor: &Executor, depth: usize) {
    let state = executor.incr_fp_state.as_ref().unwrap();
    assert_eq!(state.scope_depth, depth);
    assert_eq!(state.pending_pushes, depth);
    assert!(
        !state.disabled,
        "resource refusal must not permanently disable reuse"
    );
    assert!(state.persistent_sat.is_none());
    assert!(state.encoded_assertions.is_empty());
    assert!(state.assertion_activation_scope.is_empty());
    assert!(state.linked_predicate_vars.is_empty());
    assert!(state.linked_bool_inputs.is_empty());
    assert!(state.fp_cache.term_to_fp.is_empty());
    assert_eq!(state.fp_var_offset, None);
    assert_eq!(state.solves, 0);
}

fn revoked(executor: &Executor, origin: UnknownOrigin) {
    assert_eq!(executor.unknown_origin(), Some(origin));
    assert!(matches!(executor.last_result, Some(SolveResult::Unknown)));
    assert!(executor.last_model.is_none());
    assert!(!executor.last_model_validated);
    assert!(executor.last_proof.is_none());
    assert!(executor.last_sat_certificate.is_none());
    assert!(executor.last_unsat_certificate.is_none());
    assert!(executor.last_assumption_core.is_none());
}

fn rebuild(executor: &mut Executor) -> SolveResult {
    // A cancelled trial left no reuse proof. The next call records the full
    // set and declines; only the identical following set may be admitted.
    assert!(executor.try_solve_fp_incremental().unwrap().is_none());
    let result = executor.try_solve_fp_incremental().unwrap().unwrap();
    assert!(executor
        .incr_fp_state
        .as_ref()
        .unwrap()
        .persistent_sat
        .is_some());
    result
}

#[test]
fn actual_incremental_division_stops_inside_rows_without_retaining_partial_cache() {
    let mut executor = setup("(assert (fp.isZero (fp.div RNE x y)))");
    let roots = executor.ctx.assertions.clone();
    let flag = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&flag));
    let rows = Cell::new(0);
    let clauses = Cell::new(0);
    let searched = Cell::new(false);
    let result = executor
        .try_solve_fp_incremental_observed(&|phase| match phase {
            IncrementalFpPhase::Construction(progress)
                if progress.stage == FpBuildStage::DivideRow =>
            {
                rows.set(rows.get() + 1);
                if rows.get() == 4 {
                    clauses.set(progress.clauses);
                    flag.store(true, Ordering::Relaxed);
                }
            }
            IncrementalFpPhase::SatSearch => searched.set(true),
            _ => {}
        })
        .unwrap();
    assert!(matches!(result, Some(SolveResult::Unknown)));
    assert_eq!(rows.get(), 4);
    assert!(clauses.get() > 0);
    assert!(!searched.get());
    assert_eq!(executor.ctx.assertions, roots);
    shell(&executor, 1);
    revoked(&executor, UnknownOrigin::InterruptFlag);
    flag.store(false, Ordering::Relaxed);
    assert!(matches!(rebuild(&mut executor), SolveResult::Sat));
}

#[test]
fn every_persistent_boundary_drops_the_trial_and_revokes_older_model() {
    for target in [
        IncrementalFpPhase::Admission,
        IncrementalFpPhase::ForeignScan,
        IncrementalFpPhase::Provenance,
        IncrementalFpPhase::Tseitin,
        IncrementalFpPhase::Namespace,
        IncrementalFpPhase::SatAllocation,
        IncrementalFpPhase::GlobalDefinition,
        IncrementalFpPhase::GlobalFpClause,
        IncrementalFpPhase::PredicateLink,
        IncrementalFpPhase::Activation,
        IncrementalFpPhase::SatSearch,
        IncrementalFpPhase::SatPoll,
        IncrementalFpPhase::SatReturned,
        IncrementalFpPhase::ModelExtracted,
        IncrementalFpPhase::Publication,
        IncrementalFpPhase::Commit,
    ] {
        // Naming the conjunction creates genuine Tseitin definitions as well
        // as multiple FP/global-link clauses and scoped root activations.
        let mut executor = setup("(assert (and (fp.isZero x) (fp.isZero y)))");
        assert!(matches!(
            executor.solve_fp_stateless().unwrap(),
            SolveResult::Sat
        ));
        let flag = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(Arc::clone(&flag));
        let visits = Cell::new(0);
        let cutoff = if matches!(
            target,
            IncrementalFpPhase::GlobalFpClause | IncrementalFpPhase::PredicateLink
        ) {
            2
        } else {
            1
        };
        let result = executor
            .try_solve_fp_incremental_observed(&|phase| {
                if std::mem::discriminant(&phase) == std::mem::discriminant(&target) {
                    visits.set(visits.get() + 1);
                    if visits.get() == cutoff {
                        flag.store(true, Ordering::Relaxed);
                    }
                }
            })
            .unwrap();
        assert_eq!(visits.get(), cutoff, "{target:?} must actually be reached");
        assert!(matches!(result, Some(SolveResult::Unknown)), "{target:?}");
        shell(&executor, 1);
        revoked(&executor, UnknownOrigin::InterruptFlag);
        flag.store(false, Ordering::Relaxed);
        assert!(
            matches!(rebuild(&mut executor), SolveResult::Sat),
            "{target:?}"
        );
    }
}

#[test]
fn reset_before_outer_commit_cannot_revive_the_interrupted_trial() {
    let mut executor = simple();
    let flag = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&flag));
    let polls = Cell::new(0);
    let commits = Cell::new(0);
    let result = executor
        .try_solve_fp_incremental_observed(&|phase| match phase {
            IncrementalFpPhase::SatPoll => {
                polls.set(polls.get() + 1);
                flag.store(true, Ordering::Relaxed);
            }
            IncrementalFpPhase::Commit => {
                commits.set(commits.get() + 1);
                flag.store(false, Ordering::Relaxed);
            }
            _ => {}
        })
        .unwrap();
    assert!(polls.get() > 0);
    assert_eq!(commits.get(), 1);
    assert!(!flag.load(Ordering::Relaxed));
    assert!(matches!(result, Some(SolveResult::Unknown)));
    shell(&executor, 1);
    revoked(&executor, UnknownOrigin::InterruptFlag);
    assert!(matches!(rebuild(&mut executor), SolveResult::Sat));
}

#[test]
fn caught_transfer_unwind_leaves_only_the_same_scope_rebuild_shell() {
    let mut executor = simple();
    let clauses = Cell::new(0);
    let panic = catch_unwind(AssertUnwindSafe(|| {
        executor.try_solve_fp_incremental_observed(&|phase| {
            if matches!(phase, IncrementalFpPhase::GlobalFpClause) {
                clauses.set(clauses.get() + 1);
                if clauses.get() == 2 {
                    panic!("intentional partial-transfer unwind");
                }
            }
        })
    }));
    assert!(panic.is_err());
    assert_eq!(
        clauses.get(),
        2,
        "one actual global clause preceded the unwind"
    );
    shell(&executor, 1);
    // This private catch tests ownership, not the public panic-publication gate.
    assert!(matches!(rebuild(&mut executor), SolveResult::Sat));
}

#[test]
fn successful_reuse_keeps_the_frozen_namespace_and_does_not_reencode_cached_predicates() {
    let mut executor = simple();
    assert!(matches!(
        executor.try_solve_fp_incremental().unwrap(),
        Some(SolveResult::Sat)
    ));
    let state = executor.incr_fp_state.as_ref().unwrap();
    let frontier = (
        state.fp_var_offset,
        state.next_fp_var,
        state.tseitin_state.next_var,
        state.persistent_sat.as_ref().unwrap().total_num_vars(),
    );
    let new_circuits = Cell::new(0);
    let result = executor
        .try_solve_fp_incremental_observed(&|phase| {
            if matches!(phase, IncrementalFpPhase::GlobalFpClause) {
                new_circuits.set(new_circuits.get() + 1);
            }
        })
        .unwrap();
    assert!(matches!(result, Some(SolveResult::Sat)));
    assert_eq!(new_circuits.get(), 0);
    let state = executor.incr_fp_state.as_ref().unwrap();
    assert_eq!(state.solves, 2);
    assert_eq!(
        (
            state.fp_var_offset,
            state.next_fp_var,
            state.tseitin_state.next_var,
            state.persistent_sat.as_ref().unwrap().total_num_vars()
        ),
        frontier
    );
}

#[test]
fn push_namespace_refusal_is_delivered_before_admission_and_does_not_disable_the_session() {
    let mut executor = simple();
    executor.incr_fp_state.as_mut().unwrap().fp_cache.next_var = u32::MAX;
    executor.execute_all(&parse("(push 1)").unwrap()).unwrap();
    let observed = Cell::new(false);
    let result = executor
        .try_solve_fp_incremental_observed(&|_| observed.set(true))
        .unwrap();
    assert!(matches!(result, Some(SolveResult::Unknown)));
    assert!(
        !observed.get(),
        "pending push refusal precedes trial/admission work"
    );
    shell(&executor, 2);
    revoked(&executor, UnknownOrigin::DeterministicResourceBudget);
    assert!(matches!(rebuild(&mut executor), SolveResult::Sat));
}
