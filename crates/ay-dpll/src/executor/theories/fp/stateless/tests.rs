// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use ay_fp::FpBuildStage;
use ay_frontend::parse;

use super::*;

mod decode;
mod retries;

fn setup(script: &str) -> Executor {
    let mut executor = Executor::new();
    executor.execute_all(&parse(script).unwrap()).unwrap();
    executor
}

fn simple() -> Executor {
    setup(
        "(set-logic QF_FP)
         (declare-const x (_ FloatingPoint 5 11))
         (assert (fp.isZero x))",
    )
}

fn assert_revoked(executor: &Executor, origin: UnknownOrigin) {
    assert_eq!(executor.unknown_origin(), Some(origin));
    assert!(matches!(executor.last_result, Some(SolveResult::Unknown)));
    assert!(executor.last_model.is_none());
    assert!(executor.last_proof.is_none());
    assert!(executor.last_sat_certificate.is_none());
    assert!(executor.last_unsat_certificate.is_none());
}

#[test]
fn actual_stateless_division_stops_inside_encoding_and_fresh_retry_can_solve() {
    let mut executor = setup(
        "(set-logic QF_FP)
         (declare-const x (_ FloatingPoint 5 11))
         (declare-const y (_ FloatingPoint 5 11))
         (assert (fp.isZero (fp.div RNE x y)))",
    );
    let roots = executor.ctx.assertions.clone();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));
    let rows = Cell::new(0);
    let clauses = Cell::new(0);
    let searched = Cell::new(false);
    let result = executor
        .solve_fp_stateless_observed(&|phase| match phase {
            FpPhase::Construction(progress) if progress.stage == FpBuildStage::DivideRow => {
                rows.set(rows.get() + 1);
                if rows.get() == 4 {
                    clauses.set(progress.clauses);
                    interrupt.store(true, Ordering::Relaxed);
                }
            }
            FpPhase::SatSearch => searched.set(true),
            _ => {}
        })
        .unwrap();
    assert!(result.is_unknown());
    assert_eq!(rows.get(), 4);
    assert!(clauses.get() > 0);
    assert!(!searched.get());
    assert_eq!(executor.ctx.assertions, roots);
    assert_revoked(&executor, UnknownOrigin::InterruptFlag);
    interrupt.store(false, Ordering::Relaxed);
    assert!(matches!(
        executor.solve_fp_stateless().unwrap(),
        SolveResult::Sat
    ));
    assert!(executor.last_model.is_some());
}

#[test]
fn clause_sat_and_publication_stops_revoke_earlier_models_and_never_resume() {
    for target in [
        FpPhase::ClauseTransfer,
        FpPhase::SatLoad,
        FpPhase::SatSearch,
        FpPhase::SatPoll,
        FpPhase::SatReturned,
        FpPhase::ModelExtracted,
        FpPhase::Publication,
    ] {
        let mut executor = simple();
        assert!(matches!(
            executor.solve_fp_stateless().unwrap(),
            SolveResult::Sat
        ));
        assert!(executor.last_model.is_some());
        let interrupt = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(Arc::clone(&interrupt));
        let calls = Cell::new(0);
        let boundary = if matches!(target, FpPhase::ClauseTransfer | FpPhase::SatLoad) {
            2 // At least one real clause has already reached SAT.
        } else {
            1
        };
        let result = executor
            .solve_fp_stateless_observed(&|phase| {
                if std::mem::discriminant(&phase) == std::mem::discriminant(&target) {
                    calls.set(calls.get() + 1);
                    if calls.get() == boundary {
                        interrupt.store(true, Ordering::Relaxed);
                    }
                }
            })
            .unwrap();
        assert!(result.is_unknown(), "{target:?}");
        assert!(calls.get() >= boundary, "{target:?}");
        assert_revoked(&executor, UnknownOrigin::InterruptFlag);
        interrupt.store(false, Ordering::Relaxed);
        assert!(executor.fp_recorded_resource_stop());
        assert!(matches!(
            executor.solve_fp_stateless().unwrap(),
            SolveResult::Sat
        ));
    }
}

#[test]
fn full_stateless_solver_keeps_foreign_fp_and_bv_congruence() {
    for sort in ["(_ FloatingPoint 5 11)", "(_ BitVec 8)"] {
        let mut executor = setup(&format!(
            "(declare-const x {sort})
             (declare-const y {sort})
             (declare-fun foreign ({sort}) Bool)
             (assert (= x y))
             (assert (foreign x))
             (assert (not (foreign y)))"
        ));
        let plan_polls = Cell::new(0);
        let result = executor
            .solve_fp_stateless_observed(&|phase| {
                if matches!(phase, FpPhase::CongruencePlan) {
                    plan_polls.set(plan_polls.get() + 1);
                }
            })
            .unwrap();
        assert!(plan_polls.get() > 2);
        assert!(result.is_unsat(), "{sort}: {result:?}");
    }
}

#[test]
fn congruence_only_gap_preserves_unsat_but_refuses_relaxed_sat() {
    let script = "(declare-const c Bool)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-fun opaque (Bool) Bool)
        (declare-fun foreign ((_ FloatingPoint 5 11)) Bool)
        (assert (foreign (ite (opaque c) x y)))
        (assert (foreign x))";
    for contradiction in [false, true] {
        let mut executor = setup(script);
        if contradiction {
            executor
                .execute_all(&parse("(assert (fp.isNaN x)) (assert (not (fp.isNaN x)))").unwrap())
                .unwrap();
        }
        let stop = FpStop::from_executor(&executor);
        let prepared = prepare::prepare(
            &executor.ctx.terms,
            &executor.ctx.assertions,
            &stop,
            &|_| {},
        )
        .unwrap_or_else(|_| panic!("this gap must be introduced only by congruence"));
        assert!(prepared.congruence_incomplete);
        assert!(prepared.encoding.has_encoding_gap);
        let result = executor.solve_fp_stateless().unwrap();
        assert_eq!(result.is_unsat(), contradiction);
        if !contradiction {
            assert!(result.is_unknown());
            assert_eq!(
                executor.last_unknown_reason,
                Some(UnknownReason::Incomplete)
            );
            assert!(!executor.fp_recorded_resource_stop());
        }
    }
}

#[test]
fn base_gap_stays_distinct_from_cancellation_and_congruence_relaxation() {
    let mut executor = setup(
        "(declare-const c Bool)
         (declare-const x (_ FloatingPoint 5 11))
         (declare-const y (_ FloatingPoint 5 11))
         (declare-fun opaque (Bool) Bool)
         (assert (fp.isZero (ite (opaque c) x y)))",
    );
    let stop = FpStop::from_executor(&executor);
    assert!(matches!(
        prepare::prepare(
            &executor.ctx.terms,
            &executor.ctx.assertions,
            &stop,
            &|_| {}
        ),
        Err(FpPreparationError::BaseGap)
    ));
    assert_eq!(stop.check(), Ok(()));
    assert!(executor.solve_fp_stateless().unwrap().is_unknown());
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
    assert!(!executor.fp_recorded_resource_stop());
}

#[test]
fn real_term_budget_rejection_uses_existing_public_revocation() {
    let mut executor = simple();
    assert!(matches!(
        executor.solve_fp_stateless().unwrap(),
        SolveResult::Sat
    ));
    executor.set_term_memory_limit(Some(0));
    let result = executor.solve_fp_stateless().unwrap();
    assert!(result.is_unknown());
    let _ = executor.finalize_unknown_publication(result);
    assert_revoked(&executor, UnknownOrigin::MemoryBudget);
}

#[test]
fn sat_resource_reason_handoff_replaces_an_earlier_incomplete_branch() {
    let mut executor = simple();
    executor.last_unknown_reason = Some(UnknownReason::Incomplete);
    let stop = FpStop::from_executor(&executor);
    // Exercise the exact production handoff with an explicit SAT result/reason.
    // This is not a claim that a zero-conflict allowance stops an easy formula:
    // BCP/lucky phases can legitimately decide one before a budgeted conflict.
    executor.capture_fp_sat_unknown(
        &SatResult::Unknown,
        Some(SatUnknownReason::ResourceBudget),
        &stop,
    );
    let origin = stop.check().unwrap_err();
    assert_eq!(origin, UnknownOrigin::DeterministicResourceBudget);
    assert!(executor.fp_stopped(origin).is_unknown());
    assert_revoked(&executor, UnknownOrigin::DeterministicResourceBudget);
    assert!(executor.fp_recorded_resource_stop());
}
