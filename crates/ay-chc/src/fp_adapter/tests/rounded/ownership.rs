// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

#[test]
fn rounded_work_and_storage_one_short_stay_terminal_before_native_entry() {
    let end = Instant::now() + Duration::from_secs(20);
    for name in ["fp.sqrt", "fp.fma"] {
        let (terms, root) = support::simple(name);
        let mut poll = || {
            if Instant::now() >= end {
                ControlFlow::Break(StopReason::Deadline)
            } else {
                ControlFlow::Continue(())
            }
        };
        let mut original = WorkBudget::new(10_000_000_000, &mut poll);
        let plan = source::plan(&terms, &[root], &[], &mut original).unwrap();
        drop(original);
        let mut short = WorkBudget::new((plan.gates * 1024 - 1) as u64, &mut poll);
        assert!(matches!(
            plan.prepay(&mut short),
            Err(FpAdapterError::Owner(QueryError::Exhausted))
        ));
        assert_eq!(short.charge(0), Err(QueryError::Exhausted));
        drop(short);
        let (permit, left) = (Cell::new(false), Cell::new(plan.gates * 4096 - 1));
        let mut storage = |_, bytes| {
            if Instant::now() >= end {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
            if permit.get() {
                return Ok(());
            }
            left.set(left.get().checked_sub(bytes).ok_or(QueryError::Exhausted)?);
            Ok(())
        };
        let mut short = WorkBudget::with_admission(10_000_000_000, &mut storage);
        assert!(matches!(
            plan.prepay(&mut short),
            Err(FpAdapterError::Owner(QueryError::Exhausted))
        ));
        permit.set(true);
        assert_eq!(short.charge(0), Err(QueryError::Exhausted));
    }
    assert!(Instant::now() < end);
}

#[test]
fn rounded_original_raw_callback_and_expired_deadline_cannot_be_reset() {
    for name in ["fp.sqrt", "fp.fma"] {
        let (terms, root) = support::simple(name);
        let original = Arc::new(AtomicBool::new(true));
        let held = Arc::clone(&original);
        let end = Instant::now() + Duration::from_secs(20);
        let mut stop = || {
            if held.load(Ordering::Relaxed) {
                ControlFlow::Break(StopReason::Cancelled)
            } else if Instant::now() >= end {
                ControlFlow::Break(StopReason::Deadline)
            } else {
                ControlFlow::Continue(())
            }
        };
        let mut budget = WorkBudget::new(10_000_000_000, &mut stop);
        let namespace = ChcProblem::new();
        assert!(matches!(
            lower_fp_clause(&terms, &[root], &[], &namespace, &mut budget),
            Err(FpAdapterError::Owner(QueryError::Interrupted(
                StopReason::Cancelled
            )))
        ));
        original.store(false, Ordering::Relaxed);
        assert_eq!(
            budget.charge(0),
            Err(QueryError::Interrupted(StopReason::Cancelled))
        );
        let end = Instant::now() - Duration::from_secs(1);
        let mut stop = || {
            if Instant::now() >= end {
                ControlFlow::Break(StopReason::Deadline)
            } else {
                ControlFlow::Continue(())
            }
        };
        let mut budget = WorkBudget::new(10_000_000_000, &mut stop);
        assert!(matches!(
            lower_fp_clause(&terms, &[root], &[], &namespace, &mut budget),
            Err(FpAdapterError::Owner(QueryError::Interrupted(
                StopReason::Deadline
            )))
        ));
        assert_eq!(
            budget.charge(0),
            Err(QueryError::Interrupted(StopReason::Deadline))
        );
    }
}

#[test]
fn authentic_free_rounded_inputs_share_native_progress_refusal_and_finish_latch() {
    let end = Instant::now() + Duration::from_secs(20);
    for name in ["fp.sqrt", "fp.fma"] {
        let (terms, root, sources, targets) = support::free(name);
        let inputs = [
            FpInputBinding {
                source: sources[0],
                target: &targets[0],
            },
            FpInputBinding {
                source: sources[1],
                target: &targets[1],
            },
            FpInputBinding {
                source: sources[2],
                target: &targets[2],
            },
        ];
        let cancelled = Cell::new(false);
        let mut owner = || {
            if Instant::now() >= end {
                ControlFlow::Break(StopReason::Deadline)
            } else if cancelled.get() {
                ControlFlow::Break(StopReason::Cancelled)
            } else {
                ControlFlow::Continue(())
            }
        };
        let mut budget = WorkBudget::new(10_000_000_000, &mut owner);
        let plan = source::plan(&terms, &[root], &inputs, &mut budget).unwrap();
        plan.prepay(&mut budget).unwrap();
        let (previous, advances) = (Cell::new((0, 0)), Cell::new(0));
        let stage = if name == "fp.fma" {
            ay_fp::FpBuildStage::MultiplyRow
        } else {
            ay_fp::FpBuildStage::Operation
        };
        let mut poll = |p: ay_fp::FpBuildProgress| {
            if p.stage == stage {
                let old = previous.get();
                if p.variables > old.0 && p.clauses > old.1 {
                    advances.set(advances.get() + 1);
                    if advances.get() == 2 {
                        cancelled.set(true);
                    }
                }
                previous.set((p.variables, p.clauses));
            }
            budget.charge(0).is_err()
        };
        let mut attempt =
            ay_fp::FpConstruction::new(ay_fp::FpSolver::new(&terms), &mut poll).unwrap();
        assert!(matches!(
            attempt.try_encode_bool_condition(root),
            Err(ay_fp::FpBuildError::Interrupted)
        ));
        assert_eq!(advances.get(), 2);
        cancelled.set(false);
        assert!(matches!(
            attempt.try_encode_bool_condition(root),
            Err(ay_fp::FpBuildError::Interrupted)
        ));
        assert!(matches!(
            attempt.finish(),
            Err(ay_fp::FpBuildError::Interrupted)
        ));
        drop(poll);
        assert_eq!(
            budget.charge(0),
            Err(QueryError::Interrupted(StopReason::Cancelled))
        );
    }
}

fn adapter_final(terms: &TermStore, root: TermId, end: Instant) {
    let namespace = ChcProblem::new();
    let calls = Cell::new(0);
    let mut count = || {
        calls.set(calls.get() + 1);
        if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut calibration = WorkBudget::new(10_000_000_000, &mut count);
    assert!(lower_fp_clause(terms, &[root], &[], &namespace, &mut calibration).is_ok());
    let last = calls.get();
    drop(calibration);
    let (calls, released) = (Cell::new(0), Cell::new(false));
    let mut owner = || {
        calls.set(calls.get() + 1);
        if (!released.get() && calls.get() == last) || Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut original = WorkBudget::new(10_000_000_000, &mut owner);
    assert!(matches!(
        lower_fp_clause(terms, &[root], &[], &namespace, &mut original),
        Err(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Deadline
        )))
    ));
    released.set(true);
    assert_eq!(
        original.charge(0),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
}

#[test]
fn rounded_final_drop_and_complete_adapter_fence_never_return_data_after_refusal() {
    let end = Instant::now() + Duration::from_secs(20);
    for name in ["fp.sqrt", "fp.fma"] {
        let (terms, root) = support::simple(name);
        let (stopped, finals) = (Cell::new(false), Cell::new(0));
        let mut owner = || {
            if Instant::now() >= end {
                ControlFlow::Break(StopReason::Deadline)
            } else if stopped.get() {
                ControlFlow::Break(StopReason::Cancelled)
            } else {
                ControlFlow::Continue(())
            }
        };
        let mut budget = WorkBudget::new(10_000_000_000, &mut owner);
        let plan = source::plan(&terms, &[root], &[], &mut budget).unwrap();
        plan.prepay(&mut budget).unwrap();
        let mut poll = |p: ay_fp::FpBuildProgress| {
            if p.stage == ay_fp::FpBuildStage::Finalize {
                finals.set(finals.get() + 1);
                if finals.get() == 2 {
                    stopped.set(true);
                }
            }
            budget.charge(0).is_err()
        };
        let mut attempt =
            ay_fp::FpConstruction::new(ay_fp::FpSolver::new(&terms), &mut poll).unwrap();
        assert!(attempt.try_encode_bool_condition(root).is_ok());
        assert!(matches!(
            attempt.finish(),
            Err(ay_fp::FpBuildError::Interrupted)
        ));
        assert_eq!(finals.get(), 2);
        stopped.set(false);
        drop(poll);
        assert_eq!(
            budget.charge(0),
            Err(QueryError::Interrupted(StopReason::Cancelled))
        );
        drop(budget);
        adapter_final(&terms, root, end);
    }
}

#[test]
fn rounded_full_enum_layout_and_transfer_price_are_not_bool_variant_estimates() {
    assert!(std::mem::size_of::<usize>() <= 8);
    assert!(std::mem::size_of::<ChcExpr>() <= 128);
    assert!(std::mem::size_of::<ChcVar>() <= 64);
    assert!(std::mem::size_of::<ay_fp::FpDecomposed>() <= 128);
    assert!(std::mem::size_of::<TermId>() <= 8);
    assert!(std::mem::size_of::<ay_core::CnfClause>() <= 32);
    for (native, scratch) in [(68_853usize, 59_686usize), (86_456, 79_758)] {
        let bytes = 8192 * native + 80 * scratch + 67_108_864 + 4096;
        let work = 20 * scratch + 576 * native + 16_777_216;
        assert!(bytes < 262_144 * 4096);
        assert!(work < 262_144 * 1024);
    }
}
