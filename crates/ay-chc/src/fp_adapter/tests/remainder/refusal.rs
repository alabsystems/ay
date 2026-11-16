// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn error(terms: &TermStore, root: TermId, budget: &mut WorkBudget<'_>) -> FpAdapterError {
    let namespace = ChcProblem::new();
    match lower_fp_clause(terms, &[root], &[], &namespace, budget) {
        Ok(_) => panic!("whole unsupported source must refuse"),
        Err(error) => error,
    }
}

fn constant(terms: &mut TermStore) -> TermId {
    let x = fp_constant(terms, 0x3f800000, 32);
    let y = fp_constant(terms, 0x40400000, 32);
    let result = rem(terms, x, y, 32);
    predicate(terms, "fp.isNormal", &[result])
}

#[test]
fn remainder_rejects_rounding_operand_wrong_arity_mixed_formats_and_dead_children() {
    with_owner(1, |budget| {
        let mut terms = TermStore::new();
        let x = fp_constant(&mut terms, 0, 32);
        let y = fp_constant(&mut terms, 0, 64);
        let rm = terms.mk_app(
            Symbol::named("RNE"),
            [],
            Sort::Uninterpreted("RoundingMode".into()),
        );
        for args in [
            vec![],
            vec![x],
            vec![rm, x, x],
            vec![x, y],
            vec![x, TermId(999)],
        ] {
            let actual = terms.mk_app(Symbol::named("fp.rem"), args, Sort::FloatingPoint(8, 24));
            let root = predicate(&mut terms, "fp.isZero", &[actual]);
            assert!(matches!(
                error(&terms, root, budget),
                FpAdapterError::Invalid(_) | FpAdapterError::Unsupported(_)
            ));
        }
        let indexed = terms.mk_app(
            Symbol::indexed("fp.rem", vec![8, 24]),
            [x, x],
            Sort::FloatingPoint(8, 24),
        );
        let root = predicate(&mut terms, "fp.isZero", &[indexed]);
        assert!(matches!(
            error(&terms, root, budget),
            FpAdapterError::Unsupported(_)
        ));
    });
}

#[test]
fn full_nested_unsupported_operands_refuse_even_inside_unchosen_remainder_arms() {
    with_owner(1, |budget| {
        for form in [IteForm::Direct, IteForm::Named] {
            for condition in [false, true] {
                for unsupported in ["user_fp", "fp.min", "fp.max"] {
                    let mut terms = TermStore::new();
                    let c = terms.mk_bool(condition);
                    let x = fp_constant(&mut terms, 0, 32);
                    let hidden = terms.mk_app(
                        Symbol::named(unsupported),
                        [x, x],
                        Sort::FloatingPoint(8, 24),
                    );
                    let bad = rem(&mut terms, x, hidden, 32);
                    let (left, right) = if condition { (x, bad) } else { (bad, x) };
                    let chosen = selection_choose(&mut terms, form, c, left, right);
                    let root = predicate(&mut terms, "fp.isZero", &[chosen]);
                    assert!(matches!(
                        error(&terms, root, budget),
                        FpAdapterError::Unsupported(_)
                    ));
                }
            }
        }
    });
}

#[test]
fn exact_remainder_occurrence_fee_includes_repeated_roots_and_preserves_gate_cap() {
    with_owner(1, |budget| {
        let mut terms = TermStore::new();
        let root = constant(&mut terms);
        let plan = source::plan(&terms, &[root], &[], budget).unwrap();
        assert_eq!(plan.occurrences, 6);
        assert_eq!(plan.gates, 917_504 + 5 * 4096 + 64);
        let repeated = source::plan(&terms, &[root, root], &[], budget).unwrap();
        assert_eq!(repeated.gates, 2 * 917_504 + 10 * 4096 + 64);
        assert_eq!(repeated.occurrences, 12);
        assert_eq!(plan.clauses, 4 * plan.gates + 1);
        let old = budget.remaining();
        plan.prepay(budget).unwrap();
        assert_eq!(
            old - budget.remaining(),
            u64::try_from(plan.gates * 1024).unwrap()
        );
        assert!(matches!(
            source::plan(&terms, &[root; 18], &[], budget),
            Err(FpAdapterError::Unsupported("complete circuit envelope"))
        ));
    });
}

#[test]
fn original_remainder_work_and_storage_one_short_are_sticky_before_native_entry() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let root = constant(&mut terms);
    let mut poll = || {
        if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let plan = {
        let mut funded = WorkBudget::new(10_000_000_000, &mut poll);
        source::plan(&terms, &[root], &[], &mut funded).unwrap()
    };
    {
        let mut short = WorkBudget::new(u64::try_from(plan.gates * 1024 - 1).unwrap(), &mut poll);
        assert!(matches!(
            plan.prepay(&mut short),
            Err(FpAdapterError::Owner(QueryError::Exhausted))
        ));
        assert_eq!(short.charge(0), Err(QueryError::Exhausted));
    }
    let (permit, bytes) = (Cell::new(false), Cell::new(plan.gates * 4096 - 1));
    let mut admission = |_, cost| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        if permit.get() {
            return Ok(());
        }
        bytes.set(bytes.get().checked_sub(cost).ok_or(QueryError::Exhausted)?);
        Ok(())
    };
    {
        let mut short = WorkBudget::with_admission(10_000_000_000, &mut admission);
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
fn original_raw_flag_and_expired_end_remain_refused_after_reset() {
    let mut terms = TermStore::new();
    let root = constant(&mut terms);
    let raw = Arc::new(AtomicBool::new(true));
    let captured = Arc::clone(&raw);
    let mut stop = || {
        if captured.load(Ordering::Relaxed) {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut stop);
    assert!(matches!(
        error(&terms, root, &mut budget),
        FpAdapterError::Owner(QueryError::Interrupted(StopReason::Cancelled))
    ));
    raw.store(false, Ordering::Relaxed);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
    let end = Instant::now()
        .checked_sub(Duration::from_secs(1))
        .expect("fixture instant supports a one-second offset");
    let mut deadline = || {
        if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut deadline);
    assert!(matches!(
        error(&terms, root, &mut budget),
        FpAdapterError::Owner(QueryError::Interrupted(StopReason::Deadline))
    ));
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
}

#[test]
fn native_remainder_row_refusal_is_shared_with_the_original_sticky_ledger() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let x = terms.mk_var("row_x", Sort::FloatingPoint(11, 53));
    let y = terms.mk_var("row_y", Sort::FloatingPoint(11, 53));
    let result = rem(&mut terms, x, y, 64);
    let root = predicate(&mut terms, "fp.isNormal", &[result]);
    let targets = [
        ChcVar::new("row_x", crate::ChcSort::BitVec(64)),
        ChcVar::new("row_y", crate::ChcSort::BitVec(64)),
    ];
    let inputs = [
        FpInputBinding {
            source: x,
            target: &targets[0],
        },
        FpInputBinding {
            source: y,
            target: &targets[1],
        },
    ];
    let stopped = Cell::new(false);
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
    let plan = source::plan(&terms, &[root], &inputs, &mut budget).unwrap();
    plan.prepay(&mut budget).unwrap();
    let frontier = Cell::new(None);
    let mut stop = |progress: ay_fp::FpBuildProgress| {
        if progress.stage == ay_fp::FpBuildStage::MultiplyRow {
            if let Some(before) = frontier.get() {
                if progress.variables > before {
                    stopped.set(true);
                }
            }
            frontier.set(Some(progress.variables));
        }
        budget.charge(0).is_err()
    };
    let mut attempt = ay_fp::FpConstruction::new(ay_fp::FpSolver::new(&terms), &mut stop).unwrap();
    assert!(matches!(
        attempt.try_encode_bool_condition(root),
        Err(ay_fp::FpBuildError::Interrupted)
    ));
    assert!(frontier.get().unwrap() > 128);
    stopped.set(false);
    assert!(matches!(
        attempt.try_encode_bool_condition(root),
        Err(ay_fp::FpBuildError::Interrupted)
    ));
    assert!(matches!(
        attempt.finish(),
        Err(ay_fp::FpBuildError::Interrupted)
    ));
    drop(stop);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}

#[test]
fn complete_remainder_final_drop_boundary_cannot_publish_after_original_refusal() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let root = constant(&mut terms);
    let stopped = Cell::new(false);
    let finals = Cell::new(0);
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
    let mut stop = |progress: ay_fp::FpBuildProgress| {
        if progress.stage == ay_fp::FpBuildStage::Finalize {
            finals.set(finals.get() + 1);
            if finals.get() == 2 {
                stopped.set(true);
            }
        }
        budget.charge(0).is_err()
    };
    let mut attempt = ay_fp::FpConstruction::new(ay_fp::FpSolver::new(&terms), &mut stop).unwrap();
    assert!(attempt.try_encode_bool_condition(root).is_ok());
    assert!(matches!(
        attempt.finish(),
        Err(ay_fp::FpBuildError::Interrupted)
    ));
    assert_eq!(finals.get(), 2);
    stopped.set(false);
    drop(stop);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}
