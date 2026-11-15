// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn constant_attempt(budget: &mut WorkBudget<'_>) -> Result<(), FpAdapterError> {
    let roots = [Expr::true_()];
    let problem = ChcProblem::new();
    let data = lower_fp_expr_clause(&roots, &[], &problem, budget)?;
    let attached = data.into_body(ClauseBody::empty())?;
    let (body, source) = attached.into_parts()?;
    drop(body);
    drop(source);
    budget.charge(0)?;
    Ok(())
}

#[test]
fn original_raw_callback_refusal_stays_sticky_after_reset() {
    let raw = Cell::new(true);
    let mut admission = |_: usize, _: usize| {
        if raw.get() {
            Err(QueryError::Interrupted(StopReason::Cancelled))
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut admission);
    assert_eq!(
        constant_attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Cancelled
        )))
    );
    raw.set(false);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}

#[test]
fn expired_original_absolute_end_is_not_refreshed_for_translation_or_attachment() {
    let end = Instant::now() - Duration::from_secs(1);
    let mut admission = |_: usize, _: usize| {
        if Instant::now() >= end {
            Err(QueryError::Interrupted(StopReason::Deadline))
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut admission);
    assert_eq!(
        constant_attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Deadline
        )))
    );
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
}

#[test]
fn exact_one_short_total_work_and_storage_refuse_the_same_ledger() {
    let work = Cell::new(0usize);
    let bytes = Cell::new(0usize);
    let mut count = |w: usize, b: usize| {
        work.set(work.get().checked_add(w).unwrap());
        bytes.set(bytes.get().checked_add(b).unwrap());
        Ok(())
    };
    let mut healthy = WorkBudget::with_admission(WORK, &mut count);
    constant_attempt(&mut healthy).unwrap();
    drop(healthy);
    let total = work.get();
    let storage = bytes.get();
    assert!(total > 0 && storage > 0);
    let mut admit = |_: usize, _: usize| Ok(());
    let mut short = WorkBudget::with_admission((total - 1) as u64, &mut admit);
    assert_eq!(
        constant_attempt(&mut short).err(),
        Some(FpAdapterError::Owner(QueryError::Exhausted))
    );
    assert_eq!(short.charge(0), Err(QueryError::Exhausted));
    let mut remaining = storage - 1;
    let mut admit = |_: usize, b: usize| {
        remaining = remaining.checked_sub(b).ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    let mut short = WorkBudget::with_admission(WORK, &mut admit);
    assert_eq!(
        constant_attempt(&mut short).err(),
        Some(FpAdapterError::Owner(QueryError::Exhausted))
    );
    assert_eq!(short.charge(0), Err(QueryError::Exhausted));
}

#[test]
fn positional_snapshot_refusal_retains_exact_original_owner_error() {
    let mut admission = |_: usize, b: usize| {
        // Census and translator first pay large fixed reserves; snapshot's
        // later small nonzero record reserve is the first such request.
        if b > 0 && b < 65_536 {
            Err(QueryError::Invalid("original snapshot owner"))
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut admission);
    let roots = [Expr::true_()];
    let problem = ChcProblem::new();
    assert_eq!(
        lower_fp_expr_clause(&roots, &[], &problem, &mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Invalid(
            "original snapshot owner"
        )))
    );
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Invalid("original snapshot owner"))
    );
}

#[test]
fn final_post_arena_cleanup_callback_can_veto_all_complete_data() {
    let calls = Cell::new(0usize);
    let roots = [Expr::true_()];
    let problem = ChcProblem::new();
    let mut count = |_: usize, _: usize| {
        calls.set(calls.get() + 1);
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut count);
    drop(lower_fp_expr_clause(&roots, &[], &problem, &mut budget).unwrap());
    let last = calls.get();
    drop(budget);
    calls.set(0);
    let mut stop = |_: usize, _: usize| {
        calls.set(calls.get() + 1);
        if calls.get() == last {
            Err(QueryError::Interrupted(StopReason::Deadline))
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut stop);
    assert_eq!(
        lower_fp_expr_clause(&roots, &[], &problem, &mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Deadline
        )))
    );
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
}

#[test]
fn late_body_and_consuming_parts_fences_refuse_without_a_second_grant() {
    let permit = Cell::new(true);
    let roots = [Expr::true_()];
    let problem = ChcProblem::new();
    let mut admission = |_: usize, _: usize| {
        if permit.get() {
            Ok(())
        } else {
            Err(QueryError::Interrupted(StopReason::Cancelled))
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut admission);
    let output = lower_fp_expr_clause(&roots, &[], &problem, &mut budget).unwrap();
    permit.set(false);
    assert!(matches!(
        output.into_body(ClauseBody::empty()),
        Err(FpAdapterError::Owner(_))
    ));
    permit.set(true);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}

#[test]
fn consuming_parts_preserves_a_late_original_owner_refusal() {
    let permit = Cell::new(true);
    let roots = [Expr::true_()];
    let problem = ChcProblem::new();
    let mut admission = |_: usize, _: usize| {
        if permit.get() {
            Ok(())
        } else {
            Err(QueryError::Invalid("original parts owner"))
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut admission);
    let output = relation(&roots, &[], &problem, &mut budget);
    permit.set(false);
    assert!(matches!(
        output.into_parts(),
        Err(FpAdapterError::Owner(QueryError::Invalid(
            "original parts owner"
        )))
    ));
    permit.set(true);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Invalid("original parts owner"))
    );
}
