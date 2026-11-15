// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn truncating_total_work_and_storage_one_short_remain_sticky() {
    let end = Instant::now() + Duration::from_secs(20);
    let work = Cell::new(0usize);
    let storage = Cell::new(0usize);
    let mut count = |w: usize, b: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        work.set(work.get().checked_add(w).unwrap());
        storage.set(storage.get().checked_add(b).unwrap());
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut count);
    attempt(&mut budget).unwrap();
    drop(budget);
    let mut healthy = |_: usize, _: usize| {
        if Instant::now() >= end {
            Err(QueryError::Interrupted(StopReason::Deadline))
        } else {
            Ok(())
        }
    };
    let mut short = WorkBudget::with_admission((work.get() - 1) as u64, &mut healthy);
    assert_eq!(
        attempt(&mut short).err(),
        Some(FpAdapterError::Owner(QueryError::Exhausted))
    );
    assert_eq!(short.charge(0), Err(QueryError::Exhausted));
    drop(short);
    let mut bytes = storage.get() - 1;
    let mut limited = |_: usize, b: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        bytes = bytes.checked_sub(b).ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    let mut short = WorkBudget::with_admission(WORK, &mut limited);
    assert_eq!(
        attempt(&mut short).err(),
        Some(FpAdapterError::Owner(QueryError::Exhausted))
    );
    assert_eq!(short.charge(0), Err(QueryError::Exhausted));
}

#[test]
fn truncating_raw_and_original_end_refusal_cannot_be_reset_into_data() {
    let raw = Cell::new(true);
    let end = Instant::now() + Duration::from_secs(20);
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        if raw.get() {
            Err(QueryError::Interrupted(StopReason::Cancelled))
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    assert_eq!(
        attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Cancelled
        )))
    );
    raw.set(false);
    assert_eq!(
        attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Cancelled
        )))
    );
    let expired = Instant::now() - Duration::from_secs(1);
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= expired {
            Err(QueryError::Interrupted(StopReason::Deadline))
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    assert_eq!(
        attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Deadline
        )))
    );
}

#[test]
fn consuming_truncating_data_keeps_original_callback_after_arena_and_body_cleanup() {
    let end = Instant::now() + Duration::from_secs(20);
    let permit = Cell::new(true);
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        if permit.get() {
            Ok(())
        } else {
            Err(QueryError::Invalid("original callback"))
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    let roots = [root(32)];
    let problem = ChcProblem::new();
    let body = lower_fp_expr_clause(&roots, &[], &problem, &mut budget)
        .unwrap()
        .into_body(ClauseBody::empty())
        .unwrap();
    permit.set(false);
    assert!(matches!(
        body.into_parts(),
        Err(FpAdapterError::Owner(QueryError::Invalid(_)))
    ));
    permit.set(true);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Invalid("original callback"))
    );
}
