// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn raw_word_work_and_storage_one_short_use_the_same_sticky_ledger() {
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
    raw_attempt(&mut budget).unwrap();
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
        raw_attempt(&mut short).err(),
        Some(FpAdapterError::Owner(QueryError::Exhausted))
    );
    assert_eq!(short.charge(0), Err(QueryError::Exhausted));
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
        raw_attempt(&mut short).err(),
        Some(FpAdapterError::Owner(QueryError::Exhausted))
    );
    assert_eq!(short.charge(0), Err(QueryError::Exhausted));
}

#[test]
fn original_raw_stop_and_end_refuse_before_any_word_relation() {
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
        raw_attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Cancelled
        )))
    );
    raw.set(false);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
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
        raw_attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Deadline
        )))
    );
}

#[test]
fn post_arena_cleanup_and_retained_consumption_keep_original_callback_vetoes() {
    let end = Instant::now() + Duration::from_secs(20);
    let calls = Cell::new(0usize);
    let (word, target) = raw_input(32);
    let roots = [fields(word.clone(), 32).fp_is_normal()];
    let bindings = [FpExprInputBinding {
        source: &word,
        target: &target,
    }];
    let problem = ChcProblem::new();
    let mut count = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        calls.set(calls.get() + 1);
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut count);
    drop(lower_fp_expr_clause(&roots, &bindings, &problem, &mut budget).unwrap());
    let last = calls.get();
    drop(budget);
    calls.set(0);
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        calls.set(calls.get() + 1);
        if calls.get() == last {
            Err(QueryError::Invalid("raw cleanup owner"))
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    assert_eq!(
        lower_fp_expr_clause(&roots, &bindings, &problem, &mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Invalid(
            "raw cleanup owner"
        )))
    );
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Invalid("raw cleanup owner"))
    );
    let permit = Cell::new(true);
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        if permit.get() {
            Ok(())
        } else {
            Err(QueryError::Invalid("raw body owner"))
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    let output = relation(&roots, &bindings, &problem, &mut budget);
    permit.set(false);
    assert!(matches!(
        output.into_parts(),
        Err(FpAdapterError::Owner(QueryError::Invalid("raw body owner")))
    ));
    permit.set(true);
    assert_eq!(budget.charge(0), Err(QueryError::Invalid("raw body owner")));
}
