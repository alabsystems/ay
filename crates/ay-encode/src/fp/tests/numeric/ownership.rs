// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn measured(fixture: &Fixture, end: Instant) -> (usize, usize, usize) {
    let work = Cell::new(0usize);
    let bytes = Cell::new(0usize);
    let calls = Cell::new(0usize);
    let mut owner = |w: usize, b: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        work.set(work.get().checked_add(w).ok_or(QueryError::Exhausted)?);
        bytes.set(bytes.get().checked_add(b).ok_or(QueryError::Exhausted)?);
        calls.set(calls.get().checked_add(1).ok_or(QueryError::Exhausted)?);
        if work.get() as u64 > WORK || bytes.get() as u64 > BYTES {
            return Err(QueryError::Exhausted);
        }
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    fixture.attempt(&mut budget).unwrap();
    drop(budget);
    (work.get(), bytes.get(), calls.get())
}

#[test]
fn numeric_exact_whole_work_storage_and_one_short_are_on_one_absolute_end() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let (work, bytes, _) = measured(&fixture, end);
    assert!(work >= 18_432 * 1024 && bytes >= 18_432 * 4096);
    // These are independent positive/negative fixture owners, not a retry of
    // production refusal. None renews the common absolute end.
    for (grant, storage, success) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (0, bytes, false),
    ] {
        let mut left = storage;
        let mut owner = |_: usize, b: usize| {
            if Instant::now() >= end {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
            left = left.checked_sub(b).ok_or(QueryError::Exhausted)?;
            Ok(())
        };
        let mut budget = WorkBudget::with_admission(u64::try_from(grant).unwrap(), &mut owner);
        if success {
            fixture.attempt(&mut budget).unwrap();
        } else {
            assert_eq!(
                fixture.attempt(&mut budget).err(),
                Some(FpAdapterError::Owner(QueryError::Exhausted))
            );
            assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
        }
    }
}

#[test]
fn numeric_original_raw_and_absolute_end_refusal_cannot_be_reset() {
    let common_end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    for reason in [StopReason::Cancelled, StopReason::Deadline] {
        let stopped = Cell::new(true);
        let mut owner = |_: usize, _: usize| {
            if Instant::now() >= common_end {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
            if stopped.get() {
                Err(QueryError::Interrupted(reason))
            } else {
                Ok(())
            }
        };
        let mut budget = WorkBudget::with_admission(WORK, &mut owner);
        assert_eq!(
            fixture.attempt(&mut budget).err(),
            Some(FpAdapterError::Owner(QueryError::Interrupted(reason)))
        );
        stopped.set(false);
        assert_eq!(budget.charge(0), Err(QueryError::Interrupted(reason)));
        assert_eq!(
            fixture.attempt(&mut budget).err(),
            Some(FpAdapterError::Owner(QueryError::Interrupted(reason)))
        );
    }
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
        fixture.attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Deadline
        )))
    );
}

#[test]
fn numeric_callback_unwind_leaves_the_same_ledger_terminal() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let panic_now = Cell::new(true);
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        assert!(!panic_now.get(), "numeric original observer panic");
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    assert!(std::panic::catch_unwind(
        std::panic::AssertUnwindSafe(|| fixture.attempt(&mut budget))
    )
    .is_err());
    panic_now.set(false);
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
    assert_eq!(
        fixture.attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Exhausted))
    );
}

#[test]
fn numeric_last_post_cleanup_and_consuming_fences_preserve_original_veto() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let (_, _, last) = measured(&fixture, end);
    let calls = Cell::new(0usize);
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        calls.set(calls.get() + 1);
        if calls.get() == last {
            Err(QueryError::Invalid("numeric final original veto"))
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    assert_eq!(
        fixture.attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Invalid(
            "numeric final original veto"
        )))
    );
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Invalid("numeric final original veto"))
    );
    drop(budget);
    consuming_veto(&fixture, end);
}

fn consuming_veto(fixture: &Fixture, end: Instant) {
    let permit = Cell::new(true);
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        if permit.get() {
            Ok(())
        } else {
            Err(QueryError::Interrupted(StopReason::Cancelled))
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    let data = lower_fp_expr_clause(&fixture.roots, &[], &fixture.problem, &mut budget).unwrap();
    let body = data.into_body(ClauseBody::empty()).unwrap();
    permit.set(false);
    assert!(matches!(
        body.into_parts(),
        Err(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Cancelled
        )))
    ));
    permit.set(true);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}
