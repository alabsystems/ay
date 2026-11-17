// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError};

fn attempt(budget: &mut WorkBudget<'_>) -> Result<(), FpAdapterError> {
    budget.admit(FIXTURE, FIXTURE)?;
    let input = Expr::bitvec_const(255u8, 8);
    let (output, target) = raw("owned_integer_output", 32);
    let results = [FpRawResultRelation {
        operation: Kind::Unsigned.operation(&input),
        output: &output,
    }];
    let bindings = [FpExprInputBinding {
        source: &output,
        target: &target,
    }];
    let namespace = ChcProblem::new();
    {
        let result = lower_fp_raw_result_clause(&[], &results, &bindings, &namespace, budget)
            .and_then(|data| data.into_body(ClauseBody::empty()))
            .and_then(|body| body.into_parts());
        let (body, _source) = result?;
        drop(body);
    }
    drop(input);
    drop(output);
    drop(target);
    drop(namespace);
    budget.charge(0)?;
    Ok(())
}

fn measured(end: Instant) -> (usize, usize, usize) {
    let work = Cell::new(0usize);
    let bytes = Cell::new(0usize);
    let calls = Cell::new(0usize);
    {
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
        attempt(&mut budget).unwrap();
    }
    (work.get(), bytes.get(), calls.get())
}

#[test]
fn exact_whole_work_and_bytes_and_one_short_never_publish_partial_casts() {
    let end = Instant::now() + Duration::from_secs(20);
    let (work, bytes, _) = measured(end);
    assert!(work >= 18_432 * 1024 && bytes >= 18_432 * 4096);
    for (grant, storage, success) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (0, bytes, false),
    ] {
        // Separate entire fixture attempts share the same immutable end.
        // Every attempt has ONE ledger, no fresh per-stage grant or retry.
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
            attempt(&mut budget).unwrap();
            assert_eq!(budget.remaining(), 0);
            assert_eq!(budget.charge(0), Ok(()));
        } else {
            assert_eq!(
                attempt(&mut budget).err(),
                Some(FpAdapterError::Owner(QueryError::Exhausted))
            );
            assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
            assert_eq!(
                attempt(&mut budget).err(),
                Some(FpAdapterError::Owner(QueryError::Exhausted))
            );
        }
    }
}

#[test]
fn original_cancel_deadline_and_expired_end_are_sticky_after_raw_reset() {
    let end = Instant::now() + Duration::from_secs(20);
    for reason in [StopReason::Cancelled, StopReason::Deadline] {
        let stopped = Cell::new(true);
        let mut owner = |_: usize, _: usize| {
            if Instant::now() >= end {
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
            attempt(&mut budget).err(),
            Some(FpAdapterError::Owner(QueryError::Interrupted(reason)))
        );
        stopped.set(false);
        assert_eq!(budget.charge(0), Err(QueryError::Interrupted(reason)));
        assert_eq!(
            attempt(&mut budget).err(),
            Some(FpAdapterError::Owner(QueryError::Interrupted(reason)))
        );
    }
    let expired = Instant::now()
        .checked_sub(Duration::from_secs(1))
        .expect("fixture instant follows one-second offset");
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
fn last_real_cleanup_poll_veto_is_terminal_on_the_same_ledger() {
    let end = Instant::now() + Duration::from_secs(20);
    let (_, _, last) = measured(end);
    let calls = Cell::new(0usize);
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        calls.set(calls.get() + 1);
        if calls.get() == last {
            Err(QueryError::Invalid("integer cleanup veto"))
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    assert_eq!(
        attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Invalid(
            "integer cleanup veto"
        )))
    );
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Invalid("integer cleanup veto"))
    );
}

#[test]
fn retained_cast_consumption_keeps_the_original_late_stop_after_reset() {
    let end = Instant::now() + Duration::from_secs(20);
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
    budget.admit(FIXTURE, FIXTURE).unwrap();
    let input = Expr::bitvec_const(255u8, 8);
    let (output, target) = raw("late_integer_output", 32);
    let results = [FpRawResultRelation {
        operation: Kind::Unsigned.operation(&input),
        output: &output,
    }];
    let bindings = [FpExprInputBinding {
        source: &output,
        target: &target,
    }];
    let namespace = ChcProblem::new();
    let retained = lower_fp_raw_result_clause(&[], &results, &bindings, &namespace, &mut budget)
        .unwrap()
        .into_body(ClauseBody::empty())
        .unwrap();
    permit.set(false);
    assert!(matches!(
        retained.into_parts(),
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

#[test]
fn cloned_original_admission_cannot_renew_cast_constructor_or_native_fees() {
    let end = Instant::now() + Duration::from_secs(20);
    let (work, bytes, _) = measured(end);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(work as u64, bytes),
        end,
        Arc::new(|| false),
    );
    let clone = owner.clone();
    let adapter = |budget: &mut WorkBudget<'_>| match attempt(budget) {
        Ok(()) => Ok(()),
        Err(FpAdapterError::Owner(error)) => Err(error),
        Err(_) => Err(QueryError::Invalid("unexpected integer source refusal")),
    };
    owner.with_work(adapter).unwrap();
    assert_eq!(
        clone.with_work(adapter),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(
        owner.check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}
