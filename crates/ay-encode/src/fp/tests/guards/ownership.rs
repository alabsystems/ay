// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn zero_and_one_short_total_work_or_storage_poison_the_same_guard_ledger() {
    let end = Instant::now() + Duration::from_secs(20);
    let work = Cell::new(0usize);
    let bytes = Cell::new(0usize);
    {
        let mut count = |w: usize, b: usize| {
            if Instant::now() >= end {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
            work.set(work.get().checked_add(w).unwrap());
            bytes.set(bytes.get().checked_add(b).unwrap());
            Ok(())
        };
        let mut budget = WorkBudget::with_admission(WORK, &mut count);
        attempt(&mut budget).unwrap();
    }
    // Independent negative fixture owners share the original test end. None
    // is a renewed production retry; every refused ledger remains poisoned.
    for limit in [0, (work.get() - 1) as u64] {
        let mut owner = |_: usize, _: usize| {
            if Instant::now() >= end {
                Err(QueryError::Interrupted(StopReason::Deadline))
            } else {
                Ok(())
            }
        };
        let mut budget = WorkBudget::with_admission(limit, &mut owner);
        assert_eq!(
            attempt(&mut budget).err(),
            Some(FpAdapterError::Owner(QueryError::Exhausted))
        );
        assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
    }
    let mut left = bytes.get() - 1;
    let mut owner = |_: usize, b: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        left = left.checked_sub(b).ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    assert_eq!(
        attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Exhausted))
    );
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
}

#[test]
fn original_raw_and_expired_end_refusals_survive_reset_without_guard_data() {
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
fn late_original_callback_veto_survives_attachment_and_body_cleanup() {
    let end = Instant::now() + Duration::from_secs(20);
    let permit = Cell::new(true);
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        if permit.get() {
            Ok(())
        } else {
            Err(QueryError::Invalid("late guard owner"))
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    let (words, targets) = inputs(64);
    let roots = [words[0]
        .clone()
        .bvult(words[1].clone())
        .or(fields(words[1].clone(), 64).fp_is_zero())];
    let bindings = links(&words, &targets);
    let namespace = ChcProblem::new();
    let output = lower_fp_expr_clause(&roots, &bindings, &namespace, &mut budget).unwrap();
    let attached = output.into_body(ClauseBody::empty()).unwrap();
    permit.set(false);
    assert!(matches!(
        attached.into_parts(),
        Err(FpAdapterError::Owner(QueryError::Invalid(
            "late guard owner"
        )))
    ));
    permit.set(true);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Invalid("late guard owner"))
    );
}
