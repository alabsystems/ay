// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn full_cost_sink_receives_bulk_and_storage_not_poll_count() {
    let mut calls = Vec::new();
    let mut sink = |units, bytes| {
        calls.push((units, bytes));
        Ok(())
    };
    let mut work = WorkBudget::with_admission(10_000, &mut sink);
    work.charge(4_096).expect("admit actual bulk units");
    work.admit(7, 8_192)
        .expect("admit independent storage debit");
    work.admit(0, 256).expect("storage-only operation");
    work.charge(0).expect("publication poll");
    assert_eq!(work.remaining(), 5_897);
    assert_eq!(calls, [(4_096, 0), (7, 8_192), (0, 256), (0, 0)]);
}

#[test]
fn storage_refusal_is_sticky_and_stops_later_owner_calls() {
    let mut calls = 0;
    let mut bytes_left = 32usize;
    let mut sink = |_, bytes| {
        calls += 1;
        bytes_left = bytes_left.checked_sub(bytes).ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    let mut work = WorkBudget::with_admission(10_000, &mut sink);
    work.admit(1, 32).expect("exact storage grant");
    assert_eq!(work.admit(0, 1), Err(QueryError::Exhausted));
    assert_eq!(work.charge(0), Err(QueryError::Exhausted));
    assert_eq!(work.admit(0, 0), Err(QueryError::Exhausted));
    assert_eq!(calls, 2);
    assert_eq!(bytes_left, 0);
}

#[test]
fn aggregate_owner_survives_separate_borrowed_phase_adapters() {
    let mut work_left = 7usize;
    let mut storage_left = 5usize;
    let mut stopped = None;
    let mut sink = |units, bytes| {
        if let Some(error) = stopped {
            return Err(error);
        }
        match (
            work_left.checked_sub(units),
            storage_left.checked_sub(bytes),
        ) {
            (Some(work), Some(storage)) => {
                work_left = work;
                storage_left = storage;
                Ok(())
            }
            _ => {
                stopped = Some(QueryError::Exhausted);
                Err(QueryError::Exhausted)
            }
        }
    };
    WorkBudget::with_admission(100, &mut sink)
        .admit(4, 3)
        .expect("capture phase");
    WorkBudget::with_admission(100, &mut sink)
        .admit(3, 2)
        .expect("checking phase");
    assert_eq!(
        WorkBudget::with_admission(100, &mut sink).charge(1),
        Err(QueryError::Exhausted)
    );
    assert_eq!(
        WorkBudget::with_admission(100, &mut sink).charge(0),
        Err(QueryError::Exhausted)
    );
    drop(sink);
    assert_eq!((work_left, storage_left), (0, 0));
}

#[test]
fn caller_stop_survives_allocation_error_and_permissive_callback() {
    for reason in [StopReason::Cancelled, StopReason::Deadline] {
        let mut calls = 0;
        let mut sink = |_, _| {
            calls += 1;
            if calls == 1 {
                Err(QueryError::Interrupted(reason))
            } else {
                Ok(())
            }
        };
        let mut work = WorkBudget::with_admission(100, &mut sink);
        assert_eq!(work.admit(1, 32), Err(QueryError::Interrupted(reason)));
        assert_eq!(work.refuse_exhaustion(), QueryError::Interrupted(reason));
        assert_eq!(work.admit(0, 0), Err(QueryError::Interrupted(reason)));
        assert_eq!(calls, 1);
    }
}

#[test]
fn fallible_allocation_refusal_is_recorded_in_the_shared_latch() {
    let mut calls = 0;
    let mut sink = |_, _| {
        calls += 1;
        Ok(())
    };
    let mut work = WorkBudget::with_admission(100, &mut sink);
    work.admit(1, 16).expect("admission before allocation");
    assert_eq!(work.refuse_exhaustion(), QueryError::Exhausted);
    assert_eq!(work.charge(0), Err(QueryError::Exhausted));
    assert_eq!(calls, 1);
}

#[test]
fn exact_work_grant_and_one_short_local_ceiling_refuse_without_refund() {
    let mut total = 0usize;
    let mut sink = |units, _| {
        total += units;
        Ok(())
    };
    let mut work = WorkBudget::with_admission(10, &mut sink);
    work.charge(10).expect("exact local ceiling");
    assert_eq!(work.remaining(), 0);
    assert_eq!(work.charge(1), Err(QueryError::Exhausted));
    assert_eq!(work.charge(0), Err(QueryError::Exhausted));
    // The owner was debited before local refusal, matching compatibility order;
    // it receives no refund, and no operation occurs after failed admission.
    assert_eq!(total, 11);
}

#[test]
fn legacy_callback_order_and_sticky_interrupt_are_preserved() {
    let mut calls = 0;
    let mut poll = || {
        calls += 1;
        ControlFlow::Break(StopReason::Deadline)
    };
    let mut work = WorkBudget::new(0, &mut poll);
    assert_eq!(
        work.charge(1),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
    assert_eq!(work.remaining(), 0);
    assert_eq!(
        work.admit(0, 64),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
    assert_eq!(
        work.refuse_exhaustion(),
        QueryError::Interrupted(StopReason::Deadline)
    );
    assert_eq!(calls, 1);
}

#[test]
fn legacy_storage_only_admission_polls_but_does_not_claim_a_storage_limit() {
    let mut calls = 0;
    let mut poll = || {
        calls += 1;
        ControlFlow::Continue(())
    };
    let mut work = WorkBudget::new(1, &mut poll);
    work.admit(0, usize::MAX)
        .expect("compatibility constructor has no storage owner");
    assert_eq!(work.remaining(), 1);
    assert_eq!(calls, 1);
}

#[test]
fn caught_owner_panic_cannot_resume_the_same_ledger() {
    let mut calls = 0;
    let mut sink = |_, _| {
        calls += 1;
        assert_ne!(calls, 1, "test owner panic");
        Ok(())
    };
    let mut work = WorkBudget::with_admission(100, &mut sink);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| work.admit(2, 16))).is_err());
    assert_eq!(work.charge(0), Err(QueryError::Exhausted));
    assert_eq!(work.admit(1, 0), Err(QueryError::Exhausted));
    assert_eq!(calls, 1);
}
