// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

struct Fixture {
    input: Expr,
    output: Expr,
    target: ChcVar,
    namespace: ChcProblem,
}

impl Fixture {
    fn new() -> Self {
        let (output, target) = raw("resource_ssa", 32);
        Self {
            input: Expr::bitvec_const(0x7f800123u64, 32),
            output,
            target,
            namespace: ChcProblem::new(),
        }
    }
    fn attempt(&self, budget: &mut WorkBudget<'_>) -> Result<(), FpAdapterError> {
        let results = [FpRawResultRelation {
            operation: FpRawOperation::Copy(&self.input),
            output: &self.output,
        }];
        let bindings = [FpExprInputBinding {
            source: &self.output,
            target: &self.target,
        }];
        {
            let (body, _source) =
                lower_fp_raw_result_clause(&[], &results, &bindings, &self.namespace, budget)?
                    .into_body(ClauseBody::empty())?
                    .into_parts()?;
            drop(body);
        }
        budget.charge(0)?;
        Ok(())
    }
}

#[test]
fn exact_work_and_bytes_succeed_and_each_one_short_is_sticky() {
    let end = Instant::now() + Duration::from_secs(20);
    let paid = Cell::new(0usize);
    let stored = Cell::new(0usize);
    let fixture;
    {
        let mut count = |work: usize, bytes: usize| {
            if Instant::now() >= end {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
            paid.set(paid.get().checked_add(work).unwrap());
            stored.set(stored.get().checked_add(bytes).unwrap());
            Ok(())
        };
        let mut budget = WorkBudget::with_admission(WORK, &mut count);
        budget.admit(FIXTURE, FIXTURE).unwrap();
        fixture = Fixture::new();
        fixture.attempt(&mut budget).unwrap();
    }
    assert!(paid.get() > 0 && stored.get() > 0);
    for (work, bytes, expected) in [
        (paid.get(), stored.get(), true),
        (paid.get() - 1, stored.get(), false),
        (paid.get(), stored.get() - 1, false),
    ] {
        // Independent exact/one-short admission attempts share ONE original end;
        // each whole attempt uses ONE ledger, never a stage grant/reset/retry.
        let mut remaining = bytes;
        let mut owner = |_: usize, bytes: usize| {
            if Instant::now() >= end {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
            remaining = remaining.checked_sub(bytes).ok_or(QueryError::Exhausted)?;
            Ok(())
        };
        let mut budget = WorkBudget::with_admission(work as u64, &mut owner);
        let result = budget
            .admit(FIXTURE, FIXTURE)
            .map_err(FpAdapterError::Owner)
            .and_then(|()| fixture.attempt(&mut budget));
        assert_eq!(result.is_ok(), expected);
        if expected {
            assert_eq!(budget.remaining(), 0);
            assert_eq!(budget.charge(0), Ok(()));
        } else {
            assert_eq!(
                result.err(),
                Some(FpAdapterError::Owner(QueryError::Exhausted))
            );
            assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
        }
    }
}

#[test]
fn original_stop_reset_cannot_revive_a_raw_result_attempt() {
    let end = Instant::now() + Duration::from_secs(20);
    let stopped = Cell::new(false);
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        if stopped.get() {
            Err(QueryError::Interrupted(StopReason::Cancelled))
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    budget.admit(FIXTURE, FIXTURE).unwrap();
    let fixture = Fixture::new();
    stopped.set(true);
    assert_eq!(
        fixture.attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Cancelled
        )))
    );
    stopped.set(false);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
    assert_eq!(
        fixture.attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Cancelled
        )))
    );
}

#[test]
fn expired_original_absolute_end_refuses_before_any_synthetic_relation() {
    let end = Instant::now()
        .checked_sub(Duration::from_secs(1))
        .expect("fixture instant follows one-second offset");
    let namespace = ChcProblem::new();
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= end {
            Err(QueryError::Interrupted(StopReason::Deadline))
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    assert_eq!(
        lower_fp_raw_result_clause(&[], &[], &[], &namespace, &mut budget).err(),
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
fn final_synthetic_and_arena_cleanup_poll_can_veto_complete_data() {
    let end = Instant::now() + Duration::from_secs(20);
    let calls = Cell::new(0usize);
    let fixture;
    let results;
    let bindings;
    let final_call = {
        let mut count = |_: usize, _: usize| {
            if Instant::now() >= end {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
            calls.set(calls.get() + 1);
            Ok(())
        };
        let mut budget = WorkBudget::with_admission(WORK, &mut count);
        budget.admit(FIXTURE, FIXTURE).unwrap();
        fixture = Fixture::new();
        results = [FpRawResultRelation {
            operation: FpRawOperation::Copy(&fixture.input),
            output: &fixture.output,
        }];
        bindings = [FpExprInputBinding {
            source: &fixture.output,
            target: &fixture.target,
        }];
        drop(
            lower_fp_raw_result_clause(&[], &results, &bindings, &fixture.namespace, &mut budget)
                .unwrap(),
        );
        calls.get()
    };
    calls.set(0);
    let mut stop = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        calls.set(calls.get() + 1);
        if calls.get() == final_call {
            Err(QueryError::Invalid("raw-result final cleanup"))
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut stop);
    budget.admit(FIXTURE, FIXTURE).unwrap();
    assert_eq!(
        lower_fp_raw_result_clause(&[], &results, &bindings, &fixture.namespace, &mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Invalid(
            "raw-result final cleanup"
        )))
    );
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Invalid("raw-result final cleanup"))
    );
}

#[test]
fn retained_attachment_and_parts_have_same_original_late_owner_veto() {
    let end = Instant::now() + Duration::from_secs(20);
    for parts in [false, true] {
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
        let fixture = Fixture::new();
        let results = [FpRawResultRelation {
            operation: FpRawOperation::Copy(&fixture.input),
            output: &fixture.output,
        }];
        let bindings = [FpExprInputBinding {
            source: &fixture.output,
            target: &fixture.target,
        }];
        let output =
            lower_fp_raw_result_clause(&[], &results, &bindings, &fixture.namespace, &mut budget)
                .unwrap();
        if parts {
            let body = output.into_body(ClauseBody::empty()).unwrap();
            permit.set(false);
            assert!(matches!(
                body.into_parts(),
                Err(FpAdapterError::Owner(QueryError::Interrupted(
                    StopReason::Cancelled
                )))
            ));
        } else {
            permit.set(false);
            assert!(matches!(
                output.into_body(ClauseBody::empty()),
                Err(FpAdapterError::Owner(QueryError::Interrupted(
                    StopReason::Cancelled
                )))
            ));
        }
        permit.set(true);
        assert_eq!(
            budget.charge(0),
            Err(QueryError::Interrupted(StopReason::Cancelled))
        );
    }
}

#[test]
fn admission_callback_unwind_leaves_the_original_ledger_terminal() {
    let end = Instant::now() + Duration::from_secs(20);
    let panic_now = Cell::new(false);
    let mut owner = |_: usize, _: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        assert!(!panic_now.get(), "original test observer panic");
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(WORK, &mut owner);
    budget.admit(FIXTURE, FIXTURE).unwrap();
    let fixture = Fixture::new();
    panic_now.set(true);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        fixture.attempt(&mut budget)
    }));
    assert!(result.is_err());
    panic_now.set(false);
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
    assert_eq!(
        fixture.attempt(&mut budget).err(),
        Some(FpAdapterError::Owner(QueryError::Exhausted))
    );
}
