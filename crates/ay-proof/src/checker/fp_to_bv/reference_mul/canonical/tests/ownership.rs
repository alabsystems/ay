// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::StopReason;

#[test]
fn zero_absolute_deadline_and_missing_deadline_never_start_source_proof_search() {
    let mut terms = TermStore::new();
    let root = terms.mk_bool(false);
    let mut live = || ControlFlow::Continue(());
    let mut expired = limits();
    expired.deadline = Some(Instant::now());
    let mut missing = limits();
    missing.deadline = None;
    for configured in [&expired, &missing] {
        let mut work = WorkBudget::new(10_000_000, &mut live);
        assert!(capture(&terms, &[root], configured, &mut work).is_err());
        assert_eq!(work.charge(0), Err(QueryError::Exhausted));
        assert!(
            capture(&terms, &[root], &limits(), &mut work).is_err(),
            "an independent request cannot revive this stopped original owner"
        );
    }
}

#[test]
fn source_storage_admission_happens_before_owned_tables_and_stays_sticky() {
    let mut terms = TermStore::new();
    let root = terms.mk_bool(false);
    let bytes = Cell::new(0usize);
    let mut sink = |_: usize, storage: usize| {
        bytes.set(bytes.get() + storage);
        if storage != 0 {
            Err(QueryError::Exhausted)
        } else {
            Ok(())
        }
    };
    let mut work = WorkBudget::with_admission(10_000_000, &mut sink);
    assert!(capture(&terms, &[root], &limits(), &mut work).is_err());
    assert!(bytes.get() > 0);
    assert_eq!(work.charge(0), Err(QueryError::Exhausted));
    assert!(capture(&terms, &[root], &limits(), &mut work).is_err());
}

#[test]
fn cumulative_remaining_owner_is_never_replaced_between_capture_and_replay() {
    let mut terms = TermStore::new();
    let root = terms.mk_bool(false);
    let units = Cell::new(0usize);
    let mut sink = |work: usize, _: usize| {
        units.set(units.get() + work);
        Ok(())
    };
    let mut work = WorkBudget::with_admission(50_000_000, &mut sink);
    let mut proof = capture(&terms, &[root], &limits(), &mut work).expect("original owner");
    let remaining = proof.work.remaining();
    let consumed = units.get();
    proof.replay().expect("same original owner");
    assert!(proof.work.remaining() < remaining);
    assert!(units.get() > consumed);
}

#[test]
fn retained_absolute_limits_cannot_be_replaced_by_mutating_caller_configuration() {
    let mut terms = TermStore::new();
    let root = terms.mk_bool(false);
    let mut original = limits();
    let original_deadline = original.deadline;
    let original_vars = original.max_num_vars;
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    let mut proof = capture(&terms, &[root], &original, &mut work).expect("original limits");
    original.deadline = None;
    original.max_num_vars = 0;
    original.validation.max_work = u64::MAX;
    assert!(original.deadline.is_none());
    assert_eq!(original.max_num_vars, 0);
    assert_eq!(original.validation.max_work, u64::MAX);
    assert_eq!(proof.limits.deadline, original_deadline);
    assert_eq!(proof.limits.max_num_vars, original_vars);
    proof
        .replay()
        .expect("only the retained original limits are used");
}

#[test]
fn capture_terminal_owner_refusal_cannot_publish_or_restart() {
    let mut terms = TermStore::new();
    let root = terms.mk_bool(false);
    let calls = Cell::new(0usize);
    {
        let mut live = || {
            calls.set(calls.get() + 1);
            ControlFlow::Continue(())
        };
        let mut work = WorkBudget::new(50_000_000, &mut live);
        capture(&terms, &[root], &limits(), &mut work).expect("healthy capture");
    }
    let final_call = calls.get();
    calls.set(0);
    let stopping = Cell::new(true);
    let mut live = || {
        calls.set(calls.get() + 1);
        if stopping.get() && calls.get() == final_call {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut work = WorkBudget::new(50_000_000, &mut live);
    assert!(capture(&terms, &[root], &limits(), &mut work).is_err());
    assert_eq!(calls.get(), final_call);
    stopping.set(false);
    assert_eq!(
        work.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}

#[test]
fn cancelled_original_owner_cannot_be_swallowed_or_restarted_for_replay() {
    let mut terms = TermStore::new();
    let root = terms.mk_bool(false);
    let stop = Cell::new(false);
    let mut live = || {
        if stop.get() {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut work = WorkBudget::new(50_000_000, &mut live);
    let mut proof = capture(&terms, &[root], &limits(), &mut work).expect("before original stop");
    stop.set(true);
    assert!(proof.replay().is_err());
    stop.set(false);
    assert_eq!(
        proof.work.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
    assert!(proof.replay().is_err());
}

#[test]
fn first_source_and_binding_errors_survive_terminal_owner_refusal_without_retry() {
    let mut terms = TermStore::new();
    let root = terms.mk_bool(false);
    let fixed = limits();
    let calls = Cell::new(0usize);
    {
        let mut live = || {
            calls.set(calls.get() + 1);
            ControlFlow::Continue(())
        };
        let mut work = WorkBudget::new(50_000_000, &mut live);
        assert!(matches!(
            capture(&terms, &[TermId(u32::MAX)], &fixed, &mut work),
            Err(Error::Reference(ReferenceError::Source))
        ));
    }
    let final_call = calls.get();
    calls.set(0);
    let mut live = || {
        calls.set(calls.get() + 1);
        if calls.get() == final_call {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut work = WorkBudget::new(50_000_000, &mut live);
    assert!(matches!(
        capture(&terms, &[TermId(u32::MAX)], &fixed, &mut work),
        Err(Error::Reference(ReferenceError::Source))
    ));
    assert_eq!(
        work.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );

    let measuring = Cell::new(false);
    calls.set(0);
    {
        let mut live = || {
            if measuring.get() {
                calls.set(calls.get() + 1);
            }
            ControlFlow::Continue(())
        };
        let mut work = WorkBudget::new(50_000_000, &mut live);
        let mut proof = capture(&terms, &[root], &fixed, &mut work).expect("real originals");
        proof.dag.original_clauses[0].0 += 1;
        measuring.set(true);
        assert!(matches!(proof.replay(), Err(Error::Binding)));
    }
    let binding_final = calls.get();
    calls.set(0);
    measuring.set(false);
    let mut live = || {
        if measuring.get() {
            calls.set(calls.get() + 1);
            if calls.get() == binding_final {
                return ControlFlow::Break(StopReason::Cancelled);
            }
        }
        ControlFlow::Continue(())
    };
    let mut work = WorkBudget::new(50_000_000, &mut live);
    let mut proof = capture(&terms, &[root], &fixed, &mut work).expect("same source originals");
    proof.dag.original_clauses[0].0 += 1;
    measuring.set(true);
    assert!(matches!(proof.replay(), Err(Error::Binding)));
    drop(proof);
    assert_eq!(
        work.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}

#[test]
fn original_admission_callback_work_and_storage_are_bulk_costs_not_poll_count() {
    let mut terms = TermStore::new();
    let root = mul_identity(&mut terms);
    let seen_bulk = Cell::new(false);
    let seen_storage = Cell::new(false);
    let mut sink = |units: usize, bytes: usize| {
        if units > 1 {
            seen_bulk.set(true);
        }
        if bytes > 0 {
            seen_storage.set(true);
        }
        Ok(())
    };
    let mut work = WorkBudget::with_admission(50_000_000, &mut sink);
    capture(&terms, &[root], &limits(), &mut work).expect("actual priced source/circuit/search");
    assert!(seen_bulk.get());
    assert!(seen_storage.get());
}

#[test]
fn construction_variable_and_clause_caps_refuse_on_the_same_sticky_original_owner() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let root = app(&mut terms, "and", &[a, b], Sort::Bool);
    for max_vars in [1, 2] {
        let mut limits = limits();
        limits.max_num_vars = max_vars;
        let mut live = || ControlFlow::Continue(());
        let mut work = WorkBudget::new(10_000_000, &mut live);
        assert!(capture(&terms, &[root], &limits, &mut work).is_err());
        assert_eq!(work.charge(0), Err(QueryError::Exhausted));
    }
    let mut limits = limits();
    limits.max_input_clauses = 1;
    let root = terms.mk_bool(false);
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(10_000_000, &mut live);
    assert!(capture(&terms, &[root], &limits, &mut work).is_err());
    assert_eq!(work.charge(0), Err(QueryError::Exhausted));
}
