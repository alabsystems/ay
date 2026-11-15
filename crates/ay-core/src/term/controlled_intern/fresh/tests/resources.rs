// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::original_query::{QueryError, StopReason, WorkBudget};
use crate::time::Instant;
use std::ops::ControlFlow;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

fn measured() -> (usize, usize, usize) {
    let mut store = TermStore::new();
    let (mut work, mut bytes, mut calls) = (0usize, 0usize, 0usize);
    assert!(store
        .try_fresh_bv64_binder_with_progress(&mut |w, b| {
            work = work.checked_add(w).expect("bounded test cost");
            bytes = bytes.checked_add(b).expect("bounded test storage");
            calls += 1;
            true
        })
        .is_ok());
    (work, bytes, calls)
}

#[test]
fn one_short_original_work_refuses_registry_publication_and_stays_refused() {
    let (work, _, _) = measured();
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new((work - 1) as u64, &mut checkpoint);
    let mut store = TermStore::new();
    assert_eq!(
        store.try_fresh_bv64_binder_with_progress(&mut |w, b| budget.admit(w, b).is_ok()),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert!(store.names.is_empty());
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
    assert_eq!(
        store.try_fresh_bv64_binder_with_progress(&mut |w, b| budget.admit(w, b).is_ok()),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert!(store.names.is_empty());
}

#[test]
fn one_short_original_storage_refuses_without_a_registered_handle() {
    let (work, bytes, _) = measured();
    let mut left = bytes - 1;
    let mut owner = |_: usize, b: usize| {
        left = left.checked_sub(b).ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(work as u64, &mut owner);
    let mut store = TermStore::new();
    assert_eq!(
        store.try_fresh_bv64_binder_with_progress(&mut |w, b| budget.admit(w, b).is_ok()),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert!(store.names.is_empty());
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
}

#[test]
fn original_raw_callback_refusal_survives_reset_and_a_second_entry() {
    let raw = Arc::new(AtomicBool::new(true));
    let captured = Arc::clone(&raw);
    let end = Instant::now() + Duration::from_secs(20);
    let mut checkpoint = || {
        if captured.load(Ordering::Acquire) {
            ControlFlow::Break(StopReason::Cancelled)
        } else if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(1_000_000, &mut checkpoint);
    let mut store = TermStore::new();
    assert_eq!(
        store.try_fresh_bv64_binder_with_progress(&mut |w, b| budget.admit(w, b).is_ok()),
        Err(ControlledTermInternError::ResourceLimit)
    );
    raw.store(false, Ordering::Release);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
    assert_eq!(
        store.try_fresh_bv64_binder_with_progress(&mut |w, b| budget.admit(w, b).is_ok()),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(store.var_counter(), 0);
    assert_eq!(store.len(), 2);
}

#[test]
fn same_original_absolute_end_is_not_replaced_by_freshness_search() {
    let end = Instant::now();
    let mut checkpoint = || {
        if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(1_000_000, &mut checkpoint);
    let mut store = TermStore::new();
    for _ in 0..2 {
        assert_eq!(
            store.try_fresh_bv64_binder_with_progress(&mut |w, b| budget.admit(w, b).is_ok()),
            Err(ControlledTermInternError::ResourceLimit)
        );
    }
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
    assert_eq!(store.var_counter(), 0);
}

#[test]
fn post_scratch_final_poll_revokes_a_fully_registered_inert_handle() {
    let (_, _, last_call) = measured();
    let mut calls = 0;
    let mut store = TermStore::new();
    let result = store.try_fresh_bv64_binder_with_progress(&mut |_, _| {
        calls += 1;
        calls != last_call
    });
    assert_eq!(result, Err(ControlledTermInternError::ResourceLimit));
    assert_eq!(calls, last_call);
    assert_eq!(store.var_counter(), 1);
    assert_eq!(store.len(), 3);
    assert!(store.find_var("__ay_range_pin!0").is_some());
}

#[test]
fn owner_latches_constructor_origin_exhaustion_before_any_fresh_retry() {
    let mut store = TermStore::new();
    store.var_counter = u32::MAX;
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(1_000_000, &mut checkpoint);
    assert_eq!(
        store.try_fresh_bv64_binder_with_progress(&mut |w, b| budget.admit(w, b).is_ok()),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(budget.refuse_exhaustion(), QueryError::Exhausted);
    assert_eq!(
        store.try_fresh_bv64_binder_with_progress(&mut |w, b| budget.admit(w, b).is_ok()),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
}

#[test]
fn original_namespace_walk_refuses_between_rows_before_owning_name_copy() {
    let mut store = TermStore::new();
    for n in 0..20 {
        let _ = store.mk_app(Symbol::named(format!("source_{n}")), [], Sort::Bool);
    }
    let mut rows = 0;
    let mut copied = 0;
    let result = store.try_fresh_bv64_binder_with_progress(&mut |work, bytes| {
        copied += bytes;
        if work == 64 {
            rows += 1;
        }
        rows != 3
    });
    assert_eq!(result, Err(ControlledTermInternError::ResourceLimit));
    assert_eq!(rows, 3);
    assert_eq!(copied, 0);
    assert_eq!(store.var_counter(), 0);
    assert!(store.names.is_empty());
}
