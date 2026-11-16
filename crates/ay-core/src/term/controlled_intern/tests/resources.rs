// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::original_query::{QueryError, StopReason, WorkBudget};
use crate::time::Instant;
use std::ops::ControlFlow;
use std::sync::atomic::{AtomicBool, AtomicU64};
use std::sync::Arc;
use std::time::Duration;

fn measured() -> (usize, usize, usize) {
    let mut store = TermStore::new();
    let term = app(&store);
    let (mut work, mut bytes, mut calls) = (0usize, 0usize, 0usize);
    let result = store.try_intern_with_progress(&term, &Sort::Bool, &mut |w, b| {
        work = work.checked_add(w).expect("finite test work");
        bytes = bytes.checked_add(b).expect("finite test storage");
        calls += 1;
        true
    });
    assert!(result.is_ok());
    (work, bytes, calls)
}

#[test]
fn same_borrowed_work_ledger_refuses_one_short_and_stays_refused() {
    let (work, _, _) = measured();
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new((work - 1) as u64, &mut checkpoint);
    let mut store = TermStore::new();
    let term = app(&store);
    let before = store.len();
    assert_eq!(
        store.try_intern_with_progress(&term, &Sort::Bool, &mut |w, b| budget.admit(w, b).is_ok()),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
    assert_eq!(
        store.try_intern_with_progress(&term, &Sort::Bool, &mut |w, b| budget.admit(w, b).is_ok()),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(store.len(), before);
}

#[test]
fn same_borrowed_storage_owner_refuses_one_short_without_partial_export() {
    let (work, bytes, _) = measured();
    let mut storage_left = bytes - 1;
    let mut admit = |_: usize, storage: usize| {
        storage_left = storage_left
            .checked_sub(storage)
            .ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(work as u64, &mut admit);
    let mut store = TermStore::new();
    let term = app(&store);
    assert_eq!(
        store.try_intern_with_progress(&term, &Sort::Bool, &mut |w, b| budget.admit(w, b).is_ok()),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
    assert_eq!(store.len(), 2);
}

#[test]
fn original_raw_refusal_stays_sticky_after_flag_reset() {
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
    let term = app(&store);
    assert_eq!(
        store.try_intern_with_progress(&term, &Sort::Bool, &mut |w, b| budget.admit(w, b).is_ok()),
        Err(ControlledTermInternError::ResourceLimit)
    );
    raw.store(false, Ordering::Release);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
    assert_eq!(
        store.try_intern_with_progress(&term, &Sort::Bool, &mut |w, b| budget.admit(w, b).is_ok()),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(store.len(), 2);
}

#[test]
fn one_original_absolute_end_is_not_refreshed_between_calls() {
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
    let term = app(&store);
    for _ in 0..2 {
        assert_eq!(
            store.try_intern_with_progress(&term, &Sort::Bool, &mut |w, b| budget
                .admit(w, b)
                .is_ok()),
            Err(ControlledTermInternError::ResourceLimit)
        );
    }
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
    assert_eq!(store.len(), 2);
}

#[test]
fn final_post_scratch_poll_revokes_even_a_committed_data_handle() {
    let (_, _, total_calls) = measured();
    let mut store = TermStore::new();
    let term = app(&store);
    let mut calls = 0;
    let result = store.try_intern_with_progress(&term, &Sort::Bool, &mut |_, _| {
        calls += 1;
        calls != total_calls
    });
    assert_eq!(result, Err(ControlledTermInternError::ResourceLimit));
    assert_eq!(calls, total_calls);
    // The final fence never exports this inert entry as a successful handle.
    assert_eq!(store.len(), 3);
    assert!(store.find_interned(&term).is_some());
}

#[test]
fn collision_bucket_members_are_all_priced_before_equality_selection() {
    let mut store = TermStore::new();
    let term = app(&store);
    let hash = TermStore::compute_hash(&term);
    let t = store.true_term();
    let f = store.false_term();
    store.hash_cons.entry(hash).or_default().extend([t, f]);
    let mut collision_debits = 0;
    let result = store.try_intern_with_progress(&term, &Sort::Bool, &mut |work, _| {
        if work == 256 {
            collision_debits += 1;
        }
        true
    });
    assert!(result.is_ok());
    assert_eq!(collision_debits, 2);
}

#[test]
fn local_term_id_and_birth_stamp_overflow_are_typed_refusals() {
    assert_eq!(
        checked_term_id(u32::MAX as usize),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(
        checked_term_id((u32::MAX - 1) as usize),
        Ok(TermId(u32::MAX - 1))
    );
    let counter = AtomicU64::new(u64::MAX - 1);
    assert_eq!(next_entry_stamp(&counter), Ok(TermEntryStamp(u64::MAX - 1)));
    assert_eq!(
        next_entry_stamp(&counter),
        Err(ControlledTermInternError::ResourceLimit)
    );
    assert_eq!(counter.load(Ordering::Relaxed), u64::MAX);
}

#[test]
fn tombstone_history_uses_actual_table_storage_as_the_probe_bound() {
    let mut store = TermStore::new();
    let checkpoint = store.rollback_checkpoint();
    for n in 0..128 {
        let _ = store.mk_app(Symbol::named(format!("temporary_{n}")), [], Sort::Bool);
    }
    store.rollback_to(checkpoint);
    let table = store.hash_cons.allocation_size();
    let expected = table / size_of::<(u64, Vec<TermId>)>() + 32;
    assert_eq!(store.controlled_slots(), Ok(expected));
    assert!(table > 0);
    let term = app(&store);
    assert!(intern(&mut store, &term, &Sort::Bool).is_ok());
}
