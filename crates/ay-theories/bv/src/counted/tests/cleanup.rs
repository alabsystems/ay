// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use ay_core::original_query::OriginalAdmissionError;
use ay_core::resource::{enter_check_stop, CheckStopScope};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Mutex;

struct DropBomb {
    drops: Arc<AtomicUsize>,
    enabled: Arc<AtomicBool>,
}

impl Drop for DropBomb {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::SeqCst);
        assert!(
            !self.enabled.load(Ordering::SeqCst),
            "test captured callback destructor panic"
        );
    }
}

fn drop_scope(drops: &Arc<AtomicUsize>, enabled: &Arc<AtomicBool>) -> CheckStopScope {
    let bomb = DropBomb {
        drops: Arc::clone(drops),
        enabled: Arc::clone(enabled),
    };
    enter_check_stop(Arc::new(move || {
        let _keep_entire_capture = &bomb;
        false
    }))
}

fn stopped(cause: OriginalAdmissionError) -> CountedBvError {
    CountedBvError::Stopped(CountedAdmissionError::Original(cause))
}

#[test]
fn finish_polls_encoder_only_callback_after_its_tls_scope_was_removed() {
    let original = ample();
    let cancelled = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&cancelled);
    let scope = enter_check_stop(Arc::new(move || observed.load(Ordering::SeqCst)));
    let terms = TermStore::new();
    let encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    drop(scope);
    cancelled.store(true, Ordering::SeqCst);
    assert_eq!(
        encoder.finish(),
        Err(stopped(OriginalAdmissionError::ObserverStopped))
    );
    cancelled.store(false, Ordering::SeqCst);
    assert_eq!(
        original.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::ObserverStopped
        ))
    );
    assert!(CountedBvEncoder::new(&terms, &original).is_err());
}

#[test]
fn healthy_finish_catches_final_callback_destructor_and_drops_it_once() {
    let original = ample();
    let drops = Arc::new(AtomicUsize::new(0));
    let enabled = Arc::new(AtomicBool::new(false));
    let scope = drop_scope(&drops, &enabled);
    let terms = TermStore::new();
    let encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    drop(scope);
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    enabled.store(true, Ordering::SeqCst);
    assert_eq!(
        encoder.finish(),
        Err(stopped(OriginalAdmissionError::OperationPanicked))
    );
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    assert_eq!(
        original.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::OperationPanicked
        ))
    );
}

#[test]
fn finish_admission_exhaustion_still_catches_cleanup_and_keeps_first_cause() {
    let original = owner(4, 1 << 20);
    let drops = Arc::new(AtomicUsize::new(0));
    let enabled = Arc::new(AtomicBool::new(false));
    let scope = drop_scope(&drops, &enabled);
    let terms = TermStore::new();
    let encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    drop(scope);
    assert_eq!(original.usage().unwrap().work_remaining, 0);
    enabled.store(true, Ordering::SeqCst);
    assert_eq!(
        encoder.finish(),
        Err(CountedBvError::Stopped(
            CountedAdmissionError::WorkExhausted
        ))
    );
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    assert_eq!(original.check(), Err(CountedAdmissionError::WorkExhausted));
}

#[test]
fn refused_with_work_entry_cannot_skip_owned_callback_cleanup() {
    let original = ample();
    let drops = Arc::new(AtomicUsize::new(0));
    let enabled = Arc::new(AtomicBool::new(false));
    let scope = drop_scope(&drops, &enabled);
    let terms = TermStore::new();
    let encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    drop(scope);
    let first = CountedAdmissionError::StorageExhausted;
    assert_eq!(original.refuse(first), first);
    enabled.store(true, Ordering::SeqCst);
    let before = original.usage().unwrap();
    assert_eq!(encoder.finish(), Err(CountedBvError::Stopped(first)));
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    assert_eq!(original.usage().unwrap(), before);
    assert_eq!(original.check(), Err(first));
}

#[test]
fn operation_and_restricted_subsetup_panics_are_caught_separately_without_double_panic() {
    let original = ample();
    let drops = Arc::new(AtomicUsize::new(0));
    let enabled = Arc::new(AtomicBool::new(false));
    let bomb = DropBomb {
        drops: Arc::clone(&drops),
        enabled: Arc::clone(&enabled),
    };
    let operation_panics = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&operation_panics);
    let scope = enter_check_stop(Arc::new(move || {
        let _keep_entire_capture = &bomb;
        assert!(!observed.load(Ordering::SeqCst), "test callback panic");
        false
    }));
    let terms = TermStore::new();
    let encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    drop(scope);
    enabled.store(true, Ordering::SeqCst);
    operation_panics.store(true, Ordering::SeqCst);
    assert_eq!(
        encoder.finish(),
        Err(stopped(OriginalAdmissionError::OperationPanicked))
    );
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    operation_panics.store(false, Ordering::SeqCst);
    assert_eq!(
        original.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::OperationPanicked
        ))
    );
}

#[test]
fn constructor_refusal_drops_a_self_uninstalled_callback_inside_cleanup_fence() {
    let original = ample();
    let observed_owner = original.clone();
    let drops = Arc::new(AtomicUsize::new(0));
    let bomb = DropBomb {
        drops: Arc::clone(&drops),
        enabled: Arc::new(AtomicBool::new(true)),
    };
    let scope_slot = Arc::new(Mutex::new(None::<CheckStopScope>));
    let observed_slot = Arc::clone(&scope_slot);
    let scope = enter_check_stop(Arc::new(move || {
        let _keep_entire_capture = &bomb;
        if observed_owner.usage().unwrap().work_admitted == 0 {
            return false;
        }
        // Construction's first debit has completed and EncodingControl has
        // captured this callback before new() performs its validation fence.
        let removed = observed_slot.lock().unwrap().take();
        drop(removed);
        true
    }));
    *scope_slot.lock().unwrap() = Some(scope);
    let terms = TermStore::new();
    let result = CountedBvEncoder::new(&terms, &original);
    assert!(matches!(
        result,
        Err(CountedBvError::Stopped(CountedAdmissionError::Original(
            OriginalAdmissionError::ObserverStopped
        )))
    ));
    assert!(scope_slot.lock().unwrap().is_none());
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    assert!(ay_core::resource::current_check_stop().unwrap().is_none());
    assert_eq!(
        original.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::ObserverStopped
        ))
    );
}
