// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use ay_core::original_query::OriginalAdmissionError;
use ay_core::resource::{enter_check_stop, CheckStopScope};
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::Mutex;

struct Payload {
    replacements: u8,
    drops: Arc<AtomicUsize>,
}

impl Drop for Payload {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::SeqCst);
        if self.replacements != 0 {
            panic_any(Self {
                replacements: self.replacements - 1,
                drops: Arc::clone(&self.drops),
            });
        }
        panic!("test final nested payload destructor panic");
    }
}

struct CallbackDrop {
    enabled: Arc<AtomicBool>,
    drops: Arc<AtomicUsize>,
}

impl Drop for CallbackDrop {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::SeqCst);
        assert!(
            !self.enabled.load(Ordering::SeqCst),
            "test final retained callback destructor panic"
        );
    }
}

struct HostileObserver {
    original: CountedAdmission,
    before_seed: u64,
    fired_at: Arc<AtomicU64>,
    slot: Arc<Mutex<Option<CheckStopScope>>>,
    payload_drops: Arc<AtomicUsize>,
    callback: CallbackDrop,
    first: Option<CountedAdmissionError>,
}

impl HostileObserver {
    fn observe(&self) -> bool {
        let work = self.original.usage().unwrap().work_admitted;
        if work <= self.before_seed
            || self
                .fired_at
                .compare_exchange(0, work, Ordering::SeqCst, Ordering::SeqCst)
                .is_err()
        {
            return false;
        }
        let removed = self.slot.lock().unwrap().take();
        drop(removed);
        if let Some(first) = self.first {
            assert_eq!(self.original.refuse(first), first);
        }
        self.callback.enabled.store(true, Ordering::SeqCst);
        // Admission catches A and drops it; with_work catches B and drops it.
        // C escapes both inner boundaries. Only the constructor's outer fence
        // can stop C before unwinding the encoder's final callback capture.
        panic_any(Payload {
            replacements: 1,
            drops: Arc::clone(&self.payload_drops),
        });
    }
}

fn constructor_fault(element: Sort, first: Option<CountedAdmissionError>) {
    // The original owner/closure must NOT retain the later hostile TLS callback.
    let original = ample();
    let (mut terms, root, _) = fixture(&original, element);
    let closure = CountedArrayReadClosure::derive(&mut terms, &[root], &original).unwrap();
    let before_validation = original.usage().unwrap().work_admitted;
    closure.validate_source(&terms).unwrap();
    let after_validation = original.usage().unwrap().work_admitted;
    let validation_work = after_validation - before_validation;
    assert!(validation_work > 0);
    // The constructor repeats validation and new() admits exactly four units.
    // Strictly exceeding this threshold excludes new()'s existing catch fence.
    let before_seed = after_validation + validation_work + 4;
    let fired_at = Arc::new(AtomicU64::new(0));
    let payload_drops = Arc::new(AtomicUsize::new(0));
    let callback_drops = Arc::new(AtomicUsize::new(0));
    let slot = Arc::new(Mutex::new(None::<CheckStopScope>));
    let hostile = HostileObserver {
        original: original.clone(),
        before_seed,
        fired_at: Arc::clone(&fired_at),
        slot: Arc::clone(&slot),
        payload_drops: Arc::clone(&payload_drops),
        callback: CallbackDrop {
            enabled: Arc::new(AtomicBool::new(false)),
            drops: Arc::clone(&callback_drops),
        },
        first,
    };
    let scope = enter_check_stop(Arc::new(move || hostile.observe()));
    *slot.lock().unwrap() = Some(scope);
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        CountedBvEncoder::with_array_reads(&terms, &closure)
    }));
    let expected = first.unwrap_or(CountedAdmissionError::Original(
        OriginalAdmissionError::ObserverPanicked,
    ));
    // Consume every variant before finishing the borrowed closure. A matches!
    // on the Copy error alone can leave a possible encoder alive in outcome.
    let error = match outcome {
        Ok(Err(error)) => error,
        Ok(Ok(encoder)) => {
            encoder.finish().unwrap();
            panic!("array constructor unexpectedly succeeded");
        }
        Err(payload) => std::panic::resume_unwind(payload),
    };
    assert_eq!(error, CountedBvError::Stopped(expected));
    assert_eq!(fired_at.load(Ordering::SeqCst), before_seed + 1);
    assert!(slot.lock().unwrap().is_none());
    assert!(ay_core::resource::current_check_stop().unwrap().is_none());
    assert_eq!(payload_drops.load(Ordering::SeqCst), 2);
    assert_eq!(callback_drops.load(Ordering::SeqCst), 1);
    let refused_usage = original.usage().unwrap();
    assert_eq!(original.check(), Err(expected));
    assert!(matches!(
        closure.finish(),
        Err(ay_arrays::counted_reads::Error::Stopped(error)) if error == expected
    ));
    assert_eq!(original.check(), Err(expected));
    assert_eq!(original.usage().unwrap(), refused_usage);
}

#[test]
fn array_constructor_drains_nested_payloads_before_final_callback_drop() {
    for element in [Sort::Bool, Sort::bitvec(8)] {
        constructor_fault(element, None);
    }
}

#[test]
fn array_constructor_nested_unwind_preserves_earlier_storage_refusal() {
    for element in [Sort::Bool, Sort::bitvec(8)] {
        constructor_fault(element, Some(CountedAdmissionError::StorageExhausted));
    }
}
