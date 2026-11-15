// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
struct CaptureDrop(Arc<AtomicBool>);
impl Drop for CaptureDrop {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

#[test]
fn digest_callback_capture_cleanup_precedes_the_original_final_fence() {
    let dropped = Arc::new(AtomicBool::new(false));
    let observer = dropped.clone();
    let original = owner_at(
        Instant::now() + Duration::from_secs(20),
        2_000_000,
        8 * 1024 * 1024,
        Arc::new(move || observer.load(Ordering::SeqCst)),
    );
    let capture = CaptureDrop(dropped.clone());
    let source = fixture();
    let result = original.with_work(|work| {
        prepare_normalized_chc_input_with_work(&source, work)?.with_sha256(move |_, _, _, _| {
            assert!(!capture.0.load(Ordering::SeqCst));
            let _retain_whole_capture = &capture;
            Ok(())
        })
    });
    assert!(dropped.load(Ordering::SeqCst));
    assert_eq!(result, Err(OriginalAdmissionError::ObserverStopped));
    dropped.store(false, Ordering::SeqCst);
    assert!(original.check().is_err());
}

#[test]
fn final_stop_reset_does_not_revive_the_original_digest_owner() {
    let stopped = Arc::new(AtomicBool::new(false));
    let observer = stopped.clone();
    let original = owner_at(
        Instant::now() + Duration::from_secs(20),
        2_000_000,
        8 * 1024 * 1024,
        Arc::new(move || observer.load(Ordering::SeqCst)),
    );
    let source = fixture();
    let result = original.with_work(|work| {
        prepare_normalized_chc_input_with_work(&source, work)?.with_sha256(|_, _, _, _| {
            stopped.store(true, Ordering::SeqCst);
            Ok(())
        })
    });
    assert_eq!(result, Err(OriginalAdmissionError::ObserverStopped));
    stopped.store(false, Ordering::SeqCst);
    assert!(consume(&original.clone(), &source).is_err());
}

#[test]
fn caught_digest_callback_panic_discards_capture_before_shared_panic_latch() {
    let dropped = Arc::new(AtomicBool::new(false));
    let capture = CaptureDrop(dropped.clone());
    let original = owner_at(
        Instant::now() + Duration::from_secs(20),
        2_000_000,
        8 * 1024 * 1024,
        Arc::new(|| false),
    );
    let source = fixture();
    let result = original.with_work(|work| {
        prepare_normalized_chc_input_with_work(&source, work)?.with_sha256(move |_, _, _, _| {
            let _retain_whole_capture = &capture;
            panic!("digest callback fixture")
        })
    });
    assert!(dropped.load(Ordering::SeqCst));
    assert_eq!(result, Err(OriginalAdmissionError::OperationPanicked));
    assert!(original.clone().check().is_err());
}

#[test]
fn one_original_deadline_expires_during_digest_callback_then_refuses_after_cleanup() {
    let end = Instant::now() + Duration::from_millis(150);
    let original = owner_at(end, 2_000_000, 8 * 1024 * 1024, Arc::new(|| false));
    let entered = Arc::new(AtomicBool::new(false));
    let seen = entered.clone();
    let dropped = Arc::new(AtomicBool::new(false));
    let capture = CaptureDrop(dropped.clone());
    let source = ChcProblem::new();
    let result = original.with_work(|work| {
        prepare_normalized_chc_input_with_work(&source, work)?.with_sha256(move |_, _, _, _| {
            seen.store(true, Ordering::SeqCst);
            let _retain_whole_capture = &capture;
            while Instant::now() < end {
                std::thread::yield_now();
            }
            Ok(())
        })
    });
    assert!(entered.load(Ordering::SeqCst) && dropped.load(Ordering::SeqCst));
    assert_eq!(
        result,
        Err(OriginalAdmissionError::Query(QueryError::Interrupted(
            ay_core::original_query::StopReason::Deadline
        )))
    );
    assert!(original.check().is_err());
}
