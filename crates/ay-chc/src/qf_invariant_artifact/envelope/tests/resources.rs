// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_work_and_byte_boundary_one_short_refuses_before_success() {
    let bytes = envelope("one exact payload");
    let (work, storage) = totals(&bytes);
    consume(&owner(work, storage, Arc::new(|| false)), &bytes).unwrap();
    for original in [
        owner(work - 1, storage, Arc::new(|| false)),
        owner(work, storage - 1, Arc::new(|| false)),
    ] {
        assert!(consume(&original, &bytes).is_err());
        assert!(original.check().is_err());
        assert!(consume(&original, &bytes).is_err());
    }
}

#[test]
fn repeated_calls_and_clone_share_one_original_payload_allowance() {
    let bytes = envelope("shared");
    let (work, storage) = totals(&bytes);
    let original = owner(work * 2, storage * 2, Arc::new(|| false));
    let retained = original.clone();
    consume(&original, &bytes).unwrap();
    consume(&retained, &bytes).unwrap();
    assert!(consume(&retained, &bytes).is_err());
    assert!(original.check().is_err());
}

#[test]
fn observed_callback_stop_remains_after_reset_and_adapter_drop() {
    let stopped = Arc::new(AtomicBool::new(false));
    let read_stop = stopped.clone();
    let original = owner(
        1_000_000,
        1_000_000,
        Arc::new(move || read_stop.load(Ordering::SeqCst)),
    );
    let bytes = envelope("true");
    let result = original.with_work(|work| {
        prepare_qf_invariant_envelope_with_work(&bytes, work)
            .map_err(QfEnvelopePreparationError::query_error)?
            .with_envelope(|_, _| {
                stopped.store(true, Ordering::SeqCst);
                Ok(())
            })
    });
    assert!(matches!(
        result,
        Err(OriginalAdmissionError::ObserverStopped)
    ));
    stopped.store(false, Ordering::SeqCst);
    assert!(matches!(
        original.check(),
        Err(OriginalAdmissionError::ObserverStopped)
    ));
    assert!(consume(&original, &bytes).is_err());
}

struct CaptureDrop(Arc<AtomicBool>);
impl Drop for CaptureDrop {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

#[test]
fn final_owner_poll_occurs_after_consumed_callback_capture_cleanup() {
    let dropped = Arc::new(AtomicBool::new(false));
    let observer = dropped.clone();
    let original = owner(
        1_000_000,
        1_000_000,
        Arc::new(move || observer.load(Ordering::SeqCst)),
    );
    let capture = CaptureDrop(dropped.clone());
    let bytes = envelope("true");
    let result = original.with_work(|work| {
        prepare_qf_invariant_envelope_with_work(&bytes, work)
            .map_err(QfEnvelopePreparationError::query_error)?
            .with_envelope(move |_, _| {
                assert!(!capture.0.load(Ordering::SeqCst));
                drop(capture);
                Ok(())
            })
    });
    assert!(dropped.load(Ordering::SeqCst));
    assert!(matches!(
        result,
        Err(OriginalAdmissionError::ObserverStopped)
    ));
}

#[test]
fn consumer_refusal_and_unwind_latch_original_without_retry() {
    let bytes = envelope("true");
    let original = quiet_owner();
    let result = original.with_work(|work| {
        prepare_qf_invariant_envelope_with_work(&bytes, work)
            .map_err(QfEnvelopePreparationError::query_error)?
            .with_envelope(|_, _| Err(QueryError::Invalid("caller refused untrusted model")))
    });
    assert_eq!(
        result,
        Err(OriginalAdmissionError::Query(QueryError::Invalid(
            "caller refused untrusted model"
        )))
    );
    assert!(consume(&original, &bytes).is_err());
    let panic_owner = quiet_owner();
    let result = panic_owner.with_work(|work| {
        prepare_qf_invariant_envelope_with_work(&bytes, work)
            .map_err(QfEnvelopePreparationError::query_error)?
            .with_envelope(|_, _| panic!("caller panic fixture"))
    });
    assert!(matches!(
        result,
        Err(OriginalAdmissionError::OperationPanicked)
    ));
    assert!(panic_owner.check().is_err());
}

#[test]
fn expired_original_end_and_oversized_input_refuse_before_payload() {
    let expired = OriginalAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("fixture instant supports a one-second offset"),
        Arc::new(|| false),
    );
    assert!(consume(&expired, &envelope("true")).is_err());
    let huge = vec![b' '; CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_BYTES + 1];
    let original = quiet_owner();
    let failure =
        original.with_work(
            |work| match prepare_qf_invariant_envelope_with_work(&huge, work) {
                Err(error) => {
                    assert_eq!(error, QfEnvelopePreparationError::TooLarge);
                    Err(error.query_error())
                }
                Ok(value) => value.with_envelope(|_, _| panic!("oversized envelope admitted")),
            },
        );
    assert!(failure.is_err());
    assert!(original.check().is_err());
}
