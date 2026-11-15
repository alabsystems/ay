// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};

fn sequence(source: &ChcExpr, original: &CountedAdmission) -> Result<()> {
    let mut built = convert(source, original)?;
    let result = built.with_scalar_encoding(|encoding| {
        let assignment = model(encoding);
        let candidate = encoding.check_scalar_candidate(&assignment)?;
        encoding.replay_scalar_candidate(&candidate)
    });
    built.finish()?;
    result
}

#[test]
fn exact_and_one_short_grants_cover_attachment_decoding_replay_and_restricted_subsetup() {
    let source = formula();
    let original = ample();
    sequence(&source, &original).unwrap();
    let usage = original.usage().unwrap();
    for (work, bytes, expected) in [
        (usage.work_admitted, usage.storage_admitted, None),
        (
            usage.work_admitted - 1,
            usage.storage_admitted,
            Some(CountedAdmissionError::WorkExhausted),
        ),
        (
            usage.work_admitted,
            usage.storage_admitted - 1,
            Some(CountedAdmissionError::StorageExhausted),
        ),
    ] {
        let original = owner(work, bytes);
        let result = sequence(&source, &original);
        if let Some(error) = expected {
            assert_eq!(result, Err(Error::Stopped(error)));
            assert_eq!(original.check(), Err(error));
        } else {
            result.unwrap();
            let receipt = original.usage().unwrap();
            assert_eq!((receipt.work_remaining, receipt.storage_remaining), (0, 0));
        }
    }
}

#[test]
fn exhausted_original_owner_never_enters_even_the_true_attachment() {
    let source = ChcExpr::Bool(true);
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    original
        .admit(original.usage().unwrap().work_remaining as usize, 0)
        .unwrap();
    let mut reached = false;
    assert_eq!(
        built.with_scalar_encoding(|_| {
            reached = true;
            Ok(())
        }),
        Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
    );
    assert!(!reached);
    assert_eq!(
        built.finish(),
        Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
    );
}

struct StopOnDrop(Arc<AtomicBool>);
impl Drop for StopOnDrop {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

#[test]
fn attachment_callback_capture_disposal_is_fenced_and_refusal_stays_sticky() {
    for semantic_error in [false, true] {
        let stopped = Arc::new(AtomicBool::new(false));
        let observed = stopped.clone();
        let original = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000_000, 1 << 30),
            None,
            Arc::new(move || observed.load(Ordering::SeqCst)),
        )
        .unwrap();
        let source = formula();
        let mut built = convert(&source, &original).unwrap();
        let capture = StopOnDrop(stopped.clone());
        let result = built.with_scalar_encoding(move |_| {
            let _retained = &capture;
            if semantic_error {
                Err(Error::Unsupported)
            } else {
                Ok(())
            }
        });
        assert!(stopped.load(Ordering::SeqCst));
        assert!(matches!(result, Err(Error::Stopped(_))));
        stopped.store(false, Ordering::SeqCst);
        assert!(original.check().is_err());
        assert!(built.finish().is_err());
    }
}

#[test]
fn swallowed_candidate_refusal_and_panicking_handoff_cannot_publish_success() {
    for panic_instead in [false, true] {
        let original = ample();
        let source = formula();
        let mut built = convert(&source, &original).unwrap();
        let result = built.with_scalar_encoding(|encoding| {
            if panic_instead {
                panic!("test-only handoff unwind");
            }
            let assignment = model(encoding);
            original.admit(original.usage().unwrap().work_remaining as usize, 0)?;
            assert!(encoding.check_scalar_candidate(&assignment).is_err());
            Ok(())
        });
        assert!(matches!(result, Err(Error::Stopped(_))));
        assert!(original.check().is_err());
        assert!(built.finish().is_err());
    }
}

#[test]
fn replacing_ambient_control_never_refreshes_the_original_attachment_owner() {
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = stopped.clone();
    let scope =
        ay_core::resource::enter_check_stop(Arc::new(move || observed.load(Ordering::SeqCst)));
    let original = ample();
    let source = formula();
    let mut built = convert(&source, &original).unwrap();
    drop(scope);
    let _replacement = ay_core::resource::enter_check_stop(Arc::new(|| false));
    stopped.store(true, Ordering::SeqCst);
    let mut reached = false;
    assert!(matches!(
        built.with_scalar_encoding(|_| {
            reached = true;
            Ok(())
        }),
        Err(Error::Stopped(_))
    ));
    assert!(!reached);
    stopped.store(false, Ordering::SeqCst);
    assert!(original.check().is_err());
}

#[test]
fn panicking_payload_disposal_preserves_the_original_refusal_after_circuit_cleanup() {
    struct Payload;
    impl Drop for Payload {
        fn drop(&mut self) {
            panic!("test-only payload disposal panic");
        }
    }
    let source = formula();
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    let result = built.with_scalar_encoding::<()>(|_| std::panic::panic_any(Payload));
    let expected = CountedAdmissionError::Original(
        ay_core::original_query::OriginalAdmissionError::OperationPanicked,
    );
    assert_eq!(result, Err(Error::Stopped(expected)));
    assert_eq!(original.check(), Err(expected));
    assert_eq!(built.finish(), Err(Error::Stopped(expected)));
}
