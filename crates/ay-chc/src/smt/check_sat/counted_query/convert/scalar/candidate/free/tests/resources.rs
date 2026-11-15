// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{
    CountedAdmissionError, FiniteAdmissionGrant, OriginalAdmissionError,
};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

#[test]
fn exact_and_one_short_receipts_include_free_congruence_model_replay_and_disposal() {
    let source = boolean_source();
    let original = ample();
    sequence(&source, &original).unwrap();
    let usage = original.usage().unwrap();
    for (work, bytes, refusal) in [
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
        if let Some(refusal) = refusal {
            assert_eq!(result, Err(Error::Stopped(refusal)));
            assert_eq!(original.check(), Err(refusal));
        } else {
            result.unwrap();
            let actual = original.usage().unwrap();
            assert_eq!((actual.work_remaining, actual.storage_remaining), (0, 0));
        }
    }
}

#[test]
fn every_candidate_poll_cut_is_terminal_and_never_returns_a_witness() {
    let source = boolean_source();
    let active = Arc::new(AtomicBool::new(false));
    let polls = Arc::new(AtomicUsize::new(0));
    let (enabled, counted) = (active.clone(), polls.clone());
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 1 << 30),
        None,
        Arc::new(move || {
            if enabled.load(Ordering::SeqCst) {
                counted.fetch_add(1, Ordering::SeqCst);
            }
            false
        }),
    )
    .unwrap();
    let mut built = convert(&source, &original).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let assignment = sat_model(encoding);
            active.store(true, Ordering::SeqCst);
            let candidate = encoding.check_scalar_candidate(&assignment)?;
            encoding.replay_scalar_candidate(&candidate)?;
            active.store(false, Ordering::SeqCst);
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
    let total = polls.load(Ordering::SeqCst);
    assert!(total > 20);
    for cut in 0..total {
        candidate_cut(&source, cut);
    }
}

fn candidate_cut(source: &ChcExpr, cut: usize) {
    let active = Arc::new(AtomicBool::new(false));
    let polls = Arc::new(AtomicUsize::new(0));
    let (enabled, counted) = (active.clone(), polls.clone());
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 1 << 30),
        None,
        Arc::new(move || {
            enabled.load(Ordering::SeqCst) && counted.fetch_add(1, Ordering::SeqCst) >= cut
        }),
    )
    .unwrap();
    let mut built = convert(source, &original).unwrap();
    let result = built.with_scalar_encoding(|encoding| {
        let assignment = sat_model(encoding);
        active.store(true, Ordering::SeqCst);
        let result = encoding
            .check_scalar_candidate(&assignment)
            .and_then(|candidate| encoding.replay_scalar_candidate(&candidate));
        active.store(false, Ordering::SeqCst);
        result
    });
    let refusal = CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped);
    assert_eq!(result, Err(Error::Stopped(refusal)), "cut {cut}");
    active.store(false, Ordering::SeqCst);
    let stopped = original.usage().unwrap();
    assert_eq!(original.check(), Err(refusal));
    assert_eq!(built.finish(), Err(Error::Stopped(refusal)));
    let after = original.usage().unwrap();
    assert_eq!(
        (after.work_admitted, after.storage_admitted),
        (stopped.work_admitted, stopped.storage_admitted)
    );
}

#[test]
fn candidate_observer_unwind_and_callback_capture_cleanup_keep_the_first_owner_cause() {
    struct StopOnDrop(Arc<AtomicBool>);
    impl Drop for StopOnDrop {
        fn drop(&mut self) {
            self.0.store(true, Ordering::SeqCst);
        }
    }
    for panic_during_decode in [false, true] {
        let source = boolean_source();
        let stopped = Arc::new(AtomicBool::new(false));
        let active = Arc::new(AtomicBool::new(false));
        let (seen, enabled) = (stopped.clone(), active.clone());
        let original = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000_000, 1 << 30),
            None,
            Arc::new(move || {
                if enabled.load(Ordering::SeqCst) {
                    panic!("test-only candidate observer panic");
                }
                seen.load(Ordering::SeqCst)
            }),
        )
        .unwrap();
        let mut built = convert(&source, &original).unwrap();
        let capture = StopOnDrop(stopped.clone());
        let result = built.with_scalar_encoding(move |encoding| {
            let _retained = &capture;
            let assignment = sat_model(encoding);
            active.store(panic_during_decode, Ordering::SeqCst);
            let candidate = encoding.check_scalar_candidate(&assignment)?;
            encoding.replay_scalar_candidate(&candidate)
        });
        let cause = if panic_during_decode {
            OriginalAdmissionError::ObserverPanicked
        } else {
            OriginalAdmissionError::ObserverStopped
        };
        let refusal = CountedAdmissionError::Original(cause);
        assert_eq!(result, Err(Error::Stopped(refusal)));
        assert!(stopped.load(Ordering::SeqCst));
        stopped.store(false, Ordering::SeqCst);
        assert_eq!(original.check(), Err(refusal));
        assert_eq!(built.finish(), Err(Error::Stopped(refusal)));
    }
}

#[test]
fn completed_total_witness_is_disposed_before_hostile_payload_cleanup() {
    struct Payload(Arc<AtomicUsize>, bool);
    impl Drop for Payload {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
            if self.1 {
                std::panic::panic_any(Self(self.0.clone(), false));
            }
            panic!("test-only final replacement payload");
        }
    }
    for earlier in [None, Some(CountedAdmissionError::StorageExhausted)] {
        let original = ample();
        let source = boolean_source();
        let drops = Arc::new(AtomicUsize::new(0));
        let mut built = convert(&source, &original).unwrap();
        let result = built.with_scalar_encoding(|encoding| -> Result<()> {
            let candidate = encoding.check_scalar_candidate(&sat_model(encoding))?;
            assert_eq!(candidate.arrays.arrays[0].cells.len(), 2);
            encoding.replay_scalar_candidate(&candidate)?;
            if let Some(first) = earlier {
                assert_eq!(original.refuse(first), first);
            }
            std::panic::panic_any(Payload(drops.clone(), true));
        });
        let refusal = earlier.unwrap_or(CountedAdmissionError::Original(
            OriginalAdmissionError::OperationPanicked,
        ));
        assert_eq!(result, Err(Error::Stopped(refusal)));
        assert_eq!(drops.load(Ordering::SeqCst), 2);
        let stopped = original.usage().unwrap();
        assert_eq!(original.check(), Err(refusal));
        assert_eq!(built.finish(), Err(Error::Stopped(refusal)));
        let after = original.usage().unwrap();
        assert_eq!(
            (after.work_admitted, after.storage_admitted),
            (stopped.work_admitted, stopped.storage_admitted)
        );
    }
}
