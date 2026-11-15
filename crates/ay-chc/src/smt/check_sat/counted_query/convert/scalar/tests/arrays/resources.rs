// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

fn source() -> ChcExpr {
    op(
        ChcOp::Eq,
        vec![
            select(
                store(
                    constant(ChcSort::BitVec(2), ChcExpr::BitVec(0, 2)),
                    ChcExpr::BitVec(1, 2),
                    ChcExpr::BitVec(2, 2),
                ),
                ChcExpr::BitVec(1, 2),
            ),
            ChcExpr::BitVec(2, 2),
        ],
    )
}

fn sequence(source: &ChcExpr, original: &CountedAdmission) -> Result<()> {
    let mut built = convert(source, original)?;
    let result = built.with_scalar_encoding(|encoding| {
        let candidate = encoding.check_scalar_candidate(&model(encoding))?;
        encoding.replay_scalar_candidate(&candidate)
    });
    built.finish()?;
    result
}

#[test]
fn exact_and_one_short_grants_cover_array_rows_original_replay_and_disposal() {
    let source = source();
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
fn retained_observer_cuts_veto_array_encoding_and_replay_without_refresh() {
    let source = source();
    let polls = Arc::new(AtomicUsize::new(0));
    let counted = polls.clone();
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 1 << 30),
        None,
        Arc::new(move || {
            counted.fetch_add(1, Ordering::SeqCst);
            false
        }),
    )
    .unwrap();
    sequence(&source, &original).unwrap();
    let total = polls.load(Ordering::SeqCst);
    assert!(total > 32);
    for cut in (1..=16).map(|part| part * (total - 1) / 16) {
        let observed = Arc::new(AtomicUsize::new(0));
        let counted = observed.clone();
        let original = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000_000, 1 << 30),
            None,
            Arc::new(move || counted.fetch_add(1, Ordering::SeqCst) >= cut),
        )
        .unwrap();
        assert!(matches!(
            sequence(&source, &original),
            Err(Error::Stopped(_))
        ));
        assert!(original.check().is_err());
    }
}

#[test]
fn array_callback_unwind_and_last_capture_drop_cannot_publish_success() {
    struct StopOnDrop(Arc<AtomicBool>);
    impl Drop for StopOnDrop {
        fn drop(&mut self) {
            self.0.store(true, Ordering::SeqCst);
        }
    }
    for panic_instead in [false, true] {
        let stopped = Arc::new(AtomicBool::new(false));
        let observed = stopped.clone();
        let original = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000_000, 1 << 30),
            None,
            Arc::new(move || observed.load(Ordering::SeqCst)),
        )
        .unwrap();
        let source = source();
        let mut built = convert(&source, &original).unwrap();
        let capture = StopOnDrop(stopped.clone());
        let result = built.with_scalar_encoding(move |encoding| {
            let _retained = &capture;
            if panic_instead {
                panic!("test-only array attachment unwind");
            }
            let candidate = encoding.check_scalar_candidate(&model(encoding))?;
            encoding.replay_scalar_candidate(&candidate)
        });
        assert!(stopped.load(Ordering::SeqCst));
        assert!(matches!(result, Err(Error::Stopped(_))));
        stopped.store(false, Ordering::SeqCst);
        assert!(original.check().is_err());
        assert!(built.finish().is_err());
    }
}

#[test]
fn zero_remaining_owner_never_reaches_the_array_attachment_callback() {
    let source = source();
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
    assert!(built.finish().is_err());
}
