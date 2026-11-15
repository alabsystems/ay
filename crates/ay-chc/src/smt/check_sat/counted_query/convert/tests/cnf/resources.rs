// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

fn sequence(source: &ChcExpr, original: &CountedAdmission) -> Result<()> {
    let mut built = convert(source, original)?;
    let result = built.with_cnf(|context, cnf| {
        let root = context.term_for(source)?;
        let literal = cnf.literal_for_term(root)?;
        assert_eq!(cnf.sat_literal_term(literal)?, root);
        context.admission().admit(7, 13)?;
        Ok(())
    });
    built.finish()?;
    result
}

#[test]
fn exact_and_one_short_grants_cover_source_cnf_callback_and_restricted_subsetup() {
    let source = formula();
    let original = ample();
    sequence(&source, &original).unwrap();
    let usage = original.usage().unwrap();
    for (work, bytes, error) in [
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
        match error {
            Some(error) => {
                assert_eq!(result, Err(Error::Stopped(error)));
                assert_eq!(original.check(), Err(error));
            }
            None => {
                result.unwrap();
                assert_eq!(original.usage().unwrap().work_remaining, 0);
                assert_eq!(original.usage().unwrap().storage_remaining, 0);
            }
        }
    }
}

#[test]
fn exhausted_converted_owner_cannot_enter_callback_even_for_true() {
    let source = ChcExpr::Bool(true);
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    let remaining = original.usage().unwrap().work_remaining as usize;
    original.admit(remaining, 0).unwrap();
    let reached = AtomicBool::new(false);
    assert_eq!(
        built.with_cnf(|_, _| {
            reached.store(true, Ordering::SeqCst);
            Ok(())
        }),
        Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
    );
    assert!(!reached.load(Ordering::SeqCst));
}

struct StopOnDrop(Arc<AtomicBool>);
impl Drop for StopOnDrop {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

#[test]
fn callback_capture_cleanup_is_fenced_on_both_success_and_semantic_error() {
    for semantic_error in [false, true] {
        let stopped = Arc::new(AtomicBool::new(false));
        let observed = stopped.clone();
        let original = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000_000, 1 << 28),
            None,
            Arc::new(move || observed.load(Ordering::SeqCst)),
        )
        .unwrap();
        let source = formula();
        let mut built = convert(&source, &original).unwrap();
        let capture = StopOnDrop(stopped.clone());
        let result = built.with_cnf(move |_, _| {
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
    }
}

#[test]
fn original_callback_survives_scope_replacement_after_conversion() {
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = stopped.clone();
    let scope =
        ay_core::resource::enter_check_stop(Arc::new(move || observed.load(Ordering::SeqCst)));
    let source = formula();
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    drop(scope);
    let _replacement = ay_core::resource::enter_check_stop(Arc::new(|| false));
    stopped.store(true, Ordering::SeqCst);
    let reached = AtomicBool::new(false);
    assert!(matches!(
        built.with_cnf(|_, _| {
            reached.store(true, Ordering::SeqCst);
            Ok(())
        }),
        Err(Error::Stopped(_))
    ));
    assert!(!reached.load(Ordering::SeqCst));
    stopped.store(false, Ordering::SeqCst);
    assert!(original.check().is_err());
}
