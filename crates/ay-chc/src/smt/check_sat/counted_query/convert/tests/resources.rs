// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

#[test]
fn temporary_u128_conversion_prepays_the_full_first_digit_vector_allocation() {
    for value in [0, 1, u128::from(u64::MAX), u128::MAX] {
        let original = owner(5, 32);
        assert_eq!(
            bitvector_temporary(value, &original).unwrap(),
            num_bigint::BigInt::from(value)
        );
        let usage = original.usage().unwrap();
        assert_eq!(usage.work_admitted, 5);
        assert_eq!(usage.storage_admitted, 32);
        assert_eq!(usage.work_remaining, 0);
        assert_eq!(usage.storage_remaining, 0);
        for (work, bytes, expected) in [
            (4, 32, CountedAdmissionError::WorkExhausted),
            (5, 31, CountedAdmissionError::StorageExhausted),
        ] {
            let short = owner(work, bytes);
            assert_eq!(
                bitvector_temporary(value, &short),
                Err(Error::Stopped(expected))
            );
            assert_eq!(short.check(), Err(expected));
            // Admission is atomic: neither allocation nor work was admitted.
            assert_eq!(short.usage().unwrap().work_admitted, 0);
            assert_eq!(short.usage().unwrap().storage_admitted, 0);
        }
    }
}

#[test]
fn exact_work_and_storage_cover_census_construction_mapping_and_disposal() {
    let source = relation();
    let original = ample();
    convert(&source, &original).unwrap().finish().unwrap();
    let usage = original.usage().unwrap();
    for (work, bytes, refused) in [
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
        let result = convert(&source, &original).and_then(Converted::finish);
        match refused {
            Some(expected) => {
                assert_eq!(result, Err(Error::Stopped(expected)));
                assert_eq!(original.check(), Err(expected));
                assert!(matches!(
                    convert(&ChcExpr::Bool(true), &original),
                    Err(Error::Stopped(_))
                ));
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
fn fresh_complete_conversion_receipts_do_not_depend_on_prior_store_history() {
    let source = relation();
    let first = ample();
    convert(&source, &first).unwrap().finish().unwrap();
    let second = ample();
    convert(&source, &second).unwrap().finish().unwrap();
    assert_eq!(first.usage().unwrap(), second.usage().unwrap());
}

#[test]
fn zero_original_or_spent_post_census_owner_cannot_publish_trivial_terms() {
    for value in [false, true] {
        let source = ChcExpr::Bool(value);
        let empty = owner(0, usize::MAX);
        assert!(matches!(
            convert(&source, &empty),
            Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
        ));
        let original = ample();
        let query = read(&source, &original).unwrap();
        let remaining = original.usage().unwrap().work_remaining as usize;
        original.admit(remaining, 0).unwrap();
        drop(original);
        assert!(matches!(
            query.into_terms(),
            Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
        ));
    }
}

#[test]
fn captured_cancellation_cannot_be_replaced_after_source_admission() {
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = stopped.clone();
    let scope =
        ay_core::resource::enter_check_stop(Arc::new(move || observed.load(Ordering::SeqCst)));
    let original = ample();
    let source = relation();
    let query = read(&source, &original).unwrap();
    drop(scope);
    let _replacement = ay_core::resource::enter_check_stop(Arc::new(|| false));
    stopped.store(true, Ordering::SeqCst);
    assert!(matches!(query.into_terms(), Err(Error::Stopped(_))));
    stopped.store(false, Ordering::SeqCst);
    assert!(original.check().is_err());
}

#[test]
fn mid_construction_callback_refusal_remains_terminal_after_reset() {
    let enabled = Arc::new(AtomicBool::new(false));
    let calls = Arc::new(AtomicUsize::new(0));
    let flag = enabled.clone();
    let count = calls.clone();
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 1 << 28),
        None,
        Arc::new(move || flag.load(Ordering::SeqCst) && count.fetch_add(1, Ordering::SeqCst) == 25),
    )
    .unwrap();
    let source = relation();
    let query = read(&source, &original).unwrap();
    enabled.store(true, Ordering::SeqCst);
    assert!(matches!(query.into_terms(), Err(Error::Stopped(_))));
    assert!(calls.load(Ordering::SeqCst) >= 26);
    enabled.store(false, Ordering::SeqCst);
    assert!(original.clone().check().is_err());
}

#[test]
fn returned_mapping_stays_on_the_original_owner_after_caller_handle_drop() {
    let original = ample();
    let source = relation();
    let built = convert(&source, &original).unwrap();
    original.refuse(CountedAdmissionError::WorkExhausted);
    drop(original);
    let unrelated = ample();
    assert_eq!(
        built.term_for(&source),
        Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
    );
    assert_eq!(
        built.finish(),
        Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
    );
    assert_eq!(unrelated.usage().unwrap().work_admitted, 0);
}

#[test]
fn larger_shared_dags_do_not_pay_for_exponential_tree_expansions() {
    fn cost(count: usize) -> u64 {
        let mut source = Arc::new(var("p", ChcSort::Bool));
        for _ in 0..count {
            source = Arc::new(ChcExpr::Op(ChcOp::And, vec![source.clone(), source]));
        }
        let original = ample();
        convert(&source, &original).unwrap().finish().unwrap();
        original.usage().unwrap().work_admitted
    }
    let small = cost(128);
    let large = cost(512);
    assert!(large > small);
    assert!(large < 8 * small, "{small} -> {large}");
}
