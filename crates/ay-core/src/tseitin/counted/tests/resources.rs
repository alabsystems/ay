// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

fn sequence(original: &CountedAdmission) -> Result<()> {
    let (mut terms, distinct, _) = formula(CountedBuiltin::Distinct);
    CountedCnf::encode(&mut terms, &[distinct], original)?.finish()
}

#[test]
fn exact_and_one_short_grants_cover_bridge_rows_and_output_disposal() {
    let original = ample();
    sequence(&original).unwrap();
    let used = original.usage().unwrap();
    for (work, storage, expected) in [
        (used.work_admitted, used.storage_admitted, None),
        (
            used.work_admitted - 1,
            used.storage_admitted,
            Some(CountedAdmissionError::WorkExhausted),
        ),
        (
            used.work_admitted,
            used.storage_admitted - 1,
            Some(CountedAdmissionError::StorageExhausted),
        ),
    ] {
        let original = owner(work, storage);
        let result = sequence(&original);
        if let Some(error) = expected {
            assert_eq!(result, Err(Error::Stopped(error)));
            assert_eq!(original.check(), Err(error));
        } else {
            result.unwrap();
            let usage = original.usage().unwrap();
            assert_eq!(usage.work_remaining, 0);
            assert_eq!(usage.storage_remaining, 0);
        }
    }
}

#[test]
fn fresh_identical_originals_have_identical_receipts() {
    assert_eq!(COUNTED_CNF_WORK_VERSION, 1);
    let a = ample();
    let b = ample();
    sequence(&a).unwrap();
    sequence(&b).unwrap();
    assert_eq!(a.usage().unwrap(), b.usage().unwrap());
}

#[test]
fn zero_work_precedes_empty_and_both_constant_roots() {
    for roots in [0, 1, 2] {
        let mut terms = TermStore::new();
        let root = terms.mk_bool(roots == 1);
        let source = if roots == 0 { Vec::new() } else { vec![root] };
        let original = owner(0, usize::MAX);
        assert!(matches!(
            CountedCnf::encode(&mut terms, &source, &original),
            Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
        ));
    }
}

#[test]
fn interrupted_source_and_bridge_cannot_resume_on_original_owner() {
    let enabled = Arc::new(AtomicBool::new(false));
    let calls = Arc::new(AtomicUsize::new(0));
    let active = enabled.clone();
    let seen = calls.clone();
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1 << 24),
        None,
        Arc::new(move || active.load(Ordering::SeqCst) && seen.fetch_add(1, Ordering::SeqCst) > 40),
    )
    .unwrap();
    let (mut terms, root, _) = formula(CountedBuiltin::Distinct);
    enabled.store(true, Ordering::SeqCst);
    assert!(matches!(
        CountedCnf::encode(&mut terms, &[root], &original),
        Err(Error::Stopped(_))
    ));
    enabled.store(false, Ordering::SeqCst);
    assert!(matches!(
        CountedCnf::encode(&mut terms, &[root], &original),
        Err(Error::Stopped(_))
    ));
}

#[test]
fn output_retains_original_callback_after_tls_and_owner_handle_replacement() {
    let cancelled = Arc::new(AtomicBool::new(false));
    let seen = cancelled.clone();
    let scope = crate::resource::enter_check_stop(Arc::new(move || seen.load(Ordering::SeqCst)));
    let original = ample();
    drop(scope);
    let _replacement = crate::resource::enter_check_stop(Arc::new(|| false));
    let (mut terms, root, _) = formula(CountedBuiltin::Implies);
    let cnf = CountedCnf::encode(&mut terms, &[root], &original).unwrap();
    drop(original);
    cancelled.store(true, Ordering::SeqCst);
    assert!(cnf.check().is_err());
    cancelled.store(false, Ordering::SeqCst);
    assert!(cnf.finish().is_err());
}

#[test]
fn dense_mapping_prices_actual_historical_store_not_only_root() {
    let mut small = TermStore::new();
    let a = small.mk_var("a", Sort::Bool);
    let first = ample();
    CountedCnf::encode(&mut small, &[a], &first)
        .unwrap()
        .finish()
        .unwrap();
    let mut large = TermStore::new();
    let a = large.mk_var("a", Sort::Bool);
    for index in 0..1000 {
        let _ = large.mk_var(format!("unused{index}"), Sort::Bool);
    }
    let second = ample();
    CountedCnf::encode(&mut large, &[a], &second)
        .unwrap()
        .finish()
        .unwrap();
    assert!(second.usage().unwrap().storage_admitted > first.usage().unwrap().storage_admitted);
    assert!(second.usage().unwrap().work_admitted > first.usage().unwrap().work_admitted);
}
