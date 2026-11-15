// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

fn sequence(original: &CountedAdmission) -> Result<TermStore> {
    let mut store = TermStore::try_new_with_admission(original)?;
    let mut builder = CountedTermBuilder::new(&mut store, original)?;
    let a = builder.variable("a", &Sort::bitvec(8))?;
    let b = builder.bitvector(&BigInt::from(1), 8)?;
    let sum = builder.apply(CountedBuiltin::BvAdd, &[a, b])?;
    let _eq = builder.apply(CountedBuiltin::Eq, &[sum, b])?;
    builder.finish()?;
    Ok(store)
}

#[test]
fn exact_logical_work_and_storage_grants_and_one_short_are_terminal() {
    let original = ample();
    drop(sequence(&original).unwrap());
    let used = original.usage().unwrap();
    for (work, bytes, expected) in [
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
        let original = owner(work, bytes);
        let result = sequence(&original);
        if let Some(expected) = expected {
            assert!(matches!(result, Err(CountedTermError::Stopped(error)) if error == expected));
            assert_eq!(original.clone().check(), Err(expected));
        } else {
            drop(result.unwrap());
            assert_eq!(original.usage().unwrap().work_remaining, 0);
            assert_eq!(original.usage().unwrap().storage_remaining, 0);
        }
    }
}

#[test]
fn zero_grants_precede_bootstrap_and_both_literal_decisions() {
    let original = owner(0, usize::MAX);
    assert!(matches!(
        TermStore::try_new_with_admission(&original),
        Err(CountedTermError::Stopped(
            CountedAdmissionError::WorkExhausted
        ))
    ));
    for value in [false, true] {
        let mut store = TermStore::new();
        let original = ample();
        let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
        let remaining = original.usage().unwrap().work_remaining as usize;
        original.admit(remaining, 0).unwrap();
        assert_eq!(
            builder.boolean(value),
            Err(CountedTermError::Stopped(
                CountedAdmissionError::WorkExhausted
            ))
        );
    }
}

#[test]
fn cancellation_during_insertion_is_sticky_after_callback_reset() {
    let enabled = Arc::new(AtomicBool::new(false));
    let calls = Arc::new(AtomicUsize::new(0));
    let captured = enabled.clone();
    let observed = calls.clone();
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1 << 24),
        None,
        Arc::new(move || {
            captured.load(Ordering::SeqCst) && observed.fetch_add(1, Ordering::SeqCst) > 10
        }),
    )
    .unwrap();
    let mut store = TermStore::new();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    enabled.store(true, Ordering::SeqCst);
    assert!(matches!(
        builder.variable("cancelled", &Sort::bitvec(32)),
        Err(CountedTermError::Stopped(_))
    ));
    enabled.store(false, Ordering::SeqCst);
    assert!(matches!(
        builder.boolean(true),
        Err(CountedTermError::Stopped(_))
    ));
    assert!(builder.finish().is_err());
    assert!(original.check().is_err());
}

#[test]
fn original_callback_survives_tls_replacement_and_owner_clone() {
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = stopped.clone();
    let scope =
        crate::resource::enter_check_stop(Arc::new(move || observed.load(Ordering::SeqCst)));
    let original = ample();
    drop(scope);
    let _replacement = crate::resource::enter_check_stop(Arc::new(|| false));
    let mut store = TermStore::new();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    stopped.store(true, Ordering::SeqCst);
    assert!(matches!(
        builder.boolean(false),
        Err(CountedTermError::Stopped(_))
    ));
    stopped.store(false, Ordering::SeqCst);
    assert!(original.clone().check().is_err());
}

#[test]
fn fresh_conversion_sequences_have_identical_versioned_receipts() {
    let first = ample();
    drop(sequence(&first).unwrap());
    let second = ample();
    drop(sequence(&second).unwrap());
    assert_eq!(COUNTED_TERM_WORK_VERSION, 2);
    assert_eq!(first.usage().unwrap(), second.usage().unwrap());
}

fn interrupted_prefix(store: &mut TermStore, original: &CountedAdmission) -> Result<()> {
    let mut builder = CountedTermBuilder::new(store, original)?;
    let a = builder.variable("a", &Sort::Bool)?;
    let no = builder.boolean(false)?;
    let _raw = builder.apply(CountedBuiltin::And, &[a, no])?;
    builder.finish()
}

fn watched_owner(calls: &Arc<AtomicUsize>, stop: usize) -> CountedAdmission {
    let calls = calls.clone();
    CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1 << 24),
        None,
        Arc::new(move || calls.fetch_add(1, Ordering::SeqCst) == stop),
    )
    .unwrap()
}

#[test]
fn every_observed_refusal_boundary_leaves_a_usable_native_producer() {
    let calls = Arc::new(AtomicUsize::new(0));
    let original = watched_owner(&calls, usize::MAX);
    let mut healthy = TermStore::new();
    interrupted_prefix(&mut healthy, &original).unwrap();
    let count = calls.load(Ordering::SeqCst);
    assert!(count > 20);
    for cutoff in 0..count {
        let calls = Arc::new(AtomicUsize::new(0));
        let original = watched_owner(&calls, cutoff);
        let mut store = TermStore::new();
        assert!(matches!(
            interrupted_prefix(&mut store, &original),
            Err(CountedTermError::Stopped(_))
        ));
        assert!(original.check().is_err());
        let yes = store.mk_bool(true);
        let no = store.mk_bool(false);
        let raw = store.mk_app(Symbol::named("and"), [yes, no], Sort::Bool);
        assert_eq!(
            store.mk_app(Symbol::named("and"), [yes, no], Sort::Bool),
            raw
        );
        let var = store.mk_var("resume", Sort::Bool);
        assert_eq!(store.mk_var("resume", Sort::Bool), var);
        for (hash, ids) in &store.hash_cons {
            for id in ids {
                assert_eq!(TermStore::compute_hash(store.get(*id)), *hash);
            }
        }
    }
}

#[test]
fn geometric_native_growth_avoids_quadratic_admission_on_shared_chains() {
    fn cost(count: usize) -> u64 {
        let original = ample();
        let mut store = TermStore::try_new_with_admission(&original).unwrap();
        let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
        let mut previous = builder.variable("p", &Sort::Bool).unwrap();
        for _ in 0..count {
            previous = builder.apply(CountedBuiltin::Not, &[previous]).unwrap();
        }
        builder.finish().unwrap();
        original.usage().unwrap().work_admitted
    }
    let small = cost(128);
    let large = cost(512);
    assert!(large > small);
    assert!(
        large < small * 8,
        "geometric growth plus ordered lookup, not one whole-map scan per node"
    );
}

/// Opening a counted builder over an existing producer store must not
/// re-inspect and re-index every existing term: the store's native
/// hash-cons already indexes them, and counted construction only pays
/// for the buckets it actually touches. Re-indexing the whole store
/// charged ~35 work per existing node before any tactic ran, which
/// refused counted tactics on real-scale stores under the shared
/// functional-work budget.
#[test]
fn builder_construction_does_not_rescan_existing_store() {
    let mut store = TermStore::new();
    let existing_true = store.mk_bool(true);
    for i in 0..20_000i64 {
        store.mk_int(i.into());
    }
    let original = owner(50_000, 1 << 26);
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    // Dedup against a pre-existing term still finds the original id.
    assert_eq!(builder.boolean(true).unwrap(), existing_true);
    builder.finish().unwrap();
}
