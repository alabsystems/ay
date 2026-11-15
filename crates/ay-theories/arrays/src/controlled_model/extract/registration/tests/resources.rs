// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_original_work_and_bytes_cover_registration_and_complete_model() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let source = ArraySolver::new(&fixture.terms);
    let values = fixture.values();
    let (units, bytes, _) = costs(&source, &values, end);
    let original = owner(end, units, bytes);
    let output = original
        .with_work(|work| source.try_extract_registered_model_with_budget(&values, work))
        .unwrap();
    assert_eq!(output.array_values[&fixture.base].stores.len(), 4);
    assert!(source.dirty && source.assign_dirty && source.select_cache.is_empty());
    drop(output);
    original.check().unwrap();
}

#[test]
fn one_short_work_or_bytes_and_zero_grants_are_typed_sticky_not_partial_models() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let source = ArraySolver::new(&fixture.terms);
    let values = fixture.values();
    let (units, bytes, _) = costs(&source, &values, end);
    for (u, b) in [
        (units - 1, bytes),
        (units, bytes - 1),
        (0, bytes),
        (units, 0),
    ] {
        // Independent negative attempts, not grant renewal of an operation.
        let original = owner(end, u, b);
        assert!(matches!(
            original
                .with_work(|work| source.try_extract_registered_model_with_budget(&values, work)),
            Err(OriginalAdmissionError::Query(QueryError::Exhausted))
        ));
        assert!(original.clone().with_work(|_| Ok(())).is_err());
        assert!(source.select_cache.is_empty());
    }
}

#[test]
fn cloned_owner_repeated_registration_never_renews_the_cumulative_grant() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let source = ArraySolver::new(&fixture.terms);
    let values = fixture.values();
    let (units, bytes, _) = costs(&source, &values, end);
    let original = owner(end, 2 * units - 1, 2 * bytes);
    let first = original
        .with_work(|work| source.try_extract_registered_model_with_budget(&values, work))
        .unwrap();
    drop(first);
    assert!(original
        .clone()
        .with_work(|work| source.try_extract_registered_model_with_budget(&values, work))
        .is_err());
    assert!(original.with_work(|_| Ok(())).is_err());
}

#[test]
fn final_stop_after_real_registration_view_cleanup_is_sticky_after_raw_reset() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let source = ArraySolver::new(&fixture.terms);
    let values = fixture.values();
    let (units, bytes, polls) = costs(&source, &values, end);
    assert!(polls > 30);
    let calls = Arc::new(AtomicUsize::new(0));
    let enabled = Arc::new(AtomicBool::new(true));
    let count = calls.clone();
    let armed = enabled.clone();
    let original = OriginalAdmission::new(
        FiniteAdmissionGrant::new(units as u64, bytes),
        end,
        Arc::new(move || {
            armed.load(Ordering::Acquire) && count.fetch_add(1, Ordering::AcqRel) + 1 >= polls + 1
        }),
    );
    assert!(matches!(
        original.with_work(|work| source.try_extract_registered_model_with_budget(&values, work)),
        Err(OriginalAdmissionError::ObserverStopped)
    ));
    assert_eq!(calls.load(Ordering::Acquire), polls + 1);
    enabled.store(false, Ordering::Release);
    assert!(original
        .clone()
        .with_work(|work| source.try_extract_registered_model_with_budget(&values, work))
        .is_err());
    assert!(source.select_cache.is_empty() && source.dirty);
}

#[test]
fn original_expired_end_refuses_before_constructor_and_cannot_be_replaced() {
    let start = Instant::now();
    let fixture = Fixture::new();
    let source = ArraySolver::new(&fixture.terms);
    let original = owner(start - Duration::from_secs(1), 1_000_000, 128 << 20);
    assert!(matches!(
        original.with_work(
            |work| source.try_extract_registered_model_with_budget(&fixture.values(), work)
        ),
        Err(OriginalAdmissionError::Query(QueryError::Interrupted(
            StopReason::Deadline
        )))
    ));
    assert!(original.clone().check().is_err());
    assert!(source.select_cache.is_empty());
}

#[test]
fn observer_panic_after_registration_is_terminal_across_caller_clones() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let source = ArraySolver::new(&fixture.terms);
    let values = fixture.values();
    let (units, bytes, polls) = costs(&source, &values, end);
    let calls = Arc::new(AtomicUsize::new(0));
    let count = calls.clone();
    let original = OriginalAdmission::new(
        FiniteAdmissionGrant::new(units as u64, bytes),
        end,
        Arc::new(move || {
            if count.fetch_add(1, Ordering::AcqRel) + 1 >= polls {
                panic!("test observer");
            }
            false
        }),
    );
    assert!(matches!(
        original.with_work(|work| source.try_extract_registered_model_with_budget(&values, work)),
        Err(OriginalAdmissionError::ObserverPanicked)
    ));
    assert!(original.clone().check().is_err());
    assert!(source.dirty && source.select_cache.is_empty());
}

#[test]
fn retained_spare_capacity_has_no_rehash_offer_but_keeps_full_backing_probes() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut map: HashMap<TermId, TermId> = HashMap::default();
    map.reserve(64); // Fixture preparation outside the measured method.
    for i in 0..10 {
        map.insert(TermId(i), TermId(i));
    }
    let allocation = map.allocation_size();
    let fresh = 4 * (map.len() + 1) + 32;
    let actual = allocation / size_of::<(TermId, TermId)>() + 32;
    let expected = 16 * fresh + 8 * actual + 530;
    let charged = Cell::new(0usize);
    let bytes = Cell::new(0usize);
    let mut sink = |units, storage| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        charged.set(charged.get().checked_add(units).unwrap());
        bytes.set(bytes.get().checked_add(storage).unwrap());
        if bytes.get() > 128 << 20 {
            return Err(QueryError::Exhausted);
        }
        Ok(())
    };
    let mut work = WorkBudget::with_admission(expected as u64, &mut sink);
    maps::insert(&mut map, TermId(10), TermId(10), &mut work).unwrap();
    assert_eq!(work.remaining(), 0);
    drop(work);
    assert_eq!(charged.get(), expected);
    assert_eq!(map.allocation_size(), allocation);
    assert!(actual > fresh && bytes.get() > 0);
}

#[test]
fn true_growth_prepays_all_collision_reinserts_and_keeps_legacy_bucket_order() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut map: HashMap<TermId, TermId> = HashMap::default();
    map.reserve(3);
    for i in 0..3 {
        map.insert(TermId(i), TermId(i));
    }
    assert_eq!(map.capacity(), map.len());
    let mut legacy = map.clone(); // Unchanged pinned Clone oracle outside WB.
    let old_len = map.len();
    let old_allocation = map.allocation_size();
    let fresh = 4 * (old_len + 1) + 32;
    let charged = Cell::new(0usize);
    let mut sink = |units, _| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        charged.set(charged.get().checked_add(units).unwrap());
        Ok(())
    };
    let mut work = WorkBudget::with_admission(1_000_000, &mut sink);
    maps::insert(&mut map, TermId(3), TermId(3), &mut work).unwrap();
    drop(work);
    legacy.insert(TermId(3), TermId(3));
    let actual = map.allocation_size() / size_of::<(TermId, TermId)>() + 32;
    assert_eq!(
        charged.get(),
        16 * fresh + 8 * actual + 530 + old_len * (8 * fresh + 512)
    );
    assert!(map.allocation_size() > old_allocation);
    assert_eq!(
        map.iter().collect::<Vec<_>>(),
        legacy.iter().collect::<Vec<_>>()
    );
}
