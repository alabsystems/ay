// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_work_and_copy_grant_publish_only_the_complete_prepared_model() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let (units, bytes, _) = costs(&solver, &values);
    let owner = owner(end, units, bytes);
    let output = owner
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .unwrap();
    assert_eq!(output.array_values[&fixture.chain].stores.len(), 2);
    drop(output);
    owner.check().unwrap();
}

#[test]
fn work_one_short_is_typed_sticky_and_not_a_missing_or_default_model() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let (units, bytes, _) = costs(&solver, &values);
    let owner = owner(end, units - 1, bytes);
    assert!(matches!(
        owner.with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work)),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    assert!(owner.clone().with_work(|_| Ok(())).is_err());
    assert_eq!(values[&fixture.written[0]], "concrete");
}

#[test]
fn logical_bytes_one_short_cannot_return_a_partial_success() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let (units, bytes, _) = costs(&solver, &values);
    let owner = owner(end, units, bytes - 1);
    assert!(matches!(
        owner.with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work)),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    assert!(owner.clone().check().is_err());
}

#[test]
fn zero_original_grants_refuse_before_copy_and_never_renew() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    for (units, bytes) in [(0, 128 << 20), (1_000_000, 0)] {
        // Separate refused attempts, not replacement grants for one attempt.
        let owner = owner(end, units, bytes);
        assert!(owner
            .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
            .is_err());
        assert!(owner.clone().with_work(|_| Ok(())).is_err());
    }
}

#[test]
fn repeated_models_and_clones_share_one_original_cumulative_account() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let (units, bytes, _) = costs(&solver, &values);
    let owner = owner(end, 2 * units - 1, 2 * bytes);
    let first = owner
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .unwrap();
    drop(first);
    assert!(owner
        .clone()
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .is_err());
    assert!(owner.with_work(|_| Ok(())).is_err());
}

#[test]
fn late_original_stop_after_real_copies_and_scratch_cleanup_survives_reset() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let (units, bytes, component_polls) = costs(&solver, &values);
    assert!(component_polls > 20);
    let calls = Arc::new(AtomicUsize::new(0));
    let enabled = Arc::new(AtomicBool::new(true));
    let observed = calls.clone();
    let armed = enabled.clone();
    // One initial owner poll; the last component poll is owned::finish AFTER
    // reads/arrays/local per-array scratch have been dropped. Native solve is
    // not performed or claimed by this extraction-only control.
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(units as u64, bytes),
        end,
        Arc::new(move || {
            armed.load(Ordering::Acquire)
                && observed.fetch_add(1, Ordering::AcqRel) + 1 >= component_polls + 1
        }),
    );
    assert!(matches!(
        owner.with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work)),
        Err(OriginalAdmissionError::ObserverStopped)
    ));
    assert_eq!(calls.load(Ordering::Acquire), component_polls + 1);
    enabled.store(false, Ordering::Release);
    assert!(owner
        .clone()
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .is_err());
}

#[test]
fn expired_original_end_is_not_replaced_by_a_relative_extraction_timer() {
    let fixture = Fixture::new();
    let solver = fixture.solver();
    let values = fixture.values();
    let end = Instant::now() - Duration::from_secs(1);
    let owner = owner(end, 1_000_000, 128 << 20);
    assert!(matches!(
        owner.with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work)),
        Err(OriginalAdmissionError::Query(QueryError::Interrupted(
            StopReason::Deadline
        )))
    ));
    assert!(owner.clone().with_work(|_| Ok(())).is_err());
}

#[test]
fn dirty_preparation_is_terminal_refusal_not_an_unpriced_legacy_wrapper() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let solver = ArraySolver::new(&fixture.terms);
    let values = fixture.values();
    let owner = owner(end, 1_000_000, 128 << 20);
    assert!(owner
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .is_err());
    assert!(solver.dirty);
    assert!(owner.clone().check().is_err());
}

#[test]
fn equality_class_preparation_is_refused_without_mutating_cache_or_output() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    solver.eq_adj.insert(fixture.base, Vec::new());
    let values = fixture.values();
    let owner = owner(end, 1_000_000, 128 << 20);
    assert!(owner
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .is_err());
    assert_eq!(solver.eq_adj.len(), 1);
    assert!(owner.clone().check().is_err());
}

#[test]
fn unnamed_nested_array_value_refuses_instead_of_inventing_a_class_name() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let inner_sort = Sort::array(Sort::Int, Sort::Int);
    let outer_sort = Sort::array(Sort::Int, inner_sort.clone());
    let base = terms.mk_var("outer", outer_sort.clone());
    let nested = terms.mk_var("inner", inner_sort);
    let index = terms.mk_var("index", Sort::Int);
    terms.mk_app(Symbol::named("store"), [base, index, nested], outer_sort);
    let mut solver = ArraySolver::new(&terms);
    solver.populate_caches();
    solver.rebuild_assign_indices();
    let mut values = HashMap::default();
    values.insert(index, "0".into());
    let owner = owner(end, 1_000_000, 128 << 20);
    assert!(owner
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .is_err());
    assert!(owner.clone().check().is_err());
}

#[test]
fn malformed_cached_store_cycle_is_bounded_typed_refusal() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    solver.store_cache.insert(
        fixture.chain,
        (fixture.chain, fixture.indices[0], fixture.written[0]),
    );
    let values = fixture.values();
    let owner = owner(end, 1_000_000, 128 << 20);
    assert!(matches!(
        owner.with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work)),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    assert!(owner.clone().check().is_err());
}

#[test]
fn retained_tombstone_backing_is_priced_before_real_model_value_probes() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut fixture = Fixture::new();
    let unused: Vec<_> = (0..256)
        .map(|i| fixture.terms.mk_var(format!("unused{i}"), Sort::Int))
        .collect();
    let mut values = fixture.values();
    values.reserve(256);
    for &id in &unused {
        values.insert(id, "unrelated".into());
    }
    let allocation = values.allocation_size();
    for &id in &unused {
        values.remove(&id);
    }
    assert_eq!(values.allocation_size(), allocation);
    let solver = fixture.solver();
    let units = Cell::new(0usize);
    let mut sink = |work, bytes| {
        assert_eq!(bytes, 0);
        units.set(units.get() + work);
        Ok(())
    };
    let mut work = WorkBudget::with_admission(1_000_000, &mut sink);
    assert_eq!(
        scan::lookup(&values, fixture.written[0], &mut work)
            .unwrap()
            .map(String::as_str),
        Some("concrete")
    );
    drop(work);
    let bound = allocation / std::mem::size_of::<(TermId, String)>() + 32;
    assert_eq!(units.get(), 8 * bound + 512);
    let owner = owner(end, 1_000_000, 128 << 20);
    let output = owner
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .unwrap();
    assert_eq!(output.array_values[&fixture.chain].stores.len(), 2);
    drop(output);
    owner.check().unwrap();
}
