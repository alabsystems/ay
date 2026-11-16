// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_work_and_copy_grant_accepts_the_complete_constituent() {
    let source = model();
    let (units, bytes, _) = costs(&source);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(units as u64, bytes),
        Instant::now() + Duration::from_secs(20),
        Arc::new(|| false),
    );
    let output = owner
        .with_work(|work| source.try_clone_with_budget(work))
        .unwrap();
    assert_eq!(output.array_values, source.array_values);
    owner.check().unwrap();
}

#[test]
fn work_one_short_refuses_and_closes_every_owner_clone() {
    let source = model();
    let (units, bytes, _) = costs(&source);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(units as u64 - 1, bytes),
        Instant::now() + Duration::from_secs(20),
        Arc::new(|| false),
    );
    assert!(matches!(
        owner.with_work(|work| source.try_clone_with_budget(work)),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    assert!(owner.clone().with_work(|_| Ok(())).is_err());
    assert_eq!(source.array_values[&TermId(7)].stores[0].1, "new");
}

#[test]
fn logical_copy_one_short_refuses_and_is_not_a_missing_array() {
    let source = model();
    let (units, bytes, _) = costs(&source);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(units as u64, bytes - 1),
        Instant::now() + Duration::from_secs(20),
        Arc::new(|| false),
    );
    assert!(matches!(
        owner.with_work(|work| source.try_clone_with_budget(work)),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    assert!(owner.clone().check().is_err());
}

#[test]
fn two_models_and_retries_share_one_original_finite_grant() {
    let source = model();
    let (units, bytes, _) = costs(&source);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(units as u64 * 2 - 1, bytes * 2),
        Instant::now() + Duration::from_secs(20),
        Arc::new(|| false),
    );
    assert!(owner
        .with_work(|work| source.try_clone_with_budget(work))
        .is_ok());
    assert!(owner
        .clone()
        .with_work(|work| source.try_clone_with_budget(work))
        .is_err());
    assert!(owner.with_work(|_| Ok(())).is_err());
}

#[test]
fn observed_original_raw_stop_remains_sticky_after_reset() {
    let raw = Arc::new(AtomicBool::new(true));
    let observed = raw.clone();
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(10_000_000, 10_000_000),
        Instant::now() + Duration::from_secs(20),
        Arc::new(move || observed.load(Ordering::Acquire)),
    );
    let source = model();
    assert!(owner
        .with_work(|work| source.try_clone_with_budget(work))
        .is_err());
    raw.store(false, Ordering::Release);
    assert!(owner
        .clone()
        .with_work(|work| source.try_clone_with_budget(work))
        .is_err());
}

#[test]
fn expired_original_deadline_never_becomes_a_new_relative_timer() {
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(10_000_000, 10_000_000),
        Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("a current instant has an earlier representable second"),
        Arc::new(|| false),
    );
    let source = model();
    assert!(matches!(
        owner.with_work(|work| source.try_clone_with_budget(work)),
        Err(OriginalAdmissionError::Query(QueryError::Interrupted(
            StopReason::Deadline
        )))
    ));
    assert!(owner.clone().with_work(|_| Ok(())).is_err());
}

#[test]
fn arbitrary_observer_panic_is_shared_terminal_refusal() {
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(10_000_000, 10_000_000),
        Instant::now() + Duration::from_secs(20),
        Arc::new(|| panic!("test observer")),
    );
    let source = model();
    assert!(matches!(
        owner.with_work(|work| source.try_clone_with_budget(work)),
        Err(OriginalAdmissionError::ObserverPanicked)
    ));
    assert!(owner.clone().check().is_err());
}

#[test]
fn final_zero_debit_poll_revokes_the_unpublished_complete_owned_copy() {
    let source = model();
    let (_, _, expected_polls) = costs(&source);
    let polls = Cell::new(0usize);
    let mut sink = |_, _| {
        polls.set(polls.get() + 1);
        if polls.get() == expected_polls {
            Err(QueryError::Interrupted(StopReason::Cancelled))
        } else {
            Ok(())
        }
    };
    let mut work = WorkBudget::with_admission(10_000_000, &mut sink);
    assert_eq!(
        source.try_clone_with_budget(&mut work).unwrap_err(),
        QueryError::Interrupted(StopReason::Cancelled)
    );
    assert_eq!(
        work.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
    assert_eq!(polls.get(), expected_polls);
}

#[test]
fn recursive_sort_depth_refusal_is_terminal_not_a_default_sort() {
    let mut deep = Sort::Int;
    for _ in 0..56 {
        deep = Sort::Seq(Box::new(deep));
    }
    let source = ArrayInterpretation {
        index_sort: Some(deep),
        ..Default::default()
    };
    healthy(|work| {
        assert_eq!(
            source.try_clone_with_budget(work).unwrap_err(),
            QueryError::Exhausted
        );
        assert_eq!(work.charge(0), Err(QueryError::Exhausted));
    });
}

#[test]
fn typed_nontext_keys_refuse_before_any_owned_storage_request() {
    use num_bigint::BigInt;
    let large = BigInt::from(1u8) << 8192usize;
    for key in [
        ModelCellKey::Bool(false),
        ModelCellKey::BitVec {
            width: 8193,
            value: &large,
        },
    ] {
        let originals = [(
            ModelCellRow {
                key,
                value: "unchanged",
            },
            CellAuthority::Concrete,
        )];
        let bytes = Cell::new(0usize);
        let mut sink = |_, amount| {
            bytes.set(bytes.get() + amount);
            Ok(())
        };
        let mut work = WorkBudget::with_admission(10_000_000, &mut sink);
        assert_eq!(
            ArrayModel::try_from_indexed_rows(input(&originals, &[]), &mut work).unwrap_err(),
            QueryError::Exhausted
        );
        assert_eq!(work.charge(0), Err(QueryError::Exhausted));
        assert_eq!(bytes.get(), 0);
    }
}

#[test]
fn source_spare_hash_capacity_is_not_unpriced_iteration_work() {
    let compact = model();
    let mut spare = model();
    spare.array_values.reserve(4096);
    let (small, _, _) = costs(&compact);
    let (large, _, _) = costs(&spare);
    assert!(large > small);
    let output = healthy(|work| spare.try_clone_with_budget(work)).unwrap();
    assert_eq!(output.array_values, compact.array_values);
}

#[test]
fn checked_capacity_arithmetic_refuses_before_reservation() {
    healthy(|work| {
        assert_eq!(
            owned::reserve_table::<TermId>(usize::MAX, work).unwrap_err(),
            QueryError::Exhausted
        );
        assert_eq!(work.charge(0), Err(QueryError::Exhausted));
    });
}

#[test]
fn real_utf8_copy_frontier_refuses_without_publishing_partial_owned_data() {
    let source = ArrayInterpretation {
        default: Some("x".repeat(4000)),
        ..Default::default()
    };
    let frontier = Cell::new(0usize);
    let mut sink = |units, _| {
        if units == 132 {
            frontier.set(frontier.get() + 1);
        }
        if frontier.get() == 3 {
            Err(QueryError::Interrupted(StopReason::Cancelled))
        } else {
            Ok(())
        }
    };
    let mut work = WorkBudget::with_admission(10_000_000, &mut sink);
    assert_eq!(
        source.try_clone_with_budget(&mut work).unwrap_err(),
        QueryError::Interrupted(StopReason::Cancelled)
    );
    assert_eq!(
        work.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
    assert_eq!(frontier.get(), 3);
    assert_eq!(source.default.as_ref().unwrap().len(), 4000);
}

#[test]
fn indexed_construction_work_and_storage_one_short_refuse_the_whole_result() {
    let original = [(row("key", "old"), CellAuthority::Soft)];
    let observations = [row("key", "committed"), row("other", "second")];
    let totals = Cell::new((0usize, 0usize));
    let mut sink = |units, bytes| {
        let (w, b) = totals.get();
        totals.set((w + units, b + bytes));
        Ok(())
    };
    let mut work = WorkBudget::with_admission(10_000_000, &mut sink);
    let accepted =
        ArrayModel::try_from_indexed_rows(input(&original, &observations), &mut work).unwrap();
    assert_eq!(accepted.array_values[&TermId(7)].stores[0].1, "committed");
    drop(accepted);
    let (units, bytes) = totals.get();
    for (limit, storage) in [(units - 1, bytes), (units, bytes - 1)] {
        let owner = OriginalAdmission::new(
            FiniteAdmissionGrant::new(limit as u64, storage),
            Instant::now() + Duration::from_secs(20),
            Arc::new(|| false),
        );
        assert!(matches!(
            owner.with_work(|work| ArrayModel::try_from_indexed_rows(
                input(&original, &observations),
                work
            )),
            Err(OriginalAdmissionError::Query(QueryError::Exhausted))
        ));
        assert!(owner.clone().with_work(|_| Ok(())).is_err());
    }
}
