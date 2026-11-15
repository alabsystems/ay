// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn same_budget_exact_and_one_short_work_or_bytes_cover_both_producers() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new(Sort::bitvec(8), Shape::Reads);
    let (source, expected) = fixture.prepared();
    let (units, bytes, _) = costs(&source, &fixture.roots, end);
    assert!(units > 0 && units <= UNITS && bytes > 0 && bytes <= BYTES);
    let exact = owner(units, bytes, end);
    let actual = exact
        .with_work(|work| {
            source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
        })
        .unwrap();
    same(&actual, &expected);
    for (u, b) in [
        (units - 1, bytes),
        (units, bytes - 1),
        (0, BYTES),
        (UNITS, 0),
    ] {
        let short = owner(u, b, end);
        assert!(matches!(
            short.with_work(|work| {
                source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
            }),
            Err(OriginalAdmissionError::Query(QueryError::Exhausted))
        ));
        assert!(short.clone().check().is_err());
    }
}

#[test]
fn successful_data_does_not_renew_the_same_cloned_original_budget() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new(Sort::bitvec(8), Shape::Reads);
    let (source, expected) = fixture.prepared();
    let (units, bytes, _) = costs(&source, &fixture.roots, end);
    let original = owner(units, bytes, end);
    let clone = original.clone();
    let actual = original
        .with_work(|work| {
            source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
        })
        .unwrap();
    same(&actual, &expected);
    assert!(clone
        .with_work(|work| {
            source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
        })
        .is_err());
    assert!(original.check().is_err());
    // Already-returned DATA is not a revocable model/token or new authority.
    same(&actual, &expected);
}

#[test]
fn final_composition_zero_poll_preserves_late_cancellation_or_deadline_after_reset() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new(Sort::bitvec(8), Shape::Reads);
    let (source, _) = fixture.prepared();
    let (_, _, last_zero) = costs(&source, &fixture.roots, end);
    assert!(last_zero > 1);
    for reason in [StopReason::Cancelled, StopReason::Deadline] {
        let zeros = Cell::new(0usize);
        let stopped = Cell::new(false);
        let spent = Cell::new((0u64, 0usize));
        let mut sink = |units, bytes| {
            if Instant::now() >= end {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
            let next = (
                spent.get().0.checked_add(units as u64).unwrap(),
                spent.get().1.checked_add(bytes).unwrap(),
            );
            if next.0 > UNITS || next.1 > BYTES {
                return Err(QueryError::Exhausted);
            }
            spent.set(next);
            if units == 0 {
                zeros.set(zeros.get() + 1);
                if zeros.get() == last_zero {
                    stopped.set(true);
                }
            }
            if stopped.get() {
                Err(QueryError::Interrupted(reason))
            } else {
                Ok(())
            }
        };
        let mut work = WorkBudget::with_admission(UNITS, &mut sink);
        assert!(
            matches!(source.try_extract_prepared_euf_array_models_with_budget(
            &fixture.roots, &mut work), Err(QueryError::Interrupted(observed)) if observed == reason)
        );
        assert_eq!(zeros.get(), last_zero);
        stopped.set(false);
        assert_eq!(work.charge(0), Err(QueryError::Interrupted(reason)));
        assert_eq!(zeros.get(), last_zero);
    }
}
