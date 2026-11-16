// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn work_exact_then_same_owner_clone_cannot_renew_a_second_export() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let (units, bytes) = cost(&solver, &binding, end);
    let admission = owner(units, bytes, end);
    assert_eq!(admitted(&admission, &solver, &binding, end), Ok(Some(())));
    assert_eq!(
        admitted(&admission.clone(), &solver, &binding, end),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(
        admission.check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn work_one_short_latches_before_consumer_and_all_later_attempts() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let (units, bytes) = cost(&solver, &binding, end);
    let admission = owner(units - 1, bytes, end);
    assert_eq!(
        admitted(&admission, &solver, &binding, end),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(
        admitted(&admission.clone(), &solver, &binding, end),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn bytes_one_short_latches_original_copy_owner_without_a_new_grant() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let (units, bytes) = cost(&solver, &binding, end);
    assert!(bytes > 0);
    let admission = owner(units, bytes - 1, end);
    assert_eq!(
        admitted(&admission, &solver, &binding, end),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(
        admission.clone().check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn two_exports_share_exact_cumulative_original_work_and_copy() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let (units, bytes) = cost(&solver, &binding, end);
    let admission = owner(
        units.checked_mul(2).unwrap(),
        bytes.checked_mul(2).unwrap(),
        end,
    );
    for _ in 0..2 {
        assert_eq!(
            admitted(&admission.clone(), &solver, &binding, end),
            Ok(Some(()))
        );
    }
    assert_eq!(
        admitted(&admission, &solver, &binding, end),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn internal_resource_result_latches_even_without_a_refused_sink_offer() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let admission = owner(usize::MAX / 4, usize::MAX / 4, end);
    let completed = Cell::new(false);
    assert_eq!(
        admission.with_work(|work| {
            assert!(matches!(
                solver.with_last_unsat_retained_bundle_for_exact_query_with_work(
                    &binding,
                    end,
                    work,
                    |bundle, _| {
                        assert_ne!(bundle.obligation_assertions(), []);
                        completed.set(true);
                        Err(ProofCheckError::ResourceLimit)
                    },
                ),
                Err(ProofCheckError::ResourceLimit)
            ));
            // Even deliberately ignoring that error cannot make the adapter healthy.
            work.charge(0)
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert!(completed.get());
    assert_eq!(
        admission.clone().check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert!(solver
        .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            &binding,
            end,
            &mut |_, _| Instant::now() < end,
        )
        .unwrap()
        .is_some());
}

#[test]
fn tighter_expired_export_end_latches_original_adapter_without_revival() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let admission = owner(usize::MAX / 4, usize::MAX / 4, end);
    assert_eq!(
        admission.with_work(|work| {
            assert!(matches!(
                solver.with_last_unsat_retained_bundle_for_exact_query_with_work(
                    &binding,
                    Instant::now(),
                    work,
                    |_, _| { panic!("expired export must not reach the consumer") },
                ),
                Err(ProofCheckError::ResourceLimit)
            ));
            work.charge(0)
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(
        admitted(&admission, &solver, &binding, end),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn consumer_cancelled_result_latches_without_guessing_original_stop_cause() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let admission = owner(usize::MAX / 4, usize::MAX / 4, end);
    assert_eq!(
        admission.with_work(|work| {
            assert!(matches!(
                solver.with_last_unsat_retained_bundle_for_exact_query_with_work(
                    &binding,
                    end,
                    work,
                    |_, _| Err(ProofCheckError::Cancelled),
                ),
                Err(ProofCheckError::Cancelled)
            ));
            work.charge(0)
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(
        admission.clone().check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn copy_exact_then_original_clone_cannot_renew_its_byte_balance() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let (units, bytes) = cost(&solver, &binding, end);
    let admission = owner(units.checked_mul(4).unwrap(), bytes, end);
    assert_eq!(admitted(&admission, &solver, &binding, end), Ok(Some(())));
    assert_eq!(
        admitted(&admission.clone(), &solver, &binding, end),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(
        admission.check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}
