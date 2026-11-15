// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn mixed_original_debits_across_clones_reach_exact_grant() {
    let owner = healthy(9, 13);
    let next = owner.clone();
    owner
        .with_work(|work| work.admit(4, 7))
        .expect("first phase");
    next.with_work(|work| work.admit(5, 6))
        .expect("same exact grant");
    assert_eq!(balances(&owner), (0, 0));
    owner.check().expect("zero-debit final poll is allowed");
    assert_eq!(
        next.with_work(|work| work.charge(1)),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(balances(&owner), (0, 0));
    assert!(owner.check().is_err());
}

#[test]
fn paired_work_one_short_does_not_partially_debit_storage() {
    let owner = healthy(2, 8);
    assert_eq!(
        owner.with_work(|work| work.admit(3, 4)),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(balances(&owner), (2, 8));
    assert!(owner.clone().with_work(|work| work.admit(1, 1)).is_err());
}

#[test]
fn paired_copy_one_short_does_not_partially_debit_work() {
    let owner = healthy(8, 2);
    assert_eq!(
        owner.with_work(|work| work.admit(4, 3)),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(balances(&owner), (8, 2));
    assert!(owner.clone().with_work(|work| work.admit(1, 1)).is_err());
}

#[test]
fn storage_only_and_zero_work_do_not_hide_or_renew_a_grant() {
    let owner = healthy(0, 7);
    owner
        .with_work(|work| work.admit(0, 7))
        .expect("storage only");
    assert_eq!(balances(&owner), (0, 0));
    assert_eq!(
        owner.clone().with_work(|work| work.admit(0, 1)),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn ignored_local_exhaustion_is_folded_before_scoped_success() {
    let owner = healthy(10, 10);
    assert_eq!(
        owner.with_work(|work| {
            work.refuse_exhaustion();
            Ok(())
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(
        owner.clone().with_work(|_| Ok(())),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn local_refusal_closes_a_clone_before_the_live_adapter_returns() {
    let owner = healthy(10, 10);
    let clone = owner.clone();
    assert_eq!(
        owner.with_work(|work| {
            work.refuse_exhaustion();
            assert_eq!(
                clone.check(),
                Err(OriginalAdmissionError::Query(QueryError::Exhausted))
            );
            assert!(clone.with_work(|_| Ok(())).is_err());
            Ok(())
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn checked_size_overflow_is_terminal_for_the_original_owner() {
    let owner = healthy(10, 10);
    assert_eq!(
        owner.with_work(|work| {
            let size = usize::MAX
                .checked_mul(2)
                .ok_or_else(|| work.refuse_exhaustion())?;
            work.admit(1, size)
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert!(owner.clone().check().is_err());
}

#[test]
fn genuine_failed_reservation_is_not_a_fresh_adapter_allowance() {
    let owner = healthy(4, usize::MAX);
    let result = owner.with_work(|work| {
        work.admit(1, usize::MAX)?;
        let mut bytes = Vec::<u8>::new();
        bytes
            .try_reserve_exact(usize::MAX)
            .map_err(|_| work.refuse_exhaustion())?;
        Ok(())
    });
    assert_eq!(
        result,
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(balances(&owner), (3, 0));
    assert!(owner.clone().with_work(|_| Ok(())).is_err());
}

#[test]
fn an_explicit_local_structural_refusal_stays_exact_across_clones() {
    let owner = healthy(10, 10);
    let error = QueryError::Invalid("test refused descriptor");
    assert_eq!(
        owner.with_work::<()>(|_| Err(error)),
        Err(OriginalAdmissionError::Query(error))
    );
    assert_eq!(
        owner.clone().check(),
        Err(OriginalAdmissionError::Query(error))
    );
}
