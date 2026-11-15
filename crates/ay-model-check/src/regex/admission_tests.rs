// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant, OriginalAdmissionError};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

fn owner(work: u64, bytes: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

#[test]
fn membership_scratch_preserves_exact_work_and_storage_boundaries_without_refund() {
    let mut terms = TermStore::new();
    let all = terms.mk_app_structural(Symbol::named("re.all"), &[], Sort::RegLan);
    let paid = owner(1_000_000, 1 << 20);
    assert!(matches(&terms, "abcdefgh", all, 0, |_| unreachable!(), &paid).unwrap());
    let used = paid.usage().unwrap();
    assert!(used.storage_admitted > 0);
    for (limited, expected) in [
        (
            owner(used.work_admitted - 1, 1 << 20),
            CountedAdmissionError::WorkExhausted,
        ),
        (
            owner(1_000_000, used.storage_admitted - 1),
            CountedAdmissionError::StorageExhausted,
        ),
    ] {
        assert!(matches(&terms, "abcdefgh", all, 0, |_| unreachable!(), &limited).is_err());
        assert_eq!(limited.usage().unwrap().refusal, Some(expected));
        assert!(matches(&terms, "", all, 0, |_| unreachable!(), &limited).is_err());
    }
}

#[test]
fn regex_leaf_stop_is_polled_and_cannot_be_retried_away() {
    let mut terms = TermStore::new();
    let literal = terms.mk_string("abc".into());
    let regex = terms.mk_app_structural(Symbol::named("str.to_re"), &[literal], Sort::RegLan);
    let stop = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&stop);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1 << 20),
        None,
        Arc::new(move || observed.load(Ordering::Relaxed)),
    )
    .unwrap();
    assert!(matches(
        &terms,
        "abc",
        regex,
        0,
        |_| {
            stop.store(true, Ordering::Relaxed);
            Ok("abc".into())
        },
        &original
    )
    .is_err());
    stop.store(false, Ordering::Relaxed);
    assert!(matches(&terms, "abc", regex, 0, |_| Ok("abc".into()), &original).is_err());
    assert_eq!(
        original.usage().unwrap().refusal,
        Some(CountedAdmissionError::Original(
            OriginalAdmissionError::ObserverStopped
        ))
    );
    assert!(matches(
        &terms,
        "abc",
        regex,
        0,
        |_| Ok("abc".into()),
        &owner(1_000_000, 1 << 20)
    )
    .unwrap());
}

#[test]
fn nullable_replacement_output_uses_the_same_cumulative_owner() {
    let mut terms = TermStore::new();
    let empty = terms.mk_string(String::new());
    let regex = terms.mk_app_structural(Symbol::named("str.to_re"), &[empty], Sort::RegLan);
    let replacement = "X".repeat(1024);
    let paid = owner(1_000_000, 1 << 20);
    let actual = replace(
        &terms,
        "str.replace_re",
        "abc",
        regex,
        &replacement,
        false,
        0,
        |_| Ok(String::new()),
        &paid,
    )
    .unwrap();
    assert_eq!(actual, format!("{replacement}abc"));
    let used = paid.usage().unwrap();
    let limited = owner(1_000_000, used.storage_admitted - 1);
    assert!(replace(
        &terms,
        "str.replace_re",
        "abc",
        regex,
        &replacement,
        false,
        0,
        |_| Ok(String::new()),
        &limited
    )
    .is_err());
    assert_eq!(
        limited.usage().unwrap().refusal,
        Some(CountedAdmissionError::StorageExhausted)
    );
}
