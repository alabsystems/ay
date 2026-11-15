// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn every_inner_replay_poll_and_final_admission_refuse_without_mutation_or_retry() {
    let proof = fixture(BvOp::Xor, 1);
    let before = proof.clone();
    let limits = limits(&proof);
    let mut calls = 0;
    assert_eq!(
        proof.validate_with_limits_and_cancellation(&limits, &mut || {
            calls += 1;
            true
        }),
        Ok(())
    );
    assert!(
        calls > 50 && calls < 2_000,
        "small complete replay: {calls}"
    );
    for refusal in 1..=calls {
        let mut ordinal = 0;
        assert_eq!(
            proof.validate_with_limits_and_cancellation(&limits, &mut || {
                ordinal += 1;
                ordinal != refusal
            }),
            Err(BvBlastValidateError::Cancelled),
            "poll {refusal}/{calls}"
        );
        assert_eq!(ordinal, refusal, "a transient false must remain terminal");
    }
    assert_eq!(proof, before);
    assert_eq!(compare(&proof, &limits), Ok(()));
}

#[test]
fn pre_refusal_is_typed_even_for_a_malformed_certificate() {
    let mut proof = fixture(BvOp::Xor, 1);
    proof.format_version += 1;
    let limits = limits(&proof);
    let mut calls = 0;
    assert_eq!(
        proof.validate_with_limits_and_cancellation(&limits, &mut || {
            calls += 1;
            false
        }),
        Err(BvBlastValidateError::Cancelled)
    );
    assert_eq!(calls, 1);
    assert!(matches!(
        compare(&proof, &limits),
        Err(BvBlastValidateError::UnsupportedFormatVersion { .. })
    ));
}

#[test]
fn caught_callback_panic_keeps_the_same_budget_refused() {
    let proof = fixture(BvOp::Xor, 1);
    let limits = limits(&proof);
    let mut calls = 0;
    let mut callback = || {
        calls += 1;
        if calls == 1 {
            panic!("cancel callback payload");
        }
        true
    };
    let mut budget = ReplayBudget::new(&limits, &mut callback);
    let panic = catch_unwind(AssertUnwindSafe(|| budget.poll())).unwrap_err();
    assert_eq!(
        panic.downcast_ref::<&str>(),
        Some(&"cancel callback payload")
    );
    assert_eq!(budget.poll(), Err(BvBlastValidateError::Cancelled));
    drop(budget);
    assert_eq!(calls, 1);
}

#[test]
fn long_literal_edges_poll_inside_resolution_and_set_comparison() {
    let proof = fixture(BvOp::Xor, 1);
    let limits = limits(&proof);
    let left: Vec<_> = (0..32).map(Lit::pos).collect();
    let mut right = left.clone();
    right[0] = Lit::neg(0);
    let mut calls = 0;
    let mut callback = || {
        calls += 1;
        calls != 12
    };
    let mut budget = ReplayBudget::new(&limits, &mut callback);
    assert_eq!(
        sets::resolve(&left, &right, 0, &mut budget),
        Err(BvBlastValidateError::Cancelled)
    );
    drop(budget);
    assert_eq!(calls, 12);
    let mut calls = 0;
    let mut callback = || {
        calls += 1;
        calls != 12
    };
    let mut budget = ReplayBudget::new(&limits, &mut callback);
    assert_eq!(
        sets::clause_eq(&left, &left, &mut budget),
        Err(BvBlastValidateError::Cancelled)
    );
    drop(budget);
    assert_eq!(calls, 12);
}
