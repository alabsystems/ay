// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn original_owner_refuses_before_any_missing_source_read() {
    let terms = TermStore::new();
    let mut calls = 0;
    let outcome = super::super::super::validate_fp_to_bv(
        &terms,
        ProofId(0),
        &[TermId::SENTINEL],
        FpOp::IsNaN,
        &mut |_, _| {
            calls += 1;
            false
        },
    );
    assert!(matches!(outcome, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(calls, 1);
}

#[test]
fn final_original_owner_observation_dominates_a_valid_symbolic_schema() {
    let mut f = Fixture::new(11, 53);
    let theorem = f.theorem(FpOp::IsNaN);
    let mut healthy_calls = 0;
    super::super::super::validate_fp_to_bv(
        &f.terms,
        ProofId(0),
        &[theorem],
        FpOp::IsNaN,
        &mut |_, _| {
            healthy_calls += 1;
            true
        },
    )
    .expect("healthy schema");
    let mut calls = 0;
    let outcome = super::super::super::validate_fp_to_bv(
        &f.terms,
        ProofId(0),
        &[theorem],
        FpOp::IsNaN,
        &mut |_, _| {
            calls += 1;
            calls < healthy_calls
        },
    );
    assert!(matches!(outcome, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(calls, healthy_calls);
}

#[test]
fn borrowed_all_ones_walk_charges_original_owner_per_limb() {
    let mut f = Fixture::new(8320, 24);
    let theorem = f.theorem(FpOp::IsNaN);
    let mut remaining = 250usize;
    let outcome = super::super::super::validate_fp_to_bv(
        &f.terms,
        ProofId(0),
        &[theorem],
        FpOp::IsNaN,
        &mut |work, _| match remaining.checked_sub(work) {
            Some(next) => {
                remaining = next;
                true
            }
            None => false,
        },
    );
    assert!(matches!(outcome, Err(ProofCheckError::ResourceLimit)));
}

#[test]
fn negative_census_also_observes_the_same_original_owner_at_exit() {
    let mut f = Fixture::new(8, 24);
    let theorem = f.theorem(FpOp::IsNaN);
    let mut healthy_calls = 0;
    let rejected = super::super::super::validate_fp_to_bv(
        &f.terms,
        ProofId(0),
        &[theorem],
        FpOp::Add,
        &mut |_, _| {
            healthy_calls += 1;
            true
        },
    );
    assert!(matches!(
        rejected,
        Err(ProofCheckError::InvalidTheoryLemma { .. })
    ));
    let mut calls = 0;
    let outcome = super::super::super::validate_fp_to_bv(
        &f.terms,
        ProofId(0),
        &[theorem],
        FpOp::Add,
        &mut |_, _| {
            calls += 1;
            calls < healthy_calls
        },
    );
    assert!(matches!(outcome, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(calls, healthy_calls);
}
