// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};

use super::*;

fn every<T: std::fmt::Debug + PartialEq>(
    mut operation: impl FnMut(Progress<'_>) -> Result<T, ProofCheckError>,
) {
    let mut total = 0;
    let live = operation(&mut |work, bytes| {
        assert_eq!((work, bytes), (0, 0));
        total += 1;
        true
    });
    for stop in 1..=total {
        let mut calls = 0;
        let result = operation(&mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert!(
            matches!(result, Err(ProofCheckError::ResourceLimit)),
            "stop {stop}: {result:?}"
        );
        assert_eq!(calls, stop);
    }
    assert_eq!(operation(&mut |_, _| true), live);
}

#[test]
fn every_classification_callback_is_terminal_for_cheap_expensive_and_unsupported_inputs() {
    let mut terms = TermStore::new();
    let narrow = terms.mk_var("progress-narrow", Sort::bitvec(4));
    let wide = terms.mk_var("progress-wide", Sort::bitvec(16));
    let narrow_eq = eq(&mut terms, narrow, narrow);
    let wide_eq = eq(&mut terms, wide, wide);
    let unsupported = terms.mk_app(Symbol::named("uf"), [narrow], Sort::Bool);
    let truth = terms.true_term();
    let quantified = terms.mk_forall_with_triggers(vec![], truth, vec![vec![narrow; 5]]);
    let before = serde_json::to_vec(&terms.entries_snapshot()).unwrap();
    for roots in [
        vec![],
        vec![truth],
        vec![narrow_eq],
        vec![wide_eq],
        vec![unsupported],
        vec![quantified],
    ] {
        every(|progress| {
            bv_bitblast_requires_proof_producer_with_progress(&terms, &roots, progress)
        });
    }
    assert_eq!(
        serde_json::to_vec(&terms.entries_snapshot()).unwrap(),
        before
    );
}

#[test]
fn unsupported_collection_is_none_but_refusal_is_never_none() {
    let mut terms = TermStore::new();
    let unsupported = terms.mk_app(Symbol::named("unknown-bool"), [], Sort::Bool);
    let result = controlled(&mut |_, _| true, |poll| {
        bounded_vars(&terms, &[unsupported], poll)
    });
    assert_eq!(result, Ok(None));
    every(|progress| controlled(progress, |poll| bounded_vars(&terms, &[unsupported], poll)));
}

#[test]
fn every_census_callback_refuses_for_empty_success_and_cap_error() {
    let mut terms = TermStore::new();
    let wide = terms.mk_var("census-wide", Sort::bitvec(16));
    let equality = eq(&mut terms, wide, wide);
    for count in [0, 1, 9] {
        let proof = Proof::from_steps(vec![tagged(equality, TheoryLemmaKind::BvBitBlast); count]);
        every(|progress| validate_expensive_bv_budget_with_progress(&proof, &terms, progress));
    }
    let proof = Proof::from_steps(vec![
        evaluate(&mut terms, "extract"),
        ProofStep::Assume(equality),
    ]);
    every(|progress| validate_expensive_bv_budget_with_progress(&proof, &terms, progress));
}

#[test]
fn precancel_precedes_missing_raw_roots_without_producer_fallback() {
    let terms = TermStore::new();
    let mut calls = 0;
    assert_eq!(
        bv_bitblast_requires_proof_producer_with_progress(
            &terms,
            &[TermId::SENTINEL],
            &mut |_, _| {
                calls += 1;
                false
            }
        ),
        Err(ProofCheckError::ResourceLimit),
    );
    assert_eq!(calls, 1);
    let proof = Proof::from_steps(vec![tagged(TermId::SENTINEL, TheoryLemmaKind::BvBitBlast)]);
    assert_eq!(
        validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |_, _| false),
        Err(ProofCheckError::ResourceLimit)
    );
}

#[test]
fn one_caller_allowance_spans_multiple_classification_calls() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("cumulative", Sort::bitvec(4));
    let equality = eq(&mut terms, value, value);
    let mut total = 0;
    bv_bitblast_requires_proof_producer_with_progress(&terms, &[equality], &mut |_, _| {
        total += 1;
        true
    })
    .unwrap();
    let mut used = 0;
    let mut shared = |_, _| {
        used += 1;
        used <= total
    };
    assert_eq!(
        bv_bitblast_requires_proof_producer_with_progress(&terms, &[equality], &mut shared),
        Ok(false)
    );
    assert_eq!(
        bv_bitblast_requires_proof_producer_with_progress(&terms, &[equality], &mut shared),
        Err(ProofCheckError::ResourceLimit)
    );
}

#[test]
fn caught_callback_panic_cannot_become_a_cheap_classification() {
    let mut calls = 0;
    let result = controlled(
        &mut |_, _| {
            calls += 1;
            if calls == 2 {
                std::panic::panic_any(74u32);
            }
            true
        },
        |mut poll| {
            let caught = catch_unwind(AssertUnwindSafe(&mut poll));
            assert_eq!(*caught.unwrap_err().downcast::<u32>().unwrap(), 74);
            assert_eq!(poll(), Err(ProofCheckError::ResourceLimit));
            Ok(false)
        },
    );
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert_eq!(calls, 2);
}

#[test]
fn final_poll_follows_private_scratch_cleanup() {
    struct Scratch<'a>(&'a Cell<bool>);
    impl Drop for Scratch<'_> {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }
    let finished = Cell::new(false);
    let result = controlled(&mut |_, _| !finished.get(), |_| {
        let _scratch = Scratch(&finished);
        Ok(false)
    });
    assert!(finished.get());
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
}
