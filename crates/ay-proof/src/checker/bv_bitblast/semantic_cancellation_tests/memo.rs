// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn bounded_refusal_never_invokes_the_proof_producing_fallback() {
    let (terms, clause) = valid(Lane::BitBlast);
    let mut total = 0;
    semantic_control::run(
        &mut |_, _| {
            total += 1;
            true
        },
        |poll| {
            validate_bv_bitblast_semantics_with_fallback(&terms, ProofId(0), &clause, poll, |_| {
                panic!("bounded theorem must not invoke fallback")
            })
        },
    )
    .unwrap();
    for stop in 1..=total {
        let (fresh, clause) = valid(Lane::BitBlast);
        let mut calls = 0;
        let result = semantic_control::run(
            &mut |_, _| {
                calls += 1;
                calls != stop
            },
            |poll| {
                validate_bv_bitblast_semantics_with_fallback(
                    &fresh,
                    ProofId(0),
                    &clause,
                    poll,
                    |_| panic!("cancellation must never invoke fallback"),
                )
            },
        );
        assert_eq!(result, Err(ProofCheckError::ResourceLimit));
        assert_eq!(calls, stop);
        assert!(!fresh.strict_bv_semantics_validated(&clause));
    }
}

#[test]
fn semantic_memo_hits_still_observe_every_current_call_poll() {
    let (terms, clause) = valid(Lane::BitBlast);
    Lane::BitBlast
        .run(&terms, &clause, &mut |_, _| true)
        .unwrap();
    assert!(terms.strict_bv_semantics_validated(&clause));
    let mut total = 0;
    Lane::BitBlast
        .run(&terms, &clause, &mut |_, _| {
            total += 1;
            true
        })
        .unwrap();
    for stop in 1..=total {
        let mut calls = 0;
        let result = Lane::BitBlast.run(&terms, &clause, &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert_eq!(result, Err(ProofCheckError::ResourceLimit));
        assert_eq!(calls, stop);
        // A refusal need not erase a previously completed semantic fact.
        assert!(terms.strict_bv_semantics_validated(&clause));
    }
}

fn wide_identity() -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("fallback-wide", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), [x, x], Sort::Bool);
    (terms, vec![equality])
}

#[test]
fn ordinary_bounded_error_preserves_fallback_error_and_does_not_memoize() {
    let (terms, clause) = wide_identity();
    let bounded = validate_bounded_clause_semantics(&terms, ProofId(0), &clause).unwrap_err();
    let mut fallback_calls = 0;
    let result = semantic_control::run(&mut |_, _| true, |poll| {
        validate_bv_bitblast_semantics_with_fallback(&terms, ProofId(0), &clause, poll, |_| {
            fallback_calls += 1;
            Err(ProofProducingFailure::Rejected(
                "controlled-test fallback rejection".to_owned(),
            ))
        })
    });
    assert_eq!(fallback_calls, 1);
    assert_eq!(result, Err(ProofCheckError::InvalidTheoryLemma {
        step: ProofId(0),
        reason: format!("bv_bitblast semantic checks failed: bounded checker: {bounded}; proof-producing checker: controlled-test fallback rejection"),
    }));
    assert!(!terms.strict_bv_semantics_validated(&clause));
}

#[test]
fn final_success_refusal_prevents_fallback_memo_insertion_and_allows_fresh_retry() {
    let (terms, clause) = wide_identity();
    let mut total = 0;
    semantic_control::run(
        &mut |_, _| {
            total += 1;
            true
        },
        |poll| {
            validate_bv_bitblast_semantics_with_fallback(&terms, ProofId(0), &clause, poll, |_| {
                Ok(())
            })
        },
    )
    .unwrap();
    assert!(terms.strict_bv_semantics_validated(&clause));
    let (fresh, clause) = wide_identity();
    let mut calls = 0;
    let mut fallback_calls = 0;
    let refused = semantic_control::run(
        &mut |_, _| {
            calls += 1;
            calls != total
        },
        |poll| {
            validate_bv_bitblast_semantics_with_fallback(&fresh, ProofId(0), &clause, poll, |_| {
                fallback_calls += 1;
                Ok(())
            })
        },
    );
    assert_eq!(refused, Err(ProofCheckError::ResourceLimit));
    assert_eq!(calls, total);
    assert_eq!(fallback_calls, 1);
    assert!(!fresh.strict_bv_semantics_validated(&clause));
    semantic_control::run(&mut |_, _| true, |poll| {
        validate_bv_bitblast_semantics_with_fallback(&fresh, ProofId(0), &clause, poll, |_| Ok(()))
    })
    .unwrap();
    assert!(fresh.strict_bv_semantics_validated(&clause));
}
