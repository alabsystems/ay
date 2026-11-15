// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Callback boundaries are refusal points, never partial identity publication.
#![cfg(test)]

use super::*;

type HashFunction =
    fn(&ChcProblem, &mut dyn FnMut() -> bool) -> Result<String, IdentityHashInterrupted>;

const HASH_FUNCTIONS: [HashFunction; 2] = [
    normalized_chc_input_sha256_with_progress,
    ordered_chc_clause_sequence_sha256_with_progress,
];

fn counted(hash: HashFunction, problem: &ChcProblem) -> (String, usize) {
    let mut calls = 0;
    let result = hash(problem, &mut || {
        calls += 1;
        true
    })
    .expect("unlimited callback");
    (result, calls)
}

#[test]
fn initial_refusal_precedes_empty_and_populated_source_traversal() {
    for problem in [ChcProblem::new(), rich_problem()] {
        for hash in HASH_FUNCTIONS {
            let mut calls = 0;
            assert_eq!(
                hash(&problem, &mut || {
                    calls += 1;
                    false
                }),
                Err(IdentityHashInterrupted)
            );
            assert_eq!(calls, 1);
        }
    }
}

#[test]
fn every_callback_including_final_refusal_stops_without_retry_or_hash() {
    let problem = rich_problem();
    for hash in HASH_FUNCTIONS {
        let (expected, total) = counted(hash, &problem);
        assert!(total > 100, "fixture must reach all source phases");
        for refuse_at in 1..=total {
            let mut calls = 0;
            let result = hash(&problem, &mut || {
                calls += 1;
                calls != refuse_at
            });
            assert_eq!(
                result,
                Err(IdentityHashInterrupted),
                "callback {refuse_at}/{total}"
            );
            assert_eq!(calls, refuse_at, "refusal cannot be retried");
        }
        assert_eq!(hash(&problem, &mut || true), Ok(expected));
    }
}

#[test]
fn caller_allowance_is_shared_across_the_two_identity_passes() {
    let problem = rich_problem();
    let (_, first_calls) = counted(HASH_FUNCTIONS[0], &problem);
    let mut remaining = first_calls;
    let mut calls = 0;
    let mut progress = || {
        calls += 1;
        if remaining == 0 {
            false
        } else {
            remaining -= 1;
            true
        }
    };
    assert!(HASH_FUNCTIONS[0](&problem, &mut progress).is_ok());
    assert_eq!(
        HASH_FUNCTIONS[1](&problem, &mut progress),
        Err(IdentityHashInterrupted)
    );
    assert_eq!(calls, first_calls + 1);
}

#[test]
fn hashing_chunks_preserves_bytes_and_refuses_every_chunk_boundary() {
    let bytes = vec![0xa5; HASH_CHUNK_BYTES * 4 + 7];
    let expected = crate::proof_metadata::sha256_hex(&bytes);
    let hash = |progress: &mut dyn FnMut() -> bool| {
        let mut control = Callback(progress);
        let mut digest = Sha256::new();
        update_bytes(&mut digest, &bytes, &mut control)?;
        finish_hash(digest, &mut control)
    };
    let mut total = 0;
    assert_eq!(
        hash(&mut || {
            total += 1;
            true
        }),
        Ok(expected)
    );
    assert_eq!(total, 5 + 1 + 1 + 32 + 1);
    for refuse_at in 1..=total {
        let mut calls = 0;
        assert_eq!(
            hash(&mut || {
                calls += 1;
                calls != refuse_at
            }),
            Err(IdentityHashInterrupted)
        );
        assert_eq!(calls, refuse_at);
    }
}

#[test]
fn nested_unused_declaration_sorts_are_cancellable_before_clauses() {
    let mut sort = ChcSort::Bool;
    for _ in 0..100 {
        sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(sort));
    }
    let mut problem = ChcProblem::new();
    problem.declare_predicate("unused", vec![sort]);
    for hash in HASH_FUNCTIONS {
        let (_, total) = counted(hash, &problem);
        assert!(total > 400);
        let mut calls = 0;
        assert_eq!(
            hash(&problem, &mut || {
                calls += 1;
                calls != 50
            }),
            Err(IdentityHashInterrupted)
        );
        assert_eq!(calls, 50);
    }
}

#[test]
fn repeated_shared_expression_edges_each_reach_a_poll() {
    let mut problem = ChcProblem::new();
    push_raw(
        &mut problem,
        HornClause::query(ClauseBody::constraint(ChcExpr::FuncApp(
            "wide".to_string(),
            ChcSort::Bool,
            vec![Arc::new(ChcExpr::Int(7)); 4096],
        ))),
    );
    for hash in HASH_FUNCTIONS {
        let (_, total) = counted(hash, &problem);
        assert!(total > 8192);
        let mut calls = 0;
        assert_eq!(
            hash(&problem, &mut || {
                calls += 1;
                calls != 4096
            }),
            Err(IdentityHashInterrupted)
        );
        assert_eq!(calls, 4096);
    }
}

#[test]
fn large_single_field_hashes_in_chunks_without_changing_identity() {
    let mut problem = ChcProblem::new();
    let action = problem.declare_action("λ".repeat(HASH_CHUNK_BYTES * 3));
    push_raw(
        &mut problem,
        HornClause::query(ClauseBody::empty()).with_action(action),
    );
    assert_oracle(&problem);
    for hash in HASH_FUNCTIONS {
        let (_, large_calls) = counted(hash, &problem);
        let (_, small_calls) = counted(hash, &ChcProblem::new());
        assert!(large_calls > small_calls + 6);
    }
}
