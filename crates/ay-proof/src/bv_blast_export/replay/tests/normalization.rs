// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn actual_clause_normalization_remains_fresh_for_every_source_clause() {
    let proof = fixture(BvOp::Xor, 2);
    let mut checked = 0;
    for (index, clause) in proof.clauses.iter().enumerate() {
        let ClauseProvenance::BitLemmaCnf { lemma } = clause.provenance else {
            continue;
        };
        let mut corrupt = proof.clone();
        // No gate has an empty Tseitin clause. In particular a preceding
        // successful clause's normalized data cannot donate this admission.
        corrupt.clauses[index].lits.clear();
        assert_eq!(
            compare(&corrupt, &limits(&corrupt)),
            Err(BvBlastValidateError::ClauseNotEntailed {
                clause: clause.id,
                lemma,
                kind: proof.bit_lemmas[lemma as usize].kind,
            })
        );
        checked += 1;
    }
    assert!(
        checked > 3,
        "check later clauses after prior successful rows"
    );
}

#[test]
fn fresh_normalization_preserves_permutation_and_duplicate_literal_semantics() {
    let mut proof = fixture(BvOp::Xor, 2);
    let mut changed = 0;
    for clause in &mut proof.clauses {
        if matches!(clause.provenance, ClauseProvenance::BitLemmaCnf { .. }) {
            clause.lits.rotate_left(1);
            if let Some(&literal) = clause.lits.first() {
                clause.lits.push(literal);
                changed += 1;
            }
        }
    }
    assert!(changed > 3);
    let before = proof.clone();
    assert_eq!(compare(&proof, &limits(&proof)), Ok(()));
    assert_eq!(proof, before);
}

#[test]
fn normalization_and_every_candidate_comparison_keep_sticky_cancellation() {
    let proof = fixture(BvOp::Xor, 2);
    let limits = limits(&proof);
    let mut calls = 0;
    {
        let mut callback = || {
            calls += 1;
            true
        };
        let mut budget = ReplayBudget::new(&limits, &mut callback);
        assert_eq!(clauses::validate(&proof, &mut budget), Ok(()));
    }
    assert!(calls > 30 && calls < 2_000);
    for stop in 1..=calls {
        let mut observed = 0;
        {
            let mut callback = || {
                observed += 1;
                observed != stop
            };
            let mut budget = ReplayBudget::new(&limits, &mut callback);
            assert_eq!(
                clauses::validate(&proof, &mut budget),
                Err(BvBlastValidateError::Cancelled),
                "comparison/normalization poll {stop}/{calls}"
            );
            assert_eq!(budget.poll(), Err(BvBlastValidateError::Cancelled));
            assert_eq!(
                clauses::validate(&proof, &mut budget),
                Err(BvBlastValidateError::Cancelled)
            );
        }
        assert_eq!(observed, stop);
    }
}
