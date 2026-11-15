// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

pub(super) fn check_snapshot(encoder: Tseitin<'_>) -> TseitinResult {
    // The old BV snapshot, plus the existing parallel-annotation getter.
    // transform_all is not an oracle: it can allocate/assert new root literals.
    let expected = TseitinResult::new(
        encoder.all_clauses().to_vec(),
        encoder.term_to_var().clone(),
        encoder.var_to_term().clone(),
        0,
        encoder.num_vars(),
    )
    .with_parallel_proof_annotations(encoder.proof_annotations().map(<[_]>::to_vec));
    let clauses_ptr = encoder.clauses.as_ptr();
    let clauses_capacity = encoder.clauses.capacity();
    let payloads: Vec<_> = encoder
        .clauses
        .iter()
        .map(|clause| clause.0.as_ptr())
        .collect();
    let term_entries: Vec<_> = encoder
        .term_to_var
        .values()
        .map(std::ptr::from_ref)
        .collect();
    let variable_entries: Vec<_> = encoder
        .var_to_term
        .values()
        .map(std::ptr::from_ref)
        .collect();
    let proof_ptr = encoder
        .proof_annotations
        .as_ref()
        .map(|proofs| proofs.as_ptr());

    let result = encoder.into_assertion_result();
    assert_eq!(result.clauses, expected.clauses);
    assert_eq!(result.term_to_var, expected.term_to_var);
    assert_eq!(result.var_to_term, expected.var_to_term);
    assert_eq!(result.root, expected.root);
    assert_eq!(result.num_vars, expected.num_vars);
    assert_eq!(result.clauses.as_ptr(), clauses_ptr);
    assert_eq!(result.clauses.capacity(), clauses_capacity);
    assert_eq!(
        result
            .clauses
            .iter()
            .map(|clause| clause.0.as_ptr())
            .collect::<Vec<_>>(),
        payloads
    );
    assert_eq!(
        result
            .term_to_var
            .values()
            .map(std::ptr::from_ref)
            .collect::<Vec<_>>(),
        term_entries
    );
    assert_eq!(
        result
            .var_to_term
            .values()
            .map(std::ptr::from_ref)
            .collect::<Vec<_>>(),
        variable_entries
    );
    assert_eq!(
        result
            .proof_annotations
            .as_ref()
            .map(|proofs| proofs.as_ptr()),
        proof_ptr
    );
    match (&result.proof_annotations, &expected.proof_annotations) {
        (Some(actual), Some(expected)) => {
            assert_eq!(actual.len(), result.clauses.len());
            for (actual, expected) in actual.iter().zip(expected) {
                match (actual, expected) {
                    (Some(actual), Some(expected)) => {
                        assert_eq!(actual.rule, expected.rule);
                        assert_eq!(actual.source_term, expected.source_term);
                    }
                    (None, None) => {}
                    _ => panic!("changed annotation position"),
                }
            }
        }
        (None, None) => {}
        _ => panic!("changed proof mode"),
    }
    result
}

#[test]
fn moved_snapshot_matches_boolean_semantics_for_every_small_assignment() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let choice = terms.mk_ite(c, a, b);
    let not_c = terms.mk_not(c);
    let independent = terms.mk_or(vec![a, not_c]);
    let mut encoder = Tseitin::new_with_proofs(&terms);
    encoder.assert_term(choice);
    encoder.assert_term(independent);
    let result = check_snapshot(encoder);
    assert!(result.num_vars < 12);
    for input in 0..8u32 {
        let inputs = [
            (a, input & 1 != 0),
            (b, input & 2 != 0),
            (c, input & 4 != 0),
        ];
        let expected = (if inputs[2].1 {
            inputs[0].1
        } else {
            inputs[1].1
        }) && (inputs[0].1 || !inputs[2].1);
        let extends = (0..1u32 << result.num_vars).any(|model| {
            let variable = |index: u32| model & (1u32 << (index - 1)) != 0;
            inputs
                .iter()
                .all(|(term, value)| variable(result.term_to_var[term]) == *value)
                && result.clauses.iter().all(|clause| {
                    clause
                        .0
                        .iter()
                        .any(|literal| variable(literal.unsigned_abs()) == (*literal > 0))
                })
        });
        assert_eq!(extends, expected, "input {input}");
    }
}
