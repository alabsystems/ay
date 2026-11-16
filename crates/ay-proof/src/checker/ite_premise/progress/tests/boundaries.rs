// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn flattening_stops_at_exactly_depth_eight() {
    let mut values = entries();
    let not_c = append(&mut values, TermData::Not(C));
    let mut nested = vec![T];
    for _ in 0..9 {
        let next = app(&mut values, "or", &[nested[nested.len() - 1]]);
        nested.push(next);
    }
    let leaf_form = app(&mut values, "or", &[not_c, T]);
    let stopped_form = app(&mut values, "or", &[not_c, nested[1]]);
    let terms = store(values);
    compare(&terms, leaf_form, &[(C, nested[8], E)], true);
    compare(&terms, leaf_form, &[(C, nested[9], E)], false);
    compare(&terms, stopped_form, &[(C, nested[9], E)], true);
}

#[test]
fn assumed_disjunction_is_not_recursively_flattened() {
    let mut values = entries();
    let not_c = append(&mut values, TermData::Not(C));
    let nested = app(&mut values, "or", &[T, X]);
    let branch = app(&mut values, "or", &[nested, E]);
    let flat = app(&mut values, "or", &[not_c, T, X, E]);
    let unflattened = app(&mut values, "or", &[not_c, nested, E]);
    let terms = store(values);
    compare(&terms, flat, &[(C, branch, X)], true);
    compare(&terms, unflattened, &[(C, branch, X)], false);
}

#[test]
fn every_accessed_missing_handle_fails_typed() {
    let mut values = entries();
    let missing = TermId::SENTINEL;
    let bad_literal = app(&mut values, "or", &[missing]);
    let bad_condition = app(&mut values, "and", &[missing]);
    let bad_branch = app(&mut values, "or", &[missing]);
    let bad_negation = append(&mut values, TermData::Not(missing));
    let terms = store(values);
    let cases = [
        (missing, ITE),
        (X, (C, missing, E)),
        (X, (missing, T, E)),
        (X, (C, T, missing)),
        (bad_literal, ITE),
        (X, (bad_condition, T, E)),
        (X, (C, bad_branch, E)),
        (bad_negation, ITE),
    ];
    for (assumed, ite) in cases {
        let result = assumed_is_authored_bool_ite_consequence_with_progress(
            &terms,
            assumed,
            &[ite],
            &mut |_, _| true,
        );
        assert!(matches!(
            result,
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
    }
}

#[test]
fn empty_registry_and_success_keep_short_circuit_source_access() {
    let mut values = entries();
    let (then_form, _) = branches(&mut values);
    let terms = store(values);
    compare(&terms, TermId::SENTINEL, &[], false);
    let result = assumed_is_authored_bool_ite_consequence_with_progress(
        &terms,
        then_form,
        &[ITE, (TermId::SENTINEL, TermId::SENTINEL, TermId::SENTINEL)],
        &mut |_, _| true,
    );
    assert_eq!(result, Ok(true));
}

#[test]
fn repeated_dag_edges_are_charged_instead_of_deduplicated() {
    let mut values = entries();
    let not_c = append(&mut values, TermData::Not(C));
    let mut branch = T;
    for _ in 0..8 {
        branch = app(&mut values, "or", &[branch, branch]);
    }
    let assumed = app(&mut values, "or", &[not_c, T]);
    let terms = store(values);
    let mut work = 0;
    let mut bytes = 0;
    let result = assumed_is_authored_bool_ite_consequence_with_progress(
        &terms,
        assumed,
        &[(C, branch, E)],
        &mut |amount, allocation| {
            work += amount;
            bytes += allocation;
            true
        },
    );
    assert_eq!(result, Ok(true));
    assert!(work >= 511, "all unfolded visits must be priced");
    assert!(bytes >= 256 * (size_of::<TermId>() + 1));
    compare(&terms, assumed, &[(C, branch, E)], true);
}
