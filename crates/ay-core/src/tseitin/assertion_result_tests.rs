// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::Sort;

mod parity;
use parity::check_snapshot;

#[test]
fn assertion_result_moves_existing_storage_with_and_without_proofs() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let choice = terms.mk_ite(c, a, b);
    for with_proofs in [false, true] {
        let mut encoder = if with_proofs {
            Tseitin::new_with_proofs(&terms)
        } else {
            Tseitin::new(&terms)
        };
        encoder.assert_term(choice);
        assert!(!encoder.encoded.is_empty());
        let result = check_snapshot(encoder);
        assert_eq!(result.proof_annotations.is_some(), with_proofs);
        assert_eq!(result.root, 0);
    }
}

#[test]
fn assertion_result_includes_previously_extracted_clauses() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let both = terms.mk_and(vec![a, b]);
    let mut encoder = Tseitin::new_with_proofs(&terms);
    let extracted = encoder.encode_assertion(both);
    assert_ne!(extracted.def_clauses.as_slice(), &[]);
    let all_before = encoder.all_clauses().to_vec();
    assert_eq!(encoder.take_new_clauses().as_slice(), &[]);
    encoder.assert_term(both);
    let activation = encoder.take_new_clauses();
    assert_eq!(activation, vec![CnfClause::unit(extracted.root_lit)]);
    let result = check_snapshot(encoder);
    assert_eq!(result.clauses.len(), all_before.len() + 1);
    assert_eq!(&result.clauses[..all_before.len()], all_before);
    assert_eq!(result.clauses.last(), activation.last());
}

#[test]
fn assertion_result_does_not_activate_encoded_only_assumptions() {
    let mut terms = TermStore::new();
    let asserted = terms.mk_var("asserted", Sort::Bool);
    let assumed = terms.mk_var("assumed", Sort::Bool);
    let mut encoder = Tseitin::new_with_proofs(&terms);
    encoder.assert_term(asserted);
    let assumed_lit = encoder.encode(assumed, true);
    let asserted_lit = encoder.encode(asserted, true);
    let result = check_snapshot(encoder);
    assert_eq!(result.clauses, vec![CnfClause::unit(asserted_lit)]);
    assert_eq!(result.var_for_term(assumed), Some(assumed_lit as u32));
    for assumption_value in [false, true] {
        let value = |literal: CnfLit| {
            let positive_value = if literal.unsigned_abs() == assumed_lit.unsigned_abs() {
                assumption_value
            } else {
                true
            };
            positive_value == (literal > 0)
        };
        assert!(result
            .clauses
            .iter()
            .all(|clause| clause.0.iter().copied().any(value)));
    }
}

#[test]
fn assertion_result_keeps_empty_database_and_reserved_variable_floor() {
    let terms = TermStore::new();
    for with_proofs in [false, true] {
        for floor in [1, 17, u32::MAX] {
            let mut encoder = if with_proofs {
                Tseitin::new_with_proofs(&terms)
            } else {
                Tseitin::new(&terms)
            };
            encoder.ensure_min_next_var(floor);
            let result = check_snapshot(encoder);
            assert_eq!(result.clauses.as_slice(), &[]);
            assert_eq!(result.term_to_var, Default::default());
            assert_eq!(result.var_to_term, Default::default());
            assert_eq!(result.root, 0);
            assert_eq!(result.num_vars, floor - 1);
            assert_eq!(
                result.proof_annotations.as_ref().map(Vec::len),
                with_proofs.then_some(0)
            );
        }
    }
}

#[test]
fn assertion_result_keeps_wide_clause_payload_allocation() {
    let mut terms = TermStore::new();
    let inputs: Vec<_> = (0..4096)
        .map(|index| terms.mk_var(format!("b{index}"), Sort::Bool))
        .collect();
    let disjunction = terms.mk_or(inputs);
    let mut encoder = Tseitin::new_with_proofs(&terms);
    encoder.assert_term(disjunction);
    assert!(encoder
        .all_clauses()
        .iter()
        .any(|clause| clause.0.len() >= 4096));
    check_snapshot(encoder);
}

#[test]
fn assertion_result_preserves_restored_maps_without_inventing_old_clauses() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let mut original = Tseitin::new(&terms);
    original.assert_term(a);
    let previous_literal = original.encode(a, true);
    let state = original.into_state();
    let mut resumed = Tseitin::from_state_with_proofs(&terms, state);
    assert_eq!(resumed.encode(a, true), previous_literal);
    let result = check_snapshot(resumed);
    assert_eq!(result.clauses.as_slice(), &[]);
    assert_eq!(result.var_for_term(a), Some(previous_literal as u32));
    assert_eq!(result.num_vars, previous_literal as u32);
    assert_eq!(result.proof_annotations.as_ref().map(Vec::len), Some(0));
}

#[test]
fn assertion_result_discards_short_and_long_proof_ledgers_wholesale() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    for ledger_len in [0, 2] {
        let mut encoder = Tseitin::new_with_proofs(&terms);
        encoder.assert_term(a);
        let expected_clauses = encoder.all_clauses().to_vec();
        let expected_terms = encoder.term_to_var().clone();
        let expected_vars = encoder.var_to_term().clone();
        let expected_num_vars = encoder.num_vars();
        assert_eq!(expected_clauses.len(), 1);
        encoder.proof_annotations = Some(vec![None; ledger_len]);
        let result = encoder.into_assertion_result();
        assert_eq!(result.clauses, expected_clauses);
        assert_eq!(result.term_to_var, expected_terms);
        assert_eq!(result.var_to_term, expected_vars);
        assert_eq!(result.num_vars, expected_num_vars);
        assert_eq!(result.root, 0);
        assert!(result.proof_annotations.is_none());
    }
}
