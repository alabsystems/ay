// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for exact recursively finite Bool/BV array source authentication.

use ay_core::{Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;

use super::{authenticate_bool_bv_unsat_query, BoolBvUnsatAuthenticationError};

fn raw_select(terms: &mut TermStore, array: TermId, index: TermId, result_sort: Sort) -> TermId {
    terms.mk_app(Symbol::named("select"), [array, index], result_sort)
}

fn raw_store(
    terms: &mut TermStore,
    array: TermId,
    index: TermId,
    value: TermId,
    array_sort: Sort,
) -> TermId {
    terms.mk_app(Symbol::named("store"), [array, index, value], array_sort)
}

fn raw_equality(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool)
}

fn raw_disequality(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    let equality = raw_equality(terms, lhs, rhs);
    terms.mk_not_raw(equality)
}

#[test]
fn authenticates_bool_index_bool_leaf_store_select() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Bool);
    let array = terms.mk_var("bool_array", array_sort.clone());
    let index = terms.mk_var("bool_index", Sort::Bool);
    let value = terms.mk_bool(true);
    let stored = raw_store(&mut terms, array, index, value, array_sort.clone());
    let read = raw_select(&mut terms, stored, index, Sort::Bool);
    let contradiction = terms.mk_not_raw(read);

    let evidence = authenticate_bool_bv_unsat_query(&terms, &[contradiction], None)
        .expect("full Bool domain scalarization proves read-over-write");
    assert!(evidence.used_exact_finite_arrays());
}

#[test]
fn authenticates_bv_index_bv_leaf_const_store_select() {
    let mut terms = TermStore::new();
    let index_sort = Sort::bitvec(2);
    let leaf_sort = Sort::bitvec(4);
    let array_sort = Sort::array(index_sort.clone(), leaf_sort.clone());
    let index = terms.mk_var("bv_index", index_sort);
    let zero = terms.mk_bitvec(BigInt::from(0_u8), 4);
    let value = terms.mk_bitvec(BigInt::from(9_u8), 4);
    let constant = terms.mk_app(Symbol::named("const-array"), [zero], array_sort.clone());
    let stored = raw_store(&mut terms, constant, index, value, array_sort.clone());
    let read = raw_select(&mut terms, stored, index, leaf_sort);
    let contradiction = raw_disequality(&mut terms, read, value);

    let evidence = authenticate_bool_bv_unsat_query(&terms, &[contradiction], None)
        .expect("full BV domain scalarization proves read-over-write");
    assert!(evidence.used_exact_finite_arrays());
}

#[test]
fn authenticates_array_ite_extensional_equality() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, Sort::bitvec(2));
    let condition = terms.mk_var("array_condition", Sort::Bool);
    let array = terms.mk_var("array_branch", array_sort);
    let array_ite = terms.mk_ite_raw(condition, array, array);
    let contradiction = raw_disequality(&mut terms, array_ite, array);

    let evidence = authenticate_bool_bv_unsat_query(&terms, &[contradiction], None)
        .expect("full-domain equality proves an array ite with equal branches");
    assert!(evidence.used_exact_finite_arrays());
}

#[test]
fn authenticates_recursive_array_store_and_select() {
    let mut terms = TermStore::new();
    let inner_sort = Sort::array(Sort::bitvec(1), Sort::Bool);
    let outer_sort = Sort::array(Sort::Bool, inner_sort.clone());
    let array = terms.mk_var("nested_array", outer_sort.clone());
    let outer_index = terms.mk_var("outer_index", Sort::Bool);
    let inner_index = terms.mk_var("inner_index", Sort::bitvec(1));
    let value = terms.mk_bool(true);

    let inner = raw_select(&mut terms, array, outer_index, inner_sort.clone());
    let stored_inner = raw_store(&mut terms, inner, inner_index, value, inner_sort.clone());
    let stored_outer = raw_store(&mut terms, array, outer_index, stored_inner, outer_sort);
    let selected_inner = raw_select(&mut terms, stored_outer, outer_index, inner_sort);
    let selected_value = raw_select(&mut terms, selected_inner, inner_index, Sort::Bool);
    let contradiction = terms.mk_not_raw(selected_value);

    let evidence = authenticate_bool_bv_unsat_query(&terms, &[contradiction], None)
        .expect("recursive complete-domain scalarization proves nested read-over-write");
    assert!(evidence.used_exact_finite_arrays());
}

#[test]
fn authenticates_recursive_array_extensionality_contradiction() {
    let mut terms = TermStore::new();
    let inner_sort = Sort::array(Sort::bitvec(1), Sort::Bool);
    let outer_sort = Sort::array(Sort::Bool, inner_sort);
    let condition = terms.mk_var("nested_extensional_condition", Sort::Bool);
    let array = terms.mk_var("nested_extensional_array", outer_sort);
    let same_array_ite = terms.mk_ite_raw(condition, array, array);
    let contradiction = raw_disequality(&mut terms, same_array_ite, array);

    let evidence = authenticate_bool_bv_unsat_query(&terms, &[contradiction], None)
        .expect("recursive array equality must compare the complete nested domain");
    assert!(evidence.used_exact_finite_arrays());
}

#[test]
fn satisfiable_distinct_arrays_do_not_mint_evidence() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Bool);
    let left = terms.mk_var("satisfiable_array_left", array_sort.clone());
    let right = terms.mk_var("satisfiable_array_right", array_sort);
    let disequality = raw_disequality(&mut terms, left, right);

    let error = authenticate_bool_bv_unsat_query(&terms, &[disequality], None)
        .expect_err("two free finite arrays may be distinct");
    assert!(
        matches!(error, BoolBvUnsatAuthenticationError::Satisfiable),
        "unexpected error: {error}"
    );
    assert!(!error.is_capability_decline());
}

#[test]
fn exact_array_evidence_is_invalidated_by_term_store_mutation() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Bool);
    let array = terms.mk_var("snapshot_array", array_sort);
    let equality = raw_equality(&mut terms, array, array);
    let contradiction = terms.mk_not_raw(equality);
    let roots = [contradiction];
    let evidence = authenticate_bool_bv_unsat_query(&terms, &roots, None)
        .expect("reflexive array disequality is contradictory");
    assert!(evidence.is_current_for(&terms, &roots));
    assert!(evidence.term_snapshot_is_current(&terms));

    let _appended = terms.mk_var("snapshot_mutation", Sort::Bool);
    assert!(!evidence.is_current_for(&terms, &roots));
    assert!(!evidence.term_snapshot_is_current(&terms));
}

#[test]
fn pure_bool_bv_evidence_does_not_claim_array_scalarization() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("plain_bool", Sort::Bool);
    let negated = terms.mk_not_raw(value);
    let roots = [value, negated];

    let evidence = authenticate_bool_bv_unsat_query(&terms, &roots, None)
        .expect("plain Boolean contradiction must authenticate");
    assert!(!evidence.used_exact_finite_arrays());
}

#[test]
fn malformed_array_signatures_decline() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Bool);
    let array = terms.mk_var("malformed_array", array_sort.clone());
    let bool_index = terms.mk_var("good_index", Sort::Bool);
    let wrong_index = terms.mk_bitvec(BigInt::from(0_u8), 1);
    let bv_value = terms.mk_bitvec(BigInt::from(0_u8), 1);
    let bool_value = terms.mk_bool(false);

    let wrong_result = raw_select(&mut terms, array, bool_index, Sort::bitvec(1));
    let wrong_result_root = raw_equality(&mut terms, wrong_result, bv_value);
    let wrong_index_read = raw_select(&mut terms, array, wrong_index, Sort::Bool);
    let wrong_index_root = raw_equality(&mut terms, wrong_index_read, bool_value);
    let indexed_select = terms.mk_app(
        Symbol::indexed("select", vec![0]),
        [array, bool_index],
        Sort::Bool,
    );
    let indexed_root = raw_equality(&mut terms, indexed_select, bool_value);
    let spoof = terms.mk_app(Symbol::named("array-spoof"), [array], array_sort);
    let spoof_root = raw_disequality(&mut terms, spoof, array);

    for root in [
        wrong_result_root,
        wrong_index_root,
        indexed_root,
        spoof_root,
    ] {
        let error = authenticate_bool_bv_unsat_query(&terms, &[root], None)
            .expect_err("malformed/noncanonical array source must decline");
        assert!(error.is_unsupported_fragment(), "unexpected error: {error}");
    }
}

#[test]
fn malformed_store_arity_and_value_sort_decline() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Bool);
    let array = terms.mk_var("malformed_store_array", array_sort.clone());
    let index = terms.mk_var("malformed_store_index", Sort::Bool);
    let wrong_value = terms.mk_bitvec(BigInt::from(0_u8), 1);

    let short_store = terms.mk_app(Symbol::named("store"), [array, index], array_sort.clone());
    let short_root = raw_disequality(&mut terms, short_store, array);
    let wrong_value_store = terms.mk_app(
        Symbol::named("store"),
        [array, index, wrong_value],
        array_sort,
    );
    let wrong_value_root = raw_disequality(&mut terms, wrong_value_store, array);

    for root in [short_root, wrong_value_root] {
        let error = authenticate_bool_bv_unsat_query(&terms, &[root], None)
            .expect_err("malformed store must not mint source evidence");
        assert!(error.is_unsupported_fragment(), "unexpected error: {error}");
    }
}

#[test]
fn oversized_finite_domain_is_a_resource_decline() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::bitvec(9), Sort::Bool);
    let array = terms.mk_var("too_wide_array", array_sort);
    let equality = raw_equality(&mut terms, array, array);
    let contradiction = terms.mk_not_raw(equality);

    let error = authenticate_bool_bv_unsat_query(&terms, &[contradiction], None)
        .expect_err("full-domain enumeration above the explicit bound must decline");
    assert!(
        matches!(error, BoolBvUnsatAuthenticationError::ResourceLimit { .. }),
        "unexpected error: {error}"
    );
    assert!(error.is_capability_decline());
}
