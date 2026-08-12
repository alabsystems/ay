// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_core::{ArraySort, Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;

use super::{authenticate_bool_bv_unsat_query, BoolBvUnsatAuthenticationError};

struct Fixture {
    terms: TermStore,
    array: TermId,
    other_array: TermId,
    left_index: TermId,
    right_index: TermId,
    left_read: TermId,
    right_read: TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let index_sort = Sort::bitvec(3);
        let element_sort = Sort::Uninterpreted("ArrayCell".to_string());
        let array_sort = Sort::Array(Box::new(ArraySort::new(
            index_sort.clone(),
            element_sort.clone(),
        )));
        let array = terms.mk_var("auth_array", array_sort.clone());
        let other_array = terms.mk_var("auth_other_array", array_sort);
        let left_index = terms.mk_var("auth_left_index", index_sort.clone());
        let right_index = terms.mk_var("auth_right_index", index_sort);
        let left_read = terms.mk_app(
            Symbol::named("select"),
            [array, left_index],
            element_sort.clone(),
        );
        let right_read = terms.mk_app(Symbol::named("select"), [array, right_index], element_sort);
        Self {
            terms,
            array,
            other_array,
            left_index,
            right_index,
            left_read,
            right_read,
        }
    }

    fn derived_index_equality(&mut self) -> TermId {
        let one = self.terms.mk_bitvec(BigInt::from(1_u8), 3);
        let left = self.terms.mk_app(
            Symbol::named("bvadd"),
            [self.left_index, one],
            Sort::bitvec(3),
        );
        let right = self.terms.mk_app(
            Symbol::named("bvadd"),
            [self.right_index, one],
            Sort::bitvec(3),
        );
        self.terms
            .mk_app(Symbol::named("="), [left, right], Sort::Bool)
    }

    fn read_disequality(&mut self, left: TermId, right: TermId) -> TermId {
        let equality = self
            .terms
            .mk_app(Symbol::named("="), [left, right], Sort::Bool);
        self.terms.mk_not_raw(equality)
    }
}

#[test]
fn authenticates_derived_equal_index_same_array_read_conflict() {
    let mut fixture = Fixture::new();
    let index_equality = fixture.derived_index_equality();
    let read_disequality = fixture.read_disequality(fixture.left_read, fixture.right_read);
    let roots = [index_equality, read_disequality];

    let evidence = authenticate_bool_bv_unsat_query(&fixture.terms, &roots, None)
        .expect("array congruence plus checked BV cancellation must authenticate UNSAT");
    assert!(evidence.is_current_for(&fixture.terms, &roots));
}

#[test]
fn satisfiable_reduction_declines_without_claiming_contrary_sat() {
    let mut fixture = Fixture::new();
    let disequality = fixture.read_disequality(fixture.left_read, fixture.right_read);
    let error = authenticate_bool_bv_unsat_query(&fixture.terms, &[disequality], None)
        .expect_err("different indices can select different values");
    assert!(error.is_unsupported_fragment());
    assert!(!matches!(
        error,
        BoolBvUnsatAuthenticationError::Satisfiable
    ));
}

#[test]
fn different_arrays_and_indexed_lookalikes_decline() {
    let mut fixture = Fixture::new();
    let element_sort = Sort::Uninterpreted("ArrayCell".to_string());
    let other_read = fixture.terms.mk_app(
        Symbol::named("select"),
        [fixture.other_array, fixture.right_index],
        element_sort.clone(),
    );
    let indexed_read = fixture.terms.mk_app(
        Symbol::indexed("select", vec![0]),
        [fixture.array, fixture.left_index],
        element_sort,
    );
    let index_equality = fixture.derived_index_equality();
    for right in [other_read, indexed_read] {
        let disequality = fixture.read_disequality(fixture.left_read, right);
        let error =
            authenticate_bool_bv_unsat_query(&fixture.terms, &[index_equality, disequality], None)
                .expect_err("noncanonical/different array reads need not agree");
        assert!(error.is_unsupported_fragment());
    }
}

#[test]
fn indexed_equality_and_malformed_select_decline() {
    let mut fixture = Fixture::new();
    let one = fixture.terms.mk_bitvec(BigInt::from(1_u8), 3);
    let left = fixture.terms.mk_app(
        Symbol::named("bvadd"),
        [fixture.left_index, one],
        Sort::bitvec(3),
    );
    let right = fixture.terms.mk_app(
        Symbol::named("bvadd"),
        [fixture.right_index, one],
        Sort::bitvec(3),
    );
    let indexed_equality =
        fixture
            .terms
            .mk_app(Symbol::indexed("=", vec![0]), [left, right], Sort::Bool);
    let wrong_index = fixture.terms.mk_var("wrong_index", Sort::Bool);
    let malformed_read = fixture.terms.mk_app(
        Symbol::named("select"),
        [fixture.array, wrong_index],
        Sort::Uninterpreted("ArrayCell".to_string()),
    );
    let disequality = fixture.read_disequality(malformed_read, fixture.right_read);
    let error =
        authenticate_bool_bv_unsat_query(&fixture.terms, &[indexed_equality, disequality], None)
            .expect_err("spoofed equality and malformed select must decline");
    assert!(error.is_unsupported_fragment());
}

#[test]
fn dangling_children_and_composite_array_sources_fail_closed() {
    let mut terms = TermStore::new();
    let dangling = TermId::new(u32::MAX);
    let dangling_root = terms.mk_app(Symbol::named("not"), [dangling], Sort::Bool);
    assert!(
        authenticate_bool_bv_unsat_query(&terms, &[dangling_root], None)
            .expect_err("dangling Bool child must decline")
            .is_unsupported_fragment()
    );

    let array_sort = Sort::array(
        Sort::bitvec(3),
        Sort::Uninterpreted("ArrayCell".to_string()),
    );
    let composite_array = terms.mk_app(Symbol::named("array_spoof"), [dangling], array_sort);
    let left = terms.mk_var("composite_i", Sort::bitvec(3));
    let right = terms.mk_var("composite_j", Sort::bitvec(3));
    let cell_sort = Sort::Uninterpreted("ArrayCell".to_string());
    let left_read = terms.mk_app(
        Symbol::named("select"),
        [composite_array, left],
        cell_sort.clone(),
    );
    let right_read = terms.mk_app(Symbol::named("select"), [composite_array, right], cell_sort);
    let equality = terms.mk_app(Symbol::named("="), [left_read, right_read], Sort::Bool);
    let disequality = terms.mk_not_raw(equality);
    assert!(
        authenticate_bool_bv_unsat_query(&terms, &[disequality], None)
            .expect_err("composite array authority is deliberately outside the narrow lane")
            .is_unsupported_fragment()
    );
}
