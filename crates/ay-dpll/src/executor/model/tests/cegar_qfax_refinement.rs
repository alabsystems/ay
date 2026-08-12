// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness and resource controls for QFAX model-guided refinement.

use super::*;

struct NestedQfaxFixture {
    executor: Executor,
    violated: TermId,
    outer_indices: (TermId, TermId),
    nested_indices: (TermId, TermId),
}

fn nested_qfax_fixture(left_nested_value: i64, right_nested_value: i64) -> NestedQfaxFixture {
    let mut executor = Executor::new();
    let index_sort = Sort::bitvec(4);
    let array_sort = Sort::array(index_sort.clone(), Sort::Int);
    let base = executor.ctx.terms.mk_var("qfax_base", array_sort.clone());
    let outer_left = executor
        .ctx
        .terms
        .mk_var("qfax_outer_left", index_sort.clone());
    let outer_right = executor
        .ctx
        .terms
        .mk_var("qfax_outer_right", index_sort.clone());
    let nested_left = executor
        .ctx
        .terms
        .mk_var("qfax_nested_left", index_sort.clone());
    let nested_right = executor.ctx.terms.mk_var("qfax_nested_right", index_sort);
    let left_value =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [base, nested_left], Sort::Int);
    let right_value =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [base, nested_right], Sort::Int);
    let left_chain = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        [base, outer_left, left_value],
        array_sort.clone(),
    );
    let right_chain = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        [base, outer_right, right_value],
        array_sort,
    );
    let equality =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [left_chain, right_chain], Sort::Bool);
    let violated = executor.ctx.terms.mk_not(equality);
    executor.last_model = Some(bv_model(&[
        (outer_left, 0),
        (outer_right, 0),
        (nested_left, left_nested_value),
        (nested_right, right_nested_value),
    ]));
    NestedQfaxFixture {
        executor,
        violated,
        outer_indices: (outer_left, outer_right),
        nested_indices: (nested_left, nested_right),
    }
}

fn equality_matches(executor: &Executor, term: TermId, expected: (TermId, TermId)) -> bool {
    executor
        .exact_cegar_equality_operands(term)
        .is_some_and(|actual| actual == expected || actual == (expected.1, expected.0))
}

#[test]
fn unequal_nested_base_read_indices_cannot_mint_qfax_clause() {
    let mut fixture = nested_qfax_fixture(1, 2);

    fixture
        .executor
        .derive_qfax_refinement_clause(fixture.violated);

    assert!(
        fixture.executor.qfax_refinement_clause.is_none(),
        "base[q1] and base[q2] are not equal when the model gives q1 != q2"
    );
}

#[test]
fn equal_nested_base_read_indices_are_explicit_clause_dependencies() {
    let mut fixture = nested_qfax_fixture(1, 1);

    fixture
        .executor
        .derive_qfax_refinement_clause(fixture.violated);

    let literals = fixture
        .executor
        .qfax_refinement_clause
        .as_ref()
        .expect("equal outer and nested indices justify a refinement clause");
    assert_eq!(literals.len(), 2);
    for expected in [fixture.outer_indices, fixture.nested_indices] {
        assert!(literals.iter().any(|&(term, model_value)| {
            model_value && equality_matches(&fixture.executor, term, expected)
        }));
    }
}

#[test]
fn unatomizable_inner_write_cannot_be_masked_by_known_outer_write() {
    let mut executor = Executor::new();
    let index_sort = Sort::bitvec(4);
    let array_sort = Sort::array(index_sort.clone(), Sort::Int);
    let base = executor
        .ctx
        .terms
        .mk_var("masked_qfax_base", array_sort.clone());
    let outer_left = executor
        .ctx
        .terms
        .mk_var("masked_outer_left", index_sort.clone());
    let outer_right = executor
        .ctx
        .terms
        .mk_var("masked_outer_right", index_sort.clone());
    let inner_left = executor
        .ctx
        .terms
        .mk_var("unatomizable_inner_left", index_sort.clone());
    let inner_right = executor
        .ctx
        .terms
        .mk_var("unatomizable_inner_right", index_sort);
    let left_value = executor.ctx.terms.mk_var("masked_left_value", Sort::Int);
    let right_value = executor.ctx.terms.mk_var("masked_right_value", Sort::Int);
    let outer_value = executor.ctx.terms.mk_var("masked_outer_value", Sort::Int);
    let left_inner = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        [base, inner_left, left_value],
        array_sort.clone(),
    );
    let right_inner = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        [base, inner_right, right_value],
        array_sort.clone(),
    );
    let left = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        [left_inner, outer_left, outer_value],
        array_sort.clone(),
    );
    let right = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        [right_inner, outer_right, outer_value],
        array_sort,
    );
    let equality = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let violated = executor.ctx.terms.mk_not(equality);
    executor.last_model = Some(bv_model(&[(outer_left, 0), (outer_right, 0)]));

    executor.derive_qfax_refinement_clause(violated);

    assert!(executor.qfax_refinement_clause.is_none());
}

#[test]
fn qfax_store_walk_declines_over_limit_chain() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let mut chain = executor
        .ctx
        .terms
        .mk_var("bounded_qfax_base", array_sort.clone());
    let index = executor.ctx.terms.mk_var("bounded_qfax_index", Sort::Int);
    let value = executor.ctx.terms.mk_var("bounded_qfax_value", Sort::Int);
    for _ in 0..300 {
        chain = executor.ctx.terms.mk_app(
            Symbol::named("store"),
            [chain, index, value],
            array_sort.clone(),
        );
    }

    assert!(executor.exact_qfax_store_chain(chain).is_none());
}
