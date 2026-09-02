// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public-query census boundaries for generated reads and binders.

use super::*;

#[test]
fn generated_reads_do_not_become_public_congruence_observations() {
    let mut pair = canonical_read_pair();
    let (_, left_index) = pair
        .executor
        .exact_cegar_select_parts(pair.left)
        .expect("left read is canonical");
    let (_, right_index) = pair
        .executor
        .exact_cegar_select_parts(pair.right)
        .expect("right read is canonical");
    let conflict = pair
        .executor
        .ctx
        .terms
        .mk_distinct(vec![pair.left, pair.right]);
    let truth = pair.executor.ctx.terms.true_term();
    let model = lia_census_model(&[
        (left_index, 0),
        (right_index, 0),
        (pair.left, 1),
        (pair.right, 2),
    ]);

    pair.executor.ctx.assertions = vec![conflict];
    pair.executor.independent_gate_authored_assertions = Some(vec![truth]);
    assert!(!pair.executor.problem_has_array());
    assert!(!pair.executor.array_select_congruence_violated(&model));
    assert!(pair
        .executor
        .census_congruence_cegar_lemma(&model)
        .is_none());

    pair.executor.independent_gate_authored_assertions = Some(vec![conflict]);
    assert!(pair.executor.problem_has_array());
    assert!(pair.executor.array_select_congruence_violated(&model));
    assert!(pair
        .executor
        .census_congruence_cegar_lemma(&model)
        .is_some());
}

#[test]
fn authored_array_equalities_remain_hard_after_sat_elimination() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let left_array = executor
        .ctx
        .terms
        .mk_var("authored_left_array", array_sort.clone());
    let right_array = executor
        .ctx
        .terms
        .mk_var("authored_right_array", array_sort);
    let left_index = executor.ctx.terms.mk_var("authored_left_index", Sort::Int);
    let right_index = executor.ctx.terms.mk_var("authored_right_index", Sort::Int);
    let left_read = executor.ctx.terms.mk_select(left_array, left_index);
    let right_read = executor.ctx.terms.mk_select(right_array, right_index);
    let array_equality = executor.ctx.terms.mk_eq(left_array, right_array);
    let read_conflict = executor.ctx.terms.mk_distinct(vec![left_read, right_read]);
    let model = lia_census_model(&[
        (left_index, 0),
        (right_index, 0),
        (left_read, 1),
        (right_read, 2),
    ]);
    assert!(model.term_to_var.is_empty());

    executor.independent_gate_authored_assertions = Some(vec![array_equality, read_conflict]);
    assert!(executor.array_select_congruence_violated(&model));

    let conjunction = executor
        .ctx
        .terms
        .mk_and(vec![array_equality, read_conflict]);
    executor.independent_gate_authored_assertions = Some(vec![conjunction]);
    assert!(executor.array_select_congruence_violated(&model));
}

#[test]
fn assuming_only_reads_are_public_congruence_observations() {
    let mut pair = canonical_read_pair();
    let (_, left_index) = pair
        .executor
        .exact_cegar_select_parts(pair.left)
        .expect("left read is canonical");
    let (_, right_index) = pair
        .executor
        .exact_cegar_select_parts(pair.right)
        .expect("right read is canonical");
    let assumption = pair
        .executor
        .ctx
        .terms
        .mk_distinct(vec![pair.left, pair.right]);
    let truth = pair.executor.ctx.terms.true_term();
    let model = lia_census_model(&[
        (left_index, 0),
        (right_index, 0),
        (pair.left, 1),
        (pair.right, 2),
    ]);
    pair.executor.independent_gate_authored_assertions = Some(vec![truth]);
    pair.executor.last_assumptions = Some(vec![assumption]);

    assert!(pair.executor.array_select_congruence_violated(&model));
    assert!(pair
        .executor
        .census_congruence_cegar_lemma(&model)
        .is_some());
}

#[test]
fn nonempty_let_excludes_conditioned_reads_but_keeps_sibling_ground_observations() {
    let mut pair = canonical_read_pair();
    let (_, left_index) = pair
        .executor
        .exact_cegar_select_parts(pair.left)
        .expect("left read is canonical");
    let (_, right_index) = pair
        .executor
        .exact_cegar_select_parts(pair.right)
        .expect("right read is canonical");
    let binding = pair.executor.ctx.terms.mk_int(BigInt::from(0));
    let conflict = pair
        .executor
        .ctx
        .terms
        .mk_distinct(vec![pair.left, pair.right]);
    let let_root = pair
        .executor
        .ctx
        .terms
        .mk_let(vec![("bound".to_string(), binding)], conflict);
    let model = lia_census_model(&[
        (left_index, 0),
        (right_index, 0),
        (pair.left, 1),
        (pair.right, 2),
    ]);

    pair.executor.independent_gate_authored_assertions = Some(vec![let_root]);
    assert!(
        !pair.executor.array_select_congruence_violated(&model),
        "binder-conditioned reads are not public ground observations"
    );
    pair.executor.independent_gate_authored_assertions = Some(vec![let_root, conflict]);
    assert!(pair.executor.array_select_congruence_violated(&model));
    assert!(pair
        .executor
        .datatype_array_field_required_terms()
        .is_none());
}

#[test]
fn empty_let_remains_an_exact_ground_census_alias() {
    let mut pair = canonical_read_pair();
    let (_, left_index) = pair
        .executor
        .exact_cegar_select_parts(pair.left)
        .expect("left read is canonical");
    let (_, right_index) = pair
        .executor
        .exact_cegar_select_parts(pair.right)
        .expect("right read is canonical");
    let conflict = pair
        .executor
        .ctx
        .terms
        .mk_distinct(vec![pair.left, pair.right]);
    let let_root = pair.executor.ctx.terms.mk_let(Vec::new(), conflict);
    pair.executor.independent_gate_authored_assertions = Some(vec![let_root]);
    let model = lia_census_model(&[
        (left_index, 0),
        (right_index, 0),
        (pair.left, 1),
        (pair.right, 2),
    ]);

    assert!(pair.executor.array_select_congruence_violated(&model));
    assert!(pair
        .executor
        .datatype_array_field_required_terms()
        .is_some());
}

#[test]
fn quantifier_excludes_conditioned_reads_but_keeps_sibling_ground_observations() {
    let mut pair = canonical_read_pair();
    let (_, left_index) = pair
        .executor
        .exact_cegar_select_parts(pair.left)
        .expect("left read is canonical");
    let (_, right_index) = pair
        .executor
        .exact_cegar_select_parts(pair.right)
        .expect("right read is canonical");
    let conflict = pair
        .executor
        .ctx
        .terms
        .mk_distinct(vec![pair.left, pair.right]);
    let quantified = pair
        .executor
        .ctx
        .terms
        .mk_forall(vec![("bound".to_string(), Sort::Int)], conflict);
    let model = lia_census_model(&[
        (left_index, 0),
        (right_index, 0),
        (pair.left, 1),
        (pair.right, 2),
    ]);

    pair.executor.independent_gate_authored_assertions = Some(vec![quantified]);
    assert!(
        !pair.executor.array_select_congruence_violated(&model),
        "quantifier-conditioned reads are not public ground observations"
    );
    pair.executor.independent_gate_authored_assertions = Some(vec![quantified, conflict]);
    assert!(pair.executor.array_select_congruence_violated(&model));
    assert!(pair
        .executor
        .datatype_array_field_required_terms()
        .is_none());
}
