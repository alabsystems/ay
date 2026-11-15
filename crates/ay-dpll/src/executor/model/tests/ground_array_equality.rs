// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact evaluation of GROUND array (dis)equalities, also on the BV lane
//! (#aufbv-const-array-equality, `eval_array/ground_equality.rs`).
//!
//! Every model here carries a `bv_model`, which is what made a normalized
//! mismatch Unknown before: the solver's own `distinct_const_array` axiom
//! `(not (= ((as const A) true) ((as const A) false)))` then failed QF_AUFBV
//! model validation closed (measured on the w37 fuzz file f035). Each
//! acceptance has a twin whose arrays differ, and the finite index sorts are
//! checked both covered and uncovered.

use super::*;

fn bv_lane_model() -> Model {
    bv_model(&[])
}

fn mk_array_eq(executor: &mut Executor, lhs: TermId, rhs: TermId) -> TermId {
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// `((as const (Array index element)) value)`, interned without
/// simplification.
fn mk_const(executor: &mut Executor, index: Sort, value: TermId) -> TermId {
    let element = executor.ctx.terms.sort(value).clone();
    executor.ctx.terms.mk_app(
        Symbol::named("const-array"),
        vec![value],
        Sort::array(index, element),
    )
}

/// `(store array index value)`, interned without the store rewrites, so a
/// shadowed or redundant write stays in the term.
fn mk_raw_store(executor: &mut Executor, array: TermId, index: TermId, value: TermId) -> TermId {
    let sort = executor.ctx.terms.sort(array).clone();
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("store"), vec![array, index, value], sort)
}

fn bv(executor: &mut Executor, value: u64, width: u32) -> TermId {
    executor.ctx.terms.mk_bitvec(BigInt::from(value), width)
}

fn bools(executor: &mut Executor) -> (TermId, TermId) {
    (
        executor.ctx.terms.mk_bool(true),
        executor.ctx.terms.mk_bool(false),
    )
}

#[test]
fn const_arrays_with_different_defaults_are_unequal_on_the_bv_lane() {
    let mut executor = Executor::new();
    let (t, f) = bools(&mut executor);
    let all_true = mk_const(&mut executor, Sort::bitvec(32), t);
    let all_false = mk_const(&mut executor, Sort::bitvec(32), f);
    let eq = mk_array_eq(&mut executor, all_true, all_false);
    let axiom = executor.ctx.terms.mk_not(eq);
    let model = bv_lane_model();
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(false));
    assert_eq!(executor.evaluate_term(&model, axiom), EvalValue::Bool(true));
}

#[test]
fn const_arrays_with_equal_defaults_are_equal_on_the_bv_lane() {
    let mut executor = Executor::new();
    let seven = bv(&mut executor, 7, 8);
    // A different term with the same value: `(bvadd #x03 #x04)`.
    let three = bv(&mut executor, 3, 8);
    let four = bv(&mut executor, 4, 8);
    let also_seven =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("bvadd"), vec![three, four], Sort::bitvec(8));
    let lhs = mk_const(&mut executor, Sort::bitvec(32), seven);
    let rhs = mk_const(&mut executor, Sort::bitvec(32), also_seven);
    let eight = bv(&mut executor, 8, 8);
    let other = mk_const(&mut executor, Sort::bitvec(32), eight);
    let model = bv_lane_model();
    let eq = mk_array_eq(&mut executor, lhs, rhs);
    let ne = mk_array_eq(&mut executor, lhs, other);
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(true));
    assert_eq!(executor.evaluate_term(&model, ne), EvalValue::Bool(false));
}

#[test]
fn store_over_const_equals_its_shadowed_and_redundant_spellings() {
    let mut executor = Executor::new();
    let (t, f) = bools(&mut executor);
    let base = mk_const(&mut executor, Sort::bitvec(32), f);
    let two = bv(&mut executor, 2, 32);
    let five = bv(&mut executor, 5, 32);
    let lhs = mk_raw_store(&mut executor, base, two, t);
    // A write of the default value is redundant, and a later write to the
    // same index shadows an earlier one.
    let redundant = mk_raw_store(&mut executor, lhs, five, f);
    let shadowed_inner = mk_raw_store(&mut executor, base, two, f);
    let shadowed = mk_raw_store(&mut executor, shadowed_inner, two, t);
    let model = bv_lane_model();
    let eq_redundant = mk_array_eq(&mut executor, lhs, redundant);
    let eq_shadowed = mk_array_eq(&mut executor, lhs, shadowed);
    assert_eq!(
        executor.evaluate_term(&model, eq_redundant),
        EvalValue::Bool(true)
    );
    assert_eq!(
        executor.evaluate_term(&model, eq_shadowed),
        EvalValue::Bool(true)
    );
}

#[test]
fn store_over_const_differs_from_its_base_and_from_an_overwrite() {
    let mut executor = Executor::new();
    let (t, f) = bools(&mut executor);
    let base = mk_const(&mut executor, Sort::bitvec(32), f);
    let two = bv(&mut executor, 2, 32);
    let stored = mk_raw_store(&mut executor, base, two, t);
    // The newest write at #x2 is `false`: this is the base again.
    let overwritten = mk_raw_store(&mut executor, stored, two, f);
    let model = bv_lane_model();
    let eq_base = mk_array_eq(&mut executor, stored, base);
    let eq_overwritten = mk_array_eq(&mut executor, stored, overwritten);
    let eq_restored = mk_array_eq(&mut executor, overwritten, base);
    assert_eq!(
        executor.evaluate_term(&model, eq_base),
        EvalValue::Bool(false)
    );
    assert_eq!(
        executor.evaluate_term(&model, eq_overwritten),
        EvalValue::Bool(false)
    );
    assert_eq!(
        executor.evaluate_term(&model, eq_restored),
        EvalValue::Bool(true)
    );
}

#[test]
fn chains_over_different_defaults_differ_at_an_unwritten_index() {
    // f035's shape: `(store (store (const false) #x42 true) #x01 true)` and
    // `(store (const false) #x42 true)` agree at #x42 and differ at #x01;
    // `(store (const true) #x02 true)` is `(const true)`.
    let mut executor = Executor::new();
    let (t, f) = bools(&mut executor);
    let all_false = mk_const(&mut executor, Sort::bitvec(32), f);
    let all_true = mk_const(&mut executor, Sort::bitvec(32), t);
    let x42 = bv(&mut executor, 0x42, 32);
    let x01 = bv(&mut executor, 1, 32);
    let x02 = bv(&mut executor, 2, 32);
    let inner = mk_raw_store(&mut executor, all_false, x42, t);
    let two_writes = mk_raw_store(&mut executor, inner, x01, t);
    let true_over_true = mk_raw_store(&mut executor, all_true, x02, t);
    let model = bv_lane_model();
    let eq_chains = mk_array_eq(&mut executor, two_writes, inner);
    let eq_true = mk_array_eq(&mut executor, true_over_true, all_true);
    let eq_mixed = mk_array_eq(&mut executor, inner, all_true);
    assert_eq!(
        executor.evaluate_term(&model, eq_chains),
        EvalValue::Bool(false)
    );
    assert_eq!(
        executor.evaluate_term(&model, eq_true),
        EvalValue::Bool(true)
    );
    assert_eq!(
        executor.evaluate_term(&model, eq_mixed),
        EvalValue::Bool(false)
    );
}

#[test]
fn writes_covering_a_bv1_index_sort_make_the_defaults_irrelevant() {
    let mut executor = Executor::new();
    let (t, f) = bools(&mut executor);
    let all_false = mk_const(&mut executor, Sort::bitvec(1), f);
    let all_true = mk_const(&mut executor, Sort::bitvec(1), t);
    let zero = bv(&mut executor, 0, 1);
    let one = bv(&mut executor, 1, 1);
    let half = mk_raw_store(&mut executor, all_false, zero, t);
    let full = mk_raw_store(&mut executor, half, one, t);
    let model = bv_lane_model();
    let eq_full = mk_array_eq(&mut executor, full, all_true);
    // Twin: #b1 is unwritten and reads false on one side, true on the other.
    let eq_half = mk_array_eq(&mut executor, half, all_true);
    assert_eq!(
        executor.evaluate_term(&model, eq_full),
        EvalValue::Bool(true)
    );
    assert_eq!(
        executor.evaluate_term(&model, eq_half),
        EvalValue::Bool(false)
    );
}

#[test]
fn writes_covering_a_bv2_index_sort_across_both_sides_compare_every_cell() {
    // Each side writes two of the four indices; together they cover the sort,
    // so the differing defaults are never read.
    let mut executor = Executor::new();
    let zero = bv(&mut executor, 0, 4);
    let nine = bv(&mut executor, 9, 4);
    let idx: Vec<TermId> = (0..4).map(|i| bv(&mut executor, i, 2)).collect();
    let all_zero = mk_const(&mut executor, Sort::bitvec(2), zero);
    let all_nine = mk_const(&mut executor, Sort::bitvec(2), nine);
    // lhs writes 9 at #b00 and #b01 and reads its default 0 at #b10 and #b11;
    // rhs writes 0 at #b10 and #b11 and reads its default 9 at the other two.
    let l0 = mk_raw_store(&mut executor, all_zero, idx[0], nine);
    let lhs = mk_raw_store(&mut executor, l0, idx[1], nine);
    let r2 = mk_raw_store(&mut executor, all_nine, idx[2], zero);
    let rhs = mk_raw_store(&mut executor, r2, idx[3], zero);
    // Twin: rhs leaves index 3 at its default 9, where lhs reads 0.
    let model = bv_lane_model();
    let eq = mk_array_eq(&mut executor, lhs, rhs);
    let eq_short = mk_array_eq(&mut executor, lhs, r2);
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(true));
    assert_eq!(
        executor.evaluate_term(&model, eq_short),
        EvalValue::Bool(false)
    );
}

#[test]
fn writes_covering_a_bool_index_sort_make_the_defaults_irrelevant() {
    let mut executor = Executor::new();
    let (t, f) = bools(&mut executor);
    let zero = bv(&mut executor, 0, 8);
    let seven = bv(&mut executor, 7, 8);
    let all_zero = mk_const(&mut executor, Sort::Bool, zero);
    let all_seven = mk_const(&mut executor, Sort::Bool, seven);
    let half = mk_raw_store(&mut executor, all_zero, f, seven);
    let full = mk_raw_store(&mut executor, half, t, seven);
    let model = bv_lane_model();
    let eq_full = mk_array_eq(&mut executor, full, all_seven);
    let eq_half = mk_array_eq(&mut executor, half, all_seven);
    // Covering both indices with a different value is a different array.
    let eight = bv(&mut executor, 8, 8);
    let full_eight = mk_raw_store(&mut executor, half, t, eight);
    let eq_other = mk_array_eq(&mut executor, full_eight, all_seven);
    assert_eq!(
        executor.evaluate_term(&model, eq_full),
        EvalValue::Bool(true)
    );
    assert_eq!(
        executor.evaluate_term(&model, eq_half),
        EvalValue::Bool(false)
    );
    assert_eq!(
        executor.evaluate_term(&model, eq_other),
        EvalValue::Bool(false)
    );
}

#[test]
fn bv_element_store_chains_compare_cell_by_cell() {
    let mut executor = Executor::new();
    let zero = bv(&mut executor, 0, 8);
    let one = bv(&mut executor, 1, 8);
    let three = bv(&mut executor, 3, 8);
    let ff = bv(&mut executor, 0xff, 8);
    let fe = bv(&mut executor, 0xfe, 8);
    let base = mk_const(&mut executor, Sort::bitvec(8), zero);
    let lhs = mk_raw_store(&mut executor, base, one, ff);
    let rhs_diff = mk_raw_store(&mut executor, base, one, fe);
    let rhs_inner = mk_raw_store(&mut executor, base, three, zero);
    let rhs_same = mk_raw_store(&mut executor, rhs_inner, one, ff);
    let model = bv_lane_model();
    let eq_diff = mk_array_eq(&mut executor, lhs, rhs_diff);
    let eq_same = mk_array_eq(&mut executor, lhs, rhs_same);
    assert_eq!(
        executor.evaluate_term(&model, eq_diff),
        EvalValue::Bool(false)
    );
    assert_eq!(
        executor.evaluate_term(&model, eq_same),
        EvalValue::Bool(true)
    );
}

#[test]
fn an_int_index_sort_is_never_covered() {
    let mut executor = Executor::new();
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let all_zero = mk_const(&mut executor, Sort::Int, zero);
    let all_one = mk_const(&mut executor, Sort::Int, one);
    let lhs_inner = mk_raw_store(&mut executor, all_zero, zero, one);
    let lhs = mk_raw_store(&mut executor, lhs_inner, one, one);
    let eq = mk_array_eq(&mut executor, lhs, all_one);
    assert_eq!(
        executor.evaluate_term(&bv_lane_model(), eq),
        EvalValue::Bool(false)
    );
}

#[test]
fn a_scalar_index_reads_its_model_value() {
    let mut executor = Executor::new();
    let (t, f) = bools(&mut executor);
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(32));
    let two = bv(&mut executor, 2, 32);
    let base = mk_const(&mut executor, Sort::bitvec(32), f);
    let at_x = mk_raw_store(&mut executor, base, x, t);
    let at_two = mk_raw_store(&mut executor, base, two, t);
    let eq = mk_array_eq(&mut executor, at_x, at_two);
    assert_eq!(
        executor.evaluate_term(&bv_model(&[(x, 2)]), eq),
        EvalValue::Bool(true)
    );
    assert_eq!(
        executor.evaluate_term(&bv_model(&[(x, 3)]), eq),
        EvalValue::Bool(false)
    );
    // With no value for `x` there is no ground value, and the BV-lane guard
    // of the general comparison still answers Unknown, never `false`.
    assert_eq!(
        executor.evaluate_term(&bv_lane_model(), eq),
        EvalValue::Unknown
    );
}

#[test]
fn an_ite_operand_follows_its_decided_condition() {
    let mut executor = Executor::new();
    let (t, f) = bools(&mut executor);
    let p = executor.ctx.terms.mk_var("p", Sort::Bool);
    let all_true = mk_const(&mut executor, Sort::bitvec(32), t);
    let all_false = mk_const(&mut executor, Sort::bitvec(32), f);
    let chosen = executor.ctx.terms.mk_ite(p, all_true, all_false);
    let eq = mk_array_eq(&mut executor, chosen, all_false);
    let mut model = model_with_sat_assignments(&[(p, false)]);
    model.bv_model = bv_lane_model().bv_model;
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(true));
    let mut model = model_with_sat_assignments(&[(p, true)]);
    model.bv_model = bv_lane_model().bv_model;
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Bool(false));
}

#[test]
fn an_array_variable_operand_keeps_the_general_comparison() {
    let mut executor = Executor::new();
    let (t, f) = bools(&mut executor);
    let v = executor
        .ctx
        .terms
        .mk_var("v", Sort::array(Sort::bitvec(32), Sort::Bool));
    let all_false = mk_const(&mut executor, Sort::bitvec(32), f);
    let x01 = bv(&mut executor, 1, 32);
    let over_v = mk_raw_store(&mut executor, v, x01, t);
    let eq = mk_array_eq(&mut executor, v, all_false);
    let eq_store = mk_array_eq(&mut executor, over_v, all_false);
    assert_eq!(
        executor.evaluate_term(&bv_lane_model(), eq),
        EvalValue::Unknown
    );
    assert_eq!(
        executor.evaluate_term(&bv_lane_model(), eq_store),
        EvalValue::Unknown
    );
}

#[test]
fn the_distinct_const_array_axiom_validates_on_the_bv_lane() {
    let mut executor = Executor::new();
    let (t, f) = bools(&mut executor);
    let all_true = mk_const(&mut executor, Sort::bitvec(32), t);
    let all_false = mk_const(&mut executor, Sort::bitvec(32), f);
    let eq = mk_array_eq(&mut executor, all_true, all_false);
    let axiom = executor.ctx.terms.mk_not(eq);
    executor.ctx.assertions.push(axiom);
    executor.last_result = Some(SolveResult::Sat);
    let mut model = model_with_sat_assignments(&[(axiom, true)]);
    model.bv_model = bv_lane_model().bv_model;
    executor.last_model = Some(model);
    let result = executor
        .finalize_sat_model_validation()
        .expect("a ground array disequality validates");
    assert_eq!(result, SolveResult::Sat);
    // The canonical evaluator decided it; before, it was an incomplete gap
    // that only the independent-gate handoff could close.
    assert_eq!(
        executor
            .statistics()
            .get_int("model_validation.independent_array_handoff"),
        None
    );
}

#[test]
fn a_false_ground_array_equality_is_refuted_on_the_bv_lane() {
    let mut executor = Executor::new();
    let (t, f) = bools(&mut executor);
    let all_true = mk_const(&mut executor, Sort::bitvec(32), t);
    let all_false = mk_const(&mut executor, Sort::bitvec(32), f);
    let eq = mk_array_eq(&mut executor, all_true, all_false);
    executor.ctx.assertions.push(eq);
    executor.last_result = Some(SolveResult::Sat);
    let mut model = model_with_sat_assignments(&[(eq, true)]);
    model.bv_model = bv_lane_model().bv_model;
    executor.last_model = Some(model);
    let result = executor
        .finalize_sat_model_validation()
        .expect("a false ground array equality fails closed");
    assert_eq!(result, SolveResult::Unknown);
    // A definitive violation, not an unevaluable gap.
    assert!(
        executor
            .statistics()
            .get_string("unknown.detail")
            .is_some_and(|detail| detail.contains("evaluates to false")),
        "{:?}",
        executor.statistics().get_string("unknown.detail")
    );
}
