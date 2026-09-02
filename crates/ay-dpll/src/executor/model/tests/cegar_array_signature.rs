// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact source-shape checks for array CEGAR lemma construction.

use super::*;
use ay_core::TermData;
use ay_frontend::parse;

mod census_scope;

struct ReadPair {
    executor: Executor,
    left: TermId,
    right: TermId,
}

fn canonical_read_pair() -> ReadPair {
    let mut executor = Executor::new();
    let array = executor
        .ctx
        .terms
        .mk_var("cegar_array", Sort::array(Sort::Int, Sort::Int));
    let left_index = executor.ctx.terms.mk_var("cegar_i", Sort::Int);
    let right_index = executor.ctx.terms.mk_var("cegar_j", Sort::Int);
    let left = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [array, left_index], Sort::Int);
    let right = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [array, right_index], Sort::Int);
    ReadPair {
        executor,
        left,
        right,
    }
}

fn raw_equality(executor: &mut Executor, symbol: Symbol, left: TermId, right: TermId) -> TermId {
    executor.ctx.terms.mk_app(symbol, [left, right], Sort::Bool)
}

fn forge_canonical_owner(executor: &mut Executor, identity: &str) {
    let owner = executor.ctx.terms.mk_fresh_named_var(identity, Sort::Bool);
    executor
        .ctx
        .register_symbol(identity.to_string(), owner, Sort::Bool);
}

fn lia_census_model(values: &[(TermId, i64)]) -> Model {
    let mut model = empty_model();
    model.lia_model = Some(LiaModel {
        values: values
            .iter()
            .map(|&(term, value)| (term, BigInt::from(value)))
            .collect(),
    });
    model
}

#[test]
fn canonical_named_well_sorted_reads_authorize_congruence_lemma() {
    let mut pair = canonical_read_pair();
    let equality = raw_equality(
        &mut pair.executor,
        Symbol::named("="),
        pair.left,
        pair.right,
    );

    assert!(pair
        .executor
        .strict_oracle_select_congruence_lemma(&empty_model(), equality)
        .is_some());
}

#[test]
fn indexed_select_and_equality_lookalikes_are_rejected() {
    let mut pair = canonical_read_pair();
    let (array, index) = pair
        .executor
        .exact_cegar_select_parts(pair.left)
        .expect("fixture read must be canonical");
    let indexed_select = pair.executor.ctx.terms.mk_app(
        Symbol::indexed("select", vec![0]),
        [array, index],
        Sort::Int,
    );
    let named_equality = raw_equality(
        &mut pair.executor,
        Symbol::named("="),
        indexed_select,
        pair.right,
    );
    assert!(pair
        .executor
        .strict_oracle_select_congruence_lemma(&empty_model(), named_equality)
        .is_none());

    let indexed_equality = raw_equality(
        &mut pair.executor,
        Symbol::indexed("=", vec![0]),
        pair.left,
        pair.right,
    );
    assert!(pair
        .executor
        .strict_oracle_select_congruence_lemma(&empty_model(), indexed_equality)
        .is_none());
}

#[test]
fn forged_canonical_owners_poison_cegar_theory_recognizers() {
    let mut pair = canonical_read_pair();
    assert!(pair.executor.exact_cegar_select_parts(pair.left).is_some());
    forge_canonical_owner(&mut pair.executor, "select");
    assert!(pair.executor.exact_cegar_select_parts(pair.left).is_none());

    let mut executor = Executor::new();
    let left = executor.ctx.terms.mk_var("forged_eq_left", Sort::Int);
    let right = executor.ctx.terms.mk_var("forged_eq_right", Sort::Int);
    let equality = raw_equality(&mut executor, Symbol::named("="), left, right);
    assert!(executor.exact_cegar_equality_operands(equality).is_some());
    forge_canonical_owner(&mut executor, "=");
    assert!(executor.exact_cegar_equality_operands(equality).is_none());

    let mut executor = Executor::new();
    let left = executor.ctx.terms.mk_var("forged_distinct_left", Sort::Int);
    let right = executor
        .ctx
        .terms
        .mk_var("forged_distinct_right", Sort::Int);
    let distinct = executor
        .ctx
        .terms
        .mk_app(Symbol::named("distinct"), [left, right], Sort::Bool);
    assert!(executor.exact_cegar_distinct_operands(distinct).is_some());
    forge_canonical_owner(&mut executor, "distinct");
    assert!(executor.exact_cegar_distinct_operands(distinct).is_none());

    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let array = executor
        .ctx
        .terms
        .mk_var("forged_store_array", array_sort.clone());
    let index = executor.ctx.terms.mk_var("forged_store_index", Sort::Int);
    let value = executor.ctx.terms.mk_var("forged_store_value", Sort::Int);
    let store =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("store"), [array, index, value], array_sort);
    assert!(executor.exact_cegar_store_parts(store).is_some());
    forge_canonical_owner(&mut executor, "store");
    assert!(executor.exact_cegar_store_parts(store).is_none());
}

#[test]
fn forged_lemma_output_operators_block_congruence_before_construction() {
    for identity in ["=", "and", "or"] {
        let mut pair = canonical_read_pair();
        forge_canonical_owner(&mut pair.executor, identity);
        assert!(pair
            .executor
            .build_select_congruence_lemma(&empty_model(), pair.left, pair.right)
            .is_none());
    }
}

#[test]
fn malformed_select_signatures_are_rejected() {
    let mut pair = canonical_read_pair();
    let int_base = pair.executor.ctx.terms.mk_var("not_an_array", Sort::Int);
    let int_index = pair.executor.ctx.terms.mk_var("malformed_i", Sort::Int);
    let bool_index = pair.executor.ctx.terms.mk_var("malformed_b", Sort::Bool);
    let array = pair
        .executor
        .ctx
        .terms
        .mk_var("typed_array", Sort::array(Sort::Int, Sort::Int));
    let non_array_read =
        pair.executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [int_base, int_index], Sort::Int);
    let wrong_index_read =
        pair.executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [array, bool_index], Sort::Int);
    let wrong_result_read =
        pair.executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [array, int_index], Sort::Bool);

    for malformed in [non_array_read, wrong_index_read, wrong_result_read] {
        let equality = raw_equality(&mut pair.executor, Symbol::named("="), malformed, malformed);
        assert!(pair
            .executor
            .strict_oracle_select_congruence_lemma(&empty_model(), equality)
            .is_none());
    }
}

#[test]
fn deeply_nested_sort_descriptors_decline_before_recursive_comparison() {
    let mut executor = Executor::new();
    let mut deep_sort = Sort::Int;
    for _ in 0..40 {
        deep_sort = Sort::array(Sort::Int, deep_sort);
    }
    let left = executor
        .ctx
        .terms
        .mk_var("deep_sort_left", deep_sort.clone());
    let right = executor.ctx.terms.mk_var("deep_sort_right", deep_sort);
    let equality = raw_equality(&mut executor, Symbol::named("="), left, right);

    assert!(executor.exact_cegar_equality_operands(equality).is_none());
}

#[test]
fn malformed_equality_and_dangling_select_child_are_rejected() {
    let mut pair = canonical_read_pair();
    let wrong_result_equality =
        pair.executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [pair.left, pair.right], Sort::Int);
    assert!(pair
        .executor
        .strict_oracle_select_congruence_lemma(&empty_model(), wrong_result_equality)
        .is_none());

    let bool_indexed_array = pair
        .executor
        .ctx
        .terms
        .mk_var("bool_indexed_array", Sort::array(Sort::Bool, Sort::Int));
    let bool_index = pair.executor.ctx.terms.mk_var("bool_index", Sort::Bool);
    let incompatible_index_read = pair.executor.ctx.terms.mk_app(
        Symbol::named("select"),
        [bool_indexed_array, bool_index],
        Sort::Int,
    );
    let incompatible_index_equality = raw_equality(
        &mut pair.executor,
        Symbol::named("="),
        pair.left,
        incompatible_index_read,
    );
    assert!(pair
        .executor
        .strict_oracle_select_congruence_lemma(&empty_model(), incompatible_index_equality)
        .is_none());

    let (array, _) = pair
        .executor
        .exact_cegar_select_parts(pair.left)
        .expect("fixture read must be canonical");
    let dangling_read = pair.executor.ctx.terms.mk_app(
        Symbol::named("select"),
        [array, TermId(u32::MAX)],
        Sort::Int,
    );
    assert!(pair
        .executor
        .exact_cegar_select_parts(dangling_read)
        .is_none());
}

#[test]
fn store_shape_used_by_qfax_cegar_is_exact_and_well_sorted() {
    let mut pair = canonical_read_pair();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let array = pair
        .executor
        .ctx
        .terms
        .mk_var("store_array", array_sort.clone());
    let index = pair.executor.ctx.terms.mk_var("store_index", Sort::Int);
    let value = pair.executor.ctx.terms.mk_var("store_value", Sort::Int);
    let canonical = pair.executor.ctx.terms.mk_app(
        Symbol::named("store"),
        [array, index, value],
        array_sort.clone(),
    );
    let indexed = pair.executor.ctx.terms.mk_app(
        Symbol::indexed("store", vec![0]),
        [array, index, value],
        array_sort.clone(),
    );
    let bool_term = pair.executor.ctx.terms.mk_var("store_bool", Sort::Bool);
    let wrong_index = pair.executor.ctx.terms.mk_app(
        Symbol::named("store"),
        [array, bool_term, value],
        array_sort.clone(),
    );
    let wrong_value = pair.executor.ctx.terms.mk_app(
        Symbol::named("store"),
        [array, index, bool_term],
        array_sort,
    );
    let wrong_result = pair.executor.ctx.terms.mk_app(
        Symbol::named("store"),
        [array, index, value],
        Sort::array(Sort::Bool, Sort::Int),
    );

    assert_eq!(
        pair.executor.exact_cegar_store_parts(canonical),
        Some((array, index, value))
    );
    for malformed in [indexed, wrong_index, wrong_value, wrong_result] {
        assert!(pair.executor.exact_cegar_store_parts(malformed).is_none());
    }
}

#[test]
fn malformed_distinct_never_enters_the_datatype_array_census() {
    let mut executor = Executor::new();
    let left = executor.ctx.terms.mk_var("distinct_left", Sort::Int);
    let right = executor.ctx.terms.mk_var("distinct_right", Sort::Int);
    let boolean = executor.ctx.terms.mk_var("distinct_bool", Sort::Bool);
    let good = executor
        .ctx
        .terms
        .mk_app(Symbol::named("distinct"), [left, right], Sort::Bool);
    let unary = executor
        .ctx
        .terms
        .mk_app(Symbol::named("distinct"), [left], Sort::Bool);
    let heterogeneous =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("distinct"), [left, boolean], Sort::Bool);
    let wrong_result =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("distinct"), [left, right], Sort::Int);
    let dangling = executor.ctx.terms.mk_app(
        Symbol::named("distinct"),
        [left, TermId(u32::MAX)],
        Sort::Bool,
    );
    assert_eq!(
        executor.exact_cegar_distinct_operands(good),
        Some(vec![left, right])
    );
    for malformed in [unary, heterogeneous, wrong_result, dangling] {
        assert!(executor.exact_cegar_distinct_operands(malformed).is_none());
    }
}

#[test]
fn oversized_distinct_declines_before_census_pairing() {
    let mut executor = Executor::new();
    let operands = (0..257)
        .map(|i| {
            executor
                .ctx
                .terms
                .mk_var(format!("oversized_distinct_{i}"), Sort::Int)
        })
        .collect::<Vec<_>>();
    let distinct = executor
        .ctx
        .terms
        .mk_app(Symbol::named("distinct"), operands, Sort::Bool);

    assert!(executor.exact_cegar_distinct_operands(distinct).is_none());
}

#[test]
fn selector_lookup_rejects_indexed_and_malformed_spoofs() {
    let commands = parse("(declare-datatype CegarBox ((cegar_box (cegar_value Int))))")
        .expect("datatype declaration parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("datatype declaration executes");
    let selector = executor
        .ctx
        .constructor_selector_info("cegar_box")
        .expect("constructor metadata exists")[0]
        .0
        .clone();
    let (argument_sort, result_sort) = {
        let signature = executor
            .ctx
            .exact_datatype_member_info(&selector)
            .expect("selector has exact metadata");
        (signature.arg_sorts[0].clone(), signature.sort.clone())
    };
    let argument = executor
        .ctx
        .terms
        .mk_var("selector_argument", argument_sort);
    let indexed = executor.ctx.terms.mk_app(
        Symbol::indexed(selector.clone(), vec![0]),
        [argument],
        result_sort.clone(),
    );
    let malformed =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named(selector.clone()), [argument], Sort::Bool);
    assert!(executor.find_dt_selector_app(&selector, argument).is_none());

    let exact = executor
        .ctx
        .terms
        .mk_app(Symbol::named(selector.clone()), [argument], result_sort);
    assert_eq!(
        executor.find_dt_selector_app(&selector, argument),
        Some(exact),
        "the indexed and wrong-result terms ({indexed:?}, {malformed:?}) must be skipped"
    );
}

#[test]
fn emitted_cross_array_lemma_has_checker_recognized_shape() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let left_array = executor
        .ctx
        .terms
        .mk_var("lemma_left_array", array_sort.clone());
    let right_array = executor.ctx.terms.mk_var("lemma_right_array", array_sort);
    let index = executor.ctx.terms.mk_var("lemma_index", Sort::Int);
    let left_read =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [left_array, index], Sort::Int);
    let right_read =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [right_array, index], Sort::Int);
    let equality = raw_equality(&mut executor, Symbol::named("="), left_read, right_read);
    let lemma = executor
        .strict_oracle_select_congruence_lemma(&empty_model(), equality)
        .expect("exact reads must produce a congruence lemma");

    let TermData::App(Symbol::Named(operator), literals) = executor.ctx.terms.get(lemma) else {
        panic!("congruence lemma must be a disjunction");
    };
    assert_eq!(operator, "or");
    assert_eq!(literals.len(), 2);
    assert!(ay_proof::recognize_array_theory_lemma(&executor.ctx.terms, &[lemma]).is_some());
}
