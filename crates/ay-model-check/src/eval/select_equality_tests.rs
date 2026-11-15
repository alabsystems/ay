// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Equality must not materialize arrays before exact scalar reads can run.

use super::*;

#[path = "select_equality_tests/fixtures.rs"]
mod fixtures;
use fixtures::*;

#[test]
fn equal_lambda_reads_are_confirmed_without_a_finite_array_or_read_pin() {
    let (mut terms, model, reads) = linear_case(2);
    let root = equality(&mut terms, &reads);
    assert_gate_boolean(&terms, &model, root, true);
    assert!(model.read_calls.borrow().is_empty());
    assert!(model.application_calls.borrow().is_empty());
}

#[test]
fn unequal_lambda_reads_refute_wrong_equality_without_read_pins() {
    let (mut terms, model, reads) = linear_case(3);
    let root = equality(&mut terms, &reads);
    let opposite = terms.mk_not(root);
    assert_gate_boolean(&terms, &model, root, false);
    assert_gate_boolean(&terms, &model, opposite, true);
    assert!(model.read_calls.borrow().is_empty());
}

#[test]
fn nary_equality_checks_the_later_pointwise_value() {
    let (mut terms, model, reads) = linear_case(2);
    let array = lambda(&mut terms, 1);
    let three = terms.mk_int(BigInt::from(3));
    let third = read(&mut terms, array, three);
    let root = equality(&mut terms, &[reads[0], reads[1], third]);
    assert_gate_boolean(&terms, &model, root, false);
    assert!(model.read_calls.borrow().is_empty());
}

fn byte_copy_case(address: u64, length: u64) -> (TermStore, Model, TermId) {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let last = terms.mk_bitvec(BigInt::from(u64::MAX), 64);
    let empty = terms.mk_bitvec(BigInt::from(0), 8);
    let eleven = terms.mk_bitvec(BigInt::from(11), 8);
    let ninety_nine = terms.mk_bitvec(BigInt::from(99), 8);
    let base = app(&mut terms, "const-array", &[empty], sort.clone());
    let base = app(&mut terms, "store", &[base, zero, eleven], sort.clone());
    let base = app(
        &mut terms,
        "store",
        &[base, last, ninety_nine],
        sort.clone(),
    );
    let bound = terms.mk_var("copy_address", Sort::bitvec(64));
    let count = terms.mk_var("length", Sort::bitvec(64));
    let index = terms.mk_var("arbitrary_address", Sort::bitvec(64));
    let relative = app(&mut terms, "bvsub", &[bound, last], Sort::bitvec(64));
    let in_range = app(&mut terms, "bvult", &[relative, count], Sort::Bool);
    let source = app(&mut terms, "select", &[base, zero], Sort::bitvec(8));
    let original = app(&mut terms, "select", &[base, bound], Sort::bitvec(8));
    let body = terms.mk_ite_raw(in_range, source, original);
    let copied = app(&mut terms, "lambda-array", &[bound, body], sort);
    let left = app(&mut terms, "select", &[copied, index], Sort::bitvec(8));
    let right = app(&mut terms, "select", &[base, index], Sort::bitvec(8));
    let root = equality(&mut terms, &[left, right]);
    let mut model = Model::default();
    model
        .leaves
        .insert(count, ModelValue::bitvec(BigInt::from(length), 64));
    model
        .leaves
        .insert(index, ModelValue::bitvec(BigInt::from(address), 64));
    (terms, model, root)
}

#[test]
fn zero_length_copy_preserves_known_and_arbitrary_full_width_addresses() {
    for address in [0, 7, u64::MAX] {
        let (terms, model, root) = byte_copy_case(address, 0);
        assert_gate_boolean(&terms, &model, root, true);
        assert!(model.read_calls.borrow().is_empty());
    }
}

#[test]
fn nonzero_copy_at_the_last_address_is_not_mistaken_for_zero_length() {
    let (terms, model, root) = byte_copy_case(u64::MAX, 1);
    assert_gate_boolean(&terms, &model, root, false);
    assert!(model.read_calls.borrow().is_empty());
}

#[test]
fn raw_ite_and_named_conditionals_select_the_exact_lambda_read() {
    for kind in 0..3 {
        for choice in [false, true] {
            let mut terms = TermStore::new();
            let positive = lambda(&mut terms, 1);
            let negative = lambda(&mut terms, 2);
            let condition = terms.mk_var("choose", Sort::Bool);
            let array = match kind {
                0 => terms.mk_ite_raw(condition, positive, negative),
                _ => app(
                    &mut terms,
                    if kind == 1 { "ite" } else { "if" },
                    &[condition, positive, negative],
                    Sort::array(Sort::Int, Sort::Int),
                ),
            };
            let index = terms.mk_int(BigInt::from(2));
            let left = read(&mut terms, array, index);
            let right = read(&mut terms, positive, index);
            let root = equality(&mut terms, &[left, right]);
            let mut model = Model::default();
            model.leaves.insert(condition, ModelValue::Bool(choice));
            model.reads.insert(left, integer(3));
            assert_gate_boolean(&terms, &model, root, choice);
            assert!(model.read_calls.borrow().is_empty());
        }
    }
}

#[test]
fn unknown_conditional_guards_do_not_authorize_a_read_pin() {
    let (mut terms, model, reads) = linear_case(2);
    let positive = lambda(&mut terms, 1);
    let negative = lambda(&mut terms, 2);
    let condition = terms.mk_var("missing_guard", Sort::Bool);
    let array = terms.mk_ite_raw(condition, positive, negative);
    let index = terms.mk_int(BigInt::from(2));
    let guarded = read(&mut terms, array, index);
    let mut model = model;
    model.reads.insert(guarded, integer(3));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.eval_eq(&[guarded, reads[0]], 0),
        Err(EvalError::Refused(_))
    ));
    assert!(model.read_calls.borrow().is_empty());
    assert!(evaluator.select_graph.borrow().is_empty());
}

#[test]
fn malformed_select_arity_index_and_result_sorts_stay_refused() {
    for case in 0..3 {
        let mut terms = TermStore::new();
        let value = terms.mk_int(BigInt::from(3));
        let array = app(
            &mut terms,
            "const-array",
            &[value],
            Sort::array(Sort::Int, Sort::Int),
        );
        let left_index = terms.mk_var("left_index", if case == 1 { Sort::Bool } else { Sort::Int });
        let right_index = terms.mk_var(
            "right_index",
            if case == 1 { Sort::Bool } else { Sort::Int },
        );
        let args = |index| {
            if case == 0 {
                vec![array, index, value]
            } else {
                vec![array, index]
            }
        };
        let result_sort = if case == 2 { Sort::Bool } else { Sort::Int };
        let left = app(&mut terms, "select", &args(left_index), result_sort.clone());
        let right = app(&mut terms, "select", &args(right_index), result_sort);
        assert_ne!(left, right);
        let mut model = Model::default();
        for index in [left_index, right_index] {
            model.leaves.insert(
                index,
                if case == 1 {
                    ModelValue::Bool(false)
                } else {
                    integer(0)
                },
            );
        }
        model.reads.insert(left, integer(3));
        model.reads.insert(right, integer(3));
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(
            evaluator.eval_eq(&[left, right], 0),
            Err(EvalError::Refused(_))
        ));
        assert!(model.read_calls.borrow().is_empty());
        assert!(evaluator.select_graph.borrow().is_empty());
    }
}

#[test]
fn malformed_lambda_metadata_does_not_turn_into_an_opaque_read() {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("wrong_binder", Sort::Bool);
    let body = terms.mk_int(BigInt::from(3));
    let array = app(
        &mut terms,
        "lambda-array",
        &[bound, body],
        Sort::array(Sort::Int, Sort::Int),
    );
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let left = read(&mut terms, array, zero);
    let right = read(&mut terms, array, one);
    let mut model = Model::default();
    model.reads.insert(left, integer(3));
    model.reads.insert(right, integer(3));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.eval_eq(&[left, right], 0),
        Err(EvalError::Refused(_))
    ));
    assert!(model.read_calls.borrow().is_empty());
}

#[test]
fn read_equality_keeps_depth_failure_and_restricted_subset_shallower_retry() {
    let (terms, model, reads) = linear_case(2);
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.eval_eq(&reads, MAX_EVAL_DEPTH - 2),
        Err(EvalError::Resource {
            kind: EvalResource::Depth,
            ..
        })
    ));
    assert!(model.read_calls.borrow().is_empty());
    assert!(evaluator.select_graph.borrow().is_empty());
    assert!(evaluator.local_bindings.borrow().is_empty());
    assert!(matches!(
        evaluator.eval_eq(&reads, 0),
        Ok(ModelValue::Bool(true))
    ));
}

#[test]
fn nested_read_equality_cannot_borrow_a_lambda_dependent_pin() {
    let mut terms = TermStore::new();
    let base = terms.mk_var("opaque", Sort::array(Sort::Int, Sort::Int));
    let bound = terms.mk_var("bound", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let dependent = read(&mut terms, base, bound);
    let independent = read(&mut terms, base, zero);
    let body = equality(&mut terms, &[dependent, independent]);
    let array = app(
        &mut terms,
        "lambda-array",
        &[bound, body],
        Sort::array(Sort::Int, Sort::Bool),
    );
    let selected = app(&mut terms, "select", &[array, zero], Sort::Bool);
    let mut model = Model::default();
    model.reads.insert(dependent, integer(7));
    model.reads.insert(independent, integer(7));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.eval(selected, 0),
        Err(EvalError::Refused(_))
    ));
    assert!(evaluator.local_bindings.borrow().is_empty());
    assert!(evaluator.select_graph.borrow().is_empty());
    assert!(model.read_calls.borrow().is_empty());
    assert!(
        matches!(evaluator.eval(independent, 0), Ok(ModelValue::Int(n)) if n == BigInt::from(7))
    );
}

#[test]
fn opaque_reads_keep_first_wins_congruence_in_both_orders() {
    let mut terms = TermStore::new();
    let array = terms.mk_var("opaque", Sort::array(Sort::Int, Sort::Int));
    let left_index = terms.mk_var("left_index", Sort::Int);
    let right_index = terms.mk_var("right_index", Sort::Int);
    let reads = [
        read(&mut terms, array, left_index),
        read(&mut terms, array, right_index),
    ];
    let mut model = Model::default();
    model.leaves.insert(left_index, integer(0));
    model.leaves.insert(right_index, integer(0));
    model.reads.insert(reads[0], integer(5));
    model.reads.insert(reads[1], integer(7));
    for operands in [reads, [reads[1], reads[0]]] {
        model.read_calls.borrow_mut().clear();
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(
            evaluator.eval_eq(&operands, 0),
            Ok(ModelValue::Bool(true))
        ));
        assert_eq!(evaluator.select_graph.borrow().len(), 1);
        assert_eq!(model.read_calls.borrow().len(), 1);
    }
}

#[test]
fn opaque_reads_without_a_committed_value_do_not_become_true() {
    let mut terms = TermStore::new();
    let array = terms.mk_var("opaque", Sort::array(Sort::Int, Sort::Int));
    let left_index = terms.mk_int(BigInt::from(0));
    let zero = terms.mk_int(BigInt::from(0));
    let right_index = app(&mut terms, "+", &[zero, zero], Sort::Int);
    let reads = [
        read(&mut terms, array, left_index),
        read(&mut terms, array, right_index),
    ];
    let model = Model::default();
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.eval_eq(&reads, 0),
        Err(EvalError::ModelUnavailable(_))
    ));
    assert!(evaluator.select_graph.borrow().is_empty());
}

#[test]
fn nonselect_functions_keep_their_original_congruence_shortcut() {
    for name in ["ordinary_function", "select-data"] {
        let mut terms = TermStore::new();
        let left = terms.mk_var("left", Sort::Int);
        let right = terms.mk_var("right", Sort::Int);
        let left_app = app(&mut terms, name, &[left], Sort::Int);
        let right_app = app(&mut terms, name, &[right], Sort::Int);
        let root = equality(&mut terms, &[left_app, right_app]);
        let mut model = Model::default();
        model.leaves.insert(left, integer(4));
        model.leaves.insert(right, integer(4));
        assert_gate_boolean(&terms, &model, root, true);
        assert!(model.application_calls.borrow().is_empty());
    }
}

#[test]
fn unrelated_uf_lambda_arguments_keep_their_hard_refusal() {
    let mut terms = TermStore::new();
    let left_array = lambda(&mut terms, 1);
    let right_array = lambda(&mut terms, 2);
    let left = app(&mut terms, "observe_array", &[left_array], Sort::Int);
    let right = app(&mut terms, "observe_array", &[right_array], Sort::Int);
    let mut model = Model::default();
    model.applications.insert(left, integer(3));
    model.applications.insert(right, integer(3));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.eval_eq(&[left, right], 0),
        Err(EvalError::Refused(_))
    ));
    assert!(model.application_calls.borrow().is_empty());
}

#[test]
fn checked_read_projection_metadata_is_not_bypassed_by_raw_congruence() {
    for projection in [
        Err(crate::ProjectionLookupError::inconsistent_model(
            "authored refusal",
        )),
        Ok(Some(7)),
        Ok(Some(0)),
    ] {
        let (terms, mut model, reads) = linear_case(2);
        model.projections.insert(reads[0], projection);
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(
            evaluator.eval_eq(&reads, 0),
            Err(EvalError::Refused(_))
        ));
        assert!(model.read_calls.borrow().is_empty());
        assert!(evaluator.select_graph.borrow().is_empty());
    }
}

#[test]
fn indexed_select_spelling_does_not_acquire_builtin_or_opaque_read_authority() {
    let mut terms = TermStore::new();
    let array = lambda(&mut terms, 1);
    let left_index = terms.mk_int(BigInt::from(0));
    let right_index = terms.mk_int(BigInt::from(1));
    let left = terms.mk_app(
        Symbol::indexed("select", vec![0]),
        &[array, left_index],
        Sort::Int,
    );
    let right = terms.mk_app(
        Symbol::indexed("select", vec![0]),
        &[array, right_index],
        Sort::Int,
    );
    let mut model = Model::default();
    model.reads.insert(left, integer(0));
    model.reads.insert(right, integer(0));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(evaluator.eval_eq(&[left, right], 0).is_err());
    assert!(model.read_calls.borrow().is_empty());
    assert!(evaluator.select_graph.borrow().is_empty());
}
