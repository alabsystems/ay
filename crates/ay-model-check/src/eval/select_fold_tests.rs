// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[path = "select_fold_tests/authority.rs"]
mod authority;

#[derive(Default)]
struct CountedModel {
    leaves: HashMap<TermId, ModelValue>,
    reads: HashMap<TermId, ModelValue>,
    leaf_calls: RefCell<Vec<TermId>>,
    read_calls: RefCell<Vec<TermId>>,
}

impl ModelView for CountedModel {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        let mut calls = self.leaf_calls.borrow_mut();
        // A regressed exponential traversal fails deterministically instead of
        // leaving the test process spinning at the deepest authored case.
        assert!(calls.len() < 256, "repeated failed leaf reconstruction");
        calls.push(term);
        self.leaves.get(&term).cloned()
    }

    fn array_select_value(&self, term: TermId) -> Option<ModelValue> {
        self.read_calls.borrow_mut().push(term);
        self.reads.get(&term).cloned()
    }
}

fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

fn bv(value: u64) -> ModelValue {
    ModelValue::bitvec(BigInt::from(value), 64)
}

fn constant_array(value: bool) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Bool(value),
        store: Vec::new(),
    }))
}

fn assert_bool(value: EvalResult<ModelValue>, expected: bool) {
    assert!(matches!(value, Ok(ModelValue::Bool(actual)) if actual == expected));
}

#[test]
fn failed_nested_bases_are_walked_once_per_attempt_without_error_memoization() {
    for depth in [1, 8, 65] {
        let mut terms = TermStore::new();
        let mut sorts = vec![Sort::Bool];
        for index in 0..depth {
            sorts.push(Sort::array(Sort::bitvec(64), sorts[index].clone()));
        }
        let base = terms.mk_var("base", sorts[depth].clone());
        let zero = terms.mk_bitvec(BigInt::from(0), 64);
        let mut read = base;
        for index in (0..depth).rev() {
            read = app(&mut terms, "select", &[read, zero], sorts[index].clone());
        }
        let model = CountedModel::default();
        let evaluator = Evaluator::new(&terms, &model);
        for attempt in 1..=2 {
            let reason = evaluator.eval(read, 0).expect_err("base remains unpinned");
            assert!(reason
                .to_string()
                .contains("model does not pin this leaf: base"));
            assert_eq!(model.leaf_calls.borrow().as_slice(), vec![base; attempt]);
            assert_eq!(model.read_calls.borrow().len(), depth * attempt);
        }
        assert!(evaluator.memo.borrow().is_empty());
        assert!(evaluator.select_graph.borrow().is_empty());
    }
}

#[test]
fn a_known_miss_uses_the_original_read_pin_without_visiting_irrelevant_writes() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let base = terms.mk_var("base", sort.clone());
    let irrelevant = terms.mk_var("irrelevant", Sort::Bool);
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let one = terms.mk_bitvec(BigInt::from(1), 64);
    let updated = app(&mut terms, "store", &[base, one, irrelevant], sort);
    let base_read = app(&mut terms, "select", &[base, zero], Sort::Bool);
    let original_read = app(&mut terms, "select", &[updated, zero], Sort::Bool);
    let mut model = CountedModel::default();
    model.reads.insert(base_read, ModelValue::Bool(false));
    model.reads.insert(original_read, ModelValue::Bool(true));
    let evaluator = Evaluator::new(&terms, &model);
    // A proved miss denotes the same base/index pair, but any new pin must
    // still be acquired from the original source read, not a synthetic term.
    assert_bool(evaluator.eval(base_read, 0), false);
    assert_bool(evaluator.eval(original_read, 0), false);
    assert_eq!(model.leaf_calls.borrow().as_slice(), &[base, base]);
    assert_eq!(model.read_calls.borrow().as_slice(), &[base_read]);
    let graph = evaluator.select_graph.borrow();
    assert_eq!(graph.len(), 1);
    assert_eq!(graph[0].0, base);
    drop(graph);
    let evaluator = Evaluator::new(&terms, &model);
    assert_bool(evaluator.eval(original_read, 0), true);
    assert_bool(evaluator.eval(base_read, 0), true);
    assert_eq!(
        model.read_calls.borrow().as_slice(),
        &[base_read, original_read]
    );
    assert_eq!(evaluator.select_graph.borrow().len(), 1);
    assert_eq!(evaluator.select_graph.borrow()[0].0, base);
}

#[test]
fn original_array_and_equal_index_values_still_share_one_read_commitment() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let base = terms.mk_var("base", sort.clone());
    let i = terms.mk_var("i", Sort::bitvec(64));
    let j = terms.mk_var("j", Sort::bitvec(64));
    let one = terms.mk_bitvec(BigInt::from(1), 64);
    let irrelevant = terms.mk_var("irrelevant", Sort::Bool);
    let updated = app(&mut terms, "store", &[base, one, irrelevant], sort);
    let left = app(&mut terms, "select", &[updated, i], Sort::Bool);
    let right = app(&mut terms, "select", &[updated, j], Sort::Bool);
    let mut model = CountedModel::default();
    model.leaves.extend([(i, bv(0)), (j, bv(0))]);
    model.reads.extend([
        (left, ModelValue::Bool(true)),
        (right, ModelValue::Bool(false)),
    ]);
    let evaluator = Evaluator::new(&terms, &model);
    assert_bool(evaluator.eval(left, 0), true);
    assert_bool(evaluator.eval(right, 0), true);
    assert_eq!(model.read_calls.borrow().as_slice(), &[left]);
    assert_eq!(evaluator.select_graph.borrow().len(), 1);
    assert_eq!(evaluator.select_graph.borrow()[0].0, base);
}

#[test]
fn read_pins_and_memo_remain_isolated_from_local_index_bindings() {
    let mut terms = TermStore::new();
    let base = terms.mk_var("base", Sort::array(Sort::bitvec(64), Sort::Bool));
    let index = terms.mk_var("index", Sort::bitvec(64));
    let unrelated = terms.mk_var("unrelated", Sort::Bool);
    let read = app(&mut terms, "select", &[base, index], Sort::Bool);
    let mut model = CountedModel::default();
    model.leaves.insert(index, bv(0));
    model.reads.insert(read, ModelValue::Bool(true));
    let evaluator = Evaluator::new(&terms, &model);
    assert_bool(evaluator.eval(read, 0), true);
    let reason = evaluator
        .eval_with_binding(index, bv(1), read, 0)
        .expect_err("ambient read pin does not bind the changed index");
    assert!(reason.to_string().contains("context-dependent array read"));
    assert!(evaluator.local_bindings.borrow().is_empty());
    assert_bool(evaluator.eval(read, 0), true);
    assert_bool(
        evaluator.eval_with_binding(unrelated, ModelValue::Bool(false), read, 0),
        true,
    );
    assert!(evaluator.local_bindings.borrow().is_empty());
    assert_eq!(model.read_calls.borrow().as_slice(), &[read]);
    assert_eq!(evaluator.select_graph.borrow().len(), 1);
}

#[test]
fn terminal_depth_failure_does_not_poison_a_shallower_retry() {
    let mut terms = TermStore::new();
    let base = terms.mk_var("base", Sort::array(Sort::bitvec(64), Sort::Bool));
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let read = app(&mut terms, "select", &[base, zero], Sort::Bool);
    let mut model = CountedModel::default();
    model.leaves.insert(base, constant_array(true));
    model.reads.insert(read, ModelValue::Bool(false));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.select_over_store_chain(base, &bv(0), MAX_EVAL_DEPTH),
        Err(EvalError::Resource {
            kind: EvalResource::Depth,
            ..
        })
    ));
    assert!(model.leaf_calls.borrow().is_empty());
    assert!(matches!(
        evaluator.select_over_store_chain(base, &bv(0), 0),
        Ok(SelectFold::Value(ModelValue::Bool(true)))
    ));
    assert!(matches!(
        evaluator.select_over_store_chain(base, &bv(0), MAX_EVAL_DEPTH + 1),
        Err(EvalError::Resource {
            kind: EvalResource::Depth,
            ..
        })
    ));
    assert_eq!(model.leaf_calls.borrow().as_slice(), &[base]);
    assert_bool(evaluator.eval(read, 0), true);
    assert!(model.read_calls.borrow().is_empty());
}

#[test]
fn unknown_store_keys_request_reconstruction_but_hard_errors_stay_errors() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let base = terms.mk_var("base", sort.clone());
    let key = terms.mk_var("key", Sort::bitvec(64));
    let yes = terms.mk_bool(true);
    let unknown_store = app(&mut terms, "store", &[base, key, yes], sort.clone());
    let bad_key = terms.mk_bool(false);
    let invalid_store = app(&mut terms, "store", &[base, bad_key, yes], sort.clone());
    let constant = app(&mut terms, "const-array", &[yes], sort.clone());
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let invalid_lambda = app(&mut terms, "lambda-array", &[zero, yes], sort);
    let model = CountedModel::default();
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.select_over_store_chain(unknown_store, &bv(0), 0),
        Ok(SelectFold::Reconstruct { array }) if array == unknown_store
    ));
    assert!(evaluator
        .select_over_store_chain(invalid_store, &bv(0), 0)
        .is_err());
    assert!(evaluator
        .select_over_store_chain(invalid_lambda, &bv(0), 0)
        .is_err());
    assert!(matches!(
        evaluator.select_over_store_chain(constant, &bv(0), 0),
        Ok(SelectFold::Value(ModelValue::Bool(true)))
    ));
    assert_eq!(model.leaf_calls.borrow().as_slice(), &[key]);
    assert!(model.read_calls.borrow().is_empty());
}

fn missed_reads(terms: &mut TermStore, count: usize) -> (TermId, TermId, TermId) {
    let sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let base = terms.mk_var("base", sort.clone());
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let base_read = app(terms, "select", &[base, zero], Sort::Bool);
    let irrelevant = terms.mk_var("irrelevant", Sort::Bool);
    let mut updated = base;
    for key in 1..=count {
        let key = terms.mk_bitvec(BigInt::from(key), 64);
        updated = app(terms, "store", &[updated, key, irrelevant], sort.clone());
    }
    let original_read = app(terms, "select", &[updated, zero], Sort::Bool);
    (base, base_read, original_read)
}

#[test]
fn full_gate_rejects_conflicting_known_miss_pins_in_either_assertion_order() {
    for count in [1, 3] {
        let mut terms = TermStore::new();
        let (base, base_read, original_read) = missed_reads(&mut terms, count);
        let base_false = terms.mk_not_raw(base_read);
        let mut model = CountedModel::default();
        model.reads.extend([
            (base_read, ModelValue::Bool(false)),
            (original_read, ModelValue::Bool(true)),
        ]);
        for roots in [[base_false, original_read], [original_read, base_false]] {
            let result = crate::confirm_model(&terms, &model, &roots);
            assert!(matches!(
                result,
                crate::GateVerdict::ModelViolates { .. } | crate::GateVerdict::CannotConfirm { .. }
            ));
        }
        assert!(model.leaf_calls.borrow().iter().all(|term| *term == base));
    }
}

#[test]
fn full_gate_accepts_consistent_known_miss_pins_in_both_orders() {
    for count in [1, 3] {
        for value in [false, true] {
            let mut terms = TermStore::new();
            let (base, base_read, original_read) = missed_reads(&mut terms, count);
            let roots = if value {
                [base_read, original_read]
            } else {
                [terms.mk_not_raw(base_read), terms.mk_not_raw(original_read)]
            };
            let mut model = CountedModel::default();
            model.reads.extend([
                (base_read, ModelValue::Bool(value)),
                (original_read, ModelValue::Bool(value)),
            ]);
            for roots in [roots, [roots[1], roots[0]]] {
                assert!(matches!(
                    crate::confirm_model(&terms, &model, &roots),
                    crate::GateVerdict::ConfirmedSat
                ));
            }
            assert!(model.leaf_calls.borrow().iter().all(|term| *term == base));
        }
    }
}

#[test]
fn an_unknown_store_key_cannot_authorize_an_updated_read_pin() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let base = terms.mk_var("base", sort.clone());
    let unknown = terms.mk_var("unknown", Sort::bitvec(64));
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let yes = terms.mk_bool(true);
    let updated = app(&mut terms, "store", &[base, unknown, yes], sort);
    let base_read = app(&mut terms, "select", &[base, zero], Sort::Bool);
    let updated_read = app(&mut terms, "select", &[updated, zero], Sort::Bool);
    let mut model = CountedModel::default();
    model.reads.extend([
        (base_read, ModelValue::Bool(false)),
        (updated_read, ModelValue::Bool(true)),
    ]);
    for order in [[base_read, updated_read], [updated_read, base_read]] {
        let evaluator = Evaluator::new(&terms, &model);
        for read in order {
            if read == updated_read {
                assert!(matches!(
                    evaluator.eval(read, 0),
                    Err(EvalError::Refused(_))
                ));
            } else {
                assert_bool(evaluator.eval(read, 0), false);
            }
        }
        let graph = evaluator.select_graph.borrow();
        assert_eq!(graph.len(), 1);
        assert_eq!(graph[0].0, base);
        assert!(!evaluator.memo.borrow().contains_key(&updated_read));
    }
    assert!(!model.read_calls.borrow().contains(&updated_read));

    // A real key assignment establishes the hit, without adopting its read pin.
    model.leaves.insert(unknown, bv(0));
    let evaluator = Evaluator::new(&terms, &model);
    assert_bool(evaluator.eval(updated_read, 0), true);
    assert_bool(evaluator.eval(base_read, 0), false);
    assert!(!model.read_calls.borrow().contains(&updated_read));
}

#[test]
fn a_bound_original_store_cannot_borrow_the_ambient_base_graph() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let base = terms.mk_var("base", sort.clone());
    let key = terms.mk_var("key", Sort::bitvec(64));
    let value = terms.mk_var("value", Sort::Bool);
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let updated = app(&mut terms, "store", &[base, key, value], sort);
    let base_read = app(&mut terms, "select", &[base, zero], Sort::Bool);
    let updated_read = app(&mut terms, "select", &[updated, zero], Sort::Bool);
    let mut model = CountedModel::default();
    model.leaves.insert(key, bv(1));
    model.reads.extend([
        (base_read, ModelValue::Bool(false)),
        (updated_read, ModelValue::Bool(true)),
    ]);
    let evaluator = Evaluator::new(&terms, &model);
    assert_bool(evaluator.eval(base_read, 0), false);
    for (bound, assigned) in [(key, bv(1)), (value, ModelValue::Bool(true))] {
        let reason = evaluator
            .eval_with_binding(bound, assigned, updated_read, 0)
            .expect_err("the original store expression depends on this local binding");
        assert!(reason.to_string().contains("context-dependent array read"));
        assert!(evaluator.local_bindings.borrow().is_empty());
        assert_eq!(evaluator.select_graph.borrow().len(), 1);
        assert_eq!(model.read_calls.borrow().as_slice(), &[base_read]);
    }
    assert_bool(evaluator.eval(updated_read, 0), false);
    assert_eq!(model.read_calls.borrow().as_slice(), &[base_read]);
}

#[test]
fn a_known_miss_prefix_cannot_hide_an_unresolved_inner_store_equation() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let base = terms.mk_var("base", sort.clone());
    let unknown = terms.mk_var("unknown", Sort::bitvec(64));
    let missing = terms.mk_var("missing", Sort::Bool);
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let one = terms.mk_bitvec(BigInt::from(1), 64);
    let no = terms.mk_bool(false);
    let inner = app(&mut terms, "store", &[base, unknown, no], sort.clone());
    let outer = app(&mut terms, "store", &[inner, one, missing], sort);
    let inner_read = app(&mut terms, "select", &[inner, zero], Sort::Bool);
    let outer_read = app(&mut terms, "select", &[outer, zero], Sort::Bool);
    let inner_false = terms.mk_not_raw(inner_read);
    let mut model = CountedModel::default();
    model.reads.extend([
        (inner_read, ModelValue::Bool(false)),
        (outer_read, ModelValue::Bool(true)),
    ]);
    for roots in [[inner_false, outer_read], [outer_read, inner_false]] {
        assert!(matches!(
            crate::confirm_model(&terms, &model, &roots),
            crate::GateVerdict::ModelViolates { .. } | crate::GateVerdict::CannotConfirm { .. }
        ));
    }
    let evaluator = Evaluator::new(&terms, &model);
    for read in [outer_read, inner_read] {
        assert!(matches!(
            evaluator.eval(read, 0),
            Err(EvalError::Refused(_))
        ));
        assert!(!evaluator.memo.borrow().contains_key(&read));
    }
    assert!(evaluator.select_graph.borrow().is_empty());
    assert!(model.read_calls.borrow().is_empty());
    assert!(!model.leaf_calls.borrow().contains(&missing));

    // Once the inner key is pinned, the proved outer miss preserves its hit
    // value and still does not evaluate the irrelevant outer write.
    model.leaves.insert(unknown, bv(0));
    let evaluator = Evaluator::new(&terms, &model);
    assert_bool(evaluator.eval(outer_read, 0), false);
    assert_bool(evaluator.eval(inner_read, 0), false);
    assert!(model.read_calls.borrow().is_empty());
    assert!(!model.leaf_calls.borrow().contains(&missing));
}
