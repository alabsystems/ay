// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{
    confirm_completed_model, confirm_model, confirm_model_with_array_completion, GateVerdict,
};

#[derive(Default)]
struct Values {
    leaves: HashMap<TermId, ModelValue>,
    reads: HashMap<TermId, ModelValue>,
    functions: HashMap<TermId, ModelValue>,
    read_calls: RefCell<Vec<TermId>>,
    function_calls: RefCell<Vec<TermId>>,
}

impl ModelView for Values {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.leaves.get(&term).cloned()
    }

    fn array_select_value(&self, term: TermId) -> Option<ModelValue> {
        self.read_calls.borrow_mut().push(term);
        self.reads.get(&term).cloned()
    }

    fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
        self.function_calls.borrow_mut().push(term);
        self.functions.get(&term).cloned()
    }
}

fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

fn integer(value: i32) -> ModelValue {
    ModelValue::Int(BigInt::from(value))
}

fn refuses_both_gates(terms: &TermStore, model: &Values, roots: &[TermId]) {
    let original = confirm_model(terms, model, roots);
    let completed = confirm_completed_model(terms, model, roots);
    let (verdict, completion) =
        confirm_model_with_array_completion(terms, model, roots).into_parts();
    let verdicts = [original, completed, verdict];
    assert!(
        verdicts
            .iter()
            .all(|verdict| matches!(verdict, GateVerdict::CannotConfirm { .. })),
        "{verdicts:?}"
    );
    assert!(completion.is_none());
}

fn accepts_both_gates(terms: &TermStore, model: &Values, roots: &[TermId]) {
    assert!(matches!(
        confirm_model(terms, model, roots),
        GateVerdict::ConfirmedSat
    ));
    assert!(matches!(
        confirm_completed_model(terms, model, roots),
        GateVerdict::ConfirmedSat
    ));
}

struct ConstantStore {
    terms: TermStore,
    key: TermId,
    read: TermId,
    false_claim: TermId,
}

impl ConstantStore {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::Bool, Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let two = terms.mk_int(BigInt::from(2));
        let index = terms.mk_bool(false);
        let key = terms.mk_var("missing_key", Sort::Bool);
        let base = app(&mut terms, "const-array", &[zero], sort.clone());
        let stored = app(&mut terms, "store", &[base, key, zero], sort);
        let read = app(&mut terms, "select", &[stored, index], Sort::Int);
        let false_claim = terms.mk_eq(read, two);
        Self {
            terms,
            key,
            read,
            false_claim,
        }
    }
}

#[test]
fn an_unresolved_store_cannot_pin_two_when_every_cell_is_zero() {
    let fixture = ConstantStore::new();
    let mut model = Values::default();
    model.reads.insert(fixture.read, integer(2));
    refuses_both_gates(&fixture.terms, &model, &[fixture.false_claim]);
    assert!(model.read_calls.borrow().is_empty());
    let evaluator = Evaluator::new(&fixture.terms, &model);
    for _ in 0..2 {
        assert!(matches!(
            evaluator.eval(fixture.read, 0),
            Err(EvalError::Refused(_))
        ));
        assert!(!evaluator.memo.borrow().contains_key(&fixture.read));
        assert!(evaluator.select_graph.borrow().is_empty());
    }
}

#[test]
fn a_boolean_store_must_hit_one_of_the_two_observed_indices() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Bool, Sort::Bool);
    let base = terms.mk_var("base", sort.clone());
    let key = terms.mk_var("missing_key", Sort::Bool);
    let no = terms.mk_bool(false);
    let yes = terms.mk_bool(true);
    let stored = app(&mut terms, "store", &[base, key, yes], sort);
    let left = app(&mut terms, "select", &[stored, no], Sort::Bool);
    let right = app(&mut terms, "select", &[stored, yes], Sort::Bool);
    let left_false = terms.mk_not_raw(left);
    let right_false = terms.mk_not_raw(right);
    let mut model = Values::default();
    model.reads.extend([
        (left, ModelValue::Bool(false)),
        (right, ModelValue::Bool(false)),
    ]);
    // No assignment to the single Boolean key can make both reads false,
    // regardless of the unmaterialized base array or assertion order.
    for roots in [[left_false, right_false], [right_false, left_false]] {
        refuses_both_gates(&terms, &model, &roots);
    }
    assert!(model.read_calls.borrow().is_empty());
}

#[test]
fn pinned_keys_preserve_hits_and_partial_base_misses_in_both_orders() {
    for assigned_key in [false, true] {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::Bool, Sort::Bool);
        let base = terms.mk_var("base", sort.clone());
        let key = terms.mk_var("key", Sort::Bool);
        let hit_index = terms.mk_bool(assigned_key);
        let miss_index = terms.mk_bool(!assigned_key);
        let yes = terms.mk_bool(true);
        let stored = app(&mut terms, "store", &[base, key, yes], sort);
        let hit = app(&mut terms, "select", &[stored, hit_index], Sort::Bool);
        let miss = app(&mut terms, "select", &[stored, miss_index], Sort::Bool);
        let miss_false = terms.mk_not_raw(miss);
        let mut model = Values::default();
        model.leaves.insert(key, ModelValue::Bool(assigned_key));
        model.reads.extend([
            (hit, ModelValue::Bool(false)),
            (miss, ModelValue::Bool(false)),
        ]);
        for roots in [[hit, miss_false], [miss_false, hit]] {
            accepts_both_gates(&terms, &model, &roots);
        }
        assert!(!model.read_calls.borrow().contains(&hit));
        assert!(model.read_calls.borrow().contains(&miss));
    }
}

#[test]
fn reconstruction_can_resolve_a_key_from_a_congruent_base_observation() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(BigInt::from(0));
    let seven = terms.mk_int(BigInt::from(7));
    let equivalent_zero = app(&mut terms, "+", &[zero, zero], Sort::Int);
    let key = app(&mut terms, "f", &[zero], Sort::Int);
    let observed = app(&mut terms, "f", &[equivalent_zero], Sort::Int);
    assert_ne!(key, observed);
    let sort = Sort::array(Sort::Int, Sort::Int);
    let base = app(&mut terms, "const-array", &[observed], sort.clone());
    let stored = app(&mut terms, "store", &[base, key, seven], sort);
    let read = app(&mut terms, "select", &[stored, zero], Sort::Int);
    let claim = terms.mk_eq(read, seven);
    let mut model = Values::default();
    model.functions.insert(observed, integer(0));
    model.reads.insert(read, integer(2));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.select_over_store_chain(stored, &integer(0), 0),
        Ok(SelectFold::Reconstruct { array }) if array == stored
    ));
    assert!(evaluator.uf_graph.borrow().is_empty());
    assert!(
        matches!(evaluator.eval(read, 0), Ok(ModelValue::Int(value)) if value == BigInt::from(7))
    );
    assert_eq!(
        model.function_calls.borrow().as_slice(),
        &[key, key, observed]
    );
    assert!(model.read_calls.borrow().is_empty());
    accepts_both_gates(&terms, &model, &[claim]);
}

#[test]
fn reconstruction_preserves_hard_errors_and_a_fresh_key_assignment_recovers() {
    let fixture = ConstantStore::new();
    let mut model = Values::default();
    model.reads.insert(fixture.read, integer(2));
    let evaluator = Evaluator::new(&fixture.terms, &model);
    assert!(matches!(
        evaluator.eval(fixture.read, MAX_EVAL_DEPTH - 2),
        Err(EvalError::Resource {
            kind: EvalResource::Depth,
            ..
        })
    ));
    assert!(!evaluator.memo.borrow().contains_key(&fixture.read));
    assert!(matches!(
        evaluator.eval(fixture.read, 0),
        Err(EvalError::Refused(_))
    ));
    assert!(model.read_calls.borrow().is_empty());
    drop(evaluator);
    model.leaves.insert(fixture.key, ModelValue::Bool(true));
    let evaluator = Evaluator::new(&fixture.terms, &model);
    assert!(
        matches!(evaluator.eval(fixture.read, 0), Ok(ModelValue::Int(value)) if value == BigInt::from(0))
    );
    assert!(model.read_calls.borrow().is_empty());

    // A malformed whole-array interpretation remains its original hard error,
    // not the new missing-key refusal and never a committed read value.
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Bool, Sort::Int);
    let base = terms.mk_var("bad_base", sort.clone());
    let key = terms.mk_var("missing_key", Sort::Bool);
    let no = terms.mk_bool(false);
    let zero = terms.mk_int(BigInt::from(0));
    let stored = app(&mut terms, "store", &[base, key, zero], sort);
    let read = app(&mut terms, "select", &[stored, no], Sort::Int);
    let mut model = Values::default();
    model.leaves.insert(base, ModelValue::Bool(false));
    model.reads.insert(read, integer(2));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.select_over_store_chain(stored, &ModelValue::Bool(false), 0),
        Ok(SelectFold::Reconstruct { array }) if array == stored
    ));
    let expected = evaluator
        .eval_array_value(stored, 1)
        .expect_err("malformed base");
    assert!(matches!(expected, EvalError::Refused(_)));
    assert_eq!(
        evaluator.eval(read, 0).expect_err("same malformed base"),
        expected
    );
    assert!(model.read_calls.borrow().is_empty());
}

#[test]
fn an_array_valued_unresolved_store_cannot_recover_through_an_outer_read_pin() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));
    let no = terms.mk_bool(false);
    let key = terms.mk_var("missing_key", Sort::Bool);
    let inner_sort = Sort::array(Sort::Bool, Sort::Int);
    let outer_sort = Sort::array(Sort::Bool, inner_sort.clone());
    let inner = app(&mut terms, "const-array", &[zero], inner_sort.clone());
    let base = app(&mut terms, "const-array", &[inner], outer_sort.clone());
    let stored = app(&mut terms, "store", &[base, key, inner], outer_sort);
    let selected = app(&mut terms, "select", &[stored, no], inner_sort);
    let read = app(&mut terms, "select", &[selected, no], Sort::Int);
    let false_claim = terms.mk_eq(read, two);
    let mut model = Values::default();
    model.reads.insert(read, integer(2));
    refuses_both_gates(&terms, &model, &[false_claim]);
    assert!(model.read_calls.borrow().is_empty());
}
