// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
enum Conditional {
    Raw,
    Ite,
    If,
}

const CONDITIONALS: [Conditional; 3] = [Conditional::Raw, Conditional::Ite, Conditional::If];

#[derive(Default)]
struct Model {
    leaves: HashMap<TermId, ModelValue>,
    reads: HashMap<TermId, ModelValue>,
    projections: HashMap<TermId, Result<Option<usize>, crate::ProjectionLookupError>>,
    leaf_calls: RefCell<Vec<TermId>>,
    read_calls: RefCell<Vec<TermId>>,
}

impl ModelView for Model {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.leaf_calls.borrow_mut().push(term);
        self.leaves.get(&term).cloned()
    }

    fn array_select_value(&self, term: TermId) -> Option<ModelValue> {
        self.read_calls.borrow_mut().push(term);
        self.reads.get(&term).cloned()
    }

    fn projection_argument(
        &self,
        term: TermId,
    ) -> Result<Option<usize>, crate::ProjectionLookupError> {
        self.projections.get(&term).cloned().unwrap_or(Ok(None))
    }
}

fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

fn array_sort() -> Sort {
    Sort::array(Sort::bitvec(64), Sort::Int)
}

fn integer(value: i64) -> ModelValue {
    ModelValue::Int(BigInt::from(value))
}

fn constant(terms: &mut TermStore, value: i64) -> TermId {
    let value = terms.mk_int(BigInt::from(value));
    app(terms, "const-array", &[value], array_sort())
}

fn conditional(
    terms: &mut TermStore,
    kind: Conditional,
    condition: TermId,
    positive: TermId,
    negative: TermId,
) -> TermId {
    match kind {
        Conditional::Raw => terms.mk_ite_raw(condition, positive, negative),
        Conditional::Ite | Conditional::If => app(
            terms,
            if matches!(kind, Conditional::Ite) {
                "ite"
            } else {
                "if"
            },
            &[condition, positive, negative],
            array_sort(),
        ),
    }
}

fn read_zero(terms: &mut TermStore, array: TermId) -> TermId {
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let Sort::Array(sort) = terms.sort(array) else {
        panic!("array fixture")
    };
    let element_sort = sort.element_sort.clone();
    app(terms, "select", &[array, zero], element_sort)
}

fn equals(terms: &mut TermStore, read: TermId, value: i64) -> TermId {
    let value = terms.mk_int(BigInt::from(value));
    app(terms, "=", &[read, value], Sort::Bool)
}

fn assert_refused_by_both_gates(terms: &TermStore, model: &Model, roots: &[TermId]) {
    for verdict in [
        crate::confirm_model(terms, model, roots),
        crate::confirm_completed_model(terms, model, roots),
    ] {
        assert!(
            !matches!(verdict, crate::GateVerdict::ConfirmedSat),
            "{verdict:?}"
        );
    }
}

fn assert_confirmed_by_both_gates(terms: &TermStore, model: &Model, roots: &[TermId]) {
    for verdict in [
        crate::confirm_model(terms, model, roots),
        crate::confirm_completed_model(terms, model, roots),
    ] {
        assert!(
            matches!(verdict, crate::GateVerdict::ConfirmedSat),
            "{verdict:?}"
        );
    }
}

fn assert_integer(result: EvalResult<ModelValue>, expected: i64) {
    assert!(matches!(result, Ok(ModelValue::Int(value)) if value == BigInt::from(expected)));
}

#[test]
fn unavailable_conditional_test_cannot_authorize_an_impossible_read() {
    for kind in CONDITIONALS {
        let mut terms = TermStore::new();
        let b = terms.mk_var("b", Sort::Bool);
        let zero = constant(&mut terms, 0);
        let one = constant(&mut terms, 1);
        let array = conditional(&mut terms, kind, b, zero, one);
        let read = read_zero(&mut terms, array);
        let assertion = equals(&mut terms, read, 2);
        let mut model = Model::default();
        model.reads.insert(read, integer(2));
        assert_refused_by_both_gates(&terms, &model, &[assertion]);
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(
            evaluator.eval(array, 0),
            Err(EvalError::Refused(_))
        ));
        assert!(matches!(
            evaluator.eval(read, 0),
            Err(EvalError::Refused(_))
        ));
        assert!(!evaluator.memo.borrow().contains_key(&read));
        assert!(evaluator.select_graph.borrow().is_empty());
        assert!(model.read_calls.borrow().is_empty());
    }
}

#[test]
fn known_conditions_choose_the_exact_concrete_branch_not_the_read_pin() {
    for kind in CONDITIONALS {
        for choice in [false, true] {
            let mut terms = TermStore::new();
            let b = terms.mk_var("b", Sort::Bool);
            let zero = constant(&mut terms, 0);
            let one = constant(&mut terms, 1);
            let array = conditional(&mut terms, kind, b, zero, one);
            let read = read_zero(&mut terms, array);
            let expected = if choice { 0 } else { 1 };
            let assertion = equals(&mut terms, read, expected);
            let wrong = equals(&mut terms, read, 2);
            let mut model = Model::default();
            model.leaves.insert(b, ModelValue::Bool(choice));
            model.reads.insert(read, integer(2));
            assert_confirmed_by_both_gates(&terms, &model, &[assertion]);
            assert_refused_by_both_gates(&terms, &model, &[wrong]);
            assert!(model.read_calls.borrow().is_empty());
        }
    }
}

#[test]
fn selected_partial_array_and_original_array_share_one_semantic_read_key() {
    for kind in CONDITIONALS {
        let mut terms = TermStore::new();
        let base = terms.mk_var("base", array_sort());
        let yes = terms.mk_bool(true);
        let unused = terms.mk_var("unused", array_sort());
        let array = conditional(&mut terms, kind, yes, base, unused);
        let base_read = read_zero(&mut terms, base);
        let original_read = read_zero(&mut terms, array);
        let base_zero = equals(&mut terms, base_read, 0);
        let original_one = equals(&mut terms, original_read, 1);
        let original_zero = equals(&mut terms, original_read, 0);
        let mut model = Model::default();
        model
            .reads
            .extend([(base_read, integer(0)), (original_read, integer(1))]);
        for roots in [[base_zero, original_one], [original_one, base_zero]] {
            assert_refused_by_both_gates(&terms, &model, &roots);
        }
        model.reads.insert(original_read, integer(0));
        for roots in [[base_zero, original_zero], [original_zero, base_zero]] {
            assert_confirmed_by_both_gates(&terms, &model, &roots);
        }
        model.read_calls.borrow_mut().clear();
        let evaluator = Evaluator::new(&terms, &model);
        assert_integer(evaluator.eval(original_read, 0), 0);
        assert_integer(evaluator.eval(base_read, 0), 0);
        assert_eq!(model.read_calls.borrow().as_slice(), &[original_read]);
        assert_eq!(evaluator.select_graph.borrow()[0].0, base);
        assert!(!model.leaf_calls.borrow().contains(&unused));
    }
}

#[test]
fn partial_variables_and_nullary_ufs_keep_original_read_pins_through_store_misses() {
    for kind in CONDITIONALS {
        let mut terms = TermStore::new();
        let variable = terms.mk_var("base", array_sort());
        let function = app(&mut terms, "array_function", &[], array_sort());
        let yes = terms.mk_bool(true);
        let irrelevant = terms.mk_var("irrelevant", Sort::Int);
        let one = terms.mk_bitvec(BigInt::from(1), 64);
        for base in [variable, function] {
            let stored = app(&mut terms, "store", &[base, one, irrelevant], array_sort());
            let selected = conditional(&mut terms, kind, yes, stored, base);
            let outer = app(
                &mut terms,
                "store",
                &[selected, one, irrelevant],
                array_sort(),
            );
            let read = read_zero(&mut terms, outer);
            let assertion = equals(&mut terms, read, 7);
            let mut model = Model::default();
            model.reads.insert(read, integer(7));
            assert_confirmed_by_both_gates(&terms, &model, &[assertion]);
            assert_eq!(model.read_calls.borrow().as_slice(), &[read, read]);
            assert!(!model.leaf_calls.borrow().contains(&irrelevant));
        }
    }
}

#[test]
fn condition_resource_and_malformed_value_errors_remain_hard_with_fresh_retry() {
    for kind in CONDITIONALS {
        let mut terms = TermStore::new();
        let b = terms.mk_var("b", Sort::Bool);
        let zero = constant(&mut terms, 0);
        let one = constant(&mut terms, 1);
        let array = conditional(&mut terms, kind, b, zero, one);
        let read = read_zero(&mut terms, array);
        let mut model = Model::default();
        model.leaves.insert(b, ModelValue::Bool(true));
        model.reads.insert(read, integer(2));
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(
            evaluator.eval(read, MAX_EVAL_DEPTH - 1),
            Err(EvalError::Resource {
                kind: EvalResource::Depth,
                ..
            })
        ));
        assert!(evaluator.select_graph.borrow().is_empty());
        assert!(!evaluator.memo.borrow().contains_key(&read));
        assert_integer(evaluator.eval(read, 0), 0);
        drop(evaluator);
        model.leaves.insert(b, integer(0));
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(
            evaluator.eval(read, 0),
            Err(EvalError::Refused(_))
        ));
        assert!(model.read_calls.borrow().is_empty());
    }
}

#[test]
fn both_branch_sorts_condition_sort_and_named_arity_are_authenticated() {
    let mut terms = TermStore::new();
    let yes = terms.mk_bool(true);
    let bad_condition = terms.mk_int(BigInt::from(1));
    let zero = constant(&mut terms, 0);
    let one = constant(&mut terms, 1);
    for name in ["ite", "if"] {
        let invalid = [
            app(&mut terms, name, &[bad_condition, zero, one], array_sort()),
            app(&mut terms, name, &[yes, zero, bad_condition], array_sort()),
            app(&mut terms, name, &[yes, bad_condition, one], array_sort()),
            app(
                &mut terms,
                name,
                &[yes, zero, one],
                Sort::array(Sort::bitvec(64), Sort::Bool),
            ),
            app(&mut terms, name, &[], array_sort()),
            app(&mut terms, name, &[yes, zero], array_sort()),
            app(&mut terms, name, &[yes, zero, one, zero], array_sort()),
        ];
        for array in invalid {
            let read = read_zero(&mut terms, array);
            let mut model = Model::default();
            model.reads.insert(read, integer(2));
            let evaluator = Evaluator::new(&terms, &model);
            assert!(matches!(
                evaluator.eval(array, 0),
                Err(EvalError::Refused(_))
            ));
            assert!(matches!(
                evaluator.eval(read, 0),
                Err(EvalError::Refused(_))
            ));
            assert!(model.read_calls.borrow().is_empty());
        }
    }
}

#[test]
fn checked_projection_precedes_named_conditional_dispatch_and_rejects_bad_claims() {
    for kind in [Conditional::Ite, Conditional::If] {
        let mut terms = TermStore::new();
        let b = terms.mk_var("b", Sort::Bool);
        let zero = constant(&mut terms, 0);
        let one = constant(&mut terms, 1);
        let array = conditional(&mut terms, kind, b, zero, one);
        let read = read_zero(&mut terms, array);
        let assertion = equals(&mut terms, read, 1);
        let mut model = Model::default();
        model.reads.insert(read, integer(2));
        model.projections.insert(array, Ok(Some(2)));
        assert_confirmed_by_both_gates(&terms, &model, &[assertion]);
        assert!(!model.leaf_calls.borrow().contains(&b));
        for projection in [
            Ok(Some(0)),
            Ok(Some(99)),
            Err(crate::ProjectionLookupError::inconsistent_model(
                "invalid projection",
            )),
        ] {
            model.projections.insert(array, projection);
            let evaluator = Evaluator::new(&terms, &model);
            assert!(matches!(
                evaluator.eval(read, 0),
                Err(EvalError::Refused(_))
            ));
        }
        assert!(model.read_calls.borrow().is_empty());
    }
}

#[test]
fn semantic_branch_selection_keeps_original_lexical_binding_guards() {
    for kind in CONDITIONALS {
        let mut terms = TermStore::new();
        let b = terms.mk_var("bound", Sort::Bool);
        let base = terms.mk_var("base", array_sort());
        let array = conditional(&mut terms, kind, b, base, base);
        let read = read_zero(&mut terms, array);
        let base_read = read_zero(&mut terms, base);
        let mut model = Model::default();
        model
            .reads
            .extend([(base_read, integer(0)), (read, integer(2))]);
        let evaluator = Evaluator::new(&terms, &model);
        assert_integer(evaluator.eval(base_read, 0), 0);
        for value in [false, true] {
            assert!(matches!(
                evaluator.eval_with_binding(b, ModelValue::Bool(value), read, 0),
                Err(EvalError::Refused(_))
            ));
        }
        assert_eq!(model.read_calls.borrow().as_slice(), &[base_read]);
        assert_eq!(evaluator.select_graph.borrow().len(), 1);
        assert!(evaluator.local_bindings.borrow().is_empty());
    }
}
