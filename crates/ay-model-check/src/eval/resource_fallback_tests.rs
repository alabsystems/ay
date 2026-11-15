// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort};

#[derive(Default)]
struct Model {
    leaves: HashMap<TermId, ModelValue>,
    applications: HashMap<TermId, ModelValue>,
    reads: HashMap<TermId, ModelValue>,
    projections: HashSet<TermId>,
    leaf_calls: RefCell<Vec<TermId>>,
    application_calls: RefCell<Vec<TermId>>,
    read_calls: RefCell<Vec<TermId>>,
}

impl ModelView for Model {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        let mut calls = self.leaf_calls.borrow_mut();
        assert!(calls.len() < 512, "repeated failed subtree reconstruction");
        calls.push(term);
        self.leaves.get(&term).cloned()
    }

    fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
        self.application_calls.borrow_mut().push(term);
        self.applications.get(&term).cloned()
    }

    fn array_select_value(&self, term: TermId) -> Option<ModelValue> {
        self.read_calls.borrow_mut().push(term);
        self.reads.get(&term).cloned()
    }

    fn projection_argument(
        &self,
        term: TermId,
    ) -> Result<Option<usize>, crate::ProjectionLookupError> {
        Ok(self.projections.contains(&term).then_some(0))
    }
}

fn array_sort() -> Sort {
    Sort::array(Sort::bitvec(64), Sort::Bool)
}

fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

fn array_value(value: bool) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Bool(value),
        store: Vec::new(),
    }))
}

fn read_zero(terms: &mut TermStore, array: TermId) -> TermId {
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    app(terms, "select", &[array, zero], Sort::Bool)
}

fn interpreted_read(terms: &mut TermStore) -> TermId {
    let yes = terms.mk_bool(true);
    let no = terms.mk_bool(false);
    let positive = app(terms, "const-array", &[yes], array_sort());
    let negative = app(terms, "const-array", &[no], array_sort());
    // The raw builder is essential: a folded constant condition would remove
    // the interpreted evaluation whose resource failure this test exercises.
    let array = terms.mk_ite_raw(yes, positive, negative);
    read_zero(terms, array)
}

fn assert_bool(result: EvalResult<ModelValue>, expected: bool) {
    assert!(matches!(result, Ok(ModelValue::Bool(value)) if value == expected));
}

fn assert_depth_failure(result: EvalResult<ModelValue>) {
    assert!(matches!(
        result,
        Err(EvalError::Resource {
            kind: EvalResource::Depth,
            ..
        })
    ));
}

fn assert_no_authority(evaluator: &Evaluator<'_>, model: &Model) {
    assert!(evaluator.memo.borrow().is_empty());
    assert!(evaluator.select_graph.borrow().is_empty());
    assert!(evaluator.uf_graph.borrow().is_empty());
    assert!(model.read_calls.borrow().is_empty());
}

#[test]
fn interpreted_array_depth_failure_never_adopts_a_read_pin_or_poisons_retry() {
    let mut terms = TermStore::new();
    let read = interpreted_read(&mut terms);
    let mut model = Model::default();
    model.reads.insert(read, ModelValue::Bool(false));
    let evaluator = Evaluator::new(&terms, &model);
    assert_depth_failure(evaluator.eval(read, MAX_EVAL_DEPTH - 1));
    assert_no_authority(&evaluator, &model);
    assert!(model.leaf_calls.borrow().is_empty());
    assert!(model.application_calls.borrow().is_empty());
    assert_bool(evaluator.eval(read, 0), true);
    assert_bool(Evaluator::new(&terms, &model).eval(read, 0), true);
    assert!(model.read_calls.borrow().is_empty());
}

#[test]
fn interpreted_array_nearby_depth_boundaries_preserve_real_success() {
    let mut terms = TermStore::new();
    let read = interpreted_read(&mut terms);
    let mut model = Model::default();
    model.reads.insert(read, ModelValue::Bool(false));
    // At MAX-3 the selected const-array default is evaluated exactly at MAX.
    assert_bool(
        Evaluator::new(&terms, &model).eval(read, MAX_EVAL_DEPTH - 3),
        true,
    );
    for depth in [MAX_EVAL_DEPTH - 2, MAX_EVAL_DEPTH - 1] {
        let evaluator = Evaluator::new(&terms, &model);
        assert_depth_failure(evaluator.eval(read, depth));
        assert_no_authority(&evaluator, &model);
    }
}

#[test]
fn genuinely_missing_array_variables_and_nullary_ufs_keep_their_read_pins() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("missing_array", array_sort());
    let nullary = app(&mut terms, "missing_array_function", &[], array_sort());
    let variable_read = read_zero(&mut terms, variable);
    let nullary_read = read_zero(&mut terms, nullary);
    for (array, read) in [(variable, variable_read), (nullary, nullary_read)] {
        let mut model = Model::default();
        model.reads.insert(read, ModelValue::Bool(false));
        let evaluator = Evaluator::new(&terms, &model);
        // Unlike the interpreted ITE, reaching this missing leaf requires no
        // additional child evaluation beyond MAX, so the fallback is genuine.
        assert_bool(evaluator.eval(read, MAX_EVAL_DEPTH - 1), false);
        assert_bool(evaluator.eval(read, 0), false);
        assert_eq!(model.read_calls.borrow().as_slice(), &[read]);
        assert_eq!(evaluator.select_graph.borrow().len(), 1);
        assert_eq!(evaluator.select_graph.borrow()[0].0, array);
        if array == variable {
            assert_eq!(model.leaf_calls.borrow().as_slice(), &[variable]);
            assert!(model.application_calls.borrow().is_empty());
        } else {
            assert!(model.leaf_calls.borrow().is_empty());
            assert_eq!(model.application_calls.borrow().as_slice(), &[nullary]);
        }
    }
}

#[test]
fn an_uninterpreted_array_head_does_not_authorize_resource_failed_arguments() {
    let mut terms = TermStore::new();
    let argument = terms.mk_bool(true);
    let array = app(&mut terms, "array_function", &[argument], array_sort());
    let read = read_zero(&mut terms, array);
    let mut model = Model::default();
    model.applications.insert(array, array_value(true));
    model.reads.insert(read, ModelValue::Bool(false));
    let evaluator = Evaluator::new(&terms, &model);
    assert_depth_failure(evaluator.eval(read, MAX_EVAL_DEPTH - 1));
    assert_no_authority(&evaluator, &model);
    assert!(model.application_calls.borrow().is_empty());
    assert_bool(evaluator.eval(read, 0), true);
    assert_eq!(model.application_calls.borrow().as_slice(), &[array]);
    assert!(model.read_calls.borrow().is_empty());
}

#[test]
fn selector_fallback_cannot_hide_a_constructor_depth_failure_from_a_read() {
    let mut terms = TermStore::new();
    let record_sort = Sort::Datatype(DatatypeSort::new(
        "Box",
        vec![DatatypeConstructor::new(
            "mkBox",
            vec![DatatypeField::new("data", array_sort())],
        )],
    ));
    let yes = terms.mk_bool(true);
    let array = app(&mut terms, "const-array", &[yes], array_sort());
    let record = app(&mut terms, "mkBox", &[array], record_sort);
    let selected = app(&mut terms, "data", &[record], array_sort());
    let read = read_zero(&mut terms, selected);
    let mut model = Model::default();
    model.applications.insert(selected, array_value(false));
    model.reads.insert(read, ModelValue::Bool(false));
    for depth in [MAX_EVAL_DEPTH - 2, MAX_EVAL_DEPTH - 1] {
        let evaluator = Evaluator::new(&terms, &model);
        // The first cutoff enters the constructor and exhausts on its field;
        // the second exhausts before entering the constructor. Neither may be
        // reclassified as an ordinary datatype/selector model lookup miss.
        assert_depth_failure(evaluator.eval(read, depth));
        assert_no_authority(&evaluator, &model);
        assert!(model.application_calls.borrow().is_empty());
        assert!(model.leaf_calls.borrow().is_empty());
        assert_bool(evaluator.eval(read, 0), true);
    }
    assert_bool(Evaluator::new(&terms, &model).eval(read, 0), true);
    assert!(model.application_calls.borrow().is_empty());
    assert!(model.read_calls.borrow().is_empty());
}

#[test]
fn malformed_whole_array_values_are_refusals_not_missing_read_evidence() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("wrong_array_value", array_sort());
    let function = app(&mut terms, "wrong_array_function", &[], array_sort());
    let variable_read = read_zero(&mut terms, variable);
    let function_read = read_zero(&mut terms, function);
    for (array, read) in [(variable, variable_read), (function, function_read)] {
        let mut model = Model::default();
        if array == variable {
            model.leaves.insert(array, ModelValue::Bool(true));
        } else {
            model.applications.insert(array, ModelValue::Bool(true));
        }
        model.reads.insert(read, ModelValue::Bool(true));
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(
            evaluator.eval(read, 0),
            Err(EvalError::Refused(_))
        ));
        assert!(model.read_calls.borrow().is_empty());
        assert!(evaluator.select_graph.borrow().is_empty());
        assert!(!evaluator.memo.borrow().contains_key(&read));
    }
}

#[test]
fn public_evaluate_reaches_the_cutoff_through_iterative_exact_projections() {
    let mut terms = TermStore::new();
    let read = interpreted_read(&mut terms);
    let shallow_assertion = terms.mk_not_raw(read);
    let ignored = terms.mk_bool(true);
    let mut assertion = shallow_assertion;
    let mut model = Model::default();
    model.reads.insert(read, ModelValue::Bool(false));
    // Exact symbolic projections are an existing ModelView contract. Their
    // evaluator loop advances logical depth without adding a Rust stack frame
    // per wrapper; this exercises the public API without a deep native stack.
    for _ in 0..MAX_EVAL_DEPTH - 2 {
        assertion = app(&mut terms, "first", &[assertion, ignored], Sort::Bool);
        model.projections.insert(assertion);
    }
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.evaluate(assertion),
        EvalOutcome::Unevaluable(_)
    ));
    assert_no_authority(&evaluator, &model);
    assert!(evaluator.local_bindings.borrow().is_empty());
    assert_eq!(evaluator.active_eval_calls.get(), 0);
    assert_bool(evaluator.eval(shallow_assertion, 0), false);
    assert!(model.read_calls.borrow().is_empty());
}

#[test]
fn known_selector_absence_does_not_reenter_ordinary_uf_argument_evaluation() {
    for depth in [1, 4, 66] {
        let mut terms = TermStore::new();
        let mut sorts = vec![Sort::bitvec(64)];
        for level in 0..depth {
            sorts.push(Sort::Datatype(DatatypeSort::new(
                format!("D{level}"),
                vec![DatatypeConstructor::new(
                    format!("mk{level}"),
                    vec![DatatypeField::new(
                        format!("field{level}"),
                        sorts[level].clone(),
                    )],
                )],
            )));
        }
        let base = terms.mk_var("deep", Sort::array(Sort::bitvec(64), sorts[depth].clone()));
        let zero = terms.mk_bitvec(BigInt::from(0), 64);
        let mut selected = app(&mut terms, "select", &[base, zero], sorts[depth].clone());
        for level in (0..depth).rev() {
            selected = app(
                &mut terms,
                &format!("field{level}"),
                &[selected],
                sorts[level].clone(),
            );
        }
        let model = Model::default();
        let evaluator = Evaluator::new(&terms, &model);
        for attempt in 1..=2 {
            assert!(matches!(
                evaluator.eval(selected, 0),
                Err(EvalError::ModelUnavailable(_))
            ));
            // Each known selector checks its receiver's optional representative
            // and its own pin once. It must not then masquerade as an ordinary
            // UF and recursively evaluate that same failed receiver again.
            assert_eq!(model.leaf_calls.borrow().len(), attempt * (depth + 1));
            assert_eq!(model.read_calls.borrow().len(), attempt * (depth + 1));
            assert_eq!(model.application_calls.borrow().len(), attempt * 2 * depth);
            assert_eq!(
                model
                    .leaf_calls
                    .borrow()
                    .iter()
                    .filter(|&&term| term == base)
                    .count(),
                attempt
            );
            assert!(evaluator.memo.borrow().is_empty());
            assert!(evaluator.select_graph.borrow().is_empty());
            assert!(evaluator.uf_graph.borrow().is_empty());
        }
    }
}
