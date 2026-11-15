// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Default)]
struct Model {
    applications: HashMap<TermId, ModelValue>,
    projections: HashMap<TermId, Result<Option<usize>, crate::ProjectionLookupError>>,
    calls: RefCell<Vec<TermId>>,
}

impl ModelView for Model {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }

    fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
        self.calls.borrow_mut().push(term);
        self.applications.get(&term).cloned()
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

fn integer(value: i64) -> ModelValue {
    ModelValue::Int(BigInt::from(value))
}

fn inner_sort() -> Sort {
    Sort::array(Sort::Bool, Sort::Int)
}

fn constant_value(value: i64) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: integer(value),
        store: Vec::new(),
    }))
}

fn constant(terms: &mut TermStore, value: i64) -> TermId {
    let value = terms.mk_int(BigInt::from(value));
    app(terms, "const-array", &[value], inner_sort())
}

fn dependent(terms: &mut TermStore) -> TermId {
    let bound = terms.mk_var("bound", Sort::Bool);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let body = terms.mk_ite_raw(bound, one, zero);
    app(terms, "lambda-array", &[bound, body], inner_sort())
}

fn alias(terms: &mut TermStore, array: TermId) -> TermId {
    let yes = terms.mk_bool(true);
    terms.mk_ite_raw(yes, array, array)
}

fn default(terms: &mut TermStore, array: TermId, result: Sort) -> TermId {
    app(terms, "default", &[array], result)
}

fn assert_refused(evaluator: &Evaluator<'_>, model: &Model, term: TermId) {
    assert!(matches!(
        evaluator.eval(term, 0),
        Err(EvalError::Refused(_))
    ));
    assert!(model.calls.borrow().is_empty());
    assert!(evaluator.uf_graph.borrow().is_empty());
    assert!(!evaluator.memo.borrow().contains_key(&term));
}

#[test]
fn a_lambda_argument_cannot_authorize_an_unrelated_conditional_array_default() {
    let mut terms = TermStore::new();
    let lambda = dependent(&mut terms);
    let condition = app(&mut terms, "choose", &[lambda], Sort::Bool);
    let zero = constant(&mut terms, 0);
    let one = constant(&mut terms, 1);
    let array = terms.mk_ite_raw(condition, zero, one);
    let result = default(&mut terms, array, Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let assertion = app(&mut terms, "=", &[result, two], Sort::Bool);
    let mut model = Model::default();
    model.applications.insert(condition, ModelValue::Bool(true));
    model.applications.insert(result, integer(2));
    let evaluator = Evaluator::new(&terms, &model);
    // For either possible choice, the array is constant 0 or constant 1.
    // Failure to materialize choose's lambda ARGUMENT cannot justify 2.
    assert_refused(&evaluator, &model, result);
    assert!(!matches!(
        crate::confirm_model(&terms, &model, &[assertion]),
        crate::GateVerdict::ConfirmedSat
    ));
    assert!(model.calls.borrow().is_empty());
}

#[test]
fn a_nonfinite_store_write_does_not_change_the_known_outer_default() {
    let mut terms = TermStore::new();
    let lambda = dependent(&mut terms);
    let inner_zero = constant(&mut terms, 0);
    let outer_sort = Sort::array(Sort::Int, inner_sort());
    let base = app(&mut terms, "const-array", &[inner_zero], outer_sort.clone());
    let key = terms.mk_int(BigInt::from(5));
    let stored = app(&mut terms, "store", &[base, key, lambda], outer_sort);
    let wrapped = alias(&mut terms, stored);
    let result = default(&mut terms, wrapped, inner_sort());
    let direct = default(&mut terms, stored, inner_sort());
    let mut model = Model::default();
    model.applications.insert(result, constant_value(2));
    let evaluator = Evaluator::new(&terms, &model);
    assert_refused(&evaluator, &model, result);
    // Int-indexed store default transport is an existing exact path: the
    // direct default is inner_zero regardless of the unrepresentable write.
    let actual = evaluator.eval(direct, 0).expect("known base default");
    assert!(matches!(value_eq(&actual, &constant_value(0)), Ok(true)));
    assert!(model.calls.borrow().is_empty());
}

#[test]
fn a_const_array_element_marker_does_not_rebind_that_element_to_an_arbitrary_array() {
    let mut terms = TermStore::new();
    let lambda = dependent(&mut terms);
    let outer = app(
        &mut terms,
        "const-array",
        &[lambda],
        Sort::array(Sort::Int, inner_sort()),
    );
    let wrapped = alias(&mut terms, outer);
    let element = default(&mut terms, wrapped, inner_sort());
    let no = terms.mk_bool(false);
    let read = app(&mut terms, "select", &[element, no], Sort::Int);
    let direct = app(&mut terms, "select", &[lambda, no], Sort::Int);
    let mut model = Model::default();
    model.applications.insert(element, constant_value(2));
    let evaluator = Evaluator::new(&terms, &model);
    // The actual element is the original lambda, whose false-index read is 0.
    // A marker from that element does not make the outer array a free lambda.
    assert_refused(&evaluator, &model, read);
    assert!(matches!(evaluator.eval(direct, 0),
        Ok(ModelValue::Int(value)) if value == BigInt::from(0)));
    assert!(model.calls.borrow().is_empty());
}

#[test]
fn a_select_receiver_marker_is_not_a_marker_for_the_selected_array() {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("row", Sort::Bool);
    let zero = constant(&mut terms, 0);
    let one = constant(&mut terms, 1);
    let body = terms.mk_ite_raw(bound, one, zero);
    let lambda = app(
        &mut terms,
        "lambda-array",
        &[bound, body],
        Sort::array(Sort::Bool, inner_sort()),
    );
    let wrapped = alias(&mut terms, lambda);
    let no = terms.mk_bool(false);
    let selected = app(&mut terms, "select", &[wrapped, no], inner_sort());
    let result = default(&mut terms, selected, Sort::Int);
    let direct_selected = app(&mut terms, "select", &[lambda, no], inner_sort());
    let direct = default(&mut terms, direct_selected, Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let impossible = app(&mut terms, "=", &[result, two], Sort::Bool);
    let mut model = Model::default();
    model.applications.insert(result, integer(2));
    let evaluator = Evaluator::new(&terms, &model);
    // Known-ITE folding now permits exact beta-reduction to const-array 0;
    // the receiver's marker still cannot authorize the impossible default 2.
    assert!(matches!(evaluator.eval(result, 0),
        Ok(ModelValue::Int(value)) if value == BigInt::from(0)));
    assert!(matches!(evaluator.eval(direct, 0),
        Ok(ModelValue::Int(value)) if value == BigInt::from(0)));
    for verdict in [
        crate::confirm_model(&terms, &model, &[impossible]),
        crate::confirm_completed_model(&terms, &model, &[impossible]),
    ] {
        assert!(matches!(verdict, crate::GateVerdict::ModelViolates { .. }));
    }
    assert!(model.calls.borrow().is_empty());
}

#[test]
fn direct_and_exact_alias_lambda_defaults_keep_the_existing_opaque_choice() {
    let mut terms = TermStore::new();
    let lambda = dependent(&mut terms);
    let wrapped = alias(&mut terms, lambda);
    let projected = app(&mut terms, "array_identity", &[lambda], inner_sort());
    let direct = default(&mut terms, lambda, Sort::Int);
    let alias_default = default(&mut terms, wrapped, Sort::Int);
    let projection_default = default(&mut terms, projected, Sort::Int);
    let mut model = Model::default();
    model.projections.insert(projected, Ok(Some(0)));
    for term in [direct, alias_default, projection_default] {
        model.applications.insert(term, integer(2));
    }
    let evaluator = Evaluator::new(&terms, &model);
    for term in [direct, alias_default, projection_default] {
        assert!(matches!(evaluator.eval(term, 0),
            Ok(ModelValue::Int(value)) if value == BigInt::from(2)));
    }
    assert_eq!(
        model.calls.borrow().as_slice(),
        &[direct, alias_default, projection_default]
    );
    // A default choice still requires a real pin; this does not claim a
    // finite representation for the lambda itself.
    let missing = Model::default();
    assert!(matches!(
        Evaluator::new(&terms, &missing).eval(direct, 0),
        Err(EvalError::ModelUnavailable(_))
    ));
}

#[test]
fn malformed_lambda_metadata_and_alias_depth_cannot_be_hidden_by_default_pins() {
    for case in 0..4 {
        let mut terms = TermStore::new();
        let no = terms.mk_bool(false);
        let yes = terms.mk_bool(true);
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let bound = match case {
            0 => no,
            1 => terms.mk_var("wrong_index", Sort::Int),
            _ => terms.mk_var("bound", Sort::Bool),
        };
        let body = match case {
            1 => app(&mut terms, "+", &[bound, one], Sort::Int),
            2 => terms.mk_ite_raw(bound, yes, no),
            _ => terms.mk_ite_raw(bound, one, zero),
        };
        let sort = if case == 3 { Sort::Int } else { inner_sort() };
        let lambda = app(&mut terms, "lambda-array", &[bound, body], sort);
        let result = default(&mut terms, lambda, Sort::Int);
        let mut model = Model::default();
        model.applications.insert(result, integer(2));
        assert_refused(&Evaluator::new(&terms, &model), &model, result);
    }
    let mut terms = TermStore::new();
    let lambda = dependent(&mut terms);
    let wrapped = alias(&mut terms, lambda);
    let result = default(&mut terms, wrapped, Sort::Int);
    let mut model = Model::default();
    model.applications.insert(result, integer(2));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.eval(result, MAX_EVAL_DEPTH - 1),
        Err(EvalError::Resource {
            kind: EvalResource::Depth,
            ..
        })
    ));
    assert!(model.calls.borrow().is_empty());
    assert!(!evaluator.memo.borrow().contains_key(&result));
    assert!(matches!(evaluator.eval(result, 0),
        Ok(ModelValue::Int(value)) if value == BigInt::from(2)));
}

#[test]
fn checked_projections_own_defaults_at_the_root_and_below_peeled_stores() {
    for (index_sort, wrap) in [(Sort::Bool, false), (Sort::Int, false), (Sort::Int, true)] {
        let mut terms = TermStore::new();
        let sort = Sort::array(index_sort.clone(), Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let key = if index_sort == Sort::Bool {
            terms.mk_bool(false)
        } else {
            zero
        };
        let base = app(&mut terms, "const-array", &[zero], sort.clone());
        let projected = app(&mut terms, "store", &[base, key, one], sort.clone());
        let array = if wrap {
            app(&mut terms, "store", &[projected, key, one], sort)
        } else {
            projected
        };
        let result = default(&mut terms, array, Sort::Int);
        let assertion = app(&mut terms, "=", &[result, one], Sort::Bool);
        let mut model = Model::default();
        model.projections.insert(projected, Ok(Some(0)));
        model.applications.insert(result, integer(1));
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(evaluator.eval(result, 0),
            Ok(ModelValue::Int(value)) if value == BigInt::from(0)));
        assert!(model.calls.borrow().is_empty());
        assert!(!matches!(
            crate::confirm_model(&terms, &model, &[assertion]),
            crate::GateVerdict::ConfirmedSat
        ));
        // Without the projection, the existing small-finite-carrier rule
        // consumes the exact pin. This control does not change that rule.
        if index_sort == Sort::Bool {
            model.projections.clear();
            assert!(matches!(Evaluator::new(&terms, &model).eval(result, 0),
                Ok(ModelValue::Int(value)) if value == BigInt::from(1)));
            assert_eq!(model.calls.borrow().as_slice(), &[result]);
        }
    }
}

#[test]
fn default_fast_paths_preserve_projection_errors_indices_sorts_and_depth() {
    for shape in 0..3 {
        let mut terms = TermStore::new();
        let base = constant(&mut terms, 0);
        let no = terms.mk_bool(false);
        let one = terms.mk_int(BigInt::from(1));
        let array = match shape {
            0 => dependent(&mut terms),
            1 => base,
            _ => app(&mut terms, "store", &[base, no, one], inner_sort()),
        };
        let result = default(&mut terms, array, Sort::Int);
        for projection in [
            Err(crate::ProjectionLookupError::inconsistent_model(
                "authored refusal",
            )),
            Ok(Some(99)),
            Ok(Some(1)),
        ] {
            let mut model = Model::default();
            model.projections.insert(array, projection);
            model.applications.insert(result, integer(2));
            assert_refused(&Evaluator::new(&terms, &model), &model, result);
        }
    }
    let mut terms = TermStore::new();
    let lambda = dependent(&mut terms);
    let result = default(&mut terms, lambda, Sort::Int);
    let mut model = Model::default();
    model.applications.insert(result, integer(2));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.eval(result, MAX_EVAL_DEPTH),
        Err(EvalError::Resource {
            kind: EvalResource::Depth,
            ..
        })
    ));
    assert!(model.calls.borrow().is_empty());
    assert!(!evaluator.memo.borrow().contains_key(&result));
    assert!(matches!(evaluator.eval(result, 0),
        Ok(ModelValue::Int(value)) if value == BigInt::from(2)));
}

#[test]
fn malformed_default_store_and_constant_metadata_cannot_reach_pins_or_values() {
    for index_sort in [Sort::Bool, Sort::Int] {
        for case in 0..6 {
            let mut terms = TermStore::new();
            let sort = Sort::array(index_sort.clone(), Sort::Int);
            let zero = terms.mk_int(BigInt::from(0));
            let no = terms.mk_bool(false);
            let base_sort = if case == 0 {
                Sort::array(index_sort.clone(), Sort::Bool)
            } else {
                sort.clone()
            };
            let base = terms.mk_var("base", base_sort);
            let key = match (&index_sort, case == 1) {
                (Sort::Bool, false) | (Sort::Int, true) => no,
                _ => zero,
            };
            let value = if case == 2 { no } else { zero };
            let args = if case == 3 {
                vec![base, key]
            } else {
                vec![base, key, value]
            };
            let symbol = if case == 4 {
                Symbol::Indexed("store".into(), vec![0])
            } else {
                Symbol::named("store")
            };
            let result_sort = if case == 5 { Sort::Int } else { sort };
            let array = terms.mk_app(symbol, &args, result_sort);
            let result = default(&mut terms, array, Sort::Int);
            let mut model = Model::default();
            model.applications.insert(result, integer(2));
            assert_refused(&Evaluator::new(&terms, &model), &model, result);
        }
    }
    for case in 0..5 {
        let mut terms = TermStore::new();
        let zero = terms.mk_int(BigInt::from(0));
        let no = terms.mk_bool(false);
        let args = match case {
            0 => vec![no],
            1 => Vec::new(),
            2 => vec![zero, zero],
            _ => vec![zero],
        };
        let symbol = if case == 3 {
            Symbol::Indexed("const-array".into(), vec![0])
        } else {
            Symbol::named("const-array")
        };
        let sort = if case == 4 { Sort::Int } else { inner_sort() };
        let array = terms.mk_app(symbol, &args, sort);
        let result = default(&mut terms, array, Sort::Int);
        let mut model = Model::default();
        model.applications.insert(result, integer(2));
        assert_refused(&Evaluator::new(&terms, &model), &model, result);
    }
}

#[test]
fn projected_finite_store_default_is_not_the_overwritten_representation_default() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let no = terms.mk_bool(false);
    let yes = terms.mk_bool(true);
    let base = constant(&mut terms, 0);
    let first = app(&mut terms, "store", &[base, no, one], inner_sort());
    let covered = app(&mut terms, "store", &[first, yes, one], inner_sort());
    let projected = app(&mut terms, "array_identity", &[covered], inner_sort());
    let result = default(&mut terms, projected, Sort::Int);
    let inner_default = default(&mut terms, covered, Sort::Int);
    let positive = app(&mut terms, "=", &[result, one], Sort::Bool);
    let negative = app(&mut terms, "=", &[result, zero], Sort::Bool);
    let reads = [no, yes].map(|index| app(&mut terms, "select", &[covered, index], Sort::Int));
    let mut model = Model::default();
    model.projections.insert(projected, Ok(Some(0)));
    model.applications.insert(result, integer(1));
    // An unrelated application's pin must not replace the ORIGINAL default
    // lookup when the projection is peeled; no synthetic default is evaluated.
    model.applications.insert(inner_default, integer(7));
    let evaluator = Evaluator::new(&terms, &model);
    for read in reads {
        assert!(matches!(evaluator.eval(read, 0),
            Ok(ModelValue::Int(value)) if value == BigInt::from(1)));
    }
    assert!(matches!(evaluator.eval(result, 0),
        Ok(ModelValue::Int(value)) if value == BigInt::from(1)));
    assert_eq!(model.calls.borrow().as_slice(), &[result]);
    assert!(matches!(
        evaluator.eval(negative, 0),
        Ok(ModelValue::Bool(false))
    ));
    assert!(matches!(
        crate::confirm_model(&terms, &model, &[positive]),
        crate::GateVerdict::ConfirmedSat
    ));
    assert!(!matches!(
        crate::confirm_model(&terms, &model, &[negative]),
        crate::GateVerdict::ConfirmedSat
    ));
}

#[test]
fn default_projection_peeling_keeps_logical_and_active_call_limits() {
    let mut terms = TermStore::new();
    let base = constant(&mut terms, 0);
    let projected = app(&mut terms, "array_identity", &[base], inner_sort());
    let result = default(&mut terms, projected, Sort::Int);
    let mut model = Model::default();
    model.projections.insert(projected, Ok(Some(0)));
    model.applications.insert(result, integer(2));
    let evaluator = Evaluator::new(&terms, &model);
    for (depth, active) in [
        (MAX_EVAL_DEPTH - 1, 0),
        (0, MAX_PROJECTION_EVAL_CALL_DEPTH - 1),
    ] {
        evaluator.active_eval_calls.set(active);
        assert!(matches!(
            evaluator.eval(result, depth),
            Err(EvalError::Resource {
                kind: EvalResource::Depth,
                ..
            })
        ));
        assert_eq!(evaluator.active_eval_calls.get(), active);
        assert!(model.calls.borrow().is_empty());
        assert!(!evaluator.memo.borrow().contains_key(&result));
    }
    evaluator
        .active_eval_calls
        .set(MAX_PROJECTION_EVAL_CALL_DEPTH - 2);
    assert!(matches!(evaluator.eval(result, 0),
        Ok(ModelValue::Int(value)) if value == BigInt::from(0)));
    evaluator.active_eval_calls.set(0);
    assert!(matches!(evaluator.eval(result, 0),
        Ok(ModelValue::Int(value)) if value == BigInt::from(0)));
    assert!(model.calls.borrow().is_empty());
}
