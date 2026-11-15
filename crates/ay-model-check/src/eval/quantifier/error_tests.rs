// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ArrayValue, ModelView, MAX_EVAL_DEPTH};
use ay_core::term::Symbol;
use ay_core::TermStore;

#[derive(Default)]
struct Model(Vec<(TermId, ModelValue)>);

impl ModelView for Model {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.0
            .iter()
            .find(|(key, _)| *key == term)
            .map(|(_, value)| value.clone())
    }
}

fn boolean(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

fn assert_resource(error: EvalError, expected: EvalResource) {
    assert!(matches!(error, EvalError::Resource { kind, .. } if kind == expected));
}

#[test]
fn rejection_adapters_preserve_failure_kinds_and_context_without_text_authority() {
    for (rejection, expected) in [
        (
            QuantifierRejection::AssignmentBudget,
            EvalResource::Assignments,
        ),
        (QuantifierRejection::EvaluationBudget, EvalResource::Work),
        (QuantifierRejection::BinderLimit, EvalResource::Work),
        (QuantifierRejection::NestingLimit, EvalResource::Depth),
    ] {
        let diagnostic = rejection.to_string();
        let error = EvalError::from(rejection);
        assert_eq!(error.to_string(), diagnostic);
        assert_resource(error, expected);
    }
    for rejection in [
        QuantifierRejection::UnsupportedDomain,
        QuantifierRejection::DuplicateBinder,
        QuantifierRejection::BindingSortMismatch,
        QuantifierRejection::NonBooleanBody,
    ] {
        assert!(matches!(EvalError::from(rejection), EvalError::Refused(_)));
    }
    let error = EvalError::from(QuantifierRejection::UnevaluableBody(EvalError::Resource {
        kind: EvalResource::Depth,
        reason: "model does not pin this leaf".to_string(),
    }));
    assert_eq!(
        error.to_string(),
        "finite quantifier body is unevaluable: model does not pin this leaf"
    );
    assert_resource(error, EvalResource::Depth);
    let unavailable = EvalError::from(QuantifierRejection::UnevaluableBody(
        EvalError::ModelUnavailable("recursion depth limit exceeded".to_string()),
    ));
    assert!(unavailable.is_model_unavailable());
    assert!(matches!(
        EvalError::from(QuantifierRejection::UnevaluableBody(
            EvalError::NonFiniteLambdaArray
        )),
        EvalError::Refused(_)
    ));
}

#[test]
fn quantifier_pending_refusal_survives_unavailable_siblings_in_both_orders() {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("bound", Sort::Bool);
    let missing = terms.mk_var("missing", Sort::Bool);
    let malformed = boolean(&mut terms, "not", &[]);
    let first_hard = terms.mk_ite_raw(bound, missing, malformed);
    let last_hard = terms.mk_ite_raw(bound, malformed, missing);
    let yes = terms.mk_bool(true);
    let no = terms.mk_bool(false);
    let decisive_exists = terms.mk_ite_raw(bound, yes, malformed);
    let decisive_forall = terms.mk_ite_raw(bound, no, malformed);
    let bindings = [("bound".to_string(), Sort::Bool)];
    let model = Model::default();
    for body in [first_hard, last_hard] {
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(
            evaluator.eval_finite_quantifier(QuantifierKind::Forall, &bindings, body, 0),
            Err(EvalError::Refused(_))
        ));
        assert!(evaluator.local_bindings.borrow().is_empty());
    }
    for (kind, body, expected) in [
        (QuantifierKind::Exists, decisive_exists, true),
        (QuantifierKind::Forall, decisive_forall, false),
    ] {
        let evaluator = Evaluator::new(&terms, &model);
        assert!(matches!(
            evaluator.eval_finite_quantifier(kind, &bindings, body, 0),
            Ok(ModelValue::Bool(value)) if value == expected
        ));
        assert!(evaluator.local_bindings.borrow().is_empty());
    }
}

#[test]
fn quantifier_body_depth_error_remains_typed_and_does_not_poison_shallow_retry() {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("bound", Sort::Bool);
    let missing = terms.mk_var("missing", Sort::Bool);
    let yes = terms.mk_bool(true);
    let deeper = boolean(&mut terms, "not", &[yes]);
    let first_depth = terms.mk_ite_raw(bound, missing, deeper);
    let last_depth = terms.mk_ite_raw(bound, deeper, missing);
    let bindings = [("bound".to_string(), Sort::Bool)];
    let model = Model::default();
    for body in [first_depth, last_depth] {
        let evaluator = Evaluator::new(&terms, &model);
        // Body enters MAX-1, ITE's condition and branch enter MAX, and
        // only the nested not's operand exceeds MAX. The sibling is truly
        // model-unavailable rather than another depth failure.
        let error = evaluator
            .eval_finite_quantifier(QuantifierKind::Forall, &bindings, body, MAX_EVAL_DEPTH - 2)
            .expect_err("body depth is not optional model absence");
        assert_resource(error, EvalResource::Depth);
        assert!(evaluator.local_bindings.borrow().is_empty());
        assert_eq!(evaluator.quantifier_state.nesting.get(), 0);
        assert!(matches!(
            evaluator.eval_finite_quantifier(QuantifierKind::Forall, &bindings, body, 0),
            Ok(ModelValue::Bool(false))
        ));
    }
}

#[test]
fn actual_shared_quantifier_limits_report_resource_kinds_and_keep_fresh_retry() {
    let mut terms = TermStore::new();
    let yes = terms.mk_bool(true);
    let bindings = [("bound".to_string(), Sort::Bool)];
    let model = Model::default();
    let work = Evaluator::new(&terms, &model);
    work.quantifier_state.nesting.set(1);
    work.quantifier_state.work_left.set(0);
    for _ in 0..2 {
        assert_resource(
            work.charge_quantifier_work(1).expect_err("work exhausted"),
            EvalResource::Work,
        );
    }
    let assignments = Evaluator::new(&terms, &model);
    assignments.quantifier_state.assignments_left.set(1);
    assert_resource(
        assignments
            .eval_finite_quantifier(QuantifierKind::Forall, &bindings, yes, 0)
            .expect_err("complete domain precedes even constant truth"),
        EvalResource::Assignments,
    );
    let nesting = Evaluator::new(&terms, &model);
    nesting.quantifier_state.nesting.set(MAX_QUANTIFIER_NESTING);
    assert_resource(
        nesting
            .eval_finite_quantifier(QuantifierKind::Forall, &bindings, yes, 0)
            .expect_err("nesting exhausted"),
        EvalResource::Depth,
    );
    assert!(matches!(
        Evaluator::new(&terms, &model).eval_finite_quantifier(
            QuantifierKind::Forall,
            &bindings,
            yes,
            0
        ),
        Ok(ModelValue::Bool(true))
    ));
}

struct EndpointFixture {
    terms: TermStore,
    array: TermId,
    body: TermId,
    bindings: Vec<(String, Sort)>,
}

impl EndpointFixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let sort = Sort::bitvec(64);
        let bound = terms.mk_var("i", sort.clone());
        let array = terms.mk_var("array", Sort::array(sort.clone(), sort.clone()));
        let zero = terms.mk_bitvec(BigInt::from(0), 64);
        let endpoint = terms.mk_app(Symbol::named("select"), &[array, zero], sort.clone());
        let below = boolean(&mut terms, "bvult", &[bound, zero]);
        let above = boolean(&mut terms, "bvuge", &[bound, zero]);
        let optional = boolean(&mut terms, "bvult", &[bound, endpoint]);
        // The first two atoms already have empty joint false-support, but
        // the third endpoint still must not hide a hard evaluation failure.
        let body = boolean(&mut terms, "or", &[below, above, optional]);
        Self {
            terms,
            array,
            body,
            bindings: vec![("i".to_string(), sort)],
        }
    }

    fn derive(
        &self,
        model: &Model,
        depth: usize,
    ) -> Result<Option<GuardedDomain>, QuantifierRejection> {
        let evaluator = Evaluator::new(&self.terms, model);
        evaluator.quantifier_state.nesting.set(1);
        GuardedDomain::derive(
            &evaluator,
            QuantifierKind::Forall,
            &self.bindings,
            self.body,
            depth,
            MAX_QUANTIFIER_ASSIGNMENTS,
        )
    }
}

#[test]
fn endpoint_depth_failure_cannot_be_discarded_by_an_empty_support_sibling() {
    let fixture = EndpointFixture::new();
    let model = Model::default();
    assert!(matches!(fixture.derive(&model, 0), Ok(Some(domain)) if domain.count == 0));
    let error = match fixture.derive(&model, MAX_EVAL_DEPTH - 1) {
        Err(error) => error,
        _ => panic!("the deeper select index endpoint must exceed evaluator depth"),
    };
    assert_resource(error.into(), EvalResource::Depth);
    assert!(matches!(fixture.derive(&model, 0), Ok(Some(domain)) if domain.count == 0));
}

#[test]
fn malformed_endpoint_values_remain_hard_while_complete_typed_arrays_stay_supported() {
    let fixture = EndpointFixture::new();
    let malformed = Model(vec![(fixture.array, ModelValue::Bool(true))]);
    assert!(matches!(
        fixture.derive(&malformed, 0),
        Err(QuantifierRejection::UnevaluableBody(EvalError::Refused(_)))
    ));
    let complete = Model(vec![(
        fixture.array,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::bitvec(BigInt::from(7), 64),
            store: Vec::new(),
        })),
    )]);
    assert!(matches!(fixture.derive(&complete, 0), Ok(Some(domain)) if domain.count == 0));
}
