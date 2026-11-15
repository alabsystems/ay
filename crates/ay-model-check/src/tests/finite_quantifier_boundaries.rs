// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `finite_quantifiers` to preserve test FQNs.

#[test]
fn finite_quantifier_binder_count_limit_is_inclusive_and_precedes_enumeration() {
    let mut terms = TermStore::new();
    let no = terms.mk_bool(false);
    let mut bindings: Vec<_> = (0..16)
        .map(|index| (format!("unused_{index}"), Sort::Bool))
        .collect();
    let at_limit = terms.mk_forall(bindings.clone(), no);
    bindings.push(("one_too_many".to_string(), Sort::Bool));
    let over_limit = terms.mk_forall(bindings, no);
    let model = StubModel::new();
    let evaluator = Evaluator::new(&terms, &model);

    // The entire 2^16 carrier fits, but a counterexample at its first tuple
    // keeps this binder-boundary test cheap. Seventeen binders must decline
    // before that same false body can short-circuit domain validation.
    assert!(matches!(
        evaluator.evaluate(over_limit),
        EvalOutcome::Unevaluable(reason) if reason.contains("binder count limit")
    ));
    assert!(matches!(
        evaluator.evaluate(at_limit),
        EvalOutcome::Value(ModelValue::Bool(false))
    ));
}

#[test]
fn finite_quantifier_empty_binder_list_evaluates_its_body_once() {
    let mut terms = TermStore::new();
    let yes = terms.mk_bool(true);
    let no = terms.mk_bool(false);
    let unknown = terms.mk_var("unknown", Sort::Bool);
    let cases: Vec<_> = [yes, no, unknown]
        .into_iter()
        .map(|body| {
            (
                body,
                terms.mk_forall(Vec::new(), body),
                terms.mk_exists(Vec::new(), body),
            )
        })
        .collect();
    let model = StubModel::new();
    let evaluator = Evaluator::new(&terms, &model);

    // An empty Cartesian product has one tuple, not zero. Neither quantifier
    // may substitute its vacuity value for a false or unevaluable body.
    for (body, forall, exists) in cases {
        for quantified in [forall, exists] {
            let actual = evaluator.evaluate(quantified);
            if body == unknown {
                assert!(matches!(actual, EvalOutcome::Unevaluable(_)));
            } else {
                assert!(matches!(
                    actual,
                    EvalOutcome::Value(ModelValue::Bool(value)) if value == (body == yes)
                ));
            }
        }
    }
}

#[test]
fn finite_quantifier_single_carrier_can_spend_the_exact_assignment_cap() {
    let mut terms = TermStore::new();
    let yes = terms.mk_bool(true);
    let over_limit = terms.mk_forall(vec![("wide".to_string(), Sort::bitvec(17))], yes);
    let at_limit = terms.mk_forall(vec![("exact".to_string(), Sort::bitvec(16))], yes);
    let next = terms.mk_forall(vec![("next".to_string(), Sort::Bool)], yes);
    let model = StubModel::new();
    let evaluator = Evaluator::new(&terms, &model);

    assert!(matches!(
        evaluator.evaluate(over_limit),
        EvalOutcome::Unevaluable(reason) if reason.contains("assignment budget")
    ));
    // A constant true body forces all 65,536 universal assignments while
    // keeping work far below its separate limit. A rejected 2^17 domain must
    // not spend assignments that prevent this exact-cap domain from fitting.
    assert!(matches!(
        evaluator.evaluate(at_limit),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
    assert!(matches!(
        evaluator.evaluate(next),
        EvalOutcome::Unevaluable(reason) if reason.contains("assignment budget")
    ));
    // Exhaustion does not invalidate an already established, scope-independent
    // result, and a fresh evaluator has its own complete assignment envelope.
    assert!(matches!(
        evaluator.evaluate(at_limit),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
    assert!(matches!(
        Evaluator::new(&terms, &model).evaluate(next),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
}

#[test]
fn finite_quantifier_nesting_limit_restores_depth_and_outer_binding() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let mut too_deep_body = x;
    let mut at_limit = terms.mk_bool(true);
    // Empty binders isolate depth from Cartesian growth: each wrapper has one
    // tuple. Adding one binding wrapper below crosses exactly 32 quantifiers.
    for _ in 0..32 {
        too_deep_body = terms.mk_forall(Vec::new(), too_deep_body);
        at_limit = terms.mk_forall(Vec::new(), at_limit);
    }
    let too_deep = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], too_deep_body);
    let model = StubModel::new().with(x, ModelValue::Bool(false));
    let evaluator = Evaluator::new(&terms, &model);

    assert!(matches!(
        evaluator.evaluate(too_deep),
        EvalOutcome::Unevaluable(reason) if reason.contains("nesting or native evaluation depth")
    ));
    // Both outer valuations fail, so the last attempted binding is x=true.
    // The ambient false value must be visible again after all guards unwind.
    assert!(matches!(
        evaluator.evaluate(x),
        EvalOutcome::Value(ModelValue::Bool(false))
    ));
    // This distinct, previously unvisited root cannot borrow a cached success
    // to hide a leaked nesting counter; the inclusive limit must still work.
    assert!(matches!(
        evaluator.evaluate(at_limit),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
}

#[test]
fn finite_quantifier_native_depth_failure_restores_evaluator_and_binding() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let mut body = x;
    for _ in 0..128 {
        // Preserve every recursive edge: mk_not would fold double negations.
        body = terms.mk_not_raw(body);
    }
    let deep = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], body);
    let shallow = terms.mk_exists(vec![("x".to_string(), Sort::Bool)], x);
    let model = StubModel::new().with(x, ModelValue::Bool(false));
    let evaluator = Evaluator::new(&terms, &model);

    // Only one quantifier is active: this exercises the separate native-call
    // guard, with a linear body and at most two attempted assignments.
    assert!(matches!(
        evaluator.evaluate(deep),
        EvalOutcome::Unevaluable(reason) if reason.contains("nesting or native evaluation depth")
    ));
    assert!(matches!(
        evaluator.evaluate(x),
        EvalOutcome::Value(ModelValue::Bool(false))
    ));
    assert!(matches!(
        evaluator.evaluate(shallow),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
}
