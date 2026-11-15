// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::smt::SmtValue;
use ay_core::kani_compat::DetHashMap;

fn lift(
    problem: &ChcProblem,
    header: PredicateId,
    x: &ChcVar,
    control: &Control<'_>,
) -> Option<InvariantModel> {
    let formula = ChcExpr::Op(ChcOp::Not, vec![Arc::new(ChcExpr::var(x.clone()))]);
    lift_header_to_full_model_controlled(
        problem,
        header,
        std::slice::from_ref(x),
        &formula,
        control,
    )
}

fn check_boolean_images(model: &InvariantModel, header: PredicateId, body: PredicateId) {
    assert_eq!(model.len(), 2);
    for (predicate, expected) in [(header, false), (body, true)] {
        let interpretation = model.get(&predicate).expect("complete original model");
        assert_eq!(interpretation.vars.len(), 1);
        for value in [false, true] {
            let mut values = DetHashMap::default();
            values.insert(interpretation.vars[0].name.clone(), SmtValue::Bool(value));
            assert_eq!(
                crate::expr::evaluate::evaluate_expr(&interpretation.formula, &values),
                Some(SmtValue::Bool(value == expected))
            );
        }
    }
}

#[test]
fn lifting_every_callback_refuses_instead_of_publishing_partial_model() {
    let (problem, header, body, x) = boolean_cfg();
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let control = Control::new(deadline(), &mut callback);
    let model = lift(&problem, header, &x, &control).expect("complete Boolean images");
    check_boolean_images(&model, header, body);
    let full = calls.get();
    assert!(full > 20);
    for stop in 1..=full {
        let count = Cell::new(0);
        let mut refusal = || {
            count.set(count.get() + 1);
            count.get() != stop
        };
        let control = Control::new(deadline(), &mut refusal);
        assert!(
            lift(&problem, header, &x, &control).is_none(),
            "poll {stop}"
        );
        assert_eq!(count.get(), stop);
        assert!(control.stopped());
        assert!(lift(&problem, header, &x, &control).is_none());
        assert_eq!(count.get(), stop);
    }
    let mut live = || true;
    check_boolean_images(
        &lift(&problem, header, &x, &Control::new(deadline(), &mut live)).expect("fresh attempt"),
        header,
        body,
    );
}

#[test]
fn lifting_uses_original_deadline_and_rejects_late_true_callback() {
    let (problem, header, _, x) = boolean_cfg();
    let calls = Cell::new(0);
    let mut count = || {
        calls.set(calls.get() + 1);
        true
    };
    assert!(lift(&problem, header, &x, &Control::new(deadline(), &mut count)).is_some());
    let final_poll = calls.get();
    let start = ay_core::time::Instant::now();
    let end = start + Duration::from_secs(1);
    let now = Cell::new(start);
    let clock = || now.get();
    calls.set(0);
    let mut expire = || {
        calls.set(calls.get() + 1);
        if calls.get() == final_poll {
            now.set(end);
        }
        true
    };
    let control = Control::with_clock(end, &mut expire, &clock);
    assert!(lift(&problem, header, &x, &control).is_none());
    assert_eq!(calls.get(), final_poll);
    now.set(start);
    assert!(lift(&problem, header, &x, &control).is_none());
    assert_eq!(calls.get(), final_poll);
}

#[test]
fn incomplete_original_predicate_images_never_publish_a_partial_model() {
    let (mut problem, header, _, x) = boolean_cfg();
    problem.declare_predicate("uncovered", vec![ChcSort::Bool]);
    let mut live = || true;
    let control = Control::new(deadline(), &mut live);
    assert!(lift(&problem, header, &x, &control).is_none());
    assert!(
        !control.stopped(),
        "ordinary unsupported image is not cancellation"
    );
}
