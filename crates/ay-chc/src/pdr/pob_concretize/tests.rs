// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcSort, ChcVar};

#[test]
fn test_mark_pattern_vars() {
    // Pattern: __gg_k0 * x where __gg_k0 is a pattern var.
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);
    let x = ChcVar::new("x", ChcSort::Int);
    let pattern_vars = vec![pv.clone()];

    let model = HashMap::default();

    // mul(pattern_var, state_var) - marks the state var.
    let pattern1 = ChcExpr::mul(ChcExpr::var(pv.clone()), ChcExpr::var(x.clone()));
    let mut conc1 = PobConcretizer::new(&pattern1, &pattern_vars, &model);
    conc1.mark_pattern_vars();
    assert!(
        conc1.marked.contains(&ChcExpr::var(x.clone())),
        "pattern_var * state_var should mark the state_var"
    );

    // mul(state_var, pattern_var) - marks the state var.
    let pattern2 = ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::var(pv));
    let mut conc2 = PobConcretizer::new(&pattern2, &pattern_vars, &model);
    conc2.mark_pattern_vars();
    assert!(
        conc2.marked.contains(&ChcExpr::var(x)),
        "state_var * pattern_var should mark the state_var"
    );
}

#[test]
fn test_has_nonlinear_pattern_vars() {
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let pattern_vars = vec![pv.clone()];

    // Nonlinear: pattern_var * state_var
    let e1 = ChcExpr::mul(ChcExpr::var(pv.clone()), ChcExpr::var(x.clone()));
    assert!(has_nonlinear_pattern_vars(&e1, &pattern_vars));

    // Linear: pattern_var * numeral
    let e2 = ChcExpr::mul(ChcExpr::var(pv.clone()), ChcExpr::int(5));
    assert!(!has_nonlinear_pattern_vars(&e2, &pattern_vars));

    // No pattern vars: x * y is not a "pattern var mul"
    let e3 = ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::var(y));
    assert!(!has_nonlinear_pattern_vars(&e3, &pattern_vars));

    // Nested: x >= pattern_var * (x + 1)
    let e4 = ChcExpr::ge(
        ChcExpr::var(x.clone()),
        ChcExpr::mul(
            ChcExpr::var(pv),
            ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
        ),
    );
    assert!(has_nonlinear_pattern_vars(&e4, &pattern_vars));
}

#[test]
fn test_eval_arithmetic() {
    let model: HashMap<String, SmtValue> = [
        ("x".to_string(), SmtValue::Int(3)),
        ("y".to_string(), SmtValue::Int(5)),
    ]
    .into_iter()
    .collect();

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // x + y = 3 + 5 = 8
    let pattern = ChcExpr::Bool(true); // dummy
    let conc = PobConcretizer::new(&pattern, &[], &model);

    let expr = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y));
    let evaled = conc.eval(&expr);
    assert_eq!(evaled, ChcExpr::Int(8));

    // 2 * x = 2 * 3 = 6
    let expr2 = ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(x));
    let evaled2 = conc.eval(&expr2);
    assert_eq!(evaled2, ChcExpr::Int(6));
}

#[test]
fn test_concretize_simple() {
    // Pattern: __gg_k0 * x (pattern var times state var)
    // POB: 2*x + y <= 10 with model {x=3, y=4}
    // Expected: x <= 3 ∧ y <= 4

    let pv = ChcVar::new("__gg_k0", ChcSort::Int);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let pattern_vars = vec![pv.clone()];
    let pattern = ChcExpr::mul(ChcExpr::var(pv), ChcExpr::var(x.clone()));

    let model: HashMap<String, SmtValue> = [
        ("x".to_string(), SmtValue::Int(3)),
        ("y".to_string(), SmtValue::Int(4)),
    ]
    .into_iter()
    .collect();

    let mut conc = PobConcretizer::new(&pattern, &pattern_vars, &model);

    // POB: 2*x + y <= 10
    let cube = vec![ChcExpr::le(
        ChcExpr::add(
            ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(x.clone())),
            ChcExpr::var(y),
        ),
        ChcExpr::int(10),
    )];

    let result = conc.apply(&cube).unwrap();

    // Should have: x <= 3 (from split), y <= 4 (remaining evaluated)
    assert!(!result.is_empty(), "concretization should produce output");

    // Check that x <= 3 is in output
    let x_bound = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(3));
    assert!(
        result.contains(&x_bound),
        "should contain x <= 3, got {result:?}"
    );
}

#[test]
fn test_concretize_no_split_preserves_literal() {
    // When nothing is split out, the original literal must be preserved.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let pattern = ChcExpr::Bool(true); // no mul => no marks
    let model: HashMap<String, SmtValue> = [
        ("x".to_string(), SmtValue::Int(3)),
        ("y".to_string(), SmtValue::Int(4)),
    ]
    .into_iter()
    .collect();

    let mut conc = PobConcretizer::new(&pattern, &[], &model);

    let lit = ChcExpr::le(
        ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y)),
        ChcExpr::int(10),
    );
    let cube = vec![lit.clone()];

    let out = conc.apply(&cube).unwrap();
    assert_eq!(out, vec![lit]);
}
