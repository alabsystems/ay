// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The tightest-lower-bound comparison cross-multiplies exactly: a bound the
//! model cannot evaluate reads as i128::MIN, and with a coefficient above 1
//! the i128 product overflowed and panicked (PDKIND on
//! `examples/model_checker_consumer_looping_id_bv64.smt2`).

use super::*;

#[test]
fn an_unevaluable_lower_bound_with_a_coefficient_is_compared_without_overflow() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);
    let scaled =
        |coefficient: i128| ChcExpr::mul(ChcExpr::Int(coefficient), ChcExpr::var(x.clone()));
    let literals = vec![
        // 2x >= y and 3x >= z, where the model gives neither y nor z.
        Literal::new(ChcExpr::ge(scaled(2), ChcExpr::var(y)), true),
        Literal::new(ChcExpr::ge(scaled(3), ChcExpr::var(z)), true),
        Literal::new(ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(10)), true),
    ];
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    let projected = mbp.project_single_var(&x, literals, &model);
    assert!(
        projected
            .iter()
            .all(|literal| !literal.atom.contains_var_name("x")),
        "x is projected out: {projected:?}"
    );
}
