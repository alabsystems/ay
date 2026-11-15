// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What `extract_equalities_and_propagate` may and may not assume about its
//! input (see the postcondition in `equality.rs`).

use super::equality::{
    extract_equalities_and_propagate, extract_equalities_from_formula,
    extract_equalities_with_relations,
};
use crate::{ChcExpr, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// An UNSATISFIABLE conjunction is a legal input: `init_must_summaries_from_facts`
/// passes every fact clause's constraint unchecked. `(and (= x y) (= x 5) (= y 6))`
/// gives the related pair two different values; the propagation keeps what it saw
/// and must not treat the disagreement as a broken fixpoint (the debug
/// postcondition panicked here, and Trust printed it as a compiler panic).
#[test]
fn test_extract_equalities_contradictory_conjunction_is_not_a_fixpoint_bug() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::and_all([
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5)),
        ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(6)),
    ]);

    let values = extract_equalities_and_propagate(&expr);
    assert_eq!(values.get("x"), Some(&5));
    assert_eq!(values.get("y"), Some(&6));
}

/// `(= x (+ y 1))` is matched by the value arm for `(= n (+ y c))`, which
/// records nothing when `x` is not a constant, so it never becomes a relation
/// (the relation arms once written for it were unreachable). The model pass
/// still derives `x` by evaluating the sum once `y` is known.
#[test]
fn test_offset_equality_is_evaluated_not_related() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::and_all([
        ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(4)),
        ChcExpr::eq(
            ChcExpr::var(x),
            ChcExpr::add(ChcExpr::var(y), ChcExpr::int(1)),
        ),
    ]);

    let mut values = FxHashMap::default();
    let mut relations = Vec::new();
    extract_equalities_with_relations(&expr, &mut values, &mut relations);
    assert_eq!(values.get("y"), Some(&4));
    assert!(relations.is_empty(), "{relations:?}");

    let mut model = FxHashMap::default();
    extract_equalities_from_formula(&expr, &mut model);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(5)));
    assert_eq!(model.get("y"), Some(&SmtValue::Int(4)));
}
