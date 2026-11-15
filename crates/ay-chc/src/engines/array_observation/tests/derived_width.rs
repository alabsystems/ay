// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A small Bool root can hide a wide intermediate under extract/compare.
//! No generated, reduced or closed-model node may evade the private width cap.

use super::*;

fn derived(over_limit: bool) -> Vec<ChcExpr> {
    let extra = if over_limit { 65 } else { 64 };
    vec![
        operation(ChcOp::BvConcat, bv(0, 64), bv(0, extra)),
        ChcExpr::Op(
            ChcOp::BvRepeat(if over_limit { 3 } else { 2 }),
            vec![Arc::new(bv(0, 64))],
        ),
        ChcExpr::Op(ChcOp::BvZeroExtend(extra), vec![Arc::new(bv(0, 64))]),
        ChcExpr::Op(ChcOp::BvSignExtend(extra), vec![Arc::new(bv(0, 64))]),
        ChcExpr::Op(
            ChcOp::Int2Bv(if over_limit { 129 } else { 128 }),
            vec![Arc::new(ChcExpr::Int(0))],
        ),
    ]
}

fn enclosed(expression: ChcExpr) -> ChcExpr {
    ChcExpr::eq(
        ChcExpr::Op(ChcOp::BvExtract(31, 0), vec![Arc::new(expression)]),
        bv(0, 32),
    )
}

#[test]
fn source_derived_widths_at_128_are_admitted_even_under_a_boolean_root() {
    for expression in derived(false) {
        let mut original = source(9, false);
        let clause = &mut original.clauses_mut()[1];
        clause.body.constraint = Some(ChcExpr::and(
            clause.body.constraint.take().unwrap(),
            enclosed(expression),
        ));
        let before = original.clone();
        assert!(Projection::new(&original, &mut || true).is_some());
        same_source(&before, &original);
    }
}

#[test]
fn source_wide_concat_repeat_extensions_and_int2bv_decline_at_the_intermediate_node() {
    for expression in derived(true) {
        let mut original = source(9, false);
        let clause = &mut original.clauses_mut()[1];
        clause.body.constraint = Some(ChcExpr::and(
            clause.body.constraint.take().unwrap(),
            enclosed(expression),
        ));
        let before = original.clone();
        assert!(Projection::new(&original, &mut || true).is_none());
        same_source(&before, &original);
    }
}

#[test]
fn closed_model_and_lifted_original_formulas_admit_computed_width_128() {
    let original = source(9, false);
    let projected = project(&original);
    let body = original.lookup_predicate("B").unwrap();
    for expression in derived(false) {
        let mut model = candidate(projected.reduced());
        let interpretation = model.interpretations.get_mut(&body).unwrap();
        interpretation.formula = ChcExpr::and(interpretation.formula.clone(), enclosed(expression));
        let before = format!("{model:?}");
        assert!(projected.lift(&model, &mut || true).is_some());
        assert_eq!(format!("{model:?}"), before);
    }
}

#[test]
fn closed_bool_model_cannot_hide_wide_intermediates_from_typed_lifting() {
    let original = source(9, false);
    let projected = project(&original);
    let body = original.lookup_predicate("B").unwrap();
    for expression in derived(true) {
        let mut model = candidate(projected.reduced());
        let interpretation = model.interpretations.get_mut(&body).unwrap();
        interpretation.formula = ChcExpr::and(interpretation.formula.clone(), enclosed(expression));
        let before = format!("{model:?}");
        assert!(projected.lift(&model, &mut || true).is_none());
        assert_eq!(format!("{model:?}"), before);
    }
}
