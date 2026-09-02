// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{EngineConfig, EngineSelector, TheoryProfile};
use crate::portfolio::features::ChcFeatureExtractor;
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

#[test]
fn bv_indexed_array_uses_array_selection() {
    let mut problem = ChcProblem::new();
    let array_sort = ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::BitVec(8)));
    let inv = problem.declare_predicate("Inv", vec![array_sort.clone(), ChcSort::BitVec(32)]);
    let array = ChcVar::new("a", array_sort);
    let index = ChcVar::new("i", ChcSort::BitVec(32));

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::bool_const(true)),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(array.clone()), ChcExpr::var(index.clone())],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv,
                vec![ChcExpr::var(array.clone()), ChcExpr::var(index.clone())],
            )],
            None,
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(array.clone()), ChcExpr::var(index.clone())],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(array), ChcExpr::var(index)])],
            None,
        ),
        ClauseHead::False,
    ));

    let features = ChcFeatureExtractor::extract(&problem);
    let selection = EngineSelector::select(&features);

    assert_eq!(features.theory, TheoryProfile::BvArrays);
    assert!(features.has_bv_args);
    assert!(features.base.uses_arrays);
    assert!(selection.reason.contains("Array"));
    assert!(selection
        .engines
        .iter()
        .any(|engine| matches!(engine, EngineConfig::Lawi(_))));
    assert!(
        !selection
            .engines
            .iter()
            .any(|engine| matches!(engine, EngineConfig::Kind(_))),
        "BV-indexed arrays must not use the scalar-BV Kind roster"
    );
}
