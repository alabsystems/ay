// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn construction_rejects_ill_typed_projection() {
    let error = ProjectionUfModel::from_test_definitions([(
        Symbol::named("f"),
        vec![Sort::Bool, Sort::Int],
        Sort::Bool,
        1,
    )])
    .expect_err("the selected Int argument cannot be a Bool result");
    assert!(matches!(
        error,
        ProjectionUfModelError::ProjectionSortMismatch { .. }
    ));
}

#[test]
fn construction_rejects_indexed_symbol() {
    let error = ProjectionUfModel::from_test_definitions([(
        Symbol::indexed("extract", vec![7, 0]),
        vec![Sort::bitvec(8)],
        Sort::bitvec(8),
        0,
    )])
    .expect_err("v1 accepts named symbols only");
    assert!(matches!(error, ProjectionUfModelError::NonNamedSymbol(_)));
}

#[test]
fn lookup_requires_exact_symbol_and_complete_signature() {
    let symbol = Symbol::named("f!overload!1");
    let model = ProjectionUfModel::from_test_definitions([(
        symbol.clone(),
        vec![Sort::Bool, Sort::Int],
        Sort::Bool,
        0,
    )])
    .expect("well typed unique symbol");

    assert_eq!(
        model.projected_argument_for_signature(&symbol, &[Sort::Bool, Sort::Int], &Sort::Bool,),
        Ok(Some(0))
    );
    assert!(matches!(
        model.projected_argument_for_signature(&symbol, &[Sort::Bool], &Sort::Bool),
        Err(ProjectionUfReadError::SignatureConflict { .. })
    ));
    assert!(matches!(
        model.projected_argument_for_signature(&symbol, &[Sort::Bool, Sort::Bool], &Sort::Bool,),
        Err(ProjectionUfReadError::SignatureConflict { .. })
    ));
    assert!(matches!(
        model.projected_argument_for_signature(&symbol, &[Sort::Bool, Sort::Int], &Sort::Int,),
        Err(ProjectionUfReadError::SignatureConflict { .. })
    ));
    assert_eq!(
        model.projected_argument_for_signature(
            &Symbol::named("f"),
            &[Sort::Bool, Sort::Int],
            &Sort::Bool,
        ),
        Ok(None)
    );
}
