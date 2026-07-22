// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn translate_to_canonical_names_skips_cross_sort_constituents_7897() {
    let arr = ChcVar::new(
        "arr",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let idx = ChcVar::new("idx", ChcSort::Int);
    let canonical_val = ChcVar::new("__p0_a0", ChcSort::Int);

    let head_args = vec![ChcExpr::Op(
        ChcOp::Select,
        vec![
            Arc::new(ChcExpr::var(arr.clone())),
            Arc::new(ChcExpr::var(idx.clone())),
        ],
    )];

    let constraint = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(idx), ChcExpr::int(7)),
        ChcExpr::eq(
            ChcExpr::Op(
                ChcOp::Select,
                vec![
                    Arc::new(ChcExpr::var(arr.clone())),
                    Arc::new(ChcExpr::int(0)),
                ],
            ),
            ChcExpr::int(10),
        ),
    );

    let translated =
        PdrSolver::translate_to_canonical_names(&constraint, &head_args, &[canonical_val.clone()]);
    let translated_str = format!("{translated}");

    assert!(
        translated_str.contains(&canonical_val.name),
        "scalar index variable should map to canonical slot, got: {translated_str}"
    );
    assert!(
        translated_str.contains("arr"),
        "array constituent vars must not be rewritten through scalar slots, got: {translated_str}"
    );
}
