// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use super::*;
use crate::ChcOp;

const HIDDEN: &str = "__cprop_0_0_0";

#[test]
fn a_name_beyond_the_old_depth_cutoff_cannot_become_a_new_binder() {
    let mut formula = ChcExpr::eq(
        ChcExpr::var(ChcVar::new(HIDDEN, ChcSort::Int)),
        ChcExpr::Int(0),
    );
    // Construct the actual deep formula; `not()` may fold double negation.
    for _ in 0..600 {
        formula = ChcExpr::Op(ChcOp::Not, vec![Arc::new(formula)]);
    }
    let interpretation = PredicateInterpretation::new(Vec::new(), formula);
    let restored = restore(&interpretation, &[ChcSort::Int], &[], "__cprop_0")
        .expect("complete bounded inspection of a 600-node chain");
    assert_ne!(
        restored[0].name, HIDDEN,
        "do not bind a formerly free variable"
    );
}

#[test]
fn a_global_function_symbol_cannot_be_shadowed_by_a_reconstructed_binder() {
    let interpretation = PredicateInterpretation::new(
        Vec::new(),
        ChcExpr::FuncApp(HIDDEN.to_string(), ChcSort::Bool, Vec::new()),
    );
    let restored = restore(&interpretation, &[ChcSort::Int], &[], "__cprop_0")
        .expect("small complete namespace");
    assert_ne!(restored[0].name, HIDDEN);
}

#[test]
fn name_work_exhaustion_declines_instead_of_returning_a_partial_namespace() {
    let interpretation = PredicateInterpretation::new(
        Vec::new(),
        ChcExpr::FuncApp(
            "x".repeat(crate::expr::MAX_PREPROCESSING_NODES),
            ChcSort::Bool,
            Vec::new(),
        ),
    );
    assert!(restore(&interpretation, &[ChcSort::Int], &[], "__cprop_0").is_none());
}
