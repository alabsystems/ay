// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prover coverage tests for MBP (Model-Based Projection).
//!
//! These tests cover previously untested public functions and the
//! real-valued equality sign fix from #3005.
//! Filed as part of tool_quality audit P22.

use ay_chc::{ChcExpr, ChcOp, ChcSort, ChcVar, Mbp, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Test that `implicant_cube` (pub fn, previously untested) produces a formula
/// that is consistent with the model and mentions constrained variables.
#[test]
fn implicant_cube_produces_formula_consistent_with_model() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Formula: x > 0 AND y > x
    let formula = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::gt(ChcExpr::var(y), ChcExpr::var(x)),
    );
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));
    model.insert("y".to_string(), SmtValue::Int(7));

    let cube = mbp.implicant_cube(&formula, &model);

    // Cube must contain both x and y (both are constrained)
    let vars = cube.vars();
    assert!(
        vars.iter().any(|v| v.name == "x"),
        "implicant_cube should mention x"
    );
    assert!(
        vars.iter().any(|v| v.name == "y"),
        "implicant_cube should mention y"
    );

    // Cube must evaluate to true under the model
    assert_eq!(
        mbp.eval_bool(&cube, &model),
        Some(true),
        "implicant_cube result must be true under the model"
    );
}

/// Test that `keep_only` (pub fn, previously untested) eliminates
/// variables not in the keep set while retaining kept variables.
#[test]
fn keep_only_eliminates_non_kept_variables() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Formula: x = y + 1 AND x > 0
    let formula = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::var(x.clone()),
            ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::Int(1)),
        ),
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0)),
    );
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(4));

    // Keep only y — should eliminate x via equality substitution
    let result = mbp.keep_only(&formula, &[y], &model);
    let vars = result.vars();
    assert!(
        !vars.iter().any(|v| v.name == "x"),
        "keep_only should eliminate x"
    );
    assert!(
        vars.iter().any(|v| v.name == "y"),
        "keep_only should retain y"
    );
}

/// Regression test for #3005: project_real_var equality path with negative coefficient.
///
/// When `factor_var` processes `x = z` for variable `z`, it returns `(coeff=-1, term=-x)`.
/// `extract_bound` wraps this as `BoundKind::Equality(-1, -x)`.
/// `project_real_var` must recognize `coeff < 0` and negate the term to get `subst_term = x`,
/// so substituting `z -> x` in `z > 0` yields `x > 0` (correct).
///
/// Without the sign fix, `subst_term = -x`, producing `-x > 0` (wrong for positive x).
#[test]
fn project_real_equality_negative_coeff_substitutes_correct_sign() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Real);
    let z = ChcVar::new("z", ChcSort::Real);

    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::var(z.clone())),
        ChcExpr::gt(ChcExpr::var(z.clone()), ChcExpr::Real(0, 1)),
    );
    let model = FxHashMap::default();
    let result = mbp.project(&formula, std::slice::from_ref(&z), &model);

    // Result must not contain z
    assert!(
        !result.vars().iter().any(|v| v.name == z.name),
        "projected formula must eliminate z; got: {result:?}"
    );

    // Result should contain a Gt comparison (x > 0)
    let conjuncts = result.collect_conjuncts();
    let has_gt = conjuncts
        .iter()
        .any(|c| matches!(c, ChcExpr::Op(ChcOp::Gt, _)));
    assert!(
        has_gt,
        "projection of (x = z) AND (z > 0) should retain a > guard; got: {result:?}"
    );
}
