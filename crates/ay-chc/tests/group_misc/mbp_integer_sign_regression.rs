// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for #3005: MBP integer equality substitution must negate
//! the term when the coefficient is negative (variable on RHS of equality).
//!
//! Complements mbp_real_sign_regression.rs by testing the project_integer_var
//! equality path (mbp.rs:912-920) with model evaluation.

use ay_chc::{ChcExpr, ChcSort, ChcVar, Mbp, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// When z is on the RHS of (= x z), factor_var returns coeff=-1, term=neg(x).
/// The equality substitution must negate the term to get neg(neg(x)) = x.
/// Without the fix, z would be substituted with neg(x), violating the MBP
/// contract for model x=7 (because neg(7) = -7, and -7 > 0 is false).
#[test]
fn mbp_project_integer_equality_rhs_var_preserves_model_satisfaction() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    // Formula: (= x z) AND (z > 0) AND (z < 10)
    // Eliminating z via equality substitution.
    // Correct: substitute z with x → (x > 0) AND (x < 10)
    // Wrong: substitute z with -x → (-x > 0) AND (-x < 10) (violated by x=7)
    let formula = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x), ChcExpr::var(z.clone())),
            ChcExpr::gt(ChcExpr::var(z.clone()), ChcExpr::int(0)),
        ),
        ChcExpr::lt(ChcExpr::var(z.clone()), ChcExpr::int(10)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(7));
    model.insert("z".to_string(), SmtValue::Int(7));

    let result = mbp.project(&formula, std::slice::from_ref(&z), &model);

    // z must be eliminated
    let result_vars = result.vars();
    assert!(
        !result_vars.iter().any(|v| v.name == "z"),
        "z must be eliminated from projection result. Got: {result:?}",
    );

    // MBP contract: model must satisfy projected formula.
    // eval_arith handles neg(neg(x)) correctly for Int sort via checked_neg.
    assert_eq!(
        mbp.eval_bool(&result, &model),
        Some(true),
        "MBP contract violated: model (x=7) must satisfy projected formula. \
         If this fails with neg(x), the sign fix at mbp.rs:916-920 is broken. Got: {result:?}",
    );
}
