// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Verify eval_arith uses Euclidean division (SMT-LIB semantics)
/// via shared smt_euclid_div/smt_euclid_mod from expr.rs.
/// Unit tests for the functions themselves: expr.rs::test_smt_euclid_div_mod_all_sign_combos.
#[test]
fn test_eval_arith_euclidean_div_mod() {
    let mbp = Mbp::new();
    let model = FxHashMap::default();
    // 7 div (-2) = -3 (Euclidean, not floor's -4)
    let div_expr = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::Int(7)), Arc::new(ChcExpr::Int(-2))],
    );
    assert_eq!(mbp.eval_arith(&div_expr, &model), Some(-3));
    // 7 mod (-2) = 1 (Euclidean, not floor's -1)
    let mod_expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::Int(7)), Arc::new(ChcExpr::Int(-2))],
    );
    assert_eq!(mbp.eval_arith(&mod_expr, &model), Some(1));
}

// Overflow regression tests for simplification (#2950) are covered by
// simplify_constants tests in expr.rs: simplify_constants_add_coeff_mul_overflow_bails,
// simplify_constants_mul_overflow_bails, simplify_constants_neg_overflow_bails.

/// Regression test for #2950: extract_var_coeff with i128::MIN coefficient
#[test]
fn test_extract_var_coeff_i128_min_does_not_panic() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mul(ChcExpr::Int(i128::MIN), ChcExpr::var(x.clone()));

    let (coeff, _rest) = Mbp::extract_var_coeff(&expr, &x);
    assert_eq!(coeff, i128::MIN);
    // saturating_abs handles i128::MIN (used by project_integer_var)
    assert_eq!(coeff.saturating_abs(), i128::MAX);
}

/// MBP project contract: M |= project(phi, vars, M)
/// Tests that projection of (x > z) ∧ (z > 0) eliminating z produces
/// a formula satisfied by the model.
///
/// Regression: extract_bound sign error — when z appears on RHS of Gt,
/// factor_var returns (coeff=-1, term=-x). extract_bound must negate the
/// term when negating the coefficient, otherwise it produces z < -x instead
/// of the correct z < x.
#[test]
fn project_gt_with_var_on_rhs_preserves_model_satisfaction() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    // Formula: (x > z) ∧ (z > 0)
    let formula = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::var(z.clone())),
        ChcExpr::gt(ChcExpr::var(z.clone()), ChcExpr::int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(10));
    model.insert("z".to_string(), SmtValue::Int(3));

    // Eliminate z; expected: something like (x > 0) or (x >= 2)
    let result = mbp.project(&formula, std::slice::from_ref(&z), &model);

    // Core MBP contract: model |= result
    assert_eq!(
        mbp.eval_bool(&result, &model),
        Some(true),
        "MBP contract: model must satisfy projected formula. Got: {result:?}",
    );

    // z must be eliminated
    let result_vars = result.vars();
    assert!(
        !result_vars.iter().any(|v| v.name == "z"),
        "z must be eliminated from projection result"
    );
}

/// Same test with AllowResidual mode
#[test]
fn project_with_mode_allow_residual_preserves_model_satisfaction() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::var(z.clone())),
        ChcExpr::gt(ChcExpr::var(z.clone()), ChcExpr::int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(10));
    model.insert("z".to_string(), SmtValue::Int(3));

    let result = mbp.project_with_mode(
        &formula,
        std::slice::from_ref(&z),
        &model,
        MbpMode::AllowResidual,
    );

    // Substitute residual vars with model values for evaluation
    let mut eval_formula = result.formula.clone();
    for var in &result.residual_vars {
        if let Some(val) = model.get(&var.name) {
            let val_expr = match val {
                SmtValue::Int(n) => ChcExpr::Int(*n),
                SmtValue::Bool(b) => ChcExpr::Bool(*b),
                _ => continue,
            };
            eval_formula = eval_formula.substitute(&[(var.clone(), val_expr)]);
        }
    }

    assert_eq!(
            mbp.eval_bool(&eval_formula, &model),
            Some(true),
            "MBP contract (allow-residual): model must satisfy projected formula after residual substitution. Got: {:?}",
            result.formula,
        );
}

/// Regression for #3005: project_integer_var equality substitution must negate
/// the term when the coefficient is negative (variable on RHS of equality).
///
/// When z is on the RHS of (= x z), factor_var returns coeff=-1, term=neg(x).
/// The fix negates term to get neg(neg(x)) which is semantically x.
/// Without the fix, z would be substituted with neg(x), producing wrong sign.
#[test]
fn project_integer_var_equality_rhs_negative_coeff_sign_fix() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    // Formula: (= x z) AND (z > 0) AND (z < 10)
    // Eliminating z via equality substitution.
    // factor_var returns coeff=-1 for z on RHS.
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
             If this fails with neg(x), the sign fix at line 916-920 is broken. Got: {result:?}",
    );
}

/// Same test but using Real sort to exercise project_real_var equality path
/// at line 1078-1084 specifically.
#[test]
fn project_real_var_equality_rhs_negative_coeff_eliminates_z() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Real);
    let z = ChcVar::new("z", ChcSort::Real);

    // Formula: (= x z) AND (z > 0)
    // Eliminating z: factor_var returns coeff=-1 for z on RHS.
    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::var(z.clone())),
        ChcExpr::gt(ChcExpr::var(z.clone()), ChcExpr::int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(7));
    model.insert("z".to_string(), SmtValue::Int(7));

    let result = mbp.project(&formula, std::slice::from_ref(&z), &model);

    // z must be eliminated
    let result_vars = result.vars();
    assert!(
        !result_vars.iter().any(|v| v.name == "z"),
        "z must be eliminated from Real projection result. Got: {result:?}",
    );

    // x must be present (substituted for z)
    assert!(
        result_vars.iter().any(|v| v.name == "x"),
        "x should appear in Real projection result (substituted for z). Got: {result:?}",
    );
}

#[test]
fn extract_bound_negative_coeff_flips_term_for_all_inequalities() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);
    let x_expr = ChcExpr::var(x.clone());
    let z_expr = ChcExpr::var(z.clone());
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(7));

    let cases = vec![
        (ChcExpr::le(x_expr.clone(), z_expr.clone()), false, true),
        (ChcExpr::lt(x_expr.clone(), z_expr.clone()), true, true),
        (ChcExpr::ge(x_expr.clone(), z_expr.clone()), false, false),
        (ChcExpr::gt(x_expr, z_expr), true, false),
    ];

    for (atom, strict, expect_lower) in cases {
        let bound = mbp
            .extract_bound(&atom, &z, true)
            .expect("bound should be extractable for linear literal");
        match bound {
            BoundKind::Lower(coeff, term, is_strict) if expect_lower => {
                assert_eq!(coeff, 1, "coefficient should normalize to +1");
                assert_eq!(
                    mbp.eval_arith(&term, &model),
                    mbp.eval_arith(&ChcExpr::var(x.clone()), &model),
                    "term sign must flip"
                );
                assert_eq!(is_strict, strict);
            }
            BoundKind::Upper(coeff, term, is_strict) if !expect_lower => {
                assert_eq!(coeff, 1, "coefficient should normalize to +1");
                assert_eq!(
                    mbp.eval_arith(&term, &model),
                    mbp.eval_arith(&ChcExpr::var(x.clone()), &model),
                    "term sign must flip"
                );
                assert_eq!(is_strict, strict);
            }
            _ => panic!("unexpected bound classification"),
        }
    }
}

#[test]
fn extract_bound_negative_coeff_with_negated_literal_flips_term() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    // not(x <= z)  <=>  x > z  <=>  z < x
    let atom = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::var(z.clone()));
    let bound = mbp
        .extract_bound(&atom, &z, false)
        .expect("negated literal should still produce a bound");

    match bound {
        BoundKind::Upper(coeff, term, strict) => {
            assert_eq!(coeff, 1, "coefficient should normalize to +1");
            let mut model = FxHashMap::default();
            model.insert("x".to_string(), SmtValue::Int(11));
            assert_eq!(
                mbp.eval_arith(&term, &model),
                mbp.eval_arith(&ChcExpr::var(x), &model),
                "term sign must flip"
            );
            assert!(strict, "not(<=) becomes strict upper bound");
        }
        _ => panic!("unexpected bound classification"),
    }
}

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

#[test]
fn project_real_equality_negative_coeff_substitutes_correct_sign() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Real);
    let z = ChcVar::new("z", ChcSort::Real);

    // x = z introduces a negative z coefficient when isolating z.
    // factor_var on (x = z) for var z: lhs=x, rhs=z → coeff=-1, term=-x
    // extract_bound → BoundKind::Equality(-1, -x)
    // project_real_var should compute subst_term = neg(-x) = x, then
    // substituting z → x in (z > 0) yields x > 0.
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
        "projection of (x = z) ∧ (z > 0) should retain a > guard; got: {result:?}"
    );
}

/// Regression test for #3024: non-unit coefficient equality must substitute,
/// not just add a divisibility constraint and drop the variable.
#[test]
fn test_mbp_integer_nonunit_coeff_equality() {
    let mbp = Mbp::new();

    // Formula: 2*x = y AND x >= 0
    // When projecting out x, the correct result is:
    //   y mod 2 = 0 AND y/2 >= 0  (i.e. y >= 0 AND y is even)
    // Bug (before fix): only produced "y mod 2 = 0", dropping "x >= 0".
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // 2*x = y  (i.e.  2*x - y = 0)
    let two_x = ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x.clone()));
    let eq = ChcExpr::eq(two_x, ChcExpr::var(y));
    let ge = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(0));
    let formula = ChcExpr::and(eq, ge);

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));
    model.insert("y".to_string(), SmtValue::Int(6));

    let result = mbp.project(&formula, &[x], &model);

    // The variable x must be eliminated.
    let vars = result.vars();
    assert!(
        !vars.iter().any(|v| v.name == "x"),
        "projected formula must eliminate x; got: {result:?}"
    );

    // The result must have more than just a divisibility constraint:
    // it should also contain the substituted bound (y/2 >= 0 or equivalent).
    let conjuncts = result.collect_conjuncts();
    assert!(
        conjuncts.len() >= 2,
        "non-unit coeff equality must produce divisibility + substituted constraints; \
             got {} conjunct(s): {result:?}",
        conjuncts.len()
    );
}

/// Test BV projection: BV variables are substituted with model values.
///
/// Previously, BV vars fell through to project_single_var's `_ => without_var`
/// arm which silently dropped ALL constraints mentioning BV vars. Now BV vars
/// are substituted with model values before implicant extraction (same strategy
/// as Bool vars), producing sound under-approximations.
#[test]
fn test_mbp_bv_projection_substitutes_model_value() {
    let mbp = Mbp::new();

    // Formula: (= bv_x #x0A) AND (bvult bv_y bv_x)
    // bv_x and bv_y are 8-bit bitvectors
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(8));
    let bv_y = ChcVar::new("bv_y", ChcSort::BitVec(8));

    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(bv_x.clone()), ChcExpr::BitVec(0x0A, 8)),
        ChcExpr::Op(
            ChcOp::BvULt,
            vec![
                Arc::new(ChcExpr::var(bv_y.clone())),
                Arc::new(ChcExpr::var(bv_x.clone())),
            ],
        ),
    );

    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(0x0A, 8));
    model.insert("bv_y".to_string(), SmtValue::BitVec(0x05, 8));

    // Project out bv_x — should substitute with #x0A, leaving bvult(bv_y, #x0A)
    let result = mbp.project(&formula, std::slice::from_ref(&bv_x), &model);

    // bv_x must be eliminated
    assert!(
        !result.contains_var_name(&bv_x.name),
        "BV variable bv_x must be eliminated from projection result. Got: {result:?}"
    );

    // bv_y should remain (not being projected)
    assert!(
        result.contains_var_name(&bv_y.name),
        "bv_y should remain in formula. Got: {result:?}"
    );
}

/// Test BV projection with residuals: model value missing → BV var becomes residual
#[test]
fn test_mbp_bv_projection_residual_on_missing_model() {
    let mbp = Mbp::new();

    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(8));
    let formula = ChcExpr::eq(ChcExpr::var(bv_x.clone()), ChcExpr::BitVec(0xFF, 8));

    // Deliberately omit bv_x from model
    let model = FxHashMap::default();

    let result = mbp.project_with_residuals(&formula, std::slice::from_ref(&bv_x), &model);

    // bv_x should be reported as a residual since we can't substitute
    assert!(
        result.residual_vars.iter().any(|v| v == &bv_x),
        "missing BV model value must produce a residual. Got residuals: {:?}",
        result
            .residual_vars
            .iter()
            .map(|v| &v.name)
            .collect::<Vec<_>>()
    );
}

/// Test BV + Int mixed projection: BV substituted, Int projected via bounds
#[test]
fn test_mbp_mixed_bv_int_projection() {
    let mbp = Mbp::new();

    // Formula: (= bv_x #x05) AND (x > 0) AND (x < 10)
    // Project out both bv_x and x.
    // bv_x should be substituted with model value, x should be projected via bounds.
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(8));
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(bv_x.clone()), ChcExpr::BitVec(0x05, 8)),
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ),
        ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::var(y)),
    );

    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(0x05, 8));
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(10));

    let result = mbp.project(&formula, &[bv_x.clone(), x.clone()], &model);

    // Both bv_x and x must be eliminated
    assert!(
        !result.contains_var_name(&bv_x.name),
        "BV variable bv_x must be eliminated. Got: {result:?}"
    );
    assert!(
        !result.contains_var_name(&x.name),
        "Int variable x must be eliminated. Got: {result:?}"
    );
}

/// Regression test for #3024: real variable inequality resolution must
/// cross-multiply coefficients, not drop them.
#[test]
fn test_mbp_real_nonunit_coeff_inequality() {
    let mbp = Mbp::new();

    // Formula: 2*x >= y AND 3*x <= z   (x is Real)
    // Projecting out x: cross-multiply gives 3*y <= 2*z.
    // Bug (before fix): produced y <= z (coefficients discarded).
    let x = ChcVar::new("x", ChcSort::Real);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    // 2*x >= y  =>  2*x - y >= 0
    let two_x = ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x.clone()));
    let lower = ChcExpr::ge(two_x, ChcExpr::var(y));

    // 3*x <= z  =>  3*x - z <= 0
    let three_x = ChcExpr::mul(ChcExpr::Int(3), ChcExpr::var(x.clone()));
    let upper = ChcExpr::le(three_x, ChcExpr::var(z));

    let formula = ChcExpr::and(lower, upper);

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(2));
    model.insert("y".to_string(), SmtValue::Int(3));
    model.insert("z".to_string(), SmtValue::Int(7));

    let result = mbp.project(&formula, &[x], &model);

    // x must be eliminated.
    let vars = result.vars();
    assert!(
        !vars.iter().any(|v| v.name == "x"),
        "projected formula must eliminate x; got: {result:?}"
    );

    // The resolved constraint should be non-trivial (not just "true").
    assert_ne!(
        result,
        ChcExpr::Bool(true),
        "real non-unit coeff resolution must produce a non-trivial constraint"
    );
}

/// Regression test for W2:9 (ba4f077): model_value_expr must convert Real model
/// values to ChcExpr::Real(numer, denom). Before the fix, the Real arm was missing
/// and Real-sorted variables with model values fell through to None, causing
/// the MBQI fallback to use Real(0, 1) instead of the actual model value.
#[test]
fn test_model_value_expr_real_returns_correct_value() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let var = ChcVar::new("r", ChcSort::Real);
    let mut model = FxHashMap::default();

    // Model value: r = 3/7
    model.insert(
        "r".to_string(),
        SmtValue::Real(BigRational::new(BigInt::from(3), BigInt::from(7))),
    );

    let result = Mbp::model_value_expr(&var, &model);
    assert_eq!(
        result,
        Some(ChcExpr::Real(3, 7)),
        "model_value_expr must convert Real(3/7) to ChcExpr::Real(3, 7)"
    );
}

/// Verify model_value_expr_or_default returns Real(0, 1) when model is missing.
#[test]
fn test_model_value_expr_or_default_real_missing() {
    let var = ChcVar::new("r", ChcSort::Real);
    let model = FxHashMap::default();

    let result = Mbp::model_value_expr_or_default(&var, &model);
    assert_eq!(
        result,
        ChcExpr::Real(0, 1),
        "model_value_expr_or_default must return Real(0, 1) for missing Real var"
    );
}

/// Verify model_value_expr returns None on sort mismatch (Real var, Int value).
#[test]
fn test_model_value_expr_real_sort_mismatch_returns_none() {
    let var = ChcVar::new("r", ChcSort::Real);
    let mut model = FxHashMap::default();
    model.insert("r".to_string(), SmtValue::Int(42));

    let result = Mbp::model_value_expr(&var, &model);
    assert_eq!(
        result, None,
        "model_value_expr must return None on Real/Int sort mismatch"
    );
}

/// Regression test for #6095: invert_store_equality must produce distinct fresh
/// variable names for each store layer in a multi-store chain.
///
/// Before the fix, `indices.len()` was used as the suffix for ALL fresh variables,
/// causing name collisions (all got the same `__mbp_arr_a_2` name).
#[test]
fn test_invert_store_equality_distinct_fresh_vars_per_layer() {
    let mbp = Mbp::new();

    let idx_sort = ChcSort::Int;
    let val_sort = ChcSort::Int;
    let arr_sort = ChcSort::Array(Box::new(idx_sort), Box::new(val_sort));

    let a = ChcVar::new("a", arr_sort);
    let b = ChcVar::new("b", a.sort.clone());

    // store(store(a, 0, 10), 1, 20) = b
    let inner_store = ChcExpr::store(ChcExpr::var(a.clone()), ChcExpr::Int(0), ChcExpr::Int(10));
    let outer_store = ChcExpr::store(inner_store, ChcExpr::Int(1), ChcExpr::Int(20));
    let eq = ChcExpr::eq(outer_store, ChcExpr::var(b));

    // Model only needs scalar values — array variables aren't looked up by eval_generic.
    let model = FxHashMap::default();

    let result = mbp.project(&eq, std::slice::from_ref(&a), &model);

    // Collect all variable names starting with __mbp_arr_ from the result
    let vars = result.vars();
    let mbp_vars: Vec<&str> = vars
        .iter()
        .filter(|v| v.name.starts_with("__mbp_arr_"))
        .map(|v| v.name.as_str())
        .collect();

    // If there are MBP variables, they must all be distinct (no name collision).
    let unique_count = {
        let mut names: Vec<_> = mbp_vars.clone();
        names.sort_unstable();
        names.dedup();
        names.len()
    };
    assert_eq!(
        unique_count,
        mbp_vars.len(),
        "All __mbp_arr_ fresh variables must have unique names. Got: {mbp_vars:?}"
    );
}

/// Regression test for #6096: eval_smt_value must NOT return default values
/// for unevaluable indices, which would cause false select merges.
///
/// When two symbolic indices can't be evaluated under the model, they must
/// be treated as distinct (separate fresh variables), not merged via a
/// default value like Int(0).
#[test]
fn test_collect_selects_unevaluable_indices_not_merged() {
    let mbp = Mbp::new();

    let idx_sort = ChcSort::Int;
    let val_sort = ChcSort::Int;
    let arr_sort = ChcSort::Array(Box::new(idx_sort), Box::new(val_sort));

    let a = ChcVar::new("a", arr_sort);
    // Two symbolic indices that can't be evaluated (not in model)
    let p = ChcVar::new("p", ChcSort::Int);
    let q = ChcVar::new("q", ChcSort::Int);

    // select(a, p) > 0 AND select(a, q) > 0
    let sel_p = ChcExpr::select(ChcExpr::var(a.clone()), ChcExpr::var(p));
    let sel_q = ChcExpr::select(ChcExpr::var(a.clone()), ChcExpr::var(q));
    let formula = ChcExpr::and(
        ChcExpr::gt(sel_p, ChcExpr::Int(0)),
        ChcExpr::gt(sel_q, ChcExpr::Int(0)),
    );

    // Model has no values for p and q — their indices are unevaluable.
    // Array variables themselves are not looked up by eval_generic.
    let model = FxHashMap::default();

    let result = mbp.project(&formula, std::slice::from_ref(&a), &model);

    // Array variable `a` must be eliminated.
    let vars = result.vars();
    assert!(
        !vars.iter().any(|v| v.name == "a"),
        "Array variable 'a' must be eliminated. Got: {result:?}"
    );

    // The iterative MBP loop (#6047 Packet 2) projects fresh __mbp_sel_*
    // variables away. One-sided bounds (> 0 only) are eliminated by FM
    // projection (sound: ∃x. x>0 is true). Fresh vars should not survive.
    // The Ackermannization disequality constraint between indices should
    // remain since p and q are not projected.
    let sel_vars: Vec<&str> = vars
        .iter()
        .filter(|v| v.name.starts_with("__mbp_sel_"))
        .map(|v| v.name.as_str())
        .collect();
    assert!(
        sel_vars.is_empty(),
        "Iterative loop should project all fresh select vars. Remaining: {sel_vars:?}"
    );
}

/// Regression test: syntactically identical unevaluable indices should still
/// merge (share one fresh variable), avoiding a tautological `ne(x, x)` falsity
/// in Ackermannization.
#[test]
fn test_collect_selects_identical_unevaluable_indices_merge() {
    let mbp = Mbp::new();

    let idx_sort = ChcSort::Int;
    let val_sort = ChcSort::Int;
    let arr_sort = ChcSort::Array(Box::new(idx_sort), Box::new(val_sort));

    let a = ChcVar::new("a", arr_sort);
    let p = ChcVar::new("p", ChcSort::Int);

    // select(a, p) > 0 AND select(a, p) < 10
    // Same index `p` appears twice — should merge into ONE fresh variable.
    let sel1 = ChcExpr::select(ChcExpr::var(a.clone()), ChcExpr::var(p.clone()));
    let sel2 = ChcExpr::select(ChcExpr::var(a.clone()), ChcExpr::var(p));
    let formula = ChcExpr::and(
        ChcExpr::gt(sel1, ChcExpr::Int(0)),
        ChcExpr::lt(sel2, ChcExpr::Int(10)),
    );

    // p is not in model — index is unevaluable
    let model = FxHashMap::default();

    let result = mbp.project(&formula, std::slice::from_ref(&a), &model);

    // Array variable `a` must be eliminated.
    let vars = result.vars();
    assert!(
        !vars.iter().any(|v| v.name == "a"),
        "Array variable 'a' must be eliminated. Got: {result:?}"
    );

    // The iterative MBP loop (#6047 Packet 2) projects the merged fresh
    // variable via FM: __mbp_sel_a_0 > 0 AND __mbp_sel_a_0 < 10 resolves
    // to 2 <= 10 (tautology, dropped). Fresh vars should not survive.
    let sel_vars: Vec<&str> = vars
        .iter()
        .filter(|v| v.name.starts_with("__mbp_sel_"))
        .map(|v| v.name.as_str())
        .collect();
    assert!(
        sel_vars.is_empty(),
        "Iterative loop should project merged fresh select var. Remaining: {sel_vars:?}"
    );

    // Result must NOT contain `ne(p, p)` — that would make the formula unsatisfiable.
    let result_str = format!("{result:?}");
    assert!(
        !result_str.contains("Ne(Var("),
        "Ackermannization should not produce any Ne constraint for merged identical indices, \
         but result contains: {result_str}"
    );
}
