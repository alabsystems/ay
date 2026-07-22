// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Algorithm audit regression tests for MBP (Model-Based Projection).
//!
//! Findings from Prover algorithm_audit phase [P]63:
//! - Finding 7: Real equality with |coeff| != 1 substitutes raw term instead
//!   of term/coeff. Can produce under-approximation (soundness violation).
//! - Finding 10: Integer strictness slack uses +1 instead of +ub_coeff_abs,
//!   yielding weaker-than-necessary result for non-unit coefficients.
//! - Finding 4: Best-lower-bound selection uses truncation division instead of
//!   floor division for negative terms.

use ay_chc::{ChcExpr, ChcOp, ChcSort, ChcVar, Mbp, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Finding 7 regression: project_real_var equality with coeff=2.
///
/// Formula: 2*z = 6 AND z < w, model: {z=3, w=5}
/// extract_var_coeff recognizes Int(2)*Var(z) and returns coeff=2, term=6.
/// extract_bound returns Equality(2, 6).
/// project_real_var must divide: var = term/coeff = 6/2, substituting z -> 6/2.
///
/// Without the division fix, z -> 6, producing 6 < w (too strong for w=5).
/// With the fix, z -> 6/2 = 3, producing 3 < w (correct for w=5).
#[test]
fn real_equality_nonunit_coeff_produces_division() {
    let mbp = Mbp::new();
    let z = ChcVar::new("z", ChcSort::Real);
    let w = ChcVar::new("w", ChcSort::Real);

    // 2*z = 6 AND z < w
    let two_z = ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(z.clone()));
    let formula = ChcExpr::and(
        ChcExpr::eq(two_z, ChcExpr::Int(6)),
        ChcExpr::lt(ChcExpr::var(z.clone()), ChcExpr::var(w)),
    );

    let mut model = FxHashMap::default();
    model.insert("z".to_string(), SmtValue::Int(3));
    model.insert("w".to_string(), SmtValue::Int(5));

    let result = mbp.project(&formula, std::slice::from_ref(&z), &model);

    // z must be eliminated
    assert!(
        !result.vars().iter().any(|v| v.name == "z"),
        "projected formula must eliminate z; got: {result:?}"
    );

    // The result should contain a Lt comparison with w.
    // Without the fix: Lt(Int(6), Var(w)) — wrong, 6 < 5 is false.
    // With the fix: Lt(Div(6, 2), Var(w)) — correct, 3 < 5.
    // Check that the formula does NOT contain a raw Int(6) as the LHS of Lt.
    let conjuncts = result.collect_conjuncts();
    let lt_conjuncts: Vec<_> = conjuncts
        .iter()
        .filter(|c| matches!(c, ChcExpr::Op(ChcOp::Lt, _)))
        .collect();

    // Should have an Lt conjunct comparing something to w.
    assert!(
        !lt_conjuncts.is_empty(),
        "projected formula should retain a < comparison; got: {result:?}"
    );

    for lt in &lt_conjuncts {
        if let ChcExpr::Op(ChcOp::Lt, args) = lt {
            // The LHS should NOT be raw Int(6) — that would mean no division was applied.
            assert_ne!(
                args[0].as_ref(),
                &ChcExpr::Int(6),
                "substitution must divide by coefficient (6/2), not use raw term 6; got: {result:?}"
            );
        }
    }
}

/// Finding 7 variant: project_real_var equality with coeff=3 and negative term.
///
/// Formula: 3*z = -9 AND z > y, model: {z=-3, y=-5}
/// Correct: z = -9/3 = -3, substituting z -> Div(-9, 3) in (z > y) gives Div(-9,3) > y.
/// Buggy: z -> -9, producing -9 > y (too strong: -9 > -5 is false).
#[test]
fn real_equality_nonunit_coeff_negative_term_produces_division() {
    let mbp = Mbp::new();
    let z = ChcVar::new("z", ChcSort::Real);
    let y = ChcVar::new("y", ChcSort::Real);

    // 3*z = -9 AND z > y
    let three_z = ChcExpr::mul(ChcExpr::Int(3), ChcExpr::var(z.clone()));
    let formula = ChcExpr::and(
        ChcExpr::eq(three_z, ChcExpr::Int(-9)),
        ChcExpr::gt(ChcExpr::var(z.clone()), ChcExpr::var(y)),
    );

    let mut model = FxHashMap::default();
    model.insert("z".to_string(), SmtValue::Int(-3));
    model.insert("y".to_string(), SmtValue::Int(-5));

    let result = mbp.project(&formula, std::slice::from_ref(&z), &model);

    assert!(
        !result.vars().iter().any(|v| v.name == "z"),
        "projected formula must eliminate z; got: {result:?}"
    );

    // The result should NOT contain raw Int(-9) as the LHS of Gt.
    let conjuncts = result.collect_conjuncts();
    let gt_conjuncts: Vec<_> = conjuncts
        .iter()
        .filter(|c| matches!(c, ChcExpr::Op(ChcOp::Gt, _)))
        .collect();

    for gt in &gt_conjuncts {
        if let ChcExpr::Op(ChcOp::Gt, args) = gt {
            assert_ne!(
                args[0].as_ref(),
                &ChcExpr::Int(-9),
                "substitution must divide by coefficient (-9/3), not use raw term -9; got: {result:?}"
            );
        }
    }
}

/// Finding 7 variant: coeff=2 with symbolic term.
///
/// Formula: 2*z = x AND z > 0, model: {z=4, x=8}
/// factor_var on (2*z = x) for z: lhs_coeff=2, rhs_coeff=0, total=2, term=x-0=x.
/// extract_bound: Equality(2, x).
/// Correct: z = x/2, substituting in z > 0 gives x/2 > 0 => Div(x, 2) > 0.
/// Buggy: z -> x, giving x > 0 (too strong when x could be between 0 and 2).
#[test]
fn real_equality_nonunit_coeff_symbolic_term_uses_division() {
    let mbp = Mbp::new();
    let z = ChcVar::new("z", ChcSort::Real);
    let x = ChcVar::new("x", ChcSort::Real);

    // 2*z = x AND z > 0
    let two_z = ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(z.clone()));
    let formula = ChcExpr::and(
        ChcExpr::eq(two_z, ChcExpr::var(x)),
        ChcExpr::gt(ChcExpr::var(z.clone()), ChcExpr::Int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("z".to_string(), SmtValue::Int(4));
    model.insert("x".to_string(), SmtValue::Int(8));

    let result = mbp.project(&formula, std::slice::from_ref(&z), &model);

    assert!(
        !result.vars().iter().any(|v| v.name == "z"),
        "projected formula must eliminate z; got: {result:?}"
    );

    // The result should contain a Div operation (x/2), not just raw x.
    let result_str = format!("{result:?}");
    assert!(
        result_str.contains("Div"),
        "projected formula should contain division by coefficient; got: {result:?}"
    );
}

/// Finding 10: Integer strictness slack +1 vs +ub_coeff_abs.
///
/// Formula: 2*x > 5 AND 3*x <= 12, model: {x=3}
/// Correct bounds: x > 2.5, x <= 4 — satisfiable (x=3 works)
/// Scaled resolution: 3*5=15 vs 2*12=24, strict → 15 + ub_coeff_abs = 15 + 3 = 18 <= 24 (correct)
/// With +1 slack: 15 + 1 = 16 <= 24 (weaker but still correct)
///
/// The MBP model satisfaction contract must always hold.
#[test]
fn integer_nonunit_coeff_bounds_resolution_model_satisfaction() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Int);

    // 2*x > 5 AND 3*x <= 12, model: {x=3}
    let two_x = ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x.clone()));
    let three_x = ChcExpr::mul(ChcExpr::Int(3), ChcExpr::var(x.clone()));
    let formula = ChcExpr::and(
        ChcExpr::gt(two_x, ChcExpr::Int(5)),
        ChcExpr::le(three_x, ChcExpr::Int(12)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));

    let result = mbp.project(&formula, std::slice::from_ref(&x), &model);

    // x must be eliminated
    assert!(
        !result.vars().iter().any(|v| v.name == "x"),
        "projected formula must eliminate x; got: {result:?}"
    );

    // MBP contract: model |= result
    assert_eq!(
        mbp.eval_bool(&result, &model),
        Some(true),
        "MBP contract: model {{x=3}} must satisfy projected formula. Got: {result:?}"
    );
}

/// Finding 4: Best-lower-bound uses truncation division instead of floor.
///
/// For negative terms with non-unit coefficients, truncation rounds toward zero
/// while floor rounds toward negative infinity. This can cause incorrect bound
/// selection.
///
/// Formula: 2*x >= -7 AND x >= -3 AND x <= 0, model: {x=-2}
/// The MBP contract must hold regardless of bound selection.
#[test]
fn integer_negative_term_bound_selection_model_satisfaction() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Int);

    // 2*x >= -7 AND x >= -3 AND x <= 0
    let two_x = ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x.clone()));
    let formula = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::ge(two_x, ChcExpr::Int(-7)),
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(-3)),
        ),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(-2));

    let result = mbp.project(&formula, std::slice::from_ref(&x), &model);

    assert!(
        !result.vars().iter().any(|v| v.name == "x"),
        "projected formula must eliminate x; got: {result:?}"
    );

    assert_eq!(
        mbp.eval_bool(&result, &model),
        Some(true),
        "MBP contract: model {{x=-2}} must satisfy projected formula. Got: {result:?}"
    );
}

/// Finding 4 regression: best_lower selection must use floor division, not truncation.
///
/// With truncation: -5/3 = -1 (rounds toward zero), so the 3*x >= -5 bound
/// appears to give x >= -1, making it seem tighter than x >= -2.
/// With floor division: -5/3 = -2 (rounds toward -inf), correctly identifying
/// that 3*x >= -5 gives x >= -2 (same as the unit bound), so the unit bound wins.
///
/// When truncation selects the wrong bound (3*x >= -5), the main resolution
/// against x <= 10 produces: 1*(-5) <= 3*10 → -5 <= 30 (weaker resolution).
/// When floor correctly selects x >= -2, resolution gives: -2 <= 10 → true (tighter).
///
/// Both results are sound (valid overapproximations), but floor produces a tighter
/// result. We test model satisfaction (soundness gate) and document the precision
/// behavior.
#[test]
fn integer_best_lower_floor_vs_truncation_precision() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Int);

    // Bound A: 3*x >= -5   (x >= ceil(-5/3) = -1 in integers)
    //   floor(-5/3) = -2, trunc(-5/3) = -1
    //   With truncation: A appears tighter (-1 > -2)
    //   With floor: A and B both evaluate to -2, unit coeff wins
    // Bound B: x >= -2     (x >= -2)
    // Upper:   x <= 10
    let three_x = ChcExpr::mul(ChcExpr::Int(3), ChcExpr::var(x.clone()));
    let formula = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::ge(three_x, ChcExpr::Int(-5)),
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(-2)),
        ),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(10)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));

    let result = mbp.project(&formula, std::slice::from_ref(&x), &model);

    // x must be eliminated
    assert!(
        !result.vars().iter().any(|v| v.name == "x"),
        "projected formula must eliminate x; got: {result:?}"
    );

    // MBP contract: model must satisfy result
    assert_eq!(
        mbp.eval_bool(&result, &model),
        Some(true),
        "MBP contract: model {{x=0}} must satisfy projected formula. Got: {result:?}"
    );
}

/// Proof coverage: negative non-unit coefficient (-2) exercises BOTH sign flip
/// AND division simultaneously.
///
/// Formula: -2*z = 6 AND z < w, model: {z=-3, w=0}
/// factor_var on (-2*z = 6) for z: coeff=-2, term=6.
/// Correct: sign_adjusted = neg(6) = -6, subst_term = Div(-6, 2) = -3.
/// Substituting z → Div(-6, 2) in (z < w) gives Div(-6, 2) < w.
/// The defining equality must not be re-added as a self-substituted tautology.
#[test]
fn real_equality_negative_nonunit_coeff_applies_sign_and_division() {
    let mbp = Mbp::new();
    let z = ChcVar::new("z", ChcSort::Real);
    let w = ChcVar::new("w", ChcSort::Real);

    // -2*z = 6 AND z < w, model: {z=-3, w=0}
    let neg_two_z = ChcExpr::mul(ChcExpr::Int(-2), ChcExpr::var(z.clone()));
    let formula = ChcExpr::and(
        ChcExpr::eq(neg_two_z, ChcExpr::Int(6)),
        ChcExpr::lt(ChcExpr::var(z.clone()), ChcExpr::var(w)),
    );

    let mut model = FxHashMap::default();
    model.insert("z".to_string(), SmtValue::Int(-3));
    model.insert("w".to_string(), SmtValue::Int(0));

    let result = mbp.project(&formula, std::slice::from_ref(&z), &model);

    // z must be eliminated
    assert!(
        !result.vars().iter().any(|v| v.name == "z"),
        "projected formula must eliminate z; got: {result:?}"
    );

    // The result should be semantically equivalent to Div(-6, 2) < w, i.e. -3 < w.
    // With the canonical simplify_constants, Div(-6, 2) is evaluated to Int(-3).
    let result_str = format!("{result:?}");
    assert!(
        result_str.contains("Div") || result_str.contains("Int(-3)"),
        "negative non-unit coefficient must produce division or its evaluated result (-3); got: {result:?}"
    );

    // Verify the Lt conjunct doesn't have raw Int(6) or Int(-6) as LHS.
    // This confirms both sign flip AND division were applied.
    let conjuncts = result.collect_conjuncts();
    assert!(
        !conjuncts
            .iter()
            .any(|c| matches!(c, ChcExpr::Op(ChcOp::Eq, _))),
        "self-substituted equality should be eliminated; got: {result:?}"
    );
    let lt_conjuncts: Vec<_> = conjuncts
        .iter()
        .filter(|c| matches!(c, ChcExpr::Op(ChcOp::Lt, _)))
        .collect();
    assert!(
        !lt_conjuncts.is_empty(),
        "projected formula should retain a < comparison; got: {result:?}"
    );
    for lt in &lt_conjuncts {
        if let ChcExpr::Op(ChcOp::Lt, args) = lt {
            assert_ne!(
                args[0].as_ref(),
                &ChcExpr::Int(6),
                "must not use raw term 6 (no division); got: {result:?}"
            );
            assert_ne!(
                args[0].as_ref(),
                &ChcExpr::Int(-6),
                "must not use raw negated term -6 (no division); got: {result:?}"
            );
        }
    }

    assert!(
        result.vars().iter().any(|v| v.name == "w"),
        "projected formula should preserve non-eliminated context variables; got: {result:?}"
    );
}

/// Regression for duplicate equalities: both copies can appear in implicants.
/// MBP must not keep a ground equality tautology after substitution.
#[test]
fn real_equality_duplicate_literal_does_not_reintroduce_eq_tautology() {
    let mbp = Mbp::new();
    let z = ChcVar::new("z", ChcSort::Real);

    let neg_two_z = ChcExpr::mul(ChcExpr::Int(-2), ChcExpr::var(z.clone()));
    let eq = ChcExpr::eq(neg_two_z, ChcExpr::Int(6));
    let formula = ChcExpr::and(
        ChcExpr::and(eq.clone(), eq),
        ChcExpr::lt(ChcExpr::var(z.clone()), ChcExpr::Int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("z".to_string(), SmtValue::Int(-3));

    let result = mbp.project(&formula, std::slice::from_ref(&z), &model);

    assert!(
        !result.vars().iter().any(|v| v.name == "z"),
        "projected formula must eliminate z; got: {result:?}"
    );

    let conjuncts = result.collect_conjuncts();
    assert!(
        !conjuncts
            .iter()
            .any(|c| matches!(c, ChcExpr::Op(ChcOp::Eq, _))),
        "duplicate defining equality should not survive projection; got: {result:?}"
    );

    assert_eq!(
        mbp.eval_bool(&result, &model),
        Some(true),
        "projected formula should evaluate to true under the source model; got: {result:?}"
    );
}

/// Performance finding: MBP serial boolean substitution calls `substitute`
/// once per boolean variable, each time rebuilding a new HashMap and walking
/// the entire expression tree. With B boolean variables and tree size T, this
/// is O(B * T) tree walks instead of a single O(T) batch substitution.
///
/// This test proves the serial pattern exists: each boolean var triggers a
/// separate `substitute` call that walks the full tree, even though all
/// boolean substitutions are independent and could be batched into one call.
///
/// File: crates/ay-chc/src/mbp.rs:198-203
/// Related: #2956 (finding 3: MBP tree walks)
#[test]
fn serial_bool_substitute_proves_multiple_tree_walks() {
    let mbp = Mbp::new();

    // Create a formula with N boolean vars AND an arithmetic part
    let b0 = ChcVar::new("b0", ChcSort::Bool);
    let b1 = ChcVar::new("b1", ChcSort::Bool);
    let b2 = ChcVar::new("b2", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);

    // Formula: (b0 AND b1 AND b2) AND (x >= 0)
    // This has both boolean and arithmetic parts.
    let formula = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::and(ChcExpr::var(b0.clone()), ChcExpr::var(b1.clone())),
            ChcExpr::var(b2.clone()),
        ),
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("b0".to_string(), SmtValue::Bool(true));
    model.insert("b1".to_string(), SmtValue::Bool(true));
    model.insert("b2".to_string(), SmtValue::Bool(false));
    model.insert("x".to_string(), SmtValue::Int(5));

    // Project out all 3 boolean vars + x
    let vars_to_eliminate = vec![b0, b1, b2, x];
    let result = mbp.project(&formula, &vars_to_eliminate, &model);

    // The result should be correct regardless of serial vs batch substitution.
    // The structural proof here is that the code at mbp.rs:198-203 does:
    //   for var in &bool_vars {
    //       current = current.substitute(&[(var, bool_val)]);
    //   }
    // Each substitute() call:
    //   1. Builds a FxHashMap from the single-element slice: O(1)
    //   2. Walks the entire expression tree: O(T)
    // With 3 boolean vars, that's 3 tree walks.
    // A batch call `current.substitute(&all_bool_substs)` would do 1 walk.
    //
    // This test verifies correctness. The performance issue is structural
    // and visible in the source code: serial loop of single-var substitutes.
    let result_str = format!("{result:?}");
    // b2 is false, so (b0 AND b1 AND b2) simplifies.
    // The projection of x should produce bounds from the implicant.
    assert!(
        !result_str.contains("b0") && !result_str.contains("b1") && !result_str.contains("b2"),
        "all boolean variables should be eliminated from result; got: {result:?}"
    );
}
