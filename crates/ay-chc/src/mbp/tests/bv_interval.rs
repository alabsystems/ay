// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================================
// Packet 3: BV MBP interval elimination tests (#7015)
// ============================================================================

/// BV MBP: equality triggers substitution.
/// Project bv_x from `(= bv_x 42) AND bvult(bv_y, bv_x)`.
/// Result: `bvult(bv_y, 42)` (equality substitutes bv_x with 42).
#[test]
fn test_bv_mbp_equality_substitution() {
    let mbp = Mbp::new();
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(32));
    let bv_y = ChcVar::new("bv_y", ChcSort::BitVec(32));

    // (= bv_x 42) AND bvult(bv_y, bv_x)
    let eq = ChcExpr::eq(ChcExpr::var(bv_x.clone()), ChcExpr::BitVec(42, 32));
    let lt = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::var(bv_y)),
            Arc::new(ChcExpr::var(bv_x.clone())),
        ],
    );
    let formula = ChcExpr::and(eq, lt);

    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(42, 32));
    model.insert("bv_y".to_string(), SmtValue::BitVec(10, 32));

    let result = mbp.project(&formula, &[bv_x], &model);
    let result_str = format!("{result:?}");

    // bv_x should be eliminated
    assert!(
        !result.contains_var_name("bv_x"),
        "bv_x should be eliminated by equality substitution. Got: {result_str}"
    );
    // bv_y should remain
    assert!(
        result.contains_var_name("bv_y"),
        "bv_y should remain. Got: {result_str}"
    );
}

/// BV MBP: interval resolution eliminates variable.
/// Project bv_x from `bvuge(bv_x, 10) AND bvule(bv_x, 50)`.
/// Result: `bvule(10, 50)` or `true` (FM-style resolution).
#[test]
fn test_bv_mbp_interval_resolution() {
    let mbp = Mbp::new();
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(8));

    // bvuge(bv_x, 10) AND bvule(bv_x, 50)
    let lb = ChcExpr::Op(
        ChcOp::BvUGe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::BitVec(10, 8)),
        ],
    );
    let ub = ChcExpr::Op(
        ChcOp::BvULe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::BitVec(50, 8)),
        ],
    );
    let formula = ChcExpr::and(lb, ub);

    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(30, 8));

    let result = mbp.project(&formula, &[bv_x], &model);
    let result_str = format!("{result:?}");

    // bv_x should be eliminated
    assert!(
        !result.contains_var_name("bv_x"),
        "bv_x should be eliminated by interval resolution. Got: {result_str}"
    );
}

#[test]
fn test_bv_mbp_wide_interval_falls_back_to_exact_model_substitution() {
    let mbp = Mbp::new();
    let width = 129;
    let x = ChcVar::new("wide_x", ChcSort::BitVec(width));
    let base = num_bigint::BigUint::from(1_u8) << 128;
    let lower = ChcExpr::bitvec_from_biguint(&base, width).expect("bounded BV129 literal");
    let upper_value = &base + num_bigint::BigUint::from(10_u8);
    let upper = ChcExpr::bitvec_from_biguint(&upper_value, width).expect("bounded BV129 literal");
    let formula = ChcExpr::and(
        ChcExpr::Op(
            ChcOp::BvUGe,
            vec![Arc::new(ChcExpr::var(x.clone())), Arc::new(lower)],
        ),
        ChcExpr::Op(
            ChcOp::BvULe,
            vec![Arc::new(ChcExpr::var(x.clone())), Arc::new(upper)],
        ),
    );
    let mut model = FxHashMap::default();
    model.insert(
        x.name.clone(),
        SmtValue::bitvec_from_biguint(base + num_bigint::BigUint::from(5_u8), width),
    );

    let projected = mbp.project(&formula, &[x], &model);
    assert!(
        !projected.contains_var_name("wide_x"),
        "wide interval projection must use the exact model literal fallback: {projected:?}"
    );
}

/// BV MBP: one-sided bound with unhandled literal.
/// Project bv_x from `bvule(bv_x, 50) AND bvult(bv_y, bv_x)`.
/// Upper bound on bv_x; `bvult(bv_y, bv_x)` gives lower bound `bv_x >_u bv_y`.
#[test]
fn test_bv_mbp_one_sided_bound() {
    let mbp = Mbp::new();
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(8));
    let bv_y = ChcVar::new("bv_y", ChcSort::BitVec(8));

    // bvule(bv_x, 50) AND bvult(bv_y, bv_x)
    let ub = ChcExpr::Op(
        ChcOp::BvULe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::BitVec(50, 8)),
        ],
    );
    let lt = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::var(bv_y)),
            Arc::new(ChcExpr::var(bv_x.clone())),
        ],
    );
    let formula = ChcExpr::and(ub, lt);

    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(30, 8));
    model.insert("bv_y".to_string(), SmtValue::BitVec(10, 8));

    let result = mbp.project(&formula, &[bv_x], &model);
    let result_str = format!("{result:?}");

    // bv_x should be eliminated
    assert!(
        !result.contains_var_name("bv_x"),
        "bv_x should be eliminated. Got: {result_str}"
    );
    // bv_y should remain
    assert!(
        result.contains_var_name("bv_y"),
        "bv_y should remain. Got: {result_str}"
    );
}

/// BV MBP: negated comparison correctly flips BV ops.
/// Project bv_x from `NOT bvule(bv_x, 50)` which is `bvugt(bv_x, 50)`.
/// Combined with an upper bound, this produces interval resolution.
#[test]
fn test_bv_mbp_negated_comparison() {
    let mbp = Mbp::new();
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(8));

    // NOT bvule(bv_x, 50) [= bvugt(bv_x, 50)] AND bvule(bv_x, 100)
    // After negation: lower bound bv_x >_u 50, upper bound bv_x <=_u 100
    let neg_ule = ChcExpr::not(ChcExpr::Op(
        ChcOp::BvULe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::BitVec(50, 8)),
        ],
    ));
    let ub = ChcExpr::Op(
        ChcOp::BvULe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::BitVec(100, 8)),
        ],
    );
    let formula = ChcExpr::and(neg_ule, ub);

    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(75, 8));

    let result = mbp.project(&formula, &[bv_x], &model);
    let result_str = format!("{result:?}");

    // bv_x should be eliminated
    assert!(
        !result.contains_var_name("bv_x"),
        "bv_x should be eliminated via negated BV comparison. Got: {result_str}"
    );
}

/// BV MBP: complex expression falls back to model-value substitution.
/// `bvadd(bv_x, bv_y) = 100` has no direct bound on bv_x — falls back.
#[test]
fn test_bv_mbp_fallback_to_model_value() {
    let mbp = Mbp::new();
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(32));
    let bv_y = ChcVar::new("bv_y", ChcSort::BitVec(32));

    // bvadd(bv_x, bv_y) = 100 — no simple bound on bv_x
    let add = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::var(bv_y)),
        ],
    );
    let eq = ChcExpr::eq(add, ChcExpr::BitVec(100, 32));

    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(60, 32));
    model.insert("bv_y".to_string(), SmtValue::BitVec(40, 32));

    let result = mbp.project(&eq, &[bv_x], &model);
    let result_str = format!("{result:?}");

    // bv_x should be eliminated (via model-value substitution fallback)
    assert!(
        !result.contains_var_name("bv_x"),
        "bv_x should be eliminated by model-value fallback. Got: {result_str}"
    );
    // bv_y should remain
    assert!(
        result.contains_var_name("bv_y"),
        "bv_y should remain. Got: {result_str}"
    );
}

#[test]
fn test_implicant_preserves_dt_tester_funcapp_atom() {
    let mbp = Mbp::new();

    // Construct a Bool-returning FuncApp simulating a DT tester: is-Red(x)
    let x = ChcVar::new("x", ChcSort::Int);
    let tester = ChcExpr::FuncApp(
        "is-Red".to_string(),
        ChcSort::Bool,
        vec![Arc::new(ChcExpr::var(x.clone()))],
    );
    // Formula: is-Red(x) AND x >= 0
    let formula = ChcExpr::and(tester, ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0)));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(1));

    let implicant = mbp.get_implicant(&formula, &model);

    // The tester FuncApp should be preserved as a positive atom in the implicant.
    // Before the fix, FuncApp hit the `_ => false` arm of is_atom and was dropped.
    assert!(
        implicant.iter().any(|lit| lit.positive
            && matches!(&lit.atom, ChcExpr::FuncApp(name, ChcSort::Bool, _) if name == "is-Red")),
        "DT tester FuncApp should be preserved as atom in implicant, got: {:?}",
        implicant
            .iter()
            .map(|l| l.atom.to_string())
            .collect::<Vec<_>>()
    );
    // The >= comparison should also be preserved
    assert!(
        implicant.len() >= 2,
        "implicant should have at least 2 literals (tester + comparison), got {}",
        implicant.len()
    );
}

#[test]
fn test_is_atom_rejects_non_bool_funcapp() {
    let mbp = Mbp::new();

    // Int-returning FuncApp should NOT be an atom
    let x = ChcVar::new("x", ChcSort::Int);
    let int_func = ChcExpr::FuncApp(
        "f".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::var(x))],
    );
    assert!(
        !mbp.is_atom(&int_func),
        "Int-returning FuncApp should not be an atom"
    );

    // Bool-returning FuncApp SHOULD be an atom
    let y = ChcVar::new("y", ChcSort::Int);
    let bool_func = ChcExpr::FuncApp(
        "is-Ctor".to_string(),
        ChcSort::Bool,
        vec![Arc::new(ChcExpr::var(y))],
    );
    assert!(
        mbp.is_atom(&bool_func),
        "Bool-returning FuncApp should be an atom"
    );
}

/// Test eval_generic: DT selector application evaluates correctly (#7045 Gap A).
/// (val x) where x = Some(42) should return Int(42).
#[test]
fn test_eval_generic_dt_selector_application() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", option_int_sort());

    // sel = (val x) → FuncApp("val", Int, [Var(x)])
    let selector_app = ChcExpr::FuncApp(
        "val".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Var(x))],
    );

    let mut model = FxHashMap::default();
    model.insert(
        "x".to_string(),
        SmtValue::Datatype("Some".to_string(), vec![SmtValue::Int(42)]),
    );

    let result = mbp.eval_generic(&selector_app, &model);
    assert_eq!(result, Some(SmtValue::Int(42)));
}

/// Test eval_generic: DT selector on pair extracts second field (#7045 Gap A).
/// (snd p) where p = mkpair(10, 20) should return Int(20).
#[test]
fn test_eval_generic_dt_selector_pair_snd() {
    let mbp = Mbp::new();
    let p = ChcVar::new("p", pair_int_sort());

    let selector_app = ChcExpr::FuncApp(
        "snd".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Var(p))],
    );

    let mut model = FxHashMap::default();
    model.insert(
        "p".to_string(),
        SmtValue::Datatype(
            "mkpair".to_string(),
            vec![SmtValue::Int(10), SmtValue::Int(20)],
        ),
    );

    let result = mbp.eval_generic(&selector_app, &model);
    assert_eq!(result, Some(SmtValue::Int(20)));
}

/// Test eval_generic: DT selector returns None for wrong constructor (#7045 Gap A).
/// (val x) where x = None should return None (no selector match).
#[test]
fn test_eval_generic_dt_selector_wrong_constructor() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", option_int_sort());

    let selector_app = ChcExpr::FuncApp(
        "val".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Var(x))],
    );

    let mut model = FxHashMap::default();
    model.insert(
        "x".to_string(),
        SmtValue::Datatype("None".to_string(), vec![]),
    );

    // "val" is a selector of "Some", not "None" — should return None
    let result = mbp.eval_generic(&selector_app, &model);
    assert_eq!(result, None);
}

/// Test eval_generic: DT constructor application evaluates to Datatype value (#7045).
/// (mkpair 10 20) should evaluate to Datatype("mkpair", [Int(10), Int(20)]).
#[test]
fn test_eval_generic_dt_constructor_application() {
    let mbp = Mbp::new();

    let ctor_app = ChcExpr::FuncApp(
        "mkpair".to_string(),
        pair_int_sort(),
        vec![Arc::new(ChcExpr::Int(10)), Arc::new(ChcExpr::Int(20))],
    );

    let model = FxHashMap::default();
    let result = mbp.eval_generic(&ctor_app, &model);
    assert_eq!(
        result,
        Some(SmtValue::Datatype(
            "mkpair".to_string(),
            vec![SmtValue::Int(10), SmtValue::Int(20)]
        ))
    );
}

/// Test eval_bool: DT tester on non-variable expression (#7045 Gap A).
/// is-mkpair(mkpair(1, 2)) should evaluate to true.
#[test]
fn test_eval_bool_dt_tester_on_constructor_expr() {
    let mbp = Mbp::new();

    let inner = ChcExpr::FuncApp(
        "mkpair".to_string(),
        pair_int_sort(),
        vec![Arc::new(ChcExpr::Int(1)), Arc::new(ChcExpr::Int(2))],
    );
    let tester = ChcExpr::FuncApp(
        "is-mkpair".to_string(),
        ChcSort::Bool,
        vec![Arc::new(inner)],
    );

    let model = FxHashMap::default();
    let result = mbp.eval_bool(&tester, &model);
    assert_eq!(result, Some(true));
}

/// Test eval_bool: DT tester on non-variable expr returns false for wrong ctor (#7045).
/// is-None(mkpair(1, 2)) should evaluate to false.
#[test]
fn test_eval_bool_dt_tester_on_nonvar_wrong_ctor() {
    let mbp = Mbp::new();

    let inner = ChcExpr::FuncApp(
        "mkpair".to_string(),
        pair_int_sort(),
        vec![Arc::new(ChcExpr::Int(1)), Arc::new(ChcExpr::Int(2))],
    );
    let tester = ChcExpr::FuncApp("is-None".to_string(), ChcSort::Bool, vec![Arc::new(inner)]);

    let model = FxHashMap::default();
    let result = mbp.eval_bool(&tester, &model);
    assert_eq!(result, Some(false));
}

/// Test eval_bool: equality on selector expressions (#7045 end-to-end).
/// (= (val x) 42) where x = Some(42) should be true.
#[test]
fn test_eval_bool_eq_selector_application() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", option_int_sort());

    let sel_app = ChcExpr::FuncApp(
        "val".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Var(x))],
    );
    let eq_expr = ChcExpr::Op(
        ChcOp::Eq,
        vec![Arc::new(sel_app), Arc::new(ChcExpr::Int(42))],
    );

    let mut model = FxHashMap::default();
    model.insert(
        "x".to_string(),
        SmtValue::Datatype("Some".to_string(), vec![SmtValue::Int(42)]),
    );

    assert_eq!(mbp.eval_bool(&eq_expr, &model), Some(true));
}

/// Test eval_bool: inequality on selector expressions (#7045 end-to-end).
/// (= (val x) 99) where x = Some(42) should be false.
#[test]
fn test_eval_bool_ne_selector_application() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", option_int_sort());

    let sel_app = ChcExpr::FuncApp(
        "val".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Var(x))],
    );
    let eq_expr = ChcExpr::Op(
        ChcOp::Eq,
        vec![Arc::new(sel_app), Arc::new(ChcExpr::Int(99))],
    );

    let mut model = FxHashMap::default();
    model.insert(
        "x".to_string(),
        SmtValue::Datatype("Some".to_string(), vec![SmtValue::Int(42)]),
    );

    assert_eq!(mbp.eval_bool(&eq_expr, &model), Some(false));
}

/// BV MBP interval resolution with VARIABLE bounds — distinguishes interval
/// path from model-value fallback. If extract_bv_bound were broken (returning
/// None), all literals would be model-substituted, producing `bvuge(30, bv_y)
/// AND bvule(30, bv_z)` which still mentions the constant 30. Interval
/// resolution produces `bvule(bv_y, bv_z)` — no model constant.
#[test]
fn test_bv_mbp_interval_resolution_with_variable_bounds() {
    let mbp = Mbp::new();
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(8));
    let bv_y = ChcVar::new("bv_y", ChcSort::BitVec(8));
    let bv_z = ChcVar::new("bv_z", ChcSort::BitVec(8));

    // bvuge(bv_x, bv_y) AND bvule(bv_x, bv_z)
    let lb = ChcExpr::Op(
        ChcOp::BvUGe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::var(bv_y)),
        ],
    );
    let ub = ChcExpr::Op(
        ChcOp::BvULe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::var(bv_z)),
        ],
    );
    let formula = ChcExpr::and(lb, ub);

    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(30, 8));
    model.insert("bv_y".to_string(), SmtValue::BitVec(10, 8));
    model.insert("bv_z".to_string(), SmtValue::BitVec(50, 8));

    let result = mbp.project(&formula, &[bv_x], &model);
    let result_str = format!("{result:?}");

    // bv_x eliminated
    assert!(
        !result.contains_var_name("bv_x"),
        "bv_x should be eliminated. Got: {result_str}"
    );
    // Both bv_y and bv_z must remain (interval resolution produces bvule(bv_y, bv_z))
    assert!(
        result.contains_var_name("bv_y"),
        "bv_y should remain in interval constraint. Got: {result_str}"
    );
    assert!(
        result.contains_var_name("bv_z"),
        "bv_z should remain in interval constraint. Got: {result_str}"
    );
    // Result must NOT contain the model constant 30 — that would indicate
    // model-value fallback was used instead of interval resolution.
    assert!(
        !result_str.contains("BitVec(30,"),
        "Result should not contain model constant 30 (fallback path). Got: {result_str}"
    );
}

/// BV MBP negated comparison with variable bounds — ensures negation + interval
/// resolution actually exercises the negate_comparison + flip_bv_cmp path.
/// NOT bvule(bv_x, bv_y) [= bvugt(bv_x, bv_y)] AND bvule(bv_x, bv_z).
/// Interval resolution: bvult(bv_y, bv_z). Model fallback would produce
/// NOT bvule(75, bv_y) AND bvule(75, bv_z) containing constant 75.
#[test]
fn test_bv_mbp_negated_comparison_with_variable_bounds() {
    let mbp = Mbp::new();
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(8));
    let bv_y = ChcVar::new("bv_y", ChcSort::BitVec(8));
    let bv_z = ChcVar::new("bv_z", ChcSort::BitVec(8));

    // NOT bvule(bv_x, bv_y) [= bvugt(bv_x, bv_y)] AND bvule(bv_x, bv_z)
    let neg_ule = ChcExpr::not(ChcExpr::Op(
        ChcOp::BvULe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::var(bv_y)),
        ],
    ));
    let ub = ChcExpr::Op(
        ChcOp::BvULe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::var(bv_z)),
        ],
    );
    let formula = ChcExpr::and(neg_ule, ub);

    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(75, 8));
    model.insert("bv_y".to_string(), SmtValue::BitVec(50, 8));
    model.insert("bv_z".to_string(), SmtValue::BitVec(100, 8));

    let result = mbp.project(&formula, &[bv_x], &model);
    let result_str = format!("{result:?}");

    // bv_x eliminated
    assert!(
        !result.contains_var_name("bv_x"),
        "bv_x should be eliminated. Got: {result_str}"
    );
    // Both bv_y and bv_z must remain
    assert!(
        result.contains_var_name("bv_y"),
        "bv_y should remain. Got: {result_str}"
    );
    assert!(
        result.contains_var_name("bv_z"),
        "bv_z should remain. Got: {result_str}"
    );
    // No model constant 75
    assert!(
        !result_str.contains("BitVec(75,"),
        "Result should not contain model constant 75. Got: {result_str}"
    );
}

/// BV MBP: unpaired lower bound falls back to model-value substitution.
///
/// When projecting bv_x from `bvuge(bv_x, bv_y)` (only a lower bound,
/// no upper bound), the bound-producing literal should fall back to
/// model-value substitution to preserve constraints on bv_y.
/// Before the fix, unpaired bounds were silently dropped, losing
/// the constraint on remaining variables.
#[test]
fn test_bv_mbp_unpaired_lower_bound_preserves_constraint() {
    let mbp = Mbp::new();
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(8));
    let bv_y = ChcVar::new("bv_y", ChcSort::BitVec(8));

    // bvuge(bv_x, bv_y) — only a lower bound on bv_x, no upper bound
    let lower = ChcExpr::Op(
        ChcOp::BvUGe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::var(bv_y)),
        ],
    );

    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(50, 8));
    model.insert("bv_y".to_string(), SmtValue::BitVec(30, 8));

    let result = mbp.project(&lower, &[bv_x], &model);
    let result_str = format!("{result:?}");

    // bv_x should be eliminated
    assert!(
        !result.contains_var_name("bv_x"),
        "bv_x should be eliminated. Got: {result_str}"
    );
    // Model-value substitution should produce a constraint on bv_y:
    // bvuge(50, bv_y) i.e. 50 >=_u bv_y. This is non-trivial and
    // should be preserved (not dropped).
    assert!(
        result.contains_var_name("bv_y"),
        "bv_y should be preserved via model-value fallback. Got: {result_str}"
    );
}

/// BV MBP: lower-bound-only triggers model-value fallback for unpaired bounds.
/// Project bv_x from `bvuge(bv_x, bv_y)` — only a lower bound, no upper.
/// Interval resolution cannot fire (no upper to pair with). The bounds fallback
/// at theory.rs:627-638 should substitute bv_x with its model value.
#[test]
fn test_bv_mbp_unpaired_lower_bound_fallback() {
    let mbp = Mbp::new();
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(8));
    let bv_y = ChcVar::new("bv_y", ChcSort::BitVec(8));

    // bvuge(bv_x, bv_y) — lower bound on bv_x only, no upper bound
    let lb = ChcExpr::Op(
        ChcOp::BvUGe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::var(bv_y)),
        ],
    );

    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(50, 8));
    model.insert("bv_y".to_string(), SmtValue::BitVec(20, 8));

    let result = mbp.project(&lb, &[bv_x], &model);
    let result_str = format!("{result:?}");

    // bv_x should be eliminated
    assert!(
        !result.contains_var_name("bv_x"),
        "bv_x should be eliminated by unpaired-bound fallback. Got: {result_str}"
    );
    // The fallback substitutes bv_x=50, producing bvuge(50, bv_y).
    // bv_y should remain in the result.
    assert!(
        result.contains_var_name("bv_y"),
        "bv_y should remain after model-value substitution. Got: {result_str}"
    );
}

#[test]
fn test_bv_mbp_signed_interval_resolution() {
    let mbp = Mbp::new();
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(32));
    let bv_y = ChcVar::new("bv_y", ChcSort::BitVec(32));
    let bv_z = ChcVar::new("bv_z", ChcSort::BitVec(32));

    // bv_y <=_s bv_x AND bv_x <=_s bv_z (signed interval)
    let lb = ChcExpr::Op(
        ChcOp::BvSLe,
        vec![
            Arc::new(ChcExpr::var(bv_y)),
            Arc::new(ChcExpr::var(bv_x.clone())),
        ],
    );
    let ub = ChcExpr::Op(
        ChcOp::BvSLe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::var(bv_z)),
        ],
    );
    let formula = ChcExpr::and(lb, ub);

    // model: bv_y=-10 (0xFFFFFFF6), bv_x=5, bv_z=100
    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(5, 32));
    model.insert(
        "bv_y".to_string(),
        SmtValue::BitVec(0xFFFF_FFF6, 32), // -10 as unsigned
    );
    model.insert("bv_z".to_string(), SmtValue::BitVec(100, 32));

    let result = mbp.project(&formula, &[bv_x], &model);
    let result_str = format!("{result:?}");

    // bv_x should be eliminated via signed interval resolution
    assert!(
        !result.contains_var_name("bv_x"),
        "bv_x should be eliminated by signed interval resolution. Got: {result_str}"
    );
    // Result should be bv_y <=_s bv_z (signed comparison preserved)
    assert!(
        result.contains_var_name("bv_y") && result.contains_var_name("bv_z"),
        "Both bv_y and bv_z should remain. Got: {result_str}"
    );
}

#[test]
fn test_bv_mbp_signed_one_sided_fallback() {
    let mbp = Mbp::new();
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(8));
    let bv_y = ChcVar::new("bv_y", ChcSort::BitVec(8));

    // Only signed lower bound: bv_y <=_s bv_x (bv_x >=_s bv_y)
    let formula = ChcExpr::Op(
        ChcOp::BvSLe,
        vec![
            Arc::new(ChcExpr::var(bv_y)),
            Arc::new(ChcExpr::var(bv_x.clone())),
        ],
    );

    // model: bv_y=-5 (0xFB), bv_x=10
    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(10, 8));
    model.insert("bv_y".to_string(), SmtValue::BitVec(0xFB, 8)); // -5 as unsigned

    let result = mbp.project(&formula, &[bv_x], &model);
    let result_str = format!("{result:?}");

    // bv_x should be eliminated (via model-value fallback for one-sided signed)
    assert!(
        !result.contains_var_name("bv_x"),
        "bv_x should be eliminated. Got: {result_str}"
    );
}

#[test]
fn test_bv_mbp_mixed_signed_unsigned() {
    let mbp = Mbp::new();
    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(32));
    let bv_y = ChcVar::new("bv_y", ChcSort::BitVec(32));
    let bv_z = ChcVar::new("bv_z", ChcSort::BitVec(32));

    // Unsigned bound: bv_x <=_u bv_y
    // Signed bound: bv_z <=_s bv_x
    // These are independent — unsigned and signed intervals on same variable
    let u_ub = ChcExpr::Op(
        ChcOp::BvULe,
        vec![
            Arc::new(ChcExpr::var(bv_x.clone())),
            Arc::new(ChcExpr::var(bv_y)),
        ],
    );
    let s_lb = ChcExpr::Op(
        ChcOp::BvSLe,
        vec![
            Arc::new(ChcExpr::var(bv_z)),
            Arc::new(ChcExpr::var(bv_x.clone())),
        ],
    );
    let formula = ChcExpr::and(u_ub, s_lb);

    // model: bv_x=50, bv_y=100, bv_z=10
    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(50, 32));
    model.insert("bv_y".to_string(), SmtValue::BitVec(100, 32));
    model.insert("bv_z".to_string(), SmtValue::BitVec(10, 32));

    let result = mbp.project(&formula, &[bv_x], &model);
    let result_str = format!("{result:?}");

    // bv_x should be eliminated
    assert!(
        !result.contains_var_name("bv_x"),
        "bv_x should be eliminated (mixed signed/unsigned). Got: {result_str}"
    );
    // Both bv_y and bv_z should remain
    assert!(
        result.contains_var_name("bv_y") || result.contains_var_name("bv_z"),
        "At least one of bv_y/bv_z should remain. Got: {result_str}"
    );
}
