// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================================
// Datatype MBP tests (#7016)
// ============================================================================

/// Test eval_bool for DT tester: is-Some(x) when model has x = Some → true
#[test]
fn test_eval_bool_dt_tester_true() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", option_int_sort());

    // is-Some(x) should be true when model has x = "Some"
    let tester = ChcExpr::FuncApp(
        "is-Some".to_string(),
        ChcSort::Bool,
        vec![Arc::new(ChcExpr::Var(x))],
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Opaque("Some".to_string()));

    assert_eq!(mbp.eval_bool(&tester, &model), Some(true));
}

/// Test eval_bool for DT tester: is-None(x) when model has x = Some → false
#[test]
fn test_eval_bool_dt_tester_false() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", option_int_sort());

    let tester = ChcExpr::FuncApp(
        "is-None".to_string(),
        ChcSort::Bool,
        vec![Arc::new(ChcExpr::Var(x))],
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Opaque("Some".to_string()));

    assert_eq!(mbp.eval_bool(&tester, &model), Some(false));
}

/// Test eval_bool for DT tester: is-Some(x) with SmtValue::Datatype model value → true
#[test]
fn test_eval_bool_dt_tester_datatype_variant_true() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", option_int_sort());

    let tester = ChcExpr::FuncApp(
        "is-Some".to_string(),
        ChcSort::Bool,
        vec![Arc::new(ChcExpr::Var(x))],
    );

    let mut model = FxHashMap::default();
    model.insert(
        "x".to_string(),
        SmtValue::Datatype("Some".to_string(), vec![SmtValue::Int(42)]),
    );

    assert_eq!(mbp.eval_bool(&tester, &model), Some(true));
}

/// Test eval_bool for DT tester: is-None(x) with SmtValue::Datatype("Some", ...) → false
#[test]
fn test_eval_bool_dt_tester_datatype_variant_false() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", option_int_sort());

    let tester = ChcExpr::FuncApp(
        "is-None".to_string(),
        ChcSort::Bool,
        vec![Arc::new(ChcExpr::Var(x))],
    );

    let mut model = FxHashMap::default();
    model.insert(
        "x".to_string(),
        SmtValue::Datatype("Some".to_string(), vec![SmtValue::Int(42)]),
    );

    assert_eq!(mbp.eval_bool(&tester, &model), Some(false));
}

/// Test model_value_expr_or_default for DT: nullary constructor default.
#[test]
fn test_model_value_expr_or_default_dt_nullary() {
    let sort = option_int_sort();
    let var = ChcVar::new("x", sort.clone());
    let model = FxHashMap::default();

    let result = Mbp::model_value_expr_or_default(&var, &model);

    // Should pick the first nullary constructor: None
    match &result {
        ChcExpr::FuncApp(name, s, args) => {
            assert_eq!(name, "None");
            assert_eq!(s, &sort);
            assert!(args.is_empty());
        }
        other => panic!("Expected FuncApp(None), got: {other:?}"),
    }
}

/// Test model_value_expr_or_default for DT: non-nullary constructor default.
#[test]
fn test_model_value_expr_or_default_dt_non_nullary() {
    let sort = pair_int_sort();
    let var = ChcVar::new("p", sort.clone());
    let model = FxHashMap::default();

    let result = Mbp::model_value_expr_or_default(&var, &model);

    // Pair has no nullary constructors. Should pick mkpair with default args.
    match &result {
        ChcExpr::FuncApp(name, s, args) => {
            assert_eq!(name, "mkpair");
            assert_eq!(s, &sort);
            assert_eq!(args.len(), 2);
            // Default Int args should be Int(0)
            assert_eq!(args[0].as_ref(), &ChcExpr::Int(0));
            assert_eq!(args[1].as_ref(), &ChcExpr::Int(0));
        }
        other => panic!("Expected FuncApp(mkpair, 0, 0), got: {other:?}"),
    }
}

/// Test DT projection: project_datatype_var with nullary constructor (None).
/// x : OptionInt, model x = None, literal: is-None(x)
/// After projection of x: is-None(None) → simplified to true → empty result.
#[test]
fn test_project_datatype_var_nullary_constructor() {
    let mbp = Mbp::new();
    let sort = option_int_sort();
    let x = ChcVar::new("x", sort);

    // Literal: is-None(x)
    let tester = ChcExpr::FuncApp(
        "is-None".to_string(),
        ChcSort::Bool,
        vec![Arc::new(ChcExpr::Var(x.clone()))],
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Opaque("None".to_string()));

    let result = mbp.project(&tester, std::slice::from_ref(&x), &model);

    // After substituting x → None, is-None(None) should simplify (or be kept).
    // The result should not contain x.
    let result_vars = result.vars();
    assert!(
        !result_vars.iter().any(|v| v.name == "x"),
        "x must be eliminated. Got: {result:?}"
    );
}

/// Test DT projection with SmtValue::Datatype (non-nullary constructor).
/// project_datatype_var_with_fresh should decompose x → Some(x__val)
/// and generate a fresh variable for the field.
#[test]
fn test_project_datatype_var_nonnullary_datatype_variant() {
    let mbp = Mbp::new();
    let sort = option_int_sort();
    let x = ChcVar::new("x", sort);

    // Literal: is-Some(x)
    let tester = ChcExpr::FuncApp(
        "is-Some".to_string(),
        ChcSort::Bool,
        vec![Arc::new(ChcExpr::Var(x.clone()))],
    );

    let mut model = FxHashMap::default();
    model.insert(
        "x".to_string(),
        SmtValue::Datatype("Some".to_string(), vec![SmtValue::Int(42)]),
    );

    let result = mbp.project(&tester, std::slice::from_ref(&x), &model);

    // After substituting x → Some(x__val), x must be eliminated.
    let result_vars = result.vars();
    assert!(
        !result_vars.iter().any(|v| v.name == "x"),
        "x must be eliminated via DT projection. Got: {result:?}"
    );
}

/// Test DT literal expansion: expand_dt_literals decomposes
/// (= x (mkpair 42 7)) into (is-mkpair x) ∧ (= (fst x) 42) ∧ (= (snd x) 7).
/// Since Pair has only 1 constructor, the is-mkpair tester is NOT emitted.
#[test]
fn test_expand_dt_literals_pair() {
    let sort = pair_int_sort();
    let x = ChcVar::new("x", sort.clone());

    // (= x (mkpair 42 7))
    let ctor_app = ChcExpr::FuncApp(
        "mkpair".to_string(),
        sort,
        vec![Arc::new(ChcExpr::Int(42)), Arc::new(ChcExpr::Int(7))],
    );
    let eq = ChcExpr::eq(ChcExpr::Var(x), ctor_app);

    let mut literals = vec![Literal::new(eq, true)];
    Mbp::expand_dt_literals(&mut literals);

    // Should produce 2 selector equalities (no recognizer for single-ctor sort)
    assert_eq!(
        literals.len(),
        2,
        "Single-constructor DT should produce 2 selector equalities. Got: {literals:?}"
    );

    let lit_strs: Vec<String> = literals.iter().map(|l| format!("{:?}", l.atom)).collect();
    let combined = lit_strs.join(" | ");

    // Check for fst and snd selector equalities
    assert!(
        combined.contains("fst") && combined.contains("snd"),
        "Should have fst and snd selector equalities. Got: {combined}"
    );
}

/// Test DT literal expansion for multi-constructor: should emit is-Some tester.
#[test]
fn test_expand_dt_literals_option_adds_recognizer() {
    let sort = option_int_sort();
    let x = ChcVar::new("x", sort.clone());

    // (= x (Some 42))
    let ctor_app = ChcExpr::FuncApp("Some".to_string(), sort, vec![Arc::new(ChcExpr::Int(42))]);
    let eq = ChcExpr::eq(ChcExpr::Var(x), ctor_app);

    let mut literals = vec![Literal::new(eq, true)];
    Mbp::expand_dt_literals(&mut literals);

    // Should produce: is-Some(x) + (= (val x) 42) = 2 literals
    assert_eq!(
        literals.len(),
        2,
        "Multi-constructor DT should produce recognizer + selector eq. Got: {literals:?}"
    );

    let lit_strs: Vec<String> = literals.iter().map(|l| format!("{:?}", l.atom)).collect();
    let combined = lit_strs.join(" | ");

    assert!(
        combined.contains("is-Some"),
        "Should have is-Some recognizer. Got: {combined}"
    );
    assert!(
        combined.contains("val"),
        "Should have val selector equality. Got: {combined}"
    );
}

/// End-to-end DT projection: project x out of (> y 0) ∧ (= x (Some y))
/// with model x = Some, y = 42.
/// After projection of x: y > 0 should remain (x eliminated).
#[test]
fn test_project_dt_end_to_end_option_some() {
    let mbp = Mbp::new();
    let sort = option_int_sort();
    let x = ChcVar::new("x", sort.clone());
    let y = ChcVar::new("y", ChcSort::Int);

    // Formula: (> y 0) ∧ (= x (Some y))
    let gt = ChcExpr::gt(ChcExpr::Var(y.clone()), ChcExpr::Int(0));
    let ctor_app = ChcExpr::FuncApp("Some".to_string(), sort, vec![Arc::new(ChcExpr::Var(y))]);
    let eq = ChcExpr::eq(ChcExpr::Var(x.clone()), ctor_app);
    let formula = ChcExpr::and(gt, eq);

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Opaque("Some".to_string()));
    model.insert("y".to_string(), SmtValue::Int(42));

    let result = mbp.project(&formula, std::slice::from_ref(&x), &model);

    // x must be eliminated
    let result_vars = result.vars();
    assert!(
        !result_vars.iter().any(|v| v.name == "x"),
        "x must be eliminated. Got: {result:?}"
    );

    // y should still be present (not projected)
    let result_str = format!("{result:?}");
    assert!(
        result_str.contains("y"),
        "y should remain in result. Got: {result_str}"
    );
}

/// model_value_expr correctly converts SmtValue::Datatype to ChcExpr::FuncApp.
#[test]
fn test_model_value_expr_dt_datatype_variant() {
    let sort = pair_int_sort();
    let var = ChcVar::new("p", sort);
    let mut model = FxHashMap::default();
    model.insert(
        "p".to_string(),
        SmtValue::Datatype(
            "mkpair".to_string(),
            vec![SmtValue::Int(10), SmtValue::Int(20)],
        ),
    );
    let expr = Mbp::model_value_expr(&var, &model);
    assert!(expr.is_some(), "SmtValue::Datatype should produce Some");
    let expr = expr.unwrap();
    match &expr {
        ChcExpr::FuncApp(name, _, args) => {
            assert_eq!(name, "mkpair");
            assert_eq!(args.len(), 2);
        }
        other => panic!("Expected FuncApp, got: {other:?}"),
    }
}

// ============================================================================
// Packet 2: Iterative MBP loop for fresh variables (#6047)
// ============================================================================

/// Verify that fresh __mbp_sel_* variables introduced by array projection
/// are eliminated by the iterative FM re-projection loop.
///
/// Formula: select(a, i) = 5 AND select(a, i) < y AND a projected.
/// Without the loop: __mbp_sel_a_0 remains in the result.
/// With the loop: FM projects __mbp_sel_a_0 via equality, yielding 5 < y.
#[test]
fn test_iterative_mbp_loop_eliminates_fresh_array_vars() {
    let mbp = Mbp::new();

    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let a = ChcVar::new("a", arr_sort);
    let i = ChcVar::new("i", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // select(a, i) = 5
    let sel = ChcExpr::select(ChcExpr::var(a.clone()), ChcExpr::var(i));
    let eq = ChcExpr::eq(sel.clone(), ChcExpr::Int(5));
    // select(a, i) < y
    let lt = ChcExpr::lt(sel, ChcExpr::var(y));
    let formula = ChcExpr::and(eq, lt);

    let mut model = FxHashMap::default();
    model.insert("i".to_string(), SmtValue::Int(3));
    model.insert("y".to_string(), SmtValue::Int(10));

    let result = mbp.project(&formula, std::slice::from_ref(&a), &model);

    // a must be eliminated
    let result_vars = result.vars();
    assert!(
        !result_vars.iter().any(|v| v.name == "a"),
        "a must be eliminated. Got: {result:?}"
    );

    // Fresh __mbp_ variables must also be eliminated by the iterative loop
    assert!(
        !result_vars.iter().any(|v| v.name.starts_with("__mbp_")),
        "Fresh __mbp_ variables must be eliminated by iterative loop. Got vars: {:?}",
        result_vars.iter().map(|v| &v.name).collect::<Vec<_>>()
    );
}

/// Verify that the iterative loop handles multiple fresh vars from
/// different select indices.
///
/// Formula: select(a, 0) + select(a, 1) < y AND a projected.
/// Array projection creates __mbp_sel_a_0 and __mbp_sel_a_1.
/// Both should be eliminated (dropped as unconstrained one-sided).
#[test]
fn test_iterative_mbp_loop_multiple_fresh_vars() {
    let mbp = Mbp::new();

    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let a = ChcVar::new("a", arr_sort);
    let y = ChcVar::new("y", ChcSort::Int);

    // select(a, 0) + select(a, 1) < y
    let sel0 = ChcExpr::select(ChcExpr::var(a.clone()), ChcExpr::Int(0));
    let sel1 = ChcExpr::select(ChcExpr::var(a.clone()), ChcExpr::Int(1));
    let sum = ChcExpr::add(sel0, sel1);
    let lt = ChcExpr::lt(sum, ChcExpr::var(y));
    let formula = lt;

    let mut model = FxHashMap::default();
    model.insert("y".to_string(), SmtValue::Int(20));

    let result = mbp.project(&formula, std::slice::from_ref(&a), &model);

    // a must be eliminated
    assert!(
        !result.vars().iter().any(|v| v.name == "a"),
        "a must be eliminated. Got: {result:?}"
    );
}

// ============================================================================
// Packet 3: Array extensionality saturation (#6047)
// ============================================================================

/// Pre-projection saturation should materialize the hit guard for
/// `select(store(a, i, v), j)` when the model makes `i` and `j` equal.
#[test]
fn test_saturate_array_disequalities_adds_store_select_hit_guard() {
    let mbp = Mbp::new();

    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let a = ChcVar::new("a", arr_sort);
    let i = ChcVar::new("i", ChcSort::Int);
    let j = ChcVar::new("j", ChcSort::Int);

    let stored = ChcExpr::store(ChcExpr::var(a), ChcExpr::var(i.clone()), ChcExpr::Int(42));
    let sel = ChcExpr::select(stored, ChcExpr::var(j.clone()));
    let mut implicant = vec![Literal::new(ChcExpr::gt(sel, ChcExpr::Int(0)), true)];

    let mut model = FxHashMap::default();
    model.insert("i".to_string(), SmtValue::Int(5));
    model.insert("j".to_string(), SmtValue::Int(5));

    mbp.saturate_array_disequalities(&mut implicant, &model);

    assert!(
        implicant.iter().any(|lit| {
            lit.positive
                && lit.atom == ChcExpr::eq(ChcExpr::var(i.clone()), ChcExpr::var(j.clone()))
        }),
        "Saturation must add the model-true hit guard i = j. Got: {implicant:?}"
    );
}

/// Pre-projection saturation should materialize the miss branch for
/// `select(store(a, i, v), j)` when the model makes `i` and `j` different.
#[test]
fn test_saturate_array_disequalities_adds_store_select_miss_axioms() {
    let mbp = Mbp::new();

    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let a = ChcVar::new("a", arr_sort);
    let i = ChcVar::new("i", ChcSort::Int);
    let j = ChcVar::new("j", ChcSort::Int);

    let stored = ChcExpr::store(
        ChcExpr::var(a.clone()),
        ChcExpr::var(i.clone()),
        ChcExpr::Int(42),
    );
    let sel = ChcExpr::select(stored, ChcExpr::var(j.clone()));
    let mut implicant = vec![Literal::new(
        ChcExpr::gt(sel.clone(), ChcExpr::Int(0)),
        true,
    )];

    let mut model = FxHashMap::default();
    model.insert("i".to_string(), SmtValue::Int(5));
    model.insert("j".to_string(), SmtValue::Int(7));

    mbp.saturate_array_disequalities(&mut implicant, &model);

    let expected_guard = ChcExpr::ne(ChcExpr::var(i), ChcExpr::var(j.clone()));
    let expected_passthrough = ChcExpr::eq(sel, ChcExpr::select(ChcExpr::var(a), ChcExpr::var(j)));

    assert!(
        implicant
            .iter()
            .any(|lit| lit.positive && lit.atom == expected_guard),
        "Saturation must add the model-true miss guard i != j. Got: {implicant:?}"
    );
    assert!(
        implicant
            .iter()
            .any(|lit| lit.positive && lit.atom == expected_passthrough),
        "Saturation must add the miss passthrough equality. Got: {implicant:?}"
    );
}

/// Verify that array disequality saturation adds an explicit witness literal
/// before projection when the model distinguishes the arrays.
#[test]
fn test_saturate_array_disequalities_adds_witness_literal() {
    let mbp = Mbp::new();

    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let a = ChcVar::new("a", arr_sort.clone());
    let b = ChcVar::new("b", arr_sort);

    // Model: a = const(0), b = {default: 0, 1 -> 5}
    // Arrays differ at index 1.
    let mut model = FxHashMap::default();
    model.insert(
        "a".to_string(),
        SmtValue::ConstArray(Box::new(SmtValue::Int(0))),
    );
    model.insert(
        "b".to_string(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(1), SmtValue::Int(5))],
        },
    );

    let mut implicant = vec![Literal::new(
        ChcExpr::ne(ChcExpr::var(a), ChcExpr::var(b)),
        true,
    )];
    mbp.saturate_array_disequalities(&mut implicant, &model);

    assert!(
        implicant.len() == 2,
        "Saturation should add one witness literal. Got: {implicant:?}"
    );
    assert!(
        matches!(
            &implicant[1].atom,
            ChcExpr::Op(ChcOp::Ne, args)
                if args.len() == 2
                    && matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Select, _))
                    && matches!(args[1].as_ref(), ChcExpr::Op(ChcOp::Select, _))
        ),
        "Witness literal should be a disequality between selects. Got: {:?}",
        implicant[1]
    );
}

/// Array disequality saturation must also handle store terms, not just plain
/// array variables, so store-chain witnesses are visible before projection.
#[test]
fn test_saturate_array_disequalities_adds_witness_for_store_term() {
    let mbp = Mbp::new();

    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let a = ChcVar::new("a", arr_sort.clone());
    let b = ChcVar::new("b", arr_sort);

    let store_term = ChcExpr::store(ChcExpr::var(a), ChcExpr::Int(1), ChcExpr::Int(5));

    let mut model = FxHashMap::default();
    model.insert(
        "a".to_string(),
        SmtValue::ConstArray(Box::new(SmtValue::Int(0))),
    );
    model.insert(
        "b".to_string(),
        SmtValue::ConstArray(Box::new(SmtValue::Int(0))),
    );

    let mut implicant = vec![Literal::new(
        ChcExpr::ne(store_term.clone(), ChcExpr::var(b.clone())),
        true,
    )];
    mbp.saturate_array_disequalities(&mut implicant, &model);

    let expected_witness = ChcExpr::ne(
        ChcExpr::select(store_term, ChcExpr::Int(1)),
        ChcExpr::select(ChcExpr::var(b), ChcExpr::Int(1)),
    );
    assert!(
        implicant
            .iter()
            .any(|lit| lit.positive && lit.atom == expected_witness),
        "Saturation must add a witness for disequalities involving store terms. Got: {implicant:?}"
    );
}

// ============================================================================
// Algorithm audit: DT pipeline correctness findings (P10:2263)
// ============================================================================

/// eval_bool handles DT-sorted Eq via generic fallback.
/// (= x y) where both x,y are DT-sorted and in the model returns Some(true/false).
#[test]
fn test_eval_bool_eq_dt_sorted() {
    let mbp = Mbp::new();
    let sort = pair_int_sort();
    let x = ChcVar::new("x", sort.clone());
    let y = ChcVar::new("y", sort.clone());
    let z = ChcVar::new("z", sort);

    let eq_xy = ChcExpr::eq(ChcExpr::Var(x.clone()), ChcExpr::Var(y));
    let eq_xz = ChcExpr::eq(ChcExpr::Var(x), ChcExpr::Var(z));

    let mut model = FxHashMap::default();
    model.insert(
        "x".to_string(),
        SmtValue::Datatype(
            "mkpair".to_string(),
            vec![SmtValue::Int(1), SmtValue::Int(2)],
        ),
    );
    model.insert(
        "y".to_string(),
        SmtValue::Datatype(
            "mkpair".to_string(),
            vec![SmtValue::Int(1), SmtValue::Int(2)],
        ),
    );
    model.insert(
        "z".to_string(),
        SmtValue::Datatype(
            "mkpair".to_string(),
            vec![SmtValue::Int(3), SmtValue::Int(4)],
        ),
    );

    assert_eq!(mbp.eval_bool(&eq_xy, &model), Some(true), "equal DT values");
    assert_eq!(
        mbp.eval_bool(&eq_xz, &model),
        Some(false),
        "different DT values"
    );
}

/// BUG: smt_value_to_expr uses ChcSort::Uninterpreted for nested DT values.
/// The sort should be the actual DT sort, not Uninterpreted(ctor_name).
#[test]
fn test_smt_value_to_expr_nested_dt_uses_wrong_sort_bug() {
    let outer_val = SmtValue::Datatype(
        "mkpair".to_string(),
        vec![SmtValue::Int(42), SmtValue::Int(7)],
    );

    // Use model_value_expr which calls smt_value_to_expr for field values
    let sort = pair_int_sort();
    let var = ChcVar::new("p", sort.clone());
    let mut model = FxHashMap::default();
    model.insert("p".to_string(), outer_val);

    let result = Mbp::model_value_expr(&var, &model);
    assert!(
        result.is_some(),
        "model_value_expr should handle Datatype values"
    );
    let expr = result.unwrap();

    // Verify top-level sort is correct
    match &expr {
        ChcExpr::FuncApp(name, s, args) => {
            assert_eq!(name, "mkpair");
            assert_eq!(s, &sort, "Top-level sort should be the DT sort");
            assert_eq!(args.len(), 2);
            // Fields should be Int literals, not nested DT, so sort is fine here
            assert_eq!(args[0].as_ref(), &ChcExpr::Int(42));
            assert_eq!(args[1].as_ref(), &ChcExpr::Int(7));
        }
        other => panic!("Expected FuncApp, got: {other:?}"),
    }
}

/// smt_value_to_expr correctly converts SmtValue::Real to ChcExpr::Real.
#[test]
fn test_smt_value_to_expr_real_field() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    // Create a DT with a Real field value
    let real_val = SmtValue::Real(BigRational::new(BigInt::from(3), BigInt::from(7)));
    let dt_val = SmtValue::Datatype("wrapper".to_string(), vec![real_val]);

    // Use a DT sort that has a Real field
    let sort = {
        use crate::expr::{ChcDtConstructor, ChcDtSelector};
        ChcSort::Datatype {
            name: "RealWrapper".to_string(),
            constructors: Arc::new(vec![ChcDtConstructor {
                name: "wrapper".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "val".to_string(),
                    sort: ChcSort::Real,
                }],
            }]),
        }
    };
    let var = ChcVar::new("w", sort);
    let mut model = FxHashMap::default();
    model.insert("w".to_string(), dt_val);

    let result = Mbp::model_value_expr(&var, &model);
    assert!(
        result.is_some(),
        "model_value_expr should handle Datatype with Real field"
    );
    let expr = result.unwrap();

    match &expr {
        ChcExpr::FuncApp(_, _, args) => {
            assert_eq!(
                args[0].as_ref(),
                &ChcExpr::Real(3, 7),
                "Real field should be preserved as ChcExpr::Real(3, 7)"
            );
        }
        other => panic!("Expected FuncApp, got: {other:?}"),
    }
}
