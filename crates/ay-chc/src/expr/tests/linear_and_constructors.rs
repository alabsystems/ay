// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;

/// Helper: look up coefficient for a variable in LinearTermsProd.
fn coeff(terms: &LinearTermsProd, var: &str) -> i128 {
    terms.coeffs.get(var).copied().unwrap_or(0)
}

/// Build a left-associated AND chain of depth `n` with a leaf at the bottom.
/// Uses Op(And, ...) directly to create genuine nesting.
fn build_genuinely_nested_and_chain(depth: usize) -> ChcExpr {
    let leaf = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(0),
    );
    let mut expr = leaf.clone();
    for _ in 0..depth {
        expr = ChcExpr::Op(ChcOp::And, vec![Arc::new(expr), Arc::new(leaf.clone())]);
    }
    expr
}

fn assert_left_associated_binary_and_depth(expr: &ChcExpr, expected_depth: usize) {
    let mut depth = 0usize;
    let mut current = expr;
    while let ChcExpr::Op(ChcOp::And, args) = current {
        assert_eq!(
            args.len(),
            2,
            "And node at depth {depth} should be binary, not flattened"
        );
        depth += 1;
        current = args[0].as_ref();
    }
    assert_eq!(
        depth, expected_depth,
        "expected left-associated AND depth {expected_depth}, got {depth}"
    );
}

#[test]
fn collect_linear_terms_constant() {
    let expr = ChcExpr::Int(42);
    let terms = ChcExpr::collect_linear_terms_prod(&expr).unwrap();
    assert!(terms.coeffs.is_empty());
    assert_eq!(terms.constant, 42);
}

#[test]
fn collect_linear_terms_variable() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::var(x);
    let terms = ChcExpr::collect_linear_terms_prod(&expr).unwrap();
    assert_eq!(coeff(&terms, "x"), 1);
    assert_eq!(terms.constant, 0);
}

#[test]
fn collect_linear_terms_add() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(5));
    let terms = ChcExpr::collect_linear_terms_prod(&expr).unwrap();
    assert_eq!(coeff(&terms, "x"), 1);
    assert_eq!(terms.constant, 5);
}

#[test]
fn collect_linear_terms_sub() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::sub(ChcExpr::var(x), ChcExpr::Int(3));
    let terms = ChcExpr::collect_linear_terms_prod(&expr).unwrap();
    assert_eq!(coeff(&terms, "x"), 1);
    assert_eq!(terms.constant, -3);
}

#[test]
fn collect_linear_terms_neg() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::neg(ChcExpr::var(x));
    let terms = ChcExpr::collect_linear_terms_prod(&expr).unwrap();
    assert_eq!(coeff(&terms, "x"), -1);
}

#[test]
fn neg_constant_folding() {
    let expr = ChcExpr::neg(ChcExpr::Int(5));
    assert_eq!(expr, ChcExpr::Int(-5));
}

#[test]
fn neg_constant_folding_zero() {
    let expr = ChcExpr::neg(ChcExpr::Int(0));
    assert_eq!(expr, ChcExpr::Int(0));
}

#[test]
fn neg_constant_folding_negative() {
    let expr = ChcExpr::neg(ChcExpr::Int(-3));
    assert_eq!(expr, ChcExpr::Int(3));
}

#[test]
fn neg_i64_min_overflow_stays_op() {
    // i128-lockstep: the non-foldable boundary is now i128::MIN.
    let expr = ChcExpr::neg(ChcExpr::Int(i128::MIN));
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Neg, _)));
}

#[test]
fn neg_double_negation_elimination() {
    let x = ChcVar::new("x", ChcSort::Int);
    let var = ChcExpr::var(x);
    let double_neg = ChcExpr::neg(ChcExpr::neg(var.clone()));
    assert_eq!(double_neg, var);
}

#[test]
fn neg_non_constant_stays_op() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::neg(ChcExpr::var(x));
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Neg, _)));
}

#[test]
fn collect_linear_terms_mul_const() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mul(ChcExpr::Int(3), ChcExpr::var(x));
    let terms = ChcExpr::collect_linear_terms_prod(&expr).unwrap();
    assert_eq!(coeff(&terms, "x"), 3);
}

#[test]
fn collect_linear_terms_complex() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::add(
        ChcExpr::sub(
            ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x)),
            ChcExpr::mul(ChcExpr::Int(3), ChcExpr::var(y)),
        ),
        ChcExpr::Int(7),
    );
    let terms = ChcExpr::collect_linear_terms_prod(&expr).unwrap();
    assert_eq!(coeff(&terms, "x"), 2);
    assert_eq!(coeff(&terms, "y"), -3);
    assert_eq!(terms.constant, 7);
}

#[test]
fn collect_linear_terms_nonlinear_fails() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::var(x));
    assert!(ChcExpr::collect_linear_terms_prod(&expr).is_none());
}

#[test]
fn or_vec_empty_is_false() {
    assert_eq!(ChcExpr::or_vec(vec![]), ChcExpr::Bool(false));
}

#[test]
fn or_vec_singleton_is_identity() {
    assert_eq!(
        ChcExpr::or_vec(vec![ChcExpr::Bool(true)]),
        ChcExpr::Bool(true)
    );
}

#[test]
fn or_vec_multiple_builds_nary_op() {
    let a = ChcExpr::Bool(true);
    let b = ChcExpr::Bool(false);
    assert_eq!(
        ChcExpr::or_vec(vec![a.clone(), b.clone()]),
        ChcExpr::Op(ChcOp::Or, vec![Arc::new(a), Arc::new(b)])
    );
}

#[test]
fn and_vec_empty_is_true() {
    assert_eq!(ChcExpr::and_vec(vec![]), ChcExpr::Bool(true));
}

#[test]
fn and_vec_singleton_is_identity() {
    assert_eq!(
        ChcExpr::and_vec(vec![ChcExpr::Bool(false)]),
        ChcExpr::Bool(false)
    );
}

#[test]
fn contains_mod_distinguishes_mod_vs_div() {
    let x = ChcVar::new("x", ChcSort::Int);

    let mod_expr = ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(2));
    let div_expr = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(2))],
    );

    assert!(mod_expr.contains_mod());
    assert!(mod_expr.contains_mod_or_div());

    assert!(!div_expr.contains_mod());
    assert!(div_expr.contains_mod_or_div());
}

#[test]
fn theory_shape_detectors_flag_div_zero_and_nonconstant() {
    let x = ChcVar::new("x", ChcSort::Int);
    let div = |a: ChcExpr, b: ChcExpr| ChcExpr::Op(ChcOp::Div, vec![Arc::new(a), Arc::new(b)]);

    // #57: div/mod by a literal zero divisor.
    let div0 = div(ChcExpr::var(x.clone()), ChcExpr::int(0));
    assert!(div0.contains_div_or_mod_by_zero());
    assert!(!div0.contains_div_or_mod_by_nonconstant()); // 0 is a constant
    let mod0 = ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(0));
    assert!(mod0.contains_div_or_mod_by_zero());

    // Constant non-zero divisor: neither flag fires.
    let divc = div(ChcExpr::var(x.clone()), ChcExpr::int(3));
    assert!(!divc.contains_div_or_mod_by_zero());
    assert!(!divc.contains_div_or_mod_by_nonconstant());

    // #55: non-constant (variable) divisor — nonconstant, not zero.
    let divnc = div(ChcExpr::int(1), ChcExpr::var(x.clone()));
    assert!(divnc.contains_div_or_mod_by_nonconstant());
    assert!(!divnc.contains_div_or_mod_by_zero());

    // Detectors recurse through predicate-application args.
    let wrapped = ChcExpr::predicate_app("P", PredicateId(0), vec![div0.clone()]);
    assert!(wrapped.contains_div_or_mod_by_zero());
}

#[test]
fn contains_mod_or_div_recurses_through_apps_and_const_arrays() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mod_expr = ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(2));

    let pred = ChcExpr::predicate_app("P", PredicateId(0), vec![mod_expr.clone()]);
    assert!(pred.contains_mod());
    assert!(pred.contains_mod_or_div());

    let func = ChcExpr::FuncApp(
        "f".to_string(),
        ChcSort::Int,
        vec![Arc::new(mod_expr.clone())],
    );
    assert!(func.contains_mod());
    assert!(func.contains_mod_or_div());

    let const_arr = ChcExpr::ConstArray(ChcSort::Int, Arc::new(mod_expr));
    assert!(const_arr.contains_mod());
    assert!(const_arr.contains_mod_or_div());

    let markers = [
        ChcExpr::ConstArrayMarker(ChcSort::Int),
        ChcExpr::IsTesterMarker("Ctor".to_string()),
    ];
    for m in &markers {
        assert!(!m.contains_mod());
        assert!(!m.contains_mod_or_div());
    }
}

#[test]
fn contains_mod_or_div_depth_guard_handles_deep_nesting() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut expr = ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(2));

    for _ in 0..(MAX_EXPR_RECURSION_DEPTH + 16) {
        expr = ChcExpr::and(ChcExpr::Bool(true), expr);
    }

    assert!(
        expr.contains_mod_or_div(),
        "depth-guarded traversal should conservatively report deep nested mod"
    );
}

#[test]
fn contains_predicates_detect_ite_negation_and_strict_comparisons() {
    let x = ChcVar::new("x", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Bool);

    let ite_expr = ChcExpr::ite(ChcExpr::var(b), ChcExpr::int(1), ChcExpr::int(0));
    let negated = ChcExpr::not(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)));
    let strict = ChcExpr::Op(
        ChcOp::Lt,
        vec![
            Arc::new(ChcExpr::var(x.clone())),
            Arc::new(ChcExpr::int(10)),
        ],
    );

    let combined = ChcExpr::and(ChcExpr::and(ite_expr, negated), strict.clone());
    assert!(combined.contains_ite());
    assert!(combined.contains_negation());
    assert!(combined.contains_strict_int_comparison());

    let wrapped = ChcExpr::predicate_app("P", PredicateId(0), vec![combined.clone()]);
    assert!(wrapped.contains_ite());
    assert!(wrapped.contains_negation());
    assert!(wrapped.contains_strict_int_comparison());

    let func = ChcExpr::FuncApp("f".to_string(), ChcSort::Bool, vec![Arc::new(combined)]);
    assert!(func.contains_ite());
    assert!(func.contains_negation());
    assert!(func.contains_strict_int_comparison());

    let const_arr = ChcExpr::ConstArray(ChcSort::Int, Arc::new(strict));
    assert!(!const_arr.contains_ite());
    assert!(!const_arr.contains_negation());
    assert!(const_arr.contains_strict_int_comparison());

    let markers = [
        ChcExpr::ConstArrayMarker(ChcSort::Int),
        ChcExpr::IsTesterMarker("Ctor".to_string()),
    ];
    for m in &markers {
        assert!(!m.contains_ite());
        assert!(!m.contains_negation());
        assert!(!m.contains_strict_int_comparison());
    }

    let plain_eq = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(42));
    assert!(!plain_eq.contains_ite());
    assert!(!plain_eq.contains_negation());
    assert!(!plain_eq.contains_strict_int_comparison());
}

#[test]
fn contains_var_name_finds_variable_in_nested_expr() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::add(
        ChcExpr::var(x),
        ChcExpr::mul(ChcExpr::var(y), ChcExpr::int(2)),
    );
    assert!(expr.contains_var_name("x"));
    assert!(expr.contains_var_name("y"));
    assert!(!expr.contains_var_name("z"));
    assert!(!ChcExpr::int(42).contains_var_name("x"));
    assert!(!ChcExpr::Bool(true).contains_var_name("x"));

    let pred = ChcExpr::predicate_app(
        "P",
        PredicateId(0),
        vec![ChcExpr::var(ChcVar::new("a", ChcSort::Bool))],
    );
    assert!(pred.contains_var_name("a"));
    assert!(!pred.contains_var_name("b"));
}

#[test]
fn display_predicate_app_includes_predicate_id() {
    let x = ChcVar::new("x", ChcSort::Int);
    let arg = ChcExpr::var(x);

    let p0 = ChcExpr::predicate_app("Inv", PredicateId::new(0), vec![arg.clone()]);
    let p1 = ChcExpr::predicate_app("Inv", PredicateId::new(1), vec![arg]);

    let p0_display = p0.to_string();
    let p1_display = p1.to_string();

    assert_ne!(p0_display, p1_display);
    assert!(p0_display.contains("Inv#0"));
    assert!(p1_display.contains("Inv#1"));
}

#[test]
fn display_func_app_includes_return_sort() {
    let x = ChcVar::new("x", ChcSort::Int);
    let arg = Arc::new(ChcExpr::var(x));

    let int_app = ChcExpr::FuncApp("f".to_string(), ChcSort::Int, vec![arg.clone()]);
    let bv_app = ChcExpr::FuncApp("f".to_string(), ChcSort::BitVec(8), vec![arg]);

    let int_display = int_app.to_string();
    let bv_display = bv_app.to_string();

    assert_ne!(int_display, bv_display);
    assert!(int_display.contains("f:Int"));
    assert!(bv_display.contains("f:(_ BitVec 8)"));
}

#[test]
fn display_distinguishes_iff_from_eq() {
    let a = ChcExpr::var(ChcVar::new("a", ChcSort::Bool));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Bool));

    let iff = ChcExpr::Op(ChcOp::Iff, vec![Arc::new(a.clone()), Arc::new(b.clone())]);
    let eq = ChcExpr::Op(ChcOp::Eq, vec![Arc::new(a), Arc::new(b)]);

    assert_eq!(iff.to_string(), "(iff a b)");
    assert_eq!(eq.to_string(), "(= a b)");
}

#[test]
fn and_vec_multiple_builds_nary_op() {
    let a = ChcExpr::Bool(true);
    let b = ChcExpr::Bool(false);
    assert_eq!(
        ChcExpr::and_vec(vec![a.clone(), b.clone()]),
        ChcExpr::Op(ChcOp::And, vec![Arc::new(a), Arc::new(b)])
    );
}

#[test]
fn and_all_empty() {
    let result = ChcExpr::and_all(Vec::<ChcExpr>::new());
    assert!(matches!(result, ChcExpr::Bool(true)));
}

#[test]
fn and_all_single() {
    let parts = vec![ChcExpr::Bool(false)];
    let result = ChcExpr::and_all(parts);
    assert!(matches!(result, ChcExpr::Bool(false)));
}

#[test]
fn and_all_multiple() {
    let x = ChcVar::new("x", ChcSort::Int);
    let parts = vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(10)),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5)),
    ];
    let result = ChcExpr::and_all(parts);
    assert!(matches!(result, ChcExpr::Op(ChcOp::And, _)));
}

#[test]
fn and_all_short_circuits_on_false() {
    let parts = vec![
        ChcExpr::Bool(true),
        ChcExpr::Bool(false),
        ChcExpr::eq(ChcExpr::Int(0), ChcExpr::Int(1)),
    ];
    let result = ChcExpr::and_all(parts);
    assert!(matches!(result, ChcExpr::Bool(false)));
}

#[test]
fn and_all_skips_true() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    let parts = vec![ChcExpr::Bool(true), expr.clone(), ChcExpr::Bool(true)];
    let result = ChcExpr::and_all(parts);
    assert_eq!(result, expr);
}

#[test]
fn and_all_flattens_nested_and() {
    let a = ChcExpr::eq(ChcExpr::Int(1), ChcExpr::Int(1));
    let b = ChcExpr::eq(ChcExpr::Int(2), ChcExpr::Int(2));
    let c = ChcExpr::eq(ChcExpr::Int(3), ChcExpr::Int(3));
    let inner = ChcExpr::Op(ChcOp::And, vec![Arc::new(b), Arc::new(c)]);
    let result = ChcExpr::and_all(vec![a, inner]);
    match result {
        ChcExpr::Op(ChcOp::And, ref args) => assert_eq!(args.len(), 3),
        _ => panic!("expected And with 3 args"),
    }
}

#[test]
fn and_constructor_flattens_chain() {
    let a = ChcExpr::eq(ChcExpr::Int(1), ChcExpr::Int(1));
    let b = ChcExpr::eq(ChcExpr::Int(2), ChcExpr::Int(2));
    let c = ChcExpr::eq(ChcExpr::Int(3), ChcExpr::Int(3));
    let result = ChcExpr::and(ChcExpr::and(a, b), c);
    match result {
        ChcExpr::Op(ChcOp::And, ref args) => assert_eq!(args.len(), 3),
        _ => panic!("expected flattened And"),
    }
}

#[test]
fn and_all_recursively_flattens_deep_left_associated_and() {
    let mut nested = ChcExpr::Bool(true);
    for i in 0..256 {
        let term = ChcExpr::eq(ChcExpr::Int(i), ChcExpr::Int(i));
        nested = ChcExpr::and(nested, term);
    }

    match ChcExpr::and_all(vec![nested]) {
        ChcExpr::Op(ChcOp::And, ref args) => assert_eq!(args.len(), 256),
        _ => panic!("expected And with 256 args"),
    }
}

#[test]
fn or_all_empty() {
    let result = ChcExpr::or_all(Vec::<ChcExpr>::new());
    assert!(matches!(result, ChcExpr::Bool(false)));
}

#[test]
fn or_all_single() {
    let parts = vec![ChcExpr::Bool(true)];
    let result = ChcExpr::or_all(parts);
    assert!(matches!(result, ChcExpr::Bool(true)));
}

#[test]
fn or_all_multiple() {
    let x = ChcVar::new("x", ChcSort::Int);
    let parts = vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(10)),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5)),
    ];
    let result = ChcExpr::or_all(parts);
    assert!(matches!(result, ChcExpr::Op(ChcOp::Or, _)));
}

#[test]
fn or_all_short_circuits_on_true() {
    let parts = vec![
        ChcExpr::Bool(false),
        ChcExpr::Bool(true),
        ChcExpr::eq(ChcExpr::Int(0), ChcExpr::Int(1)),
    ];
    let result = ChcExpr::or_all(parts);
    assert!(matches!(result, ChcExpr::Bool(true)));
}

#[test]
fn or_all_skips_false() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    let parts = vec![ChcExpr::Bool(false), expr.clone(), ChcExpr::Bool(false)];
    let result = ChcExpr::or_all(parts);
    assert_eq!(result, expr);
}

#[test]
fn or_all_flattens_nested_or() {
    let a = ChcExpr::eq(ChcExpr::Int(1), ChcExpr::Int(1));
    let b = ChcExpr::eq(ChcExpr::Int(2), ChcExpr::Int(2));
    let c = ChcExpr::eq(ChcExpr::Int(3), ChcExpr::Int(3));
    let inner = ChcExpr::Op(ChcOp::Or, vec![Arc::new(b), Arc::new(c)]);
    let result = ChcExpr::or_all(vec![a, inner]);
    match result {
        ChcExpr::Op(ChcOp::Or, ref args) => assert_eq!(args.len(), 3),
        _ => panic!("expected Or with 3 args"),
    }
}

#[test]
fn or_constructor_flattens_chain() {
    let a = ChcExpr::eq(ChcExpr::Int(1), ChcExpr::Int(1));
    let b = ChcExpr::eq(ChcExpr::Int(2), ChcExpr::Int(2));
    let c = ChcExpr::eq(ChcExpr::Int(3), ChcExpr::Int(3));
    let result = ChcExpr::or(ChcExpr::or(a, b), c);
    match result {
        ChcExpr::Op(ChcOp::Or, ref args) => assert_eq!(args.len(), 3),
        _ => panic!("expected flattened Or"),
    }
}

#[test]
fn collect_linear_terms_bool_var_fails() {
    let b = ChcVar::new("b", ChcSort::Bool);
    let expr = ChcExpr::var(b);
    assert!(ChcExpr::collect_linear_terms_prod(&expr).is_none());
}

#[test]
fn collect_linear_terms_nested_mul() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mul(
        ChcExpr::Int(2),
        ChcExpr::mul(ChcExpr::Int(3), ChcExpr::var(x)),
    );
    let terms = ChcExpr::collect_linear_terms_prod(&expr).unwrap();
    assert_eq!(coeff(&terms, "x"), 6);
    assert_eq!(terms.constant, 0);
}

#[test]
fn walk_linear_mul_neg_int_constant() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mul(ChcExpr::neg(ChcExpr::Int(3)), ChcExpr::var(x));
    let terms = ChcExpr::collect_linear_terms_prod(&expr).unwrap();
    assert_eq!(coeff(&terms, "x"), -3);
    assert_eq!(terms.constant, 0);
}

#[test]
fn walk_linear_mul_var_neg_int_constant() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mul(ChcExpr::var(x), ChcExpr::neg(ChcExpr::Int(5)));
    let terms = ChcExpr::collect_linear_terms_prod(&expr).unwrap();
    assert_eq!(coeff(&terms, "x"), -5);
    assert_eq!(terms.constant, 0);
}

#[test]
fn walk_linear_variadic_sub() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);
    let expr = ChcExpr::Op(
        ChcOp::Sub,
        vec![
            Arc::new(ChcExpr::var(x)),
            Arc::new(ChcExpr::var(y)),
            Arc::new(ChcExpr::var(z)),
        ],
    );
    let terms = ChcExpr::collect_linear_terms_prod(&expr).unwrap();
    assert_eq!(coeff(&terms, "x"), 1);
    assert_eq!(coeff(&terms, "y"), -1);
    assert_eq!(coeff(&terms, "z"), -1);
    assert_eq!(terms.constant, 0);
}

#[test]
fn walk_linear_overflow_checked_neg_i64_min() {
    // i128-lockstep: checked_neg of an i64::MIN multiplier must still bail
    // (the i64 coefficient lane narrows fail-closed).
    let mut constant = 0i64;
    let result = walk_linear_expr(
        &ChcExpr::Op(
            ChcOp::Sub,
            vec![Arc::new(ChcExpr::Int(0)), Arc::new(ChcExpr::Int(1))],
        ),
        i64::MIN,
        &mut |mult: i64, n: i128| {
            constant =
                constant.checked_add(i64::try_from(i128::from(mult).checked_mul(n)?).ok()?)?;
            Some(())
        },
        &mut |_mult: i64, _v| Some(()),
    );
    assert!(result.is_none());
}

#[test]
fn deep_nesting_collect_conjuncts_no_stack_overflow() {
    let deep = build_genuinely_nested_and_chain(400);

    assert_left_associated_binary_and_depth(&deep, 400);

    let conjuncts = deep.collect_conjuncts();
    assert_eq!(
        conjuncts.len(),
        401,
        "Expected 401 conjuncts from depth-400 AND chain, got {}",
        conjuncts.len()
    );
}

#[test]
fn deep_nesting_sort_no_stack_overflow() {
    let deep = build_genuinely_nested_and_chain(2_000);
    assert_left_associated_binary_and_depth(&deep, 2_000);
    let s = deep.sort();
    assert_eq!(
        s,
        ChcSort::Bool,
        "AND chain should have Bool sort, got {s:?}"
    );
}

#[test]
fn deep_nesting_substitute_no_stack_overflow() {
    let deep = build_genuinely_nested_and_chain(2_000);
    assert_left_associated_binary_and_depth(&deep, 2_000);
    let y = ChcVar::new("y", ChcSort::Int);
    let x = ChcVar::new("x", ChcSort::Int);
    let result = deep.substitute(&[(x, ChcExpr::var(y))]);
    let vars = result.vars();
    assert!(
        vars.iter().all(|v| v.name == "y"),
        "All variables should be 'y' after substitution, found: {vars:?}"
    );
}

#[test]
fn contains_nonlinear_mul_treats_constant_factor_as_linear() {
    let x = ChcVar::new("x", ChcSort::Real);
    // (* (- 1.0) x): the `(- 1.0)` factor has no variables, so the product is
    // linear. Previously misclassified as nonlinear because `(- 1.0)` is
    // `Op(Neg,[Real])` rather than a literal — which wrongly suppressed the
    // executor fallback on cav12/array_max-style LRA queries.
    let neg_one_times_x = ChcExpr::mul(ChcExpr::neg(ChcExpr::Real(1, 1)), ChcExpr::var(x.clone()));
    assert!(
        !neg_one_times_x.contains_nonlinear_mul(),
        "(* (- 1.0) x) is linear (constant * var)"
    );

    // (* 2 x) literal-constant factor stays linear too.
    let two_times_x = ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x.clone()));
    assert!(!two_times_x.contains_nonlinear_mul());

    // (* x x): two variable-bearing factors -> genuinely nonlinear.
    let x_times_x = ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::var(x.clone()));
    assert!(
        x_times_x.contains_nonlinear_mul(),
        "(* x x) is nonlinear (var * var)"
    );

    // (* (+ x 1) x): both factors carry a variable -> nonlinear.
    let y = ChcVar::new("y", ChcSort::Real);
    let sum_times_y = ChcExpr::mul(
        ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(1)),
        ChcExpr::var(y),
    );
    assert!(
        sum_times_y.contains_nonlinear_mul(),
        "(* (+ x 1) y) is nonlinear (both factors have vars)"
    );
}

#[test]
fn test_or_all_dedup_preserves_distinct_disjuncts_9076() {
    // #9076: or_all must dedup by EXACT structural identity, not hash alone.
    // The soundness property: every structurally-DISTINCT disjunct survives
    // (dropping one would weaken the Or — a latent unsat->sat path).
    let x = ChcVar::new("x", ChcSort::Int);
    let mk = |k: i64| ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(k));

    // 5 distinct disjuncts -> all 5 must be present.
    let distinct = ChcExpr::or_all([mk(0), mk(1), mk(2), mk(3), mk(4)]);
    match &distinct {
        ChcExpr::Op(ChcOp::Or, args) => assert_eq!(
            args.len(),
            5,
            "all distinct disjuncts must be preserved, got {args:?}"
        ),
        other => panic!("expected Or of 5 distinct disjuncts, got {other:?}"),
    }

    // Exact duplicates ARE removed (the #5877 optimization still holds).
    let with_dups = ChcExpr::or_all([mk(0), mk(1), mk(0), mk(1), mk(0)]);
    match &with_dups {
        ChcExpr::Op(ChcOp::Or, args) => {
            assert_eq!(
                args.len(),
                2,
                "exact duplicates collapse to 2, got {args:?}"
            )
        }
        other => panic!("expected Or of 2 after dedup, got {other:?}"),
    }

    // Nested Or flattening + dedup across levels.
    let nested = ChcExpr::or_all([ChcExpr::or_all([mk(0), mk(1)]), mk(1), mk(2)]);
    match &nested {
        ChcExpr::Op(ChcOp::Or, args) => {
            assert_eq!(args.len(), 3, "flatten+dedup -> {{0,1,2}}, got {args:?}")
        }
        other => panic!("expected flattened Or of 3, got {other:?}"),
    }
}

/// Independent, from-scratch structural equality (the "ground truth" the custom
/// `PartialEq` in types.rs must match). Deliberately does NOT use `==` (which is
/// the impl under test) and does NOT use `Arc::ptr_eq` — pure structural.
fn reference_eq(a: &ChcExpr, b: &ChcExpr) -> bool {
    use std::sync::Arc;
    fn kids(x: &[Arc<ChcExpr>], y: &[Arc<ChcExpr>]) -> bool {
        x.len() == y.len() && x.iter().zip(y).all(|(p, q)| reference_eq(p, q))
    }
    match (a, b) {
        (ChcExpr::Bool(p), ChcExpr::Bool(q)) => p == q,
        (ChcExpr::Int(p), ChcExpr::Int(q)) => p == q,
        (ChcExpr::Real(pn, pd), ChcExpr::Real(qn, qd)) => pn == qn && pd == qd,
        (ChcExpr::BitVec(pv, pw), ChcExpr::BitVec(qv, qw)) => pv == qv && pw == qw,
        (ChcExpr::Var(p), ChcExpr::Var(q)) => p == q,
        (ChcExpr::Op(po, pa), ChcExpr::Op(qo, qa)) => po == qo && kids(pa, qa),
        (ChcExpr::PredicateApp(pn, pi, pa), ChcExpr::PredicateApp(qn, qi, qa)) => {
            pi == qi && pn == qn && kids(pa, qa)
        }
        (ChcExpr::FuncApp(pn, ps, pa), ChcExpr::FuncApp(qn, qs, qa)) => {
            pn == qn && ps == qs && kids(pa, qa)
        }
        (ChcExpr::ConstArrayMarker(p), ChcExpr::ConstArrayMarker(q)) => p == q,
        (ChcExpr::IsTesterMarker(p), ChcExpr::IsTesterMarker(q)) => p == q,
        (ChcExpr::ConstArray(ps, pv), ChcExpr::ConstArray(qs, qv)) => {
            ps == qs && reference_eq(pv, qv)
        }
        _ => false,
    }
}

/// Build a deterministic, diverse corpus of expressions (leaves + nested ops +
/// apps + arrays + markers). Each call rebuilds with FRESH Arcs (no sharing),
/// so the corpus exercises the custom Eq's *structural fallback* path.
fn eq_corpus() -> Vec<ChcExpr> {
    let xi = ChcVar::new("x", ChcSort::Int);
    let yr = ChcVar::new("y", ChcSort::Real);
    let arr = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let leaves = vec![
        ChcExpr::Bool(true),
        ChcExpr::Bool(false),
        ChcExpr::Int(0),
        ChcExpr::Int(1),
        ChcExpr::Int(-1),
        ChcExpr::Real(1, 2),
        ChcExpr::Real(2, 4), // structurally distinct from 1/2
        ChcExpr::BitVec(5, 8),
        ChcExpr::BitVec(5, 16), // same value, different width
        ChcExpr::var(xi.clone()),
        ChcExpr::var(yr.clone()),
    ];
    let mut out = leaves.clone();
    // unary / binary / ternary ops over leaves
    out.push(ChcExpr::not(ChcExpr::Bool(true)));
    out.push(ChcExpr::add(ChcExpr::var(xi.clone()), ChcExpr::Int(1)));
    out.push(ChcExpr::add(ChcExpr::Int(1), ChcExpr::var(xi.clone()))); // arg order matters
    out.push(ChcExpr::le(ChcExpr::var(xi.clone()), ChcExpr::Int(7)));
    out.push(ChcExpr::le(ChcExpr::var(xi.clone()), ChcExpr::Int(8)));
    out.push(ChcExpr::and(
        ChcExpr::le(ChcExpr::var(xi.clone()), ChcExpr::Int(7)),
        ChcExpr::Bool(true),
    ));
    out.push(ChcExpr::ite(
        ChcExpr::Bool(true),
        ChcExpr::var(xi.clone()),
        ChcExpr::Int(0),
    ));
    out.push(ChcExpr::select(ChcExpr::var(arr.clone()), ChcExpr::Int(3)));
    out.push(ChcExpr::store(
        ChcExpr::var(arr.clone()),
        ChcExpr::Int(3),
        ChcExpr::Int(9),
    ));
    // nested
    out.push(ChcExpr::and(
        ChcExpr::le(ChcExpr::var(xi.clone()), ChcExpr::Int(7)),
        ChcExpr::le(ChcExpr::var(yr.clone()), ChcExpr::Real(1, 2)),
    ));
    // markers + const array
    out.push(ChcExpr::ConstArrayMarker(ChcSort::Int));
    out.push(ChcExpr::IsTesterMarker("Cons".to_string()));
    out.push(ChcExpr::ConstArray(
        ChcSort::Int,
        std::sync::Arc::new(ChcExpr::Int(0)),
    ));
    out
}

#[test]
fn test_custom_eq_matches_reference_structural_eq_9077() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let corpus = eq_corpus();
    let h = |e: &ChcExpr| {
        let mut s = DefaultHasher::new();
        e.hash(&mut s);
        s.finish()
    };
    for a in &corpus {
        // Reflexivity.
        assert!(a == a, "reflexivity failed for {a:?}");
        for b in &corpus {
            let custom = a == b;
            let reference = reference_eq(a, b);
            // (1) custom PartialEq is EXACTLY structural eq.
            assert_eq!(
                custom, reference,
                "custom eq != structural eq for\n {a:?}\n {b:?}"
            );
            // (2) symmetry.
            assert_eq!(a == b, b == a, "symmetry failed");
            // (3) Hash consistency: a == b => hash(a) == hash(b).
            if custom {
                assert_eq!(h(a), h(b), "a==b but hashes differ");
            }
            // (4) Ord consistency: a == b  <=>  cmp == Equal.
            assert_eq!(
                custom,
                a.cmp(b) == std::cmp::Ordering::Equal,
                "Eq/Ord disagree for\n {a:?}\n {b:?}"
            );
        }
    }
}

#[test]
fn test_custom_eq_ptr_eq_fastpath_and_fallback_9077() {
    use std::sync::Arc;
    // Two structurally-equal Ops built with DISTINCT child Arcs (fallback path).
    let mk = || {
        ChcExpr::Op(
            ChcOp::Le,
            vec![
                Arc::new(ChcExpr::var(ChcVar::new("z", ChcSort::Int))),
                Arc::new(ChcExpr::Int(42)),
            ],
        )
    };
    let a = mk();
    let b = mk();
    assert!(a == b, "structural fallback must find distinct-Arc equals");

    // SHARED child Arcs (ptr-eq fast path) — must also be equal, same result.
    let shared = Arc::new(ChcExpr::var(ChcVar::new("z", ChcSort::Int)));
    let c = ChcExpr::Op(ChcOp::Le, vec![shared.clone(), Arc::new(ChcExpr::Int(42))]);
    let d = ChcExpr::Op(ChcOp::Le, vec![shared, Arc::new(ChcExpr::Int(42))]);
    assert!(c == d, "ptr-eq fast path must agree with structural eq");
    assert!(a == c, "distinct-Arc and shared-Arc versions are equal");
}
