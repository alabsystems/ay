// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;

/// Build a pathologically deep expression tree with 2^depth nodes.
fn build_deep_tree(depth: u32) -> ChcExpr {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut expr = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0));
    for _ in 0..depth {
        expr = ChcExpr::and(expr.clone(), expr);
    }
    expr
}

#[test]
fn test_node_count_small() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0)),
    );
    assert_eq!(expr.node_count(100), 7);
}

#[test]
fn test_node_count_stops_at_limit() {
    let tree = build_deep_tree(21);
    let count = tree.node_count(1000);
    assert_eq!(count, 1000);
}

#[test]
fn test_eliminate_ite_budget_does_not_crash() {
    let x = ChcVar::new("x", ChcSort::Int);
    let ite = ChcExpr::ite(ChcExpr::Bool(true), ChcExpr::var(x), ChcExpr::int(0));
    let leaf = ChcExpr::le(ite, ChcExpr::int(5));
    let mut expr = leaf;
    for _ in 0..21 {
        expr = ChcExpr::and(expr.clone(), expr);
    }
    let _result = expr.eliminate_ite();
}

#[test]
fn test_eliminate_mod_budget_does_not_crash() {
    let x = ChcVar::new("x", ChcSort::Int);
    let modexpr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(3))],
    );
    let leaf = ChcExpr::le(modexpr, ChcExpr::int(2));
    let mut expr = leaf;
    for _ in 0..21 {
        expr = ChcExpr::and(expr.clone(), expr);
    }
    let _result = expr.eliminate_mod();
}

#[test]
fn test_substitute_map_budget_does_not_crash() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let mut expr = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0));
    for _ in 0..21 {
        expr = ChcExpr::and(expr.clone(), expr);
    }
    let subst = vec![(x, ChcExpr::var(y))];
    let _result = expr.substitute(&subst);
}

#[test]
fn test_substitute_name_map_rewrites_nested_nodes() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let expr = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1))),
            Arc::new(ChcExpr::PredicateApp(
                "P".to_string(),
                PredicateId::new(7),
                vec![Arc::new(ChcExpr::var(x.clone())), Arc::new(ChcExpr::var(y))],
            )),
            Arc::new(ChcExpr::ConstArray(
                ChcSort::Int,
                Arc::new(ChcExpr::var(x.clone())),
            )),
        ],
    );

    let mut map = FxHashMap::default();
    map.insert(x.name, ChcExpr::add(ChcExpr::var(z), ChcExpr::int(2)));

    let rewritten = expr.substitute_name_map(&map);

    let expected = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::eq(
                ChcExpr::add(
                    ChcExpr::var(ChcVar::new("z", ChcSort::Int)),
                    ChcExpr::int(2),
                ),
                ChcExpr::int(1),
            )),
            Arc::new(ChcExpr::PredicateApp(
                "P".to_string(),
                PredicateId::new(7),
                vec![
                    Arc::new(ChcExpr::add(
                        ChcExpr::var(ChcVar::new("z", ChcSort::Int)),
                        ChcExpr::int(2),
                    )),
                    Arc::new(ChcExpr::var(ChcVar::new("y", ChcSort::Int))),
                ],
            )),
            Arc::new(ChcExpr::ConstArray(
                ChcSort::Int,
                Arc::new(ChcExpr::add(
                    ChcExpr::var(ChcVar::new("z", ChcSort::Int)),
                    ChcExpr::int(2),
                )),
            )),
        ],
    );

    assert_eq!(rewritten, expected);
}

#[test]
fn test_substitute_name_map_budget_does_not_crash() {
    let mut expr = ChcExpr::le(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(0),
    );
    for _ in 0..21 {
        expr = ChcExpr::and(expr.clone(), expr);
    }

    let mut map = FxHashMap::default();
    map.insert(
        "x".to_string(),
        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
    );

    let _result = expr.substitute_name_map(&map);
}

#[test]
fn test_eliminate_ite_small_expression_still_works() {
    let x = ChcVar::new("x", ChcSort::Int);
    let ite = ChcExpr::ite(
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::int(1),
        ChcExpr::int(2),
    );
    let expr = ChcExpr::eq(ChcExpr::var(x), ite);
    let result = expr.eliminate_ite();
    assert!(!matches!(result, ChcExpr::Op(ChcOp::Eq, _)));
}

#[test]
fn test_eliminate_mod_small_expression_still_works() {
    let x = ChcVar::new("x", ChcSort::Int);
    let modexpr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(3))],
    );
    let result = modexpr.eliminate_mod();
    assert!(matches!(
        result,
        ChcExpr::Var(_) | ChcExpr::Op(ChcOp::And, _)
    ));
}

#[test]
fn test_eliminate_mod_product_divisor_expression() {
    let x = ChcVar::new("x", ChcSort::Int);
    let pow2_64 = ChcExpr::mul(
        ChcExpr::int(4_294_967_296_i64),
        ChcExpr::int(4_294_967_296_i64),
    );
    let modexpr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(pow2_64)],
    );

    let result = modexpr.eliminate_mod();

    assert!(
        !result.contains_mod_or_div(),
        "product-shaped constant divisors should be eliminated, got {result}"
    );
}

#[test]
fn test_eliminate_div_product_divisor_expression() {
    let x = ChcVar::new("x", ChcSort::Int);
    let pow2_63 = ChcExpr::mul(
        ChcExpr::int(4_294_967_296_i64),
        ChcExpr::int(2_147_483_648_i64),
    );
    let divexpr = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(pow2_63)],
    );

    let result = divexpr.eliminate_mod();

    assert!(
        !result.contains_mod_or_div(),
        "product-shaped constant divisors should be eliminated, got {result}"
    );
}

#[test]
fn test_simplify_constants_budget_does_not_crash() {
    let tree = build_deep_tree(21);
    let _result = tree.simplify_constants();
}

#[test]
fn test_simplify_constants_depth_limit_returns_original_deep_suffix() {
    let mut expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::int(7)), Arc::new(ChcExpr::int(3))],
    );
    for _ in 0..(MAX_EXPR_RECURSION_DEPTH + 8) {
        expr = ChcExpr::ConstArray(ChcSort::Int, Arc::new(expr));
    }

    let simplified = expr.simplify_constants();
    assert_eq!(simplified, expr);
}

#[test]
fn test_expr_recursion_depth_bound_caps_stacker_heap_below_two_gib() {
    let max_stacker_heap_bytes =
        (MAX_EXPR_RECURSION_DEPTH as u64).saturating_mul(EXPR_STACK_SIZE as u64);
    assert!(
        max_stacker_heap_bytes <= 2 * 1024 * 1024 * 1024,
        "depth={MAX_EXPR_RECURSION_DEPTH} and stack={EXPR_STACK_SIZE} bytes exceed 2 GiB cap ({max_stacker_heap_bytes} bytes)"
    );
}

#[test]
fn test_simplify_constants_small_expression_still_works() {
    let expr = ChcExpr::add(ChcExpr::int(1), ChcExpr::int(2));
    let result = expr.simplify_constants();
    assert_eq!(result, ChcExpr::Int(3));
}

#[test]
fn test_simplify_constants_mod_still_works() {
    let expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::int(7)), Arc::new(ChcExpr::int(3))],
    );
    let result = expr.simplify_constants();
    assert_eq!(result, ChcExpr::Int(1));
}

#[test]
fn test_simplify_constants_implies_false_is_true() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::implies(
        ChcExpr::Bool(false),
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
    );
    assert_eq!(expr.simplify_constants(), ChcExpr::Bool(true));
}

#[test]
fn test_simplify_constants_implies_true_returns_body() {
    let x = ChcVar::new("x", ChcSort::Int);
    let body = ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10));
    let expr = ChcExpr::implies(ChcExpr::Bool(true), body.clone());
    assert_eq!(expr.simplify_constants(), body);
}

#[test]
fn test_simplify_constants_implies_false_rhs_negates_lhs() {
    let x = ChcVar::new("x", ChcSort::Bool);
    let expr = ChcExpr::implies(ChcExpr::var(x), ChcExpr::Bool(false));
    assert_eq!(
        expr.simplify_constants(),
        ChcExpr::not(ChcExpr::var(ChcVar::new("x", ChcSort::Bool)))
    );
}

#[test]
fn test_simplify_constants_implies_inactive_singleloop_branch_drops_alien_vars() {
    let own = ChcVar::new("v0", ChcSort::Int);
    let alien = ChcVar::new(".arg_1_0", ChcSort::Int);
    let expr = ChcExpr::and(
        ChcExpr::implies(
            ChcExpr::Bool(true),
            ChcExpr::lt(ChcExpr::var(own.clone()), ChcExpr::int(10)),
        ),
        ChcExpr::implies(
            ChcExpr::Bool(false),
            ChcExpr::lt(ChcExpr::var(alien), ChcExpr::int(10)),
        ),
    );
    let simplified = expr.simplify_constants();
    assert_eq!(
        simplified,
        ChcExpr::lt(ChcExpr::var(own.clone()), ChcExpr::int(10))
    );
    assert_eq!(simplified.vars(), vec![own]);
}

#[test]
fn test_smt_euclid_div_mod_all_sign_combos() {
    assert_eq!(smt_euclid_div(7, 2), Some(3));
    assert_eq!(smt_euclid_mod(7, 2), Some(1));
    assert_eq!(smt_euclid_div(-7, 2), Some(-4));
    assert_eq!(smt_euclid_mod(-7, 2), Some(1));
    assert_eq!(smt_euclid_div(7, -2), Some(-3));
    assert_eq!(smt_euclid_mod(7, -2), Some(1));
    assert_eq!(smt_euclid_div(-7, -2), Some(4));
    assert_eq!(smt_euclid_mod(-7, -2), Some(1));
    assert_eq!(smt_euclid_div(-6, 3), Some(-2));
    assert_eq!(smt_euclid_mod(-6, 3), Some(0));
    assert_eq!(smt_euclid_div(7, 0), None);
    assert_eq!(smt_euclid_mod(7, 0), None);
    // i128-lockstep: the overflow edge moved to the i128 boundary.
    assert_eq!(smt_euclid_div(i128::MIN, -1), None);
    assert_eq!(smt_euclid_mod(i128::MIN, -1), None);
    // i64::MIN / -1 now folds exactly in the widened domain.
    assert_eq!(
        smt_euclid_div(i128::from(i64::MIN), -1),
        Some(-i128::from(i64::MIN))
    );

    for &(a, b) in &[(7, 2), (-7, 2), (7, -2), (-7, -2), (0, 5), (1, 1)] {
        let q = smt_euclid_div(a, b).unwrap();
        let r = smt_euclid_mod(a, b).unwrap();
        assert_eq!(a, b * q + r, "invariant: {a} = {b} * {q} + {r}");
        assert!(
            r >= 0,
            "remainder must be non-negative: mod({a}, {b}) = {r}"
        );
        assert!(
            r < b.saturating_abs(),
            "remainder must be < |b|: mod({a}, {b}) = {r}"
        );
    }
}

#[test]
fn test_simplify_constants_div_negative_operands() {
    let expr = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::int(-7)), Arc::new(ChcExpr::int(-2))],
    );
    assert_eq!(expr.simplify_constants(), ChcExpr::Int(4));

    let expr = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::int(-7)), Arc::new(ChcExpr::int(2))],
    );
    assert_eq!(expr.simplify_constants(), ChcExpr::Int(-4));
}

#[test]
fn test_simplify_constants_mod_negative_operands() {
    let expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::int(-7)), Arc::new(ChcExpr::int(2))],
    );
    assert_eq!(expr.simplify_constants(), ChcExpr::Int(1));

    let expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::int(-7)), Arc::new(ChcExpr::int(-2))],
    );
    assert_eq!(expr.simplify_constants(), ChcExpr::Int(1));
}

#[test]
fn test_simplify_constants_large_nonnegative_mod_expression() {
    let width = ChcExpr::int(4_294_967_296_i64);
    let huge_modulus = ChcExpr::Op(
        ChcOp::Mul,
        vec![Arc::new(width.clone()), Arc::new(width.clone())],
    );
    let shifted = ChcExpr::Op(
        ChcOp::Add,
        vec![
            Arc::new(ChcExpr::Op(
                ChcOp::Mul,
                vec![Arc::new(ChcExpr::int(2)), Arc::new(width.clone())],
            )),
            Arc::new(ChcExpr::int(0)),
        ],
    );
    let wrapped = ChcExpr::Op(
        ChcOp::Mod,
        vec![
            Arc::new(ChcExpr::Op(
                ChcOp::Mod,
                vec![Arc::new(shifted), Arc::new(huge_modulus)],
            )),
            Arc::new(width),
        ],
    );

    assert_eq!(wrapped.simplify_constants(), ChcExpr::Int(0));
}

fn option_bool_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "Option_bool".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "None_Option_bool".to_string(),
                selectors: vec![],
            },
            ChcDtConstructor {
                name: "Some_Option_bool".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "value_Option_bool".to_string(),
                    sort: ChcSort::Bool,
                }],
            },
        ]),
    }
}

fn option_none(sort: ChcSort) -> ChcExpr {
    ChcExpr::FuncApp("None_Option_bool".to_string(), sort, vec![])
}

fn option_some(sort: ChcSort, value: ChcExpr) -> ChcExpr {
    ChcExpr::FuncApp("Some_Option_bool".to_string(), sort, vec![Arc::new(value)])
}

fn option_selector_term(sort: ChcSort, source: ChcExpr) -> ChcExpr {
    ChcExpr::FuncApp("next_option".to_string(), sort, vec![Arc::new(source)])
}

#[test]
fn test_simplify_constants_bool_equality_and_double_not() {
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let expr = ChcExpr::not(ChcExpr::eq(
        ChcExpr::not(ChcExpr::var(flag.clone())),
        ChcExpr::Bool(true),
    ));

    assert_eq!(expr.simplify_constants(), ChcExpr::var(flag));
}

#[test]
fn test_simplify_constants_datatype_constructor_equality() {
    let sort = option_bool_sort();
    let eq = ChcExpr::eq(
        option_some(sort.clone(), ChcExpr::Bool(false)),
        option_some(sort.clone(), ChcExpr::Bool(true)),
    );
    let ne_ctor = ChcExpr::eq(
        option_none(sort.clone()),
        option_some(sort, ChcExpr::Bool(false)),
    );

    assert_eq!(eq.simplify_constants(), ChcExpr::Bool(false));
    assert_eq!(ne_ctor.simplify_constants(), ChcExpr::Bool(false));
}

#[test]
fn test_simplify_constants_keeps_datatype_returning_function_equality() {
    let sort = option_bool_sort();
    let source = ChcExpr::var(ChcVar::new("source", ChcSort::Int));
    let selector_like = option_selector_term(sort.clone(), source);
    let eq = ChcExpr::eq(
        selector_like.clone(),
        option_some(sort, ChcExpr::Bool(true)),
    );

    assert_eq!(
        eq.simplify_constants(),
        ChcExpr::eq(
            selector_like,
            option_some(option_bool_sort(), ChcExpr::Bool(true))
        )
    );
}

#[test]
fn test_simplify_constants_datatype_selector_projection() {
    let sort = option_bool_sort();
    let selector = ChcExpr::FuncApp(
        "value_Option_bool".to_string(),
        ChcSort::Bool,
        vec![Arc::new(option_some(sort, ChcExpr::Bool(true)))],
    );

    assert_eq!(selector.simplify_constants(), ChcExpr::Bool(true));
}

#[test]
fn test_simplify_constants_datatype_tester_on_constructor() {
    let sort = option_bool_sort();
    let tester = ChcExpr::FuncApp(
        "is-Some_Option_bool".to_string(),
        ChcSort::Bool,
        vec![Arc::new(option_none(sort))],
    );

    assert_eq!(tester.simplify_constants(), ChcExpr::Bool(false));
}

#[test]
fn test_simplify_constants_keeps_tester_on_datatype_returning_function() {
    let sort = option_bool_sort();
    let source = ChcExpr::var(ChcVar::new("source", ChcSort::Int));
    let selector_like = option_selector_term(sort, source);
    let tester = ChcExpr::FuncApp(
        "is-Some_Option_bool".to_string(),
        ChcSort::Bool,
        vec![Arc::new(selector_like.clone())],
    );

    assert_eq!(
        tester.simplify_constants(),
        ChcExpr::FuncApp(
            "is-Some_Option_bool".to_string(),
            ChcSort::Bool,
            vec![Arc::new(selector_like)]
        )
    );
}

#[test]
fn test_simplify_constants_lifts_equality_over_datatype_ite() {
    let sort = option_bool_sort();
    let present = ChcVar::new("present", ChcSort::Bool);
    let idx = ChcVar::new("idx", ChcSort::Int);
    let idx_is_one = ChcExpr::eq(ChcExpr::var(idx.clone()), ChcExpr::int(1));

    let expr = ChcExpr::not(ChcExpr::eq(
        ChcExpr::ite(
            ChcExpr::var(present.clone()),
            option_some(sort.clone(), ChcExpr::Bool(false)),
            option_none(sort.clone()),
        ),
        option_some(sort, idx_is_one.clone()),
    ));

    assert_eq!(
        expr.simplify_constants(),
        ChcExpr::ite(ChcExpr::var(present), idx_is_one, ChcExpr::Bool(true))
    );
}

#[test]
fn test_simplify_constants_bv_urem_drops_constant_alignment_guard_1753() {
    let addr32 = ChcExpr::Op(
        ChcOp::BvExtract(31, 0),
        vec![Arc::new(ChcExpr::Op(
            ChcOp::BvConcat,
            vec![
                Arc::new(ChcExpr::BitVec(0x0000_0002, 32)),
                Arc::new(ChcExpr::BitVec(0x0000_0000, 32)),
            ],
        ))],
    );
    let guard = ChcExpr::not(ChcExpr::eq(
        ChcExpr::Op(
            ChcOp::BvURem,
            vec![Arc::new(addr32), Arc::new(ChcExpr::BitVec(4, 32))],
        ),
        ChcExpr::BitVec(0, 32),
    ));

    assert_eq!(guard.simplify_constants(), ChcExpr::Bool(false));
}

#[test]
fn test_simplify_constants_bv_udiv_by_zero_uses_smtlib_semantics_1753() {
    let expr = ChcExpr::Op(
        ChcOp::BvUDiv,
        vec![
            Arc::new(ChcExpr::BitVec(5, 8)),
            Arc::new(ChcExpr::BitVec(0, 8)),
        ],
    );

    assert_eq!(expr.simplify_constants(), ChcExpr::BitVec(0xFF, 8));
}

#[test]
fn test_simplify_constants_bv_urem_by_zero_returns_dividend_1753() {
    let expr = ChcExpr::Op(
        ChcOp::BvURem,
        vec![
            Arc::new(ChcExpr::BitVec(5, 8)),
            Arc::new(ChcExpr::BitVec(0, 8)),
        ],
    );

    assert_eq!(expr.simplify_constants(), ChcExpr::BitVec(5, 8));
}

#[test]
fn simplify_constants_bv2nat_literal_folds_to_int_9004() {
    let expr = ChcExpr::Op(ChcOp::Bv2Nat, vec![Arc::new(ChcExpr::BitVec(1, 32))]);
    assert_eq!(expr.simplify_constants(), ChcExpr::Int(1));
}

#[test]
fn simplify_constants_div_large_product_divisor_folds_9604() {
    let divisor = ChcExpr::mul(
        ChcExpr::int(4_294_967_296_i64),
        ChcExpr::int(2_147_483_648_i64),
    );
    let expr = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::int(1)), Arc::new(divisor)],
    );

    assert_eq!(expr.simplify_constants(), ChcExpr::Int(0));
}

#[test]
fn simplify_constants_ite_with_large_product_divisor_condition_9604() {
    let divisor = ChcExpr::mul(
        ChcExpr::int(4_294_967_296_i64),
        ChcExpr::int(2_147_483_648_i64),
    );
    let condition = ChcExpr::eq(
        ChcExpr::Op(
            ChcOp::Div,
            vec![Arc::new(ChcExpr::int(1)), Arc::new(divisor)],
        ),
        ChcExpr::int(1),
    );
    let expr = ChcExpr::ite(condition, ChcExpr::Bool(true), ChcExpr::Bool(false));

    assert_eq!(expr.simplify_constants(), ChcExpr::Bool(false));
}

#[test]
fn test_normalize_strict_int_comparisons_budget_does_not_crash() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut expr = ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(5));
    for _ in 0..21 {
        expr = ChcExpr::and(expr.clone(), expr);
    }
    let _result = expr.normalize_strict_int_comparisons();
}

#[test]
fn test_normalize_strict_int_comparisons_small_still_works() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let result = expr.normalize_strict_int_comparisons();
    assert_eq!(result, ChcExpr::le(ChcExpr::var(x), ChcExpr::int(4)));
}

#[test]
fn test_normalize_strict_int_comparisons_depth_guard_keeps_deep_suffix_unmodified() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let mut expr = ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(5));
    let depth = MAX_EXPR_RECURSION_DEPTH + 16;
    for _ in 0..depth {
        expr = ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0))),
                Arc::new(expr),
            ],
        );
    }
    let normalized = expr.normalize_strict_int_comparisons();
    let deep_leaf = right_leaf_of_left_associated_and_chain(&normalized, depth);
    assert!(
        matches!(deep_leaf, ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2),
        "deep suffix should stay unnormalized once depth guard triggers: {deep_leaf:?}"
    );
}

#[test]
fn depth_tracking_increments_and_decrements() {
    assert_eq!(expr_depth(), 0);

    maybe_grow_expr_stack(|| {
        assert_eq!(expr_depth(), 1);

        maybe_grow_expr_stack(|| {
            assert_eq!(expr_depth(), 2);
        });

        assert_eq!(expr_depth(), 1);
    });

    assert_eq!(expr_depth(), 0);
}

#[test]
fn depth_guard_returns_some_within_limit() {
    assert_eq!(expr_depth(), 0);
    let guard = ExprDepthGuard::check();
    assert!(guard.is_some());
}

#[test]
fn depth_guard_returns_none_at_limit() {
    fn recurse(depth: usize) -> bool {
        maybe_grow_expr_stack(|| {
            if depth + 1 >= MAX_EXPR_RECURSION_DEPTH {
                ExprDepthGuard::check().is_none()
            } else {
                recurse(depth + 1)
            }
        })
    }
    assert!(recurse(0));
}

#[test]
fn stacker_stops_growing_beyond_limit() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut expr = ChcExpr::var(x);
    for _ in 0..600 {
        expr = ChcExpr::Op(ChcOp::Neg, vec![Arc::new(expr)]);
    }

    let empty_map: FxHashMap<&ChcVar, &ChcExpr> = Default::default();
    let result = expr.substitute_map(&empty_map);
    assert_eq!(result.to_string().len(), expr.to_string().len());
}

#[test]
fn simplify_constants_bounded_on_deep_expression() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut expr = ChcExpr::var(x);
    for _ in 0..600 {
        expr = ChcExpr::Op(ChcOp::Neg, vec![Arc::new(expr)]);
    }

    let result = expr.simplify_constants();
    assert!(!result.to_string().is_empty());
}

#[test]
fn simplify_constants_add_coeff_mul_overflow_bails() {
    let expr = ChcExpr::Op(
        ChcOp::Add,
        vec![
            Arc::new(ChcExpr::Int(i128::MAX)),
            Arc::new(ChcExpr::Int(i128::MAX)),
        ],
    );
    let result = expr.simplify_constants();
    if let ChcExpr::Int(n) = &result {
        panic!("should not fold to Int({n}) — sum overflows i128");
    }
}

#[test]
fn simplify_constants_mul_overflow_bails() {
    let expr = ChcExpr::Op(
        ChcOp::Mul,
        vec![Arc::new(ChcExpr::Int(i128::MAX)), Arc::new(ChcExpr::Int(2))],
    );
    let result = expr.simplify_constants();
    match &result {
        ChcExpr::Op(ChcOp::Mul, _) => {}
        ChcExpr::Int(n) => panic!("should not fold to Int({n}) — product overflows i128"),
        other => panic!("unexpected result: {other}"),
    }
}

#[test]
fn simplify_constants_sub_overflow_bails() {
    let expr = ChcExpr::Op(
        ChcOp::Sub,
        vec![Arc::new(ChcExpr::Int(i128::MIN)), Arc::new(ChcExpr::Int(1))],
    );
    let result = expr.simplify_constants();
    match &result {
        ChcExpr::Op(ChcOp::Sub, _) => {}
        ChcExpr::Int(n) => panic!("should not fold to Int({n}) — difference overflows i128"),
        other => panic!("unexpected result: {other}"),
    }
}

#[test]
fn simplify_constants_neg_overflow_bails() {
    let expr = ChcExpr::Op(ChcOp::Neg, vec![Arc::new(ChcExpr::Int(i128::MIN))]);
    let result = expr.simplify_constants();
    match &result {
        ChcExpr::Op(ChcOp::Neg, _) => {}
        ChcExpr::Int(n) => panic!("should not fold to Int({n}) — negation overflows i128"),
        other => panic!("unexpected result: {other}"),
    }
}

#[test]
fn simplify_constants_sub_neg_coeff_overflow_preserves_sign() {
    let expr = ChcExpr::Op(
        ChcOp::Sub,
        vec![Arc::new(ChcExpr::Int(0)), Arc::new(ChcExpr::Int(i128::MIN))],
    );
    let result = expr.simplify_constants();
    match &result {
        ChcExpr::Int(n) if *n == i128::MIN => {
            panic!("bailout lost negation: got Int(i128::MIN) instead of Neg(Int(i128::MIN))")
        }
        _ => {}
    }
}

#[test]
fn simplify_constants_mul_no_overflow_still_folds() {
    let expr = ChcExpr::Op(
        ChcOp::Mul,
        vec![Arc::new(ChcExpr::Int(3)), Arc::new(ChcExpr::Int(7))],
    );
    assert_eq!(expr.simplify_constants(), ChcExpr::Int(21));
}

#[test]
fn simplify_constants_sub_no_overflow_still_folds() {
    let expr = ChcExpr::Op(
        ChcOp::Sub,
        vec![Arc::new(ChcExpr::Int(10)), Arc::new(ChcExpr::Int(3))],
    );
    assert_eq!(expr.simplify_constants(), ChcExpr::Int(7));
}

/// Wishlist rank 3 (2026-07-08): division by a power-of-two constant rewrites
/// to shift/mask — exact SMT-LIB equivalences — so `bvudiv`/`bvurem` never
/// survive into lanes that abstract them to havoc bits (the safe-midpoint
/// `x / 2` class).
#[test]
fn test_bvudiv_by_pow2_rewrites_to_lshr() {
    use std::sync::Arc;
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(128)));
    let div = ChcExpr::Op(
        ChcOp::BvUDiv,
        vec![Arc::new(x.clone()), Arc::new(ChcExpr::BitVec(2, 128))],
    );
    let simplified = div.simplify_constants();
    match &simplified {
        ChcExpr::Op(ChcOp::BvLShr, args) => {
            assert_eq!(args[0].as_ref(), &x);
            assert_eq!(
                args[1].as_ref(),
                &ChcExpr::BitVec(1, 128),
                "2 = 2^1 → shift by 1"
            );
        }
        other => panic!("bvudiv(x, 2) must rewrite to bvlshr(x, 1), got {other:?}"),
    }
}

#[test]
fn test_bvurem_by_pow2_rewrites_to_mask() {
    use std::sync::Arc;
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)));
    let rem = ChcExpr::Op(
        ChcOp::BvURem,
        vec![Arc::new(x.clone()), Arc::new(ChcExpr::BitVec(8, 8))],
    );
    let simplified = rem.simplify_constants();
    match &simplified {
        ChcExpr::Op(ChcOp::BvAnd, args) => {
            assert_eq!(args[0].as_ref(), &x);
            assert_eq!(
                args[1].as_ref(),
                &ChcExpr::BitVec(7, 8),
                "mod 8 → mask 0b111"
            );
        }
        other => panic!("bvurem(x, 8) must rewrite to bvand(x, 7), got {other:?}"),
    }
}

/// Literal/literal division still constant-folds (takes precedence over the
/// pow2 rewrite), and a NON-power-of-two constant divisor keeps the division op
/// (no unsound generalization of the rewrite).
#[test]
fn test_bvudiv_pow2_rewrite_scoping() {
    use std::sync::Arc;
    let folded = ChcExpr::Op(
        ChcOp::BvUDiv,
        vec![
            Arc::new(ChcExpr::BitVec(6, 8)),
            Arc::new(ChcExpr::BitVec(2, 8)),
        ],
    )
    .simplify_constants();
    assert_eq!(
        folded,
        ChcExpr::BitVec(3, 8),
        "constant fold takes precedence"
    );

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)));
    let non_pow2 = ChcExpr::Op(
        ChcOp::BvUDiv,
        vec![Arc::new(x), Arc::new(ChcExpr::BitVec(3, 8))],
    )
    .simplify_constants();
    assert!(
        matches!(&non_pow2, ChcExpr::Op(ChcOp::BvUDiv, _)),
        "non-pow2 divisor must keep the division op, got {non_pow2:?}"
    );
}
