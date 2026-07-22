// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

// --- parse_linear_expr_alg ---

#[test]
fn parse_linear_expr_constant() {
    let (coeffs, constant) = PdrSolver::parse_linear_expr_alg(&ChcExpr::int(42)).unwrap();
    assert!(coeffs.is_empty());
    assert_eq!(constant, 42);
}

#[test]
fn parse_linear_expr_variable() {
    let (coeffs, constant) = PdrSolver::parse_linear_expr_alg(&var("x")).unwrap();
    assert_eq!(coeffs.len(), 1);
    assert_eq!(coeffs["x"], 1);
    assert_eq!(constant, 0);
}

#[test]
fn parse_linear_expr_add() {
    // x + y + 3
    let expr = ChcExpr::add(ChcExpr::add(var("x"), var("y")), ChcExpr::int(3));
    let (coeffs, constant) = PdrSolver::parse_linear_expr_alg(&expr).unwrap();
    assert_eq!(coeffs["x"], 1);
    assert_eq!(coeffs["y"], 1);
    assert_eq!(constant, 3);
}

#[test]
fn parse_linear_expr_sub() {
    // x - y
    let expr = ChcExpr::sub(var("x"), var("y"));
    let (coeffs, constant) = PdrSolver::parse_linear_expr_alg(&expr).unwrap();
    assert_eq!(coeffs["x"], 1);
    assert_eq!(coeffs["y"], -1);
    assert_eq!(constant, 0);
}

#[test]
fn parse_linear_expr_scalar_mul() {
    // 3 * x
    let expr = ChcExpr::mul(ChcExpr::int(3), var("x"));
    let (coeffs, constant) = PdrSolver::parse_linear_expr_alg(&expr).unwrap();
    assert_eq!(coeffs["x"], 3);
    assert_eq!(constant, 0);
}

#[test]
fn parse_linear_expr_neg() {
    // -x
    let expr = ChcExpr::neg(var("x"));
    let (coeffs, constant) = PdrSolver::parse_linear_expr_alg(&expr).unwrap();
    assert_eq!(coeffs["x"], -1);
    assert_eq!(constant, 0);
}

#[test]
fn parse_linear_expr_complex() {
    // 2*x - 3*y + 5
    let expr = ChcExpr::add(
        ChcExpr::sub(
            ChcExpr::mul(ChcExpr::int(2), var("x")),
            ChcExpr::mul(ChcExpr::int(3), var("y")),
        ),
        ChcExpr::int(5),
    );
    let (coeffs, constant) = PdrSolver::parse_linear_expr_alg(&expr).unwrap();
    assert_eq!(coeffs["x"], 2);
    assert_eq!(coeffs["y"], -3);
    assert_eq!(constant, 5);
}

#[test]
fn parse_linear_expr_nonlinear_returns_none() {
    // x * y (nonlinear)
    let expr = ChcExpr::mul(var("x"), var("y"));
    assert!(PdrSolver::parse_linear_expr_alg(&expr).is_none());
}

// --- parse_linear_eq_alg ---

#[test]
fn parse_linear_eq_simple() {
    // x = y + 1
    let (name, coeffs, constant) =
        PdrSolver::parse_linear_eq_alg(&var("x"), &ChcExpr::add(var("y"), ChcExpr::int(1)))
            .unwrap();
    assert_eq!(name, "x");
    assert_eq!(coeffs["y"], 1);
    assert_eq!(constant, 1);
}

#[test]
fn parse_linear_eq_rejects_self_reference() {
    // x = x + 1 (lhs var appears in rhs)
    let result =
        PdrSolver::parse_linear_eq_alg(&var("x"), &ChcExpr::add(var("x"), ChcExpr::int(1)));
    assert!(result.is_none());
}

#[test]
fn parse_linear_eq_rejects_nonvar_lhs() {
    // 5 = x (lhs is not a variable)
    let result = PdrSolver::parse_linear_eq_alg(&ChcExpr::int(5), &var("x"));
    assert!(result.is_none());
}

// --- sub_lin_alg, neg_lin_alg, lin_eq_alg, is_zero_alg ---

#[test]
fn sub_lin_alg_computes_difference() {
    // (2x + 3) - (x + 1) = x + 2
    let mut c1 = FxHashMap::default();
    c1.insert("x".to_string(), 2);
    let mut c2 = FxHashMap::default();
    c2.insert("x".to_string(), 1);
    let (result, constant) = PdrSolver::sub_lin_alg(&c1, 3, &c2, 1);
    assert_eq!(result["x"], 1);
    assert_eq!(constant, 2);
}

#[test]
fn sub_lin_alg_cancels_to_zero() {
    // (x + 5) - (x + 5) = 0
    let mut c = FxHashMap::default();
    c.insert("x".to_string(), 1);
    let (result, constant) = PdrSolver::sub_lin_alg(&c, 5, &c, 5);
    assert!(result.is_empty()); // retain removes zero coefficients
    assert_eq!(constant, 0);
}

#[test]
fn neg_lin_alg_negates() {
    let mut c = FxHashMap::default();
    c.insert("x".to_string(), 3);
    c.insert("y".to_string(), -2);
    let (r, s) = PdrSolver::neg_lin_alg(&c, 7);
    assert_eq!(r["x"], -3);
    assert_eq!(r["y"], 2);
    assert_eq!(s, -7);
}

#[test]
fn lin_eq_alg_equal_expressions() {
    let mut c1 = FxHashMap::default();
    c1.insert("x".to_string(), 1);
    c1.insert("y".to_string(), 2);
    let c2 = c1.clone();
    assert!(PdrSolver::lin_eq_alg(&c1, 5, &c2, 5));
}

#[test]
fn lin_eq_alg_different_constant() {
    let mut c = FxHashMap::default();
    c.insert("x".to_string(), 1);
    assert!(!PdrSolver::lin_eq_alg(&c, 5, &c, 6));
}

#[test]
fn is_zero_alg_true_for_zero() {
    let c = FxHashMap::default();
    assert!(PdrSolver::is_zero_alg(&c, 0));
}

#[test]
fn is_zero_alg_false_for_nonzero_constant() {
    let c = FxHashMap::default();
    assert!(!PdrSolver::is_zero_alg(&c, 1));
}

// --- apply_subs_once ---

#[test]
fn apply_subs_once_substitutes_variable() {
    // x where x := y + 1 => y + 1
    let mut coeffs = FxHashMap::default();
    coeffs.insert("x".to_string(), 1);

    let mut subs = FxHashMap::default();
    let mut sub_coeffs = FxHashMap::default();
    sub_coeffs.insert("y".to_string(), 1);
    subs.insert("x".to_string(), (sub_coeffs, 1i128));

    let (result, constant) = PdrSolver::apply_subs_once(&coeffs, 0, &subs);
    assert_eq!(result["y"], 1);
    assert!(!result.contains_key("x"));
    assert_eq!(constant, 1);
}

#[test]
fn apply_subs_once_preserves_unsubstituted() {
    // y where x := z => y (no change)
    let mut coeffs = FxHashMap::default();
    coeffs.insert("y".to_string(), 1);

    let mut subs = FxHashMap::default();
    let mut sub_coeffs = FxHashMap::default();
    sub_coeffs.insert("z".to_string(), 1);
    subs.insert("x".to_string(), (sub_coeffs, 0i128));

    let (result, constant) = PdrSolver::apply_subs_once(&coeffs, 3, &subs);
    assert_eq!(result["y"], 1);
    assert_eq!(constant, 3);
}

// --- apply_subs_alg (fixed-point) ---

#[test]
fn apply_subs_alg_chains_substitutions() {
    // F where F := C - 1, C := B + 2  =>  B + 1
    let mut coeffs = FxHashMap::default();
    coeffs.insert("F".to_string(), 1);

    let mut subs = FxHashMap::default();
    // F := C - 1
    let mut f_sub = FxHashMap::default();
    f_sub.insert("C".to_string(), 1);
    subs.insert("F".to_string(), (f_sub, -1i128));
    // C := B + 2
    let mut c_sub = FxHashMap::default();
    c_sub.insert("B".to_string(), 1);
    subs.insert("C".to_string(), (c_sub, 2i128));

    let (result, constant) = PdrSolver::apply_subs_alg(&coeffs, 0, &subs);
    assert_eq!(result.get("B"), Some(&1));
    assert!(!result.contains_key("F"));
    assert!(!result.contains_key("C"));
    assert_eq!(constant, 1); // -1 + 2 = 1
}

// --- extract_linear_equalities_alg ---

#[test]
fn extract_linear_equalities_from_conjunction() {
    // (x = y + 1) AND (z = 3)
    let body = ChcExpr::and(
        ChcExpr::eq(var("x"), ChcExpr::add(var("y"), ChcExpr::int(1))),
        ChcExpr::eq(var("z"), ChcExpr::int(3)),
    );
    let eqs = PdrSolver::extract_linear_equalities_alg(&body);
    assert_eq!(eqs.len(), 2);
    assert!(eqs.contains_key("x"));
    assert!(eqs.contains_key("z"));
    let (z_coeffs, z_const) = &eqs["z"];
    assert!(z_coeffs.is_empty());
    assert_eq!(*z_const, 3);
}

// --- verify_implication_algebraically ---

#[test]
fn verify_implication_equality_chain() {
    // body: x = y + 1 AND z = x + 2
    // head: z = y + 3
    // Should verify: z = x + 2 = (y + 1) + 2 = y + 3
    let body = ChcExpr::and(
        ChcExpr::eq(var("x"), ChcExpr::add(var("y"), ChcExpr::int(1))),
        ChcExpr::eq(var("z"), ChcExpr::add(var("x"), ChcExpr::int(2))),
    );
    let head = ChcExpr::eq(var("z"), ChcExpr::add(var("y"), ChcExpr::int(3)));
    assert!(PdrSolver::verify_implication_algebraically(&body, &head));
}

#[test]
fn verify_implication_rejects_invalid() {
    // body: x = y + 1
    // head: x = y + 2 (wrong)
    let body = ChcExpr::eq(var("x"), ChcExpr::add(var("y"), ChcExpr::int(1)));
    let head = ChcExpr::eq(var("x"), ChcExpr::add(var("y"), ChcExpr::int(2)));
    assert!(!PdrSolver::verify_implication_algebraically(&body, &head));
}

#[test]
fn verify_implication_rejects_not_constraints() {
    // body: x = 5
    // head: NOT(x = 3)
    // Algebraic verifier conservatively rejects Not constraints (#1011)
    let body = ChcExpr::eq(var("x"), ChcExpr::int(5));
    let head = ChcExpr::not(ChcExpr::eq(var("x"), ChcExpr::int(3)));
    assert!(!PdrSolver::verify_implication_algebraically(&body, &head));
}

#[test]
fn verify_implication_empty_body_equalities() {
    // body: x >= 0 (no equalities, only inequality)
    // head: x = 0
    // Should fail: no equalities to extract
    let body = ChcExpr::ge(var("x"), ChcExpr::int(0));
    let head = ChcExpr::eq(var("x"), ChcExpr::int(0));
    assert!(!PdrSolver::verify_implication_algebraically(&body, &head));
}

// --- contains_ite ---

#[test]
fn contains_ite_detects_ite() {
    let ite = ChcExpr::ite(
        ChcExpr::ge(var("x"), ChcExpr::int(0)),
        var("x"),
        ChcExpr::neg(var("x")),
    );
    assert!(ite.contains_ite());
}

#[test]
fn contains_ite_false_for_simple() {
    assert!(!ChcExpr::add(var("x"), ChcExpr::int(1)).contains_ite());
}

// --- contains_mod_or_div ---

#[test]
fn contains_mod_or_div_detects_mod() {
    let expr = ChcExpr::mod_op(var("x"), ChcExpr::int(2));
    assert!(PdrSolver::contains_mod_or_div(&expr));
}

#[test]
fn contains_mod_or_div_false_for_simple() {
    assert!(!PdrSolver::contains_mod_or_div(&ChcExpr::add(
        var("x"),
        ChcExpr::int(1)
    )));
}

// --- extract_sum_equalities_alg ---

#[test]
fn extract_sum_equalities_single() {
    // x + y = z (both sides linear)
    let body = ChcExpr::eq(ChcExpr::add(var("x"), var("y")), var("z"));
    let result = PdrSolver::extract_sum_equalities_alg(&body);
    assert_eq!(result.len(), 1);
    // lhs: x + y => {x: 1, y: 1}, const 0
    let ((lc, ls), (rc, rs)) = &result[0];
    assert_eq!(lc["x"], 1);
    assert_eq!(lc["y"], 1);
    assert_eq!(*ls, 0);
    assert_eq!(rc["z"], 1);
    assert_eq!(*rs, 0);
}

#[test]
fn extract_sum_equalities_conjunction() {
    // (x = y + 1) AND (a + b = c)
    let body = ChcExpr::and(
        ChcExpr::eq(var("x"), ChcExpr::add(var("y"), ChcExpr::int(1))),
        ChcExpr::eq(ChcExpr::add(var("a"), var("b")), var("c")),
    );
    let result = PdrSolver::extract_sum_equalities_alg(&body);
    assert_eq!(result.len(), 2);
}

#[test]
fn extract_sum_equalities_skips_nonlinear() {
    // x * y = z (nonlinear, should not extract)
    let body = ChcExpr::eq(ChcExpr::mul(var("x"), var("y")), var("z"));
    let result = PdrSolver::extract_sum_equalities_alg(&body);
    assert!(result.is_empty());
}

#[test]
fn extract_sum_equalities_skips_constant_only() {
    // 5 = 5 (both sides constant, no variables)
    let body = ChcExpr::eq(ChcExpr::int(5), ChcExpr::int(5));
    let result = PdrSolver::extract_sum_equalities_alg(&body);
    assert!(result.is_empty()); // filtered: both sides empty coefficients
}

// --- verify_equality_by_sub_alg ---

#[test]
fn verify_equality_by_sub_direct_match() {
    // body equalities: x = y + 1
    // verify: x = y + 1 (trivial after substitution)
    let mut body_eq = FxHashMap::default();
    let mut x_coeffs = FxHashMap::default();
    x_coeffs.insert("y".to_string(), 1);
    body_eq.insert("x".to_string(), (x_coeffs, 1i128));

    let sum_eq = vec![];

    // After substitution, x becomes y + 1, so x = y + 1 becomes (y+1) = (y+1)
    assert!(PdrSolver::verify_equality_by_sub_alg(
        &var("x"),
        &ChcExpr::add(var("y"), ChcExpr::int(1)),
        &body_eq,
        &sum_eq,
    ));
}

#[test]
fn verify_equality_by_sub_chained() {
    // body equalities: x = z + 2, z = y - 1
    // verify: x = y + 1 (after chained substitution: x = z+2 = (y-1)+2 = y+1)
    let mut body_eq = FxHashMap::default();
    let mut x_coeffs = FxHashMap::default();
    x_coeffs.insert("z".to_string(), 1);
    body_eq.insert("x".to_string(), (x_coeffs, 2i128));

    let mut z_coeffs = FxHashMap::default();
    z_coeffs.insert("y".to_string(), 1);
    body_eq.insert("z".to_string(), (z_coeffs, -1i128));

    let sum_eq = vec![];

    assert!(PdrSolver::verify_equality_by_sub_alg(
        &var("x"),
        &ChcExpr::add(var("y"), ChcExpr::int(1)),
        &body_eq,
        &sum_eq,
    ));
}

#[test]
fn verify_equality_by_sub_rejects_invalid() {
    // body equalities: x = y + 1
    // verify: x = y + 2 (wrong constant)
    let mut body_eq = FxHashMap::default();
    let mut x_coeffs = FxHashMap::default();
    x_coeffs.insert("y".to_string(), 1);
    body_eq.insert("x".to_string(), (x_coeffs, 1i128));

    let sum_eq = vec![];

    assert!(!PdrSolver::verify_equality_by_sub_alg(
        &var("x"),
        &ChcExpr::add(var("y"), ChcExpr::int(2)),
        &body_eq,
        &sum_eq,
    ));
}

#[test]
fn verify_equality_by_sub_uses_sum_equalities() {
    // body sum equality: a + b = c (i.e., a + b - c = 0)
    // verify: c = a + b
    // After substitution, diff = c - (a+b) = c - a - b
    // The sum equality gives (a+b) - c = 0, or equivalently c - a - b = 0
    let body_eq = FxHashMap::default();

    // sum equality: lhs = {a:1, b:1}, const 0; rhs = {c:1}, const 0
    let mut lhs_c = FxHashMap::default();
    lhs_c.insert("a".to_string(), 1);
    lhs_c.insert("b".to_string(), 1);
    let mut rhs_c = FxHashMap::default();
    rhs_c.insert("c".to_string(), 1);
    let sum_eq = vec![((lhs_c, 0i128), (rhs_c, 0i128))];

    assert!(PdrSolver::verify_equality_by_sub_alg(
        &var("c"),
        &ChcExpr::add(var("a"), var("b")),
        &body_eq,
        &sum_eq,
    ));
}

#[test]
fn verify_equality_by_sub_nonlinear_returns_false() {
    // x * y = z cannot be parsed as linear
    let body_eq = FxHashMap::default();
    let sum_eq = vec![];
    assert!(!PdrSolver::verify_equality_by_sub_alg(
        &ChcExpr::mul(var("x"), var("y")),
        &var("z"),
        &body_eq,
        &sum_eq,
    ));
}

// --- verify_ge_zero_from_body ---

#[test]
fn verify_ge_zero_positive_constant() {
    // 5 >= 0 is trivially true
    let coeffs = FxHashMap::default();
    let body = vec![];
    assert!(PdrSolver::verify_ge_zero_from_body(&coeffs, 5, &body));
}

#[test]
fn verify_ge_zero_negative_constant_no_vars() {
    // -1 >= 0 is false
    let coeffs = FxHashMap::default();
    let body = vec![];
    assert!(!PdrSolver::verify_ge_zero_from_body(&coeffs, -1, &body));
}

#[test]
fn verify_ge_zero_positive_var_bounded() {
    // x >= 0 where body has x >= 0
    let mut coeffs = FxHashMap::default();
    coeffs.insert("x".to_string(), 1);
    let body = vec![ChcExpr::ge(var("x"), ChcExpr::int(0))];
    assert!(PdrSolver::verify_ge_zero_from_body(&coeffs, 0, &body));
}

#[test]
fn verify_ge_zero_positive_var_unbounded() {
    // x >= 0 but body has no bound on x
    let mut coeffs = FxHashMap::default();
    coeffs.insert("x".to_string(), 1);
    let body = vec![];
    assert!(!PdrSolver::verify_ge_zero_from_body(&coeffs, 0, &body));
}

#[test]
fn verify_ge_zero_diff_with_body_pair() {
    // x - y + 0 >= 0 where body has x >= y
    let mut coeffs = FxHashMap::default();
    coeffs.insert("x".to_string(), 1);
    coeffs.insert("y".to_string(), -1);
    let body = vec![ChcExpr::ge(var("x"), var("y"))];
    assert!(PdrSolver::verify_ge_zero_from_body(&coeffs, 0, &body));
}

#[test]
fn verify_ge_zero_diff_with_positive_constant() {
    // x - y + 3 >= 0 where body has x >= y (since x-y >= 0, x-y+3 >= 3 >= 0)
    let mut coeffs = FxHashMap::default();
    coeffs.insert("x".to_string(), 1);
    coeffs.insert("y".to_string(), -1);
    let body = vec![ChcExpr::ge(var("x"), var("y"))];
    assert!(PdrSolver::verify_ge_zero_from_body(&coeffs, 3, &body));
}

#[test]
fn verify_ge_zero_diff_no_pair() {
    // x - y >= 0 but body has no x >= y
    let mut coeffs = FxHashMap::default();
    coeffs.insert("x".to_string(), 1);
    coeffs.insert("y".to_string(), -1);
    let body = vec![];
    assert!(!PdrSolver::verify_ge_zero_from_body(&coeffs, 0, &body));
}

// --- verify_ge_from_body_alg ---

#[test]
fn verify_ge_from_body_direct_match() {
    // body: x >= y
    // verify: x >= y
    let body = ChcExpr::ge(var("x"), var("y"));
    let body_eq = FxHashMap::default();
    assert!(PdrSolver::verify_ge_from_body_alg(
        &var("x"),
        &var("y"),
        &body,
        &body_eq,
    ));
}

#[test]
fn verify_ge_from_body_with_substitution() {
    // body: (d = b) AND (f = c - 1) AND (b >= c)
    // verify: d >= f
    // After substitution: d = b, f = c-1, so d >= f becomes b >= c-1
    // From b >= c we get b - c >= 0, so b - (c-1) = b - c + 1 >= 1 >= 0
    let body = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::eq(var("d"), var("b")),
            ChcExpr::eq(var("f"), ChcExpr::sub(var("c"), ChcExpr::int(1))),
        ),
        ChcExpr::ge(var("b"), var("c")),
    );
    let mut body_eq = FxHashMap::default();
    let mut d_coeffs = FxHashMap::default();
    d_coeffs.insert("b".to_string(), 1);
    body_eq.insert("d".to_string(), (d_coeffs, 0i128));

    let mut f_coeffs = FxHashMap::default();
    f_coeffs.insert("c".to_string(), 1);
    body_eq.insert("f".to_string(), (f_coeffs, -1i128));

    assert!(PdrSolver::verify_ge_from_body_alg(
        &var("d"),
        &var("f"),
        &body,
        &body_eq,
    ));
}

// --- normalize_with_single_substitution ---

#[test]
fn normalize_single_sub_applies() {
    // x where x := y + 3  => y + 3 (single step)
    let mut body_eq = FxHashMap::default();
    let mut x_coeffs = FxHashMap::default();
    x_coeffs.insert("y".to_string(), 1);
    body_eq.insert("x".to_string(), (x_coeffs, 3i128));

    let (coeffs, constant) = PdrSolver::normalize_with_single_substitution(&var("x"), &body_eq);
    assert_eq!(coeffs["y"], 1);
    assert!(!coeffs.contains_key("x"));
    assert_eq!(constant, 3);
}

#[test]
fn normalize_single_sub_no_chain() {
    // x where x := y + 1, y := z + 2
    // Single step: x => y + 1 (does NOT further resolve y => z + 2)
    let mut body_eq = FxHashMap::default();
    let mut x_coeffs = FxHashMap::default();
    x_coeffs.insert("y".to_string(), 1);
    body_eq.insert("x".to_string(), (x_coeffs, 1i128));

    let mut y_coeffs = FxHashMap::default();
    y_coeffs.insert("z".to_string(), 1);
    body_eq.insert("y".to_string(), (y_coeffs, 2i128));

    let (coeffs, constant) = PdrSolver::normalize_with_single_substitution(&var("x"), &body_eq);
    assert_eq!(coeffs.get("y"), Some(&1));
    assert!(!coeffs.contains_key("z")); // NOT chained
    assert_eq!(constant, 1);
}

#[test]
fn normalize_single_sub_nonlinear_fallback() {
    // x * y cannot be parsed as linear; falls back to (empty, 0)
    let body_eq = FxHashMap::default();
    let expr = ChcExpr::mul(var("x"), var("y"));
    let (coeffs, constant) = PdrSolver::normalize_with_single_substitution(&expr, &body_eq);
    assert!(coeffs.is_empty());
    assert_eq!(constant, 0);
}

// --- extract_mod2_remainder ---

#[test]
fn extract_mod2_remainder_forward() {
    // (x mod 2) = 1
    let lemma = ChcExpr::eq(ChcExpr::mod_op(var("x"), ChcExpr::int(2)), ChcExpr::int(1));
    assert_eq!(PdrSolver::extract_mod2_remainder(&lemma, "x"), Some(1));
}

#[test]
fn extract_mod2_remainder_reversed() {
    // 0 = (x mod 2)
    let lemma = ChcExpr::eq(ChcExpr::int(0), ChcExpr::mod_op(var("x"), ChcExpr::int(2)));
    assert_eq!(PdrSolver::extract_mod2_remainder(&lemma, "x"), Some(0));
}

#[test]
fn extract_mod2_remainder_wrong_var() {
    // (y mod 2) = 1, asking for x
    let lemma = ChcExpr::eq(ChcExpr::mod_op(var("y"), ChcExpr::int(2)), ChcExpr::int(1));
    assert_eq!(PdrSolver::extract_mod2_remainder(&lemma, "x"), None);
}

#[test]
fn extract_mod2_remainder_not_mod() {
    // x = 1 (not a mod expression)
    let lemma = ChcExpr::eq(var("x"), ChcExpr::int(1));
    assert_eq!(PdrSolver::extract_mod2_remainder(&lemma, "x"), None);
}

#[test]
fn extract_mod2_remainder_mod3_returns_none() {
    // (x mod 3) = 1 (not mod 2)
    let lemma = ChcExpr::eq(ChcExpr::mod_op(var("x"), ChcExpr::int(3)), ChcExpr::int(1));
    assert_eq!(PdrSolver::extract_mod2_remainder(&lemma, "x"), None);
}

// --- constraint_contains_strict_gt ---

#[test]
fn constraint_gt_direct() {
    // x > y
    let c = ChcExpr::gt(var("x"), var("y"));
    assert!(PdrSolver::constraint_contains_strict_gt(&c, "x", "y"));
}

#[test]
fn constraint_gt_reversed_false() {
    // x > y, asking for y > x
    let c = ChcExpr::gt(var("x"), var("y"));
    assert!(!PdrSolver::constraint_contains_strict_gt(&c, "y", "x"));
}

#[test]
fn constraint_gt_via_lt() {
    // y < x means x > y
    let c = ChcExpr::lt(var("y"), var("x"));
    assert!(PdrSolver::constraint_contains_strict_gt(&c, "x", "y"));
}

#[test]
fn constraint_gt_via_not_le() {
    // NOT(x <= y) means x > y
    let c = ChcExpr::not(ChcExpr::le(var("x"), var("y")));
    assert!(PdrSolver::constraint_contains_strict_gt(&c, "x", "y"));
}

#[test]
fn constraint_gt_in_conjunction() {
    // (a >= 0) AND (x > y) - should find x > y in conjunction
    let c = ChcExpr::and(
        ChcExpr::ge(var("a"), ChcExpr::int(0)),
        ChcExpr::gt(var("x"), var("y")),
    );
    assert!(PdrSolver::constraint_contains_strict_gt(&c, "x", "y"));
}

#[test]
fn constraint_gt_not_present() {
    // x >= y (not strict)
    let c = ChcExpr::ge(var("x"), var("y"));
    assert!(!PdrSolver::constraint_contains_strict_gt(&c, "x", "y"));
}
