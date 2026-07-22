// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================
// ParametricMultiplicationProvider unit tests for helpers
// ============================================================

#[test]
fn test_parse_mul_guard_simple_mul_ge() {
    // (* 2 x) >= y  =>  MulGuard { op: Ge, mul_on_lhs: true, k: 2 }
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::ge(
        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(x)),
        ChcExpr::var(y),
    );
    let guard = ParametricMultiplicationProvider::parse_mul_guard(&expr)
        .expect("invariant: should parse (* 2 x) >= y");
    assert!(matches!(guard.op, ChcOp::Ge));
    assert!(guard.mul_on_lhs);
    assert_eq!(guard.k, 2);
    assert_eq!(guard.mul_var.name, "x");
    assert_eq!(guard.other_var.name, "y");
}

#[test]
fn test_parse_mul_guard_rhs_mul() {
    // y <= (* 3 x)  =>  MulGuard { op: Le, mul_on_lhs: false, k: 3 }
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::le(
        ChcExpr::var(y),
        ChcExpr::mul(ChcExpr::int(3), ChcExpr::var(x)),
    );
    let guard = ParametricMultiplicationProvider::parse_mul_guard(&expr)
        .expect("invariant: should parse y <= (* 3 x)");
    assert!(matches!(guard.op, ChcOp::Le));
    assert!(!guard.mul_on_lhs);
    assert_eq!(guard.k, 3);
    assert_eq!(guard.mul_var.name, "x");
    assert_eq!(guard.other_var.name, "y");
}

#[test]
fn test_parse_mul_guard_eq_var_var() {
    // (= a b) treated as (= a (* 1 b)) => k=1
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let expr = ChcExpr::eq(ChcExpr::var(a), ChcExpr::var(b));
    let guard = ParametricMultiplicationProvider::parse_mul_guard(&expr)
        .expect("invariant: should parse (= a b)");
    assert!(matches!(guard.op, ChcOp::Eq));
    assert_eq!(guard.k, 1);
    assert_eq!(guard.other_var.name, "a");
    assert_eq!(guard.mul_var.name, "b");
}

#[test]
fn test_parse_mul_guard_rejects_same_var() {
    // (* 2 x) >= x should be rejected (other_var == mul_var)
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::ge(
        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(x.clone())),
        ChcExpr::var(x),
    );
    assert!(ParametricMultiplicationProvider::parse_mul_guard(&expr).is_none());
}

#[test]
fn test_parse_mul_guard_rejects_non_comparison() {
    // (+ x y) is not a comparison
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y));
    assert!(ParametricMultiplicationProvider::parse_mul_guard(&expr).is_none());
}

#[test]
fn test_parse_mul_guard_rejects_eq_same_var() {
    // (= x x) should be rejected
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(x));
    assert!(ParametricMultiplicationProvider::parse_mul_guard(&expr).is_none());
}

#[test]
fn test_const_mul_var_simple() {
    // (* 5 x) => (5, x)
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mul(ChcExpr::int(5), ChcExpr::var(x));
    let (k, var) = ParametricMultiplicationProvider::const_mul_var(&expr)
        .expect("invariant: should parse (* 5 x)");
    assert_eq!(k, 5);
    assert_eq!(var.name, "x");
}

#[test]
fn test_const_mul_var_rejects_negative_coeff() {
    // (* -2 x) => None (coeff must be positive)
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mul(ChcExpr::int(-2), ChcExpr::var(x));
    assert!(ParametricMultiplicationProvider::const_mul_var(&expr).is_none());
}

#[test]
fn test_const_mul_var_rejects_zero_coeff() {
    // (* 0 x) => None (coeff must be positive)
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mul(ChcExpr::int(0), ChcExpr::var(x));
    assert!(ParametricMultiplicationProvider::const_mul_var(&expr).is_none());
}

#[test]
fn test_const_mul_var_rejects_two_vars() {
    // (* x y) => None (must be const * var, not var * var)
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::mul(ChcExpr::var(x), ChcExpr::var(y));
    assert!(ParametricMultiplicationProvider::const_mul_var(&expr).is_none());
}

#[test]
fn test_const_mul_var_rejects_non_mul() {
    // (+ 2 x) is not a multiplication
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::add(ChcExpr::int(2), ChcExpr::var(x));
    assert!(ParametricMultiplicationProvider::const_mul_var(&expr).is_none());
}

#[test]
fn test_mul_term_k_zero() {
    let x = ChcVar::new("x", ChcSort::Int);
    let result = ParametricMultiplicationProvider::mul_term(0, x);
    assert!(matches!(result, ChcExpr::Int(0)));
}

#[test]
fn test_mul_term_k_one() {
    let x = ChcVar::new("x", ChcSort::Int);
    let result = ParametricMultiplicationProvider::mul_term(1, x);
    assert!(matches!(result, ChcExpr::Var(ref v) if v.name == "x"));
}

#[test]
fn test_mul_term_k_general() {
    let x = ChcVar::new("x", ChcSort::Int);
    let result = ParametricMultiplicationProvider::mul_term(3, x);
    // Should be (* 3 x)
    assert!(
        matches!(&result, ChcExpr::Op(ChcOp::Mul, args)
            if args.len() == 2
                && matches!(args[0].as_ref(), ChcExpr::Int(3))
                && matches!(args[1].as_ref(), ChcExpr::Var(v) if v.name == "x")
        ),
        "expected (* 3 x), got {result:?}"
    );
}

// ============================================================================
// Canonical variable helper tests (#1405, #1413)
// ============================================================================

#[test]
fn test_canonical_var_name() {
    use super::canonical_var_name;

    assert_eq!(canonical_var_name(PredicateId(0), 0), "__p0_a0");
    assert_eq!(canonical_var_name(PredicateId(0), 1), "__p0_a1");
    assert_eq!(canonical_var_name(PredicateId(3), 7), "__p3_a7");
}

#[test]
fn test_canonical_var_for_pred_arg() {
    use super::canonical_var_for_pred_arg;

    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Bool]);

    let var0 = canonical_var_for_pred_arg(&problem, pred, 0);
    assert!(var0.is_some());
    let var0 = var0.unwrap();
    assert_eq!(var0.name, "__p0_a0");
    assert_eq!(var0.sort, ChcSort::Int);

    let var1 = canonical_var_for_pred_arg(&problem, pred, 1);
    assert!(var1.is_some());
    let var1 = var1.unwrap();
    assert_eq!(var1.name, "__p0_a1");
    assert_eq!(var1.sort, ChcSort::Bool);

    // Out-of-bounds arg index
    assert!(canonical_var_for_pred_arg(&problem, pred, 2).is_none());

    // Invalid predicate
    assert!(canonical_var_for_pred_arg(&problem, PredicateId(99), 0).is_none());
}

#[test]
fn test_canonical_vars_for_pred() {
    use super::canonical_vars_for_pred;

    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int, ChcSort::Bool]);

    let vars = canonical_vars_for_pred(&problem, pred);
    assert!(vars.is_some());
    let vars = vars.unwrap();
    assert_eq!(vars.len(), 3);
    assert_eq!(vars[0].name, "__p0_a0");
    assert_eq!(vars[0].sort, ChcSort::Int);
    assert_eq!(vars[1].name, "__p0_a1");
    assert_eq!(vars[1].sort, ChcSort::Int);
    assert_eq!(vars[2].name, "__p0_a2");
    assert_eq!(vars[2].sort, ChcSort::Bool);

    // Invalid predicate
    assert!(canonical_vars_for_pred(&problem, PredicateId(99)).is_none());
}

// ============================================================================
// Runtime hint provider registration tests (#1405)
// ============================================================================

#[test]
fn test_hint_providers_newtype_default_empty() {
    use super::HintProviders;

    let providers = HintProviders::default();
    assert!(providers.0.is_empty());
}

#[test]
fn test_collect_all_hints_with_extra_providers() {
    use super::collect_all_hints_with_extra_providers;
    use std::sync::Arc;

    // Custom runtime provider
    struct TestRuntimeProvider;
    impl LemmaHintProvider for TestRuntimeProvider {
        fn collect(&self, _req: &HintRequest<'_>, out: &mut Vec<LemmaHint>) {
            out.push(LemmaHint::new(
                PredicateId(0),
                ChcExpr::ge(
                    ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
                    ChcExpr::int(42),
                ),
                10,
                "test-runtime-provider",
            ));
        }
    }

    let problem = ChcProblem::new();
    let vars: Vec<ChcVar> = vec![];
    let vars_ref: &[ChcVar] = &vars;
    let canonical_vars_fn = |_: PredicateId| -> Option<&[ChcVar]> { Some(vars_ref) };
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);

    let provider: Arc<dyn LemmaHintProvider> = Arc::new(TestRuntimeProvider);
    let providers = vec![provider];

    let hints = collect_all_hints_with_extra_providers(&req, &providers, &[]);
    let found = hints.iter().any(|h| h.source == "test-runtime-provider");
    assert!(found, "Runtime provider hint should be collected");
}

#[test]
fn test_pdr_config_user_hint_providers_builder() {
    use super::HintProviders;
    use crate::pdr::PdrConfig;
    use std::sync::Arc;

    struct NoopProvider;
    impl LemmaHintProvider for NoopProvider {
        fn collect(&self, _req: &HintRequest<'_>, _out: &mut Vec<LemmaHint>) {}
    }

    let provider: Arc<dyn LemmaHintProvider> = Arc::new(NoopProvider);
    let providers = HintProviders(vec![provider]);

    let config = PdrConfig::default().with_user_hint_providers(providers);
    assert_eq!(config.user_hint_providers.0.len(), 1);
}
