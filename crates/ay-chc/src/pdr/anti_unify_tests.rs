// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcOp, ChcSort};

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn contains_int(expr: &ChcExpr, n: i128) -> bool {
    match expr {
        ChcExpr::Int(v) => *v == n,
        ChcExpr::Op(_, args) => args.iter().any(|a| contains_int(a.as_ref(), n)),
        ChcExpr::PredicateApp(_, _, args) => args.iter().any(|a| contains_int(a.as_ref(), n)),
        ChcExpr::FuncApp(_, _, args) => args.iter().any(|a| contains_int(a.as_ref(), n)),
        ChcExpr::ConstArray(_ks, v) => contains_int(v.as_ref(), n),
        _ => false,
    }
}

#[test]
fn test_anti_unify_simple_int_substitution() {
    let e1 = ChcExpr::gt(var("x"), ChcExpr::Int(5));
    let e2 = ChcExpr::gt(var("x"), ChcExpr::Int(10));

    let r = anti_unify(&e1, &e2);
    assert_eq!(r.pattern_vars.len(), 1);
    assert_eq!(r.subst1, vec![ChcExpr::Int(5)]);
    assert_eq!(r.subst2, vec![ChcExpr::Int(10)]);
    assert!(r.is_numeric_int_substitution());

    // Pattern is: (gt x __au_k0)
    let ChcExpr::Op(ChcOp::Gt, args) = &r.pattern else {
        panic!("expected gt pattern, got: {}", r.pattern);
    };
    assert_eq!(args.len(), 2);
    assert_eq!(args[0].as_ref(), &var("x"));
    let ChcExpr::Var(pv) = args[1].as_ref() else {
        panic!("expected pattern var rhs");
    };
    assert_eq!(pv, &r.pattern_vars[0]);
}

#[test]
fn test_anti_unify_keeps_common_constants() {
    // (and (= x 0) (= y 5)) with (and (= x 0) (= y 10)) should keep the 0 constant
    // and abstract only the y constant.
    let e1 = ChcExpr::and(
        ChcExpr::eq(var("x"), ChcExpr::Int(0)),
        ChcExpr::eq(var("y"), ChcExpr::Int(5)),
    );
    let e2 = ChcExpr::and(
        ChcExpr::eq(var("x"), ChcExpr::Int(0)),
        ChcExpr::eq(var("y"), ChcExpr::Int(10)),
    );

    let r = anti_unify(&e1, &e2);
    assert_eq!(r.pattern_vars.len(), 1);
    assert_eq!(r.pattern_vars[0].sort, ChcSort::Int);
    assert_eq!(r.subst1, vec![ChcExpr::Int(5)]);
    assert_eq!(r.subst2, vec![ChcExpr::Int(10)]);

    assert!(
        contains_int(&r.pattern, 0),
        "expected common constant to remain in pattern: {}",
        r.pattern
    );
}

#[test]
fn test_anti_unify_nonlinear_mul_guard() {
    use std::sync::Arc;
    // Non-linear multiplication (x * y) should NOT be descended into because
    // neither operand is a constant. This matches Z3 spacer_antiunify.cpp:55-66.
    //
    // Expression 1: x * y > 5
    // Expression 2: x * y > 10
    //
    // Without the guard, we would anti-unify into (x * y) and create pattern:
    //   (__au_k0 * __au_k1) > __au_k2
    //
    // With the guard, (x * y) is treated as a unit, giving pattern:
    //   __au_k0 > __au_k1
    let mul_a = ChcExpr::Op(ChcOp::Mul, vec![Arc::new(var("x")), Arc::new(var("y"))]);
    let mul_b = ChcExpr::Op(ChcOp::Mul, vec![Arc::new(var("x")), Arc::new(var("y"))]);
    let e1 = ChcExpr::gt(mul_a, ChcExpr::Int(5));
    let e2 = ChcExpr::gt(mul_b, ChcExpr::Int(10));

    let r = anti_unify(&e1, &e2);

    // Only the constant on the RHS differs, so we should have 1 pattern var
    assert_eq!(
        r.pattern_vars.len(),
        1,
        "expected 1 pattern var for constant difference, got {}",
        r.pattern_vars.len()
    );

    // The mul expression should be preserved as-is in the pattern (same in both inputs)
    let ChcExpr::Op(ChcOp::Gt, args) = &r.pattern else {
        panic!("expected gt pattern, got: {}", r.pattern);
    };
    assert!(
        matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Mul, _)),
        "expected Mul on LHS of gt, got: {}",
        args[0]
    );
}

#[test]
fn test_anti_unify_linear_mul_allowed() {
    use std::sync::Arc;
    // Linear multiplication (2 * x) vs (3 * x) SHOULD be descended into
    // because at least one operand is a constant.
    let mul_a = ChcExpr::Op(
        ChcOp::Mul,
        vec![Arc::new(ChcExpr::Int(2)), Arc::new(var("x"))],
    );
    let mul_b = ChcExpr::Op(
        ChcOp::Mul,
        vec![Arc::new(ChcExpr::Int(3)), Arc::new(var("x"))],
    );
    let e1 = ChcExpr::eq(var("y"), mul_a);
    let e2 = ChcExpr::eq(var("y"), mul_b);

    let r = anti_unify(&e1, &e2);

    // Should abstract the differing constants (2 vs 3)
    assert_eq!(
        r.pattern_vars.len(),
        1,
        "expected 1 pattern var for coefficient difference, got {}",
        r.pattern_vars.len()
    );
    assert_eq!(r.subst1, vec![ChcExpr::Int(2)]);
    assert_eq!(r.subst2, vec![ChcExpr::Int(3)]);
}

#[test]
fn test_anti_unify_mixed_linear_nonlinear_mul_guard() {
    use std::sync::Arc;
    // If either side is non-linear (no constant factor), we must avoid
    // descending into Mul to prevent generating non-linear patterns.
    let linear_mul = ChcExpr::Op(
        ChcOp::Mul,
        vec![Arc::new(ChcExpr::Int(2)), Arc::new(var("x"))],
    );
    let nonlinear_mul = ChcExpr::Op(ChcOp::Mul, vec![Arc::new(var("a")), Arc::new(var("b"))]);
    let e1 = ChcExpr::eq(var("y"), linear_mul.clone());
    let e2 = ChcExpr::eq(var("y"), nonlinear_mul.clone());

    let r = anti_unify(&e1, &e2);
    assert_eq!(
        r.pattern_vars.len(),
        1,
        "mixed linear/non-linear mul should abstract mul as a unit"
    );
    assert_eq!(r.subst1, vec![linear_mul]);
    assert_eq!(r.subst2, vec![nonlinear_mul]);

    let ChcExpr::Op(ChcOp::Eq, args) = &r.pattern else {
        panic!("expected eq pattern, got: {}", r.pattern);
    };
    assert!(
        matches!(args[1].as_ref(), ChcExpr::Var(_)),
        "rhs should be abstracted as a single pattern var"
    );
}

#[test]
fn test_anti_unify_nary_nonlinear_mul_guard() {
    use std::sync::Arc;
    // Guard should apply to n-ary multiplication too, not only binary Mul.
    let mul_a = ChcExpr::Op(
        ChcOp::Mul,
        vec![Arc::new(var("x")), Arc::new(var("y")), Arc::new(var("z"))],
    );
    let mul_b = ChcExpr::Op(
        ChcOp::Mul,
        vec![Arc::new(var("x")), Arc::new(var("y")), Arc::new(var("w"))],
    );
    let e1 = ChcExpr::gt(mul_a.clone(), ChcExpr::Int(0));
    let e2 = ChcExpr::gt(mul_b.clone(), ChcExpr::Int(0));

    let r = anti_unify(&e1, &e2);
    assert_eq!(
        r.pattern_vars.len(),
        1,
        "n-ary nonlinear mul should be abstracted as a single unit"
    );
    assert_eq!(r.subst1, vec![mul_a]);
    assert_eq!(r.subst2, vec![mul_b]);
}

#[test]
fn test_anti_unify_real_numerals() {
    // Real numerals (1.5 vs 2.5) should be anti-unified correctly
    let e1 = ChcExpr::gt(var("x"), ChcExpr::Real(3, 2)); // 1.5
    let e2 = ChcExpr::gt(var("x"), ChcExpr::Real(5, 2)); // 2.5

    let r = anti_unify(&e1, &e2);
    assert_eq!(r.pattern_vars.len(), 1);
    assert_eq!(r.subst1, vec![ChcExpr::Real(3, 2)]);
    assert_eq!(r.subst2, vec![ChcExpr::Real(5, 2)]);

    // Verify is_numeric_int_substitution returns false for Real
    assert!(
        !r.is_numeric_int_substitution(),
        "Real substitution should not count as int"
    );

    // Pattern should be (gt x __au_k0)
    let ChcExpr::Op(ChcOp::Gt, args) = &r.pattern else {
        panic!("expected gt pattern, got: {}", r.pattern);
    };
    assert_eq!(args.len(), 2);
    assert!(matches!(args[1].as_ref(), ChcExpr::Var(_)));
}

#[test]
fn test_anti_unify_identical_input() {
    // When e1 == e2, should return the expression unchanged with no pattern vars
    let e = ChcExpr::and(
        ChcExpr::gt(var("x"), ChcExpr::Int(0)),
        ChcExpr::lt(var("y"), ChcExpr::Int(10)),
    );

    let r = anti_unify(&e, &e);
    assert!(
        r.pattern_vars.is_empty(),
        "identical inputs should have no pattern vars"
    );
    assert!(
        r.subst1.is_empty(),
        "identical inputs should have no substitutions"
    );
    assert!(
        r.subst2.is_empty(),
        "identical inputs should have no substitutions"
    );
    assert_eq!(r.pattern, e, "pattern should equal original expression");
}

#[test]
fn test_anti_unify_bool_values() {
    // Bool literals true vs false should create a pattern var
    let e1 = ChcExpr::eq(var("x"), ChcExpr::Bool(true));
    let e2 = ChcExpr::eq(var("x"), ChcExpr::Bool(false));

    let r = anti_unify(&e1, &e2);
    assert_eq!(r.pattern_vars.len(), 1);
    assert_eq!(r.pattern_vars[0].sort, ChcSort::Bool);
    assert_eq!(r.subst1, vec![ChcExpr::Bool(true)]);
    assert_eq!(r.subst2, vec![ChcExpr::Bool(false)]);
}

#[test]
fn test_anti_unify_variable_mismatch() {
    // Two different variables (same sort) should be abstracted
    let v1 = ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let v2 = ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let e1 = ChcExpr::gt(v1.clone(), ChcExpr::Int(0));
    let e2 = ChcExpr::gt(v2.clone(), ChcExpr::Int(0));

    let r = anti_unify(&e1, &e2);
    assert_eq!(r.pattern_vars.len(), 1);
    assert_eq!(r.subst1, vec![v1]);
    assert_eq!(r.subst2, vec![v2]);
}

#[test]
fn test_anti_unify_nested_structures() {
    use std::sync::Arc;
    // Deeply nested structure: (and (or (gt x 1) (lt y 2)) (gt z 3))
    // vs                       (and (or (gt x 5) (lt y 2)) (gt z 3))
    // Should only abstract the 1 vs 5 constant, keeping everything else.
    let inner1 = ChcExpr::Op(
        ChcOp::Or,
        vec![
            Arc::new(ChcExpr::gt(var("x"), ChcExpr::Int(1))),
            Arc::new(ChcExpr::lt(var("y"), ChcExpr::Int(2))),
        ],
    );
    let inner2 = ChcExpr::Op(
        ChcOp::Or,
        vec![
            Arc::new(ChcExpr::gt(var("x"), ChcExpr::Int(5))),
            Arc::new(ChcExpr::lt(var("y"), ChcExpr::Int(2))),
        ],
    );
    let e1 = ChcExpr::and(inner1, ChcExpr::gt(var("z"), ChcExpr::Int(3)));
    let e2 = ChcExpr::and(inner2, ChcExpr::gt(var("z"), ChcExpr::Int(3)));

    let r = anti_unify(&e1, &e2);
    assert_eq!(
        r.pattern_vars.len(),
        1,
        "expected 1 pattern var for nested difference"
    );
    assert_eq!(r.subst1, vec![ChcExpr::Int(1)]);
    assert_eq!(r.subst2, vec![ChcExpr::Int(5)]);

    // Common constants 2 and 3 should remain
    assert!(contains_int(&r.pattern, 2), "expected 2 in pattern");
    assert!(contains_int(&r.pattern, 3), "expected 3 in pattern");
}

#[test]
fn test_anti_unify_cache_hit() {
    use std::sync::Arc;
    // When the same subterm pair appears multiple times, cache should be used.
    // (and (gt x 1) (gt x 1)) vs (and (gt x 2) (gt x 2))
    // The (gt x 1) vs (gt x 2) pair appears twice but should only create one pattern var.
    let gt1 = ChcExpr::gt(var("x"), ChcExpr::Int(1));
    let gt2 = ChcExpr::gt(var("x"), ChcExpr::Int(2));
    let e1 = ChcExpr::Op(ChcOp::And, vec![Arc::new(gt1.clone()), Arc::new(gt1)]);
    let e2 = ChcExpr::Op(ChcOp::And, vec![Arc::new(gt2.clone()), Arc::new(gt2)]);

    let r = anti_unify(&e1, &e2);

    // Only 1 pattern var despite 2 occurrences of the same difference
    assert_eq!(
        r.pattern_vars.len(),
        1,
        "cache should reuse pattern var for identical subterm pairs"
    );

    // Pattern should be (and (gt x __au_k0) (gt x __au_k0))
    let ChcExpr::Op(ChcOp::And, args) = &r.pattern else {
        panic!("expected and pattern");
    };
    assert_eq!(
        args[0], args[1],
        "repeated subterms should produce identical pattern subterms"
    );
}

#[test]
fn test_anti_unify_const_array() {
    use std::sync::Arc;
    // ConstArray with different elements should be anti-unified
    let arr1 = ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::Int(0)));
    let arr2 = ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::Int(1)));

    let r = anti_unify(&arr1, &arr2);
    assert_eq!(r.pattern_vars.len(), 1);
    assert_eq!(r.subst1, vec![ChcExpr::Int(0)]);
    assert_eq!(r.subst2, vec![ChcExpr::Int(1)]);

    // Pattern should be ConstArray(__au_k0)
    let ChcExpr::ConstArray(_ks, elem) = &r.pattern else {
        panic!("expected ConstArray pattern, got: {}", r.pattern);
    };
    assert!(matches!(elem.as_ref(), ChcExpr::Var(_)));
}

#[test]
fn test_are_neighbours_int_only_true() {
    // Two expressions differing only in Int constants should be neighbours
    let e1 = ChcExpr::gt(var("x"), ChcExpr::Int(5));
    let e2 = ChcExpr::gt(var("x"), ChcExpr::Int(10));

    assert!(
        are_neighbours_int_only(&e1, &e2),
        "expressions differing only in Int should be int-only neighbours"
    );
}

#[test]
fn test_are_neighbours_int_only_false_for_identical() {
    // Identical expressions are NOT neighbours
    let e = ChcExpr::gt(var("x"), ChcExpr::Int(5));
    assert!(
        !are_neighbours_int_only(&e, &e),
        "identical expressions should not be neighbours"
    );
}

#[test]
fn test_are_neighbours_int_only_false_for_real() {
    // Expressions differing in Real constants are not int-only neighbours
    let e1 = ChcExpr::gt(var("x"), ChcExpr::Real(1, 2));
    let e2 = ChcExpr::gt(var("x"), ChcExpr::Real(3, 2));

    assert!(
        !are_neighbours_int_only(&e1, &e2),
        "expressions differing in Real should not be int-only neighbours"
    );
}

#[test]
fn test_is_numeric_int_substitution_mixed() {
    // Mixed Int/Real substitution should return false
    let e1 = ChcExpr::and(
        ChcExpr::gt(var("x"), ChcExpr::Int(5)),
        ChcExpr::lt(var("y"), ChcExpr::Real(1, 2)),
    );
    let e2 = ChcExpr::and(
        ChcExpr::gt(var("x"), ChcExpr::Int(10)),
        ChcExpr::lt(var("y"), ChcExpr::Real(3, 2)),
    );

    let r = anti_unify(&e1, &e2);
    assert_eq!(r.pattern_vars.len(), 2, "should have 2 pattern vars");
    assert!(
        !r.is_numeric_int_substitution(),
        "mixed Int/Real substitution should not be int-only"
    );
}

#[test]
fn test_fresh_var_avoids_existing_names() {
    // When input has a var named __au_k0, fresh var should use __au_k1
    let v = ChcExpr::var(ChcVar::new("__au_k0", ChcSort::Int));
    let e1 = ChcExpr::gt(v, ChcExpr::Int(5));
    let e2 = ChcExpr::gt(
        ChcExpr::var(ChcVar::new("__au_k0", ChcSort::Int)),
        ChcExpr::Int(10),
    );

    let r = anti_unify(&e1, &e2);
    // The pattern var should avoid the existing __au_k0 name
    assert_eq!(r.pattern_vars.len(), 1);
    assert_ne!(
        r.pattern_vars[0].name, "__au_k0",
        "fresh var should avoid collision with existing name"
    );
    assert!(
        r.pattern_vars[0].name.starts_with("__au_k"),
        "fresh var should follow naming pattern"
    );
}
