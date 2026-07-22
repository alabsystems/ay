// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for #2881: AY SMT solver returns false UNSAT for
//! mod-elimination formulas with shared dividend variable.
//!
//! Root cause: the mod-elimination pass (expr.rs `eliminate_mod_recursive`)
//! previously encoded each `(mod x k)` using a definitional equality that
//! triggered false UNSAT in the CHC SMT path when formulas shared dividend
//! variables across multiple modulo terms.
//!
//! These tests guard against that soundness regression.

use ay_chc::{ChcExpr, ChcSort, ChcVar, SmtContext, SmtResult, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Helper: extract integer value of variable from SAT model.
fn get_int(model: &FxHashMap<String, SmtValue>, var: &str) -> i128 {
    match model.get(var) {
        Some(SmtValue::Int(n)) => *n,
        other => panic!("expected Int for {var}, got {other:?}"),
    }
}

/// SMT-LIB div semantics: Euclidean division (remainder always non-negative).
fn smt_mod(a: i128, b: i128) -> i128 {
    a.rem_euclid(b)
}

/// (distinct (mod x 6) (mod (+ x 2) 6)) AND x >= 0 AND (mod x 2) = 0
/// is SAT at x=4: (4 mod 6)=4, (6 mod 6)=0, 4!=0, 4>=0, 4 mod 2=0.
///
/// This is the formula that causes the even_odd.smt2 soundness bug.
/// The SMT solver incorrectly returns UNSAT because of a bug in mod elimination
/// when multiple mod expressions share the same dividend variable.
#[test]
fn test_mod_distinct_with_parity_constraint() {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_expr = ChcExpr::var(x);

    // (distinct (mod x 6) (mod (+ x 2) 6))
    let mod_x_6 = ChcExpr::mod_op(x_expr.clone(), ChcExpr::int(6));
    let x_plus_2 = ChcExpr::add(x_expr.clone(), ChcExpr::int(2));
    let mod_x_plus_2_6 = ChcExpr::mod_op(x_plus_2, ChcExpr::int(6));
    let distinct = ChcExpr::ne(mod_x_6, mod_x_plus_2_6);

    // x >= 0
    let x_ge_0 = ChcExpr::ge(x_expr.clone(), ChcExpr::int(0));

    // (mod x 2) = 0
    let mod_x_2 = ChcExpr::mod_op(x_expr, ChcExpr::int(2));
    let even_parity = ChcExpr::eq(mod_x_2, ChcExpr::int(0));

    let query = ChcExpr::and_all(vec![distinct, x_ge_0, even_parity]);

    let mut ctx = SmtContext::new();
    let result = ctx.check_sat(&query);
    let model = match result {
        SmtResult::Sat(m) => m,
        other => panic!(
            "#2881: (distinct (mod x 6) (mod (+ x 2) 6)) AND x >= 0 AND (mod x 2) = 0 should be SAT, got {other:?}"
        ),
    };

    // Validate model satisfies all constraints
    let xv = get_int(&model, "x");
    assert!(xv >= 0, "model must satisfy x >= 0, got x={xv}");
    assert_eq!(
        smt_mod(xv, 2),
        0,
        "model must satisfy (mod x 2) = 0, got x={xv}"
    );
    assert_ne!(
        smt_mod(xv, 6),
        smt_mod(xv + 2, 6),
        "model must satisfy (distinct (mod x 6) (mod (+ x 2) 6)), got x={xv}"
    );
}

/// Simpler version: (distinct (mod x 3) (mod (+ x 2) 3)) AND x >= 0
/// is SAT at x=0: (0 mod 3)=0, (2 mod 3)=2, 0!=2.
///
/// This simpler case remains SAT as a control.
#[test]
fn test_mod_distinct_simple() {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_expr = ChcExpr::var(x);

    let mod_x_3 = ChcExpr::mod_op(x_expr.clone(), ChcExpr::int(3));
    let x_plus_2 = ChcExpr::add(x_expr.clone(), ChcExpr::int(2));
    let mod_x_plus_2_3 = ChcExpr::mod_op(x_plus_2, ChcExpr::int(3));
    let distinct = ChcExpr::ne(mod_x_3, mod_x_plus_2_3);

    let x_ge_0 = ChcExpr::ge(x_expr, ChcExpr::int(0));

    let query = ChcExpr::and(distinct, x_ge_0);

    let mut ctx = SmtContext::new();
    let result = ctx.check_sat(&query);
    let model = match result {
        SmtResult::Sat(m) => m,
        other => panic!(
            "#2881: (distinct (mod x 3) (mod (+ x 2) 3)) AND x >= 0 should be SAT, got {other:?}"
        ),
    };

    // Validate model satisfies all constraints
    let xv = get_int(&model, "x");
    assert!(xv >= 0, "model must satisfy x >= 0, got x={xv}");
    assert_ne!(
        smt_mod(xv, 3),
        smt_mod(xv + 2, 3),
        "model must satisfy (distinct (mod x 3) (mod (+ x 2) 3)), got x={xv}"
    );
}

/// Variant: (distinct (mod x 3) (mod (+ x 1) 3)) AND x >= 0 AND x < 10
/// is SAT at x=0: (0 mod 3)=0, (1 mod 3)=1, 0!=1.
///
/// Tests the +1 offset case which also showed false UNSAT in debug tracing.
#[test]
fn test_mod_distinct_plus_one() {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_expr = ChcExpr::var(x);

    let mod_x_3 = ChcExpr::mod_op(x_expr.clone(), ChcExpr::int(3));
    let x_plus_1 = ChcExpr::add(x_expr.clone(), ChcExpr::int(1));
    let mod_x_plus_1_3 = ChcExpr::mod_op(x_plus_1, ChcExpr::int(3));
    let distinct = ChcExpr::ne(mod_x_3, mod_x_plus_1_3);

    let x_ge_0 = ChcExpr::ge(x_expr.clone(), ChcExpr::int(0));
    let x_lt_10 = ChcExpr::lt(x_expr, ChcExpr::int(10));

    let query = ChcExpr::and_all(vec![distinct, x_ge_0, x_lt_10]);

    let mut ctx = SmtContext::new();
    let result = ctx.check_sat(&query);
    let model = match result {
        SmtResult::Sat(m) => m,
        other => panic!(
            "#2881: (distinct (mod x 3) (mod (+ x 1) 3)) AND x >= 0 AND x < 10 should be SAT, got {other:?}"
        ),
    };

    // Validate model satisfies all constraints
    let xv = get_int(&model, "x");
    assert!(xv >= 0, "model must satisfy x >= 0, got x={xv}");
    assert!(xv < 10, "model must satisfy x < 10, got x={xv}");
    assert_ne!(
        smt_mod(xv, 3),
        smt_mod(xv + 1, 3),
        "model must satisfy (distinct (mod x 3) (mod (+ x 1) 3)), got x={xv}"
    );
}
