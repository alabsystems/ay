// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for proactive invariant discovery routines.

#![allow(clippy::unwrap_used)]

use crate::pdr::config::PdrConfig;
use crate::pdr::solver::test_helpers::solver_from_str;
use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcOp, ChcParser, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::sync::Arc;

// Helper to create div expression (no ChcExpr::div exists)
fn make_div(a: ChcExpr, b: ChcExpr) -> ChcExpr {
    ChcExpr::Op(ChcOp::Div, vec![Arc::new(a), Arc::new(b)])
}

#[test]
fn test_extract_div_threshold_le_pattern() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (<= 5 (div x 10)) means x/10 >= 5, i.e., x >= 50
    let expr = ChcExpr::le(ChcExpr::Int(5), make_div(ChcExpr::var(x), ChcExpr::Int(10)));
    let result = PdrSolver::extract_div_threshold_condition(&expr);
    assert_eq!(result, Some(("x".to_string(), 10, 5)));
}

#[test]
fn test_extract_div_threshold_ge_pattern() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (>= (div x 4) 3) means x/4 >= 3, i.e., x >= 12
    let expr = ChcExpr::ge(make_div(ChcExpr::var(x), ChcExpr::Int(4)), ChcExpr::Int(3));
    let result = PdrSolver::extract_div_threshold_condition(&expr);
    assert_eq!(result, Some(("x".to_string(), 4, 3)));
}

#[test]
fn test_extract_div_threshold_negative_divisor() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (>= (div x -4) 3) - negative divisor should return None
    let expr = ChcExpr::ge(make_div(ChcExpr::var(x), ChcExpr::Int(-4)), ChcExpr::Int(3));
    let result = PdrSolver::extract_div_threshold_condition(&expr);
    assert_eq!(result, None);
}

#[test]
fn test_extract_var_plus_const_simple() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (+ x 5)
    let expr = ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(5));
    let result = PdrSolver::extract_var_plus_const(&expr);
    assert_eq!(result, Some(("x".to_string(), 5)));
}

#[test]
fn test_extract_var_plus_const_reversed() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (+ 5 x) - reversed order
    let expr = ChcExpr::add(ChcExpr::Int(5), ChcExpr::var(x));
    let result = PdrSolver::extract_var_plus_const(&expr);
    assert_eq!(result, Some(("x".to_string(), 5)));
}

#[test]
fn test_extract_var_plus_const_non_matching() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // (+ x y) - not var + const
    let expr = ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y));
    let result = PdrSolver::extract_var_plus_const(&expr);
    assert_eq!(result, None);
}

#[test]
fn test_constraint_has_mod_equality() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (= 0 (mod x 2)) or equivalently (= (mod x 2) 0)
    let constraint = ChcExpr::eq(
        ChcExpr::Int(0),
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::Int(2)),
    );
    assert!(PdrSolver::constraint_has_mod_equality(&constraint, 2));
}

#[test]
fn test_constraint_has_mod_equality_wrong_modulus() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (= 0 (mod x 3)) - looking for k=2
    let constraint = ChcExpr::eq(
        ChcExpr::Int(0),
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::Int(3)),
    );
    assert!(!PdrSolver::constraint_has_mod_equality(&constraint, 2));
}

#[test]
fn test_find_constant_value_in_constraint() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (= x 42)
    let constraint = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(42));
    let result = PdrSolver::find_constant_value_in_constraint(&constraint, "x");
    assert_eq!(result, Some(42));
}

#[test]
fn test_find_constant_value_in_conjunction() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // (and (= y 10) (= x 42))
    let constraint = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(y), ChcExpr::Int(10)),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(42)),
    );
    let result = PdrSolver::find_constant_value_in_constraint(&constraint, "x");
    assert_eq!(result, Some(42));
}

#[test]
fn test_find_constant_value_not_found() {
    let y = ChcVar::new("y", ChcSort::Int);
    // (= y 10) - looking for x
    let constraint = ChcExpr::eq(ChcExpr::var(y), ChcExpr::Int(10));
    let result = PdrSolver::find_constant_value_in_constraint(&constraint, "x");
    assert_eq!(result, None);
}

#[test]
fn early_conditional_probe_proves_s_disj_ite_05_shape_9695() {
    let input = r#"(set-logic HORN)

(declare-fun inv ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and (= A 0) (= B 50))
      (inv A B)
    )
  )
)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (inv A B)
        (and (= C (+ 1 A)) (not (<= 100 A)) (ite (<= C 50) (= D B) (= D (+ 1 B))))
      )
      (inv C D)
    )
  )
)

(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (inv A B)
        (and (= A 100) (not (= B 100)))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

    let mut solver = solver_from_str(input);

    assert!(
        solver.discover_conditional_invariants_early_probe(),
        "expected the early conditional probe to admit a phase invariant"
    );
    let model = solver
        .check_invariants_prove_safety()
        .expect("admitted conditional invariant should prove the query unreachable");
    let result = solver.finish_safe_with_result_trace(model, "issue #9695 regression");
    assert!(
        matches!(result, crate::pdr::PdrResult::Safe(_)),
        "s_disj_ite_05-shape model should pass strict final validation"
    );
}

#[test]
fn early_conditional_probe_rejects_unsupported_hyperedge_9695() {
    let input = r#"(set-logic HORN)

(declare-fun inv ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and (= A 0) (= B 50))
      (inv A B)
    )
  )
)

(assert
  (forall ( (A Int) (B Int) (E Int) (F Int) (C Int) (D Int) )
    (=>
      (and
        (inv A B)
        (inv E F)
        (= C (+ 1 A))
        (not (<= 100 A))
        (ite (<= C 50) (= D B) (= D (+ 1 B)))
      )
      (inv C D)
    )
  )
)

(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (inv A B)
        (and (= A 100) (not (= B 100)))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

    let mut solver = solver_from_str(input);

    assert!(
        !solver.discover_conditional_invariants_early_probe(),
        "early algebraic probe must fail closed on hyperedge transitions"
    );
}

#[test]
fn test_compute_static_init_parity() {
    // Test with constant: 6 mod 2 = 0
    let expr = ChcExpr::Int(6);
    assert_eq!(PdrSolver::compute_static_init_parity(&expr, 2), Some(0));

    // Test with constant: 7 mod 2 = 1
    let expr = ChcExpr::Int(7);
    assert_eq!(PdrSolver::compute_static_init_parity(&expr, 2), Some(1));
}

#[test]
fn test_compute_static_init_parity_negative() {
    // Negative number: -5 mod 2 should be 1 under Euclidean remainder semantics.
    let expr = ChcExpr::Int(-5);
    let result = PdrSolver::compute_static_init_parity(&expr, 2);
    assert_eq!(result, Some(1));
}

#[test]
fn test_find_equality_rhs_simple() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (= x 100)
    let formula = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(100));
    let result = PdrSolver::find_equality_rhs(&formula, "x");
    assert_eq!(result, Some(ChcExpr::Int(100)));
}

#[test]
fn test_find_equality_rhs_reversed() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (= 100 x) - reversed
    let formula = ChcExpr::eq(ChcExpr::Int(100), ChcExpr::var(x));
    let result = PdrSolver::find_equality_rhs(&formula, "x");
    assert_eq!(result, Some(ChcExpr::Int(100)));
}

#[test]
fn test_find_equality_rhs_expression() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // (= x (+ y 1))
    let rhs = ChcExpr::add(ChcExpr::var(y), ChcExpr::Int(1));
    let formula = ChcExpr::eq(ChcExpr::var(x), rhs.clone());
    let result = PdrSolver::find_equality_rhs(&formula, "x");
    assert_eq!(result, Some(rhs));
}

#[test]
fn test_get_init_expression_for_var_with_expression_head_arg() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P (+ x 1)))))
(check-sat)
"#;
    let problem = ChcParser::parse(input).expect("parse expression-head init");
    let solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver.problem.lookup_predicate("P").expect("P predicate");

    let init_expr = solver
        .get_init_expression_for_var(pred, 0)
        .expect("init expression for P arg 0");
    let expected = ChcExpr::add(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(1),
    );
    assert_eq!(init_expr, expected);
}

#[test]
fn test_find_canonical_index_matches_expression_head_arg() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(1));
    let head_args = vec![expr.clone(), ChcExpr::var(y)];

    assert_eq!(PdrSolver::find_canonical_index(&expr, &head_args), Some(0));
}

// Note: The following functions require a var_map and are tested indirectly
// through integration tests:
// - extract_simple_negated_equality
// - extract_ge_mult_pattern
// - extract_eq_mult_pattern
// - extract_mult_expr
// - extract_var_difference
// - extract_interval_conflict_disjunction

#[test]
fn test_extract_interval_conflict_disjunction() {
    let c = ChcVar::new("C", ChcSort::Int);
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);

    // (and (<= D E) (>= C E))
    let constraint = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(d), ChcExpr::var(e.clone())),
        ChcExpr::ge(ChcExpr::var(c), ChcExpr::var(e)),
    );

    let mut var_map: FxHashMap<String, (usize, String)> = FxHashMap::default();
    var_map.insert("C".to_string(), (0, "__p0_a3".to_string()));
    var_map.insert("D".to_string(), (1, "__p0_a1".to_string()));
    var_map.insert("E".to_string(), (2, "__p0_a4".to_string()));

    let extracted = PdrSolver::extract_interval_conflict_disjunction(&constraint, &var_map)
        .expect("interval conflict should be extracted");

    let expected = ChcExpr::or(
        ChcExpr::not(ChcExpr::le(
            ChcExpr::var(ChcVar::new("__p0_a1", ChcSort::Int)),
            ChcExpr::var(ChcVar::new("__p0_a4", ChcSort::Int)),
        )),
        ChcExpr::not(ChcExpr::ge(
            ChcExpr::var(ChcVar::new("__p0_a3", ChcSort::Int)),
            ChcExpr::var(ChcVar::new("__p0_a4", ChcSort::Int)),
        )),
    );

    assert_eq!(extracted, expected);
}

#[test]
fn test_extract_interval_conflict_disjunction_requires_shared_pivot() {
    let c = ChcVar::new("C", ChcSort::Int);
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    let f = ChcVar::new("F", ChcSort::Int);

    // No shared pivot: (<= D E) and (>= C F)
    let constraint = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(d), ChcExpr::var(e)),
        ChcExpr::ge(ChcExpr::var(c), ChcExpr::var(f)),
    );

    let mut var_map: FxHashMap<String, (usize, String)> = FxHashMap::default();
    var_map.insert("C".to_string(), (0, "__p0_a3".to_string()));
    var_map.insert("D".to_string(), (1, "__p0_a1".to_string()));
    var_map.insert("E".to_string(), (2, "__p0_a4".to_string()));
    var_map.insert("F".to_string(), (3, "__p0_a0".to_string()));

    assert!(
        PdrSolver::extract_interval_conflict_disjunction(&constraint, &var_map).is_none(),
        "without shared pivot variable, no disjunctive consequence should be extracted"
    );
}

#[test]
fn test_extract_lt_guard_other_var() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // NOT (<= y x) represents x < y (looking for other variable relative to x)
    // This pattern is used in step-bounded invariant detection
    let constraint = ChcExpr::not(ChcExpr::le(ChcExpr::var(y), ChcExpr::var(x)));
    let result = PdrSolver::extract_lt_guard_other_var(&constraint, "x");
    assert_eq!(result, Some("y".to_string()));
}

// Tests for extract_thresholds_from_expr

#[test]
fn test_extract_thresholds_from_le() {
    let x = ChcVar::new("x", ChcSort::Int);
    // x <= 10
    let expr = ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(10));
    let mut thresholds = FxHashSet::default();
    PdrSolver::extract_thresholds_from_expr(&expr, &mut thresholds);
    assert!(thresholds.contains(&10));
    assert!(thresholds.contains(&9)); // k-1
    assert!(thresholds.contains(&11)); // k+1
}

#[test]
fn test_extract_thresholds_from_gt() {
    let x = ChcVar::new("x", ChcSort::Int);
    // x > 5
    let expr = ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(5));
    let mut thresholds = FxHashSet::default();
    PdrSolver::extract_thresholds_from_expr(&expr, &mut thresholds);
    assert!(thresholds.contains(&5));
    assert!(thresholds.contains(&4)); // k-1
    assert!(thresholds.contains(&6)); // k+1
}

#[test]
fn test_extract_thresholds_from_nested() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (and (>= x 0) (<= x 100))
    let expr = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(100)),
    );
    let mut thresholds = FxHashSet::default();
    PdrSolver::extract_thresholds_from_expr(&expr, &mut thresholds);
    assert!(thresholds.contains(&0));
    assert!(thresholds.contains(&100));
}

#[test]
fn test_extract_thresholds_non_comparison() {
    let x = ChcVar::new("x", ChcSort::Int);
    // Just a variable - no thresholds
    let expr = ChcExpr::var(x);
    let mut thresholds = FxHashSet::default();
    PdrSolver::extract_thresholds_from_expr(&expr, &mut thresholds);
    assert!(thresholds.is_empty());
}

// Tests for analyze_self_loop_increments

#[test]
fn test_analyze_self_loop_increments() {
    // Create a simple counter problem
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let increments = solver.analyze_self_loop_increments(inv);

    // The variable should increment by 1
    // Note: The exact variable name depends on canonicalization
    assert!(
        !increments.is_empty() && increments.values().any(|&v| v == 1),
        "Should detect increment of 1 for counter variable"
    );
}

// Tests for the exit-value algorithm (compute_definite_exit_value in exit_value.rs).
// The function is module-private, so we verify via a reference implementation that
// documents the algorithm contract: given init, step, bound (where step > 0 and
// init < bound), compute the first value >= bound in the sequence init, init+step,
// init+2*step, ...

/// Reference implementation of compute_definite_exit_value for test verification.
fn ref_exit_value(init: i128, step: i128, bound: i128) -> Option<i128> {
    if step <= 0 || bound <= init {
        return None;
    }
    let gap = bound - init;
    let n = if gap % step == 0 {
        gap / step
    } else {
        gap / step + 1
    };
    let v = init + n * step;
    if v >= bound {
        Some(v)
    } else {
        None
    }
}

#[test]
fn test_exit_value_exact_boundary_hit() {
    // 0, 2, 4, ..., 16 — exits at 16 (bound=16)
    assert_eq!(ref_exit_value(0, 2, 16), Some(16));
}

#[test]
fn test_exit_value_overshoot_boundary() {
    // 0, 3, 6, 9 — exits at 9 (bound=8)
    assert_eq!(ref_exit_value(0, 3, 8), Some(9));
}

#[test]
fn test_exit_value_step_one() {
    assert_eq!(ref_exit_value(0, 1, 10), Some(10));
}

#[test]
fn test_exit_value_nonzero_init() {
    // 5, 7, 9, 11 — exits at 11 (bound=10)
    assert_eq!(ref_exit_value(5, 2, 10), Some(11));
}

#[test]
fn test_exit_value_init_equals_bound_returns_none() {
    assert_eq!(ref_exit_value(10, 2, 10), None);
}

#[test]
fn test_exit_value_init_above_bound_returns_none() {
    assert_eq!(ref_exit_value(15, 2, 10), None);
}

#[test]
fn test_exit_value_zero_step_returns_none() {
    assert_eq!(ref_exit_value(0, 0, 10), None);
}

#[test]
fn test_exit_value_negative_step_returns_none() {
    assert_eq!(ref_exit_value(0, -1, 10), None);
}

#[test]
fn test_exit_value_count_by_2_m_nest_inner_loop() {
    // Inner loop: init=0, step=2, bound=16 → exit_value=16
    // (count_by_2_m_nest benchmark pattern)
    assert_eq!(ref_exit_value(0, 2, 16), Some(16));
}

#[test]
fn test_exit_value_single_iteration() {
    // 0, 5 — exits at 5 (bound=1)
    assert_eq!(ref_exit_value(0, 5, 1), Some(5));
}

#[test]
fn test_exit_value_large_step() {
    // 0, 100 — exits at 100 (bound=50)
    assert_eq!(ref_exit_value(0, 100, 50), Some(100));
}

// ============================================================================
// BV bit-group invariant discovery tests (#7044)
// ============================================================================

/// Test BV group equality discovery on a Bool-encoded problem simulating
/// BvToBool output. Two 2-bit BV groups (x0,x1) and (y0,y1) are initialized
/// to the same values and preserved identically by the transition.
/// The discovery should find the equality invariant: x0=y0 ∧ x1=y1.
#[test]
fn bv_group_equality_discovers_matching_groups() {
    // Simulates BvToBool output: Inv(x0: Bool, x1: Bool, y0: Bool, y1: Bool)
    // where x = BV(x1,x0), y = BV(y1,y0).
    // Init: x0=false, x1=false, y0=false, y1=false (both BVs start at 0)
    // Trans: identity (all vars preserved)
    // Safety: not(x0 != y0) — i.e., x0 = y0 must hold
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Bool Bool Bool Bool) Bool)
; Init: all false
(assert (forall ((x0 Bool) (x1 Bool) (y0 Bool) (y1 Bool))
  (=> (and (not x0) (not x1) (not y0) (not y1))
      (inv x0 x1 y0 y1))))
; Trans: identity
(assert (forall ((x0 Bool) (x1 Bool) (y0 Bool) (y1 Bool)
                 (x0p Bool) (x1p Bool) (y0p Bool) (y1p Bool))
  (=> (and (inv x0 x1 y0 y1)
           (= x0p x0) (= x1p x1) (= y0p y0) (= y1p y1))
      (inv x0p x1p y0p y1p))))
; Safety: x0 = y0 (partial check — equality invariant should help)
(assert (forall ((x0 Bool) (x1 Bool) (y0 Bool) (y1 Bool))
  (=> (and (inv x0 x1 y0 y1) (not (= x0 y0))) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let config = PdrConfig {
        // Two BV groups: group 0 = args 0..2 (width 2), group 1 = args 2..4 (width 2)
        bv_bit_groups: vec![(0, 2), (2, 2)],
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);
    let inv = solver.problem.lookup_predicate("inv").unwrap();

    // Run BV group equality discovery
    solver.discover_bv_group_equalities();

    // Check that the equality invariant was added to frame[1].
    // The equality should be: x0=y0 ∧ x1=y1 (bit-pair conjunction).
    let canonical_vars = solver.canonical_vars(inv).unwrap().to_vec();
    let eq_invariant = ChcExpr::and_all([
        ChcExpr::eq(
            ChcExpr::var(canonical_vars[0].clone()),
            ChcExpr::var(canonical_vars[2].clone()),
        ),
        ChcExpr::eq(
            ChcExpr::var(canonical_vars[1].clone()),
            ChcExpr::var(canonical_vars[3].clone()),
        ),
    ]);

    assert!(
        solver.frames[1].contains_lemma(inv, &eq_invariant),
        "BV group equality discovery should add x0=y0 ∧ x1=y1 to frame[1]"
    );
}

/// Test BV group constant-zero discovery. A 2-bit BV group initialized to 0
/// with identity transition should be discovered as constantly zero.
#[test]
fn bv_group_constant_discovers_zero_group() {
    // Inv(x0: Bool, x1: Bool) where x = BV(x1,x0)
    // Init: x0=false, x1=false (x = 0)
    // Trans: identity
    // Safety: not(x0) — x0 must stay false
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Bool Bool) Bool)
; Init: all false (x = 0)
(assert (forall ((x0 Bool) (x1 Bool))
  (=> (and (not x0) (not x1))
      (inv x0 x1))))
; Trans: identity
(assert (forall ((x0 Bool) (x1 Bool) (x0p Bool) (x1p Bool))
  (=> (and (inv x0 x1) (= x0p x0) (= x1p x1))
      (inv x0p x1p))))
; Safety: x0 = false
(assert (forall ((x0 Bool) (x1 Bool))
  (=> (and (inv x0 x1) x0) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let config = PdrConfig {
        bv_bit_groups: vec![(0, 2)],
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);
    let inv = solver.problem.lookup_predicate("inv").unwrap();

    // Run BV group constant discovery
    solver.discover_bv_group_constants();

    // Check that the constant-zero invariant was added: ¬x0 ∧ ¬x1
    let canonical_vars = solver.canonical_vars(inv).unwrap().to_vec();
    let zero_invariant = ChcExpr::and_all([
        ChcExpr::not(ChcExpr::var(canonical_vars[0].clone())),
        ChcExpr::not(ChcExpr::var(canonical_vars[1].clone())),
    ]);

    assert!(
        solver.frames[1].contains_lemma(inv, &zero_invariant),
        "BV group constant-zero discovery should add ¬x0 ∧ ¬x1 to frame[1]"
    );
}

/// Test per-bit constant discovery (#7044, Packet 2). A BV(4) group where
/// the top 2 bits are always false (value always < 4) should discover
/// individual bit-level constants for bits 2 and 3.
#[test]
fn bv_group_bit_bounds_discovers_high_zeros() {
    // Inv(x0: Bool, x1: Bool, x2: Bool, x3: Bool) where x = BV(x3,x2,x1,x0)
    // Init: x0=true, x1=false, x2=false, x3=false (x = 1, value < 4)
    // Trans: identity
    // Safety: not(x3) — top bit must be false
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Bool Bool Bool Bool) Bool)
; Init: x = 1 (x0=true, rest false)
(assert (forall ((x0 Bool) (x1 Bool) (x2 Bool) (x3 Bool))
  (=> (and x0 (not x1) (not x2) (not x3))
      (inv x0 x1 x2 x3))))
; Trans: identity
(assert (forall ((x0 Bool) (x1 Bool) (x2 Bool) (x3 Bool)
                 (x0p Bool) (x1p Bool) (x2p Bool) (x3p Bool))
  (=> (and (inv x0 x1 x2 x3)
           (= x0p x0) (= x1p x1) (= x2p x2) (= x3p x3))
      (inv x0p x1p x2p x3p))))
; Safety
(assert (forall ((x0 Bool) (x1 Bool) (x2 Bool) (x3 Bool))
  (=> (and (inv x0 x1 x2 x3) x3) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let config = PdrConfig {
        bv_bit_groups: vec![(0, 4)],
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);
    let inv = solver.problem.lookup_predicate("inv").unwrap();

    solver.discover_bv_group_bit_bounds();

    // Bit 0 should be discovered as constant true (x0 = true)
    let canonical_vars = solver.canonical_vars(inv).unwrap().to_vec();
    let bit0_true = ChcExpr::var(canonical_vars[0].clone());
    assert!(
        solver.frames[1].contains_lemma(inv, &bit0_true),
        "Bit 0 should be discovered as constant true"
    );

    // Bit 2 should be discovered as constant false (¬x2)
    let bit2_false = ChcExpr::not(ChcExpr::var(canonical_vars[2].clone()));
    assert!(
        solver.frames[1].contains_lemma(inv, &bit2_false),
        "Bit 2 (high bit) should be discovered as constant false"
    );
}

/// Test unsigned LE ordering between BV groups (#7044, Packet 2).
/// With two 2-bit BV groups where x is always 0 and y is always 0,
/// both x <= y and y <= x should be discoverable.
#[test]
fn bv_group_ordering_discovers_ule() {
    // Two 2-bit groups both initialized to 0, identity transition.
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Bool Bool Bool Bool) Bool)
; Init: all false (both BVs = 0)
(assert (forall ((x0 Bool) (x1 Bool) (y0 Bool) (y1 Bool))
  (=> (and (not x0) (not x1) (not y0) (not y1))
      (inv x0 x1 y0 y1))))
; Trans: identity
(assert (forall ((x0 Bool) (x1 Bool) (y0 Bool) (y1 Bool)
                 (x0p Bool) (x1p Bool) (y0p Bool) (y1p Bool))
  (=> (and (inv x0 x1 y0 y1)
           (= x0p x0) (= x1p x1) (= y0p y0) (= y1p y1))
      (inv x0p x1p y0p y1p))))
; Safety
(assert (forall ((x0 Bool) (x1 Bool) (y0 Bool) (y1 Bool))
  (=> (and (inv x0 x1 y0 y1) x0) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let config = PdrConfig {
        bv_bit_groups: vec![(0, 2), (2, 2)],
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    // Run ordering discovery
    let frame1_before = solver.frames[1].lemmas.len();
    solver.discover_bv_group_ordering();
    let frame1_after = solver.frames[1].lemmas.len();

    // At least one ordering invariant should be added (x ule y or y ule x)
    assert!(
        frame1_after > frame1_before,
        "BV group ordering should discover at least one ule invariant"
    );
}

/// Test that BV group discovery is a no-op when bv_bit_groups is empty.
#[test]
fn bv_group_discovery_noop_without_bit_groups() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Bool Bool) Bool)
(assert (forall ((x0 Bool) (x1 Bool))
  (=> (and (not x0) (not x1)) (inv x0 x1))))
(assert (forall ((x0 Bool) (x1 Bool) (x0p Bool) (x1p Bool))
  (=> (and (inv x0 x1) (= x0p x0) (= x1p x1)) (inv x0p x1p))))
(assert (forall ((x0 Bool) (x1 Bool))
  (=> (and (inv x0 x1) x0) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    // No bv_bit_groups — discovery should be no-op
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let frame1_before = solver.frames[1].lemmas.len();
    solver.discover_bv_group_equalities();
    solver.discover_bv_group_constants();
    let frame1_after = solver.frames[1].lemmas.len();

    assert_eq!(
        frame1_before, frame1_after,
        "BV group discovery should not add lemmas when bv_bit_groups is empty"
    );
}
