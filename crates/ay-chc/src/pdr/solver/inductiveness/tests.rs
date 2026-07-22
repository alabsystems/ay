// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
use crate::parser::ChcParser;
use crate::pdr::config::PdrConfig;
use crate::pdr::frame::{Frame, Lemma};
use crate::pdr::solver::test_helpers::solver_from_str;
use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
#[path = "entry_failure_tests.rs"]
mod entry_failure_tests;
#[path = "get_constant_tests.rs"]
mod get_constant_tests;
#[path = "issue_5877_tests.rs"]
mod issue_5877_tests;
#[path = "issue_6358_tests.rs"]
mod issue_6358_tests;
#[path = "issue_6366_tests.rs"]
mod issue_6366_tests;

#[test]
fn test_substitute_canonical_vars() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let canonical_vars = vec![a.clone(), b.clone()];
    // a + b
    let formula = ChcExpr::add(ChcExpr::var(a), ChcExpr::var(b));
    let args = vec![ChcExpr::Int(3), ChcExpr::Int(7)];
    let result = PdrSolver::substitute_canonical_vars(&formula, &canonical_vars, &args);
    // 3 + 7
    assert_eq!(result, ChcExpr::add(ChcExpr::Int(3), ChcExpr::Int(7)));
}

#[test]
fn test_substitute_canonical_vars_length_mismatch() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let canonical_vars = vec![a.clone(), b.clone()];
    let formula = ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::var(b.clone()));
    // Only one arg - mismatch
    let args = vec![ChcExpr::Int(3)];
    let result = PdrSolver::substitute_canonical_vars(&formula, &canonical_vars, &args);
    // Should return formula unchanged
    assert_eq!(result, ChcExpr::add(ChcExpr::var(a), ChcExpr::var(b)));
}

#[test]
fn test_get_constant_int() {
    let expr = ChcExpr::Int(42);
    assert_eq!(PdrSolver::get_constant(&expr), Some(42));
}

#[test]
fn test_get_constant_negative() {
    // (neg 42) should be recognized as -42
    let expr = ChcExpr::neg(ChcExpr::Int(42));
    assert_eq!(PdrSolver::get_constant(&expr), Some(-42));
}

#[test]
fn test_get_constant_non_constant() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::var(x);
    assert_eq!(PdrSolver::get_constant(&expr), None);
}

#[test]
fn test_is_var_expr_match() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::var(x);
    assert!(PdrSolver::is_var_expr(&expr, "x"));
}

#[test]
fn test_is_var_expr_no_match() {
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::var(y);
    assert!(!PdrSolver::is_var_expr(&expr, "x"));
}

#[test]
fn test_extract_addition_offset_simple() {
    let x = ChcVar::new("x", ChcSort::Int);
    // x + 5
    let expr = ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(5));
    assert_eq!(PdrSolver::extract_addition_offset(&expr, "x"), Some(5));
}

#[test]
fn test_extract_addition_offset_reverse() {
    let x = ChcVar::new("x", ChcSort::Int);
    // 5 + x
    let expr = ChcExpr::add(ChcExpr::Int(5), ChcExpr::var(x));
    assert_eq!(PdrSolver::extract_addition_offset(&expr, "x"), Some(5));
}

#[test]
fn test_extract_addition_offset_identity() {
    let x = ChcVar::new("x", ChcSort::Int);
    // Just x (identity)
    let expr = ChcExpr::var(x);
    assert_eq!(PdrSolver::extract_addition_offset(&expr, "x"), Some(0));
}

#[test]
fn test_algebraic_parity_preserved_identity() {
    let x = ChcVar::new("x", ChcSort::Int);
    let pre = ChcExpr::var(x.clone());
    let post = ChcExpr::var(x);
    // Identity: pre == post, parity always preserved
    assert!(PdrSolver::algebraic_parity_preserved(&pre, &post, None, 2));
}

#[test]
fn test_algebraic_parity_preserved_even_offset() {
    let pre_var = ChcVar::new("pre_x", ChcSort::Int);
    // post = pre_x + 4 with k=2: 4 mod 2 == 0, so parity preserved
    let pre = ChcExpr::var(pre_var.clone());
    let post = ChcExpr::add(ChcExpr::var(pre_var), ChcExpr::Int(4));
    // Test with a constraint that binds pre to post via the +4 offset
    // Algebraically: if post = pre + 4 and k=2, then post mod 2 == pre mod 2
    assert!(PdrSolver::algebraic_parity_preserved(&pre, &post, None, 2));
}

#[test]
fn test_is_parity_preserved_by_transitions_rejects_increment_by_one() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 10) (inv x))))
(assert (forall ((x Int) (x_next Int))
  (=> (and (inv x) (= x_next (+ x 1))) (inv x_next))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();

    // x' = x + 1 does not preserve mod 4 parity.
    assert!(
        !solver.is_parity_preserved_by_transitions(inv, &x, 4, 2),
        "x' = x + 1 must not preserve x mod 4 = 2"
    );
}

#[test]
fn test_discover_parity_invariants_skips_non_inductive_increment_by_one() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((i Int) (n Int)) (=> (and (= i 0) (= n 10)) (inv i n))))
(assert
  (forall ((i Int) (n Int) (i_next Int) (n_next Int))
    (=> (and (inv i n) (= i_next (+ i 1)) (= n_next (+ n 1))) (inv i_next n_next))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    solver.discover_parity_invariants(None);

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let has_parity_lemma = solver.frames[1]
            .lemmas
            .iter()
            .filter(|l| l.predicate == inv)
            .any(|l| {
                matches!(
                    &l.formula,
                    ChcExpr::Op(ChcOp::Eq, args)
                        if args.len() == 2
                            && matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Mod, mod_args) if mod_args.len() == 2)
                )
            });

    assert!(
        !has_parity_lemma,
        "increment-by-one transition must not learn parity invariants"
    );
}

#[test]
fn test_add_discovered_invariant_rejects_non_inductive_parity_formula() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 10) (inv x))))
(assert (forall ((x Int) (x_next Int))
  (=> (and (inv x) (= x_next (+ x 1))) (inv x_next))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();
    let parity = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::Int(4)),
        ChcExpr::Int(2),
    );

    assert!(
        !solver.add_discovered_invariant(inv, parity.clone(), 1),
        "non-inductive parity invariant must be rejected by discovery gate"
    );
    assert!(
        !solver.frames[1].contains_lemma(inv, &parity),
        "rejected parity invariant must not be inserted into frame 1"
    );
}

#[test]
fn test_add_discovered_invariant_accepts_inductive_parity_formula() {
    // x starts at 0, increments by 2 each step => x mod 2 = 0 is inductive.
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x_next Int))
  (=> (and (inv x) (= x_next (+ x 2))) (inv x_next))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();
    let parity = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::Int(2)),
        ChcExpr::Int(0),
    );

    assert!(
        solver.add_discovered_invariant(inv, parity.clone(), 1),
        "inductive parity invariant (x mod 2 = 0) must be accepted"
    );
    assert!(
        solver.frames[1].contains_lemma(inv, &parity),
        "accepted parity invariant must be present in frame 1"
    );
}

#[test]
fn test_extract_sum_terms_addition() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    // a + b
    let expr = ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::var(b.clone()));
    let terms = PdrSolver::extract_sum_terms(&expr);
    assert_eq!(terms.len(), 2);
    assert!(terms.contains(&ChcExpr::var(a)));
    assert!(terms.contains(&ChcExpr::var(b)));
}

#[test]
fn test_extract_sum_terms_single() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::var(x.clone());
    let terms = PdrSolver::extract_sum_terms(&expr);
    assert_eq!(terms.len(), 1);
    assert!(terms.contains(&ChcExpr::var(x)));
}

#[test]
fn test_is_inductive_blocking_populates_prop_solver_issue_6358() {
    let mut solver = solver_from_str(
        r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x_next Int))
  (=> (and (inv x) (= x_next (+ x 1))) (inv x_next))))
(check-sat)
"#,
    );
    let pred = solver
        .problem
        .lookup_predicate("inv")
        .expect("predicate inv");
    let x = solver.canonical_vars(pred).expect("canonical vars")[0].clone();
    let blocking_formula = ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0));

    assert!(solver.is_inductive_blocking(&blocking_formula, pred, 0));
    // prop_solver is only populated when incremental_pdr_enabled() is true.
    // For LIA problems, incremental PDR is disabled (#6583/#8205).
    if solver.incremental_pdr_enabled() {
        assert!(
            solver.prop_solvers.contains_key(&pred),
            "level-0 inductiveness check should allocate the per-predicate prop_solver"
        );
    }
}

#[test]
fn test_find_var_definition_equality() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (= x 5)
    let constraint = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(5));
    let result = PdrSolver::find_var_definition(&constraint, "x");
    assert_eq!(result, Some(ChcExpr::Int(5)));
}

#[test]
fn test_find_var_definition_equality_reversed() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (= 5 x) - reversed order
    let constraint = ChcExpr::eq(ChcExpr::Int(5), ChcExpr::var(x));
    let result = PdrSolver::find_var_definition(&constraint, "x");
    assert_eq!(result, Some(ChcExpr::Int(5)));
}

#[test]
fn test_find_var_definition_in_conjunction() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // (and (= x 5) (>= y 0))
    let constraint = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(5)),
        ChcExpr::ge(ChcExpr::var(y), ChcExpr::Int(0)),
    );
    let result = PdrSolver::find_var_definition(&constraint, "x");
    assert_eq!(result, Some(ChcExpr::Int(5)));
}

#[test]
fn test_is_inductive_blocking_with_solver() {
    // Test is_inductive_blocking with a simple CHC problem
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 10)) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (>= x 10)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();

    // Test blocking formula: x < 0
    // The corresponding lemma is NOT(x < 0) = (x >= 0)
    // This lemma IS compatible with init (x = 0 satisfies x >= 0)
    let x_lt_0 = ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0));

    // Initialize frames for PDR
    solver.frames.push(Frame::default());
    solver.frames.push(Frame::default());

    let result = solver.is_inductive_blocking(&x_lt_0, inv, 1);
    // Blocking x < 0 yields lemma x >= 0, which is valid for this counter
    // (init has x=0 which satisfies x >= 0, and x+1 >= 0 when x >= 0)
    assert!(
        result,
        "blocking x < 0 should be inductive (lemma x >= 0 is valid)"
    );
}

// Tests for find_or_constraint

#[test]
fn test_find_or_constraint_direct_or() {
    let a = ChcVar::new("a", ChcSort::Bool);
    let b = ChcVar::new("b", ChcSort::Bool);
    // (or a b)
    let or_expr = ChcExpr::or(ChcExpr::var(a), ChcExpr::var(b));
    let result = PdrSolver::find_or_constraint(&or_expr);
    assert!(result.is_some());
    assert_eq!(result.unwrap(), or_expr);
}

#[test]
fn test_find_or_constraint_nested_in_and() {
    let a = ChcVar::new("a", ChcSort::Bool);
    let b = ChcVar::new("b", ChcSort::Bool);
    let c = ChcVar::new("c", ChcSort::Bool);
    // (and c (or a b))
    let or_expr = ChcExpr::or(ChcExpr::var(a), ChcExpr::var(b));
    let and_expr = ChcExpr::and(ChcExpr::var(c), or_expr.clone());
    let result = PdrSolver::find_or_constraint(&and_expr);
    assert!(result.is_some());
    assert_eq!(result.unwrap(), or_expr);
}

#[test]
fn test_find_or_constraint_none() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (>= x 0) - no OR
    let ge_expr = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));
    let result = PdrSolver::find_or_constraint(&ge_expr);
    assert!(result.is_none());
}

// Tests for extract_any_offset

#[test]
fn test_extract_any_offset_variable() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::var(x);
    assert_eq!(PdrSolver::extract_any_offset(&expr), Some(0));
}

#[test]
fn test_extract_any_offset_constant() {
    let expr = ChcExpr::Int(42);
    assert_eq!(PdrSolver::extract_any_offset(&expr), Some(42));
}

#[test]
fn test_extract_any_offset_neg() {
    let expr = ChcExpr::neg(ChcExpr::Int(5));
    assert_eq!(PdrSolver::extract_any_offset(&expr), Some(-5));
}

#[test]
fn test_extract_any_offset_add_with_constant() {
    let y = ChcVar::new("y", ChcSort::Int);
    // y + 10
    let expr = ChcExpr::add(ChcExpr::var(y), ChcExpr::Int(10));
    assert_eq!(PdrSolver::extract_any_offset(&expr), Some(10));
}

#[test]
fn test_extract_any_offset_sub_with_constant() {
    let y = ChcVar::new("y", ChcSort::Int);
    // y - 3
    let expr = ChcExpr::sub(ChcExpr::var(y), ChcExpr::Int(3));
    assert_eq!(PdrSolver::extract_any_offset(&expr), Some(-3));
}

// Tests for find_var_offset_in_conjuncts

#[test]
fn test_find_var_offset_in_conjuncts_simple_eq() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (= x 5)
    let eq_expr = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(5));
    let result = PdrSolver::find_var_offset_in_conjuncts(&eq_expr, "x");
    assert_eq!(result, Some(5));
}

#[test]
fn test_find_var_offset_in_conjuncts_add() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // (= x (+ y 7))
    let eq_expr = ChcExpr::eq(
        ChcExpr::var(x),
        ChcExpr::add(ChcExpr::var(y), ChcExpr::Int(7)),
    );
    let result = PdrSolver::find_var_offset_in_conjuncts(&eq_expr, "x");
    assert_eq!(result, Some(7));
}

#[test]
fn test_find_var_offset_in_conjuncts_in_and() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // (and (>= y 0) (= x 3))
    let and_expr = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(y), ChcExpr::Int(0)),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(3)),
    );
    let result = PdrSolver::find_var_offset_in_conjuncts(&and_expr, "x");
    assert_eq!(result, Some(3));
}

// Tests for find_offset_in_constraint

#[test]
fn test_find_offset_in_constraint_simple() {
    let pre = ChcVar::new("pre_x", ChcSort::Int);
    let post = ChcVar::new("post_x", ChcSort::Int);
    // (= post_x (+ pre_x 1))
    let eq_expr = ChcExpr::eq(
        ChcExpr::var(post),
        ChcExpr::add(ChcExpr::var(pre), ChcExpr::Int(1)),
    );
    let result = PdrSolver::find_offset_in_constraint(&eq_expr, "pre_x", "post_x");
    assert_eq!(result, Some(1));
}

#[test]
fn test_find_offset_in_constraint_reversed() {
    let pre = ChcVar::new("pre_x", ChcSort::Int);
    let post = ChcVar::new("post_x", ChcSort::Int);
    // (= (+ pre_x 2) post_x)
    let eq_expr = ChcExpr::eq(
        ChcExpr::add(ChcExpr::var(pre), ChcExpr::Int(2)),
        ChcExpr::var(post),
    );
    let result = PdrSolver::find_offset_in_constraint(&eq_expr, "pre_x", "post_x");
    assert_eq!(result, Some(2));
}

#[test]
fn test_find_offset_in_constraint_in_conjunction() {
    let pre = ChcVar::new("pre_x", ChcSort::Int);
    let post = ChcVar::new("post_x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // (and (>= y 0) (= post_x (+ pre_x 5)))
    let and_expr = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(y), ChcExpr::Int(0)),
        ChcExpr::eq(
            ChcExpr::var(post),
            ChcExpr::add(ChcExpr::var(pre), ChcExpr::Int(5)),
        ),
    );
    let result = PdrSolver::find_offset_in_constraint(&and_expr, "pre_x", "post_x");
    assert_eq!(result, Some(5));
}

#[test]
fn test_find_offset_in_constraint_identity() {
    let pre = ChcVar::new("pre_x", ChcSort::Int);
    let post = ChcVar::new("post_x", ChcSort::Int);
    // (= post_x pre_x) - identity, offset 0
    let eq_expr = ChcExpr::eq(ChcExpr::var(post), ChcExpr::var(pre));
    let result = PdrSolver::find_offset_in_constraint(&eq_expr, "pre_x", "post_x");
    assert_eq!(result, Some(0));
}

#[test]
fn test_find_offset_in_constraint_no_match() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (>= x 0) - not an equality
    let ge_expr = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));
    let result = PdrSolver::find_offset_in_constraint(&ge_expr, "pre_x", "post_x");
    assert_eq!(result, None);
}

// Tests for rename_to_canonical_vars

#[test]
fn test_rename_to_canonical_vars_simple() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 10)) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (>= x 10)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let canonical_vars = solver.canonical_vars(inv).unwrap();

    // Create a formula with a non-canonical variable name "y"
    let non_canonical_var = ChcVar::new("y", ChcSort::Int);
    let formula = ChcExpr::ge(ChcExpr::var(non_canonical_var), ChcExpr::Int(0));

    // The mapping should rename "y" to the canonical name
    let mut name_map = FxHashMap::default();
    name_map.insert("y".to_string(), canonical_vars[0].name.clone());
    let result = PdrSolver::rename_to_canonical_vars(&formula, &name_map);

    // Check that the variable was renamed
    if let ChcExpr::Op(ChcOp::Ge, ref renamed_args) = result {
        if let ChcExpr::Var(ref v) = renamed_args[0].as_ref() {
            assert_eq!(v.name, canonical_vars[0].name);
        } else {
            panic!("Expected variable in result");
        }
    } else {
        panic!("Expected >= expression (got {result:?})");
    }
}

// Tests for blocks_initial_states

#[test]
fn test_blocks_initial_states_blocking_formula() {
    // x < 0 should block init (init has x = 0)
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();

    // x < 0 should block init state (x = 0 doesn't satisfy x < 0)
    let x_lt_0 = ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0));
    assert!(
        solver.blocks_initial_states(inv, &x_lt_0),
        "x < 0 should block init where x = 0"
    );
}

#[test]
fn test_blocks_initial_states_non_blocking_formula() {
    // x >= 0 should NOT block init (init has x = 0 which satisfies x >= 0)
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();

    // x >= 0 does NOT block init (x = 0 satisfies x >= 0)
    let x_ge_0 = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));
    assert!(
        !solver.blocks_initial_states(inv, &x_ge_0),
        "x >= 0 should NOT block init where x = 0"
    );
}

#[test]
fn test_blocks_initial_states_equality_blocking() {
    // x = 5 should block init (init has x = 0)
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();

    // x = 5 should block init (x = 0 doesn't satisfy x = 5)
    let x_eq_5 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(5));
    assert!(
        solver.blocks_initial_states(inv, &x_eq_5),
        "x = 5 should block init where x = 0"
    );
}

// Tests for is_self_inductive_blocking

#[test]
fn test_is_self_inductive_blocking_simple() {
    // For a counter that increments, x >= 0 should be self-inductive
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();

    // Initialize frames
    solver.frames.push(Frame::default());
    solver.frames.push(Frame::default());

    // Blocking x < 0: the lemma NOT(x < 0) = x >= 0 should be self-inductive
    // because if x >= 0, then x + 1 >= 0
    let x_lt_0 = ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0));
    let result = solver.is_self_inductive_blocking(&x_lt_0, inv);
    assert!(
        result,
        "blocking x < 0 should be self-inductive (lemma x >= 0)"
    );
}

#[test]
fn test_strict_self_inductive_checks_hyperedge_self_loop_sat_case() {
    // Regression for #2059: strict self-inductive checks must not skip
    // hyperedge self-loops. This clause has a self-loop on inv plus an
    // extra body predicate, so x <= 0 is not preserved (x' = x + 1).
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(declare-fun side (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (y Int))
  (=> (and (inv x) (side y))
      (inv (+ x 1)))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();

    // Blocking x > 0 corresponds to lemma x <= 0.
    // Hyperedge transition x' = x + 1 violates it at x = 0.
    let blocking = ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0));
    assert!(
        !solver.is_self_inductive_blocking(&blocking, inv),
        "non-strict check should reject non-inductive hyperedge lemma"
    );
    assert!(
        !solver.is_strictly_self_inductive_blocking(&blocking, inv),
        "strict check must also reject non-inductive hyperedge lemma"
    );
}

#[test]
fn test_strict_self_inductive_checks_hyperedge_self_loop_unsat_case() {
    // Hyperedge self-loop where lemma x >= 0 is preserved by x' = x + 1.
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(declare-fun side (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (y Int))
  (=> (and (inv x) (side y))
      (inv (+ x 1)))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();

    // Blocking x < 0 corresponds to lemma x >= 0, which is inductive here.
    let blocking = ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0));
    assert!(
        solver.is_self_inductive_blocking(&blocking, inv),
        "non-strict check should accept inductive hyperedge lemma"
    );
    assert!(
        solver.is_strictly_self_inductive_blocking(&blocking, inv),
        "strict check should accept inductive hyperedge lemma"
    );
}

#[test]
fn test_is_entry_inductive_uses_clause_guarded_lemmas_issue_2459() {
    // Entry clause p -> q with concrete predecessor p(1).
    // Invariant q <= 0 is not entry-inductive by itself (counterexample y=1),
    // but becomes inductive when the active entry clause has a matching
    // clause-guarded propagated lemma.
    let smt2 = r#"
(set-logic HORN)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 1) (p x))))
(assert (forall ((x Int) (y Int)) (=> (and (p x) (= y x)) (q y))))
(check-sat)
"#;

    // Baseline: without clause-guarded lemma, invariant should fail entry-inductiveness.
    let mut solver_without_guard =
        PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    let q0 = solver_without_guard.problem.lookup_predicate("q").unwrap();
    let q0_var = solver_without_guard.canonical_vars(q0).unwrap()[0].clone();
    let invariant0 = ChcExpr::le(ChcExpr::var(q0_var), ChcExpr::Int(0));
    assert!(
        !solver_without_guard.is_entry_inductive(&invariant0, q0, 1),
        "without clause guard, invariant should fail on entry transition from p(1)"
    );

    // With clause-guarded lemma on q's entry clause, the same check should pass.
    let mut solver_with_guard =
        PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    let q1 = solver_with_guard.problem.lookup_predicate("q").unwrap();
    let q1_var = solver_with_guard.canonical_vars(q1).unwrap()[0].clone();
    let invariant1 = ChcExpr::le(ChcExpr::var(q1_var), ChcExpr::Int(0));
    let (entry_clause_index, _) = solver_with_guard
        .problem
        .clauses_defining_with_index(q1)
        .find(|(_, clause)| {
            !clause.body.predicates.is_empty()
                && clause
                    .body
                    .predicates
                    .iter()
                    .any(|(body_pred, _)| *body_pred != q1)
        })
        .expect("expected entry clause for q");
    solver_with_guard
        .caches
        .clause_guarded_lemmas
        .insert((q1, entry_clause_index), vec![(invariant1.clone(), 1)]);

    assert!(
        solver_with_guard.is_entry_inductive(&invariant1, q1, 1),
        "clause-guarded lemma should make entry-inductiveness check pass"
    );
}

// Tests for check_paired_sum_parity (algebraic invariant checking)

#[test]
fn test_check_paired_sum_parity_identity() {
    let pre = ChcVar::new("pre_x", ChcSort::Int);
    let post = ChcVar::new("post_x", ChcSort::Int);
    // Identity: post_x = pre_x
    let constraint = ChcExpr::eq(ChcExpr::var(post), ChcExpr::var(pre));
    // For identity, check_paired_sum_parity with k=2 should preserve parity
    let result = PdrSolver::check_paired_sum_parity(&constraint, "pre_x", "post_x", 2);
    assert!(result, "identity transition should preserve parity");
}

#[test]
fn test_check_paired_sum_parity_no_or_even_offset() {
    // Post-OR-split clauses have no OR constraint but constant offsets.
    // check_paired_sum_parity should handle these via the fallback path.
    let pre = ChcVar::new("pre_x", ChcSort::Int);
    let post = ChcVar::new("post_x", ChcSort::Int);
    // post_x = pre_x + 2 (even offset, no OR pattern)
    let constraint = ChcExpr::eq(
        ChcExpr::var(post),
        ChcExpr::add(ChcExpr::var(pre), ChcExpr::Int(2)),
    );
    // Even offset (2 mod 2 = 0) → parity preserved
    let result = PdrSolver::check_paired_sum_parity(&constraint, "pre_x", "post_x", 2);
    assert!(result, "even offset should preserve parity mod 2");
}

#[test]
fn test_check_paired_sum_parity_no_or_odd_offset() {
    // Odd offset should NOT preserve parity mod 2
    let pre = ChcVar::new("pre_x", ChcSort::Int);
    let post = ChcVar::new("post_x", ChcSort::Int);
    // post_x = pre_x + 3 (odd offset)
    let constraint = ChcExpr::eq(
        ChcExpr::var(post),
        ChcExpr::add(ChcExpr::var(pre), ChcExpr::Int(3)),
    );
    let result = PdrSolver::check_paired_sum_parity(&constraint, "pre_x", "post_x", 2);
    assert!(!result, "odd offset should not preserve parity mod 2");
}

#[test]
fn test_check_paired_sum_parity_s_mutants_22_pattern() {
    // Mirrors s_mutants_22 after OR-split (positive branch):
    // Constraint: D=A+1 ∧ E=B+1 ∧ F=C+D+E
    // pre_var="C", post_var="F", k=2
    // D offset=1, E offset=1, sum=2, 2 mod 2=0 → parity preserved
    let c = ChcExpr::var(ChcVar::new("C", ChcSort::Int));
    let d = ChcExpr::var(ChcVar::new("D", ChcSort::Int));
    let e = ChcExpr::var(ChcVar::new("E", ChcSort::Int));
    let f = ChcExpr::var(ChcVar::new("F", ChcSort::Int));
    let a = ChcExpr::var(ChcVar::new("A", ChcSort::Int));
    let b = ChcExpr::var(ChcVar::new("B", ChcSort::Int));
    // F = (C + D) + E (nested binary adds)
    let c_plus_d = ChcExpr::add(c, d.clone());
    let c_plus_d_plus_e = ChcExpr::add(c_plus_d, e.clone());
    let constraint = ChcExpr::and_all(vec![
        ChcExpr::eq(d, ChcExpr::add(ChcExpr::Int(1), a)),
        ChcExpr::eq(e, ChcExpr::add(ChcExpr::Int(1), b)),
        ChcExpr::eq(f, c_plus_d_plus_e),
    ]);
    let result = PdrSolver::check_paired_sum_parity(&constraint, "C", "F", 2);
    assert!(result, "s_mutants_22 pattern: D+E offset sum = 2 mod 2 = 0");
}

#[test]
fn test_check_paired_sum_parity_s_mutants_22_negative_branch() {
    // Second OR-split branch: D=A-1, E=B-1, F=C+D+E
    // D offset=-1, E offset=-1, sum=-2, (-2) mod 2=0 → parity preserved
    let c = ChcExpr::var(ChcVar::new("C", ChcSort::Int));
    let d = ChcExpr::var(ChcVar::new("D", ChcSort::Int));
    let e = ChcExpr::var(ChcVar::new("E", ChcSort::Int));
    let f = ChcExpr::var(ChcVar::new("F", ChcSort::Int));
    let a = ChcExpr::var(ChcVar::new("A", ChcSort::Int));
    let b = ChcExpr::var(ChcVar::new("B", ChcSort::Int));
    let c_plus_d = ChcExpr::add(c, d.clone());
    let c_plus_d_plus_e = ChcExpr::add(c_plus_d, e.clone());
    let constraint = ChcExpr::and_all(vec![
        ChcExpr::eq(d, ChcExpr::add(ChcExpr::Int(-1), a)),
        ChcExpr::eq(e, ChcExpr::add(ChcExpr::Int(-1), b)),
        ChcExpr::eq(f, c_plus_d_plus_e),
    ]);
    let result = PdrSolver::check_paired_sum_parity(&constraint, "C", "F", 2);
    assert!(
        result,
        "s_mutants_22 negative branch: D+E offset sum = -2 mod 2 = 0"
    );
}

// Tests for try_weaken_equality_to_inequality (BUG FIX #2100)

#[test]
fn test_weaken_equality_to_inequality_simple() {
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    // A = B
    let eq = ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::var(b.clone()));

    let result = PdrSolver::try_weaken_equality_to_inequality(&eq);
    assert!(result.is_some());
    let weakened = result.unwrap();
    assert_eq!(weakened.len(), 2);

    // Should produce A >= B and A <= B
    let expected_ge = ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(b.clone()));
    let expected_le = ChcExpr::le(ChcExpr::var(a), ChcExpr::var(b));
    assert_eq!(weakened[0], expected_ge);
    assert_eq!(weakened[1], expected_le);
}

#[test]
fn test_weaken_equality_to_inequality_with_subtraction() {
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);
    // (A - B - C) = 0 which is represented as (= (- (- A B) C) 0)
    let diff = ChcExpr::sub(
        ChcExpr::sub(ChcExpr::var(a), ChcExpr::var(b)),
        ChcExpr::var(c),
    );
    let eq = ChcExpr::eq(diff.clone(), ChcExpr::Int(0));

    let result = PdrSolver::try_weaken_equality_to_inequality(&eq);
    assert!(result.is_some());
    let weakened = result.unwrap();
    assert_eq!(weakened.len(), 2);

    // Should produce (A - B - C) >= 0 and (A - B - C) <= 0
    let expected_ge = ChcExpr::ge(diff.clone(), ChcExpr::Int(0));
    let expected_le = ChcExpr::le(diff, ChcExpr::Int(0));
    assert_eq!(weakened[0], expected_ge);
    assert_eq!(weakened[1], expected_le);
}

#[test]
fn test_weaken_equality_to_inequality_non_equality() {
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    // A >= B (not an equality)
    let ge = ChcExpr::ge(ChcExpr::var(a), ChcExpr::var(b));

    let result = PdrSolver::try_weaken_equality_to_inequality(&ge);
    assert!(result.is_none());
}

#[test]
fn test_weaken_equality_to_inequality_bool_equality() {
    // Bool equality should not be weakened
    let bool_eq = ChcExpr::eq(ChcExpr::Bool(true), ChcExpr::Bool(false));

    let result = PdrSolver::try_weaken_equality_to_inequality(&bool_eq);
    assert!(result.is_none());
}

/// Regression test for #3831 / #5653: `can_push_lemma` must reject non-inductive
/// discovered parity invariants in both debug and release modes.
///
/// #5653 Phase 1A removed the spot-check sampling entirely: all discovered
/// invariants now get full SMT inductiveness checks during push.
#[test]
fn test_can_push_lemma_rejects_non_inductive_discovered_parity_invariant() {
    // Transition: x' = x + 1. Parity (x mod 4 = 2) is NOT preserved.
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 10) (inv x))))
(assert (forall ((x Int) (x_next Int))
  (=> (and (inv x) (= x_next (+ x 1))) (inv x_next))))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();

    // (= (mod x 4) 2) — a discovered parity invariant
    let parity = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::Int(4)),
        ChcExpr::Int(2),
    );

    // Ensure the formula is classified as a discovered invariant
    assert!(
        PdrSolver::is_discovered_invariant(&parity),
        "parity formula must be recognized as discovered invariant"
    );

    // Create a level-1 lemma
    let lemma = Lemma::new(inv, parity, 1);

    // can_push_lemma must return false: the parity invariant is not inductive
    // because x' = x + 1 does not preserve x mod 4 = 2.
    // All discovered invariants get full SMT checks (#5653 Phase 1A).
    let result = solver.can_push_lemma(&lemma, 1);
    assert!(
        !result,
        "can_push_lemma must reject non-inductive parity invariant (debug and release)"
    );
}

/// #8578: is_strictly_self_inductive_blocking must return false for predicates
/// with no self-loop transition clauses. Without this, the inductiveness check
/// is vacuously true and any arbitrary lemma passes, enabling false Safe results
/// on acyclic multi-predicate problems.
#[test]
fn test_strictly_self_inductive_returns_false_for_no_self_loop_predicate_8578() {
    // Two predicates: P -> Q (no self-loops on either).
    // Q is defined by P, not by itself. Any lemma on Q should NOT be
    // considered strictly self-inductive.
    let smt2 = r#"
(set-logic HORN)
(declare-fun P ((_ BitVec 8)) Bool)
(declare-fun Q ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> true (P x))))
(assert (forall ((x (_ BitVec 8))) (=> (P x) (Q x))))
(assert (forall ((x (_ BitVec 8))) (=> (and (Q x) (not (= x #x00))) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let q = solver.problem.lookup_predicate("Q").unwrap();
    let x = solver.canonical_vars(q).unwrap()[0].clone();

    // A wrong lemma: x = 0. This would be vacuously "strictly self-inductive"
    // under the old code because Q has no self-loop clause.
    let wrong_blocking = ChcExpr::not(ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(0, 8)));
    assert!(
        !solver.is_strictly_self_inductive_blocking(&wrong_blocking, q),
        "#8578: is_strictly_self_inductive_blocking must return false for predicates \
         with no self-loop clauses (vacuous truth is not sufficient)"
    );
}

/// P0 (model-checker-consumer wishlist 2026-07-17 item 2): on native-BV problems the strict
/// self-inductiveness check requires DUAL confirmation — the internal UNSAT
/// must be independently re-proven by the ay-dpll executor before a lemma
/// counts as strict (strict UNSATs are what grant the #5877
/// `individually_inductive` whole-model verification skip). A genuinely
/// inductive BV lemma must still pass: no over-degradation.
#[test]
fn test_strict_self_inductive_bv_dual_confirmation_accepts_genuine() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x01) (inv x))))
(assert (forall ((x (_ BitVec 8))) (=> (inv x) (inv (bvor x #x01)))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (= x #x00)) false)))
(check-sat)
"#;
    let mut solver = solver_from_str(smt2);
    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();

    // Blocking x = 0 corresponds to lemma x != 0, preserved by
    // x' = bvor x #x01 (low bit always set). Both the internal solver and
    // the executor cross-check must prove the consecution query UNSAT.
    let blocking = ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(0, 8));
    assert!(
        solver.is_strictly_self_inductive_blocking(&blocking, inv),
        "genuinely inductive BV lemma must remain strict under dual confirmation"
    );
}

/// P0 (wishlist item 2 / item 4 archetype): a BV counter lemma that is
/// "monotone" under a wrap-blind Int reading but NOT inductive in BV
/// semantics (bvadd wraps 0xFF -> 0x00) must be rejected by the strict
/// check — this is the byte-offset-overflow shape from model-checker-consumer task #25.
#[test]
fn test_strict_self_inductive_bv_wrap_not_inductive() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x01) (inv x))))
(assert (forall ((x (_ BitVec 8))) (=> (inv x) (inv (bvadd x #x01)))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (= x #x00)) false)))
(check-sat)
"#;
    let mut solver = solver_from_str(smt2);
    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();

    // Blocking x = 0 corresponds to lemma x != 0. Under unsigned-Int
    // abstraction the counter "only increases" from 1, so the lemma looks
    // inductive — but in BV semantics x = 0xFF steps to 0x00. Strict
    // self-inductiveness must fail.
    let blocking = ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(0, 8));
    assert!(
        !solver.is_strictly_self_inductive_blocking(&blocking, inv),
        "wrapping bvadd breaks lemma x != 0; strict check must reject (task #25 shape)"
    );
    assert!(
        !solver.is_self_inductive_blocking(&blocking, inv),
        "non-strict check must also reject the wrapping counter lemma"
    );
}

/// P0 (wishlist item 2.3): the forward-sample acceptance taint. A lemma
/// whose self-inductiveness was accepted via forward simulation samples is
/// heuristic evidence only; `lemma_sample_tainted` is the flag the
/// `individually_inductive` grants consult to keep such lemmas away from
/// whole-model verification skips.
#[test]
fn test_sample_accepted_taint_mechanism() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;
    let solver = {
        let mut s = solver_from_str(smt2);
        let inv = s.problem.lookup_predicate("inv").unwrap();
        let x = s.canonical_vars(inv).unwrap()[0].clone();
        let blocking = ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::Int(0));
        let other_blocking = ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(10));

        assert!(
            !s.lemma_sample_tainted(inv, &blocking),
            "no taint before any sample acceptance"
        );

        // Simulate a forward-sample acceptance (the insertion performed by
        // is_self_inductive_blocking_uncached on the nonlinear-Unknown path).
        s.caches
            .sample_accepted_taint
            .insert((inv, blocking.structural_hash()));

        assert!(
            s.lemma_sample_tainted(inv, &blocking),
            "taint must be visible for the sampled blocking formula"
        );
        assert!(
            !s.lemma_sample_tainted(inv, &other_blocking),
            "taint must be keyed per formula"
        );
        s
    };
    drop(solver);
}
