// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transitions whose `let` chain shares each level twice (the bist_cell
//! shape): BV candidate extraction visits each distinct sub-formula once, and
//! a whole bounded PDR solve over such a transition keeps its 5 s budget.
//!
//! Every tree walk over the shared DAG on the startup-discovery, BV
//! bit-blast and model-verification paths was exponential in the chain's
//! depth: the solves below ran for minutes (or were killed) before the
//! walks were made DAG-linear.

use crate::pdr::config::PdrConfig;
use crate::pdr::solver::test_helpers::solver_from_str;
use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PdrResult};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use std::fmt::Write;
use std::sync::Arc;
use std::time::Duration;

/// `a(0) = (x <= 5 or y <= 3)`, `a(i+1) = (a(i) and x1 <= x) or (a(i) and
/// y1 <= y)`: `2^levels` tree occurrences of `a(0)`'s comparisons. Unsafe:
/// `(0, 0) -> (17, 0)` in one step, and the error is `x > 16`.
fn shared_let_chain_problem(levels: usize) -> String {
    let mut body = String::from("(let ((a0 (or (bvsle x #x05) (bvsle y #x03))))\n");
    for i in 1..=levels {
        let p = i - 1;
        let _ = writeln!(
            body,
            "(let ((a{i} (or (and a{p} (bvsle x1 x)) (and a{p} (bvule y1 y)))))"
        );
    }
    let _ = write!(body, "a{levels}{}", ")".repeat(levels + 1));
    bv_transition_problem(&body, "(bvsgt x #x10)")
}

/// Safe twin: `a(0)` pins `0 <= x1 <= x` and `y1 = y`, and every level is a
/// tautological split on `y1 <=u y`; `x` stays 0, so `x > 16` is unreachable.
fn safe_shared_let_chain_problem(levels: usize) -> String {
    let mut body = String::from("(let ((a0 (and (bvsle x1 x) (bvsge x1 #x00) (= y1 y))))\n");
    for i in 1..=levels {
        let p = i - 1;
        let _ = writeln!(
            body,
            "(let ((a{i} (or (and a{p} (bvule y1 y)) (and a{p} (bvuge y1 y)))))"
        );
    }
    let _ = write!(body, "a{levels}{}", ")".repeat(levels + 1));
    bv_transition_problem(&body, "(bvsgt x #x10)")
}

/// Term-level sharing: `t(0) = x`, `t(i+1) = t(i) + (t(i) xor k(i))`,
/// `x1 = t(levels)`. From `x = 0` the value runs through a fixed cycle that
/// never hits `#x7f` (z3: sat, i.e. Safe).
fn shared_term_chain_problem(levels: usize) -> String {
    let mut body = String::from("(let ((t0 x))\n");
    for i in 1..=levels {
        let p = i - 1;
        let k = (i % 250) + 1;
        let _ = writeln!(body, "(let ((t{i} (bvadd t{p} (bvxor t{p} #x{k:02x}))))");
    }
    let _ = write!(
        body,
        "(and (= x1 t{levels}) (= y1 y)){}",
        ")".repeat(levels + 1)
    );
    bv_transition_problem(&body, "(= x #x7f)")
}

/// Integer twin of [`shared_let_chain_problem`] (Unsafe the same way).
fn int_shared_let_chain_problem(levels: usize) -> String {
    let mut body = String::from("(let ((a0 (or (<= x 5) (<= y 3))))\n");
    for i in 1..=levels {
        let p = i - 1;
        let _ = writeln!(
            body,
            "(let ((a{i} (or (and a{p} (<= x1 x)) (and a{p} (<= y1 y)))))"
        );
    }
    let _ = write!(body, "a{levels}{}", ")".repeat(levels + 1));
    format!(
        "(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (inv x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int)) (=> (and (inv x y) {body}) (inv x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (> x 16)) false)))
(check-sat)
"
    )
}

fn bv_transition_problem(body: &str, bad: &str) -> String {
    format!(
        "(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (and (= x #x00) (= y #x00)) (inv x y))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (x1 (_ BitVec 8)) (y1 (_ BitVec 8)))
  (=> (and (inv x y) {body}) (inv x1 y1))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (and (inv x y) {bad}) false)))
(check-sat)
"
    )
}

/// The bounded PDR configuration of the bist_cell test
/// (`bounded_bv_clause_splitting_config` in `tests/group_bv`).
fn bounded_pdr(input: &str) -> PdrResult {
    let mut config = PdrConfig::default();
    config.max_frames = 3;
    config.max_iterations = 25;
    config.max_obligations = 1_000;
    config.solve_timeout = Some(Duration::from_secs(5));
    crate::testing::pdr_solve_from_str(input, config).expect("the problem parses")
}

#[test]
#[ntest::timeout(60_000)]
fn bv_candidates_of_a_shared_transition_are_collected_once_per_sub_formula() {
    let solver = solver_from_str(&shared_let_chain_problem(48));
    let pred = solver.problem.lookup_predicate("inv").expect("inv");
    let vars = solver
        .canonical_vars(pred)
        .expect("canonical vars")
        .to_vec();

    let candidates = solver.extract_bv_candidate_invariants(pred, &vars);
    let seeds = solver.extract_bv_clause_seeds(pred, &vars);

    // The comparison at the bottom of the chain, over the canonical `x`.
    let bottom = ChcExpr::Op(
        ChcOp::BvSLe,
        vec![
            Arc::new(ChcExpr::var(vars[0].clone())),
            Arc::new(ChcExpr::BitVec(5, 8)),
        ],
    );
    assert!(candidates.contains(&bottom), "{bottom} must be a candidate");
    assert!(seeds
        .iter()
        .any(|seed| seed.comparison_atoms.contains(&bottom)));
}

/// A 5 s bounded solve over a 48-level shared chain returns and never claims
/// Safe. The timeout is 24x the budget: in a whole-lib run the solve shares
/// the process (the global expression interner, the allocator) with about 20
/// test threads, and one such run took the int twin past 30 s. A tree walk
/// over the chain (2^48 tree nodes) still never returns within it.
#[test]
#[ntest::timeout(120_000)]
fn a_bounded_solve_over_a_shared_unsafe_chain_keeps_its_budget() {
    let result = bounded_pdr(&shared_let_chain_problem(48));
    assert!(
        !matches!(result, PdrResult::Safe(_)),
        "Unsafe by construction"
    );
}

/// Safe twin: the same budget, and never Unsafe.
#[test]
#[ntest::timeout(120_000)]
fn a_bounded_solve_over_a_shared_safe_chain_keeps_its_budget() {
    let result = bounded_pdr(&safe_shared_let_chain_problem(48));
    assert!(
        !matches!(result, PdrResult::Unsafe(_)),
        "Safe by construction"
    );
}

/// Term-level sharing (a shared BV arithmetic chain) keeps the budget too.
#[test]
#[ntest::timeout(120_000)]
fn a_bounded_solve_over_a_shared_bv_term_chain_keeps_its_budget() {
    let result = bounded_pdr(&shared_term_chain_problem(48));
    assert!(!matches!(result, PdrResult::Unsafe(_)), "z3: Safe");
}

/// The integer twin goes through the LIA side of discovery.
#[test]
#[ntest::timeout(120_000)]
fn a_bounded_solve_over_a_shared_int_chain_keeps_its_budget() {
    let result = bounded_pdr(&int_shared_let_chain_problem(48));
    assert!(
        !matches!(result, PdrResult::Safe(_)),
        "Unsafe by construction"
    );
}

fn int_var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn node(op: ChcOp, args: Vec<Arc<ChcExpr>>) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::Op(op, args))
}

/// `c(0)` holds one atom of each kind the startup collectors harvest;
/// `c(i+1) = (c(i) and x <= 100+i) or (c(i) and y >= 100+i)` shares it, so the
/// tree has `2^depth` copies of `c(0)`.
fn shared_int_chain(depth: usize) -> ChcExpr {
    let (x, y) = (int_var("x"), int_var("y"));
    let mut c = node(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::eq(x.clone(), ChcExpr::int(3))),
            Arc::new(ChcExpr::le(y.clone(), ChcExpr::int(7))),
            Arc::new(ChcExpr::eq(
                y.clone(),
                ChcExpr::mul(ChcExpr::int(5), x.clone()),
            )),
        ],
    );
    for i in 0..depth {
        let bound = ChcExpr::int(100 + i as i64);
        let left = node(
            ChcOp::And,
            vec![
                Arc::clone(&c),
                Arc::new(ChcExpr::le(x.clone(), bound.clone())),
            ],
        );
        let right = node(
            ChcOp::And,
            vec![Arc::clone(&c), Arc::new(ChcExpr::ge(y.clone(), bound))],
        );
        c = node(ChcOp::Or, vec![left, right]);
    }
    Arc::unwrap_or_clone(c)
}

/// `values` without repeats, in first-occurrence order.
fn first_occurrences(values: &[i128]) -> Vec<i128> {
    let mut seen = FxHashSet::default();
    values.iter().copied().filter(|v| seen.insert(*v)).collect()
}

/// The startup collectors on a `2^60`-copy DAG: each distinct sub-term is
/// visited a bounded number of times (the distinct walk's first 512 pops
/// skip no repeats; the tree walks never returned), and every atom is still
/// found. The callers keep only first occurrences.
#[test]
#[ntest::timeout(60_000)]
fn startup_collectors_visit_each_shared_sub_term_once() {
    let expr = shared_int_chain(60);

    let mut coefficients = Vec::new();
    PdrSolver::collect_mul_coefficients(&expr, &mut coefficients);
    assert_eq!(first_occurrences(&coefficients), vec![5]);
    assert!(coefficients.len() < 600, "{} visits", coefficients.len());

    let mut constants = Vec::new();
    PdrSolver::collect_equality_constants(&expr, &mut constants);
    assert_eq!(first_occurrences(&constants), vec![3]);
    assert!(constants.len() < 600, "{} visits", constants.len());

    let mut literals = Vec::new();
    PdrSolver::collect_int_literals(&expr, &mut literals);
    let literal_set: FxHashSet<i128> = literals.iter().copied().collect();
    let mut expected: FxHashSet<i128> = [3, 5, 7].into_iter().collect();
    expected.extend(100..160);
    assert_eq!(literal_set, expected);
    assert!(literals.len() < 4_000, "{} literals", literals.len());

    let mut thresholds = FxHashSet::default();
    PdrSolver::extract_thresholds_from_expr(&expr, &mut thresholds);
    for k in [6, 7, 8, 99, 100, 159, 160] {
        assert!(thresholds.contains(&k), "threshold {k}");
    }
}

/// The scale-factor list is consumed in first-occurrence order. A small
/// expression gets exactly the tree walk's list (repeat included); behind a
/// large shared DAG the repeat of the shared `(* 2 a)` is skipped and the
/// first occurrences keep their order.
#[test]
#[ntest::timeout(60_000)]
fn the_coefficient_walk_keeps_the_tree_walks_order() {
    let twice_a = Arc::new(ChcExpr::mul(ChcExpr::int(2), int_var("a")));
    let times = |k: i64, v: &str| Arc::new(ChcExpr::mul(ChcExpr::int(k), int_var(v)));
    let eq = |v: &str, rhs: Arc<ChcExpr>| node(ChcOp::Eq, vec![Arc::new(int_var(v)), rhs]);
    let tail = vec![
        eq("z", Arc::clone(&twice_a)),
        node(
            ChcOp::Or,
            vec![eq("w", times(3, "b")), eq("v", Arc::clone(&twice_a))],
        ),
        eq("u", times(4, "c")),
    ];

    let mut small = Vec::new();
    PdrSolver::collect_mul_coefficients(&ChcExpr::Op(ChcOp::And, tail.clone()), &mut small);
    assert_eq!(small, vec![2, 3, 2, 4]);

    let mut behind_dag = vec![Arc::new(shared_int_chain(60))];
    behind_dag.extend(tail);
    let mut large = Vec::new();
    PdrSolver::collect_mul_coefficients(&ChcExpr::Op(ChcOp::And, behind_dag), &mut large);
    assert_eq!(first_occurrences(&large), vec![5, 2, 3, 4]);
    assert_eq!(large.iter().filter(|&&k| k == 2).count(), 1);
}
