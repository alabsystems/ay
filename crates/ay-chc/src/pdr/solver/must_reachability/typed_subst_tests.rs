// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PDR never builds an ill-typed atom (PDR_typed_subst_2026-09-19.md).
//!
//! kind2 lustre encodings reuse short clause-variable names across clauses
//! with different sorts (`C` is Bool in 12 clauses of metros_1 and Int in one)
//! and their init clauses carry Bool equalities. The symbolic-equality
//! propagation to derived predicates found such a Bool equality, failed the
//! self-inductiveness check, and weakened it into `<=` halves — `(<= b1 b2)`
//! over Bool canonical variables, which both SMT lanes refuse instantly and
//! the entry / self-inductiveness checks re-issued thousands of times per
//! solve. These tests lock the sort-aware weakening, the admission gate, and
//! the end-to-end property on a problem with the same shape.

use super::PdrSolver;
use crate::parser::ChcParser;
use crate::pdr::config::PdrConfig;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PdrResult};
use serial_test::serial;
use std::time::Duration;

// The two tests below read process-wide counters (`ill_typed_candidates_rejected`,
// `ill_typed_engine_queries`) as before/after deltas. They stay process-wide on
// purpose: a PDR solve can spawn worker threads, and a thread-local count would
// miss what those do and pass vacuously. So the tests that read the deltas run
// serially with each other: the admission test adds exactly one rejection, which
// the kind2 test read as its own ("left: 1, right: 0") whenever the two overlapped.

/// Same shape as kind2 `metros_1` / `fast_2_000`: the clause variable `C` is
/// Bool in four clauses and Int in two; the init clause carries a Bool
/// equality (`(= C D)`) and two Int constants (`A = B = 0`); the identity
/// transfer `R -> S` propagates both equalities by position; the `S` self-loop
/// breaks both (`A + 1`, `(not C)`), so every propagated equality fails
/// self-inductiveness and is weakened; the property `A >= B` is safe.
const KIND2_SHAPED: &str = r"
(set-logic HORN)
(declare-fun R (Int Int Bool Bool) Bool)
(declare-fun S (Int Int Bool Bool) Bool)
(declare-fun H (Int) Bool)
(assert (forall ((A Int) (B Int) (C Bool) (D Bool)) (=> (and (= A 0) (= B 0) (= C D) C) (R A B C D))))
(assert (forall ((C Int)) (=> (= C 5) (H C))))
(assert (forall ((A Int) (B Int) (C Bool) (D Bool)) (=> (R A B C D) (S A B C D))))
(assert (forall ((A Int) (B Int) (X Bool) (Y Bool) (C Int)) (=> (and (H C) (R A B X Y) (= C 5)) (S A B X Y))))
(assert (forall ((A Int) (B Int) (C Bool) (D Bool)) (=> (S A B C D) (S (+ A 1) B (not C) D))))
(assert (forall ((A Int) (B Int) (C Bool) (D Bool)) (=> (and (S A B C D) (< A B)) false)))
(check-sat)
";

fn ivar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn bvar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Bool))
}

fn is_ill_typed(e: &ChcExpr) -> bool {
    crate::smt::executor_sort_guard::unsupported_executor_expr_reason(e).is_some()
}

#[test]
fn equality_halves_are_sort_aware() {
    let int_eq = ChcExpr::eq(ivar("x"), ivar("y"));
    let halves = PdrSolver::equality_halves(&int_eq);
    assert_eq!(halves.len(), 2);
    assert!(halves
        .iter()
        .all(|h| matches!(h, ChcExpr::Op(ChcOp::Le, _)) && !is_ill_typed(h)));

    let bool_eq = ChcExpr::eq(bvar("p"), bvar("q"));
    let halves = PdrSolver::equality_halves(&bool_eq);
    assert_eq!(
        halves.len(),
        2,
        "a Bool equality weakens to its two implications"
    );
    assert!(halves
        .iter()
        .all(|h| matches!(h, ChcExpr::Op(ChcOp::Implies, _)) && !is_ill_typed(h)));

    // Mixed or non-scalar sorts: no weakening rather than an ill-typed atom.
    assert_eq!(
        PdrSolver::equality_halves(&ChcExpr::eq(ivar("x"), bvar("p"))),
        [] as [ChcExpr; 0]
    );
    let arr = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let arr_eq = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("a", arr.clone())),
        ChcExpr::var(ChcVar::new("b", arr)),
    );
    assert_eq!(PdrSolver::equality_halves(&arr_eq), [] as [ChcExpr; 0]);
    assert_eq!(PdrSolver::equality_halves(&bvar("p")), [] as [ChcExpr; 0]);
}

#[test]
#[serial(ill_typed_counters)]
fn admission_rejects_an_ill_typed_candidate_before_any_smt_query() {
    let problem = ChcParser::parse(KIND2_SHAPED).unwrap();
    let pred = problem
        .predicates()
        .iter()
        .find(|p| p.name == "S")
        .map(|p| p.id)
        .unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::production(false));
    let canon = solver.canonical_vars(pred).unwrap().to_vec();
    assert_eq!(canon[2].sort, ChcSort::Bool);
    assert_eq!(canon[3].sort, ChcSort::Bool);
    let ill_typed = ChcExpr::le(
        ChcExpr::var(canon[2].clone()),
        ChcExpr::var(canon[3].clone()),
    );
    assert!(is_ill_typed(&ill_typed));
    let rejected_before = crate::pdr::solver::inductiveness::ill_typed_candidates_rejected();
    let queries_before = crate::smt::ill_typed_engine_queries();
    assert!(!solver.add_discovered_invariant(pred, ill_typed, 1));
    assert_eq!(
        crate::pdr::solver::inductiveness::ill_typed_candidates_rejected(),
        rejected_before + 1
    );
    assert_eq!(
        crate::smt::ill_typed_engine_queries(),
        queries_before,
        "the gate must fire before the entry/self-inductiveness SMT checks"
    );
}

#[test]
#[serial(ill_typed_counters)]
fn kind2_shaped_name_reuse_reaches_the_pob_loop_without_ill_typed_queries() {
    let problem = ChcParser::parse(KIND2_SHAPED).unwrap();
    let mut config = PdrConfig::production(false);
    config.solve_timeout = Some(Duration::from_secs(20));
    let queries_before = crate::smt::ill_typed_engine_queries();
    let rejected_before = crate::pdr::solver::inductiveness::ill_typed_candidates_rejected();
    let mut solver = PdrSolver::new(problem, config);
    let outcome = solver.solve_with_stats();
    assert!(
        !matches!(outcome.result, PdrResult::Unsafe(_)),
        "the property A >= B is safe; got {:?}",
        outcome.result
    );
    assert_eq!(
        crate::smt::ill_typed_engine_queries(),
        queries_before,
        "an ill-typed engine-built query reached the SMT bridge"
    );
    assert_eq!(
        crate::pdr::solver::inductiveness::ill_typed_candidates_rejected(),
        rejected_before,
        "a discovery routine still builds ill-typed candidates (the admission gate caught it)"
    );
    assert!(
        outcome.stats.iterations > 0 || matches!(outcome.result, PdrResult::Safe(_)),
        "PDR must reach the POB loop (or prove the property outright); stats={:?}",
        outcome.stats.iterations
    );
}
