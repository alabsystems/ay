// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for PDR model building, counterexample construction, and convex closure.

#![allow(clippy::unwrap_used)]

use super::PdrSolver;
use crate::pdr::config::PdrConfig;
use crate::pdr::frame::{Frame, Lemma};
use crate::pdr::model::{InvariantModel, PredicateInterpretation};
use crate::pdr::obligation::ProofObligation;
use crate::smt::SmtValue;
use crate::{
    ChcExpr, ChcOp, ChcParser, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

fn test_config() -> PdrConfig {
    PdrConfig {
        verbose: false,
        use_negated_equality_splits: false,
        ..PdrConfig::default()
    }
}

fn expr_contains(formula: &ChcExpr, needle: &ChcExpr) -> bool {
    if formula == needle {
        return true;
    }
    match formula {
        ChcExpr::Op(_, args) => args.iter().any(|arg| expr_contains(arg, needle)),
        ChcExpr::PredicateApp(_, _, args) => args.iter().any(|arg| expr_contains(arg, needle)),
        _ => false,
    }
}

fn blocking_zero_formula(solver: &PdrSolver, pred_name: &str) -> (crate::PredicateId, ChcExpr) {
    let pred = solver
        .problem
        .get_predicate_by_name(pred_name)
        .expect("predicate should exist")
        .id;
    let canon_x = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")[0]
        .clone();
    let blocking = ChcExpr::not(ChcExpr::eq(ChcExpr::var(canon_x), ChcExpr::int(0)));
    (pred, blocking)
}

fn linear_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));
    problem
}

#[test]
fn verify_model_rejects_missing_head_interpretation_without_panicking() {
    let mut problem = ChcProblem::new();
    let body_pred = problem.declare_predicate("Body", vec![ChcSort::Int]);
    let head_pred = problem.declare_predicate("Head", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(body_pred, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(head_pred, vec![ChcExpr::var(x)]),
    ));

    let mut solver = PdrSolver::new(problem, test_config());
    let body_vars = solver
        .canonical_vars(body_pred)
        .expect("body predicate should have canonical vars")
        .to_vec();
    let mut incomplete = InvariantModel::new();
    incomplete.set(
        body_pred,
        PredicateInterpretation::new(body_vars, ChcExpr::Bool(true)),
    );

    assert!(
        !solver.verify_model(&incomplete),
        "a model missing a clause-head interpretation must fail closed"
    );
    assert!(
        matches!(solver.try_verify_model(&incomplete), Ok(false)),
        "the panic-safe public verifier must report ordinary verification failure"
    );
}

fn non_pure_lia_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x_next.clone()),
                ChcExpr::mod_op(
                    ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(1)),
                    ChcExpr::Int(3),
                ),
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x_next)]),
    ));
    problem
}

fn fact_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));
    problem
}

fn increment_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x1 = ChcVar::new("x1", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x1.clone()),
                ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x1)]),
    ));
    problem
}

fn bitvec_problem(width: u32) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::BitVec(width)]);
    let x = ChcVar::new("x", ChcSort::BitVec(width));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));
    problem
}

fn nested_datatype_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inner_sort = ChcSort::Datatype {
        name: "Inner".to_string(),
        constructors: Arc::new(vec![crate::ChcDtConstructor {
            name: "mkInner".to_string(),
            selectors: vec![crate::ChcDtSelector {
                name: "value".to_string(),
                sort: ChcSort::Int,
            }],
        }]),
    };
    let outer_sort = ChcSort::Datatype {
        name: "Outer".to_string(),
        constructors: Arc::new(vec![crate::ChcDtConstructor {
            name: "mkOuter".to_string(),
            selectors: vec![
                crate::ChcDtSelector {
                    name: "inner".to_string(),
                    sort: inner_sort,
                },
                crate::ChcDtSelector {
                    name: "flag".to_string(),
                    sort: ChcSort::Bool,
                },
            ],
        }]),
    };
    let p = problem.declare_predicate("P", vec![outer_sort.clone()]);
    let x = ChcVar::new("x", outer_sort);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));
    problem
}

fn monotone_bitvec_problem(width: u32) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::BitVec(width)]);
    let x = ChcVar::new("x", ChcSort::BitVec(width));
    let xp = ChcVar::new("xp", ChcSort::BitVec(width));
    let max_value = if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::eq(
                ChcExpr::var(x.clone()),
                ChcExpr::BitVec(1, width),
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::and_all([
                ChcExpr::not(ChcExpr::eq(
                    ChcExpr::var(x.clone()),
                    ChcExpr::BitVec(max_value, width),
                )),
                ChcExpr::eq(
                    ChcExpr::var(xp.clone()),
                    ChcExpr::Op(
                        ChcOp::BvAdd,
                        vec![
                            Arc::new(ChcExpr::var(x)),
                            Arc::new(ChcExpr::BitVec(1, width)),
                        ],
                    ),
                ),
            ])),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(xp)]),
    ));
    problem
}

fn hyperedge_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let a = problem.declare_predicate("A", vec![ChcSort::Int]);
    let b = problem.declare_predicate("B", vec![ChcSort::Int]);
    let c = problem.declare_predicate("C", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (a, vec![ChcExpr::var(x.clone())]),
                (b, vec![ChcExpr::var(y)]),
            ],
            None,
        ),
        ClauseHead::Predicate(c, vec![ChcExpr::var(x)]),
    ));
    problem
}

#[test]
fn record_blocked_state_for_convex_caps_entries_fifo() {
    let mut solver = PdrSolver::new(linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let canon_x = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")[0]
        .clone();

    for value in 0..105_i64 {
        let state = ChcExpr::eq(ChcExpr::var(canon_x.clone()), ChcExpr::int(value));
        solver.record_blocked_state_for_convex(pred, &state);
    }

    let entries = solver
        .caches
        .blocked_states_for_convex
        .get(&pred)
        .expect("blocked-state history should exist");
    assert_eq!(
        entries.len(),
        super::MAX_BLOCKED_STATES_PER_PREDICATE,
        "convex-state cache should be capped"
    );
    assert_eq!(
        entries.front().and_then(|m| m.get(&canon_x.name).copied()),
        Some(5),
        "oldest entries should be evicted first when cap is exceeded"
    );
    assert_eq!(
        entries.back().and_then(|m| m.get(&canon_x.name).copied()),
        Some(104),
        "newest blocked state should be retained"
    );
}

#[test]
fn record_blocked_state_for_convex_caps_predicate_map() {
    let mut problem = ChcProblem::new();
    let predicate_count = super::MAX_BLOCKED_STATE_PREDICATES + 1;
    let mut predicate_names = Vec::with_capacity(predicate_count);
    for idx in 0..predicate_count {
        let pred_name = format!("P{idx}");
        problem.declare_predicate(&pred_name, vec![ChcSort::Int]);
        predicate_names.push(pred_name);
    }

    let mut solver = PdrSolver::new(problem, test_config());
    for (idx, pred_name) in predicate_names.iter().enumerate() {
        let pred = solver
            .problem
            .get_predicate_by_name(pred_name)
            .expect("predicate should exist")
            .id;
        let state = ChcExpr::eq(
            ChcExpr::var(ChcVar::new(format!("x{idx}"), ChcSort::Int)),
            ChcExpr::int(i64::try_from(idx).expect("idx fits in i64")),
        );
        solver.record_blocked_state_for_convex(pred, &state);
    }

    let newest_pred = solver
        .problem
        .get_predicate_by_name(
            predicate_names
                .last()
                .expect("there should be at least one predicate"),
        )
        .expect("newest predicate should exist")
        .id;

    assert_eq!(
        solver.caches.blocked_states_for_convex.len(),
        1,
        "overflow insert should clear old predicate histories before inserting the new one"
    );
    assert!(
        solver
            .caches
            .blocked_states_for_convex
            .contains_key(&newest_pred),
        "newest predicate history should be retained after overflow clear"
    );
}

#[test]
fn can_push_lemma_uses_clause_guarded_constraint_for_linear_clause() {
    let mut solver_without_guard = PdrSolver::new(linear_problem(), test_config());
    let (pred_without_guard, blocking_without_guard) =
        blocking_zero_formula(&solver_without_guard, "P");
    let lemma_without_guard = Lemma::new(pred_without_guard, blocking_without_guard, 0);
    assert!(!solver_without_guard.can_push_lemma(&lemma_without_guard, 0));

    let mut solver_with_guard = PdrSolver::new(linear_problem(), test_config());
    let (pred_with_guard, blocking_with_guard) = blocking_zero_formula(&solver_with_guard, "P");
    let lemma_with_guard = Lemma::new(pred_with_guard, blocking_with_guard.clone(), 0);
    let clause_index = solver_with_guard
        .problem
        .clauses_defining_with_index(pred_with_guard)
        .next()
        .expect("linear clause should exist")
        .0;
    solver_with_guard.caches.clause_guarded_lemmas.insert(
        (pred_with_guard, clause_index),
        vec![(blocking_with_guard, usize::MAX)],
    );
    assert!(solver_with_guard.can_push_lemma(&lemma_with_guard, 0));
}

#[test]
fn can_push_lemma_populates_prop_solver_issue_6358() {
    let mut solver = PdrSolver::new(linear_problem(), test_config());
    let (pred, blocking) = blocking_zero_formula(&solver, "P");
    let lemma = Lemma::new(pred, blocking, 0);

    let _ = solver.can_push_lemma(&lemma, 0);

    // prop_solver is only populated when incremental_pdr_enabled() is true.
    // For LIA problems, incremental PDR is disabled (#6583/#8205).
    if solver.incremental_pdr_enabled() {
        assert!(
            solver.prop_solvers.contains_key(&pred),
            "can_push_lemma should route through the per-predicate prop_solver"
        );
    }
}

#[test]
fn can_push_lemma_skips_prop_solver_for_non_pure_lia_issue_6358() {
    let mut solver = PdrSolver::new(non_pure_lia_problem(), test_config());
    // #7048: mod/div with constant divisors is promoted to pure-LIA.
    assert!(
        solver.problem_is_pure_lia,
        "mod over integers is promoted to pure-LIA (#7048)"
    );
    let (pred, blocking) = blocking_zero_formula(&solver, "P");
    let lemma = Lemma::new(pred, blocking, 0);

    let _ = solver.can_push_lemma(&lemma, 0);

    // For LIA problems, incremental PDR is disabled (#6583/#8205), so
    // prop_solvers are never populated.
    assert!(
        !solver.prop_solvers.contains_key(&pred),
        "prop_solver not populated for LIA problem (incremental PDR disabled)"
    );
}

#[test]
fn can_push_lemma_uses_clause_guarded_constraint_for_fact_clause() {
    let mut solver_without_guard = PdrSolver::new(fact_problem(), test_config());
    let (pred_without_guard, blocking_without_guard) =
        blocking_zero_formula(&solver_without_guard, "P");
    let lemma_without_guard = Lemma::new(pred_without_guard, blocking_without_guard, 0);
    assert!(!solver_without_guard.can_push_lemma(&lemma_without_guard, 0));

    let mut solver_with_guard = PdrSolver::new(fact_problem(), test_config());
    let (pred_with_guard, blocking_with_guard) = blocking_zero_formula(&solver_with_guard, "P");
    let lemma_with_guard = Lemma::new(pred_with_guard, blocking_with_guard.clone(), 0);
    let clause_index = solver_with_guard
        .problem
        .clauses_defining_with_index(pred_with_guard)
        .next()
        .expect("fact clause should exist")
        .0;
    solver_with_guard.caches.clause_guarded_lemmas.insert(
        (pred_with_guard, clause_index),
        vec![(blocking_with_guard, usize::MAX)],
    );
    assert!(solver_with_guard.can_push_lemma(&lemma_with_guard, 0));
}

#[test]
fn can_push_lemma_uses_clause_guarded_constraint_for_hyperedge_clause() {
    let mut solver_without_guard = PdrSolver::new(hyperedge_problem(), test_config());
    let (pred_without_guard, blocking_without_guard) =
        blocking_zero_formula(&solver_without_guard, "C");
    let lemma_without_guard = Lemma::new(pred_without_guard, blocking_without_guard, 0);
    assert!(!solver_without_guard.can_push_lemma(&lemma_without_guard, 0));

    let mut solver_with_guard = PdrSolver::new(hyperedge_problem(), test_config());
    let (pred_with_guard, blocking_with_guard) = blocking_zero_formula(&solver_with_guard, "C");
    let lemma_with_guard = Lemma::new(pred_with_guard, blocking_with_guard.clone(), 0);
    let clause_index = solver_with_guard
        .problem
        .clauses_defining_with_index(pred_with_guard)
        .next()
        .expect("hyperedge clause should exist")
        .0;
    solver_with_guard.caches.clause_guarded_lemmas.insert(
        (pred_with_guard, clause_index),
        vec![(blocking_with_guard, usize::MAX)],
    );
    assert!(solver_with_guard.can_push_lemma(&lemma_with_guard, 0));
}

/// Helper: create a PdrSolver with a clause-guarded lemma at a specific max_level.
/// Ensures enough frames exist for testing at levels up to `max_level + 1`.
fn solver_with_guarded_lemma_at_level(max_level: usize) -> (PdrSolver, Lemma) {
    let mut solver = PdrSolver::new(linear_problem(), test_config());
    // PdrSolver::new creates 2 frames (indices 0, 1).
    // Add more so we can test at levels up to max_level + 1.
    while solver.frames.len() <= max_level + 1 {
        solver.frames.push(Frame::new());
    }
    let (pred, blocking) = blocking_zero_formula(&solver, "P");
    let lemma = Lemma::new(pred, blocking.clone(), 0);
    let clause_index = solver
        .problem
        .clauses_defining_with_index(pred)
        .next()
        .expect("linear clause should exist")
        .0;
    solver
        .caches
        .clause_guarded_lemmas
        .insert((pred, clause_index), vec![(blocking, max_level)]);
    (solver, lemma)
}

#[test]
fn clause_guarded_level_filter_includes_at_equal_level() {
    // max_level=2, check_level=2: lemma included (2 >= 2)
    let (mut solver, lemma) = solver_with_guarded_lemma_at_level(2);
    assert!(solver.can_push_lemma(&lemma, 2));
}

#[test]
fn clause_guarded_level_filter_includes_below_max() {
    // max_level=2, check_level=1: lemma included (2 >= 1)
    let (mut solver, lemma) = solver_with_guarded_lemma_at_level(2);
    assert!(solver.can_push_lemma(&lemma, 1));
}

#[test]
fn clause_guarded_level_filter_excludes_above_max() {
    // max_level=2, check_level=3: lemma excluded (2 < 3), falls back to unguarded behavior
    let (mut solver, lemma) = solver_with_guarded_lemma_at_level(2);
    assert!(!solver.can_push_lemma(&lemma, 3));
}

#[test]
fn clause_guarded_level_filter_excludes_zero_max_at_level_one() {
    // max_level=0, check_level=1: lemma excluded (0 < 1)
    let (mut solver, lemma) = solver_with_guarded_lemma_at_level(0);
    assert!(!solver.can_push_lemma(&lemma, 1));
}

#[test]
fn clause_guarded_level_filter_includes_zero_max_at_level_zero() {
    // max_level=0, check_level=0: lemma included (0 >= 0)
    let (mut solver, lemma) = solver_with_guarded_lemma_at_level(0);
    assert!(solver.can_push_lemma(&lemma, 0));
}

#[test]
fn can_push_lemma_rejects_non_inductive_discovered_parity_invariant() {
    // Regression test for #3831 / #5653: discovered parity invariants must be
    // rejected by can_push_lemma. #5653 Phase 1A removed the spot-check
    // sampling entirely so all lemmas get full SMT checks.
    //
    // increment_problem: P(x) -> P(x+1)
    // Parity invariant: (mod x 2) = 0  ("x is always even")
    // This is NOT inductive: if x is even, x+1 is odd.
    let mut solver = PdrSolver::new(increment_problem(), test_config());
    // Ensure enough frames for level 1 push check
    while solver.frames.len() <= 2 {
        solver.frames.push(Frame::new());
    }
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let x = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")[0]
        .clone();
    // (mod x 2) = 0 — passes is_discovered_invariant (parity pattern)
    let parity_formula = ChcExpr::eq(
        ChcExpr::Op(
            ChcOp::Mod,
            vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(2))],
        ),
        ChcExpr::int(0),
    );
    let lemma = Lemma::new(pred, parity_formula, 1);
    assert!(
        PdrSolver::is_discovered_invariant(&lemma.formula),
        "parity formula should be recognized as a discovered invariant"
    );
    // All discovered invariants get full SMT checks (#5653 Phase 1A).
    // This must reject: (mod x 2) = 0 is not inductive for P(x) → P(x+1).
    assert!(
        !solver.can_push_lemma(&lemma, 1),
        "non-inductive parity invariant must be rejected in both debug and release modes"
    );
}

#[test]
fn build_model_from_entry_inductive_lemmas_prunes_model_entry_invalid_lemma() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun p (Int) Bool)
(declare-fun q (Int Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int) (b Int))
  (=> (and (p x) (= b 0)) (q x b))))
(assert (forall ((x Int) (b Int) (b2 Int))
  (=> (and (q x b) (< b 16) (= b2 (+ b 2))) (q x b2))))
(check-sat)
"#;

    let mut solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), test_config());
    let p = solver.problem.lookup_predicate("p").unwrap();
    let q = solver.problem.lookup_predicate("q").unwrap();

    let p_x = solver.canonical_vars(p).unwrap()[0].clone();
    let q_x = solver.canonical_vars(q).unwrap()[0].clone();
    let q_b = solver.canonical_vars(q).unwrap()[1].clone();

    let p_ge_0 = ChcExpr::ge(ChcExpr::var(p_x.clone()), ChcExpr::int(0));
    let p_le_255 = ChcExpr::le(ChcExpr::var(p_x), ChcExpr::int(255));
    let q_ge_0 = ChcExpr::ge(ChcExpr::var(q_x.clone()), ChcExpr::int(0));
    let q_le_255 = ChcExpr::le(ChcExpr::var(q_x.clone()), ChcExpr::int(255));
    let q_even = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(q_b.clone()), ChcExpr::int(2)),
        ChcExpr::int(0),
    );
    let q_lt_16 = ChcExpr::lt(ChcExpr::var(q_b.clone()), ChcExpr::int(16));
    let q_le_16 = ChcExpr::le(ChcExpr::var(q_b.clone()), ChcExpr::int(16));
    let q_bad = ChcExpr::lt(
        ChcExpr::var(q_x),
        ChcExpr::add(ChcExpr::var(q_b), ChcExpr::int(2)),
    );

    solver.frames[1].add_lemma(Lemma::new(p, p_ge_0, 1));
    solver.frames[1].add_lemma(Lemma::new(p, p_le_255, 1));
    solver.frames[1].add_lemma(Lemma::new(q, q_ge_0, 1));
    solver.frames[1].add_lemma(Lemma::new(q, q_le_255, 1));
    solver.frames[1].add_lemma(Lemma::new(q, q_even.clone(), 1));
    solver.frames[1].add_lemma(Lemma::new(q, q_lt_16.clone(), 1));
    solver.frames[1].add_lemma(Lemma::new(q, q_le_16, 1));
    solver.frames[1].add_lemma(Lemma::new(q, q_bad.clone(), 1));

    assert!(
        solver.is_entry_inductive(&q_bad, q, 1),
        "fact-only entry check should accept the startup-local lemma before model pruning"
    );

    let model = solver.build_model_from_entry_inductive_lemmas(1);
    let q_formula = &model.get(&q).expect("q interpretation missing").formula;

    assert!(
        !expr_contains(q_formula, &q_bad),
        "model pruning should remove entry-invalid lemma from q, got {q_formula}"
    );
    assert!(
        !expr_contains(q_formula, &q_lt_16),
        "model pruning should remove strict self-loop bound from q, got {q_formula}"
    );
    assert!(
        expr_contains(q_formula, &q_even),
        "pruning should retain genuinely inductive q lemmas, got {q_formula}"
    );
    assert!(
        solver.verify_model(&model),
        "filtered entry-inductive model should satisfy the CHC clauses"
    );
}

#[test]
fn build_model_from_entry_inductive_lemmas_keeps_single_predicate_bv_query_blocker_issue_7964() {
    // `simple.c_000` reduces to this shape for the diagnostic boundary:
    // a single BV predicate, a direct exact-negated-query blocker, and a
    // small entry-inductive model that must keep that blocker intact.
    let smt2 = r#"
(set-logic HORN)
(declare-fun p ((_ BitVec 8)) Bool)

(assert
  (forall ((x (_ BitVec 8)))
    (=>
      (= x #x00)
      (p x))))

(assert
  (forall ((x (_ BitVec 8)))
    (=>
      (and (p x))
      (p x))))

(assert
  (forall ((x (_ BitVec 8)))
    (=>
      (and (p x) (= x #x01))
      false)))

(check-sat)
"#;

    let mut solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), test_config());
    let pred = solver.problem.lookup_predicate("p").unwrap();
    let x = solver.canonical_vars(pred).unwrap()[0].clone();
    let blocker = ChcExpr::not(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(1, 8)));
    let keep = ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(0, 8));

    solver.frames[1]
        .add_lemma(Lemma::new(pred, blocker.clone(), 1).with_algebraically_verified(true));
    solver.frames[1].add_lemma(Lemma::new(pred, keep.clone(), 1).with_algebraically_verified(true));

    let model = solver.build_model_from_entry_inductive_lemmas(1);
    let p_formula = &model
        .get(&pred)
        .expect("predicate interpretation missing")
        .formula;

    assert!(
        expr_contains(p_formula, &blocker),
        "entry-inductive BV model should keep the exact negated-query blocker, got {p_formula}"
    );
    assert!(
        expr_contains(p_formula, &keep),
        "entry-inductive BV model should keep the supporting init fact, got {p_formula}"
    );
    assert!(
        solver.verify_model(&model),
        "entry-inductive BV model should still verify after pruning"
    );
}

#[test]
fn build_model_from_inductive_lemmas_keeps_algebraically_verified_lemma() {
    let mut solver_plain = PdrSolver::new(increment_problem(), test_config());
    let pred_plain = solver_plain
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let x_plain = solver_plain
        .canonical_vars(pred_plain)
        .expect("predicate should have canonical vars")[0]
        .clone();
    let non_inductive_inv_plain = ChcExpr::eq(ChcExpr::var(x_plain), ChcExpr::int(0));
    solver_plain.frames[1].add_lemma(Lemma::new(pred_plain, non_inductive_inv_plain, 1));
    let plain_model = solver_plain.build_model_from_inductive_lemmas(1);
    assert_eq!(
        plain_model
            .get(&pred_plain)
            .expect("predicate interpretation should exist")
            .formula,
        ChcExpr::Bool(true),
        "non-algebraic non-inductive lemma should be filtered"
    );

    let mut solver_alg = PdrSolver::new(increment_problem(), test_config());
    let pred_alg = solver_alg
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let x_alg = solver_alg
        .canonical_vars(pred_alg)
        .expect("predicate should have canonical vars")[0]
        .clone();
    let non_inductive_inv_alg = ChcExpr::eq(ChcExpr::var(x_alg), ChcExpr::int(0));
    solver_alg.frames[1].add_lemma(
        Lemma::new(pred_alg, non_inductive_inv_alg.clone(), 1).with_algebraically_verified(true),
    );
    let alg_model = solver_alg.build_model_from_inductive_lemmas(1);
    assert_eq!(
        alg_model
            .get(&pred_alg)
            .expect("predicate interpretation should exist")
            .formula,
        non_inductive_inv_alg,
        "algebraically-verified lemmas should bypass strict self-inductive filtering"
    );
}

/// Build a POB chain: root (level 2, query_clause=Some(0)) -> mid (level 1) -> leaf (level 0)
fn build_pob_chain(pred: crate::PredicateId) -> ProofObligation {
    let mut model_0 = FxHashMap::default();
    model_0.insert("x".to_string(), SmtValue::Int(10));
    let mut model_1 = FxHashMap::default();
    model_1.insert("x".to_string(), SmtValue::Int(20));
    let mut model_2 = FxHashMap::default();
    model_2.insert("x".to_string(), SmtValue::Int(30));

    let root = ProofObligation::new(pred, ChcExpr::Bool(true), 2)
        .with_query_clause(0)
        .with_smt_model(model_2);
    let mid = ProofObligation::new(pred, ChcExpr::Bool(true), 1)
        .with_parent(root)
        .with_smt_model(model_1);
    ProofObligation::new(pred, ChcExpr::Bool(true), 0)
        .with_parent(mid)
        .with_smt_model(model_0)
}

#[test]
fn build_cex_query_clause_from_root() {
    let solver = PdrSolver::new(linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let leaf = build_pob_chain(pred);
    let cex = solver.build_cex(&leaf);

    // query_clause should come from the root POB (level 2), not the leaf
    let witness = cex.witness.expect("witness should exist");
    assert_eq!(witness.query_clause, Some(0));
}

#[test]
fn build_cex_steps_in_init_to_bad_order() {
    let solver = PdrSolver::new(linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let leaf = build_pob_chain(pred);
    let cex = solver.build_cex(&leaf);

    // Steps should be in init->bad order: level 2 (root) first, level 0 (leaf) last
    assert_eq!(cex.steps.len(), 3);
    // Root (level 2) was assigned x=30
    assert_eq!(cex.steps[0].assignments.get("x"), Some(&30));
    // Mid (level 1) was assigned x=20
    assert_eq!(cex.steps[1].assignments.get("x"), Some(&20));
    // Leaf (level 0) was assigned x=10
    assert_eq!(cex.steps[2].assignments.get("x"), Some(&10));
}

#[test]
fn build_cex_non_point_states_still_use_smt_model_assignments() {
    let solver = PdrSolver::new(linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;

    let x = ChcVar::new("x", ChcSort::Int);
    let root_state = ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let leaf_state = ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(100));

    let mut root_model = FxHashMap::default();
    root_model.insert("x".to_string(), SmtValue::Int(42));
    let root = ProofObligation::new(pred, root_state, 1).with_smt_model(root_model);

    let mut leaf_model = FxHashMap::default();
    leaf_model.insert("x".to_string(), SmtValue::Int(7));
    let leaf = ProofObligation::new(pred, leaf_state, 0)
        .with_parent(root)
        .with_smt_model(leaf_model);

    let cex = solver.build_cex(&leaf);
    assert_eq!(cex.steps.len(), 2);
    assert_eq!(
        cex.steps[0].assignments.get("x"),
        Some(&42),
        "build_cex must pull concrete values from SMT model for non-point root states"
    );
    assert_eq!(
        cex.steps[1].assignments.get("x"),
        Some(&7),
        "build_cex must pull concrete values from SMT model for non-point leaf states"
    );
}

#[test]
fn extract_point_blocking_preserves_bitvec_state_literals() {
    let solver = PdrSolver::new(bitvec_problem(32), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let x = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")[0]
        .clone();

    let state = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(5, 32));
    let mut model = FxHashMap::default();
    model.insert(x.name.clone(), SmtValue::BitVec(5, 32));
    let pob = ProofObligation::new(pred, state, 1).with_smt_model(model);

    assert_eq!(
        solver.extract_point_blocking(&pob),
        Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(5, 32))),
        "BV point-blocking should preserve the BitVec literal from the state instead of shadowing it as Int"
    );
}

#[test]
fn extract_point_blocking_preserves_nested_datatype_field_sorts() {
    let solver = PdrSolver::new(nested_datatype_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let x = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")[0]
        .clone();

    let state = ChcExpr::eq(
        ChcExpr::var(x.clone()),
        ChcExpr::FuncApp(
            "mkOuter".to_string(),
            x.sort.clone(),
            vec![
                Arc::new(ChcExpr::FuncApp(
                    "mkInner".to_string(),
                    match &x.sort {
                        ChcSort::Datatype { constructors, .. } => {
                            constructors[0].selectors[0].sort.clone()
                        }
                        other => panic!("expected datatype sort, got {other:?}"),
                    },
                    vec![Arc::new(ChcExpr::Int(42))],
                )),
                Arc::new(ChcExpr::Bool(true)),
            ],
        ),
    );
    let mut model = FxHashMap::default();
    model.insert(
        x.name,
        SmtValue::Datatype(
            "mkOuter".to_string(),
            vec![
                SmtValue::Datatype("mkInner".to_string(), vec![SmtValue::Int(42)]),
                SmtValue::Bool(true),
            ],
        ),
    );
    let pob = ProofObligation::new(pred, state.clone(), 1).with_smt_model(model);

    assert_eq!(
        solver.extract_point_blocking(&pob),
        Some(state),
        "point-blocking should preserve nested datatype sorts instead of degrading them to uninterpreted constructors"
    );
}

#[test]
fn supports_i64_numeric_sort_rejects_wide_bitvecs() {
    assert!(PdrSolver::supports_i64_numeric_sort(&ChcSort::Int));
    assert!(PdrSolver::supports_i64_numeric_sort(&ChcSort::BitVec(32)));
    assert!(
        !PdrSolver::supports_i64_numeric_sort(&ChcSort::BitVec(64)),
        "BV64 must stay off the i64-based convex-closure path"
    );
}

#[test]
fn try_convex_closure_generalization_learns_bv_lower_bound() {
    let mut solver = PdrSolver::new(monotone_bitvec_problem(8), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let x = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")[0]
        .clone();

    let entries = solver
        .caches
        .blocked_states_for_convex
        .entry(pred)
        .or_default();
    // 6 data points: MIN_DATA_POINTS=3, RUN_INTERVAL=3 → fires at len%3==0.
    for value in [1_i64, 2, 3, 4, 5, 6] {
        let mut m = FxHashMap::default();
        m.insert(x.name.clone(), value);
        entries.push_back(m);
    }

    let lower_bound = ChcExpr::bv_ule(ChcExpr::BitVec(1, 8), ChcExpr::var(x.clone()));
    let non_inductive_upper_bound = ChcExpr::bv_ule(ChcExpr::var(x), ChcExpr::BitVec(6, 8));

    let learned = solver.try_convex_closure_generalization(pred, 0);
    assert!(
        learned.iter().any(|lemma| lemma.formula == lower_bound),
        "expected convex closure to learn BV lower bound, got {learned:?}"
    );
    assert!(
        !learned
            .iter()
            .any(|lemma| lemma.formula == non_inductive_upper_bound),
        "convex closure should skip non-inductive BV upper bounds: {learned:?}"
    );
}

#[test]
fn build_cex_witness_entries_match_chain_order() {
    let solver = PdrSolver::new(linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let leaf = build_pob_chain(pred);
    let cex = solver.build_cex(&leaf);

    let witness = cex.witness.expect("witness should exist");
    assert_eq!(witness.entries.len(), 3);
    // Entries should be in init->bad order matching steps
    assert_eq!(witness.entries[0].level, 2); // root
    assert_eq!(witness.entries[1].level, 1); // mid
    assert_eq!(witness.entries[2].level, 0); // leaf
                                             // Root entry is at index 0
    assert_eq!(witness.root, 0);
}

#[test]
fn simplify_model_removes_redundant_conjuncts() {
    // Model with x >= 0, x >= 5, x >= 10 — first two are subsumed by x >= 10
    let problem = fact_problem();
    let mut solver = PdrSolver::new(problem, test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let vars = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")
        .to_vec();
    let x = &vars[0];

    // Build model: AND(x >= 0, x >= 5, x >= 10)
    let formula = ChcExpr::and_all(vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)),
    ]);

    use crate::pdr::model::{InvariantModel, PredicateInterpretation};
    let mut model = InvariantModel::new();
    model.set(pred, PredicateInterpretation::new(vars, formula));

    let result = solver.simplify_model(&mut model);
    assert!(
        result.redundancy_removed,
        "simplify_model must report redundancy_removed when conjuncts are removed (#5922)"
    );
    assert!(
        result.modified(),
        "simplify_model must report modified when conjuncts are removed (#5922)"
    );

    // After simplification, only x >= 10 should remain
    let simplified = &model.get(&pred).expect("predicate should exist").formula;
    let conjuncts = simplified.conjuncts();
    assert_eq!(
        conjuncts.len(),
        1,
        "expected 1 conjunct after simplification, got {}: {:?}",
        conjuncts.len(),
        conjuncts
    );
    // The surviving conjunct should be the tightest bound (>= var 10)
    let s = conjuncts[0].to_string();
    assert!(
        s.contains("10"),
        "surviving conjunct should contain the tightest bound 10, got: {s}"
    );
}

#[test]
fn simplify_model_preserves_independent_conjuncts() {
    // Model with x >= 0, y >= 0 — neither subsumes the other.
    // Use a 2-parameter predicate so both variables are declared params
    // (sanitize_free_variables strips conjuncts referencing undeclared vars, #5246).
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x), ChcExpr::var(y)]),
    ));
    let mut solver = PdrSolver::new(problem, test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let vars = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")
        .to_vec();

    // Build model: AND(vars[0] >= 0, vars[1] >= 0)
    let formula = ChcExpr::and_all(vec![
        ChcExpr::ge(ChcExpr::var(vars[0].clone()), ChcExpr::int(0)),
        ChcExpr::ge(ChcExpr::var(vars[1].clone()), ChcExpr::int(0)),
    ]);

    use crate::pdr::model::{InvariantModel, PredicateInterpretation};
    let mut model = InvariantModel::new();
    model.set(pred, PredicateInterpretation::new(vars, formula));

    let result = solver.simplify_model(&mut model);
    assert!(
        !result.modified(),
        "simplify_model must report not modified when no conjuncts are removed"
    );

    // Both conjuncts are independent — both should survive
    let simplified = &model.get(&pred).expect("predicate should exist").formula;
    let conjuncts = simplified.conjuncts();
    assert_eq!(
        conjuncts.len(),
        2,
        "expected 2 conjuncts (independent), got {}: {:?}",
        conjuncts.len(),
        conjuncts
    );
}

#[test]
fn simplify_model_single_conjunct_unchanged() {
    // Model with a single conjunct — nothing to simplify
    let problem = fact_problem();
    let mut solver = PdrSolver::new(problem, test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("predicate should exist")
        .id;
    let vars = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")
        .to_vec();
    let x = &vars[0];

    let formula = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5));

    use crate::pdr::model::{InvariantModel, PredicateInterpretation};
    let mut model = InvariantModel::new();
    model.set(pred, PredicateInterpretation::new(vars, formula.clone()));

    let result = solver.simplify_model(&mut model);
    assert!(
        !result.modified(),
        "simplify_model must report not modified when nothing is removed"
    );

    // Single conjunct should be unchanged
    let simplified = &model.get(&pred).expect("predicate should exist").formula;
    assert_eq!(simplified.to_string(), formula.to_string());
}
