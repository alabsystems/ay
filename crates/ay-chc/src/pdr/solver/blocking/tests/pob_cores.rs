// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Workstream B contract C2 (`DESIGN` §3.3, §4.1.1–4.1.2; owner WP-B1-P):
//! `check_predecessor_reachability` records exactly one `ClauseCore` per
//! UNSAT `(clause, fact?)` pair under the lane — the fact clause of the POB's
//! own predicate, every single-body clause (including the
//! `propagate_equalities() == false` shortcut, attributed through C3), and at level 1 every
//! `(clause, fact)` pair — with `core.len() == pob.cube().len()`,
//! `had_exclusion` set exactly when a non-trivial exclusion constraint was in
//! the Q1 query, and nothing recorded with the lane off. The exactness of a
//! core is L's (C3); these locks only require the coverage invariant
//! `!exact ⇒ core is all-true`.

use super::super::*;
use super::unit_test_config;
use crate::pdr::frame::Frame;
use crate::ChcParser;

const TWO_TRANSITIONS: &str = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (P x) (= x1 (+ x 1))) (P x1))))
(assert (forall ((x Int) (x1 Int)) (=> (and (P x) (= x1 (+ x 2))) (P x1))))
(assert (forall ((x Int)) (=> (and (P x) (>= x 10)) false)))
(check-sat)
"#;

const TWO_FACTS: &str = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (= x 100) (P x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (P x) (= x1 (+ x 1))) (P x1))))
(assert (forall ((x Int) (x1 Int)) (=> (and (P x) (= x1 (+ x 2))) (P x1))))
(assert (forall ((x Int)) (=> (and (P x) (>= x 10)) false)))
(check-sat)
"#;

fn solver(smt2: &str, lane: bool, top_level: usize) -> (PdrSolver, PredicateId, ChcExpr) {
    let problem = ChcParser::parse(smt2).unwrap();
    let mut config = unit_test_config();
    if lane {
        // Rung 1: `core_lemma` on, so C3 issues the proxied core solve.
        config.spacer = crate::pdr::config::SpacerLane::rung(1);
    }
    let mut solver = PdrSolver::new(problem, config);
    solver.spacer_core = lane;
    while solver.frames.len() <= top_level {
        solver.frames.push(Frame::new());
    }
    let p = solver.problem.get_predicate_by_name("P").unwrap().id;
    let x = ChcExpr::var(solver.canonical_vars(p).unwrap()[0].clone());
    (solver, p, x)
}

fn all_true(core: &ClauseCore) -> bool {
    core.core.iter().all(|b| *b)
}

fn check_coverage_invariants(cores: &[ClauseCore], n: usize) {
    for c in cores {
        assert_eq!(
            c.core.len(),
            n,
            "core length == cube length (clause {})",
            c.clause_index
        );
        if !c.exact {
            assert!(
                all_true(c),
                "an inexact core is all-true (clause {})",
                c.clause_index
            );
        }
        assert_eq!(c.uses_level, None, "legacy backend never sets uses_level");
    }
}

fn keys(cores: &[ClauseCore]) -> Vec<(usize, Option<usize>)> {
    let mut k: Vec<_> = cores
        .iter()
        .map(|c| (c.clause_index, c.fact_index))
        .collect();
    k.sort_unstable();
    k
}

#[test]
fn every_unsat_clause_gets_one_core_at_level_two() {
    let (mut solver, p, x) = solver(TWO_TRANSITIONS, true, 2);
    // F_1(P) = x ≤ 1 blocks both transitions to x = 5; the fact x = 0 is UNSAT too.
    solver.frames[1].add_lemma(Lemma::new(p, ChcExpr::le(x.clone(), ChcExpr::Int(1)), 1));
    let mut pob = ProofObligation::new(p, ChcExpr::eq(x, ChcExpr::Int(5)), 2);
    let data = match solver.check_predecessor_reachability(&mut pob, &[]) {
        Ok(d) => d,
        Err(
            BlockResult::Blocked(_)
            | BlockResult::AlreadyBlocked
            | BlockResult::Reachable(_)
            | BlockResult::MustReachable(_)
            | BlockResult::Unknown,
        ) => panic!("every clause is UNSAT: expected Ok(ReachabilityData)"),
    };
    assert_eq!(keys(&data.cores), vec![(0, None), (1, None), (2, None)]);
    check_coverage_invariants(&data.cores, 1);
    assert!(
        data.cores.iter().all(|c| !c.had_exclusion),
        "no exclusion was in play"
    );
}

#[test]
fn the_propagate_shortcut_still_records_one_core_per_pair() {
    let (mut solver, p, x) = solver(TWO_TRANSITIONS, true, 2);
    // F_1(P) = (x = 0): with the head pinned to 5, `propagate_equalities`
    // folds `5 = 0 + 1` to false before any verdict solver runs
    // (single_body.rs). The pair is still recorded (C2), attributed through
    // C3 (exact when the proxied solve reproduces the contradiction, all-true
    // inexact otherwise — never dropped).
    solver.frames[1].add_lemma(Lemma::new(p, ChcExpr::eq(x.clone(), ChcExpr::Int(0)), 1));
    let mut pob = ProofObligation::new(p, ChcExpr::eq(x, ChcExpr::Int(5)), 2);
    let q1_before = solver.spacer_stats.q1_calls;
    let data = solver
        .check_predecessor_reachability(&mut pob, &[])
        .unwrap_or_else(|_| panic!("every clause is UNSAT"));
    assert_eq!(keys(&data.cores), vec![(0, None), (1, None), (2, None)]);
    check_coverage_invariants(&data.cores, 1);
    assert!(data.cores.iter().all(|c| !c.had_exclusion));
    // One `record_q1` per UNSAT pair (C3 records its own source).
    assert!(
        solver.spacer_stats.q1_calls >= q1_before + 3,
        "one record per UNSAT pair (got {})",
        solver.spacer_stats.q1_calls - q1_before
    );
}

#[test]
fn had_exclusion_is_set_exactly_when_an_exclusion_literal_participated() {
    let (mut solver, p, x) = solver(TWO_TRANSITIONS, true, 3);
    solver.frames[1].add_lemma(Lemma::new(p, ChcExpr::le(x.clone(), ChcExpr::Int(1)), 1));
    let mut pob = ProofObligation::new(p, ChcExpr::eq(x.clone(), ChcExpr::Int(5)), 2);
    let excluded = ChcExpr::eq(x, ChcExpr::Int(4));

    // An unknown predecessor at ANOTHER parent level adds no exclusion.
    let data = solver
        .check_predecessor_reachability(&mut pob, &[(3, p, excluded.clone())])
        .unwrap_or_else(|_| panic!("every clause is UNSAT"));
    assert_eq!(data.cores.len(), 3);
    assert!(data.cores.iter().all(|c| !c.had_exclusion));

    // At the POB's own level the exclusion enters every single-body Q1 (and
    // never the fact clause's query).
    let data = solver
        .check_predecessor_reachability(&mut pob, &[(2, p, excluded)])
        .unwrap_or_else(|_| panic!("every clause is UNSAT"));
    assert_eq!(keys(&data.cores), vec![(0, None), (1, None), (2, None)]);
    for c in &data.cores {
        assert_eq!(
            c.had_exclusion,
            c.clause_index != 0,
            "had_exclusion ⇔ single-body clause (clause {})",
            c.clause_index
        );
    }
    check_coverage_invariants(&data.cores, 1);
}

#[test]
fn level_one_records_one_core_per_clause_fact_pair() {
    let (mut solver, p, x) = solver(TWO_FACTS, true, 1);
    // x = 5 at level 1: facts 0/1 as clauses of P, and (transition, fact) pairs.
    let mut pob = ProofObligation::new(p, ChcExpr::eq(x, ChcExpr::Int(5)), 1);
    let data = solver
        .check_predecessor_reachability(&mut pob, &[])
        .unwrap_or_else(|_| panic!("every pair is UNSAT"));
    assert_eq!(
        keys(&data.cores),
        vec![
            (0, None),
            (1, None),
            (2, Some(0)),
            (2, Some(1)),
            (3, Some(0)),
            (3, Some(1)),
        ]
    );
    check_coverage_invariants(&data.cores, 1);
    assert!(data.cores.iter().all(|c| !c.had_exclusion));
}

#[test]
fn level_one_exclusion_marks_the_fact_pairs() {
    let (mut solver, p, x) = solver(TWO_FACTS, true, 1);
    let mut pob = ProofObligation::new(p, ChcExpr::eq(x.clone(), ChcExpr::Int(5)), 1);
    let excluded = ChcExpr::eq(x, ChcExpr::Int(4));
    let data = solver
        .check_predecessor_reachability(&mut pob, &[(1, p, excluded)])
        .unwrap_or_else(|_| panic!("every pair is UNSAT"));
    assert_eq!(data.cores.len(), 6);
    for c in &data.cores {
        assert_eq!(
            c.had_exclusion,
            c.fact_index.is_some(),
            "clause {}",
            c.clause_index
        );
    }
}

#[test]
fn multi_literal_cube_cores_index_the_cube() {
    let (mut solver, p, x) = solver(TWO_TRANSITIONS, true, 2);
    solver.frames[1].add_lemma(Lemma::new(p, ChcExpr::le(x.clone(), ChcExpr::Int(1)), 1));
    // Three literals; the cube view is the top-level conjunct order.
    let state = ChcExpr::and_all([
        ChcExpr::ge(x.clone(), ChcExpr::Int(5)),
        ChcExpr::le(x.clone(), ChcExpr::Int(7)),
        ChcExpr::not(ChcExpr::eq(x, ChcExpr::Int(6))),
    ]);
    let mut pob = ProofObligation::new(p, state, 2);
    assert_eq!(pob.cube().len(), 3);
    let data = solver
        .check_predecessor_reachability(&mut pob, &[])
        .unwrap_or_else(|_| panic!("every clause is UNSAT"));
    assert_eq!(data.cores.len(), 3);
    check_coverage_invariants(&data.cores, 3);
}

#[test]
fn a_sat_clause_yields_reachable_with_lits_on_the_lane_only() {
    for lane in [true, false] {
        let (mut solver, p, x) = solver(TWO_TRANSITIONS, lane, 2);
        // F_1(P) = x ≤ 4 leaves x = 4 → x = 5 open.
        solver.frames[1].add_lemma(Lemma::new(p, ChcExpr::le(x.clone(), ChcExpr::Int(4)), 1));
        let mut pob = ProofObligation::new(p, ChcExpr::eq(x, ChcExpr::Int(5)), 2);
        match solver.check_predecessor_reachability(&mut pob, &[]) {
            Err(BlockResult::Reachable(pred)) => {
                assert_eq!(pred.predicate, p);
                assert_eq!(pred.lits.is_some(), lane, "lits Some ⇔ lane on");
                if let Some(lits) = &pred.lits {
                    assert_eq!(
                        lits.lits(),
                        pred.state.collect_conjuncts_nontrivial().as_slice(),
                        "the literal view is the cube's top-level conjuncts"
                    );
                }
            }
            Err(
                BlockResult::Blocked(_)
                | BlockResult::AlreadyBlocked
                | BlockResult::MustReachable(_)
                | BlockResult::Unknown,
            ) => panic!("expected Reachable"),
            Ok(_) => panic!("x = 4 → x = 5 is a predecessor: expected Reachable"),
        }
    }
}

#[test]
fn lane_off_records_no_cores() {
    let (mut solver, p, x) = solver(TWO_TRANSITIONS, false, 2);
    solver.frames[1].add_lemma(Lemma::new(p, ChcExpr::le(x.clone(), ChcExpr::Int(1)), 1));
    let mut pob = ProofObligation::new(p, ChcExpr::eq(x, ChcExpr::Int(5)), 2);
    let data = solver
        .check_predecessor_reachability(&mut pob, &[])
        .unwrap_or_else(|_| panic!("every clause is UNSAT"));
    assert!(data.cores.is_empty(), "legacy path: cores stay empty");
    assert_eq!(
        solver.spacer_stats.q1_calls, 0,
        "no core work with the lane off"
    );
}

#[test]
fn the_lane_reads_the_delta_frame_hypothesis() {
    // A lemma stored ABOVE prev_level is part of F_{prev_level} under the
    // lane (D2) and invisible to the local frame read of the legacy path.
    for lane in [true, false] {
        let (mut solver, p, x) = solver(TWO_TRANSITIONS, lane, 3);
        solver.frames[3].add_lemma(Lemma::new(p, ChcExpr::le(x.clone(), ChcExpr::Int(1)), 3));
        let mut pob = ProofObligation::new(p, ChcExpr::eq(x, ChcExpr::Int(5)), 2);
        let result = solver.check_predecessor_reachability(&mut pob, &[]);
        if lane {
            let data = result.unwrap_or_else(|_| panic!("delta frame blocks every clause"));
            assert_eq!(data.cores.len(), 3);
        } else {
            assert!(
                matches!(result, Err(BlockResult::Reachable(_))),
                "the local frame at level 1 is empty: legacy finds a predecessor"
            );
        }
    }
}
