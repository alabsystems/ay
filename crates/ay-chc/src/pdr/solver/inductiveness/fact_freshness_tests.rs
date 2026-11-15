// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::model::{InvariantModel, PredicateInterpretation};
use crate::pdr::solver::{EntryInductiveFailureReason, PdrSolver};
use crate::pdr::{PdrConfig, PdrResult};
use crate::{ChcExpr, ChcParser, ChcSort, ChcVar, ClauseHead, PredicateId};

#[path = "fact_freshness_tests/final_model.rs"]
mod final_model;

const TWO_FACTS: &str = r#"
(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(declare-fun C (Int Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (A x))))
(assert (forall ((x Int)) (=> (= x 1) (B x))))
(assert (forall ((a Int) (b Int)) (=> (and (A a) (B b)) (C a b))))
(check-sat)
"#;

fn solver(source: &str) -> PdrSolver {
    let problem = ChcParser::parse(source).unwrap();
    let clauses = format!("{:?}", problem.clauses());
    let solver = PdrSolver::new(
        problem,
        PdrConfig {
            preserve_original_clauses: true,
            use_must_summaries: false,
            use_mixed_summaries: false,
            ..PdrConfig::default()
        },
    );
    assert_eq!(format!("{:?}", solver.problem.clauses()), clauses);
    for predicate in solver.problem.predicates() {
        assert!(solver
            .reachability
            .must_summaries
            .get(0, predicate.id)
            .is_none());
    }
    solver
}

fn pair(solver: &PdrSolver) -> (PredicateId, ChcExpr) {
    let pred = solver.problem.lookup_predicate("C").unwrap();
    let vars = solver.canonical_vars(pred).unwrap();
    assert_eq!(vars.len(), 2);
    (
        pred,
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::Int(0)),
            ChcExpr::eq(ChcExpr::var(vars[1].clone()), ChcExpr::Int(1)),
        ),
    )
}

fn assert_sat_hyperedge(solver: &mut PdrSolver, pred: PredicateId, invalid: &ChcExpr) {
    assert!(!solver.is_entry_inductive(invalid, pred, 1));
    assert_eq!(
        solver
            .telemetry
            .entry_inductive_failure_counts
            .get(&EntryInductiveFailureReason::SatHyperedge),
        Some(&1)
    );
}

#[test]
fn entry_two_fact_locals_are_independent_and_valid_invariant_survives() {
    let mut solver = solver(TWO_FACTS);
    for fact in &solver.problem.clauses()[..2] {
        let ClauseHead::Predicate(_, args) = &fact.head else {
            panic!("fact head")
        };
        assert_eq!(args, &[ChcExpr::var(ChcVar::new("x", ChcSort::Int))]);
    }
    assert_eq!(solver.problem.clauses()[2].body.predicates.len(), 2);
    let (pred, valid) = pair(&solver);
    assert_sat_hyperedge(&mut solver, pred, &ChcExpr::not(valid.clone()));
    assert!(solver.is_entry_inductive(&valid, pred, 1));
}

#[test]
fn entry_repeated_predicate_occurrences_do_not_share_fact_locals() {
    let source = r#"
(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun C (Int Int) Bool)
(assert (forall ((x Int)) (A x)))
(assert (forall ((a Int) (b Int)) (=> (and (A a) (A b)) (C a b))))
(check-sat)
"#;
    let mut solver = solver(source);
    let body = &solver.problem.clauses()[1].body.predicates;
    assert_eq!(body.len(), 2);
    assert_eq!(body[0].0, body[1].0);
    assert_ne!(body[0].1, body[1].1);
    let pred = solver.problem.lookup_predicate("C").unwrap();
    let vars = solver.canonical_vars(pred).unwrap();
    let invalid = ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone()));
    assert_sat_hyperedge(&mut solver, pred, &invalid);
    assert!(solver.is_entry_inductive(&ChcExpr::Bool(true), pred, 1));
}

#[test]
fn entry_fresh_prefix_avoids_source_binders_of_both_sorts() {
    for (sort, constraint) in [
        (ChcSort::Int, "(and (> CAPTURE 6) (< CAPTURE 8))"),
        (ChcSort::Bool, "CAPTURE"),
    ] {
        let name = "__entry_fact_2_0_0_x";
        let sort_text = if sort == ChcSort::Int { "Int" } else { "Bool" };
        let transition = format!(
            "(assert (forall ((a Int) (b Int) ({name} {sort_text})) \
             (=> (and (A a) (B b) {}) (C a b))))",
            constraint.replace("CAPTURE", name),
        );
        let source = TWO_FACTS.replace(
            "(assert (forall ((a Int) (b Int)) (=> (and (A a) (B b)) (C a b))))",
            &transition,
        );
        let mut solver = solver(&source);
        assert!(solver.problem.clauses()[2]
            .body
            .constraint
            .as_ref()
            .unwrap()
            .vars()
            .contains(&ChcVar::new(name, sort)));
        let (pred, valid) = pair(&solver);
        assert_sat_hyperedge(&mut solver, pred, &ChcExpr::not(valid.clone()));
        assert!(solver.is_entry_inductive(&valid, pred, 1));
    }
}

#[test]
fn entry_query_only_collision_refuses_instead_of_changing_the_join() {
    for (name, collides) in [("query_local", false), ("__entry_fact_2_0_0_x", true)] {
        let mut solver = solver(TWO_FACTS);
        let (pred, valid) = pair(&solver);
        // This disjunction remains valid on the only reachable pair for any
        // value of the new local; a normal completed check must accept it.
        let valid = ChcExpr::or(
            valid,
            ChcExpr::eq(
                ChcExpr::var(ChcVar::new(name, ChcSort::Int)),
                ChcExpr::Int(9),
            ),
        );
        assert_eq!(solver.is_entry_inductive(&valid, pred, 1), !collides);
    }
}

const BLOCKING: &str = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((a Int) (CAPTURE Int))
  (=> (and (P a) (= CAPTURE (+ a 1)) (>= CAPTURE 1)) (P CAPTURE))))
(check-sat)
"#;

#[test]
fn blocking_both_levels_avoid_old_and_current_fresh_prefixes() {
    for name in ["__fact_x", "__fact_0_x"] {
        for level in [0, 1] {
            let mut solver = solver(&BLOCKING.replace("CAPTURE", name));
            let transition = &solver.problem.clauses()[1];
            let live = ChcVar::new(name, ChcSort::Int);
            assert!(transition
                .body
                .constraint
                .as_ref()
                .unwrap()
                .vars()
                .contains(&live));
            let ClauseHead::Predicate(_, args) = &transition.head else {
                panic!("head")
            };
            assert_eq!(args, &[ChcExpr::var(live)]);
            let pred = solver.problem.lookup_predicate("P").unwrap();
            let arg = ChcExpr::var(solver.canonical_vars(pred).unwrap()[0].clone());
            assert!(!solver.is_inductive_blocking(
                &ChcExpr::eq(arg.clone(), ChcExpr::Int(1)),
                pred,
                level
            ));
            assert!(solver.is_inductive_blocking(&ChcExpr::lt(arg, ChcExpr::Int(0)), pred, level));
        }
    }
}

#[test]
fn blocking_both_levels_keep_other_sort_fact_locals_apart() {
    let source = r#"
(set-logic HORN)
(declare-fun P (Int Bool) Bool)
(assert (forall ((n Int) (x Bool)) (=> (and (= n 0) x) (P n x))))
(assert (forall ((a Int) (p Bool) (__fact_0_x Int))
  (=> (and (P a p) (= __fact_0_x (+ a 1)) (>= __fact_0_x 1)) (P __fact_0_x p))))
"#;
    for level in [0, 1] {
        let mut solver = solver(source);
        assert!(solver.problem.clauses()[0]
            .body
            .constraint
            .as_ref()
            .unwrap()
            .vars()
            .contains(&ChcVar::new("x", ChcSort::Bool)));
        assert!(solver.problem.clauses()[1]
            .body
            .constraint
            .as_ref()
            .unwrap()
            .vars()
            .contains(&ChcVar::new("__fact_0_x", ChcSort::Int)));
        let pred = solver.problem.lookup_predicate("P").unwrap();
        let arg = ChcExpr::var(solver.canonical_vars(pred).unwrap()[0].clone());
        assert!(!solver.is_inductive_blocking(
            &ChcExpr::eq(arg.clone(), ChcExpr::Int(1)),
            pred,
            level
        ));
        assert!(solver.is_inductive_blocking(&ChcExpr::lt(arg, ChcExpr::Int(0)), pred, level));
    }
}

#[test]
fn blocking_query_only_collision_is_terminal_before_query_publication() {
    for level in [0, 1] {
        for (name, collides) in [("query_local", false), ("__fact_0_x", true)] {
            let mut solver = solver(&BLOCKING.replace("CAPTURE", "successor"));
            let pred = solver.problem.lookup_predicate("P").unwrap();
            let arg = ChcExpr::var(solver.canonical_vars(pred).unwrap()[0].clone());
            let blocking = ChcExpr::and(
                ChcExpr::lt(arg, ChcExpr::Int(0)),
                ChcExpr::eq(
                    ChcExpr::var(ChcVar::new(name, ChcSort::Int)),
                    ChcExpr::Int(9),
                ),
            );
            assert_eq!(
                solver.is_inductive_blocking(&blocking, pred, level),
                !collides
            );
            // Incremental PDR is currently disabled. This is only a control
            // on that posture, not exercised segment-cache coverage.
            assert!(!solver.incremental_pdr_enabled());
            assert!(solver.prop_solvers.is_empty());
        }
    }
}

fn pair_model(solver: &PdrSolver, valid: bool) -> InvariantModel {
    let (pred_c, reachable_pair) = pair(solver);
    let mut model = InvariantModel::new();
    for (name, value) in [("A", 0), ("B", 1)] {
        let pred = solver.problem.lookup_predicate(name).unwrap();
        let vars = solver.canonical_vars(pred).unwrap().to_vec();
        let formula = ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::Int(value));
        model.set(pred, PredicateInterpretation::new(vars, formula));
    }
    model.set(
        pred_c,
        PredicateInterpretation::new(
            solver.canonical_vars(pred_c).unwrap().to_vec(),
            if valid {
                reachable_pair
            } else {
                ChcExpr::not(reachable_pair)
            },
        ),
    );
    // Neither search-side evidence flag may replace final clause checking.
    model.individually_inductive = true;
    model.convergence_proven = true;
    model
}

#[test]
fn fresh_final_model_gate_rejects_the_captured_invariant() {
    for valid in [false, true] {
        let mut solver = solver(TWO_FACTS);
        let model = pair_model(&solver, valid);
        let result = solver.finish_safe_with_result_trace(model, "entry-fact-freshness-test");
        if valid {
            assert!(matches!(result, PdrResult::Safe(_)), "got {result:?}");
        } else {
            assert!(matches!(result, PdrResult::Unknown), "got {result:?}");
        }
    }
}
