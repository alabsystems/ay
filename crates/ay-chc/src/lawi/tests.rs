// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::art::{AbstractReachabilityTree, ArtLocation};
use super::covering::CoveringRelation;
use super::path_encoding::art_edge_formula_at;
use super::solver::{LawiConfig, LawiSolver};
use crate::smt::{SmtContext, SmtResult};
use crate::transition_system::TransitionSystem;
use crate::{
    ChcEngineResult, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
};

fn self_loop_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![]);

    // true => Inv()
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(inv, vec![]),
    ));

    // Inv() => Inv()
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![])]),
        ClauseHead::Predicate(inv, vec![]),
    ));

    problem
}

fn self_loop_with_query_problem() -> ChcProblem {
    let mut problem = self_loop_problem();
    let inv = problem.lookup_predicate("Inv").expect("Inv should exist");

    // Inv() => false
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![])]),
        ClauseHead::False,
    ));
    problem
}

/// Safe problem: counter increments from 0, bounded by x<5, query checks x>=10.
/// Invariant: 0 <= x <= 5.
fn bounded_increment_safe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 5 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x >= 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Unsafe problem: counter increments unboundedly from 0, query checks x>=1.
fn unbounded_increment_unsafe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x >= 1 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn branching_edge_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x = 0 => Inv(0)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::int(0)]),
    ));

    // Inv(x) /\ x = 0 => Inv(1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::int(1)]),
    ));

    // Inv(x) /\ x = 1 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));

    problem
}

// --- ART unit tests ---

#[test]
fn art_expand_prioritizes_error_edges() {
    let problem = self_loop_with_query_problem();
    let mut art = AbstractReachabilityTree::try_new(&problem).expect("art should initialize");
    let root = art.root();

    let children = art.expand(root);
    assert_eq!(
        children.len(),
        2,
        "query + transition should create two children"
    );
    assert!(
        matches!(art.location(children[0]), ArtLocation::Error),
        "error edge should be expanded first"
    );
}

#[test]
fn art_ancestor_and_path_queries_work() {
    let problem = self_loop_problem();
    let mut art = AbstractReachabilityTree::try_new(&problem).expect("art should initialize");
    let root = art.root();

    let first = art.expand(root)[0];
    let second = art.expand(first)[0];

    assert!(art.is_ancestor(root, second));
    assert!(art.is_ancestor(first, second));
    assert!(!art.is_ancestor(second, first));

    let nca = art.nearest_common_ancestor(first, second);
    assert_eq!(nca, first);

    let path = art.path_from_ancestor(root, second);
    assert_eq!(path.len(), 2);
}

#[test]
fn art_path_from_root_returns_correct_vertices() {
    let problem = self_loop_problem();
    let mut art = AbstractReachabilityTree::try_new(&problem).expect("art should initialize");
    let root = art.root();

    let first = art.expand(root)[0];
    let second = art.expand(first)[0];

    let vertices = art.path_vertices_from_root(second);
    assert_eq!(vertices.len(), 3, "path should include root, first, second");
    assert_eq!(vertices[0], root);
    assert_eq!(vertices[1], first);
    assert_eq!(vertices[2], second);
}

// --- Covering relation tests ---

#[test]
fn covering_relation_is_transitive_over_ancestors() {
    let problem = self_loop_problem();
    let mut art = AbstractReachabilityTree::try_new(&problem).expect("art should initialize");
    let mut covering = CoveringRelation::default();
    let root = art.root();

    let first = art.expand(root)[0];
    let second = art.expand(first)[0];

    covering.update_with(&art, first, root);
    assert!(covering.is_covered(first, &art));
    assert!(
        covering.is_covered(second, &art),
        "descendant should be covered via ancestor"
    );
}

#[test]
fn covering_relation_drops_pairs_when_coverer_strengthens() {
    let problem = self_loop_problem();
    let mut art = AbstractReachabilityTree::try_new(&problem).expect("art should initialize");
    let mut covering = CoveringRelation::default();
    let root = art.root();

    let first = art.expand(root)[0];
    let second = art.expand(first)[0];

    covering.update_with(&art, second, first);
    assert_eq!(covering.len(), 1);
    covering.vertex_strengthened(first);
    assert_eq!(covering.len(), 0);
}

// --- Concrete path encoding tests ---

#[test]
fn art_edge_formula_uses_selected_transition_clause() {
    let problem = branching_edge_problem();
    let ts = TransitionSystem::from_chc_problem(&problem).expect("ts should initialize");
    let stay_zero = art_edge_formula_at(&ts, &problem, 1, 0).expect("clause 1 should encode");
    let to_one = art_edge_formula_at(&ts, &problem, 2, 0).expect("clause 2 should encode");

    let v0 = ChcVar::new("v0", ChcSort::Int);
    let v0_1 = ChcVar::new("v0_1", ChcSort::Int);

    let mut smt = SmtContext::new();
    let stay_zero_sat = ChcExpr::and_all([
        stay_zero.clone(),
        ChcExpr::eq(ChcExpr::var(v0.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(v0_1.clone()), ChcExpr::int(0)),
    ]);
    assert!(
        matches!(smt.check_sat(&stay_zero_sat), SmtResult::Sat(_)),
        "clause 1 should encode the 0 -> 0 edge"
    );

    let mut smt = SmtContext::new();
    let stay_zero_unsat = ChcExpr::and_all([
        stay_zero,
        ChcExpr::eq(ChcExpr::var(v0.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(v0_1.clone()), ChcExpr::int(1)),
    ]);
    assert!(
        matches!(
            smt.check_sat(&stay_zero_unsat),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "clause 1 must not admit the 0 -> 1 edge"
    );

    let mut smt = SmtContext::new();
    let to_one_sat = ChcExpr::and_all([
        to_one.clone(),
        ChcExpr::eq(ChcExpr::var(v0.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(v0_1.clone()), ChcExpr::int(1)),
    ]);
    assert!(
        matches!(smt.check_sat(&to_one_sat), SmtResult::Sat(_)),
        "clause 2 should encode the 0 -> 1 edge"
    );

    let mut smt = SmtContext::new();
    let to_one_unsat = ChcExpr::and_all([
        to_one,
        ChcExpr::eq(ChcExpr::var(v0), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(v0_1), ChcExpr::int(0)),
    ]);
    assert!(
        matches!(
            smt.check_sat(&to_one_unsat),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "clause 2 must not collapse back to the full transition disjunction"
    );
}

#[test]
fn art_edge_formula_uses_selected_query_clause_step() {
    let problem = branching_edge_problem();
    let ts = TransitionSystem::from_chc_problem(&problem).expect("ts should initialize");
    let query = art_edge_formula_at(&ts, &problem, 3, 1).expect("query clause should encode");

    let v0_1 = ChcVar::new("v0_1", ChcSort::Int);

    let mut smt = SmtContext::new();
    let sat_query = ChcExpr::and_all([
        query.clone(),
        ChcExpr::eq(ChcExpr::var(v0_1.clone()), ChcExpr::int(1)),
    ]);
    assert!(
        matches!(smt.check_sat(&sat_query), SmtResult::Sat(_)),
        "query clause should be asserted at the selected boundary state"
    );

    let mut smt = SmtContext::new();
    let unsat_query = ChcExpr::and_all([query, ChcExpr::eq(ChcExpr::var(v0_1), ChcExpr::int(0))]);
    assert!(
        matches!(
            smt.check_sat(&unsat_query),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "query clause should not accept an unrelated state valuation"
    );
}

// --- Solver integration tests ---

#[test]
fn lawi_solver_detects_trivially_unsafe_zero_arity() {
    // 0-arity predicate with query: init ∧ query is SAT → Unsafe.
    let problem = self_loop_with_query_problem();
    let mut solver = LawiSolver::new(problem, LawiConfig::default());
    let result = solver.solve();
    // May return Unsafe (if TS extraction succeeds) or Unknown (if 0-arity
    // predicate is not representable as a TransitionSystem).
    assert!(
        matches!(
            result,
            ChcEngineResult::Unsafe(_) | ChcEngineResult::Unknown
        ),
        "0-arity query problem should be Unsafe or Unknown, got {result:?}",
    );
}

#[test]
fn lawi_solver_safe_bounded_increment() {
    // x=0, x<5 → x+1, x>=10 → false.
    // System is safe: x never reaches 10.
    let problem = bounded_increment_safe();
    let mut solver = LawiSolver::new(problem, LawiConfig::default());
    let result = solver.solve();
    assert!(
        matches!(result, ChcEngineResult::Safe(_)),
        "bounded increment should be Safe, got {result:?}",
    );
}

#[test]
fn lawi_solver_unsafe_unbounded_increment() {
    // x=0, x → x+1, x>=1 → false.
    // System is unsafe: x reaches 1 after one step.
    let problem = unbounded_increment_unsafe();
    let mut solver = LawiSolver::new(problem, LawiConfig::default());
    let result = solver.solve();
    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "unbounded increment with x>=1 query should be Unsafe, got {result:?}",
    );
}

#[test]
fn lawi_solver_returns_not_applicable_for_non_linear() {
    // Multi-predicate non-linear problem.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // true => P(0)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // true => Q(0)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));

    // P(x) /\ Q(x) => false  (non-linear: 2 body predicates)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (p, vec![ChcExpr::var(x.clone())]),
                (q, vec![ChcExpr::var(x)]),
            ],
            None,
        ),
        ClauseHead::False,
    ));

    let mut solver = LawiSolver::new(problem, LawiConfig::default());
    let result = solver.solve();
    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "non-linear problem should return Unknown, got {result:?}",
    );
}
