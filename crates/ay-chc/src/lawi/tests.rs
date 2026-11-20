// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::art::{AbstractReachabilityTree, ArtLocation};
use super::covering::CoveringRelation;
use super::path_encoding::art_edge_formula_at;
use super::solver::test_hooks::{force_itp_unknown, forced_unknown_fired, ForcedItpUnknown};
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
    let mut solver = LawiSolver::new(problem.clone(), LawiConfig::default());
    let result = solver.solve();
    let ChcEngineResult::Unsafe(cex) = result else {
        panic!("unbounded increment with x>=1 query should be Unsafe, got {result:?}");
    };
    assert_ground_evidence(&problem, &cex);
}

/// The path model is carried as a ground derivation that validates on the
/// solved problem, plus a derivation witness.
fn assert_ground_evidence(problem: &ChcProblem, cex: &crate::pdr::Counterexample) {
    let derivation = cex
        .ground_derivation
        .as_ref()
        .expect("LAWI Unsafe carries its path model as a ground derivation");
    crate::ground_derivation::validate_ground_derivation(problem, derivation)
        .expect("the carried derivation validates on the solved problem");
    assert!(
        cex.witness.is_some(),
        "Int path yields a derivation witness"
    );
}

#[test]
fn lawi_unsafe_follows_the_fired_branch_clause() {
    // Only the `Inv(x) /\ x = 0 => Inv(1)` branch (clause 2) reaches the
    // query; the derivation must name it, not the `Inv(0)` self-loop.
    let problem = branching_edge_problem();
    let mut solver = LawiSolver::new(problem.clone(), LawiConfig::default());
    let result = solver.solve();
    let ChcEngineResult::Unsafe(cex) = result else {
        panic!("branching problem is unsafe, got {result:?}");
    };
    assert_ground_evidence(&problem, &cex);
    let derivation = cex.ground_derivation.as_ref().expect("derivation");
    assert!(derivation.steps.iter().any(|step| step.clause_index == 2));
}

#[test]
fn lawi_unsafe_real_system_with_nondeterministic_local() {
    // P(0); P(x) /\ 0 <= d <= 1/2 /\ y = x + d => P(y); P(x) /\ x >= 1 => false.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Real]);
    let x = ChcVar::new("x", ChcSort::Real);
    let y = ChcVar::new("y", ChcSort::Real);
    let d = ChcVar::new("d", ChcSort::Real);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::Real(0, 1)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::and_all(vec![
                ChcExpr::le(ChcExpr::Real(0, 1), ChcExpr::var(d.clone())),
                ChcExpr::le(ChcExpr::var(d.clone()), ChcExpr::Real(1, 2)),
                ChcExpr::eq(
                    ChcExpr::var(y.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(d)),
                ),
            ])),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(y)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::Real(1, 1))),
        ),
        ClauseHead::False,
    ));
    let mut solver = LawiSolver::new(problem.clone(), LawiConfig::default());
    let result = solver.solve();
    let ChcEngineResult::Unsafe(cex) = result else {
        panic!("drifting Real counter reaches 1, got {result:?}");
    };
    let derivation = cex
        .ground_derivation
        .as_ref()
        .expect("Real path model is carried as a ground derivation");
    crate::ground_derivation::validate_ground_derivation(&problem, derivation)
        .expect("validates on the solved problem");
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

// --- Refinement soundness (cav12 transmitter.5: Safe(true) on an unsafe task) ---

/// x = 0 ∧ y = 0; x < 3 ⇒ (x+1, y+1); x ≠ y ⇒ false. Safe: x = y.
/// The query edge has no clause-local variable.
fn lockstep_counters_safe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let args = || vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())];
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(inv, args()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, args())],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::int(1)),
            ],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, args())],
            Some(ChcExpr::not(ChcExpr::eq(
                ChcExpr::var(x.clone()),
                ChcExpr::var(y.clone()),
            ))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// Clears the injected interpolation fault when the test ends.
struct ForcedItpGuard;

impl ForcedItpGuard {
    fn install(boundary: usize, suppress_fallback: bool) -> Self {
        Self::install_limited(boundary, suppress_fallback, usize::MAX)
    }

    fn install_limited(boundary: usize, suppress_fallback: bool, max_fires: usize) -> Self {
        force_itp_unknown(Some(ForcedItpUnknown {
            boundary,
            suppress_fallback,
            max_fires,
        }));
        Self
    }
}

impl Drop for ForcedItpGuard {
    fn drop(&mut self) {
        force_itp_unknown(None);
    }
}

/// A Safe result must be finished, well-labeled, and a model the original
/// clauses accept.
fn assert_sound_safe(problem: &ChcProblem, solver: &LawiSolver, result: &ChcEngineResult) {
    let ChcEngineResult::Safe(model) = result else {
        return;
    };
    assert_eq!(
        solver.unfinished_vertex_count(),
        0,
        "Safe with an unfinished ART"
    );
    assert!(
        solver.well_labeling_violations().is_empty(),
        "Safe over a labeling that is not well-labeled: {:?}",
        solver.well_labeling_violations()
    );
    let mut verifier = crate::PdrSolver::new(problem.clone(), crate::PdrConfig::default());
    assert!(
        verifier.verify_model(model),
        "LAWI Safe model must be inductive"
    );
}

#[test]
fn lawi_interpolation_gap_never_yields_an_unsound_safe() {
    // Before the fix a gap at a boundary returned a partial `Refined`, the
    // error vertex was dropped, and covering closed over a `true` label. Now
    // the error vertex is abandoned: the labeling stays well-labeled, and
    // Safe needs every abandoned vertex covered or refuted after all.
    for problem in [bounded_increment_safe(), lockstep_counters_safe()] {
        for boundary in 1..=4 {
            let _fault = ForcedItpGuard::install(boundary, true);
            let mut solver = LawiSolver::new(problem.clone(), LawiConfig::default());
            let result = solver.solve();
            assert!(
                solver.well_labeling_violations().is_empty(),
                "gap at boundary {boundary}: labeling not well-labeled: {:?}",
                solver.well_labeling_violations()
            );
            if forced_unknown_fired() > 0 {
                assert!(
                    matches!(result, ChcEngineResult::Unknown | ChcEngineResult::Safe(_)),
                    "a forced interpolation gap at boundary {boundary}: got {result:?}",
                );
            } else {
                // The ART closed before any path reached this boundary.
                assert!(
                    matches!(result, ChcEngineResult::Safe(_)),
                    "no gap was hit at boundary {boundary}, expected Safe, got {result:?}",
                );
            }
            assert_sound_safe(&problem, &solver, &result);
            if boundary == 1 {
                assert!(
                    forced_unknown_fired() > 0,
                    "every refinement past the root crosses boundary 1"
                );
                // Boundary 1 fails on every path of length >= 2: nothing can
                // refute those error vertices.
                assert!(
                    matches!(result, ChcEngineResult::Unknown),
                    "gap at boundary 1 on every path must end Unknown, got {result:?}",
                );
            }
        }
    }
}

#[test]
fn lawi_abandoned_error_path_does_not_stop_the_search() {
    // x = 0; x -> x + 1; x >= 3 -> false. Unsafe at depth 3. Every path of
    // length >= 2 loses its boundary-1 interpolant, so the error vertices at
    // depth 2 and 3 are abandoned; with covering off LAWI goes on to the
    // feasible depth-4 path. Before, the first gap ended LAWI with Unknown.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(3))),
        ),
        ClauseHead::False,
    ));
    let _fault = ForcedItpGuard::install(1, true);
    let config = LawiConfig {
        covering_candidate_limit: 0,
        max_vertices: 64,
        ..LawiConfig::default()
    };
    let mut solver = LawiSolver::new(problem.clone(), config);
    let result = solver.solve();
    assert!(
        forced_unknown_fired() >= 2,
        "the depth-2 and depth-3 paths hit the forced gap"
    );
    assert!(
        solver.abandoned_error_count() >= 2,
        "both spurious paths were abandoned"
    );
    let ChcEngineResult::Unsafe(cex) = result else {
        panic!("LAWI must search past abandoned error paths, got {result:?}");
    };
    assert_ground_evidence(&problem, &cex);
}

#[test]
fn lawi_one_off_gap_keeps_safe_sound() {
    // A single gap (the first boundary-1 call) abandons one error vertex;
    // later refinements may strengthen its parent enough to refute it.
    // Whatever happens, a Safe has no open abandoned vertex and is sound.
    for problem in [bounded_increment_safe(), lockstep_counters_safe()] {
        let _fault = ForcedItpGuard::install_limited(1, true, 1);
        let mut solver = LawiSolver::new(problem.clone(), LawiConfig::default());
        let result = solver.solve();
        assert_eq!(forced_unknown_fired(), 1);
        assert!(
            matches!(result, ChcEngineResult::Unknown | ChcEngineResult::Safe(_)),
            "safe problem with one gap: got {result:?}",
        );
        assert!(solver.well_labeling_violations().is_empty());
        if matches!(result, ChcEngineResult::Safe(_)) {
            assert_eq!(solver.abandoned_error_count(), 0, "Safe with an open error");
        }
        assert_sound_safe(&problem, &solver, &result);
    }
}

/// Init Inv(5, 7); Inv(v1, v0) ∧ v1 > 0 ⇒ Inv(v1 - 5, v0);
/// Inv(v1, v0) ∧ v1 < 1 ⇒ false. The clause variables are named like the
/// canonical state variables but sit in swapped positions: the first
/// argument goes 5 → 0, so the system is unsafe at depth 1. Renaming the
/// arguments one at a time captured `v1` into the second position, which
/// never drops below 7, and the encoding read the system as safe.
fn swapped_canonical_names_unsafe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
    let v0 = ChcVar::new("v0", ChcSort::Int);
    let v1 = ChcVar::new("v1", ChcSort::Int);
    let swapped = || vec![ChcExpr::var(v1.clone()), ChcExpr::var(v0.clone())];
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(inv, vec![ChcExpr::int(5), ChcExpr::int(7)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, swapped())],
            Some(ChcExpr::gt(ChcExpr::var(v1.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::sub(ChcExpr::var(v1.clone()), ChcExpr::int(5)),
                ChcExpr::var(v0.clone()),
            ],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, swapped())],
            Some(ChcExpr::lt(ChcExpr::var(v1.clone()), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));
    problem
}

#[test]
fn lawi_clause_variables_named_like_state_variables_are_not_captured() {
    let problem = swapped_canonical_names_unsafe();
    let mut solver = LawiSolver::new(problem.clone(), LawiConfig::default());
    let result = solver.solve();
    let ChcEngineResult::Unsafe(cex) = result else {
        panic!("first argument reaches 0 after one step, got {result:?}");
    };
    assert_ground_evidence(&problem, &cex);
}

#[test]
fn lawi_interpolation_gap_on_unsafe_problem_never_safe() {
    let problem = unbounded_increment_unsafe();
    for boundary in 1..=3 {
        let _fault = ForcedItpGuard::install(boundary, true);
        let mut solver = LawiSolver::new(problem.clone(), LawiConfig::default());
        let result = solver.solve();
        assert!(
            matches!(
                result,
                ChcEngineResult::Unsafe(_) | ChcEngineResult::Unknown
            ),
            "unsafe problem with a gap at boundary {boundary}: got {result:?}",
        );
    }
}

#[test]
fn lawi_last_boundary_fallback_keeps_refining_soundly() {
    // With the `¬query` fallback the forced gap at the last boundary is
    // filled by the weakest valid interpolant; any Safe must still be sound.
    for problem in [bounded_increment_safe(), lockstep_counters_safe()] {
        for boundary in 1..=4 {
            let _fault = ForcedItpGuard::install(boundary, false);
            let mut solver = LawiSolver::new(problem.clone(), LawiConfig::default());
            let result = solver.solve();
            assert!(
                matches!(result, ChcEngineResult::Safe(_) | ChcEngineResult::Unknown),
                "safe problem, gap at boundary {boundary}: got {result:?}",
            );
            assert_sound_safe(&problem, &solver, &result);
        }
    }
}

#[test]
fn lawi_chained_refinement_is_well_labeled() {
    for problem in [bounded_increment_safe(), lockstep_counters_safe()] {
        let mut solver = LawiSolver::new(problem.clone(), LawiConfig::default());
        let result = solver.solve();
        assert!(
            matches!(result, ChcEngineResult::Safe(_)),
            "expected Safe, got {result:?}",
        );
        assert_sound_safe(&problem, &solver, &result);
    }
}

#[test]
fn lawi_last_boundary_fallback_only_without_clause_locals() {
    // Query edge over state variables only: ¬query is a valid interpolant.
    let solver = LawiSolver::new(lockstep_counters_safe(), LawiConfig::default());
    let fallback = solver.last_boundary_fallback_for(2, 3);
    assert!(
        fallback.is_some(),
        "a local-free query edge takes the ¬query fallback"
    );

    // Inv(x) ∧ x = z + z ∧ z > 10 ⇒ false: the query edge has the local z,
    // the interpolant would be ¬∃z. query, and no fallback is taken.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(2))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(x),
                    ChcExpr::add(ChcExpr::var(z.clone()), ChcExpr::var(z.clone())),
                ),
                ChcExpr::gt(ChcExpr::var(z), ChcExpr::int(10)),
            )),
        ),
        ClauseHead::False,
    ));
    let solver = LawiSolver::new(problem, LawiConfig::default());
    assert!(
        solver.last_boundary_fallback_for(2, 3).is_none(),
        "a query edge with a clause-local variable must not take the fallback",
    );
}
