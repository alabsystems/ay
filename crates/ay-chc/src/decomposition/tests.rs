// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcSort;

/// Create a linear chain problem: P1 -> P2 -> P3
///
/// P1(x) := x = 0
/// P2(x) := P1(x-1)  (i.e., x = 1)
/// P3(x) := P2(x-1)  (i.e., x = 2)
/// Query: P3(x) /\ x > 10 => false (should be safe)
fn create_chain_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p1 = problem.declare_predicate("P1", vec![ChcSort::Int]);
    let p2 = problem.declare_predicate("P2", vec![ChcSort::Int]);
    let p3 = problem.declare_predicate("P3", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => P1(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p1, vec![ChcExpr::var(x.clone())]),
    ));

    // P1(x-1) => P2(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            p1,
            vec![ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        )]),
        ClauseHead::Predicate(p2, vec![ChcExpr::var(x.clone())]),
    ));

    // P2(x-1) => P3(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            p2,
            vec![ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        )]),
        ClauseHead::Predicate(p3, vec![ChcExpr::var(x.clone())]),
    ));

    // P3(x) /\ x > 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p3, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Create a tree problem: P1 -> {P2, P3}
///
/// P1(x) := x = 0
/// P2(x) := P1(x)
/// P3(x) := P1(x)
/// Query: P2(x) /\ P3(y) /\ x + y > 10 => false
fn create_tree_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p1 = problem.declare_predicate("P1", vec![ChcSort::Int]);
    let p2 = problem.declare_predicate("P2", vec![ChcSort::Int]);
    let p3 = problem.declare_predicate("P3", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // x = 0 => P1(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p1, vec![ChcExpr::var(x.clone())]),
    ));

    // P1(x) => P2(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p1, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(p2, vec![ChcExpr::var(x.clone())]),
    ));

    // P1(x) => P3(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p1, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(p3, vec![ChcExpr::var(x.clone())]),
    ));

    // P2(x) /\ P3(y) /\ x + y > 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (p2, vec![ChcExpr::var(x.clone())]),
                (p3, vec![ChcExpr::var(y.clone())]),
            ],
            Some(ChcExpr::gt(
                ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y)),
                ChcExpr::int(10),
            )),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Create a single-SCC problem (cyclic, no decomposition benefit)
fn create_cyclic_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // P(x) /\ x < 5 => P(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            p,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // P(x) /\ x > 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_chain_decomposition() {
    let problem = create_chain_problem();
    let config = DecompositionConfig::default();
    let solver = DecompositionSolver::new(problem, config);
    let result = solver.solve();

    // Chain should decompose into 3 SCCs and solve
    match result {
        DecompositionResult::Safe(model) => {
            // Should have invariants for P1, P2, P3
            assert!(!model.is_empty(), "expected non-empty invariant model");
        }
        DecompositionResult::Unknown => {
            // Acceptable if PDR couldn't solve a subproblem
        }
        DecompositionResult::NotApplicable => {
            panic!("chain problem should be decomposable");
        }
        DecompositionResult::Unsafe(_) => {
            panic!("chain problem is safe");
        }
    }
}

#[test]
fn test_tree_decomposition() {
    let problem = create_tree_problem();
    let config = DecompositionConfig::default();
    let solver = DecompositionSolver::new(problem, config);
    let result = solver.solve();

    match result {
        DecompositionResult::Safe(model) => {
            assert!(!model.is_empty());
        }
        DecompositionResult::Unknown => {
            // Acceptable
        }
        DecompositionResult::NotApplicable => {
            panic!("tree problem should be decomposable");
        }
        DecompositionResult::Unsafe(_) => {
            panic!("tree problem is safe");
        }
    }
}

#[test]
fn test_cyclic_not_decomposable() {
    let problem = create_cyclic_problem();
    let config = DecompositionConfig::default();
    let solver = DecompositionSolver::new(problem, config);
    assert!(matches!(solver.solve(), DecompositionResult::NotApplicable));
}

#[test]
fn test_single_predicate_not_applicable() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let solver = DecompositionSolver::new(problem, DecompositionConfig::default());
    assert!(matches!(solver.solve(), DecompositionResult::NotApplicable));
}

#[test]
fn test_scc_info_for_chain() {
    let problem = create_chain_problem();
    let scc_info = tarjan_scc(&problem);

    // Chain P1 -> P2 -> P3 should have 3 non-cyclic SCCs
    assert_eq!(scc_info.sccs.len(), 3, "chain should have 3 SCCs");

    for scc in &scc_info.sccs {
        assert_eq!(scc.predicates.len(), 1, "each SCC should have 1 predicate");
        assert!(!scc.is_cyclic, "chain SCCs should not be cyclic");
    }
}

#[test]
fn test_substitute_interpretation_substitutes_vars_on_success() {
    let solver = DecompositionSolver::new(ChcProblem::new(), DecompositionConfig::default());

    let v0 = ChcVar::new("v0", ChcSort::Int);
    let v1 = ChcVar::new("v1", ChcSort::Int);
    let interp = PredicateInterpretation::new(
        vec![v0.clone(), v1.clone()],
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(v0), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(v1), ChcExpr::int(1)),
        ),
    );

    let args = vec![ChcExpr::int(10), ChcExpr::int(20)];
    let substituted = solver
        .substitute_interpretation(&interp, &args)
        .expect("expected successful substitution");

    let expected = ChcExpr::and(
        ChcExpr::eq(ChcExpr::int(10), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::int(20), ChcExpr::int(1)),
    );
    assert_eq!(substituted, expected);
}

#[test]
fn test_substitute_interpretation_returns_none_on_arity_mismatch() {
    let solver = DecompositionSolver::new(ChcProblem::new(), DecompositionConfig::default());

    let v0 = ChcVar::new("v0", ChcSort::Int);
    let v1 = ChcVar::new("v1", ChcSort::Int);
    let interp = PredicateInterpretation::new(vec![v0, v1], ChcExpr::Bool(true));

    // 2 vars, 3 args => arity mismatch.
    let args = vec![ChcExpr::int(1), ChcExpr::int(2), ChcExpr::int(3)];

    assert!(solver.substitute_interpretation(&interp, &args).is_none());
}

#[test]
fn test_extract_subproblem_substitutes_known_invariants_into_constraints() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // P(x) => Q(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));

    // Q(x) /\ x > 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let solver = DecompositionSolver::new(problem, DecompositionConfig::default());

    // Known invariant for P(v): v = 0
    let v = ChcVar::new("v", ChcSort::Int);
    let mut known_invariants: FxHashMap<PredicateId, PredicateInterpretation> =
        FxHashMap::default();
    known_invariants.insert(
        p,
        PredicateInterpretation::new(
            vec![v.clone()],
            ChcExpr::eq(ChcExpr::var(v), ChcExpr::int(0)),
        ),
    );

    let q_scc = PredicateSCC {
        predicates: vec![q],
        is_cyclic: false,
    };

    let subproblem = solver
        .extract_subproblem(&q_scc, &known_invariants)
        .expect("expected subproblem extraction");

    assert_eq!(subproblem.predicates().len(), 1);
    let q_sub = subproblem
        .lookup_predicate("Q")
        .expect("Q should be declared");

    let mut def_clauses = subproblem.clauses_defining(q_sub);
    let def_clause = def_clauses.next().expect("expected defining clause for Q");
    assert!(
        def_clauses.next().is_none(),
        "expected exactly one defining clause"
    );

    assert!(
        def_clause.body.predicates.is_empty(),
        "expected P(x) to be substituted away"
    );
    assert_eq!(
        def_clause.body.constraint,
        Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)))
    );
    let ClauseHead::Predicate(pred, args) = &def_clause.head else {
        panic!("expected predicate head");
    };
    assert_eq!(*pred, q_sub);
    assert_eq!(args, &vec![ChcExpr::var(x.clone())]);

    let mut queries = subproblem.queries();
    let query = queries.next().expect("expected query clause");
    assert!(
        queries.next().is_none(),
        "expected exactly one query clause"
    );

    assert!(query.is_query());
    assert_eq!(query.body.predicates.len(), 1);
    assert_eq!(query.body.predicates[0].0, q_sub);
    assert_eq!(query.body.predicates[0].1, vec![ChcExpr::var(x.clone())]);
    assert_eq!(
        query.body.constraint,
        Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10)))
    );
}

#[test]
fn test_extract_subproblem_fails_on_missing_invariant() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x)]),
    ));

    let solver = DecompositionSolver::new(problem, DecompositionConfig::default());
    let q_scc = PredicateSCC {
        predicates: vec![q],
        is_cyclic: false,
    };

    let known_invariants: FxHashMap<PredicateId, PredicateInterpretation> = FxHashMap::default();
    assert!(solver
        .extract_subproblem(&q_scc, &known_invariants)
        .is_none());
}

#[test]
fn test_extract_subproblem_fails_when_scc_body_predicate_unmapped() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);

    // A predicate ID referenced in a clause but not declared in `problem`.
    let unmapped = PredicateId::new(999);

    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(unmapped, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));

    // Simulate a (buggy) SCC that includes an undeclared predicate ID.
    let scc = PredicateSCC {
        predicates: vec![p, unmapped],
        is_cyclic: false,
    };

    let solver = DecompositionSolver::new(problem, DecompositionConfig::default());
    let known_invariants: FxHashMap<PredicateId, PredicateInterpretation> = FxHashMap::default();
    assert!(solver.extract_subproblem(&scc, &known_invariants).is_none());
}

#[test]
fn test_extract_subproblem_fails_when_scc_head_predicate_unmapped() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);

    // A predicate ID referenced in a clause but not declared in `problem`.
    let unmapped = PredicateId::new(999);

    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(unmapped, vec![ChcExpr::var(x)]),
    ));

    // Simulate a (buggy) SCC that includes an undeclared predicate ID.
    let scc = PredicateSCC {
        predicates: vec![p, unmapped],
        is_cyclic: false,
    };

    let solver = DecompositionSolver::new(problem, DecompositionConfig::default());
    let known_invariants: FxHashMap<PredicateId, PredicateInterpretation> = FxHashMap::default();
    assert!(solver.extract_subproblem(&scc, &known_invariants).is_none());
}

#[test]
fn test_decomposition_returns_unknown_on_substitution_arity_mismatch() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // No clauses define P, so its SCC will be skipped and given a trivial invariant.
    // Malformed call: P expects 1 argument, but the body uses 2.
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(y)])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x)]),
    ));

    let solver = DecompositionSolver::new(problem, DecompositionConfig::default());
    assert!(matches!(solver.solve(), DecompositionResult::Unknown));
}

/// Test that the merged model from decomposition is verified against the original problem.
/// This ensures the verify_model() call on line 276 is working correctly.
#[test]
fn test_decomposition_verifies_merged_model() {
    // Create a simple chain problem that should decompose and verify successfully
    let problem = create_chain_problem();
    let config = DecompositionConfig::default();
    let solver = DecompositionSolver::new(problem.clone(), config);
    let result = solver.solve();

    match result {
        DecompositionResult::Safe(model) => {
            // Double-check: manually verify the returned model against the original problem
            let mut verifier = PdrSolver::new(problem, PdrConfig::default());
            assert!(
                verifier.verify_model(&model),
                "decomposition returned a model that fails verification"
            );
        }
        DecompositionResult::Unknown => {
            // Acceptable if PDR couldn't solve a subproblem, but we can't verify
        }
        DecompositionResult::NotApplicable | DecompositionResult::Unsafe(_) => {
            panic!("chain problem should be decomposable and safe");
        }
    }
}
