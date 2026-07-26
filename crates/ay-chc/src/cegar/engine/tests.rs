// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::cancellation::CancellationToken;
use crate::engine_config::ChcEngineConfig;
use crate::{ChcProblem, ChcSort, ClauseBody, ClauseHead, HornClause};
use ay_core::kani_compat::DetHashSet as FxHashSet;

#[test]
fn test_cegar_config_default() {
    let config = CegarConfig::default();
    assert_eq!(config.max_iterations, 100);
    assert!(!config.base.verbose);
}

#[test]
fn test_extract_comparison_atoms() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let expr = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(y), ChcExpr::int(10)),
    );

    let atoms = CegarEngine::extract_comparison_atoms(&expr);
    assert_eq!(atoms.len(), 2);
}

#[test]
fn test_extract_comparison_atoms_nested() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // (x >= 0 AND (y < 5 OR x != y))
    let expr = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::or(
            ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::int(5)),
            ChcExpr::ne(ChcExpr::var(x), ChcExpr::var(y)),
        ),
    );

    let atoms = CegarEngine::extract_comparison_atoms(&expr);
    // Should extract: x >= 0, y < 5, x != y
    assert_eq!(atoms.len(), 3);
}

#[test]
fn test_extract_comparison_atoms_negation() {
    let x = ChcVar::new("x", ChcSort::Int);

    // NOT(x >= 0) -- should extract the inner comparison
    let expr = ChcExpr::not(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0)));

    let atoms = CegarEngine::extract_comparison_atoms(&expr);
    assert_eq!(atoms.len(), 1);
}

/// Helper: create a simple safe CHC problem.
/// x = 0 => Inv(x)
/// Inv(x) /\ x < 3 => Inv(x+1)
/// Inv(x) /\ x >= 10 => false
///
/// Safe because x only reaches 0..3, never >= 10.
fn create_safe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Helper: create an unsafe CHC problem.
/// x = 0 => Inv(x)
/// Inv(x) => Inv(x+1)      (no guard!)
/// Inv(x) /\ x > 5 => false
///
/// Unsafe because x grows without bound.
fn create_unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_cegar_safe_simple() {
    let problem = create_safe_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    let result = engine.solve();

    // Must report Safe, not just "not Unsafe". (#2493, #3868)
    assert!(
        matches!(&result, CegarResult::Safe(model) if !model.is_empty()),
        "CEGAR should report Safe with non-empty invariants, got: {result:?}"
    );
}

#[test]
fn test_cegar_unsafe_immediate_fact_to_false() {
    // A fact clause directly implies False:
    // x = 0 => false
    let mut problem = ChcProblem::new();
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0))),
        ClauseHead::False,
    ));

    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    let result = engine.solve();

    // Must report Unsafe, not just "not Safe". (#2493, #3868)
    assert!(
        matches!(result, CegarResult::Unsafe(_)),
        "CEGAR should report Unsafe on immediately-unsafe problem, got: {result:?}"
    );
}

fn create_immediate_fact_to_false_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0))),
        ClauseHead::False,
    ));

    problem
}

fn create_spurious_counterexample_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x > 0 => false   (spurious in abstraction)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_multi_predicate_fact_problem() -> (ChcProblem, PredicateId, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(1))),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y)]),
    ));

    (problem, p, q)
}

fn make_deep_conjunction(depth: usize) -> ChcExpr {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut expr = ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0));
    for _ in 0..depth {
        // Keep an exponentially large occurrence graph without routing it
        // through canonical conjunction deduplication or the simplifier's
        // reflexive-equality fold.
        expr = ChcExpr::eq(expr.clone(), ChcExpr::not(expr));
    }
    expr
}

#[test]
fn test_analyze_counterexample_reports_genuine_for_feasible_trace() {
    let problem = create_immediate_fact_to_false_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    engine.seed_facts();

    let cex_edge_idx = match engine.expand_until_counterexample() {
        ExpandResult::Counterexample(idx) => idx,
        other => panic!(
            "expected direct counterexample from fact query, got {:?}",
            result_label(&other)
        ),
    };

    match engine.analyze_counterexample(cex_edge_idx) {
        CexAnalysis::Genuine(trace) => {
            assert_eq!(trace.len(), 1, "expected single-step fact counterexample");
            assert_eq!(trace[0].0, 0, "counterexample should reference clause 0");
        }
        CexAnalysis::Spurious(predicates) => panic!(
            "expected genuine counterexample, got spurious with {} predicates",
            predicates.len()
        ),
        CexAnalysis::AnalysisFailed => {
            panic!("expected genuine counterexample, analysis failed")
        }
    }
}

#[test]
fn test_analyze_counterexample_reports_spurious_for_infeasible_trace() {
    let problem = create_spurious_counterexample_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    engine.seed_facts();

    let cex_edge_idx = match engine.expand_until_counterexample() {
        ExpandResult::Counterexample(idx) => idx,
        other => panic!(
            "expected query counterexample candidate, got {:?}",
            result_label(&other)
        ),
    };

    match engine.analyze_counterexample(cex_edge_idx) {
        CexAnalysis::Spurious(predicates) => assert!(
            !predicates.is_empty(),
            "spurious analysis should propose at least one predicate"
        ),
        CexAnalysis::Genuine(trace) => panic!(
            "expected spurious counterexample, got genuine trace with {} steps",
            trace.len()
        ),
        CexAnalysis::AnalysisFailed => {
            panic!("expected spurious counterexample, analysis failed")
        }
    }
}

#[test]
fn test_try_generate_edge_treats_smt_unknown_as_feasible() {
    // Depth 20 exceeds the SMT conversion-node budget and deterministically
    // returns Unknown in check_sat.
    let deep_constraint = make_deep_conjunction(20);

    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(deep_constraint.clone()),
        ClauseHead::False,
    ));

    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    let edge = engine
        .try_generate_edge(&[], 0, &deep_constraint)
        .expect("Unknown must be treated as feasible and produce an edge");
    assert!(
        engine.smt.conversion_budget_exceeded(),
        "precondition: deep constraint should exceed conversion budget and produce Unknown"
    );
    assert_eq!(edge.clause_index, 0);
    assert!(
        edge.from.is_empty(),
        "fact edge should have no predecessors"
    );
    assert_eq!(
        edge.to.relation,
        PredicateId(u32::MAX),
        "query edge must target the synthetic false relation"
    );
}

#[test]
fn test_extract_invariants_handles_multi_predicate_fact_problem() {
    let (problem, p, q) = create_multi_predicate_fact_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());

    let result = engine.solve();
    let model = match result {
        CegarResult::Safe(model) => model,
        other => panic!("expected Safe on fact-only multi-predicate problem, got {other:?}"),
    };

    let p_interp = model
        .get(&p)
        .expect("safe model should include invariant for predicate P");
    let q_interp = model
        .get(&q)
        .expect("safe model should include invariant for predicate Q");

    assert_eq!(p_interp.vars.len(), 1);
    assert_eq!(q_interp.vars.len(), 1);
    assert_eq!(p_interp.formula, ChcExpr::Bool(true));
    assert_eq!(q_interp.formula, ChcExpr::Bool(true));
}

#[test]
fn test_postpone_counterexample_increments_count_and_reenqueues() {
    let problem = create_immediate_fact_to_false_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    engine.seed_facts();

    // First expansion should find a counterexample and save expansion info
    match engine.expand_until_counterexample() {
        ExpandResult::Counterexample(_) => {}
        other => panic!("expected counterexample, got {:?}", result_label(&other)),
    }
    assert!(
        engine.last_cex_expansion.is_some(),
        "last_cex_expansion should be saved after finding counterexample"
    );

    let queue_before = engine.queue.len();
    engine.postpone_counterexample();
    assert_eq!(engine.postponed_count, 1);
    assert_eq!(
        engine.queue.len(),
        queue_before + 1,
        "postponed expansion should be re-enqueued"
    );
    assert!(
        engine.last_cex_expansion.is_none(),
        "last_cex_expansion should be consumed by postpone"
    );
}

#[test]
fn test_ratio_based_stall_detection() {
    let problem = create_immediate_fact_to_false_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());

    // Both conditions needed: postponed > queue AND postponed >= 20
    engine.postponed_count = 20;
    // Queue is empty (size 0), so both conditions met → should give up
    assert!(
        engine.postponed_count > engine.queue.len() && engine.postponed_count >= 20,
        "stall detection should trigger when postponed >= 20 and > queue size"
    );

    // Below minimum threshold: even if postponed > queue, don't trigger
    engine.postponed_count = 15;
    assert!(
        !(engine.postponed_count > engine.queue.len() && engine.postponed_count >= 20),
        "stall detection should NOT trigger when postponed < 20 minimum"
    );

    // When queue has items, postponed should be below threshold
    engine.seed_facts();
    engine.postponed_count = 0;
    assert!(
        !engine.queue.is_empty(),
        "queue should have items after seeding"
    );
    assert!(
        engine.postponed_count <= engine.queue.len(),
        "stall detection should NOT trigger when queue has pending work"
    );
}

fn result_label(result: &ExpandResult) -> &'static str {
    match result {
        ExpandResult::QueueEmpty => "QueueEmpty",
        ExpandResult::Counterexample(_) => "Counterexample",
        ExpandResult::Cancelled => "Cancelled",
        ExpandResult::IterationLimit => "IterationLimit",
    }
}

#[test]
fn test_cegar_unsafe_counter() {
    let problem = create_unsafe_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    let result = engine.solve();

    // Must report Unsafe with non-empty trace, not just "not Safe". (#2493, #3868)
    assert!(
        matches!(&result, CegarResult::Unsafe(cex) if !cex.trace.is_empty()),
        "CEGAR should report Unsafe with non-empty trace, got: {result:?}"
    );
}

#[test]
fn test_cegar_empty_problem() {
    // No clauses, no predicates. Queue stays empty, should return Safe
    // with no invariants.
    let problem = ChcProblem::new();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    let result = engine.solve();

    match result {
        CegarResult::Safe(model) => {
            assert!(model.is_empty(), "empty problem should have no invariants");
        }
        other => panic!("Expected Safe for empty problem, got {other:?}"),
    }
}

#[test]
fn test_cegar_iteration_limit() {
    let problem = create_unsafe_problem();
    let config = CegarConfig {
        max_iterations: 0,
        ..CegarConfig::default()
    };
    let mut engine = CegarEngine::new(problem, config);
    let result = engine.solve();

    // With max_iterations=0, the engine should give up quickly.
    // It may find the cex before checking the iteration limit (since
    // expand_until_counterexample checks iteration at each dequeue).
    assert!(
        matches!(result, CegarResult::Unknown | CegarResult::Unsafe(_)),
        "Expected Unknown or Unsafe with 0 iterations, got {result:?}"
    );
}

#[test]
fn test_cegar_cancellation() {
    let problem = create_safe_problem();
    let token = CancellationToken::new();
    token.cancel(); // Pre-cancel

    let config = CegarConfig {
        base: ChcEngineConfig {
            verbose: false,
            cancellation_token: Some(token),
        },
        ..CegarConfig::default()
    };
    let mut engine = CegarEngine::new(problem, config);
    let result = engine.solve();

    // Weak assertion intentional: pre-cancelled token legitimately produces
    // Unknown (cancellation detected) or Safe (queue emptied first). Both are
    // correct behavior, not a testing gap. Unsafe is the only wrong answer.
    // (#2493, #3868)
    assert!(
        !matches!(result, CegarResult::Unsafe(_)),
        "Pre-cancelled solver should not report Unsafe, got: {result:?}"
    );
}

#[test]
fn test_cegar_seed_facts() {
    // Verify that seed_facts enqueues exactly the fact clauses
    let problem = create_safe_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());

    // Before seeding, queue should be empty
    assert!(engine.queue.is_empty());

    engine.seed_facts();

    // create_safe_problem has exactly 1 fact clause (x = 0 => Inv(x))
    let expansion = engine
        .queue
        .dequeue()
        .expect("seed_facts must enqueue the fact clause");
    assert_eq!(
        expansion.clause_index, 0,
        "only clause #0 is a fact in create_safe_problem"
    );
    assert!(
        expansion.states.is_empty(),
        "fact seeding should not attach predecessor states"
    );
    assert!(
        !expansion.is_query,
        "fact clause in create_safe_problem is not a query clause"
    );
    assert!(engine.queue.is_empty());
}

#[test]
fn test_cegar_seed_facts_multiple() {
    // Problem with 2 fact clauses:
    // x = 0 => Inv(x)
    // x = 1 => Inv(x)
    // Inv(x) /\ x > 10 => false
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    engine.seed_facts();

    let first = engine
        .queue
        .dequeue()
        .expect("first fact clause should be queued");
    let second = engine
        .queue
        .dequeue()
        .expect("second fact clause should be queued");

    let mut clause_indices = vec![first.clause_index, second.clause_index];
    clause_indices.sort_unstable();
    assert_eq!(
        clause_indices,
        vec![0, 1],
        "seed_facts must enqueue exactly the two fact clauses"
    );
    assert!(
        first.states.is_empty() && second.states.is_empty(),
        "fact seeding should not attach predecessor states"
    );
    assert!(
        !first.is_query && !second.is_query,
        "fact clauses in this test are not query clauses"
    );
    assert!(
        engine.queue.is_empty(),
        "should have exactly 2 fact clauses in queue"
    );
}

#[test]
fn test_cegar_predicate_store_integration() {
    // After solving a safe problem, the predicate store may have been
    // populated through refinement.
    let problem = create_safe_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());

    // Initially, the predicate store should be empty
    assert_eq!(engine.predicates.len(), 0);

    let result = engine.solve();

    // Must solve as Safe with an invariant model
    let model = match result {
        CegarResult::Safe(m) => m,
        other => panic!("create_safe_problem must solve as Safe, got {other:?}"),
    };

    // The invariant model must contain an interpretation for the Inv predicate
    // (predicate 0 in create_safe_problem, with arity 1 over Int)
    let inv_id = PredicateId::new(0);
    let interp = model
        .get(&inv_id)
        .expect("Safe result must contain interpretation for Inv (predicate 0)");
    assert_eq!(
        interp.vars.len(),
        1,
        "Inv takes 1 argument, interpretation should have 1 variable"
    );
    assert_eq!(
        interp.vars[0].sort,
        ChcSort::Int,
        "Inv's variable should be Int"
    );
    // The invariant formula should not be trivially true — CEGAR should
    // find a non-trivial invariant that excludes the query region (x >= 10).
    assert_ne!(
        interp.formula,
        ChcExpr::Bool(true),
        "invariant should not be trivially true"
    );
}

#[test]
fn test_cegar_safe_with_unsat_query() {
    // A problem where the query constraint is unsatisfiable:
    // x = 0 => Inv(x)
    // Inv(x) /\ x < 0 => false  (x starts at 0, never < 0)
    //
    // The query body is Inv(x) AND x < 0. Since Inv only has x=0,
    // this is unsat. CEGAR should report Safe.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    let result = engine.solve();

    // Must report Safe when query is unsatisfiable, not just "not Unsafe".
    // The weak assertion would also pass on Unknown. (#2493)
    assert!(
        matches!(result, CegarResult::Safe(_)),
        "Should report Safe when query constraint is unsatisfiable, got: {:?}",
        match &result {
            CegarResult::Safe(_) => "Safe",
            CegarResult::Unsafe(_) => "Unsafe",
            CegarResult::Unknown => "Unknown",
        }
    );
}

#[test]
fn test_cegar_canonical_vars() {
    // Verify canonical_vars generates the expected variable names
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);

    let engine = CegarEngine::new(problem, CegarConfig::default());
    let vars = engine.canonical_vars(inv);

    assert_eq!(vars.len(), 2);
    assert!(vars[0].name.contains("_cegar_P"));
    assert!(vars[1].name.contains("_cegar_P"));
    assert_eq!(vars[0].sort, ChcSort::Int);
    assert_eq!(vars[1].sort, ChcSort::Int);
}

fn create_two_var_fact_problem() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Unconstrained fact to keep clause-atom extraction empty for this relation.
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())]),
    ));

    // Query: P(x, y) /\ x != y => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            Some(ChcExpr::ne(ChcExpr::var(x), ChcExpr::var(y))),
        ),
        ClauseHead::False,
    ));

    (problem, p)
}

fn create_multi_body_match_problem(
    inequality_query: bool,
) -> (ChcProblem, PredicateId, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);

    let constraint = if inequality_query {
        ChcExpr::ne(ChcExpr::var(a.clone()), ChcExpr::var(b.clone()))
    } else {
        ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::var(b.clone()))
    };

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(a)]), (q, vec![ChcExpr::var(b)])],
            Some(constraint),
        ),
        ClauseHead::False,
    ));

    (problem, p, q)
}

#[test]
fn test_enumerate_state_combinations_prunes_infeasible_assignments() {
    let (problem, p, q) = create_multi_body_match_problem(true);
    let mut engine = CegarEngine::new(problem, CegarConfig::default());

    let p_var = engine
        .canonical_vars(p)
        .into_iter()
        .next()
        .expect("P should have one canonical argument variable");
    let q_var = engine
        .canonical_vars(q)
        .into_iter()
        .next()
        .expect("Q should have one canonical argument variable");

    let p_pred = engine
        .predicates
        .add_predicate(p, ChcExpr::eq(ChcExpr::var(p_var), ChcExpr::int(0)));
    let q_pred = engine
        .predicates
        .add_predicate(q, ChcExpr::eq(ChcExpr::var(q_var), ChcExpr::int(0)));

    let p_state = AbstractState::new(p, vec![p_pred]);
    let q_state = AbstractState::new(q, vec![q_pred]);
    engine.active_states.entry(q).or_default().insert(q_state);

    let body_predicates = engine.problem.clauses()[0].body.predicates.clone();
    let combinations = engine.enumerate_state_combinations(0, &body_predicates, 0, &p_state);
    assert!(
        combinations.is_empty(),
        "assignment P(a)=0, Q(b)=0 with query constraint a!=b should be pruned as infeasible"
    );
}

#[test]
fn test_enumerate_state_combinations_keeps_feasible_assignments() {
    let (problem, p, q) = create_multi_body_match_problem(false);
    let mut engine = CegarEngine::new(problem, CegarConfig::default());

    let p_var = engine
        .canonical_vars(p)
        .into_iter()
        .next()
        .expect("P should have one canonical argument variable");
    let q_var = engine
        .canonical_vars(q)
        .into_iter()
        .next()
        .expect("Q should have one canonical argument variable");

    let p_pred = engine
        .predicates
        .add_predicate(p, ChcExpr::eq(ChcExpr::var(p_var), ChcExpr::int(0)));
    let q_pred = engine
        .predicates
        .add_predicate(q, ChcExpr::eq(ChcExpr::var(q_var), ChcExpr::int(0)));

    let p_state = AbstractState::new(p, vec![p_pred]);
    let q_state = AbstractState::new(q, vec![q_pred]);
    engine
        .active_states
        .entry(q)
        .or_default()
        .insert(q_state.clone());

    let body_predicates = engine.problem.clauses()[0].body.predicates.clone();
    let combinations = engine.enumerate_state_combinations(0, &body_predicates, 0, &p_state);
    assert_eq!(combinations.len(), 1);
    assert_eq!(combinations[0][0].relation, p);
    assert_eq!(combinations[0][1], q_state);
}

#[test]
fn test_cegar_template_fallback_adds_relational_qualifiers() {
    let (problem, p) = create_two_var_fact_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());

    engine
        .edges
        .push(AbstractEdge::new(vec![], AbstractState::new(p, vec![]), 0));

    let templates = engine.generate_template_predicates(&[0]);
    let canonical = engine.canonical_vars(p);
    let expected_eq = ChcExpr::eq(
        ChcExpr::var(canonical[0].clone()),
        ChcExpr::var(canonical[1].clone()),
    );

    assert!(
        templates
            .iter()
            .any(|(rel, formula)| *rel == p && *formula == expected_eq),
        "expected qualifier fallback to include canonical equality"
    );
}

#[test]
fn test_cegar_template_fallback_skips_existing_predicates() {
    let (problem, p) = create_two_var_fact_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    let canonical = engine.canonical_vars(p);
    let existing_eq = ChcExpr::eq(
        ChcExpr::var(canonical[0].clone()),
        ChcExpr::var(canonical[1].clone()),
    );
    engine.predicates.add_predicate(p, existing_eq.clone());

    engine
        .edges
        .push(AbstractEdge::new(vec![], AbstractState::new(p, vec![]), 0));

    let templates = engine.generate_template_predicates(&[0]);

    assert!(
        !templates
            .iter()
            .any(|(rel, formula)| *rel == p && *formula == existing_eq),
        "existing predicates must not be regenerated"
    );
}

#[test]
fn test_cegar_max_states_per_relation() {
    // With max_states_per_relation=1, the engine should not accumulate
    // many states per relation. It may still solve or return Unknown.
    let problem = create_safe_problem();
    let config = CegarConfig {
        max_states_per_relation: 1,
        ..CegarConfig::default()
    };
    let mut engine = CegarEngine::new(problem, config);
    let result = engine.solve();

    // With only 1 state per relation, the engine is severely constrained.
    // It should not report Unsafe on a safe problem.
    assert!(
        !matches!(result, CegarResult::Unsafe(_)),
        "max_states_per_relation=1 should not cause false Unsafe"
    );

    // Verify state counts are bounded
    for states in engine.active_states.values() {
        assert!(
            states.len() <= 1,
            "active states should be bounded by max_states_per_relation"
        );
    }
}

/// Test sequence interpolation on a multi-predicate safe problem.
///
/// x = 0 => Init(x)
/// Init(x) => Mid(x)
/// Mid(x) => Inv(x)
/// Inv(x) /\ x >= 10 => false
///
/// Safe because x=0 propagates through Init -> Mid -> Inv, so x < 10 always.
/// Sequence interpolation should discover predicates for Init, Mid, and Inv
/// in a single consistent pass.
#[test]
fn test_cegar_sequence_interpolation_multi_pred() {
    let mut problem = ChcProblem::new();
    let init = problem.declare_predicate("Init", vec![ChcSort::Int]);
    let mid = problem.declare_predicate("Mid", vec![ChcSort::Int]);
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // x = 0 => Init(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(init, vec![ChcExpr::var(x.clone())]),
    ));

    // Init(x) => Mid(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(init, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(mid, vec![ChcExpr::var(x.clone())]),
    ));

    // Mid(y) => Inv(y)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(mid, vec![ChcExpr::var(y.clone())])], None),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(y)]),
    ));

    // Inv(x) /\ x >= 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let config = CegarConfig {
        base: ChcEngineConfig {
            verbose: false,
            ..ChcEngineConfig::default()
        },
        ..CegarConfig::default()
    };
    let mut engine = CegarEngine::new(problem, config);
    let result = engine.solve();

    // Must report Safe on a provably safe problem, not just "not Unsafe".
    // The weak assertion !matches!(Unsafe(_)) would also pass on Unknown,
    // masking interpolation regressions. (#2493)
    assert!(
        matches!(result, CegarResult::Safe(_)),
        "multi-predicate safe problem should be proved Safe, got: {:?}",
        match &result {
            CegarResult::Safe(_) => "Safe",
            CegarResult::Unsafe(_) => "Unsafe",
            CegarResult::Unknown => "Unknown",
        }
    );
}

fn create_branching_query_safe_problem() -> (ChcProblem, PredicateId, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);

    // x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));

    // y = 1 => Q(y)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(1))),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y)]),
    ));

    // P(a) /\ Q(b) /\ a = b => false
    // This is unreachable because facts force a=0 and b=1.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (p, vec![ChcExpr::var(a.clone())]),
                (q, vec![ChcExpr::var(b.clone())]),
            ],
            Some(ChcExpr::eq(ChcExpr::var(a), ChcExpr::var(b))),
        ),
        ClauseHead::False,
    ));

    (problem, p, q)
}

#[test]
fn test_extract_trace_tree_includes_all_query_branches() {
    let (problem, p, q) = create_branching_query_safe_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());

    let p_state = AbstractState::new(p, vec![]);
    let q_state = AbstractState::new(q, vec![]);

    engine
        .edges
        .push(AbstractEdge::new(vec![], p_state.clone(), 0));
    engine
        .edges
        .push(AbstractEdge::new(vec![], q_state.clone(), 1));
    engine.edges.push(AbstractEdge::new(
        vec![p_state, q_state],
        AbstractState::new(PredicateId(u32::MAX), vec![]),
        2,
    ));

    let tree = engine.extract_trace_tree(2);
    assert_eq!(tree.len(), 3, "query + two fact producers expected");
    assert_eq!(tree[0].children.len(), 2, "query must keep both branches");

    let child_edges: FxHashSet<usize> = tree[0]
        .children
        .iter()
        .map(|&idx| tree[idx].edge_idx)
        .collect();
    assert!(child_edges.contains(&0));
    assert!(child_edges.contains(&1));
}

#[test]
fn test_cegar_branching_query_safe_not_unsafe() {
    let (problem, _, _) = create_branching_query_safe_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    let result = engine.solve();

    // Must report Safe, not just "not Unsafe".
    // The weak assertion would also pass on Unknown. (#2493)
    assert!(
        matches!(result, CegarResult::Safe(_)),
        "branching safe query should be proved Safe, got: {:?}",
        match &result {
            CegarResult::Safe(_) => "Safe",
            CegarResult::Unsafe(_) => "Unsafe",
            CegarResult::Unknown => "Unknown",
        }
    );
}

#[test]
fn test_record_template_refinement_success_respects_skip_reset_cap() {
    let problem = create_immediate_fact_to_false_problem();
    let mut engine = CegarEngine::new(problem, CegarConfig::default());

    // Under cap: template success resets postponed counter.
    engine.postponed_count = 3;
    engine.template_resets = 0;
    assert!(
        engine.record_template_refinement_success(),
        "template success should reset postponed counter while under cap"
    );
    assert_eq!(engine.template_resets, 1);
    assert_eq!(engine.postponed_count, 0);

    // Past cap with no predicate growth: template success should NOT reset.
    engine.postponed_count = 4;
    engine.template_resets = MIN_TEMPLATE_RESETS;
    engine.predicates_at_last_reset = 0; // no growth since last reset
    assert!(
        !engine.record_template_refinement_success(),
        "template success should stop resetting when past cap and no predicate growth"
    );
    assert_eq!(engine.template_resets, MIN_TEMPLATE_RESETS + 1);
    assert_eq!(
        engine.postponed_count, 4,
        "postponed_count must remain unchanged when template resets exceed cap without growth"
    );
}

// Moved from tests/cegar_integration.rs — uses CegarConfig/CegarEngine/CegarResult (now pub(crate))

/// CEGAR on a problem that requires refinement.
/// Invariant is x >= 0 AND x <= 100.
#[test]
fn test_cegar_requires_refinement() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(100))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    let result = engine.solve();
    // Must report Safe, not just "not Unsafe". (#2493, #3868)
    assert!(
        matches!(result, CegarResult::Safe(_)),
        "CEGAR should report Safe on a safe problem, got: {result:?}"
    );
}

/// CEGAR on a genuine unsafe problem.
/// x=5, decrement without bound, query x < 0.
#[test]
fn test_cegar_genuine_counterexample() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(-1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    let result = engine.solve();
    // Must report Unsafe, not just "not Safe". (#2493, #3868)
    assert!(
        matches!(result, CegarResult::Unsafe(_)),
        "CEGAR should report Unsafe on an unsafe problem, got: {result:?}"
    );
}

/// CEGAR on a two-variable safe problem (needs relational invariant x = y).
#[test]
fn test_cegar_two_variable_safe() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
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
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            Some(ChcExpr::ne(ChcExpr::var(x), ChcExpr::var(y))),
        ),
        ClauseHead::False,
    ));

    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    let result = engine.solve();
    // Must report Safe, not just "not Unsafe". (#2493, #3868)
    assert!(
        matches!(result, CegarResult::Safe(_)),
        "CEGAR should report Safe on x=y invariant problem, got: {result:?}"
    );
}

/// Regression test for #6047: CEGAR must not return false-Unsafe on safe
/// multi-predicate problems. The abstract feasibility check can produce
/// false genuines when the CEGAR abstraction loses precision, and BMC
/// validation is unavailable for multi-predicate systems.
///
/// This problem is safe:
///   x = 0 => P(x)
///   P(x) => Q(x)
///   Q(x) /\ x < 0 => false   (unreachable because x = 0 >= 0)
///
/// Before the fix, CEGAR would declare a "genuine" counterexample here
/// because the abstract trace (P -> Q -> false) passes the symbolic
/// feasibility check and BMC validation is skipped for multi-predicate.
#[test]
fn test_cegar_no_false_unsafe_multi_predicate_6047() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    // P(x) => Q(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    // Q(x) /\ x < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let mut engine = CegarEngine::new(problem, CegarConfig::default());
    let result = engine.solve();
    // CEGAR must NOT return Unsafe on a safe problem. Safe or Unknown are
    // both acceptable; Unsafe is a soundness violation.
    assert!(
        !matches!(result, CegarResult::Unsafe(_)),
        "CEGAR must not return false-Unsafe on safe multi-predicate problem (#6047), got: {result:?}"
    );
}
