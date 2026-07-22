// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the TRL engine.

#![allow(clippy::unwrap_used)]

use super::*;
use crate::smt::{SmtContext, SmtResult};
use crate::{ChcOp, PredicateId};

fn make_simple_ts() -> TransitionSystem {
    // Simple counter: x starts at 0, increments, query is x >= 10
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        // init: x = 0
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        // trans: x_next = x + 1
        ChcExpr::eq(
            ChcExpr::var(x_next),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
        // query: x >= 10
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10)),
    )
}

#[test]
fn test_trl_chain_formulas_composes_state_vars() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let solver = TrlSolver::new(ts, config);

    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    let fst = ChcExpr::eq(
        ChcExpr::var(x_next.clone()),
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
    );
    let snd = ChcExpr::eq(
        ChcExpr::var(x_next),
        ChcExpr::add(ChcExpr::var(x), ChcExpr::int(2)),
    );

    let (chained, _sigma1, _sigma2, _fst_vars, _snd_vars) = solver.chain_formulas(&fst, &snd);
    let vars = chained.vars();

    let var_names: FxHashSet<_> = vars.iter().map(|v| v.name.as_str()).collect();
    assert!(var_names.contains("x"));
    assert!(var_names.contains("x_next"));

    let chain_vars: Vec<_> = vars
        .iter()
        .filter(|v| v.name.starts_with("__trl_chain_x"))
        .collect();
    assert_eq!(
        chain_vars.len(),
        1,
        "Expected exactly one chained state var"
    );

    // x=0, intermediate=1, x_next=3 satisfies:
    //  (__trl_chain_x_0 = x + 1) AND (x_next = __trl_chain_x_0 + 2)
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert(chain_vars[0].name.clone(), SmtValue::Int(1));
    model.insert("x_next".to_string(), SmtValue::Int(3));

    assert_eq!(solver.mbp.eval_bool(&chained, &model), Some(true));
}

#[test]
fn test_trl_chain_formulas_renames_colliding_temp_vars() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let solver = TrlSolver::new(ts, config);

    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    let trace_id = ChcVar::new("trace_id", ChcSort::Int);

    let fst = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(trace_id.clone()), ChcExpr::int(0)),
        ChcExpr::eq(
            ChcExpr::var(x_next.clone()),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
    );
    let snd = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(trace_id), ChcExpr::int(1)),
        ChcExpr::eq(
            ChcExpr::var(x_next),
            ChcExpr::add(ChcExpr::var(x), ChcExpr::int(2)),
        ),
    );

    let (chained, _sigma1, _sigma2, _fst_vars, _snd_vars) = solver.chain_formulas(&fst, &snd);
    let vars = chained.vars();

    assert!(vars.iter().any(|v| v.name == "trace_id"));
    assert!(vars
        .iter()
        .any(|v| v.name.starts_with("__trl_chain_tmp_trace_id")));
}

#[test]
fn test_trl_compress_two_step_loop_is_sat() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let mut solver = TrlSolver::new(ts, config);

    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    let trace_id = ChcVar::new("trace_id", ChcSort::Int);

    // Step 0: trace_id = 0 AND x_next = x + 1
    let step0 = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(trace_id.clone()), ChcExpr::int(0)),
        ChcExpr::eq(
            ChcExpr::var(x_next.clone()),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
    );
    let id0 = solver.trace.graph.intern(step0);
    let mut m0 = FxHashMap::default();
    m0.insert("x".to_string(), SmtValue::Int(0));
    m0.insert("x_next".to_string(), SmtValue::Int(1));
    m0.insert("trace_id".to_string(), SmtValue::Int(0));
    solver.trace.push(TraceElement {
        _transition_id: 0,
        implicant_id: id0,
        model: m0,
    });

    // Step 1: trace_id = 1 AND x_next = x + 2
    let step1 = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(trace_id), ChcExpr::int(1)),
        ChcExpr::eq(
            ChcExpr::var(x_next),
            ChcExpr::add(ChcExpr::var(x), ChcExpr::int(2)),
        ),
    );
    let id1 = solver.trace.graph.intern(step1);
    let mut m1 = FxHashMap::default();
    m1.insert("x".to_string(), SmtValue::Int(1));
    m1.insert("x_next".to_string(), SmtValue::Int(3));
    m1.insert("trace_id".to_string(), SmtValue::Int(1));
    solver.trace.push(TraceElement {
        _transition_id: 1,
        implicant_id: id1,
        model: m1,
    });

    let (compressed, model) = solver.compress(0, 1);
    assert_eq!(solver.mbp.eval_bool(&compressed, &model), Some(true));

    let mut smt = SmtContext::new();
    assert!(matches!(smt.check_sat(&compressed), SmtResult::Sat(_)));

    // Regression: naive conjunction without composition is unsat:
    //  (x_next = x + 1) AND (x_next = x + 2)
    let naive = ChcExpr::and_all(vec![
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
            ChcExpr::add(
                ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
                ChcExpr::int(1),
            ),
        ),
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
            ChcExpr::add(
                ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
                ChcExpr::int(2),
            ),
        ),
    ]);
    let mut smt = SmtContext::new();
    assert!(matches!(
        smt.check_sat(&naive),
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    ));

    // Specialized formula should eliminate chaining intermediates and trace_id.
    let (specialized, _model) = solver.specialize(0, 1, |v| solver.is_temp_var(v));
    let specialized_vars = specialized.vars();
    assert!(
        !specialized_vars
            .iter()
            .any(|v| v.name.starts_with("__trl_chain")),
        "specialize should eliminate chaining intermediates"
    );
    assert!(
        specialized_vars.iter().all(|v| !solver.is_temp_var(v)),
        "specialize should eliminate all temp vars: {specialized_vars:?}"
    );
}

#[test]
fn test_trl_config_default() {
    let config = TrlConfig::default();
    assert_eq!(config.max_depth, 1000);
    assert_eq!(config.max_iterations, 10000);
    assert!(!config.base.verbose);
    assert!(config.base.cancellation_token.is_none());
}

#[test]
fn test_trl_solver_creation() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let solver = TrlSolver::new(ts, config);

    // Should have one learned relation (the original transition)
    assert_eq!(solver.learned.len(), 1);
    assert!(solver.blocked.is_empty());
}

// test_trl_build_invariant_model_populates_predicate removed:
// TRL no longer returns Safe (#5379 soundness fix), so build_invariant_model
// is dead code. The diameter proof was unsound (blocking clauses in solver).

#[test]
fn test_trl_has_covering_relation_skips_original_for_self_loops() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let solver = TrlSolver::new(ts, config);

    // Model satisfying the original transition.
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("x_next".to_string(), SmtValue::Int(1));
    assert_eq!(solver.mbp.eval_bool(&solver.learned[0], &model), Some(true));

    // For self-loops, we must not "cover" using the original transition (id 0),
    // since it would yield a useless blocking clause (matches LoAT).
    assert_eq!(solver.has_covering_relation(1, &model), None);
}

#[test]
fn test_trl_has_covering_relation_allows_original_for_non_self_loops() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let solver = TrlSolver::new(ts, config);

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("x_next".to_string(), SmtValue::Int(1));

    assert_eq!(solver.has_covering_relation(2, &model), Some(0));
}

#[test]
fn test_trl_has_covering_relation_prefers_newest() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let mut solver = TrlSolver::new(ts, config);

    // Add a duplicate learned relation (id 1) that is also satisfied by the model.
    solver.learned.push(solver.learned[0].clone());

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("x_next".to_string(), SmtValue::Int(1));

    // Self-loop: skip id 0 but accept id 1.
    assert_eq!(solver.has_covering_relation(1, &model), Some(1));
    // Non-self-loop: both cover; pick the newest to strengthen blocking.
    assert_eq!(solver.has_covering_relation(2, &model), Some(1));
}

#[test]
fn test_trl_has_covering_relation_injects_trp_n() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let mut solver = TrlSolver::new(ts, config);

    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    let n = ChcVar::new(TRP_N_VAR_NAME, ChcSort::Int);
    solver.learned.push(ChcExpr::eq(
        ChcExpr::var(x_next),
        ChcExpr::add(ChcExpr::var(x), ChcExpr::var(n)),
    ));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("x_next".to_string(), SmtValue::Int(1));
    assert_eq!(solver.mbp.eval_bool(&solver.learned[1], &model), None);

    // Coverage should succeed by evaluating with `__trp_n = 1`.
    assert_eq!(solver.has_covering_relation(1, &model), Some(1));
}

#[test]
fn test_trl_self_loop_saturation_streak_trips() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let mut solver = TrlSolver::new(ts, config);

    let mut streak = 0;
    for _ in 0..=TRL_SELF_LOOP_SATURATION_LIMIT {
        streak = solver.record_loop_streak(0, 0);
    }
    assert_eq!(streak, TRL_SELF_LOOP_SATURATION_LIMIT + 1);

    // Different loop resets streak.
    assert_eq!(solver.record_loop_streak(1, 1), 1);
    assert_eq!(solver.record_loop_streak(1, 1), 2);
}

#[test]
fn test_trl_handle_loop_uses_coverage_instead_of_learning() {
    // Self-loop system: x_next = x
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(x_next.clone()), ChcExpr::var(x.clone())),
        ChcExpr::Bool(false),
    );

    let config = TrlConfig::default();
    let mut solver = TrlSolver::new(ts, config);

    // Inject a learned relation that already covers the loop model (id 1).
    solver.learned.push(solver.learned[0].clone());

    // Build a trace with two identical steps so the dependency graph contains an (id,id) edge,
    // which will be detected as a 0->0 self-loop.
    let trace_id = ChcVar::new("trace_id", ChcSort::Int);
    let step = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(trace_id), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(x_next), ChcExpr::var(x)),
    );

    let implicant_id = solver.trace.graph.intern(step);
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("x_next".to_string(), SmtValue::Int(0));
    model.insert("trace_id".to_string(), SmtValue::Int(0));

    solver.trace.push(TraceElement {
        _transition_id: 0,
        implicant_id,
        model: model.clone(),
    });
    solver.trace.push(TraceElement {
        _transition_id: 0,
        implicant_id,
        model,
    });

    assert_eq!(solver.trace.find_looping_infix(), Some((0, 0)));

    assert!(solver.handle_loop(0, 0));

    // Coverage should prevent unbounded growth of learned relations.
    assert_eq!(solver.learned.len(), 2);
    assert!(solver.blocked.get(&1).is_some_and(|m| m.contains_key(&1)));
}

#[test]
fn test_trl_build_step_formula() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let solver = TrlSolver::new(ts, config);

    // Build step formula for step 0
    let formula = solver.build_step_formula(0);

    // Should be a conjunction (trace_id = 0) AND transition
    assert!(matches!(formula, ChcExpr::Op(ChcOp::And, _)));
}

#[test]
fn test_trl_version_transition() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let solver = TrlSolver::new(ts, config);

    // Version transition from 0 to 1
    let trans = &solver.learned[0];
    let versioned = solver.version_transition(trans, 0, 1);

    // Result should reference x (at time 0) and x_1 (at time 1)
    let vars = versioned.vars();
    let var_names: FxHashSet<_> = vars.iter().map(|v| v.name.as_str()).collect();
    assert!(var_names.contains("x"));
    assert!(var_names.contains("x_1"));
}

#[test]
fn test_trl_replays_unsafe_depth_with_concrete_assignments() {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(x_next), ChcExpr::int(1)),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1)),
    );
    let config = TrlConfig {
        max_depth: 4,
        max_iterations: 8,
        ..TrlConfig::default()
    };
    let mut solver = TrlSolver::new(ts, config);

    let result = solver.solve();
    match result {
        ChcEngineResult::Unsafe(cex) => {
            assert_eq!(
                cex.steps.len(),
                2,
                "one-step unsafe system should produce a depth-1 counterexample"
            );
            assert_eq!(
                cex.steps[0].assignments.get("x"),
                Some(&0),
                "replayed witness should include init-state assignments",
            );
            assert_eq!(
                cex.steps[1].assignments.get("x"),
                Some(&1),
                "replayed witness should include bad-state assignments",
            );
        }
        other => panic!("expected Unsafe for simple counter, got {other:?}"),
    }
}

#[test]
fn test_trl_replay_unsafe_depth_reports_spurious_for_unreachable_query() {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(x_next), ChcExpr::int(1)),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(10)),
    );
    let solver = TrlSolver::new(ts, TrlConfig::default());

    assert!(
        matches!(solver.replay_unsafe_depth(1), UnsafeReplayResult::Spurious),
        "unreachable exact-depth replay must be classified as spurious, not inconclusive",
    );
}

#[test]
fn test_trl_finite_system_safe() {
    // A finite system with bounded transitions should be provable safe
    // x starts at 0, goes to 1, then stays at 1
    // query: x >= 10 (never reachable)
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        // init: x = 0
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        // trans: if x < 1 then x_next = x + 1 else x_next = x
        // Simplified: x_next = min(x + 1, 1)
        // Using: (x < 1 => x_next = x + 1) AND (x >= 1 => x_next = x)
        ChcExpr::and(
            ChcExpr::or(
                ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ChcExpr::eq(
                    ChcExpr::var(x_next.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ),
            ),
            ChcExpr::or(
                ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ChcExpr::eq(ChcExpr::var(x_next), ChcExpr::var(x.clone())),
            ),
        ),
        // query: x >= 10 (never reachable since x maxes at 1)
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10)),
    );

    let config = TrlConfig {
        max_depth: 20,
        max_iterations: 100,
        ..TrlConfig::default()
    };
    let mut solver = TrlSolver::new(ts, config);
    let result = solver.solve();

    // After #7384 soundness fix, TRL only synthesizes Safe when diameter is
    // Confirmed (no paths exist even without blocking clauses). For systems
    // with self-loops (like this one where x stays at 1 forever), the diameter
    // is always Spurious because arbitrary-length paths exist. TRL correctly
    // returns Unknown in this case; the portfolio validation layer handles
    // Safe verification. Safe is still acceptable if the inner PDR/Kind solver
    // on the expanded system happens to prove it within the depth where
    // diameter is confirmed.
    match result {
        ChcEngineResult::Safe(model) => {
            assert!(
                !model.is_empty(),
                "TRL safe path must synthesize a non-empty model",
            );
        }
        ChcEngineResult::Unknown => {
            // Expected after #7384: TRL cannot confirm diameter for
            // self-looping systems, so it conservatively returns Unknown.
        }
        other => panic!("expected Safe or Unknown for bounded finite system, got {other:?}"),
    }
}

#[test]
fn test_trl_self_loop_blocking_clause_allows_any_learned_relation() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let mut solver = TrlSolver::new(ts, config);

    solver.learned.push(ChcExpr::Bool(true));
    solver.learned.push(ChcExpr::Bool(true));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("trace_id".to_string(), SmtValue::Int(1));

    let clause = solver.compute_blocking_clause(0, 1, 2, &solver.learned[2], &model);
    assert_eq!(
        solver.mbp.eval_bool(&clause, &model),
        Some(true),
        "self-loop blocking must accept any learned relation via trace_id >= 1",
    );
}

#[test]
fn test_trl_blocking_clause_projects_learned_relation_not_loop_body() {
    let ts = make_simple_ts();
    let config = TrlConfig::default();
    let solver = TrlSolver::new(ts, config);

    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    let loop_body = ChcExpr::eq(
        ChcExpr::var(x_next),
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
    );
    let learned_relation = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("x_next".to_string(), SmtValue::Int(1));

    let clause = solver.compute_blocking_clause(0, 2, 0, &learned_relation, &model);
    let vars = clause.vars();
    assert!(
        !vars.iter().any(|var| var.name == "x_next"),
        "blocking clause must be projected from the learned relation, not the raw loop body: {loop_body:?} -> {clause:?}",
    );
}

/// Integration test: TRP uses recurrence analysis to compute transitive projection.
///
/// This test exercises the integration between TRP and `analyze_transition`,
/// verifying that constant delta patterns are correctly identified and
/// transitive projections are computed.
#[test]
fn test_trp_recurrence_analyzer_integration() {
    use crate::trp::Trp;

    // Loop: x' = x + 1 (constant delta)
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    let loop_body = ChcExpr::eq(
        ChcExpr::var(x_next),
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
    );

    // Create TRP with x as state variable
    let trp = Trp::new(vec![x]);

    // Create model where x=0, x_next=1
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("x_next".to_string(), SmtValue::Int(1));

    // Compute transitive projection
    let result = trp.compute(&loop_body, &model);

    // Should produce some projection (not None)
    assert!(
        result.is_some(),
        "TRP should produce a transitive projection"
    );

    // The projection should capture the recurrence pattern
    let projection = result.unwrap();

    // Verify the projection includes the iteration variable (__trp_n)
    let projection_vars = projection.vars();
    let has_n = projection_vars.iter().any(|v| v.name == "__trp_n");

    // TRP produces n-dependent constraints for non-trivial recurrences
    // The result should reference n_var if recurrence analysis was applied
    assert!(
        has_n || !matches!(projection, ChcExpr::Bool(true)),
        "TRP should produce meaningful constraints: {projection:?}"
    );
}

/// Integration test: TRL solver with TRP on a bounded loop.
///
/// Verifies that TRL can leverage TRP to reason about loops that require
/// recurrence analysis to prove safe.
#[test]
fn test_trl_with_trp_bounded_loop() {
    // Loop: x starts at 0, increments by 1, guard x < 5
    // Query: x >= 100 (unreachable)
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        // init: x = 0
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        // trans: x < 5 AND x_next = x + 1
        ChcExpr::and(
            ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5)),
            ChcExpr::eq(
                ChcExpr::var(x_next),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            ),
        ),
        // query: x >= 100 (never reachable since x < 5)
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(100)),
    );

    let config = TrlConfig {
        max_depth: 20,
        max_iterations: 100,
        ..TrlConfig::default()
    };
    let mut solver = TrlSolver::new(ts, config);
    let result = solver.solve();

    // Should prove safe (loop is bounded and cannot reach x >= 100)
    // or Unknown if learning fails (acceptable since TRL is iterative)
    assert!(
        matches!(result, ChcEngineResult::Safe(_) | ChcEngineResult::Unknown),
        "TRL should prove safe or return unknown: {result:?}"
    );
}

// ====================================================================
// Replacement invariant tests for tautological Kani harnesses deleted
// from trl/verification.rs (P1 formal_proofs audit).
// These exercise real AY Trace/DependencyGraph code.
// ====================================================================

use crate::trace::{DependencyGraph, Trace, TraceElement};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Helper: create a TraceElement with given transition_id and implicant.
fn make_trace_element(
    graph: &mut DependencyGraph,
    transition_id: i128,
    expr: ChcExpr,
) -> TraceElement {
    let implicant_id = graph.intern(expr);
    TraceElement {
        _transition_id: transition_id,
        implicant_id,
        model: FxHashMap::default(),
    }
}

/// Replaces tautological proof_loop_detection_correct.
/// Verifies find_looping_infix prefers shorter infixes when multiple loops exist.
#[test]
fn test_loop_detection_prefers_shorter_infix() {
    let mut trace = Trace::new();

    let a = ChcExpr::Bool(true);
    let b = ChcExpr::Var(ChcVar::new("b", ChcSort::Bool));
    let c = ChcExpr::Var(ChcVar::new("c", ChcSort::Bool));

    let elem_a = make_trace_element(&mut trace.graph, 0, a);
    let elem_b = make_trace_element(&mut trace.graph, 0, b);
    let elem_c = make_trace_element(&mut trace.graph, 0, c);

    let id_b = elem_b.implicant_id;

    trace.push(elem_a);
    trace.push(elem_b);
    trace.push(elem_c);

    let id_a = trace.elements[0].implicant_id;
    let id_c = trace.elements[2].implicant_id;
    trace.graph.add_edge(id_c, id_a);
    trace.graph.add_edge(id_b, id_b);

    let result = trace.find_looping_infix();
    assert!(result.is_some(), "Should find a loop");
    let (start, end) = result.unwrap();
    assert_eq!(start, end, "Shorter (length-0) infix should be preferred");
    assert_eq!(start, 1, "B is at index 1");
}

/// Replaces tautological proof_backtrack_preserves_invariant.
/// Verifies forward-only traces (no back-edges) return None.
#[test]
fn test_loop_detection_no_false_positives_on_forward_trace() {
    let mut trace = Trace::new();

    let exprs: Vec<ChcExpr> = (0..4)
        .map(|i| ChcExpr::Var(ChcVar::new(&format!("v{i}"), ChcSort::Bool)))
        .collect();

    for (i, expr) in exprs.into_iter().enumerate() {
        let elem = make_trace_element(&mut trace.graph, i as i128, expr);
        trace.push(elem);
    }

    let result = trace.find_looping_infix();
    assert!(
        result.is_none(),
        "Forward-only trace must not report a loop"
    );
}

/// Replaces tautological proof_loop_detection_correct + proof_trace_id_bounds.
/// Verifies returned indices satisfy start<=end, valid bounds, and back-edge exists.
#[test]
fn test_loop_detection_result_indices_valid() {
    let mut trace = Trace::new();

    let a = ChcExpr::Var(ChcVar::new("a", ChcSort::Bool));
    let b = ChcExpr::Var(ChcVar::new("b", ChcSort::Bool));

    let elem_a = make_trace_element(&mut trace.graph, 0, a);
    let elem_b = make_trace_element(&mut trace.graph, 1, b);

    let id_a = elem_a.implicant_id;
    let id_b = elem_b.implicant_id;

    trace.push(elem_a);
    trace.push(elem_b);

    trace.graph.add_edge(id_b, id_a);

    let (start, end) = trace.find_looping_infix().expect("Should find loop");

    assert!(start <= end, "start must be <= end");
    assert!(start < trace.len(), "start must be in bounds");
    assert!(end < trace.len(), "end must be in bounds");
    assert!(
        trace.graph.has_edge(
            trace.elements[end].implicant_id,
            trace.elements[start].implicant_id
        ),
        "Back-edge must exist for reported loop"
    );
}

/// Replaces tautological proof_learned_relations_monotonic.
/// Verifies trace.clear() preserves graph nodes and edges.
#[test]
fn test_trace_clear_preserves_all_graph_state() {
    let mut trace = Trace::new();

    let a = ChcExpr::Var(ChcVar::new("a", ChcSort::Bool));
    let b = ChcExpr::Var(ChcVar::new("b", ChcSort::Bool));

    let elem_a = make_trace_element(&mut trace.graph, 0, a);
    let elem_b = make_trace_element(&mut trace.graph, 1, b);

    let id_a = elem_a.implicant_id;
    let id_b = elem_b.implicant_id;

    trace.push(elem_a);
    trace.push(elem_b);

    let nodes_before = trace.graph.num_nodes();
    let edges_before = trace.graph.num_edges();
    assert!(nodes_before >= 2);
    assert!(edges_before >= 1);

    trace.clear();

    assert!(trace.is_empty());
    assert_eq!(trace.graph.num_nodes(), nodes_before);
    assert_eq!(trace.graph.num_edges(), edges_before);
    assert!(trace.graph.has_edge(id_a, id_b));
}

/// Replaces tautological proof_blocking_clause_depth_valid.
/// Verifies that interning the same expression returns the same ID.
#[test]
fn test_graph_intern_idempotent() {
    let mut graph = DependencyGraph::new();

    let expr = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));

    let id1 = graph.intern(expr.clone());
    let id2 = graph.intern(expr);

    assert_eq!(id1, id2, "Same expression must get the same ID");
    assert_eq!(
        graph.num_nodes(),
        1,
        "Duplicate intern must not create new node"
    );

    let other = ChcExpr::Var(ChcVar::new("y", ChcSort::Int));
    let id3 = graph.intern(other);
    assert_ne!(id1, id3, "Different expressions must get different IDs");
    assert_eq!(graph.num_nodes(), 2, "Two distinct expressions = two nodes");
}
