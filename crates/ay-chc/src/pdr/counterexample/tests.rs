// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::pdr::ChcReplayObligationKind;
use crate::predicate::PredicateId;
use crate::ChcParser;

fn pred(id: u32) -> PredicateId {
    PredicateId::new(id)
}

fn make_state(val: i128) -> ChcExpr {
    ChcExpr::Op(
        crate::ChcOp::Eq,
        vec![
            std::sync::Arc::new(ChcExpr::Var(crate::ChcVar::new("x", crate::ChcSort::Int))),
            std::sync::Arc::new(ChcExpr::Int(val)),
        ],
    )
}

#[test]
fn witness_builder_node_creates_entry() {
    let mut wb = WitnessBuilder::default();
    let state = make_state(42);
    let idx = wb.node(pred(0), 0, &state, None);
    assert_eq!(idx, 0);
    assert_eq!(wb.entries.len(), 1);
    assert_eq!(wb.entries[0].predicate, pred(0));
    assert_eq!(wb.entries[0].level, 0);
    assert_eq!(wb.entries[0].state, state);
    assert!(wb.entries[0].instances.is_empty());
}

#[test]
fn witness_builder_node_deduplicates_same_state() {
    let mut wb = WitnessBuilder::default();
    let state = make_state(10);
    let idx1 = wb.node(pred(0), 1, &state, None);
    let idx2 = wb.node(pred(0), 1, &state, None);
    assert_eq!(
        idx1, idx2,
        "same (pred, level, state) should return same index"
    );
    assert_eq!(wb.entries.len(), 1, "should not create duplicate entry");
}

#[test]
fn witness_builder_node_updates_instances_on_dedup() {
    let mut wb = WitnessBuilder::default();
    let state = make_state(5);

    // First call without instances
    let idx1 = wb.node(pred(0), 0, &state, None);
    assert!(wb.entries[idx1].instances.is_empty());

    // Second call with instances -- should update
    let mut instances = FxHashMap::default();
    instances.insert("x".to_string(), SmtValue::Int(5));
    let idx2 = wb.node(pred(0), 0, &state, Some(&instances));
    assert_eq!(idx1, idx2);
    assert_eq!(
        wb.entries[idx1].instances.get("x"),
        Some(&SmtValue::Int(5)),
        "dedup should update empty instances"
    );
}

#[test]
fn witness_builder_node_does_not_overwrite_existing_instances() {
    let mut wb = WitnessBuilder::default();
    let state = make_state(7);

    let mut first = FxHashMap::default();
    first.insert("x".to_string(), SmtValue::Int(7));
    let idx1 = wb.node(pred(0), 0, &state, Some(&first));

    // Second call with different instances -- should NOT overwrite
    let mut second = FxHashMap::default();
    second.insert("x".to_string(), SmtValue::Int(999));
    let idx2 = wb.node(pred(0), 0, &state, Some(&second));
    assert_eq!(idx1, idx2);
    assert_eq!(
        wb.entries[idx1].instances.get("x"),
        Some(&SmtValue::Int(7)),
        "non-empty instances must not be overwritten"
    );
}

#[test]
fn witness_builder_different_predicates_are_distinct() {
    let mut wb = WitnessBuilder::default();
    let state = make_state(1);
    let idx0 = wb.node(pred(0), 0, &state, None);
    let idx1 = wb.node(pred(1), 0, &state, None);
    assert_ne!(
        idx0, idx1,
        "different predicates must produce different entries"
    );
    assert_eq!(wb.entries.len(), 2);
}

#[test]
fn witness_builder_different_levels_are_distinct() {
    let mut wb = WitnessBuilder::default();
    let state = make_state(1);
    let idx0 = wb.node(pred(0), 0, &state, None);
    let idx1 = wb.node(pred(0), 1, &state, None);
    assert_ne!(
        idx0, idx1,
        "different levels must produce different entries"
    );
    assert_eq!(wb.entries.len(), 2);
}

#[test]
fn witness_builder_different_states_are_distinct() {
    let mut wb = WitnessBuilder::default();
    let s1 = make_state(1);
    let s2 = make_state(2);
    let idx0 = wb.node(pred(0), 0, &s1, None);
    let idx1 = wb.node(pred(0), 0, &s2, None);
    assert_ne!(
        idx0, idx1,
        "different states must produce different entries"
    );
    assert_eq!(wb.entries.len(), 2);
}

#[test]
fn witness_builder_set_derivation_basic() {
    let mut wb = WitnessBuilder::default();
    let s0 = make_state(0);
    let s1 = make_state(1);
    let premise_idx = wb.node(pred(0), 0, &s0, None);
    let head_idx = wb.node(pred(0), 1, &s1, None);

    wb.set_derivation(head_idx, 42, vec![premise_idx]);

    assert_eq!(wb.entries[head_idx].incoming_clause, Some(42));
    assert_eq!(wb.entries[head_idx].premises, vec![premise_idx]);
}

#[test]
fn witness_builder_set_derivation_idempotent() {
    let mut wb = WitnessBuilder::default();
    let s0 = make_state(0);
    let s1 = make_state(1);
    let premise_idx = wb.node(pred(0), 0, &s0, None);
    let head_idx = wb.node(pred(0), 1, &s1, None);

    wb.set_derivation(head_idx, 42, vec![premise_idx]);
    // Second call should not overwrite
    wb.set_derivation(head_idx, 99, vec![]);

    assert_eq!(
        wb.entries[head_idx].incoming_clause,
        Some(42),
        "first set_derivation must win"
    );
    assert_eq!(
        wb.entries[head_idx].premises,
        vec![premise_idx],
        "first set_derivation premises must persist"
    );
}

#[test]
fn witness_builder_multi_step_derivation_dag() {
    // Build a 3-node derivation: init -> mid -> bad
    let mut wb = WitnessBuilder::default();
    let init_state = make_state(0);
    let mid_state = make_state(5);
    let bad_state = make_state(10);

    let init_idx = wb.node(pred(0), 0, &init_state, None);
    let mid_idx = wb.node(pred(0), 1, &mid_state, None);
    let bad_idx = wb.node(pred(0), 2, &bad_state, None);

    wb.set_derivation(mid_idx, 0, vec![init_idx]);
    wb.set_derivation(bad_idx, 1, vec![mid_idx]);

    assert_eq!(wb.entries.len(), 3);
    // Verify DAG structure
    assert!(
        wb.entries[init_idx].premises.is_empty(),
        "init has no premises"
    );
    assert_eq!(wb.entries[mid_idx].premises, vec![init_idx]);
    assert_eq!(wb.entries[bad_idx].premises, vec![mid_idx]);
    assert_eq!(wb.entries[mid_idx].incoming_clause, Some(0));
    assert_eq!(wb.entries[bad_idx].incoming_clause, Some(1));
}

#[test]
fn trace_validity_replay_obligation_binds_concrete_unsafe_trace() {
    let problem = ChcParser::parse(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#,
    )
    .expect("parse unsafe trace fixture");
    let predicate = problem.predicates()[0].id;
    let cex = Counterexample::new(vec![
        CounterexampleStep::new(predicate, [("x".to_string(), 0)].into_iter().collect()),
        CounterexampleStep::new(predicate, [("x".to_string(), 1)].into_iter().collect()),
    ]);

    let obligations = cex
        .trace_validity_replay_obligations(&problem)
        .expect("concrete single-predicate trace should export");

    assert_eq!(obligations.len(), 1);
    assert_eq!(obligations[0].kind, ChcReplayObligationKind::TraceValidity);
    assert!(obligations[0].name.contains("trace-validity"));
    assert!(
        obligations[0].smtlib.contains("; expected-result: sat"),
        "trace-validity replay should record the expected SAT verdict: {}",
        obligations[0].smtlib
    );
    assert!(
        obligations[0].smtlib.contains("(= v0 0)") && obligations[0].smtlib.contains("(= v0_1 1)"),
        "trace assignments should be bound into the replay query: {}",
        obligations[0].smtlib
    );
}

#[test]
fn trace_validity_replay_obligation_fails_closed_without_assignments() {
    let problem = ChcParser::parse(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#,
    )
    .expect("parse unsafe trace fixture");
    let predicate = problem.predicates()[0].id;
    let cex = Counterexample::new(vec![CounterexampleStep::new(
        predicate,
        FxHashMap::default(),
    )]);

    let error = cex
        .trace_validity_replay_obligations(&problem)
        .expect_err("missing concrete trace assignments must fail closed");

    assert!(
        error
            .to_string()
            .contains("missing concrete trace assignment"),
        "unexpected error: {error}"
    );
}

/// The single-predicate transition fixture used by the STEP D
/// ground-evaluation battery: `Inv(0)` reachable, `Inv(x+1)` on transition,
/// `Inv(1)` violates safety. The concrete trace `x: 0 → 1` genuinely reaches
/// the bad state.
fn step_d_inv_fixture() -> (ChcProblem, PredicateId) {
    let problem = ChcParser::parse(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#,
    )
    .expect("parse STEP D unsafe fixture");
    let predicate = problem.predicates()[0].id;
    (problem, predicate)
}

/// STEP D pass-path (transition-trace form): a concrete trace that pins the
/// time-versioned successor value ground-evaluates the reachability obligation
/// `init(0) ∧ transition ∧ query` to a concrete `true` — the UNSAFE verdict is
/// independently confirmed with no external solver.
#[test]
fn step_d_trace_ground_evaluates_confirms_genuine_trace() {
    let (problem, predicate) = step_d_inv_fixture();
    // The canonical state variable is `v0`; its time-1 version is `v0_1`
    // (matching the `(= v0 0)` / `(= v0_1 1)` pins the replay obligation emits).
    let cex = Counterexample::new(vec![
        CounterexampleStep::new(predicate, [("v0".to_string(), 0)].into_iter().collect()),
        CounterexampleStep::new(predicate, [("v0_1".to_string(), 1)].into_iter().collect()),
    ]);
    assert!(
        cex.trace_validity_ground_evaluates(&problem)
            .expect("a genuine reachability trace must ground-evaluate, not error"),
        "a genuine reachability trace must ground-evaluate to true"
    );
    // `ground_checks_unsafe` (no attached derivation) delegates to the same path.
    assert!(
        cex.ground_checks_unsafe(&problem)
            .expect("ground check must not error on a genuine trace"),
        "ground check must confirm the genuine trace"
    );
}

/// STEP D reject-path: a trace whose pinned successor value contradicts the
/// transition relation (`v0_1 = 5` but the transition forces `v0_1 = v0 + 1`)
/// ground-evaluates to a concrete `false` — the caller must NOT ship `unsat`.
#[test]
fn step_d_trace_ground_evaluates_rejects_corrupted_trace() {
    let (problem, predicate) = step_d_inv_fixture();
    let corrupted = Counterexample::new(vec![
        CounterexampleStep::new(predicate, [("v0".to_string(), 0)].into_iter().collect()),
        // v0_1 = 5 violates the transition v0_1 = v0 + 1 = 1.
        CounterexampleStep::new(predicate, [("v0_1".to_string(), 5)].into_iter().collect()),
    ]);
    assert!(
        !corrupted
            .trace_validity_ground_evaluates(&problem)
            .expect("a corrupted trace must ground-evaluate to a concrete false, not error"),
        "a trace that contradicts the transition relation must be rejected"
    );
    assert!(
        !corrupted
            .ground_checks_unsafe(&problem)
            .expect("ground check must return a concrete false, not error"),
        "ground check must reject the corrupted trace"
    );
}

/// STEP D fail-closed: a trace with no time-versioned successor binding (only
/// the source value is available at the non-initial step) leaves the successor
/// state variable unbound, so the obligation is not fully ground and the check
/// returns an error — the caller fail-closes to `unknown` (the sound direction).
#[test]
fn step_d_trace_ground_evaluates_fails_closed_on_unpinned_successor() {
    let (problem, predicate) = step_d_inv_fixture();
    let cex = Counterexample::new(vec![
        CounterexampleStep::new(predicate, [("v0".to_string(), 0)].into_iter().collect()),
        // Only the unversioned (source-semantic) name is present at time 1; it
        // is skipped, so `v0_1` stays unbound and the obligation is not ground.
        CounterexampleStep::new(predicate, [("v0".to_string(), 1)].into_iter().collect()),
    ]);
    assert!(
        cex.trace_validity_ground_evaluates(&problem).is_err(),
        "an un-ground-evaluable trace must fail closed, not decide"
    );
}
