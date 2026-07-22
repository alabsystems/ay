// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for GSpacer-style queued MAY proof obligations (agenda #6).
//!
//! Covers: spawn mechanics (gas budget, level clamping, dedup, gates),
//! gas exhaustion, may-pob lemma insertion reaching the desired level, and
//! the SOUNDNESS PIN: a reachable may-pob must never produce an Unsafe
//! verdict — counterexamples flow only through must-pob traces.

use super::super::super::*;
use crate::pdr::config::PdrConfig;
use crate::{ChcParser, ChcVar};

/// SAFE counter system: init x=0 (clause 0), x'=x+1 (clause 1),
/// query x<0 (clause 2).
const SAFE_COUNTER: &str = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (inv x) (= x2 (+ x 1))) (inv x2))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;

fn safe_counter_solver(config: PdrConfig) -> (PdrSolver, PredicateId, ChcVar) {
    let problem = ChcParser::parse(SAFE_COUNTER).unwrap();
    let solver = PdrSolver::new(problem, config);
    let inv = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let x = solver.canonical_vars(inv).unwrap()[0].clone();
    (solver, inv, x)
}

fn expr_mentions_int(expr: &ChcExpr, needle: i128) -> bool {
    match expr {
        ChcExpr::Int(v) => *v == needle,
        ChcExpr::Op(_, args) => args.iter().any(|a| expr_mentions_int(a, needle)),
        ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter().any(|a| expr_mentions_int(a, needle))
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Spawn mechanics
// ---------------------------------------------------------------------------

#[test]
fn spawn_may_pob_enqueues_gas_budgeted_pob_at_clamped_level() {
    let (mut solver, inv, x) = safe_counter_solver(PdrConfig::default());
    let origin = ProofObligation::new(
        inv,
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(7)),
        2,
    );
    let candidate = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5));

    assert!(solver.spawn_may_pob(&origin, candidate.clone(), PobKind::MaySubsume, Some(0), 3));

    let pob = solver
        .pop_obligation()
        .expect("spawned may-pob should be queued");
    assert_eq!(pob.kind, PobKind::MaySubsume);
    assert!(pob.is_may());
    assert_eq!(pob.level, 1, "cluster min level 0 must clamp to level 1");
    assert_eq!(pob.desired_level, 2, "desired level = origin pob level");
    assert_eq!(pob.gas, 15, "gas = MAY_POB_GAS_PER_MEMBER x cluster size");
    assert_eq!(pob.predicate, inv);
    assert_eq!(pob.state, candidate);
    assert!(
        pob.query_clause.is_none() && pob.parent.is_none() && pob.derivation_id.is_none(),
        "may-pobs must never carry query/derivation lineage"
    );
    assert!(solver.pop_obligation().is_none(), "exactly one pob spawned");
}

#[test]
fn spawn_may_pob_dedups_and_respects_gates() {
    let (mut solver, inv, x) = safe_counter_solver(PdrConfig::default());
    let origin = ProofObligation::new(
        inv,
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(7)),
        2,
    );
    let candidate = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5));

    assert!(solver.spawn_may_pob(&origin, candidate.clone(), PobKind::MaySubsume, None, 2));
    assert!(
        !solver.spawn_may_pob(&origin, candidate.clone(), PobKind::MaySubsume, None, 2),
        "identical candidate must be deduplicated"
    );
    assert!(
        solver.spawn_may_pob(&origin, candidate.clone(), PobKind::MayConjecture, None, 2),
        "dedup key includes the pob kind"
    );

    // A may origin never spawns further may-pobs (gas discipline).
    let may_origin = ProofObligation::new(
        inv,
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(3)),
        2,
    )
    .with_may(PobKind::MaySubsume, 5, 2);
    let other = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(-3));
    assert!(!solver.spawn_may_pob(&may_origin, other.clone(), PobKind::MaySubsume, None, 2));

    // An empty cluster never spawns.
    assert!(!solver.spawn_may_pob(&origin, other.clone(), PobKind::MaySubsume, None, 0));

    // Config kill switch.
    let config_off = PdrConfig {
        use_may_pobs: false,
        ..PdrConfig::default()
    };
    let (mut solver_off, inv_off, x_off) = safe_counter_solver(config_off);
    let origin_off = ProofObligation::new(
        inv_off,
        ChcExpr::eq(ChcExpr::var(x_off.clone()), ChcExpr::int(7)),
        2,
    );
    assert!(!solver_off.spawn_may_pob(
        &origin_off,
        ChcExpr::ge(ChcExpr::var(x_off), ChcExpr::int(5)),
        PobKind::MaySubsume,
        None,
        3
    ));
    assert!(
        solver_off.pop_obligation().is_none(),
        "kill switch must prevent enqueueing"
    );
}

// ---------------------------------------------------------------------------
// Soundness pin: may-pobs never produce Unsafe
// ---------------------------------------------------------------------------

/// SOUNDNESS PIN (agenda #6): a may-pob whose state is genuinely reachable
/// (here `x >= 0` covers the init state of a SAFE system) must be dropped
/// silently — the strengthen result must not be Unsafe and must not be
/// degraded by the auxiliary may work.
#[test]
fn soundness_pin_reachable_may_pob_never_produces_unsafe() {
    let (mut solver, inv, x) = safe_counter_solver(PdrConfig::default());
    let reachable = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    let may = ProofObligation::new(inv, reachable, 1).with_may(PobKind::MaySubsume, 10, 1);
    solver.push_obligation(may);

    let result = solver.strengthen();
    assert!(
        !matches!(result, StrengthenResult::Unsafe(_)),
        "reachable may-pob must never yield an Unsafe verdict"
    );
    assert!(
        matches!(result, StrengthenResult::Safe),
        "dropping the unblockable may-pob must not degrade the safe verdict"
    );
}

/// Gas exhaustion: a reachable may-pob with zero gas is dropped before any
/// predecessor descent; the solve outcome is unaffected.
#[test]
fn out_of_gas_reachable_may_pob_is_dropped_without_descent() {
    let (mut solver, inv, x) = safe_counter_solver(PdrConfig::default());
    let reachable = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    let may = ProofObligation::new(inv, reachable, 1).with_may(PobKind::MayConjecture, 0, 1);
    solver.push_obligation(may);

    let result = solver.strengthen();
    assert!(
        matches!(result, StrengthenResult::Safe),
        "gas-exhausted may-pob must be dropped silently"
    );
    assert!(
        solver.pop_obligation().is_none(),
        "no residual obligations after silent drop"
    );
}

/// SOUNDNESS PIN (must-reachability fast path): a may-pob at the current
/// level that intersects a backed must-reachable state is dropped silently,
/// while an otherwise-identical MUST pob with query lineage DOES construct a
/// counterexample through the very same code path — proving the guard
/// distinguishes pob kinds rather than passing vacuously.
#[test]
fn soundness_pin_may_pob_on_must_reachable_state_dropped_while_must_pob_flags_cex() {
    fn setup_with_backed_reach_fact() -> (PdrSolver, PredicateId, ChcExpr) {
        let (mut solver, inv, x) = safe_counter_solver(PdrConfig::default());
        // x = 0 is genuinely reachable: it IS the init state (clause 0).
        let state = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0));
        let mut instances = FxHashMap::default();
        cube::extract_equalities_from_formula(&state, &mut instances);
        let rf_id = PdrSolver::insert_reach_fact_bounded(
            &mut solver.reachability,
            false,
            ReachFact {
                id: ReachFactId(0),
                predicate: inv,
                level: 0,
                state: state.clone(),
                incoming_clause: Some(0),
                premises: vec![],
                instances,
            },
        )
        .expect("reach fact store should accept the init fact");
        solver.add_must_summary_backed(inv, 0, state.clone(), rf_id);
        solver
            .reachability
            .reach_solvers
            .add_backed(inv, rf_id, state.clone());
        (solver, inv, state)
    }

    // Leg 1: MAY pob intersecting the must-reachable state -> dropped silently.
    let (mut may_solver, inv, state) = setup_with_backed_reach_fact();
    let may = ProofObligation::new(inv, state.clone(), 1).with_may(PobKind::MaySubsume, 10, 1);
    may_solver.push_obligation(may);
    let may_result = may_solver.strengthen();
    assert!(
        !matches!(may_result, StrengthenResult::Unsafe(_)),
        "may-pob intersecting a must-reachable state must never yield Unsafe"
    );

    // Leg 2 (contrast): identical MUST pob with query lineage exercises the
    // same must-reachability fast path and does flag a counterexample.
    let (mut must_solver, must_inv, must_state) = setup_with_backed_reach_fact();
    let must = ProofObligation::new(must_inv, must_state, 1).with_query_clause(2);
    must_solver.push_obligation(must);
    let must_result = must_solver.strengthen();
    assert!(
        matches!(must_result, StrengthenResult::Unsafe(_)),
        "contrast leg: the same state as a query-derived MUST pob must reach \
         counterexample construction (otherwise the may pin passes vacuously)"
    );
}

// ---------------------------------------------------------------------------
// May-pob lemma insertion at the desired level
// ---------------------------------------------------------------------------

/// A blockable may-pob's lemma must be learned and be active at the pob's
/// `desired_level`. AY frames are cumulative (frames 1..=k all participate in
/// the level-k constraint), so the lemma learned when the may-pob is blocked
/// at its spawn level — plus the gas-budgeted promotion re-verification —
/// makes the conjecture part of the desired level's constraint.
#[test]
fn blocked_may_pob_lemma_is_active_at_desired_level() {
    let config = super::unit_test_config();
    let (mut solver, inv, x) = safe_counter_solver(config);
    // Grow to 4 frames so the desired level 3 exists (current level = 3).
    while solver.frames.len() <= 3 {
        solver.frames.push(Frame::new());
    }

    // x = 5 is unreachable at level 1 (init is x=0, one step reaches x=1),
    // so the may-pob is blockable; the query lemma (about x < 0) never
    // mentions the constant 5, keeping the assertion unambiguous.
    let cube_x5 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5));
    let may = ProofObligation::new(inv, cube_x5, 1).with_may(PobKind::MaySubsume, 5, 3);
    solver.push_obligation(may);

    let result = solver.strengthen();
    assert!(
        !matches!(result, StrengthenResult::Unsafe(_)),
        "blockable may-pob must not affect the verdict"
    );

    let constraint = solver
        .cumulative_frame_constraint(3, inv)
        .expect("blocking the may-pob must have produced lemmas");
    assert!(
        expr_mentions_int(&constraint, 5),
        "may-pob lemma (about x=5) must be active at the desired level 3, got {constraint}"
    );
}
