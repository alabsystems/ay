// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Workstream B locks owned by WP-B1-S (`DESIGN_spacer_pob_lemma_pipeline.md`
//! §6 S11): L3 `frame_hyp(k) ⇒ frame_hyp(k+1)`, L4
//! `cumulative_frame_constraint == frame_hyp` modulo the `false` filter under
//! the lane, the delta `frames_equivalent` quick-accept, the lifted-cap
//! policies, and the construction gates of `spacer_core`.

use super::*;
use crate::pdr::config::SpacerLane;
use crate::pdr::solver::strengthen::{level0_cap_policy, point_block_cap_policy};
use crate::PredicateId;

/// `Init: x = 0 → P(x)`, `P(x) ∧ x' = x + 1 → P(x')`, `P(x) ∧ x < 0 → false`.
fn counter_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x1 = ChcVar::new("x1", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(0))),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x1.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::Int(1)),
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x1)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// A predicate with a two-body (hyperedge) clause: `P(x) ∧ P(y) → Q(x + y)`.
fn hyperedge_problem() -> ChcProblem {
    let mut problem = counter_problem();
    let p = problem.predicates()[0].id;
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (p, vec![ChcExpr::var(x.clone())]),
                (p, vec![ChcExpr::var(y.clone())]),
            ],
            None,
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y))]),
    ));
    problem
}

fn solver_with_frames(spacer_core: bool) -> (PdrSolver, PredicateId, Vec<ChcExpr>) {
    let mut solver = PdrSolver::new(
        counter_problem(),
        test_config().with_spacer(SpacerLane::OFF),
    );
    solver.spacer_core = spacer_core;
    let p = solver.problem.predicates()[0].id;
    let canon = solver.canonical_vars(p).expect("canonical vars").to_vec();
    let x = ChcExpr::var(canon[0].clone());
    // frames 0..=4
    while solver.frames.len() < 5 {
        solver.frames.push(Frame::new());
    }
    let l1 = ChcExpr::ge(x.clone(), ChcExpr::Int(0));
    let l2 = ChcExpr::ge(x.clone(), ChcExpr::Int(-1));
    let l3 = ChcExpr::ge(x.clone(), ChcExpr::Int(-2));
    let l4 = ChcExpr::le(x, ChcExpr::Int(100));
    solver.frames[1].add_lemma(Lemma::new(p, l1.clone(), 1));
    solver.frames[2].add_lemma(Lemma::new(p, l2.clone(), 2));
    solver.frames[3].add_lemma(Lemma::new(p, l3.clone(), 3));
    solver.frames[3].add_lemma(Lemma::new(p, ChcExpr::Bool(false), 3));
    solver.frames[4].add_lemma(Lemma::new(p, l4.clone(), 4));
    (solver, p, vec![l1, l2, l3, l4])
}

fn conjunct_set(e: Option<ChcExpr>) -> Vec<ChcExpr> {
    match e {
        None => Vec::new(),
        Some(ChcExpr::Bool(false)) => vec![ChcExpr::Bool(false)],
        Some(e) => e.collect_conjuncts_nontrivial(),
    }
}

#[test]
fn frame_hyp_is_the_delta_frame_and_monotone_l3() {
    let (solver, p, l) = solver_with_frames(true);
    // frame_hyp keeps Bool(false): `and_all` short-circuits it to `false`.
    assert_eq!(solver.frame_hyp(3, p), Some(ChcExpr::Bool(false)));
    assert_eq!(conjunct_set(solver.frame_hyp(4, p)), vec![l[3].clone()]);
    // frame_hyp(0) is None by contract.
    assert!(solver.frame_hyp(0, p).is_none());
    // Lemma sets: F_k ⊇ F_{k+1} (lock L3), checked on the set view.
    for k in 1..4 {
        let lower = solver.frame_hyp_lemma_set(k, p);
        let upper = solver.frame_hyp_lemma_set(k + 1, p);
        assert!(upper.is_subset(&lower), "L3 violated at k={k}");
    }
    assert_eq!(solver.frame_hyp_lemma_set(1, p).len(), 5);
    assert_eq!(solver.frame_hyp_lemma_set(4, p).len(), 1);
    // Beyond the top frame: clamped to the top.
    assert_eq!(solver.frame_hyp(9, p), solver.frame_hyp(4, p));
    solver.debug_check_frame_hyp_monotone(2, p);
}

#[test]
fn cumulative_equals_frame_hyp_modulo_false_under_the_lane_l4() {
    let (solver, p, l) = solver_with_frames(true);
    // Under the lane: cumulative(k) = frame_hyp(k) without the `false` lemma.
    assert_eq!(
        conjunct_set(solver.cumulative_frame_constraint(1, p)),
        vec![l[0].clone(), l[1].clone(), l[2].clone(), l[3].clone()]
    );
    assert_eq!(
        conjunct_set(solver.cumulative_frame_constraint(3, p)),
        vec![l[2].clone(), l[3].clone()]
    );
    assert_eq!(
        conjunct_set(solver.cumulative_frame_constraint(4, p)),
        vec![l[3].clone()]
    );
    assert!(solver.cumulative_frame_constraint(0, p).is_none());
    // frame_hyp(k) with the `false` lemma filtered == cumulative(k).
    for k in 1..=4 {
        let mut hyp: Vec<ChcExpr> = solver
            .frame_hyp_lemma_set(k, p)
            .into_iter()
            .filter(|f| !matches!(f, ChcExpr::Bool(false)))
            .collect();
        let mut cum = conjunct_set(solver.cumulative_frame_constraint(k, p));
        hyp.sort_by_key(ChcExpr::structural_hash);
        cum.sort_by_key(ChcExpr::structural_hash);
        assert_eq!(hyp, cum, "L4 violated at k={k}");
    }
    // Legacy (lane off): cumulative(k) = ∧ frames[1..=k] — the OTHER direction.
    let (legacy, p, l) = solver_with_frames(false);
    assert_eq!(
        conjunct_set(legacy.cumulative_frame_constraint(1, p)),
        vec![l[0].clone()]
    );
    assert_eq!(
        conjunct_set(legacy.cumulative_frame_constraint(3, p)),
        vec![l[0].clone(), l[1].clone(), l[2].clone()]
    );
}

#[test]
fn delta_frames_equivalent_quick_accept() {
    let (mut solver, p, l) = solver_with_frames(true);
    // frames[1] = {l1}; l1 is not above → undecided (SMT would run).
    assert_eq!(solver.frames_equivalent_delta_quick(1, 2), None);
    // Duplicate l1 into frames[2] → quick-accept at (1, 2).
    solver.frames[2].add_lemma(Lemma::new(p, l[0].clone(), 2));
    assert_eq!(solver.frames_equivalent_delta_quick(1, 2), Some(true));
    // frames[4] = {l4}: nothing above → undecided; an empty tail → Some(false).
    assert_eq!(solver.frames_equivalent_delta_quick(4, 5), None);
    solver.frames.push(Frame::new());
    solver.frames.push(Frame::new());
    assert_eq!(solver.frames_equivalent_delta_quick(5, 6), Some(false));
    assert_eq!(solver.frames_equivalent_delta_quick(0, 1), Some(false));
}

#[test]
fn lifted_cap_policies() {
    let off = SpacerLane::OFF;
    let r1 = SpacerLane::rung(1);
    assert_eq!(point_block_cap_policy(false, &off, 25), Some(25));
    assert_eq!(point_block_cap_policy(false, &r1, 25), Some(25));
    assert_eq!(point_block_cap_policy(true, &r1, 25), None);
    let mut valve = r1;
    valve.enum_valve = Some(7);
    assert_eq!(point_block_cap_policy(true, &valve, 25), Some(7));
    let mut no_lift = r1;
    no_lift.lift_caps = false;
    assert_eq!(point_block_cap_policy(true, &no_lift, 25), Some(25));
    assert_eq!(level0_cap_policy(false, &off, 50), Some(50));
    assert_eq!(level0_cap_policy(true, &r1, 50), None);
    assert_eq!(level0_cap_policy(true, &no_lift, 50), Some(50));
}

#[test]
fn spacer_core_construction_gates() {
    // Lane OFF: nothing enabled.
    let solver = PdrSolver::new(
        counter_problem(),
        test_config().with_spacer(SpacerLane::OFF),
    );
    assert!(!solver.spacer_core);
    assert!(solver.problem_is_linear);
    let p = solver.problem.predicates()[0].id;
    assert!(solver.linear_pred(p));

    // Lane ON, linear LIA: core on.
    let cfg = test_config().with_spacer(SpacerLane::rung(1));
    let solver = PdrSolver::new(counter_problem(), cfg.clone());
    assert!(solver.spacer_core);
    assert!(solver.config.spacer.lift_caps);
    assert_eq!(
        solver.oracle_backend,
        crate::pdr::config::OracleBackend::Legacy
    );

    // Session backend degrades to Legacy while incremental PDR is off.
    let solver = PdrSolver::new(
        counter_problem(),
        test_config().with_spacer(SpacerLane::rung(4)),
    );
    assert_eq!(
        solver.oracle_backend,
        crate::pdr::config::OracleBackend::Legacy
    );

    // Hyperedge predicate: problem nonlinear, the lane is bypassed (R3);
    // only the linear predicate is `linear_pred`.
    let solver = PdrSolver::new(hyperedge_problem(), cfg.clone());
    assert!(!solver.spacer_core);
    assert!(!solver.problem_is_linear);
    assert_eq!(solver.spacer_stats.lane_bypassed_nonlinear, 1);
    assert!(
        solver.config.use_pob_push,
        "a bypassed problem keeps its profile"
    );
    let preds: Vec<_> = solver.problem.predicates().iter().map(|p| p.id).collect();
    assert!(solver.linear_pred(preds[0]));
    assert!(!solver.linear_pred(preds[1]));

    // BV sorts bypass the lane entirely (§7.4).
    let mut bv = ChcProblem::new();
    let q = bv.declare_predicate("Q", vec![ChcSort::BitVec(8)]);
    let b = ChcVar::new("b", ChcSort::BitVec(8));
    bv.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::BitVec(0, 8))),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(b)]),
    ));
    let solver = PdrSolver::new(bv, cfg);
    assert!(!solver.spacer_core);
    assert_eq!(solver.spacer_stats.lane_bypassed_bv, 1);

    // Validator-shaped config with the lane pinned OFF: counter stays 0 (S10).
    let validator = PdrConfig {
        preserve_original_clauses: true,
        disable_array_scalarization: true,
        spacer: SpacerLane::OFF,
        ..test_config()
    };
    let solver = PdrSolver::new(counter_problem(), validator);
    assert_eq!(solver.spacer_stats.constructions_with_lane_in_validator, 0);
    assert!(!solver.spacer_core);
}

/// WP-S 2026-09-23 hand-off 5: `--chc-spacer-rung N` reaches every PDR config
/// through `PdrConfig::default()` (the process-wide A/B switches) but not the
/// Spacer profile; `PdrSolver::new` must apply the profile whenever the lane
/// runs, and only then.
#[test]
fn spacer_profile_is_applied_when_the_lane_runs_via_the_cli_switch() {
    let base = crate::ab_switches::ChcAbSwitches::default();
    let switches = crate::ab_switches::ChcAbSwitches {
        spacer_rung: 1,
        ..base
    };
    let _override = crate::ab_switches::TestOverride::set(switches);

    // The CLI path: the lane flags arrive through the config default, the
    // technique toggles are the production ones.
    let production = PdrConfig::production(false);
    assert!(
        production.spacer.enabled,
        "the switch reaches PdrConfig::default()"
    );
    assert!(production.use_convex_closure && production.use_restarts && production.use_pob_push);

    let solver = PdrSolver::new(counter_problem(), production.clone());
    assert!(solver.spacer_core);
    assert!(
        !solver.config.use_convex_closure,
        "convex closure off under the lane"
    );
    assert!(
        !solver.config.use_restarts,
        "Luby restarts off under the lane"
    );
    assert!(!solver.config.use_pob_push, "POB push off under the lane");
    assert!(!solver.config.use_may_pobs, "may-pobs off under the lane");
    assert!(solver.config.use_mbp);
    assert!(solver.config.spacer.false_lemma_in_model);

    // A problem the lane bypasses (BV) keeps its config: lane OFF ≡ before.
    let mut bv = ChcProblem::new();
    let q = bv.declare_predicate("Q", vec![ChcSort::BitVec(8)]);
    let b = ChcVar::new("b", ChcSort::BitVec(8));
    bv.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::BitVec(0, 8))),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(b)]),
    ));
    let solver = PdrSolver::new(bv, production.clone());
    assert!(!solver.spacer_core);
    assert_eq!(
        solver.config.use_convex_closure,
        production.use_convex_closure
    );
    assert_eq!(solver.config.use_restarts, production.use_restarts);
    assert_eq!(solver.config.use_pob_push, production.use_pob_push);
}

#[test]
fn spacer_profile_is_not_applied_with_the_lane_off() {
    let config = PdrConfig::production(false).with_spacer(SpacerLane::OFF);
    let solver = PdrSolver::new(counter_problem(), config.clone());
    assert!(!solver.spacer_core);
    assert_eq!(solver.config.use_convex_closure, config.use_convex_closure);
    assert_eq!(solver.config.use_restarts, config.use_restarts);
    assert_eq!(solver.config.use_pob_push, config.use_pob_push);
    assert_eq!(solver.config.use_may_pobs, config.use_may_pobs);
}

/// `DESIGN` §4.2.5: under the lane, escalation widens the ind-gen budget
/// (×2, ×4) instead of re-enabling convex closure; lane off is unchanged.
#[test]
fn escalation_under_the_lane_widens_ind_gen_instead_of_convex_closure() {
    let lane = PdrConfig::production(false).with_spacer(SpacerLane::rung(1));
    let mut solver = PdrSolver::new(counter_problem(), lane);
    let base = solver.config.spacer.ind_gen_max_queries;
    assert!(solver.escalate_generalization_strategy());
    assert_eq!(solver.config.spacer.ind_gen_max_queries, base * 2);
    assert!(solver.escalate_generalization_strategy());
    assert_eq!(solver.config.spacer.ind_gen_max_queries, base * 4);
    assert!(
        !solver.config.use_convex_closure,
        "escalation must not re-enable convex closure"
    );
    assert!(solver.escalate_generalization_strategy());
    assert_eq!(solver.config.spacer.ind_gen_max_queries, base * 4);

    let off = PdrConfig::production(false).with_spacer(SpacerLane::OFF);
    let mut legacy = PdrSolver::new(counter_problem(), off);
    let legacy_queries = legacy.config.spacer.ind_gen_max_queries;
    assert!(legacy.escalate_generalization_strategy());
    assert!(legacy.escalate_generalization_strategy());
    assert!(
        legacy.config.use_convex_closure,
        "legacy escalation unchanged"
    );
    assert_eq!(legacy.config.spacer.ind_gen_max_queries, legacy_queries);
}

/// WP-S 2026-09-23 (HOLA-44 root cause, part 2): a clause guard propagated from
/// a body lemma at level L carries `max_level = L + 1` and is valid only for
/// parent checks whose body frame lies inside `F_L`. A push from `level` reads
/// `F_level`, so it must consult guards at check level `level + 1` — with the
/// lane on AND off since the push-guard fix (`push_guard_check_level`,
/// `model/push_guard_level_tests.rs`).
#[test]
fn push_reads_clause_guards_at_the_target_level_under_the_lane() {
    fn setup(lane: SpacerLane) -> (PdrSolver, Lemma) {
        let config = PdrConfig::production(false).with_spacer(lane);
        let mut solver = PdrSolver::new(counter_problem(), config);
        let p = solver.problem.predicates()[0].id;
        let x = ChcExpr::var(solver.canonical_vars(p).expect("canonical vars")[0].clone());
        while solver.frames.len() < 5 {
            solver.frames.push(Frame::new());
        }
        let step_index = solver
            .problem
            .clauses_defining_with_index(p)
            .find(|(_, c)| !c.body.predicates.is_empty())
            .map(|(i, _)| i)
            .expect("step clause");
        // A guard on the step clause's head `x' ≥ 0`, as if propagated from a
        // body lemma at level 1 (max_level = 2).
        let guard = ChcExpr::ge(x.clone(), ChcExpr::Int(0));
        solver
            .caches
            .clause_guarded_lemmas
            .insert((p, step_index), vec![(guard, 2)]);
        let lemma = Lemma::new(p, ChcExpr::ge(x, ChcExpr::Int(0)), 1);
        (solver, lemma)
    }

    // Lane on: from level 1 (body F_1 ⊆ F_1) the guard is valid → the push holds;
    // from level 2 (body F_2, no lemma) it is not → `x' = x + 1 ≥ 0` fails.
    let (mut lane, lemma) = setup(SpacerLane::rung(1));
    assert!(lane.spacer_core);
    assert_eq!(PdrSolver::push_guard_check_level(2), 3);
    assert!(
        lane.can_push_lemma(&lemma, 1),
        "guard valid for a push from level 1"
    );
    assert!(
        !lane.can_push_lemma(&lemma, 2),
        "a level-1 guard must not justify a push from level 2 under the lane"
    );

    // Lane off: the same reading (the push-guard fix is not lane-gated).
    let (mut legacy, lemma) = setup(SpacerLane::OFF);
    assert!(
        legacy.can_push_lemma(&lemma, 1),
        "guard valid for a push from level 1"
    );
    assert!(
        !legacy.can_push_lemma(&lemma, 2),
        "a level-1 guard must not justify a push from level 2 with the lane off either"
    );
}
