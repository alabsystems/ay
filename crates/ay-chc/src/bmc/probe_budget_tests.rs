// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the front probe's per-depth budget policy
//! (`BmcSolver::ts_depth_cap`, `ts_probe_admit_next_depth`,
//! `enter_probe_extension` / `leave_probe_extension`); see
//! the development design notes at `9598c4206`.

use super::{BmcConfig, BmcSolver};
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ay_core::time::Instant;
use std::time::Duration;

fn tiny_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(3))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// A solver configured like the front probe: soft 14 s, hard 28 s, solve
/// deadline `solve_left` from now. Deadlines are pinned as
/// `solve_with_memory_scope` would pin them at `start`.
fn probe_solver(start: Instant, soft: Duration, hard: Duration, solve_left: Duration) -> BmcSolver {
    let config = BmcConfig {
        time_budget: Some(hard),
        soft_time_budget: Some(soft),
        probe_extension_deadline: Some(Instant::now() + solve_left),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(tiny_problem(), config);
    solver.solve_deadline.set(Some(start + soft));
    solver.probe_soft_deadline.set(Some(start + soft));
    solver.probe_hard_deadline.set(Some(start + hard));
    solver.probe_extension_active.set(false);
    solver
}

fn secs(d: Duration) -> f64 {
    d.as_secs_f64()
}

#[test]
fn depth_cap_is_at_least_the_predicted_cost_within_the_remaining_budget() {
    // Lane started 5 s ago in a 14 s soft budget: 9 s remain, half = 4.5 s.
    let start = Instant::now()
        .checked_sub(Duration::from_secs(5))
        .expect("fixture instant supports a five-second offset");
    let solver = probe_solver(
        start,
        Duration::from_secs(14),
        Duration::from_secs(28),
        Duration::from_secs(50),
    );
    let now = Instant::now();

    // No decided depth yet: the old half-remaining rule.
    let cap = solver.ts_depth_cap(now, &start, None).expect("budgeted");
    assert!(
        (secs(cap - now) - 4.5).abs() < 0.2,
        "half remaining, got {:.2}",
        secs(cap - now)
    );

    // Last depth cost 3 s -> prediction 6 s beats half remaining (4.5 s).
    let cap = solver
        .ts_depth_cap(now, &start, Some(Duration::from_secs(3)))
        .expect("budgeted");
    assert!(
        (secs(cap - now) - 6.0).abs() < 0.2,
        "predicted, got {:.2}",
        secs(cap - now)
    );

    // Last depth cost 4 s -> prediction 8 s still fits the 9 s remaining.
    let cap = solver
        .ts_depth_cap(now, &start, Some(Duration::from_secs(4)))
        .expect("budgeted");
    assert!(
        (secs(cap - now) - 8.0).abs() < 0.2,
        "predicted within the remainder, got {:.2}",
        secs(cap - now)
    );

    // Last depth cost 8 s -> prediction 16 s exceeds the 9 s remaining: the
    // depth is predicted not to finish, so it keeps the half rule.
    let cap = solver
        .ts_depth_cap(now, &start, Some(Duration::from_secs(8)))
        .expect("budgeted");
    assert!(
        (secs(cap - now) - 4.5).abs() < 0.2,
        "half remaining, got {:.2}",
        secs(cap - now)
    );
}

/// Outside the front probe (no soft budget: e.g. the counterexample replay,
/// `solve_bmc_only`, the adaptive BMC lanes) only the cap keeps budget for the
/// fresh fallback.
/// Shaped on the kind2 durationThm_3 replay that starved: a 45 s window,
/// depth 2 stretched to 20.9 s of wall, 21.5 s in.
#[test]
fn an_unaffordable_depth_leaves_the_fresh_fallback_half_the_remainder() {
    let start = Instant::now()
        .checked_sub(Duration::from_millis(21_500))
        .expect("fixture instant supports the elapsed probe window");
    let config = BmcConfig {
        time_budget: Some(Duration::from_secs(45)),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(tiny_problem(), config);
    let now = Instant::now();

    // 23.5 s left, prediction 41.8 s: half, not the whole remainder.
    let cap = solver
        .ts_depth_cap(now, &start, Some(Duration::from_millis(20_900)))
        .expect("budgeted");
    assert!(
        (secs(cap - now) - 11.75).abs() < 0.2,
        "half the remainder, got {:.2}",
        secs(cap - now)
    );

    // Twin: an affordable prediction (20 s) is honoured past half (metros_2).
    let cap = solver
        .ts_depth_cap(now, &start, Some(Duration::from_secs(10)))
        .expect("budgeted");
    assert!(
        (secs(cap - now) - 20.0).abs() < 0.2,
        "the affordable prediction, got {:.2}",
        secs(cap - now)
    );
}

#[test]
fn depth_within_soft_budget_is_admitted_without_extending() {
    let start = Instant::now()
        .checked_sub(Duration::from_secs(5))
        .expect("fixture instant supports a five-second offset");
    let solver = probe_solver(
        start,
        Duration::from_secs(14),
        Duration::from_secs(28),
        Duration::from_secs(50),
    );
    assert!(solver.ts_probe_admit_next_depth(&start, Some(Duration::from_secs(2))));
    assert!(!solver.probe_extension_active.get());
    assert_eq!(
        solver.solve_deadline.get(),
        solver.probe_soft_deadline.get()
    );
}

#[test]
fn soft_budget_reached_with_expensive_prediction_stops_the_lane() {
    // 13 s elapsed of 14 s soft; last depth 3 s -> predicted 6 s, which is
    // more than 10 % of the 50 s left on the solve: not converging enough.
    let start = Instant::now()
        .checked_sub(Duration::from_secs(13))
        .expect("fixture instant supports the elapsed soft budget");
    let solver = probe_solver(
        start,
        Duration::from_secs(14),
        Duration::from_secs(28),
        Duration::from_secs(50),
    );
    assert!(!solver.ts_probe_admit_next_depth(&start, Some(Duration::from_secs(3))));
    assert!(!solver.probe_extension_active.get());
    // With no decided depth at all there is nothing to predict from: stop.
    let start = Instant::now()
        .checked_sub(Duration::from_secs(15))
        .expect("fixture instant supports the elapsed soft budget");
    let solver = probe_solver(
        start,
        Duration::from_secs(14),
        Duration::from_secs(28),
        Duration::from_secs(50),
    );
    assert!(!solver.ts_probe_admit_next_depth(&start, None));
}

#[test]
fn converging_lane_extends_to_the_hard_budget_and_leaves_cleanly() {
    // 13 s elapsed of 14 s soft; last depth 1 s -> predicted 2 s: fits the
    // hard budget (15 s left) and 10 % of a 50 s solve remainder (5 s).
    let start = Instant::now()
        .checked_sub(Duration::from_secs(13))
        .expect("fixture instant supports the elapsed soft budget");
    let solver = probe_solver(
        start,
        Duration::from_secs(14),
        Duration::from_secs(28),
        Duration::from_secs(50),
    );
    assert!(solver.ts_probe_admit_next_depth(&start, Some(Duration::from_secs(1))));
    assert!(solver.probe_extension_active.get());
    assert_eq!(
        solver.solve_deadline.get(),
        solver.probe_hard_deadline.get()
    );
    assert_eq!(
        solver.effective_time_budget(),
        Some(Duration::from_secs(28))
    );

    // While extended, an admitted depth is capped at twice its prediction
    // (4 s here), not at the whole hard remainder (15 s).
    let now = Instant::now();
    let cap = solver
        .ts_depth_cap(now, &start, Some(Duration::from_secs(1)))
        .expect("budgeted");
    assert!(
        (secs(cap - now) - 4.0).abs() < 0.2,
        "bounded extension cap, got {:.2}",
        secs(cap - now)
    );

    // A depth whose prediction no longer fits is refused even while extended.
    assert!(!solver.ts_probe_admit_next_depth(&start, Some(Duration::from_secs(4))));

    // Leaving restores the soft deadline for the fallback paths.
    solver.leave_probe_extension();
    assert!(!solver.probe_extension_active.get());
    assert_eq!(
        solver.solve_deadline.get(),
        solver.probe_soft_deadline.get()
    );
    assert_eq!(
        solver.effective_time_budget(),
        Some(Duration::from_secs(14))
    );
}

#[test]
fn without_a_soft_budget_the_policy_is_inert() {
    let start = Instant::now()
        .checked_sub(Duration::from_secs(20))
        .expect("fixture instant supports the elapsed solve budget");
    let solver = BmcSolver::new(
        tiny_problem(),
        BmcConfig {
            time_budget: Some(Duration::from_secs(30)),
            ..BmcConfig::default()
        },
    );
    assert!(solver.ts_probe_admit_next_depth(&start, Some(Duration::from_secs(9))));
    assert!(!solver.probe_extension_active.get());
    assert_eq!(
        solver.effective_time_budget(),
        Some(Duration::from_secs(30))
    );
}

/// #9690 under the soft/hard split: the front probe arms `per_depth_timeout`
/// at the HARD budget, so `per_depth_deadline` must still clamp every
/// per-depth executor deadline to the SOFT deadline outside an admitted
/// extension, reach the hard deadline only while extended, and fall back to
/// soft on leaving. (Deadlines pinned by hand, as in `probe_solver`; the
/// next test pins them through `solve()`.)
#[test]
fn per_depth_deadline_follows_the_soft_budget_unless_extended() {
    let soft = Duration::from_secs(14);
    let hard = Duration::from_secs(28);
    let start = Instant::now()
        .checked_sub(Duration::from_secs(13))
        .expect("fixture instant supports the elapsed soft budget");
    let mut solver = probe_solver(start, soft, hard, Duration::from_secs(50));
    solver.config.per_depth_timeout = Some(hard);

    assert_eq!(
        solver.per_depth_deadline(Instant::now()),
        solver.probe_soft_deadline.get(),
        "outside an extension the hard per-depth timeout is clamped to the soft deadline"
    );

    // 13 s of 14 s soft elapsed, last depth 1 s: converging -> extension.
    assert!(solver.ts_probe_admit_next_depth(&start, Some(Duration::from_secs(1))));
    assert_eq!(
        solver.per_depth_deadline(Instant::now()),
        solver.probe_hard_deadline.get(),
        "an admitted extension may run to, but never past, the hard deadline"
    );

    solver.leave_probe_extension();
    assert_eq!(
        solver.per_depth_deadline(Instant::now()),
        solver.probe_soft_deadline.get(),
        "leaving the extension restores the soft per-depth deadline"
    );
}

/// #9690 end to end: a solve configured like the front probe
/// (`per_depth_timeout == time_budget == hard`, `soft_time_budget == soft`)
/// pins the deadline every path reads at the SOFT deadline and keeps the
/// hard one aside for an admitted extension, so a non-extended per-depth
/// executor deadline is the soft deadline, never `start + hard`.
#[test]
fn a_front_probe_shaped_solve_pins_the_soft_deadline_and_keeps_the_hard_one_aside() {
    let soft = Duration::from_secs(14);
    let hard = Duration::from_secs(28);
    // Counterexample at depth 6, lane limited to depth 3: levels 0..=3 are
    // decided in milliseconds, far inside the soft budget, so no extension.
    let solver = BmcSolver::new(
        counter_problem(6),
        BmcConfig {
            per_depth_timeout: Some(hard),
            time_budget: Some(hard),
            soft_time_budget: Some(soft),
            probe_extension_deadline: Some(Instant::now() + Duration::from_secs(50)),
            ..lane_config(3)
        },
    );
    assert!(!matches!(solver.solve(), crate::ChcEngineResult::Unsafe(_)));
    assert_eq!(
        solver.proven_unsat_prefix(),
        4,
        "the lane decided levels 0..=3 under the probe's budgets"
    );

    let (Some(soft_deadline), Some(hard_deadline)) = (
        solver.probe_soft_deadline.get(),
        solver.probe_hard_deadline.get(),
    ) else {
        panic!("a budgeted solve pins both probe deadlines");
    };
    assert_eq!(
        hard_deadline
            .checked_duration_since(soft_deadline)
            .expect("hard deadline follows the soft deadline"),
        hard.checked_sub(soft)
            .expect("hard deadline follows soft deadline"),
        "both deadlines are measured from the same solve start"
    );
    assert!(!solver.probe_extension_active.get());
    assert_eq!(solver.solve_deadline.get(), Some(soft_deadline));
    assert_eq!(
        solver.per_depth_deadline(Instant::now()),
        Some(soft_deadline),
        "a non-extended per-depth deadline is the soft deadline, not start + hard"
    );
}

// ---------------------------------------------------------------------------
// Hand-off frontier (BMC_probe_handoff_2026-09-19)
// ---------------------------------------------------------------------------

/// `P(0)`, `P(x) ∧ y = x+1 ⇒ P(y)`, `P(x) ∧ x ≥ bound ⇒ ⊥`: the shortest
/// counterexample has exactly `bound` transitions.
fn counter_problem(bound: i128) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(y.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(y)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(bound))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// The front probe's configuration shape (per-depth timeout set so the
/// transition-system lane, not the concrete-scalar prepass, decides).
fn lane_config(max_depth: usize) -> BmcConfig {
    BmcConfig {
        max_depth,
        time_budget: Some(Duration::from_secs(30)),
        per_depth_timeout: Some(Duration::from_secs(30)),
        enable_k_induction: false,
        enable_adaptive_stepping: false,
        ..BmcConfig::default()
    }
}

#[test]
fn a_probe_that_gives_up_exports_its_proven_level_prefix() {
    // Counterexample at depth 6, but the probe may only look to depth 3:
    // levels 0..=3 are proven unreachable, nothing is found.
    let problem = counter_problem(6);
    let solver = BmcSolver::new(problem, lane_config(3));
    assert!(!matches!(solver.solve(), crate::ChcEngineResult::Unsafe(_)));
    assert_eq!(
        solver.proven_unsat_prefix(),
        4,
        "levels 0,1,2,3 decided unsat"
    );
}

#[test]
fn portfolio_bmc_resumes_at_the_exported_depth_and_finds_the_cex_one_level_deeper() {
    let problem = counter_problem(4);
    let frontier = super::ProbeFrontier {
        depth: 3,
        fingerprint: super::problem_fingerprint(&problem),
    };
    let solver = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            resume_frontier: Some(frontier),
            ..lane_config(10)
        },
    );
    let crate::ChcEngineResult::Unsafe(cex) = solver.solve() else {
        panic!("the counter reaches 4");
    };
    // Resumed at level 3: exactly two checks (3 unsat, 4 sat), not five.
    let stats = solver.stats.borrow();
    assert_eq!(stats.max_depth_reached, 4);
    assert_eq!(stats.num_checks, 2, "levels 0..3 were not re-checked");
    drop(stats);
    let witness = cex.witness.as_ref().expect("witness");
    assert_eq!(witness.entries.len(), 5, "cex at depth 4 = k+1");
    crate::ground_derivation::validate_ground_derivation(
        &problem,
        cex.ground_derivation.as_ref().expect("ground derivation"),
    )
    .expect("the resumed run's counterexample validates on the original clauses");
}

#[test]
fn a_frontier_from_a_different_problem_is_ignored() {
    let problem = counter_problem(4);
    let other = counter_problem(5);
    let frontier = super::ProbeFrontier {
        depth: 3,
        fingerprint: super::problem_fingerprint(&other),
    };
    assert_ne!(frontier.fingerprint, super::problem_fingerprint(&problem));
    let solver = BmcSolver::new(
        problem,
        BmcConfig {
            resume_frontier: Some(frontier),
            ..lane_config(10)
        },
    );
    assert!(matches!(solver.solve(), crate::ChcEngineResult::Unsafe(_)));
    assert_eq!(
        solver.stats.borrow().num_checks,
        5,
        "fingerprint mismatch: every level from 0 is checked"
    );
}

#[test]
fn problem_fingerprint_is_structural() {
    let a = counter_problem(4);
    let b = counter_problem(4);
    let c = counter_problem(5);
    assert_eq!(
        super::problem_fingerprint(&a),
        super::problem_fingerprint(&b)
    );
    assert_ne!(
        super::problem_fingerprint(&a),
        super::problem_fingerprint(&c)
    );
}

/// Real-sorted TS lane per-depth cap (the development design notes at `9598c4206`):
/// `max(2 s, 8 × last decided depth)`, Int systems uncapped.
#[test]
fn real_sorted_ts_lane_caps_a_depth_at_its_trend() {
    let start = Instant::now();
    assert_eq!(BmcSolver::ts_real_depth_cap(false, start, None), None);
    assert_eq!(
        BmcSolver::ts_real_depth_cap(false, start, Some(Duration::from_secs(1))),
        None
    );
    assert_eq!(
        BmcSolver::ts_real_depth_cap(true, start, None),
        Some(start + Duration::from_secs(2)),
        "an undecided first depth gets the floor"
    );
    assert_eq!(
        BmcSolver::ts_real_depth_cap(true, start, Some(Duration::from_millis(14))),
        Some(start + Duration::from_secs(2)),
        "cheap unsat depths keep the floor"
    );
    assert_eq!(
        BmcSolver::ts_real_depth_cap(true, start, Some(Duration::from_millis(500))),
        Some(start + Duration::from_secs(4)),
        "a costlier trend scales the cap by 8"
    );
}
