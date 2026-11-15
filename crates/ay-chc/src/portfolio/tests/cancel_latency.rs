// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mid-run cancellation latency of every portfolio engine (WP-D1-E).
//!
//! Each engine runs exactly as a parallel portfolio lane runs it (lane child
//! token injected, [`crate::smt::ScopedLaneCancellation`] bound to the worker
//! thread with the group's interrupt flag, a lane solve deadline far away) on
//! instances that are hard for it, the group is cancelled after one second,
//! and the time until the engine returns is measured. A loser that keeps
//! running after cancellation holds back nothing any more (the verdict reap is
//! bounded), but it still burns a core the winner's validation and the next
//! stage need, and without a verdict the portfolio still joins it.
//!
//! The instances are CHC-COMP 2026 benchmarks (`tests/fixtures/cancel_latency`):
//! `metros_4` (LIA-Lin lustre, the S-reap-shaped LIA-Lin loss), `tte_synchro`
//! (S-reap), `om1_with_relays_agreement` (S-IMC canary, LRA) and
//! `s_multipl_12` (LIA, nonlinear CEGAR templates).
//!
//! The suite runs the first instance (`metros_4`, the S-reap shape) so the test
//! stays inside the lib suite's budget (the repository bans disabled tests);
//! widen `MEASURED_INSTANCES` locally to measure all four with `--nocapture`.

use super::*;
use crate::portfolio::engines::run_engine;
use crate::portfolio::selector::EngineSelector;
use std::time::Instant;

/// Budget for one engine to notice cancellation and return. The design target
/// is one SMT query (about two seconds on a quiet host); the assertion allows
/// ten because this runs inside the parallel lib suite on a loaded machine.
const MAX_CANCEL_LATENCY: Duration = Duration::from_secs(10);
/// How many of [`INSTANCES`] the test measures (all four: about 1–2 minutes).
const MEASURED_INSTANCES: usize = 1;
/// How long each engine runs before its group is cancelled.
const RUN_BEFORE_CANCEL: Duration = Duration::from_secs(1);
/// Give up on a straggler after this long (it is then reported, not joined).
const STRAGGLER_WAIT: Duration = Duration::from_secs(60);

const INSTANCES: &[(&str, &str)] = &[
    (
        "metros_4_e2_968_e3_931_000",
        include_str!("../../../tests/fixtures/cancel_latency/metros_4_e2_968_e3_931_000.smt2"),
    ),
    (
        "tte_synchro.sm_clock_distance_strict_000",
        include_str!(
            "../../../tests/fixtures/cancel_latency/tte_synchro.sm_clock_distance_strict_000.smt2"
        ),
    ),
    (
        "om1_with_relays_agreement_000",
        include_str!("../../../tests/fixtures/cancel_latency/om1_with_relays_agreement_000.smt2"),
    ),
    (
        "s_multipl_12_000",
        include_str!("../../../tests/fixtures/cancel_latency/s_multipl_12_000.smt2"),
    ),
];

enum LaneOutcome {
    /// The engine returned before the cancellation point.
    FinishedEarly(&'static str),
    /// Returned `latency` after the group was cancelled.
    Cancelled(Duration, &'static str),
    /// Still running `STRAGGLER_WAIT` after cancellation (thread detached).
    Straggler,
}

fn run_lane_and_cancel(config: EngineConfig, problem: ChcProblem) -> LaneOutcome {
    let group = CancellationToken::new();
    let lane = group.child();
    let group_interrupt = group.interrupt_flag();
    let (tx, rx) = mpsc::channel();
    let handle = PortfolioSolver::spawn_solver_thread(move || {
        let _deadline = crate::smt::ScopedSolveDeadline::new(Some(
            ay_core::time::Instant::now() + Duration::from_secs(600),
        ));
        let _lane =
            crate::smt::ScopedLaneCancellation::install(lane.clone(), Some(group_interrupt));
        let mut config = config;
        config.inject_cancellation_token(lane);
        let result = run_engine(config, problem, 0, false);
        let _ = tx.send((Instant::now(), result.summary()));
    })
    .expect("spawn engine lane");

    if let Ok((_, summary)) = rx.recv_timeout(RUN_BEFORE_CANCEL) {
        handle.join().expect("engine lane");
        return LaneOutcome::FinishedEarly(summary);
    }
    let cancelled_at = Instant::now();
    group.cancel();
    match rx.recv_timeout(STRAGGLER_WAIT) {
        Ok((finished_at, summary)) => {
            handle.join().expect("engine lane");
            LaneOutcome::Cancelled(finished_at.saturating_duration_since(cancelled_at), summary)
        }
        Err(_) => {
            drop(handle);
            LaneOutcome::Straggler
        }
    }
}

/// The production engine roster for `problem`: the full default roster plus
/// the configurations the learned selector picks for this instance.
fn engine_roster(problem: &ChcProblem) -> Vec<EngineConfig> {
    let mut roster = EngineSelector::default_engines();
    let features = crate::portfolio::features::ChcFeatureExtractor::extract(problem);
    roster.extend(EngineSelector::select(&features).engines);
    roster
}

#[test]
fn every_engine_returns_promptly_after_mid_run_cancellation() {
    let mut offenders = Vec::new();
    for (name, text) in &INSTANCES[..MEASURED_INSTANCES] {
        let parsed = ChcParser::parse(text).expect("fixture parses");
        let portfolio = PortfolioSolver::new(
            parsed,
            PortfolioConfig {
                enable_preprocessing: true,
                ..PortfolioConfig::default()
            },
        );
        let problem = portfolio.engine_problem().clone();
        for config in engine_roster(&problem) {
            let engine = config.name();
            match run_lane_and_cancel(config, problem.clone()) {
                LaneOutcome::FinishedEarly(summary) => {
                    eprintln!("CANCEL-LATENCY {name} {engine}: finished before cancel ({summary})");
                }
                LaneOutcome::Cancelled(latency, summary) => {
                    eprintln!(
                        "CANCEL-LATENCY {name} {engine}: returned {:.3}s after cancel ({summary})",
                        latency.as_secs_f64()
                    );
                    if latency > MAX_CANCEL_LATENCY {
                        offenders.push(format!("{name}/{engine}: {latency:?}"));
                    }
                }
                LaneOutcome::Straggler => {
                    eprintln!(
                        "CANCEL-LATENCY {name} {engine}: STILL RUNNING {STRAGGLER_WAIT:?} after cancel"
                    );
                    offenders.push(format!("{name}/{engine}: > {STRAGGLER_WAIT:?}"));
                }
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "engines exceeding {MAX_CANCEL_LATENCY:?} after mid-run cancellation: {offenders:#?}"
    );
}
