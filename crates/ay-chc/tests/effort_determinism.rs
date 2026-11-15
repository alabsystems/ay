// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A CHC proof run under an effort is decided by its count (P4a slice 8,
//! the development design notes §14): on a host the slow-host seam makes about
//! twenty times slower, in every run, and with one run or eight at once in the
//! process, it gives the same result, frames, lemmas, ticks and stop.
//!
//! A binary of its own: the stop-poll seam is process-wide, and the threads
//! of the last test must not share the process with other solves. The two
//! tests take one lock for the same reason.

use std::sync::Mutex;
use std::time::{Duration, Instant};

use ay_chc::{engines, CancellationToken, ChcParser, ChcRunWork, PdrConfig};
use ay_core::resource::{test_seams, Exhausted};

/// Safe; PDR decides it in a few thousand ticks over several frames.
const DECIDED: &str = include_str!("../examples/hyperedge_safe.smt2");
/// Unsafe; PDR needs more than [`SMALL_B`] ticks to refute it.
const STOPPED: &str = include_str!("../examples/hyperedge_unsafe.smt2");

/// A budget the decided fixture finishes well within.
const LARGE_B: u64 = 50_000_000;
/// A budget the stopped fixture spends long before it refutes.
const SMALL_B: u64 = 3_000;

/// One test at a time in this process (the seams are the process's).
static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

/// What a run is compared on, and its wall time.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Outcome {
    result: String,
    accepted: bool,
    model_sha256: String,
    ticks: u64,
    frames: u64,
    lemmas: u64,
    stop: Option<Exhausted>,
    work: ChcRunWork,
}

/// One proof run of `input` under `effort`, with a backstop clock far past
/// any run here and a token nobody cancels (an embedder's: it also keeps the
/// case split, whose branches run on clocks, out of the run).
fn run(input: &str, effort: u64) -> (Outcome, Duration) {
    let problem = ChcParser::parse(input).expect("the fixture parses");
    let mut config = PdrConfig::production(false).with_effort(Some(effort));
    config.solve_timeout = Some(Duration::from_secs(600));
    config.cancellation_token = Some(CancellationToken::new());
    let started = Instant::now();
    let run = engines::solve_pdr_proof(problem, config).expect("the run runs");
    let wall = started.elapsed();
    let work = *run.work().expect("a run under an effort is metered");
    let metadata = run.metadata().to_json_value();
    let outcome = Outcome {
        result: metadata["result"].to_string(),
        accepted: run.accepted_as_proof(),
        model_sha256: run.model_artifact().sha256().to_owned(),
        ticks: work.ticks,
        frames: work.frames,
        lemmas: work.lemmas,
        stop: work.stop,
        work,
    };
    (outcome, wall)
}

/// The same run on a host about `factor` times slower: every tick charged on
/// this thread and every SAT stop poll naps, sized from the run at 1x.
fn run_slowed(input: &str, effort: u64, at_1x: Duration, ticks: u64, factor: u32) -> Outcome {
    let extra = at_1x.saturating_mul(factor - 1);
    let polls_before = test_seams::stop_polls();
    let _ = run(input, effort);
    let polls = test_seams::stop_polls() - polls_before;
    // Half of the extra on the ticks, half on the stop polls (all of it on
    // the ticks when the run makes none).
    let on_ticks = if polls == 0 { extra } else { extra / 2 };
    let picos =
        u64::try_from(on_ticks.as_nanos() * 1_000 / u128::from(ticks.max(1))).unwrap_or(u64::MAX);
    let per_poll = if polls == 0 {
        Duration::ZERO
    } else {
        extra.saturating_sub(on_ticks) / u32::try_from(polls).unwrap_or(u32::MAX)
    };
    test_seams::delay_each_tick_picos(picos);
    test_seams::delay_each_stop_poll(per_poll);
    let started = Instant::now();
    let (outcome, _) = run(input, effort);
    let slowed = started.elapsed();
    test_seams::delay_each_tick_picos(0);
    test_seams::delay_each_stop_poll(Duration::ZERO);
    assert!(
        slowed >= at_1x.saturating_mul(factor / 4),
        "the slow host is slow: {slowed:?} against {at_1x:?} at 1x"
    );
    outcome
}

#[test]
fn a_run_under_an_effort_is_the_same_on_a_slow_host() {
    let _alone = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let (decided, wall) = run(DECIDED, LARGE_B);
    assert_eq!(decided.result, "\"safe\"", "{decided:?}");
    assert!(decided.accepted && decided.stop.is_none(), "{decided:?}");
    assert!(
        decided.frames >= 2 && decided.lemmas > 0,
        "the search stepped: {decided:?}"
    );
    let slowed = run_slowed(DECIDED, LARGE_B, wall, decided.ticks, 20);
    assert_eq!(slowed, decided, "a decided run, at 20x");

    let (stopped, wall) = run(STOPPED, SMALL_B);
    assert_eq!(stopped.result, "\"unknown\"", "{stopped:?}");
    assert_eq!(stopped.stop, Some(Exhausted::Rlimit), "{stopped:?}");
    assert!(stopped.ticks >= SMALL_B, "{stopped:?}");
    let slowed = run_slowed(STOPPED, SMALL_B, wall, stopped.ticks, 20);
    assert_eq!(slowed, stopped, "a run its count stopped, at 20x");
}

#[test]
fn a_small_budget_stops_at_the_same_tick_in_every_run_and_with_eight_threads() {
    let _alone = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let (first, _) = run(STOPPED, SMALL_B);
    assert_eq!(first.stop, Some(Exhausted::Rlimit), "{first:?}");
    for _ in 1..10 {
        assert_eq!(
            run(STOPPED, SMALL_B).0,
            first,
            "ten runs, one after another"
        );
    }
    let together: Vec<Outcome> = std::thread::scope(|scope| {
        let runs: Vec<_> = (0..8)
            .map(|_| scope.spawn(|| run(STOPPED, SMALL_B).0))
            .collect();
        runs.into_iter()
            .map(|run| run.join().expect("a run thread"))
            .collect()
    });
    for outcome in together {
        assert_eq!(outcome, first, "eight runs at once in the process");
    }
}

/// Under an effort the frame, iteration and obligation caps are not armed
/// (DR-37: no count besides B): the decided fixture, which steps several
/// frames, is capped to `unknown` without an effort when its caps are one,
/// and decided with the same caps under one.
#[test]
fn an_effort_arms_no_count_cap_beside_it() {
    let _alone = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let capped = |effort: Option<u64>| {
        let problem = ChcParser::parse(DECIDED).expect("the fixture parses");
        let mut config = PdrConfig::production(false)
            .with_max_frames(1)
            .with_max_iterations(1)
            .with_max_obligations(1)
            .with_effort(effort);
        config.solve_timeout = Some(Duration::from_secs(600));
        config.cancellation_token = Some(CancellationToken::new());
        let run = engines::solve_pdr_proof(problem, config).expect("the run runs");
        run.metadata().to_json_value()["result"].to_string()
    };
    assert_eq!(
        capped(None),
        "\"unknown\"",
        "the caps bind without an effort"
    );
    assert_eq!(
        capped(Some(LARGE_B)),
        "\"safe\"",
        "and are not armed under one"
    );
}
