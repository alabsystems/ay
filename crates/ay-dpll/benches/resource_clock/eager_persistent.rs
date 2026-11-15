// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! P4a (T2): a QF_LRA check-sat that carries `:rlimit` and runs on the
//! eager-persistent split-loop arm is decided by counts, never by the host's
//! speed.
//!
//! Each fixture runs twice with an `:rlimit` and a far backstop: once as it
//! is, and once on a "slow host" made by both determinism seams of
//! `ay_core::resource::test_seams`. One sleeps about twenty times a round
//! trip's idle cost inside every split-loop round trip (the arm counts its
//! round trips at the top of each round); the other sleeps about twenty times a
//! stop poll's idle cost inside every executor stop poll (`work_grant_spent`,
//! polled thousands of times per second by these fixtures' SAT searches). The
//! two runs must agree on everything the arm decides: the
//! result, the `Unknown` reason, the conflicts, the decisions, the split
//! loop's round trips, the searches it drew an allowance for, the rounds its
//! own slice stopped, and the model.
//!
//! The fixtures are SMT-LIB 2025 QF_LRA benchmarks, verbatim
//! (`non-incremental/QF_LRA/sc/`, SMT-LIB release 2025, Zenodo 15493090), the
//! synchronizer circuits the arm's #8399 stall escalation was written for:
//! `sc-8.induction2` (sat, 7 split-loop round trips) and `sc-5.base` (unsat,
//! 4). Both need splits after the first round, and at the arm's own slice
//! sizes every round ends on a split: neither makes the decisions a slice
//! allows. So `sc-8.induction2` also runs with its slices divided by
//! [`SLICE_DIVISOR`] (`test_seams::shrink_round_slices`): then rounds end on
//! their own slices and the next round resumes or continues the search, the
//! path a counted slice exists for, on the same counts. (No small SMT-LIB
//! QF_LRA file reaches that path quickly through this API: of 196 that the
//! CLI solves or stops within 20 s, the one with a slice stop within 10 s
//! here was still unsolved at 10 s, and `sc-15.induction`, which the CLI
//! solves in 4 s after one slice stop, takes a minute here.)
//!
//! The backstop control runs the sliced run on the slow host with backstops
//! that land inside it: whatever they cut ends as the verdict or as a STOP
//! (`timeout`), never as an incomplete search, a `resourceout`, or another
//! verdict, also when the cut lands right after a round its slice stopped.
//!
//! No assertion reads wall time except to show the seams slowed a run.

use std::sync::{Mutex, MutexGuard, PoisonError};
use std::time::{Duration, Instant};

use ay_core::resource::{test_seams, work};
use ay_dpll::api::{Logic, Solver};

/// The seams are process-wide: one slow host at a time.
static SEAM: Mutex<()> = Mutex::new(());

/// The seams, held by one test, and all switched off again when it ends,
/// however it ends.
struct Seams {
    _held: MutexGuard<'static, ()>,
}

impl Drop for Seams {
    fn drop(&mut self) {
        switch_the_seams_off();
    }
}

fn seams() -> Seams {
    let held = SEAM.lock().unwrap_or_else(PoisonError::into_inner);
    switch_the_seams_off();
    Seams { _held: held }
}

fn switch_the_seams_off() {
    test_seams::delay_each_round_trip(Duration::ZERO);
    test_seams::delay_each_stop_poll(Duration::ZERO);
    test_seams::shrink_round_slices(1);
}

/// Far above any fixture's conflicts, so it bounds without deciding.
const RLIMIT: &str = "400000";
/// What the sliced run divides the arm's slices by: `sc-8.induction2`'s
/// second round then gets 21 decisions (700 ms at 32 decisions per ms, over
/// 1,024) and a resumed round 937, where its whole run makes about 12,000;
/// eight of its rounds then end on their own slices.
const SLICE_DIVISOR: u64 = 1024;
/// The historical BCP regression size and the forced slice-stop size.
const RESUME_DIVISORS: [u64; 2] = [64, SLICE_DIVISOR];
/// Far enough that no fixture meets it at the slowdown below.
const BACKSTOP: Duration = Duration::from_secs(600);
/// The slow host's round trips and stop polls each cost this many times
/// their idle share...
const SLOWDOWN: u32 = 20;
/// ...unless that would add more than this to one run per seam (the slowdown
/// is then smaller, still an order of magnitude).
const SLOW_RUN_ALLOWANCE: Duration = Duration::from_secs(20);

/// What the arm decided, as the public API reports it.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Decided {
    result: String,
    unknown_reason: Option<String>,
    conflicts: u64,
    decisions: u64,
    /// The split loop's own round trips (`dpll.round_trips`).
    round_trips: u64,
    /// Searches the arm drew a fresh allowance for.
    searches: u64,
    /// Rounds the counted slice stopped.
    slice_stops: u64,
    model: Option<String>,
}

struct Run {
    decided: Decided,
    /// Every split-loop round trip the process ran during the check-sat, the
    /// nested executors that certify an `unsat` included. Reported, not
    /// compared: those executors are not this arm and keep clocks of their
    /// own (P4a.1's noted residual, T2's check-wide ticks); on `sc-5.base`
    /// this count moved between two IDLE runs in one process (15, 11) while
    /// the split loop's own stayed at 4.
    check_round_trips: u64,
    stop_polls: u64,
    elapsed: Duration,
}

fn fixture(name: &str) -> String {
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/eager_persistent")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn solve(script: &str, backstop: Duration) -> Run {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver
        .try_set_option("rlimit", RLIMIT)
        .expect("an :rlimit is accepted");
    solver.set_timeout(Some(backstop));
    solver.parse_smtlib2(script).expect("fixture parses");
    let before = work().snapshot();
    let polls_before = test_seams::stop_polls();
    let started = Instant::now();
    let result = solver.check_sat();
    let elapsed = started.elapsed();
    let check_round_trips = work().snapshot().since(before).split_round_trips;
    let stop_polls = test_seams::stop_polls().saturating_sub(polls_before);
    let model = result.is_sat().then(|| {
        solver
            .try_get_model_str()
            .unwrap_or_else(|e| format!("no model: {e:?}"))
    });
    let statistics = solver.statistics();
    let decided = Decided {
        result: format!("{:?}", result.result()),
        unknown_reason: statistics.get_string("unknown.reason").map(str::to_string),
        conflicts: statistics.conflicts,
        decisions: statistics.decisions,
        round_trips: statistics.get_int("dpll.round_trips").unwrap_or(0),
        searches: statistics
            .get_int("dpll.eager_persistent.searches")
            .unwrap_or(0),
        slice_stops: statistics
            .get_int("dpll.eager_persistent.slice_stops")
            .unwrap_or(0),
        model,
    };
    Run {
        decided,
        check_round_trips,
        stop_polls,
        elapsed,
    }
}

/// The slow host's delays: about `SLOWDOWN` times the idle run's cost per
/// round trip and per stop poll.
#[derive(Clone, Copy, Debug)]
struct SlowHost {
    round_trip: Duration,
    stop_poll: Duration,
}

impl SlowHost {
    fn sized_by(idle: &Run) -> Self {
        let share = |count: u64| {
            let count = u32::try_from(count.max(1)).unwrap_or(u32::MAX);
            ((idle.elapsed / count) * SLOWDOWN)
                .min(SLOW_RUN_ALLOWANCE / count)
                .max(Duration::from_micros(100))
        };
        Self {
            round_trip: share(idle.check_round_trips),
            stop_poll: share(idle.stop_polls),
        }
    }

    fn run(self, script: &str, backstop: Duration) -> Run {
        test_seams::delay_each_round_trip(self.round_trip);
        test_seams::delay_each_stop_poll(self.stop_poll);
        let run = solve(script, backstop);
        test_seams::delay_each_round_trip(Duration::ZERO);
        test_seams::delay_each_stop_poll(Duration::ZERO);
        run
    }
}

/// An idle run, then a slow-host run sized by it.
fn idle_then_slow(name: &str, script: &str) -> (Run, Run, SlowHost) {
    let idle = solve(script, BACKSTOP);
    assert!(
        idle.decided.round_trips >= 3,
        "{name}: non-vacuity: the query runs at least two split rounds after the first \
         ({:?})",
        idle.decided
    );
    assert!(
        idle.stop_polls > 0,
        "{name}: non-vacuity: the query's SAT search polls its stop, so the seam slows it"
    );
    let host = SlowHost::sized_by(&idle);
    let slow = host.run(script, BACKSTOP);
    // Every round trip and stop poll of the slow run slept: the seams did
    // slow this run.
    let trips = u32::try_from(slow.check_round_trips).unwrap_or(u32::MAX);
    let polls = u32::try_from(slow.stop_polls).unwrap_or(u32::MAX);
    assert!(
        slow.elapsed >= host.round_trip * trips + host.stop_poll * polls,
        "{name}: the seams slowed the run ({:?} for {trips} round trips and {polls} stop \
         polls, {host:?})",
        slow.elapsed,
    );
    eprintln!(
        "{name}: idle {:?} {:?} ({} in the check, {} stop polls); \
         slow {:?} {:?} ({} in the check, {host:?})",
        idle.elapsed,
        idle.decided,
        idle.check_round_trips,
        idle.stop_polls,
        slow.elapsed,
        slow.decided,
        slow.check_round_trips,
    );
    (idle, slow, host)
}

/// Run `script` idle and on the slow host; they must agree. Returns the idle
/// run's decision and the slow run, for the route and control checks.
fn idle_and_slow(name: &str, script: &str) -> (Decided, Run, SlowHost) {
    let (idle, slow, host) = idle_then_slow(name, script);
    assert_eq!(
        idle.decided, slow.decided,
        "{name}: the eager-persistent arm decided differently on a slower host \
         (idle {:?}, slow {:?}, {host:?})",
        idle.elapsed, slow.elapsed
    );
    assert!(
        idle.decided.searches > 0,
        "{name}: the query ran on the eager-persistent arm ({:?})",
        idle.decided
    );
    (idle.decided, slow, host)
}

/// Under the slow host, backstops that land inside the run end it as the
/// verdict or as a stop, never as anything else; at least one of them stops
/// it.
fn a_backstop_under_load_is_a_stop(
    name: &str,
    script: &str,
    idle: &Decided,
    slow: &Run,
    host: SlowHost,
) {
    for eighths in [1u32, 3, 5, 7] {
        let run = host.run(script, slow.elapsed * eighths / 8);
        if run.decided.result == idle.result {
            continue;
        }
        assert_eq!(
            run.decided.unknown_reason.as_deref(),
            Some("timeout"),
            "{name}: a backstop at {eighths}/8 of the slow run ended it as something other \
             than its verdict or a timeout: {:?}",
            run.decided
        );
        return;
    }
    panic!("{name}: no backstop landed inside the run");
}

/// The eight-stage synchronizer's second induction step: sat after seven round
/// trips.
fn the_second_induction_step_decides_the_same_on_a_slow_host() {
    let _seams = seams();
    let script = fixture("sc-8.induction2.cvc.smt2");
    let (idle, _, _) = idle_and_slow("sc-8.induction2", &script);
    assert!(idle.result.starts_with("Sat"), "{idle:?}");
    assert!(idle.model.is_some(), "{idle:?}");
}

/// The base case of the five-stage synchronizer: unsat after four split-loop
/// round trips.
fn the_base_case_decides_the_same_on_a_slow_host() {
    let _seams = seams();
    let script = fixture("sc-5.base.cvc.smt2");
    let (idle, _, _) = idle_and_slow("sc-5.base", &script);
    assert!(idle.result.starts_with("Unsat"), "{idle:?}");
}

/// The second induction step again, with its slices divided: rounds end on
/// their own slices and the search resumes, and still decides the same on a
/// slow host. The backstop control runs here, where a cut can land right
/// after such a round.
fn rounds_their_own_slices_stopped_resume_the_same_on_a_slow_host() {
    let _seams = seams();
    let name = "sc-8.induction2 with slices over 1024";
    let script = fixture("sc-8.induction2.cvc.smt2");
    test_seams::shrink_round_slices(SLICE_DIVISOR);
    let (idle, slow, host) = idle_and_slow(name, &script);
    assert!(
        idle.slice_stops > 0,
        "{name}: non-vacuity: a round's own slice stopped its solve and the search went on \
         ({idle:?})"
    );
    assert!(
        idle.result.starts_with("Sat"),
        "{name}: the sliced search still reaches its verdict ({idle:?})"
    );
    a_backstop_under_load_is_a_stop(name, &script, &idle, &slow, host);
}

/// A round its slice stopped can stop anywhere in the SAT loop, also between
/// finding a conflict and analysing it; the round that resumes the search must
/// still see that conflict. Each fixture reaches its verdict under slices of
/// both sizes here. Before `resume_solving_with_extension` restarted above the
/// assumption prefix, `sc-8.induction2` over 64 failed ay-sat's debug check
/// "BUG [#8078]: BCP missed conflict!" (a learned clause falsified by the
/// complete assignment the resumed round reached).
pub(super) fn counted_search_reaches_verdict_at_the_bcp_regression_and_forced_slice_sizes() {
    let _seams = seams();
    let mut forced_slice_stops = 0;
    for (name, verdict) in [
        ("sc-8.induction2.cvc.smt2", "Sat"),
        ("sc-5.base.cvc.smt2", "Unsat"),
    ] {
        let script = fixture(name);
        for divisor in RESUME_DIVISORS {
            test_seams::shrink_round_slices(divisor);
            let run = solve(&script, BACKSTOP);
            assert!(
                run.decided.result.starts_with(verdict),
                "{name} with slices over {divisor}: {:?}",
                run.decided
            );
            if divisor == SLICE_DIVISOR {
                forced_slice_stops += run.decided.slice_stops;
            }
        }
    }
    assert!(
        forced_slice_stops > 0,
        "the forced size must stop a round on its own slice"
    );
}

pub(super) fn run() {
    the_second_induction_step_decides_the_same_on_a_slow_host();
    the_base_case_decides_the_same_on_a_slow_host();
    rounds_their_own_slices_stopped_resume_the_same_on_a_slow_host();
}
