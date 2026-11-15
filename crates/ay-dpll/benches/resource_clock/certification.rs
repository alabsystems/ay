// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! T-b (P4a.1): a certified verdict is a function of the query and its
//! counts, never of the host's speed.
//!
//! Each fixture runs twice with an `:rlimit` and a far backstop: once as it
//! is, and once on a "slow host", made by the
//! determinism seam `ay_core::resource::test_seams::delay_each_round_trip`,
//! which sleeps about twenty times a round trip's own cost INSIDE every
//! DPLL(T) split-loop round trip. A sleep there reaches every clock the solver
//! reads (a sleep at a stop poll would reach none), while every count it keeps
//! is unchanged. The two runs must agree on everything certification decides:
//! the result, the `Unknown` reason, the discharge arm that corroborated the
//! `unsat` (`cert.unsat_corroboration`), the certification pool's spend
//! (`cert.discharge_effort_spent`), the conflicts, and, under
//! `:produce-proofs`, the strict verdict of the exported proof artifact.
//!
//! The fixtures are deductive-checks obligations whose refutations lean on `trust`
//! steps, so their certification runs the deferred-trust discharge: the
//! forged-UNSAT guard, step (3)'s per-clause lanes on the pool (the refutation
//! loop draws there; the set-fold frame's step (3) declines its first clause
//! at `check_bv_clause`), and step (4a)'s entailment question, which accepts.
//! That needs the discharge to be
//! eligible, i.e. no explicit proof demand (proof mode requires a strict
//! presentation and never enters the discharge); the proof-mode run checks
//! that its verdict, a deterministic refusal, does not move either.
//!
//! The negative control runs the slow host with backstops that land inside the
//! run: whatever they cut, the outcome is the verdict or a STOP (`timeout`),
//! never a rejection (`SelfCheckRejected`, `ProofTrusted`, a `Rejected`
//! artifact verdict).
//!
//! No assertion reads wall time except to show the seam slowed a run.

use std::sync::Mutex;
use std::time::{Duration, Instant};

use ay_core::resource::{test_seams, work};
use ay_dpll::api::{Logic, Solver, StrictProofVerdict};

/// The seam is process-wide: one delay at a time.
static SEAM: Mutex<()> = Mutex::new(());

/// The outer query's own count, which the discharge divides (P4a.1).
const RLIMIT: &str = "400000";
/// Far enough that no fixture meets it at the slowdown below.
const BACKSTOP: Duration = Duration::from_secs(600);
/// The slow host's round trip costs this many idle round trips more...
const SLOWDOWN: u32 = 20;
/// ...unless that would add more than this to one run (the slowdown is then
/// smaller, still an order of magnitude).
const SLOW_RUN_ALLOWANCE: Duration = Duration::from_secs(20);

/// What certification decided, as the public API reports it.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Certified {
    result: String,
    unknown_reason: Option<String>,
    corroboration: Option<String>,
    effort_spent: Option<u64>,
    conflicts: u64,
    verdict: Option<String>,
}

struct Run {
    certified: Certified,
    /// Split-loop round trips of the whole check-sat. Reported, not compared:
    /// the first solve still has clocks of its own (outside the certification
    /// funnel), and on the set-fold frame they change its work trace on a slow
    /// host (413 round trips idle, about 410 slow) without changing anything
    /// certification decides.
    round_trips: u64,
    elapsed: Duration,
}

fn verdict_kind(verdict: &StrictProofVerdict) -> String {
    match verdict {
        StrictProofVerdict::Verified(_) => "verified".to_string(),
        StrictProofVerdict::Rejected(reason) => format!("rejected: {reason}"),
        StrictProofVerdict::Stopped(stop) => format!("stopped: {stop:?}"),
        other => format!("{other:?}"),
    }
}

/// Whether a run demands proofs (and exports the artifact).
#[derive(Clone, Copy, Debug)]
enum Proofs {
    Off,
    On,
}

fn fixture(name: &str) -> String {
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn certify(script: &str, proofs: Proofs, backstop: Duration) -> Run {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    if matches!(proofs, Proofs::On) {
        solver.set_option(":produce-proofs", "true");
    }
    solver
        .try_set_option("rlimit", RLIMIT)
        .expect("an :rlimit is accepted");
    solver.set_timeout(Some(backstop));
    solver.parse_smtlib2(script).expect("fixture parses");
    let before = work().snapshot();
    let started = Instant::now();
    let result = solver.check_sat();
    let elapsed = started.elapsed();
    let round_trips = work().snapshot().since(before).split_round_trips;
    let verdict = (result.is_unsat() && matches!(proofs, Proofs::On)).then(|| {
        solver.export_last_unsat_artifact().map_or_else(
            || "no artifact".to_string(),
            |artifact| verdict_kind(&artifact.strict_verdict),
        )
    });
    let statistics = solver.statistics();
    let certified = Certified {
        result: format!("{:?}", result.result()),
        unknown_reason: statistics.get_string("unknown.reason").map(str::to_string),
        corroboration: statistics
            .get_string("cert.unsat_corroboration")
            .map(str::to_string),
        effort_spent: statistics.get_int("cert.discharge_effort_spent"),
        conflicts: statistics.conflicts,
        verdict,
    };
    Run {
        certified,
        round_trips,
        elapsed,
    }
}

/// Run `script` idle and on the slow host; they must agree. Returns the idle
/// run's certification and the slow run, for the route and control checks.
fn idle_and_slow(name: &str, script: &str, proofs: Proofs) -> (Certified, Run, Duration) {
    test_seams::delay_each_round_trip(Duration::ZERO);
    let idle = certify(script, proofs, BACKSTOP);
    assert!(
        idle.round_trips > 0,
        "{name}: non-vacuity: the query runs split-loop round trips, so the seam slows it"
    );
    let trips = u32::try_from(idle.round_trips).unwrap_or(u32::MAX);
    let per_trip = idle.elapsed / trips;
    let delay = (per_trip * SLOWDOWN)
        .min(SLOW_RUN_ALLOWANCE / trips)
        .max(Duration::from_micros(100));
    test_seams::delay_each_round_trip(delay);
    let slow = certify(script, proofs, BACKSTOP);
    test_seams::delay_each_round_trip(Duration::ZERO);
    assert_eq!(
        idle.certified, slow.certified,
        "{name}: certification decided differently on a {SLOWDOWN}x slower host \
         (idle {:?}, slow {:?}, delay {delay:?} per round trip)",
        idle.elapsed, slow.elapsed
    );
    // Every round trip of the slow run slept: the seam did slow this run.
    let slow_trips = u32::try_from(slow.round_trips).unwrap_or(u32::MAX);
    assert!(
        slow_trips > 0 && slow.elapsed >= delay * slow_trips,
        "{name}: the seam slowed the run ({:?} for {slow_trips} round trips at {delay:?} each)",
        slow.elapsed,
    );
    eprintln!(
        "{name}: {:?}; idle {:?} ({trips} round trips), slow {:?} ({slow_trips} round trips, \
         {delay:?} each)",
        idle.certified, idle.elapsed, slow.elapsed
    );
    (idle.certified, slow, delay)
}

/// Under the slow host, backstops that land inside the run end it as the
/// verdict or as a stop, never as a rejection; at least one of them stops it.
fn a_backstop_under_load_is_a_stop(name: &str, script: &str, slow: &Run, delay: Duration) {
    let mut stopped = 0;
    for eighths in [1u32, 3, 5, 7] {
        test_seams::delay_each_round_trip(delay);
        let run = certify(script, Proofs::Off, slow.elapsed * eighths / 8);
        test_seams::delay_each_round_trip(Duration::ZERO);
        let reason = run.certified.unknown_reason.as_deref().unwrap_or("");
        assert!(
            !reason.contains("self-check-rejected") && !reason.contains("proof-trusted"),
            "{name}: a backstop at {eighths}/8 of the slow run read as a rejection: {:?}",
            run.certified
        );
        assert!(
            !run.certified
                .verdict
                .as_deref()
                .is_some_and(|verdict| verdict.starts_with("rejected")),
            "{name}: a backstop at {eighths}/8 left a rejected artifact: {:?}",
            run.certified
        );
        if run.certified.result == "Unknown" {
            assert_eq!(
                reason, "timeout",
                "{name}: a backstop at {eighths}/8 stopped the run as something other than a \
                 timeout: {:?}",
                run.certified
            );
            stopped += 1;
        }
    }
    assert!(stopped > 0, "{name}: no backstop landed inside the run");
}

/// deductive-checks's set-fold frame (`sets_rs::test_set_fold_singleton`, reduced):
/// step (3) declines, step (4a) accepts.
///
/// The refutation leans on three `trust` steps (ground facts only the
/// assertions entail), so certification runs the deferred-trust discharge.
/// Step (3) declines the first of them at `check_bv_clause`: a ground fact is
/// no standalone tautology, so its pool-drawing negated-clause solve finds a
/// model without a conflict, and step (3) stops before any nested lane runs.
/// This frame's pool spend is therefore 0, and `idle_and_slow` still requires
/// the slow host to spend the same. The non-zero pool draw is pinned on the
/// refutation loop instead. This frame drew
/// 1 only while its Bool-element read lemma
/// `(or (not (= S (const false))) (not (select S x)))` was a `Generic` trust
/// step deferred first; the strict checker now validates it as a folded
/// `ArrayRowChain` instance (`array_axiom::folded_conclusions`).
fn the_set_fold_frame_certifies_the_same_on_a_slow_host() {
    let _seam = SEAM
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let script = fixture("deductive_checks_set_fold_quantified_frame.smt2");
    let (idle, slow, delay) = idle_and_slow("set-fold frame", &script, Proofs::Off);
    assert!(idle.result.starts_with("Unsat"), "{idle:?}");
    assert_eq!(
        idle.corroboration.as_deref(),
        Some("entailment"),
        "the fixture must reach the discharge, and step (4a) must accept it: {idle:?}"
    );
    a_backstop_under_load_is_a_stop("set-fold frame", &script, &slow, delay);
}

/// deductive-checks's `push_appends_entailed` refutation loop: the obligation whose
/// certification envelope a search lane once narrowed
/// (`deductive_checks_certification_envelope.rs`). Step (3) draws from the pool,
/// step (4a) accepts: this is the fixture that pins a non-zero pool spend.
fn the_refutation_loop_certifies_the_same_on_a_slow_host() {
    let _seam = SEAM
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let script = fixture(
        "deductive_checks_certification_envelope/refutation_loop_push_appends_entailed.smt2",
    );
    let (idle, _, _) = idle_and_slow("refutation loop", &script, Proofs::Off);
    assert!(idle.result.starts_with("Unsat"), "{idle:?}");
    assert!(
        idle.corroboration.is_some() && idle.effort_spent.is_some_and(|spent| spent > 0),
        "the fixture must reach the discharge and draw from its pool: {idle:?}"
    );
}

/// Under `:produce-proofs` the same frame must present a strict proof; its
/// verdict (and exported artifact, when there is one) does not move either.
fn the_set_fold_frame_under_proofs_decides_the_same_on_a_slow_host() {
    let _seam = SEAM
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let script = fixture("deductive_checks_set_fold_quantified_frame.smt2");
    idle_and_slow("set-fold frame, proofs", &script, Proofs::On);
}

pub(super) fn run() {
    the_set_fold_frame_certifies_the_same_on_a_slow_host();
    the_refutation_loop_certifies_the_same_on_a_slow_host();
    the_set_fold_frame_under_proofs_decides_the_same_on_a_slow_host();
}
