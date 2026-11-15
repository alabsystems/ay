// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A same-context probe under a counted grant (#deterministic-probe-metering).
//!
//! The wall-metered probe stopped wherever its grant's clock ran out, so the
//! terms it minted on the shared store, and every later solve of the query,
//! depended on host load. These tests pin the counted grant: it stops the
//! probe at the same round trip every time, with the wall backstop far away;
//! the metered lane hands its claimed count to the probe; and the grant ends
//! with the probe, recording no stop on the enclosing executor. They also pin
//! `ay_lia`'s per-thread probe trajectory state to the query: reset at the
//! external boundary, left as found by a probe.

use ay_core::resource::{thread_round_trips, work_grant_spent};
use ay_core::TermId;
use ay_frontend::parse;

use super::ProbeCap;
use crate::counted_array_fixture::frobenius_script;
use crate::executor::quantifier_loop::result_mapping::{
    SameContextProbeOutcome, SameContextWindow,
};
use crate::Executor;

/// Three array reads, each outside `[0, 4]` but inside `[-2, 6]`, summing
/// to 6: unsat, and the lazy array/arithmetic loop needs several theory
/// conflicts to see it (14 split-loop round trips as a plain query).
const ARRAY_READS: &str = "(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-const i Int)(declare-const j Int)(declare-const k Int)
(assert (or (< (select a i) 0) (> (select a i) 4)))
(assert (or (< (select a j) 0) (> (select a j) 4)))
(assert (or (< (select a k) 0) (> (select a k) 4)))
(assert (= (+ (select a i) (select a j) (select a k)) 6))
(assert (and (<= (- 2) (select a i)) (<= (select a i) 6)
             (<= (- 2) (select a j)) (<= (select a j) 6)
             (<= (- 2) (select a k)) (<= (select a k) 6)))";

/// A wall backstop no probe here comes near, so only the count can stop one.
const FAR_WALL_MS: u64 = 600_000;

fn array_reads_executor() -> (Executor, Vec<TermId>) {
    array_reads_executor_for(ARRAY_READS)
}

fn array_reads_executor_for(script: &str) -> (Executor, Vec<TermId>) {
    let mut exec = Executor::new();
    exec.execute_all(&parse(script).expect("parse"))
        .expect("execute");
    let roots = exec.ctx.assertions.clone();
    (exec, roots)
}

/// One probe over the array-read roots on a fresh executor: its outcome and the
/// split-loop round trips it started.
fn probe(work_round_trips: Option<u64>) -> (SameContextProbeOutcome, u64) {
    probe_for(ARRAY_READS, work_round_trips)
}

fn probe_for(script: &str, work_round_trips: Option<u64>) -> (SameContextProbeOutcome, u64) {
    let (mut exec, roots) = array_reads_executor_for(script);
    let before = thread_round_trips();
    let outcome = exec.checked_same_context_unsat_proof(
        &roots,
        SameContextWindow::Ground,
        Some(FAR_WALL_MS),
        work_round_trips,
        true,
    );
    let spent = thread_round_trips() - before;
    assert!(
        !work_grant_spent(),
        "the counted grant must end with the probe"
    );
    assert!(
        !exec.should_abort_theory_loop(),
        "the enclosing executor must be free to keep solving after the probe"
    );
    (outcome, spent)
}

fn refuted(outcome: &SameContextProbeOutcome) -> bool {
    matches!(
        outcome,
        SameContextProbeOutcome::Proof(_) | SameContextProbeOutcome::UnsatUnpromotable
    )
}

#[test]
fn a_counted_grant_stops_the_probe_at_the_same_round_trip_every_time() {
    let (free, needed) = probe(None);
    assert!(
        refuted(&free),
        "the ungranted probe refutes the array reads"
    );
    assert!(
        needed >= 3,
        "ANTI-VACUITY: the refutation must need several split rounds, or no grant \
         below it can be tested (needed {needed})"
    );

    let grant = needed - 2;
    let (cut, spent) = probe(Some(grant));
    assert!(
        matches!(cut, SameContextProbeOutcome::Other),
        "a grant two round trips short of the refutation must stop the probe"
    );
    assert_eq!(
        spent,
        grant + 1,
        "the probe runs exactly its granted round trips and stops at the next"
    );
    let (again, spent_again) = probe(Some(grant));
    assert!(matches!(again, SameContextProbeOutcome::Other));
    assert_eq!(
        spent_again, spent,
        "the same grant stops at the same round trip"
    );
}

/// Negative twin: a grant covering the whole refutation changes nothing, so
/// the count is what stopped the probe above, not the backstop or the grant's
/// mere presence.
#[test]
fn a_counted_grant_that_covers_the_refutation_admits_it() {
    let (free, needed) = probe(None);
    assert!(refuted(&free));
    let (granted, spent) = probe(Some(needed));
    assert!(
        refuted(&granted),
        "a grant of exactly the work needed admits it"
    );
    assert_eq!(spent, needed);
}

#[test]
fn an_external_query_starts_from_a_clean_lia_probe_state() {
    let earlier_query = ay_lia::probe_state_for_tests(vec![(TermId(1), TermId(2))], 9, 400);
    ay_lia::restore_probe_state(earlier_query);
    let mut exec = Executor::new();
    exec.begin_external_decision_query(false);
    assert_eq!(
        ay_lia::save_probe_state(),
        ay_lia::probe_state_for_tests(Vec::new(), 0, 0),
        "a query must not inherit the probe state an earlier query left on this thread"
    );
}

/// A QF_UFLIA refutation whose LIA side runs a shared-equality probe, which
/// writes `ay_lia`'s per-thread fail streak (`f(a) + 1 = f(b)` with `a = b`
/// forced by bounds).
const UFLIA_SHARED_PROBE: &str = "(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)(declare-const b Int)(declare-const c Int)
(assert (<= a b))(assert (<= b a))(assert (= c (+ (f a) 1)))(assert (= c (f b)))";

fn uflia_shared_probe_executor() -> Executor {
    let mut exec = Executor::new();
    exec.execute_all(&parse(UFLIA_SHARED_PROBE).expect("parse"))
        .expect("execute");
    exec
}

#[test]
fn a_same_context_probe_leaves_the_enclosing_lia_probe_state_as_found() {
    let enclosing = ay_lia::probe_state_for_tests(vec![(TermId(1), TermId(2))], 3, 7);
    // ANTI-VACUITY: the same problem solved in place (`check_sat` does not
    // cross the external boundary, so nothing resets the state first)
    // rewrites the state, so the probe below has something to leave intact.
    ay_lia::restore_probe_state(enclosing.clone());
    let mut plain = uflia_shared_probe_executor();
    let _ = plain.check_sat();
    assert_ne!(
        ay_lia::save_probe_state(),
        enclosing,
        "ANTI-VACUITY: the fixture must write the ay_lia probe state"
    );
    let mut exec = uflia_shared_probe_executor();
    let roots = exec.ctx.assertions.clone();
    ay_lia::restore_probe_state(enclosing.clone());
    let outcome = exec.checked_same_context_unsat_proof(
        &roots,
        SameContextWindow::Ground,
        Some(FAR_WALL_MS),
        None,
        true,
    );
    assert!(refuted(&outcome));
    assert_eq!(
        ay_lia::save_probe_state(),
        enclosing,
        "the probe decides another problem and must leave the enclosing state as found"
    );
}

/// The counted grant is the PROBE's alone: a probe it stops must leave no
/// stop recorded on the enclosing executor, or every later probe of the query
/// (the whole-set probe after a cut anchored one, `anchored_replay_open`)
/// would be refused. Asserted on the executor's recorded stop state, which a
/// grant scope that outlived the probe's closure would write through the
/// enclosing executor's own post-probe stop poll.
#[test]
fn a_probe_stopped_by_its_grant_records_no_stop_on_the_enclosing_executor() {
    let (_, needed) = probe(None);
    let (mut exec, roots) = array_reads_executor();
    let reason_before = exec.last_unknown_reason;
    let result_before = exec.last_result.clone();
    let outcome = exec.checked_same_context_unsat_proof(
        &roots,
        SameContextWindow::Ground,
        Some(FAR_WALL_MS),
        Some(needed - 2),
        true,
    );
    assert!(matches!(outcome, SameContextProbeOutcome::Other));
    assert_eq!(
        exec.last_unknown_reason, reason_before,
        "the probe's spent grant must not record a stop on the enclosing executor"
    );
    assert_eq!(exec.last_result, result_before);
}

/// One metered, window-scoped probe over the array-read roots on a fresh
/// executor and envelope: its proof, the split-loop round trips it started,
/// and the round trips the envelope still counts as granted afterwards.
fn metered_probe(round_trips: u64) -> (Option<ay_core::Proof>, u64, u64) {
    metered_probe_for(ARRAY_READS, round_trips)
}

fn metered_probe_for(script: &str, round_trips: u64) -> (Option<ay_core::Proof>, u64, u64) {
    let (mut exec, roots) = array_reads_executor_for(script);
    let cap = ProbeCap {
        wall_ms: 5_000,
        round_trips,
    };
    let before = thread_round_trips();
    let proof = exec.metered_scoped_consequence_replay_probe(&roots, cap);
    let spent = thread_round_trips() - before;
    (
        proof,
        spent,
        exec.consequence_replay_probe_round_trips_granted().0,
    )
}

/// Calibration is finite and stricter than the original uncounted setup:
/// at most three fresh probes, each with 64 round trips. A selected member
/// must yield a real proof within that ceiling, not merely return Unknown.
/// checked_same_context_unsat_proof already preserves the enclosing LIA state.
fn claim_floor_fixture() -> (String, u64) {
    for k in [2, 3, 4] {
        let script = frobenius_script(k);
        let (outcome, needed) = probe_for(&script, Some(64));
        if matches!(outcome, SameContextProbeOutcome::Proof(_)) && (10..=64).contains(&needed) {
            return (script, needed);
        }
    }
    panic!("ANTI-VACUITY: no bounded proof clears the unchanged claim floor of 8");
}

#[test]
fn the_claim_floor_family_admits_its_proof_when_the_claim_covers_it() {
    let (script, needed) = claim_floor_fixture();
    let (proof, spent, still_granted) = metered_probe_for(&script, needed.max(8));
    assert!(
        proof.is_some(),
        "the selected family has a real proof inside its full claim"
    );
    assert_eq!(spent, needed);
    assert_eq!(still_granted, needed, "only unused work is refunded");
}

/// The production wiring, not only the mechanism: the metered lane runs its
/// probe under the count it CLAIMED, so a claim two round trips short of the
/// refutation stops the probe at exactly that count, however far away the
/// wall backstop is, and a probe stopped by its count refunds nothing.
#[test]
fn the_metered_lane_stops_its_probe_at_the_claimed_count() {
    let (script, needed) = claim_floor_fixture();
    let grant = needed - 2;
    assert!(
        grant >= 8,
        "ANTI-VACUITY: the claim must clear the counted floor (needed {needed})"
    );
    let (proof, spent, still_granted) = metered_probe_for(&script, grant);
    assert!(
        proof.is_none(),
        "a claim short of the refutation yields no proof"
    );
    assert_eq!(
        spent,
        grant + 1,
        "the metered probe stops at its claimed count, not at its wall backstop"
    );
    assert_eq!(
        still_granted, grant,
        "a probe stopped by its count refunds nothing"
    );
}

/// Negative twin: a claim covering the refutation admits exactly what the
/// ungranted probe found, and the envelope gets back the part of the claim the
/// probe did not use.
#[test]
fn the_metered_lane_admits_a_refutation_inside_its_count() {
    let (free, needed) = probe(None);
    assert!(
        matches!(free, SameContextProbeOutcome::Proof(_)),
        "the ungranted probe proves the array reads"
    );
    let (proof, spent, still_granted) = metered_probe(needed.max(8));
    assert!(
        proof.is_some(),
        "a claim covering the refutation admits its proof"
    );
    assert_eq!(spent, needed);
    assert_eq!(
        still_granted, needed,
        "the unused part of the claim is refunded"
    );
}
