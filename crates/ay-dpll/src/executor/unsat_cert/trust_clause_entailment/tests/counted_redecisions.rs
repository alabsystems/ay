// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The whole-problem re-decisions' round-trip counts
//! (#r30-reconfirm-slices-counted): step (4a)'s question and a closed-sentence
//! refutation each stop after exactly their count, at the same round on every
//! run, and decline without latching a stop; step (4a)'s question has no
//! clock but its cap of half the envelope, and its proof assembly runs on an
//! allowance of its own (#r30-4a-nested-assembly-count); step (4)'s re-solve
//! runs no count at all.
//! Each boundary decline is required to occur exactly one round trip past
//! its count. The original scope was historically measured still running
//! after 1025 rounds and four minutes (debug); that is provenance, not a
//! current cost assumption. A bounded family now establishes the long-enough
//! premise explicitly while original-formula positive controls remain.

use std::time::Duration;

use super::super::entailment_deadline;
use super::*;
use crate::api::proofs::CLOSED_SENTENCE_REFUTATION_ROUND_TRIPS;
use crate::counted_array_fixture::{
    outer_count_frobenius_script, preserve_lia_probe_state, OUTER_COUNT_MEMBERS,
};
use ay_core::resource::{enter_work_grant, thread_round_trips, work_grant_spent};

/// The far enclosing grant: twice the closed-sentence count, and far above
/// step (4a)'s floor.
const FAR: u64 = 2 * CLOSED_SENTENCE_REFUTATION_ROUND_TRIPS;

/// The original 12-read/sum63 UNSAT scope, retained for positive and
/// smaller-count controls. Its formerly long search was a historical fixture
/// premise; the scoped-retention solver can now finish it early.
/// This constructor does not execute check-sat, so its first-solve counters
/// remain empty and floor-based controls keep their intended setup.
fn long_unsat() -> Executor {
    let mut script = String::from("(set-logic QF_AUFLIA)\n(declare-fun a () (Array Int Int))\n");
    let reads: Vec<String> = (0..12).map(|read| format!("(select a i{read})")).collect();
    for read in &reads {
        let index = &read["(select a ".len()..read.len() - 1];
        script += &format!(
            "(declare-const {index} Int)\n\
             (assert (or (< {read} 0) (> {read} 9)))\n\
             (assert (and (<= (- 1) {read}) (<= {read} 11)))\n"
        );
    }
    script += &format!("(assert (= (+ {}) 63))\n", reads.join(" "));
    let mut exec = elaborated(&script);
    exec.last_proof = Some(trust_only_proof());
    exec
}

/// Run `body` inside the [`FAR`] enclosing grant, so a re-decision without a
/// count of its own fails on it instead of running on: what it returned and
/// the round trips it started.
fn far_bounded<T>(body: impl FnOnce() -> T) -> (T, u64) {
    let far = enter_work_grant(FAR);
    let before = thread_round_trips();
    let value = body();
    let spent = thread_round_trips() - before;
    drop(far);
    assert!(!work_grant_spent(), "every grant ends with its re-decision");
    (value, spent)
}

/// Step (4a)'s question (the fixture refuted beside a fresh literal, so only
/// the long refutation answers it) stops after its round-trip count and
/// declines on the count, not on the clock.
#[test]
fn step_4a_stops_after_its_round_trip_count() {
    let run = || {
        let mut exec = long_unsat();
        let scope = exec.ctx.assertions.clone();
        let fresh = exec
            .ctx
            .terms
            .mk_var("counted_redecision_fresh", Sort::Bool);
        let controls = exec.certification_discharge_controls();
        let count = entailment_limits(&controls)
            .max_round_trips
            .expect("step (4a) runs on a round-trip count");
        let (accepted, spent) = far_bounded(|| {
            exec.reconfirms_deferred_clause_entailment(&scope, &deferred(&[vec![fresh]]), &controls)
        });
        (accepted, spent.checked_sub(count), controls.decline_stop())
    };
    let stopped = run();
    assert_eq!(
        stopped,
        (false, Some(1), None),
        "the question runs exactly its count, declines, and latches no stop"
    );
    assert_eq!(run(), stopped, "at the same round trip every time");
}

fn frobenius_unsat(k: i64) -> Executor {
    let mut exec = elaborated(&outer_count_frobenius_script(k));
    exec.last_proof = Some(trust_only_proof());
    exec
}

/// This is a distinct raw P query, not a call to the entailment function
/// under test. Its completed cost must reach the same unchanged outer count.
fn raw_scope_exhausts_outer_count(exec: &Executor) -> bool {
    use crate::api::proofs::EffortShare;
    let _probe_state = preserve_lia_probe_state();
    let enclosing = enter_work_grant(4 * FAR);
    let controls = exec.certification_discharge_controls();
    let mut probe = Executor::new();
    probe.force_strengthenings_off();
    probe.ctx = exec.ctx.clone();
    assert!(controls
        .install_on(&mut probe, EffortShare::Reconfirm)
        .is_some());
    let before = thread_round_trips();
    probe.begin_public_solve(false);
    probe.bind_unsat_query_assumptions(&[]);
    let unknown = matches!(probe.check_sat(), Ok(result) if result.is_unknown());
    controls.settle_nested(&probe, EffortShare::Reconfirm);
    let spent = thread_round_trips() - before;
    let exhausted = work_grant_spent();
    let stop = controls.decline_stop();
    drop(controls);
    drop(enclosing);
    assert!(
        !work_grant_spent(),
        "calibration leaves no spent grant on the thread"
    );
    unknown && exhausted && spent == 4 * FAR + 1 && stop.is_none()
}

fn entailment_count_fixture() -> Executor {
    for k in OUTER_COUNT_MEMBERS {
        let mut exec = frobenius_unsat(k);
        exec.last_statistics
            .set_int("all_lanes.round_trips", 1_000_000);
        exec.last_statistics.time_seconds = 0.0;
        if raw_scope_exhausts_outer_count(&exec) {
            return exec;
        }
    }
    panic!("ANTI-VACUITY: no bounded UNSAT family exhausted the unchanged outer count");
}

#[test]
fn step_4a_redecides_the_original_scope_before_the_outer_count() {
    let mut exec = long_unsat();
    exec.last_statistics
        .set_int("all_lanes.round_trips", 1_000_000);
    exec.last_statistics.time_seconds = 0.0;
    let scope = exec.ctx.assertions.clone();
    let fresh = exec
        .ctx
        .terms
        .mk_var("counted_redecision_original_fresh", Sort::Bool);
    let enclosing = enter_work_grant(4 * FAR);
    let controls = exec.certification_discharge_controls();
    let accepted =
        exec.reconfirms_deferred_clause_entailment(&scope, &deferred(&[vec![fresh]]), &controls);
    let spent = work_grant_spent();
    let stop = controls.decline_stop();
    drop(controls);
    drop(enclosing);
    assert!(accepted, "the original 12-read/sum63 question now finishes");
    assert!(
        !spent,
        "its natural decision precedes the unchanged outer count"
    );
    assert_eq!(stop, None);
}

/// Without an envelope the question has no clock at all: a first solve whose
/// ledger is far above anything the fixture reaches and that took no time at
/// all, so only the enclosing grant can end the question, and it ends as a
/// plain decline with no stop. Counterfactual: the former slice (as long as
/// the first solve took, at least 250 ms) ended the question long before this
/// grant, as a lane-local clock that the funnel reported as `Backstop` (the
/// pin this replaces).
#[test]
fn step_4a_has_no_first_solve_slice() {
    let mut exec = entailment_count_fixture();
    exec.last_statistics
        .set_int("all_lanes.round_trips", 1_000_000);
    exec.last_statistics.time_seconds = 0.0;
    let scope = exec.ctx.assertions.clone();
    let fresh = exec
        .ctx
        .terms
        .mk_var("counted_redecision_slice_fresh", Sort::Bool);
    // Entered before the envelope, so its Certify node hangs below it and the
    // enclosing grant bounds the question whatever its own count.
    let enclosing = enter_work_grant(4 * FAR);
    let controls = exec.certification_discharge_controls();
    let accepted =
        exec.reconfirms_deferred_clause_entailment(&scope, &deferred(&[vec![fresh]]), &controls);
    let stop = controls.decline_stop();
    let enclosing_spent = work_grant_spent();
    drop(controls);
    drop(enclosing);
    assert!(!accepted);
    assert!(enclosing_spent, "only the enclosing grant ended it");
    assert_eq!(
        stop, None,
        "a spent count is a plain decline, never a clock"
    );
}

/// The cap: half of what remains of the certification envelope, so step (4)
/// keeps the other half, and none without an envelope. It reads no duration
/// of the first solve. Counterfactual: with no cap (the envelope's backstop
/// as the question's deadline), `storeeq_7373_0236` at `--timeout 4000` and
/// `aufl_7373_00096` at `--timeout 2000` publish `unknown` (release), where
/// the question runs its whole count and leaves step (4) nothing.
#[test]
fn the_cap_is_half_of_what_remains_of_the_envelope() {
    let now = Instant::now();
    let seconds = Duration::from_secs;
    assert_eq!(entailment_deadline(now, None), None);
    assert_eq!(
        entailment_deadline(now, Some(now + seconds(4))),
        Some(now + seconds(2))
    );
    assert_eq!(
        entailment_deadline(now + seconds(1), Some(now + seconds(4))),
        Some(now + Duration::from_millis(2_500))
    );
    assert_eq!(
        entailment_deadline(now + seconds(1), Some(now)),
        Some(now + seconds(1)),
        "a passed backstop leaves no time"
    );

    let clauses: [Vec<TermId>; 0] = [];
    let capped = super::super::EntailmentQuestion {
        clauses: &clauses,
        deadline: Some(now + seconds(2)),
    };
    assert_eq!(
        capped.deadline_within(Some(now + seconds(4))),
        Some(now + seconds(2))
    );
    assert_eq!(
        capped.deadline_within(Some(now + seconds(1))),
        Some(now + seconds(1)),
        "never later than the backstop"
    );
    let uncapped = super::super::EntailmentQuestion {
        clauses: &clauses,
        deadline: None,
    };
    assert_eq!(uncapped.deadline_within(None), None);
}

/// A separate exact-query cost premise, with the SAME scope, fresh literal,
/// eligibility and structural screen as the tested question. Only the lane
/// cap is absent: the original four-second outer backstop remains intact.
/// Each attempt owns its own envelope. Returning a fixture carries DATA only;
/// its proof, clauses, controls and heuristic state are not reused.
fn wall_cap_fixture() -> Executor {
    for k in OUTER_COUNT_MEMBERS {
        let reaches_outer_backstop = {
            let _probe_state = preserve_lia_probe_state();
            let mut probe_owner = frobenius_unsat(k);
            probe_owner
                .last_statistics
                .set_int("all_lanes.round_trips", 1_000_000);
            let scope = probe_owner.ctx.assertions.clone();
            let fresh = probe_owner
                .ctx
                .terms
                .mk_var("counted_redecision_cap_fresh", Sort::Bool);
            let deferred = deferred(&[vec![fresh]]);
            let backstop = Instant::now() + Duration::from_secs(4);
            probe_owner.certification_deadline.set(Some(backstop));
            let controls = probe_owner.certification_discharge_controls();
            assert!(!ay_nia::is_integer_unit_conjunction(
                &probe_owner.ctx.terms,
                &scope
            ));
            let clauses = probe_owner
                .entailment_eligible_clauses(&scope, &deferred)
                .expect("the fixed array question is genuinely eligible");
            let uncapped_question = super::super::EntailmentQuestion {
                clauses: &clauses,
                deadline: None,
            };
            let accepted = probe_owner
                .reconfirm_unsat_within(
                    &scope,
                    Some(&uncapped_question),
                    entailment_limits(&controls),
                    &controls,
                    false,
                    super::super::super::ReconfirmationReading::EitherClass,
                )
                .is_some();
            !accepted
                && controls.observed_stop() == Some(EnvelopeStop::Backstop)
                && controls.decline_stop() == Some(EnvelopeStop::Backstop)
        };
        if reaches_outer_backstop {
            // Rebuild the exact data after the calibration's heuristic guard
            // dropped. Never reset/refund consumed thread work or reuse its
            // expired envelope, proof, solver state or accepting authority.
            return frobenius_unsat(k);
        }
    }
    panic!("ANTI-VACUITY: no bounded eligible question reached the unchanged four-second backstop");
}

/// With an envelope, the question stops at its cap, half of what remained of
/// the envelope: a lane-local clock (no latched stop, `Backstop` on a
/// decline), and the backstop has not passed when it returns, so step (4)
/// keeps the other half. A distinct raw query first establishes that this
/// exact question reaches the unchanged full backstop without the lane cap;
/// a cheap completed query or a different refusal cannot admit the fixture.
/// Counterfactual: without the cap it runs into the backstop, which latches
/// `Backstop` and leaves step (4) nothing (`storeeq_7373_0236` at `--timeout
/// 4000`, release: `unsat` became `unknown`).
#[test]
fn step_4a_stops_at_half_of_what_remains_of_the_envelope() {
    let mut exec = wall_cap_fixture();
    exec.last_statistics
        .set_int("all_lanes.round_trips", 1_000_000);
    let scope = exec.ctx.assertions.clone();
    let fresh = exec
        .ctx
        .terms
        .mk_var("counted_redecision_cap_fresh", Sort::Bool);
    let backstop = Instant::now() + Duration::from_secs(4);
    exec.certification_deadline.set(Some(backstop));
    let controls = exec.certification_discharge_controls();
    let accepted =
        exec.reconfirms_deferred_clause_entailment(&scope, &deferred(&[vec![fresh]]), &controls);
    let before_backstop = Instant::now() < backstop;
    assert!(!accepted);
    assert!(before_backstop, "the cap, not the backstop, ended it");
    assert_eq!(controls.observed_stop(), None, "the backstop never fired");
    assert_eq!(
        controls.decline_stop(),
        Some(EnvelopeStop::Backstop),
        "a question the cap ended is a lane-local clock"
    );
}

/// The limits of step (4a)'s question with `observations` of assembly.
fn with_assembly(
    controls: &crate::api::proofs::TrustClauseDischargeControls,
    observations: Option<u64>,
) -> super::super::super::FreshReconfirmationLimits {
    super::super::super::FreshReconfirmationLimits {
        max_assembly_observations: observations,
        ..entailment_limits(controls)
    }
}

/// A spent assembly allowance (#r30-4a-nested-assembly-count) is a plain
/// decline: over an UNSATISFIABLE scope, where the question succeeds on its
/// counts, an allowance of no observation declines it, latches no stop, and
/// does so on every run. The allowance is the question's count, not the
/// clock's: the same question with its own allowance accepts.
#[test]
fn a_spent_assembly_allowance_is_a_plain_decline() {
    let (exec, problem, p) = contradictory_scope();
    let clauses = [vec![p]];
    let question = super::super::EntailmentQuestion {
        clauses: &clauses,
        deadline: None,
    };
    let run = |observations: Option<u64>| {
        let controls = exec.certification_discharge_controls();
        let accepted = exec
            .reconfirm_unsat_within(
                &problem,
                Some(&question),
                with_assembly(&controls, observations),
                &controls,
                false,
                super::super::super::ReconfirmationReading::EitherClass,
            )
            .is_some();
        (accepted, controls.decline_stop())
    };
    let own = entailment_limits(&exec.certification_discharge_controls());
    assert_eq!(run(own.max_assembly_observations), (true, None));
    assert_eq!(run(Some(0)), (false, None));
    assert_eq!(run(Some(0)), (false, None), "the same decline every time");
}

/// Why the decline above is the caller's: a spent allowance ends the nested
/// assembly with the fail-closed poison, the check still answers `unsat`,
/// and the poison's lone `trust` step is a rejection the re-decisions'
/// structural screen accepts as its entry condition. Counterfactual: without
/// `check_within_counts` reporting the spend, step (4a) would accept a
/// re-decision whose proof it never built.
#[test]
fn a_spent_allowance_leaves_a_poison_the_screen_would_accept() {
    let mut exec = elaborated(
        "(set-logic QF_LRA)
         (set-option :produce-proofs true)
         (declare-const x Real)
         (declare-const y Real)
         (assert (< x y))
         (assert (< y x))",
    );
    let controls = exec.certification_discharge_controls();
    let limits = with_assembly(&controls, Some(0));
    let (verdict, spent) =
        super::super::super::redecision_counts::check_within_counts(&mut exec, limits, &controls);
    assert!(
        matches!(verdict, Ok(ref result) if result.is_unsat()),
        "{verdict:?}"
    );
    let spent = spent.expect("the assembly spent its allowance of none");
    assert_eq!(spent.granted, 0);
    assert!(spent.observed > 0);
    let proof = exec.last_proof.clone().expect("the poison is installed");
    assert_eq!(proof.steps.len(), 1, "the fail-closed poison: {proof:?}");
    let rejection = exec
        .check_proof_strict_with_datatypes(&proof)
        .expect_err("the poison is a trust step");
    assert!(Executor::is_deferred_discharge_rejection(&rejection));
}

/// A stop an enclosing allowance makes is reported as the re-decision's
/// spend too: the check's own allowance is far from spent, but its assembly
/// stopped on a count all the same. Counterfactual: reading only its own
/// grant, `check_within_counts` reports nothing and the poison reaches the
/// screen above.
#[test]
fn an_enclosing_spent_allowance_is_reported_too() {
    let mut exec = elaborated(
        "(set-logic QF_LRA)
         (set-option :produce-proofs true)
         (declare-const x Real)
         (declare-const y Real)
         (assert (< x y))
         (assert (< y x))",
    );
    let controls = exec.certification_discharge_controls();
    let limits = with_assembly(&controls, Some(1_000_000));
    let enclosing = crate::executor::proof::assembly_observations::enter_allowance(0);
    let (verdict, spent) =
        super::super::super::redecision_counts::check_within_counts(&mut exec, limits, &controls);
    drop(enclosing);
    assert!(
        matches!(verdict, Ok(ref result) if result.is_unsat()),
        "{verdict:?}"
    );
    let spent = spent.expect("the enclosing allowance stopped the assembly");
    assert_eq!(spent.granted, 1_000_000);
    assert!(spent.observed <= spent.granted);
}

/// Step (4)'s re-solve runs no round-trip count: it re-decides the whole
/// problem in a fresh layout, so its rounds are not proportional to the first
/// solve's, and it is the funnel's last accepting step (`redecision`). Here
/// the first solve recorded 50 round trips, as on the generated
/// `sem2_arithidx`-shaped file whose re-solve accepts after 1236, and the
/// re-solve runs until the far enclosing grant stops it. Counterfactual: a
/// grant of the larger of 512 and four first solves stops it after 513, and
/// turned that file's `unsat` into `unknown`.
#[test]
fn step_4_runs_no_round_trip_count() {
    let mut exec = long_unsat();
    exec.last_statistics.set_int("all_lanes.round_trips", 50);
    let scope = exec.ctx.assertions.clone();
    let controls = exec.certification_discharge_controls();
    let (accepted, spent) = far_bounded(|| {
        exec.reconfirms_unsat_under(&scope, WHOLE_PROBLEM_RECONFIRMATION_LIMITS, &controls)
    });
    assert_eq!(
        (accepted, spent, controls.decline_stop()),
        (false, FAR + 1, None)
    );
}

/// A closed-sentence certificate's refutation runs inside a search, with no
/// finished first solve to measure, and stops after its fixed count.
#[test]
fn a_closed_sentence_refutation_stops_after_its_count() {
    let exec = long_unsat();
    let scope = exec.ctx.assertions.clone();
    assert_eq!(
        far_bounded(|| exec.reconfirm_negation_refuted_for_closed_sentence(&scope)),
        (None, CLOSED_SENTENCE_REFUTATION_ROUND_TRIPS + 1)
    );
}
