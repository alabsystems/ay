// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The forged-UNSAT guard's re-solve runs under a counted grant of split-loop
//! round trips (`EffortShare::Guard.round_trips()`,
//! #counted-certification-budgets).
//!
//! Its conflict share bounds each round's SAT solve, not the rounds, so
//! without the grant a re-solve of cheap rounds ran until it finished or the
//! backstop stopped it: the deductive-checks set-fold obligation's guard ran 3750
//! round trips (21.4 s on an X925 core, 38.9 s on an A725 core), and
//! deductive-checks's 30 s deadline, not a count, decided that query. These tests pin
//! the grant where the guard runs it: a re-solve longer than the grant stops
//! after exactly the granted round trips and the one that finds the grant
//! spent, on every run; the stop is a decline, never a latched stop; and a
//! re-solve the grant covers still refutes a satisfiable problem.

use ay_core::resource::{enter_work_grant, thread_round_trips, work_grant_spent};
use ay_frontend::parse;

use crate::api::proofs::{CertificationEffort, EffortShare, TrustClauseDischargeControls};
use crate::Executor;

/// Three array reads, each outside `[0, 4]` but inside `[-2, 6]`, summing to
/// 9: satisfiable only by reads `{5, 5, -1}` in some order, and the lazy
/// array/arithmetic loop needs several split rounds to find one.
const ARRAY_READS_SAT: &str = "(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-const i Int)(declare-const j Int)(declare-const k Int)
(assert (or (< (select a i) 0) (> (select a i) 4)))
(assert (or (< (select a j) 0) (> (select a j) 4)))
(assert (or (< (select a k) 0) (> (select a k) 4)))
(assert (= (+ (select a i) (select a j) (select a k)) 9))
(assert (and (<= (- 2) (select a i)) (<= (select a i) 6)
             (<= (- 2) (select a j)) (<= (select a j) 6)
             (<= (- 2) (select a k)) (<= (select a k) 6)))";

/// `reads` array reads, each in `{-1, 10, 11}`, summing to `sum`.
pub(super) fn array_reads(reads: usize, sum: i64) -> String {
    let mut script = String::from("(set-logic QF_AUFLIA)\n(declare-fun a () (Array Int Int))\n");
    for read in 0..reads {
        script += &format!(
            "(declare-const i{read} Int)\n\
             (assert (or (< (select a i{read}) 0) (> (select a i{read}) 9)))\n\
             (assert (and (<= (- 1) (select a i{read})) (<= (select a i{read}) 11)))\n"
        );
    }
    let terms: Vec<String> = (0..reads)
        .map(|read| format!("(select a i{read})"))
        .collect();
    script += &format!("(assert (= (+ {}) {sum}))\n", terms.join(" "));
    script
}

/// Twelve reads in `{-1, 10, 11}` summing to 63, which no choice reaches:
/// unsat, and the re-solve needs far more split rounds than the guard's
/// grant (anti-vacuity below).
fn long_unsat() -> String {
    array_reads(12, 63)
}

fn executor(script: &str) -> Executor {
    let mut exec = Executor::new();
    exec.execute_all(&parse(script).expect("parse"))
        .expect("execute");
    exec
}

fn controls(exec: &Executor) -> TrustClauseDischargeControls {
    TrustClauseDischargeControls::new(
        None,
        None,
        exec.memory_limit(),
        exec.term_memory_limit(),
        CertificationEffort::for_query(exec),
    )
}

/// One guard over `script`: whether it fired, the split-loop round trips its
/// re-solve started, and the stop a decline of the funnel would now report.
/// A far enclosing grant (four times the guard's) bounds the run, so a guard
/// without its own grant fails on the count instead of running on.
fn guard(script: &str) -> (bool, u64, Option<crate::api::proofs::EnvelopeStop>) {
    let exec = executor(script);
    let authored = exec.ctx.assertions.clone();
    let controls = controls(&exec);
    let far = enter_work_grant(4 * guard_grant());
    let before = thread_round_trips();
    let fired = exec.redecides_definitive_sat_within(&authored, &controls);
    let spent = thread_round_trips() - before;
    drop(far);
    assert!(!work_grant_spent(), "the guard's grant ends with the guard");
    (fired, spent, controls.decline_stop())
}

/// The guard's own re-solve with no guard grant, the same fresh executor on
/// the same share of the count run directly, but bounded by an enclosing
/// grant of `bound` round trips so it cannot run on: the round trips it
/// started, `bound + 1` when it outlasted the bound.
fn ungranted_resolve_round_trips(script: &str, bound: u64) -> u64 {
    let exec = executor(script);
    let authored = exec.ctx.assertions.clone();
    let controls = controls(&exec);
    let mut derived = exec.new_derived_query_executor();
    assert!(controls
        .install_on(&mut derived, EffortShare::Guard)
        .is_some());
    derived.ctx.assertions = authored;
    let _bound = enter_work_grant(bound);
    let before = thread_round_trips();
    let _ = derived.check_sat();
    thread_round_trips() - before
}

fn guard_grant() -> u64 {
    EffortShare::Guard
        .round_trips()
        .expect("the guard has a round-trip grant")
}

/// The production grant, pinned where it acts: a re-solve longer than the
/// grant runs exactly the granted round trips and the one that finds the
/// grant spent, on every run; the guard abstains; and nothing is latched, so
/// a later decline of the funnel is a decline, not a timeout.
#[test]
fn the_guard_stops_a_long_resolve_after_its_round_trip_grant() {
    let bound = 2 * guard_grant();
    assert_eq!(
        ungranted_resolve_round_trips(&long_unsat(), bound),
        bound + 1,
        "ANTI-VACUITY: without the guard's grant the re-solve outlasts twice the grant"
    );
    let stopped = guard(&long_unsat());
    assert_eq!(
        stopped,
        (false, guard_grant() + 1, None),
        "the guard's re-solve runs exactly its round-trip grant, abstains, and \
         latches no stop"
    );
    assert_eq!(
        guard(&long_unsat()),
        stopped,
        "and stops at the same round trip every time"
    );
}

/// Negative twin: a satisfiable problem whose re-solve fits inside the grant
/// is still re-decided SAT, so the guard still refuses the forged refutation.
#[test]
fn the_guard_still_refutes_a_satisfiable_problem_inside_its_grant() {
    let (fired, spent, stop) = guard(ARRAY_READS_SAT);
    assert!(fired, "the guard re-decides the satisfiable problem as SAT");
    assert!(
        (3..=guard_grant()).contains(&spent),
        "ANTI-VACUITY: the re-solve runs several split rounds, inside the grant \
         (spent {spent})"
    );
    assert_eq!(stop, None);
}

/// Characterization (passes without the guard's own grant: an enclosing
/// grant was already honoured): a guard run while an enclosing grant is
/// nearly spent (a metered probe certifying its own refutation) is bounded by
/// that grant, the tighter one, abstains, and leaves it spent.
#[test]
fn an_enclosing_grant_still_bounds_the_guard() {
    let enclosing = enter_work_grant(1);
    let exec = executor(ARRAY_READS_SAT);
    let authored = exec.ctx.assertions.clone();
    let controls = controls(&exec);
    let before = thread_round_trips();
    let fired = exec.redecides_definitive_sat_within(&authored, &controls);
    assert!(!fired, "the tighter enclosing grant stops the re-solve");
    assert_eq!(
        thread_round_trips() - before,
        2,
        "one granted round trip, stopped at the next"
    );
    assert!(work_grant_spent(), "the enclosing grant stays spent");
    drop(enclosing);
    assert!(!work_grant_spent());
}
