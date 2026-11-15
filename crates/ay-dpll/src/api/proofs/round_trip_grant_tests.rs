// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The round-trip grants of the guard and the pool lanes
//! (`TrustClauseDischargeControls::in_round_trip_grant`,
//! #counted-certification-budgets): which share carries which grant, where
//! the grant hangs, and each nested solve that runs under it, stopped after
//! exactly its granted round trips and the one that finds it spent. A spent
//! grant is a decline, never a latched stop.

use super::*;
use crate::counted_array_fixture::{
    outer_count_frobenius_script, preserve_lia_probe_state, OUTER_COUNT_MEMBERS,
};
use ay_core::resource::{
    current_guard, enter_work_grant, thread_round_trips, work, work_grant_spent, NodeLabel,
};
use ay_core::{Sort, TermId, TermStore};
use ay_frontend::parse;
use num_bigint::BigInt;

#[path = "round_trip_grant_tests/caller_boundary.rs"]
mod caller_boundary;

fn controls() -> TrustClauseDischargeControls {
    TrustClauseDischargeControls::new(None, None, None, None, CertificationEffort::default())
}

fn grant(share: EffortShare) -> u64 {
    share
        .round_trips()
        .expect("this share has a round-trip grant")
}

/// Run `solve` inside a far enclosing grant (four times the larger share
/// grant), so a nested solve without its own grant fails on the count
/// instead of running on: what it returned and the round trips it started.
fn far_bounded<T>(solve: impl FnOnce() -> T) -> (T, u64) {
    let far = enter_work_grant(4 * grant(EffortShare::Guard).max(grant(EffortShare::Pool)));
    let before = thread_round_trips();
    let value = solve();
    let spent = thread_round_trips() - before;
    drop(far);
    assert!(!work_grant_spent(), "every grant ends with its solve");
    (value, spent)
}

/// Inside `in_round_trip_grant(share)`, charge round trips one by one and
/// return how many were charged before the grant read spent (`None`: never
/// within `limit`).
fn round_trips_until_spent(
    controls: &TrustClauseDischargeControls,
    share: EffortShare,
    limit: u64,
) -> Option<u64> {
    controls.in_round_trip_grant(share, || {
        (0..=limit).find(|_| {
            if work_grant_spent() {
                return true;
            }
            work().note_round_trip();
            false
        })
    })
}

#[test]
fn each_share_carries_its_round_trip_grant_and_spends_it_exactly() {
    let controls = controls();
    for share in [EffortShare::Guard, EffortShare::Pool] {
        assert_eq!(
            round_trips_until_spent(&controls, share, 10_000),
            Some(grant(share) + 1),
            "{share:?}: spent once more round trips than granted are charged"
        );
        assert!(
            !work_grant_spent(),
            "{share:?}: the grant ends with the solve"
        );
    }
    assert_eq!(
        round_trips_until_spent(&controls, EffortShare::Reconfirm, 10_000),
        None,
        "step (4)'s re-solve keeps its own limits and gets no round-trip grant"
    );
    assert_eq!(
        controls.decline_stop(),
        None,
        "a spent grant latches no stop"
    );
}

/// The grant is entered below the certification's node, so a nested check
/// that hangs where the thread runs stays under that node's envelope.
#[test]
fn the_grant_hangs_below_the_certification_node() {
    let controls = controls();
    let certify = controls
        .certify()
        .expect("a built envelope has a certification node");
    controls.in_round_trip_grant(EffortShare::Pool, || {
        let current = current_guard().expect("the grant is entered on this thread");
        assert!(current.nearest(NodeLabel::Grant).is_some());
        assert!(
            current.is_within(&certify),
            "the grant hangs below the certification's node"
        );
    });
    assert!(
        current_guard().is_none_or(|node| !node.is_within(&certify)),
        "and both are left when the solve ends"
    );
}

/// Characterization (passes without the shares' grants: an enclosing grant
/// was already honoured): a grant around the certification still bounds a
/// nested solve when it is the tighter one.
#[test]
fn an_enclosing_grant_still_bounds_a_share() {
    let enclosing = enter_work_grant(2);
    assert_eq!(
        round_trips_until_spent(&controls(), EffortShare::Guard, 10_000),
        Some(3)
    );
    assert!(work_grant_spent(), "the enclosing grant stays spent");
    drop(enclosing);
    assert!(!work_grant_spent());
}

/// `reads` array reads, each in `{-1, 10, 11}`, summing to `sum`.
fn array_reads(reads: usize, sum: i64) -> String {
    let mut script = String::from("(declare-fun a () (Array Int Int))\n");
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

/// Twelve reads summing to 63, which no choice reaches: unsat, and every
/// lane's solve of it needs far more split rounds than a lane's grant.
const READS: usize = 12;
const SUM: i64 = 63;

fn long_unsat_executor() -> crate::Executor {
    let mut exec = crate::Executor::new();
    let script = format!("(set-logic QF_AUFLIA)\n{}", array_reads(READS, SUM));
    exec.execute_all(&parse(&script).expect("parse"))
        .expect("execute");
    exec
}

/// The pool lane `run_pool_lane` runs over the long unsat problem: whether it
/// accepted and the round trips it started.
fn pool_lane(lane: &str) -> (Option<bool>, u64, Option<EnvelopeStop>) {
    let mut exec = crate::Executor::new();
    exec.ctx = long_unsat_executor().ctx;
    let controls = controls();
    let (accepted, spent) = far_bounded(|| run_pool_lane(&controls, &mut exec, lane));
    (accepted, spent, controls.decline_stop())
}

/// The same lane solve with no lane grant, armed on the pool and run
/// directly, but bounded by an enclosing grant of `bound` round trips so it
/// cannot run on: the round trips it started, `bound + 1` when it outlasted
/// the bound.
fn ungranted_lane_round_trips(bound: u64) -> u64 {
    let mut exec = crate::Executor::new();
    exec.ctx = long_unsat_executor().ctx;
    let controls = controls();
    assert!(controls.install_on(&mut exec, EffortShare::Pool).is_some());
    let _bound = enter_work_grant(bound);
    let before = thread_round_trips();
    let _ = executor_reports_plain_strict_unsat(&mut exec);
    thread_round_trips() - before
}

#[test]
fn a_pool_lane_stops_after_its_round_trip_grant() {
    let bound = 2 * grant(EffortShare::Pool);
    assert_eq!(
        ungranted_lane_round_trips(bound),
        bound + 1,
        "ANTI-VACUITY: without the lane's grant the solve outlasts twice the grant"
    );
    let stopped = pool_lane("entailment-lane");
    assert_eq!(
        stopped,
        (Some(false), grant(EffortShare::Pool) + 1, None),
        "the lane runs exactly its round-trip grant, declines, and latches no stop"
    );
    assert_eq!(
        pool_lane("entailment-lane"),
        stopped,
        "and stops at the same round trip every time"
    );
}

fn wide_bv_literal(terms: &mut TermStore) -> TermId {
    let b = terms.mk_var("round_trip_grant_wide_b", Sort::bitvec(64));
    let zero = terms.mk_bitvec(BigInt::from(0_u8), 64);
    let is_zero = terms.mk_eq(b, zero);
    terms.mk_not(is_zero)
}

/// Through the whole funnel: the clause `not P or b != 0`, with `P` the long
/// unsat conjunction and `b` a 64-bit vector, which neither specialized
/// checker models and no structural lane accepts, reaches the standalone
/// lane, which stops after its grant, and the clause is declined.
#[test]
fn the_standalone_lane_of_the_funnel_stops_after_its_round_trip_grant() {
    let run = || {
        let exec = long_unsat_executor();
        let mut terms = exec.ctx.terms.clone();
        let conjunction = terms.mk_and(exec.ctx.assertions.clone());
        let clause = vec![terms.mk_not(conjunction), wide_bv_literal(&mut terms)];
        let controls = controls();
        let (discharged, spent) = far_bounded(|| {
            discharge_trust_clause_with_controls(&terms, &clause, &[], &controls).is_some()
        });
        (discharged, spent, controls.decline_stop())
    };
    let stopped = run();
    assert_eq!(
        stopped,
        (false, grant(EffortShare::Pool) + 1, None),
        "only the standalone lane solves here, and it runs exactly its grant"
    );
    assert_eq!(run(), stopped);
}

/// A native proof-checking solve on the pool (the BV and array lanes' solver)
/// runs under the lane's grant too.
#[test]
fn a_native_pool_solve_stops_after_its_round_trip_grant() {
    let run = || {
        let mut solver =
            crate::api::Solver::try_new_with_smtlib_logic("QF_AUFLIA").expect("solver");
        solver
            .parse_smtlib2(&array_reads(READS, SUM))
            .expect("fixture parses");
        let controls = controls();
        let (result, spent) =
            far_bounded(|| controls.check_native_solver(&mut solver, EffortShare::Pool));
        (
            result.map(|verified| verified.is_unsat()),
            spent,
            controls.decline_stop(),
        )
    };
    let stopped = run();
    assert_eq!(
        stopped,
        (Some(false), grant(EffortShare::Pool) + 1, None),
        "the native solve runs exactly the lane's grant and is not an unsat"
    );
    assert_eq!(run(), stopped);
}

struct RawReconfirmationObservation {
    unsat: bool,
    unknown: bool,
    public_proof: bool,
    outer_spent: bool,
    spent: u64,
    stop: Option<EnvelopeStop>,
}

/// A separate, bounded raw query establishes the cost premise. Restore
/// heuristic probe state, but never refund the round-trip work it consumed.
fn raw_reconfirmation_observation(ctx: &ay_frontend::Context) -> RawReconfirmationObservation {
    let _probe_state = preserve_lia_probe_state();
    let mut exec = checking_executor();
    exec.ctx = ctx.clone();
    let controls = controls();
    assert!(controls
        .install_on(&mut exec, EffortShare::Reconfirm)
        .is_some());
    let ((unsat, unknown, public_proof, outer_spent), spent) = far_bounded(|| {
        exec.begin_public_solve(false);
        exec.bind_unsat_query_assumptions(&[]);
        let result = exec.check_sat();
        let unsat = matches!(&result, Ok(result) if result.is_unsat());
        let unknown = matches!(&result, Ok(result) if result.is_unknown());
        let public_proof = exec.last_proof().is_some();
        controls.settle_nested(&exec, EffortShare::Reconfirm);
        (unsat, unknown, public_proof, work_grant_spent())
    });
    RawReconfirmationObservation {
        unsat,
        unknown,
        public_proof,
        outer_spent,
        spent,
        stop: controls.decline_stop(),
    }
}

fn reconfirmation_count_fixture() -> crate::Executor {
    let far = 4 * grant(EffortShare::Guard).max(grant(EffortShare::Pool));
    for k in OUTER_COUNT_MEMBERS {
        let mut exec = crate::Executor::new();
        exec.execute_all(&parse(&outer_count_frobenius_script(k)).expect("parse bounded family"))
            .expect("elaborate bounded family");
        let observed = raw_reconfirmation_observation(&exec.ctx);
        if observed.unknown
            && observed.outer_spent
            && observed.spent == far + 1
            && observed.stop.is_none()
        {
            return exec;
        }
    }
    panic!("ANTI-VACUITY: no bounded UNSAT family member exhausted the unchanged outer count");
}

#[test]
fn original_twelve_read_scope_finishes_raw_without_requesting_public_proof() {
    let exec = long_unsat_executor();
    let observed = raw_reconfirmation_observation(&exec.ctx);
    assert!(
        observed.unsat,
        "the original 12-read/sum63 scope remains UNSAT"
    );
    let far = 4 * grant(EffortShare::Guard).max(grant(EffortShare::Pool));
    assert!(
        observed.spent <= far,
        "the original now finishes inside the existing outer count"
    );
    assert!(
        !observed.outer_spent,
        "the original finishes before the enclosing grant is spent"
    );
    assert!(
        !observed.public_proof,
        "this unchanged script did not request a public artifact"
    );
    assert_eq!(observed.stop, None);
}

/// The proof-export path's step (4) re-solve runs no round-trip grant, like
/// the executor path's (`certification_effort/redecision.rs` says why): it
/// runs until the far enclosing grant stops it. Counterfactual: a grant on
/// step (4)'s share stops it one round trip past that grant.
#[test]
fn the_export_path_reconfirmation_runs_no_round_trip_grant() {
    let exec = reconfirmation_count_fixture();
    let controls = controls();
    let (accepted, spent) = far_bounded(|| executor_reconfirms_unsat(&exec.ctx, &controls));
    let far = 4 * grant(EffortShare::Guard).max(grant(EffortShare::Pool));
    assert_eq!(
        (accepted, spent, controls.decline_stop()),
        (false, far + 1, None)
    );
}

/// The proof-export path's guard runs under the guard's grant as well.
#[test]
fn the_export_path_guard_stops_after_its_round_trip_grant() {
    let run = || {
        let exec = long_unsat_executor();
        let controls = controls();
        let (fired, spent) =
            far_bounded(|| executor_redecides_definitive_sat(&exec.ctx, &controls));
        (fired, spent, controls.decline_stop())
    };
    let stopped = run();
    assert_eq!(stopped, (false, grant(EffortShare::Guard) + 1, None));
    assert_eq!(run(), stopped);
}
