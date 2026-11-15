// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::ground_derivation::{
    validate_ground_derivation, GroundDerivation, GroundDerivationStep,
};
use crate::{
    ChcExpr, ChcProblem, ClauseBody, Counterexample, HornClause, VerifiedChcResult,
    VerifiedCounterexample,
};

const BUDGET: Duration = Duration::from_secs(600);

pub(crate) fn checked_ground_fixture() -> ChcCheckedReplayRun {
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    let derivation = GroundDerivation {
        steps: vec![GroundDerivationStep {
            clause_index: 0,
            env: Default::default(),
            premises: vec![],
        }],
        query_step: 0,
    };
    validate_ground_derivation(&problem, &derivation).unwrap();
    let counterexample = Counterexample::new(vec![]).with_ground_derivation(derivation);
    ChcPdrProofRun::new(
        problem,
        VerifiedChcResult::Unsafe(VerifiedCounterexample::from_validated(counterexample)),
        "retained-deadline-test",
    )
    .run_checked_replay(BUDGET)
    .expect("native ground evidence must produce an actual checked run")
}

fn valid_sat_payload() -> (ChcCheckedReplayObligation, SealedReplayObligationPayload) {
    let bytes = b"(assert true)\n(check-sat)\n".to_vec();
    let obligation = ChcCheckedReplayObligation::new(
        "retained-sat-deadline",
        ChcReplayObligationKind::TraceValidity,
        ChcProofArtifactDigest::from_bytes("replay-obligation", &bytes),
        "test-only",
        ChcReplayCheckResult::pass(),
    );
    let payload =
        SealedReplayObligationPayload::try_new_smt(&obligation, bytes, None, None).unwrap();
    (obligation, payload)
}

#[test]
fn original_deadline_is_fixed_and_overflow_fails_closed() {
    let start = Instant::now();
    let deadline = fresh_recheck_deadline(start, BUDGET).unwrap();
    assert_eq!(deadline, start.checked_add(BUDGET).unwrap());
    let error = fresh_recheck_deadline(start, Duration::MAX)
        .expect_err("unrepresentable wall must not become an unlimited timeout");
    assert!(error.to_string().contains("deadline is not representable"));
}

#[test]
fn zero_budget_and_alignment_error_precedence_are_unchanged() {
    let checked = checked_ground_fixture();
    let mut misaligned = checked.clone();
    misaligned.obligation_payloads.clear();
    let mut calls = 0;
    let mut clock = || {
        calls += 1;
        Instant::now()
    };
    let zero = misaligned
        .recheck_with_fresh_ay_using_clock(Duration::ZERO, &mut clock)
        .expect_err("zero budget has original precedence");
    assert_eq!(
        zero.to_string(),
        verification_error("checked replay fresh AY recheck budget is zero").to_string(),
    );
    let alignment = misaligned
        .recheck_with_fresh_ay_using_clock(Duration::MAX, &mut clock)
        .expect_err("alignment must still precede deadline setup");
    assert!(alignment
        .to_string()
        .contains("payload alignment is incomplete"));
    assert_eq!(calls, 0);
    assert!(checked
        .recheck_with_fresh_ay(Duration::MAX)
        .unwrap_err()
        .to_string()
        .contains("deadline is not representable"));
}

#[test]
fn the_wall_is_checked_at_every_admission_and_never_after_the_last_row() {
    let checked = checked_ground_fixture();
    assert_eq!(checked.obligation_payloads.len(), 1);
    let start = Instant::now();
    let deadline = fresh_recheck_deadline(start, BUDGET).unwrap();
    let mut samples = 0;
    checked
        .recheck_with_fresh_ay_using_clock(BUDGET, &mut || {
            samples += 1;
            start
        })
        .expect("a live absolute wall preserves actual ground replay");
    checked.recheck_with_fresh_ay(BUDGET).unwrap();
    assert!(
        samples >= 3,
        "entry, payload admission and recheck admission"
    );
    // Negative controls: the wall passing at any admission, including the
    // last row's recheck admission, refuses the row before it is checked.
    for expire_at in 2..=samples {
        let mut ordinal = 0;
        let error = checked
            .recheck_with_fresh_ay_using_clock(BUDGET, &mut || {
                ordinal += 1;
                if ordinal >= expire_at {
                    deadline
                } else {
                    start
                }
            })
            .expect_err("expiry at an admission refuses the row");
        assert_eq!(ordinal, expire_at);
        assert!(
            error
                .to_string()
                .contains("budget exhausted before obligation"),
            "{error}"
        );
    }
    // #completed-check-accepted: every sample above was an ADMISSION. The
    // recheck used to sample the wall again after the last row's result was
    // destroyed and once more on return, so a recheck that had validated every
    // row failed whenever the deadline landed after it. Nothing samples it
    // now: a wall that passes once the final row's recheck has returned is
    // never observed, and the completed recheck is accepted.
    let mut ordinal = 0;
    checked
        .recheck_with_fresh_ay_using_clock(BUDGET, &mut || {
            ordinal += 1;
            if ordinal > samples {
                deadline
            } else {
                start
            }
        })
        .expect("a wall that passes after the last row cannot refuse it");
    assert_eq!(ordinal, samples, "no clock sample follows the last row");
}

#[test]
fn payload_validation_cannot_renew_the_original_solver_deadline() {
    let (obligation, payload) = valid_sat_payload();
    let start = Instant::now();
    let deadline = fresh_recheck_deadline(start, BUDGET).unwrap();
    let mut calls = 0;
    let error = validate_payload_with_deadline(&payload, &obligation, deadline, &mut || {
        calls += 1;
        if calls == 1 {
            start
        } else {
            deadline
        }
    })
    .expect_err("payload work can consume all remaining time before SMT starts");
    assert_eq!(calls, 2);
    assert!(error
        .to_string()
        .contains("budget exhausted before obligation"));
}

#[test]
fn expired_smt_rows_do_not_acquire_a_fresh_relative_timeout() {
    let (mut obligation, _) = valid_sat_payload();
    let expired = Instant::now();
    for kind in [
        ChcReplayObligationKind::TraceValidity,
        ChcReplayObligationKind::Safety,
    ] {
        obligation.kind = kind;
        let error = recheck_smt_payload(b"(malformed", &obligation, expired)
            .expect_err("both absolute adapters must decline an expired call");
        assert!(error.to_string().contains("fresh AY recheck expected"));
    }
}

#[test]
fn completed_smt_rechecks_are_accepted_without_a_post_completion_poll() {
    // #completed-check-accepted: the actual SAT solve and the actual
    // exact-query UNSAT certificate (accepted by the independent strict
    // reader) complete under a live wall and are returned. The row takes no
    // clock: nothing re-samples the wall after the result exists, so the
    // verdict on a finished recheck cannot depend on when the wall passes.
    let (obligation, payload) = valid_sat_payload();
    let SealedReplayObligationPayload::Smt { query_bytes, .. } = payload else {
        panic!("SAT fixture must retain the actual SMT query");
    };
    let deadline = fresh_recheck_deadline(Instant::now(), Duration::from_secs(60)).unwrap();
    recheck_smt_payload(&query_bytes, &obligation, deadline)
        .expect("a completed SAT recheck is accepted");

    let query = b"(set-logic QF_LIA)\n\
                  (declare-const x Int)\n\
                  (assert (> x 5))\n\
                  (assert (< x 3))\n\
                  (check-sat)\n\
                  (exit)\n";
    let obligation = ChcCheckedReplayObligation::new(
        "retained-strict-deadline",
        ChcReplayObligationKind::Safety,
        ChcProofArtifactDigest::from_bytes("replay-obligation", query),
        "test-only",
        ChcReplayCheckResult::pass(),
    );
    recheck_smt_payload(query, &obligation, deadline)
        .expect("a completed strict UNSAT recheck is accepted");
}
