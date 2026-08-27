// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deferred-writer joins across an exhausted first-refusal window.

use super::*;

#[test]
fn contradictory_second_writer_traps_after_refusal_window_expires() {
    let _ = crate::cert_io::ledger::take();
    let (mut session, objective) = objective_session();
    let requested_until = Instant::now() + Duration::from_secs(1);
    session.opts.deadline = Some(requested_until);
    let solved = SolvedObjective {
        coeffs: &objective,
        sense: Sense::Minimize,
        offset: 0.0,
        exact: None,
    };
    assert!(session
        .admit_or_defer(
            &crate::claim::SPECIALIZED_PB_REPLAY,
            infeasible(),
            &solved,
            vec![replay_claim("first-refutation")],
            Finisher::ExactReduction,
        )
        .is_none());
    let first_until = session
        .deferred_claim
        .as_ref()
        .expect("first writer retained")
        .first_refusal
        .until;
    assert_eq!(first_until, requested_until);

    session.opts.deadline = Some(Instant::now());
    let result = session
        .admit_or_defer(
            &crate::claim::SPECIALIZED_PB_REPLAY,
            optimal(0),
            &solved,
            vec![replay_claim("second-optimum")],
            Finisher::ExactReduction,
        )
        .expect("contradiction must finish with a trap");
    assert!(matches!(
        result,
        Outcome::Unknown {
            reason: UnknownReason::WitnessRejected { .. }
        }
    ));
    let claims = crate::cert_io::ledger::take();
    assert_eq!(claims.len(), 2);
    assert!(claims.iter().any(|claim| claim.claim == "first-refutation"));
    assert!(claims.iter().any(|claim| claim.claim == "second-optimum"));
}

#[test]
fn compatible_second_writer_keeps_first_expired_refusal_window() {
    let _ = crate::cert_io::ledger::take();
    let (mut session, objective) = objective_session();
    let requested_until = Instant::now() + Duration::from_secs(1);
    session.opts.deadline = Some(requested_until);
    let solved = SolvedObjective {
        coeffs: &objective,
        sense: Sense::Minimize,
        offset: 0.0,
        exact: None,
    };
    assert!(session
        .admit_or_defer(
            &crate::claim::SPECIALIZED_PB_REPLAY,
            infeasible(),
            &solved,
            vec![replay_claim("compatible-first")],
            Finisher::ExactReduction,
        )
        .is_none());
    let first_until = session
        .deferred_claim
        .as_ref()
        .expect("compatible first writer retained")
        .first_refusal
        .until;
    assert_eq!(first_until, requested_until);

    session.opts.deadline = Some(Instant::now());
    assert!(session
        .admit_or_defer(
            &crate::claim::SPECIALIZED_PB_REPLAY,
            infeasible(),
            &solved,
            vec![replay_claim("compatible-second")],
            Finisher::ExactReduction,
        )
        .is_none());
    assert_eq!(
        session
            .deferred_claim
            .as_ref()
            .expect("first compatible writer still retained")
            .first_refusal
            .until,
        first_until
    );
    let claims = crate::cert_io::ledger::take();
    assert_eq!(claims.len(), 1);
    assert_eq!(claims[0].claim, "compatible-second");
}
