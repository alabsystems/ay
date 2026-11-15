// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

fn parity_session() -> BabSession {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let even = model.add_int_col(0.0, f64::INFINITY);
    let odd = model.add_int_col(0.0, f64::INFINITY);
    model.add_row(0.0, 0.0, &[(x, 1.0), (even, -2.0)]);
    model.add_row(-1.0, -1.0, &[(x, 1.0), (odd, -2.0)]);
    model.set_objective(&[(x, 1.0)], Sense::Minimize);
    BabSession::new(model, &SolveOpts::new().with_require_certificates(true)).unwrap()
}

#[test]
fn exhausted_followup_and_unwind_do_not_keep_the_prior_admitting_lane() {
    let mut session = parity_session();
    assert!(session.check().unwrap().is_infeasible());
    assert_eq!(
        session.admitted_infeasibility_evidence(),
        Some(InfeasibilityEvidenceKind::Parity)
    );

    session.opts.deadline = Some(Instant::now());
    assert!(matches!(session.check().unwrap(), Outcome::Unknown { .. }));
    assert_eq!(session.admitted_infeasibility_evidence(), None);

    session.opts.deadline = None;
    assert!(session.check().unwrap().is_infeasible());
    panic_after_next_attempt_deadline();
    assert!(catch_unwind(AssertUnwindSafe(|| session.check())).is_err());
    assert_eq!(session.admitted_infeasibility_evidence(), None);
}

#[test]
fn a_real_candidate_certificate_without_a_terminal_route_has_no_attribution() {
    let mut session = parity_session();
    let outcome = crate::parity::try_solve(session.model(), None).unwrap();
    assert!(outcome.is_infeasible());
    let certificate = crate::parity::take_pending_infeasibility_certificate().unwrap();
    crate::verify_parity_infeasibility_certificate(session.model(), &certificate).unwrap();
    session.parity_infeasibility_certificate = Some(certificate);
    assert_eq!(session.admitted_infeasibility_evidence(), None);
}
