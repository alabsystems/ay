// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Consumer-visible attribution follows the accepted route, never artifact presence.

use ay_milp::{BabSession, InfeasibilityEvidenceKind as Kind, Model, Outcome, Sense, SolveOpts};
use std::time::Duration;

fn strict_options() -> SolveOpts {
    SolveOpts::new()
        .with_time_limit(Duration::from_secs(30))
        .with_require_certificates(true)
}

fn parity_model() -> Model {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let even = model.add_int_col(0.0, f64::INFINITY);
    let odd = model.add_int_col(0.0, f64::INFINITY);
    model.add_row(0.0, 0.0, &[(x, 1.0), (even, -2.0)]);
    model.add_row(-1.0, -1.0, &[(x, 1.0), (odd, -2.0)]);
    model.set_objective(&[(x, 1.0)], Sense::Minimize);
    model
}

#[test]
fn attribution_names_the_replayed_parity_artifact_and_failed_check_clears_it() {
    let mut session = BabSession::new(parity_model(), &strict_options()).unwrap();
    assert_eq!(session.admitted_infeasibility_evidence(), None);
    assert!(session.check().unwrap().is_infeasible());
    assert_eq!(
        session.admitted_infeasibility_evidence(),
        Some(Kind::Parity)
    );
    ay_milp::verify_parity_infeasibility_certificate(
        session.model(),
        session.parity_infeasibility_certificate().unwrap(),
    )
    .unwrap();

    assert!(session.check_shared_binary_prefix(&[]).is_err());
    assert_eq!(session.admitted_infeasibility_evidence(), None);
    assert!(session.parity_infeasibility_certificate().is_none());
    assert!(session.check().unwrap().is_infeasible());
    assert_eq!(
        session.admitted_infeasibility_evidence(),
        Some(Kind::Parity)
    );
}

#[test]
fn attribution_names_the_actual_hybrid_cut_ledger() {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
    model.add_row(1.0, f64::INFINITY, &[(y, 1.0), (x, -1.0)]);
    model.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (x, -1.0)]);
    let mut session = BabSession::new(model, &strict_options()).unwrap();
    assert!(session.check().unwrap().is_infeasible());
    assert_eq!(
        session.admitted_infeasibility_evidence(),
        Some(Kind::HybridPbLp)
    );
    ay_milp::verify_hybrid_pb_lp_infeasibility_certificate(
        session.model(),
        session.hybrid_pb_lp_infeasibility_certificate().unwrap(),
    )
    .unwrap();
}

#[test]
fn source_scope_changes_clear_residual_attribution_before_the_next_feasible_check() {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let open = model.add_int_col(0.0, f64::INFINITY);
    model.add_row(2.0, f64::INFINITY, &[(open, 1.0)]);
    let mut session = BabSession::new(model, &strict_options()).unwrap();
    session.push().unwrap();
    session.add_row(1.0, f64::INFINITY, &[(x, 1.0)]).unwrap();
    session
        .add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)])
        .unwrap();
    assert!(session.check().unwrap().is_infeasible());
    assert!(matches!(
        session.admitted_infeasibility_evidence(),
        Some(Kind::OpenDomainSingleRowDp | Kind::OpenDomainMultiRowBdd)
    ));
    session.pop().unwrap();
    assert_eq!(session.admitted_infeasibility_evidence(), None);
    assert!(session.check().unwrap().is_sat());
    assert_eq!(session.admitted_infeasibility_evidence(), None);
}

#[test]
fn ordinary_farkas_evidence_is_not_mislabelled_as_supplemental() {
    let mut model = Model::new();
    let x = model.add_col(0.0, 1.0);
    model.add_row(2.0, f64::INFINITY, &[(x, 1.0)]);
    let mut session = BabSession::new(model, &strict_options()).unwrap();
    let Outcome::Infeasible {
        cert: Some(certificate),
        ..
    } = session.check().unwrap()
    else {
        panic!("exact continuous infeasibility needs its root Farkas artifact")
    };
    certificate.verify(session.model()).unwrap();
    assert_eq!(session.admitted_infeasibility_evidence(), None);
}
