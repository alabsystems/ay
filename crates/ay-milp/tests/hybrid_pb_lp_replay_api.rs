// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Public consumer seam: original-model replay, not session-policy authority.
use ay_milp::{
    verify_hybrid_pb_lp_infeasibility_certificate as verify,
    verify_hybrid_pb_lp_infeasibility_certificate_interruptible as verify_interruptible,
    BabSession, HybridPbLpCertificateVerificationError, HybridPbLpInfeasibilityCertificate,
    Outcome, SolveOpts,
};
use std::time::{Duration, Instant};

// Existing cert_io hybrid fixture: each Boolean assignment leaves the
// continuous contradiction Y-X>=1 and Y-X<=0. No external executable/data.
const ORIGINAL: &str = "NAME HYBRID_API
ROWS
 N COST
 G RLOW
 L RUP
COLUMNS
 X RLOW -1 RUP -1
 Y RLOW 1 RUP 1
RHS
 RHS RLOW 1 RUP 0
BOUNDS
 BV BND X
 FR BND Y
ENDATA
";

#[test]
fn public_hybrid_replay_checks_original_model_ledger_deadline_and_cancel() {
    let original = ay_milp::read_mps(ORIGINAL).expect("original model parses");
    let deadline = Instant::now() + Duration::from_secs(60);
    let opts = SolveOpts::new()
        .with_deadline(deadline)
        .with_require_certificates(true);
    let mut session = BabSession::new(original.model, &opts).expect("session");
    let outcome = session.check().expect("one original hybrid solve");
    assert!(matches!(outcome, Outcome::Infeasible { .. }), "{outcome:?}");
    let proof = session
        .hybrid_pb_lp_infeasibility_certificate()
        .expect("the actual typed hybrid ledger owns this outcome");
    verify(session.model(), proof).expect("public exact replay");
    verify_interruptible(session.model(), proof, Some(deadline), &mut || false)
        .expect("same original absolute deadline");

    let foreign = ay_milp::read_mps(&ORIGINAL.replace("RLOW 1 RUP 0", "RLOW 0 RUP 0"))
        .expect("feasible foreign model parses");
    assert!(
        verify(&foreign.model, proof).is_err(),
        "another model is not authority"
    );
    let mut wire = serde_json::to_value(proof).expect("public artifact serde");
    assert_ne!(
        wire["cuts"].as_array().expect("cut ledger").as_slice(),
        &[] as &[serde_json::Value]
    );
    wire["cuts"] = serde_json::json!([]);
    let omitted: HybridPbLpInfeasibilityCertificate =
        serde_json::from_value(wire).expect("well-formed typed object with its licenses omitted");
    assert!(
        verify(session.model(), &omitted).is_err(),
        "the final master needs its cut licenses"
    );

    let mut polls = 0;
    let cancelled = verify_interruptible(session.model(), proof, Some(deadline), &mut || {
        polls += 1;
        true
    });
    assert!(matches!(
        cancelled,
        Err(HybridPbLpCertificateVerificationError::Interrupted)
    ));
    assert_eq!(polls, 1);
    let expired = verify_interruptible(session.model(), proof, Some(Instant::now()), &mut || false);
    assert!(matches!(
        expired,
        Err(HybridPbLpCertificateVerificationError::Interrupted)
    ));
}
