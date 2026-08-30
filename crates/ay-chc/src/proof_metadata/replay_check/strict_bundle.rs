// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native strict proof-bundle discharge for one checked-replay obligation.

use super::{verification_error, ChcObligationStrictCert};
use crate::pdr::ChcReplayObligation;
use crate::{ChcError, ChcResult};
use std::time::Duration;

fn cert_from_checked_bundle(
    obligation: &ChcReplayObligation,
    cert: crate::smt::executor_adapter::StrictUnsatCert,
) -> Result<ChcObligationStrictCert, ChcError> {
    if !matches!(
        &cert.strict_verdict,
        ay_dpll::api::StrictProofVerdict::Verified(quality) if quality.is_complete()
    ) {
        return Err(verification_error(format!(
            "checked replay obligation {} native strict bundle verdict is not complete \
             Verified; staying metadata-only",
            obligation.name
        )));
    }

    let proof_bundle_schema = cert.bundle.schema.clone();
    let bundle_bytes = serde_json::to_vec(&cert.bundle).map_err(|error| {
        verification_error(format!(
            "checked replay bundle serialization for obligation {}: {error}",
            obligation.name
        ))
    })?;
    let alethe_sha256 = cert
        .alethe
        .as_ref()
        .map(|alethe| super::super::sha256_hex(alethe.as_bytes()));
    Ok(ChcObligationStrictCert::new_bundle(
        proof_bundle_schema,
        alethe_sha256,
        super::super::sha256_hex(&bundle_bytes),
        "verified",
    ))
}

/// Discharge one UNSAT row with exact-query authority and AY's independent
/// native bundle checker. Absence, incomplete quality, or serialization failure
/// fails closed to metadata-only through a verification error.
pub(super) fn discharge(
    obligation: &ChcReplayObligation,
    remaining: Duration,
    expected: &str,
) -> ChcResult<(ChcObligationStrictCert, String)> {
    let Some(cert) = crate::smt::executor_adapter::smtlib_strict_unsat_cert_via_executor(
        &obligation.smtlib,
        Some(remaining),
    ) else {
        super::dump_failed_obligation(obligation);
        return Err(verification_error(format!(
            "checked replay obligation {} did not produce a native strict UNSAT \
             certificate; staying metadata-only",
            obligation.name
        )));
    };
    let cert = cert_from_checked_bundle(obligation, cert)?;
    let command = format!(
        "{} --strict-proof-bundle --expect {expected} {}",
        super::CHC_IN_PROCESS_REPLAY_CHECKER_NAME,
        obligation.name
    );
    Ok((cert, command))
}
