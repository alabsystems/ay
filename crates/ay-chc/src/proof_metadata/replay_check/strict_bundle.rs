// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native strict proof-bundle discharge for one checked-replay obligation.

use super::phase_probe::{self, Phase};
use super::{verification_error, ChcObligationStrictCert};
use crate::pdr::ChcReplayObligation;
use crate::smt::executor_adapter::ReplayLimit;
use crate::{ChcError, ChcResult};

mod retained;
pub(super) use retained::{discharge_retained, RetainedDischarge};

pub(super) struct StrictBundleDischarge {
    pub(super) cert: ChcObligationStrictCert,
    pub(super) bundle_bytes: Vec<u8>,
    pub(super) alethe_bytes: Option<Vec<u8>>,
    pub(super) checker_command: String,
}

fn cert_from_checked_bundle(
    obligation: &ChcReplayObligation,
    cert: crate::smt::executor_adapter::StrictUnsatCert,
    limit: ReplayLimit<'_>,
) -> Result<(ChcObligationStrictCert, Vec<u8>, Option<Vec<u8>>), ChcError> {
    check_budget(limit)?;
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
    check_budget(limit)?;
    let encoded = phase_probe::result(Phase::Serialize, limit, || serde_json::to_vec(&cert.bundle));
    check_budget(limit)?;
    let bundle_bytes = encoded.map_err(|error| {
        verification_error(format!(
            "checked replay bundle serialization for obligation {}: {error}",
            obligation.name
        ))
    })?;
    let alethe_bytes = cert.alethe.map(String::into_bytes);
    check_budget(limit)?;
    let (alethe_sha256, bundle_sha256) = phase_probe::result(Phase::Hash, limit, || {
        let alethe_sha256 = alethe_bytes.as_deref().map(super::super::sha256_hex);
        check_budget(limit)?;
        let bundle_sha256 = super::super::sha256_hex(&bundle_bytes);
        check_budget(limit)?;
        Ok::<_, ChcError>((alethe_sha256, bundle_sha256))
    })?;
    let record = ChcObligationStrictCert::new_bundle(
        proof_bundle_schema,
        alethe_sha256,
        bundle_sha256,
        "verified",
    );
    Ok((record, bundle_bytes, alethe_bytes))
}

/// Discharge one UNSAT row with exact-query authority and AY's independent
/// native bundle checker. Absence, incomplete quality, or serialization failure
/// fails closed to metadata-only through a verification error.
pub(super) fn discharge(
    obligation: &ChcReplayObligation,
    limit: ReplayLimit<'_>,
    expected: &str,
) -> ChcResult<StrictBundleDischarge> {
    // The outer phase includes destruction of the native certificate and any
    // other local intermediates before the serialized discharge is admitted.
    phase_probe::option(Phase::Discharge, limit, || {
        limit.phase(|| Some(discharge_until(obligation, expected, limit)))
    })
    .ok_or_else(exhausted)?
}

fn exhausted() -> ChcError {
    verification_error(
        "checked replay budget exhausted or interrupted during strict bundle discharge; staying metadata-only",
    )
}

fn check_budget(limit: ReplayLimit<'_>) -> ChcResult<()> {
    limit.check().ok_or_else(exhausted)
}

fn discharge_until(
    obligation: &ChcReplayObligation,
    expected: &str,
    limit: ReplayLimit<'_>,
) -> ChcResult<StrictBundleDischarge> {
    // NativeOnly: same native bundle/verdict authority as the WithAletheDiagnostic
    // path (see `StrictPresentation`), just without rendering the optional Alethe
    // text. This mandatory checked-replay discharge runs once per UNSAT proof
    // obligation (one per PDR invariant clause's Initiation/Consecution check) for
    // EVERY accepted Safe/Unsafe verdict, so its per-call cost is multiplied by the
    // clause count. Regression 2026-09 (mainF 22507faaa -> mainH 99ea8b365,
    // culprit 0296c098c "reland(proof): keep BOTH the equality-node guard..."):
    // that commit's `printed_equality_states` switched a byte-for-byte compare to
    // carcara's `same_printed_term` (a parse-based check) in the shared-endpoint
    // consolidation this path exercises, which is correct but heavier; on
    // multi-predicate CHC instances with many invariant clauses (e.g. kind2
    // peterson_4, 13 chained predicates) the extra per-obligation cost pushed
    // total wall time past the competition deadline (sat ~30s -> unknown@57s).
    // `checked_run.rs`'s sibling sealed-payload consumer already treats Alethe as
    // optional (`validate_alethe_bytes` accepts `(None, None)`), and
    // `replay_check_tests/strict_bundle.rs::assert_strict_bundle_rows` already
    // handles an absent `alethe_sha256` — this call site is simply the one place
    // that never adopted the NativeOnly mode 59f1798eb introduced elsewhere.
    let proposed = crate::smt::executor_adapter::smtlib_strict_unsat_cert_native_only_with_limit(
        &obligation.smtlib,
        limit,
    );
    // Expiry wins before any failed-obligation file/diagnostic work begins.
    check_budget(limit)?;
    let Some(cert) = proposed else {
        super::dump_failed_obligation(obligation);
        return Err(verification_error(format!(
            "checked replay obligation {} did not produce a native strict UNSAT \
             certificate; staying metadata-only",
            obligation.name
        )));
    };
    let (cert, bundle_bytes, alethe_bytes) = limit
        .phase(|| Some(cert_from_checked_bundle(obligation, cert, limit)))
        .ok_or_else(exhausted)??;
    let checker_command = format!(
        "{} --strict-proof-bundle --expect {expected} {}",
        super::CHC_IN_PROCESS_REPLAY_CHECKER_NAME,
        obligation.name
    );
    Ok(StrictBundleDischarge {
        cert,
        bundle_bytes,
        alethe_bytes,
        checker_command,
    })
}

#[cfg(test)]
mod deadline_tests;
