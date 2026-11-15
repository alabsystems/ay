// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A sealed retained row can only originate in a live exact-query export.

use super::super::{retained_resources, verification_error};
use super::{
    ChcCheckedReplayObligationPayload, FreshRecheckControl, SealedReplayObligationPayload,
    SmtSourceAuthority,
};
use crate::smt::executor_adapter::{BoundRetainedProofBytes, RetainedReplayProgress};
use crate::{ChcCheckedReplayObligation, ChcReplayPayloadFormat, ChcResult};
use ay_core::time::Instant;

#[cfg(test)]
mod tests;

#[derive(Clone, Copy)]
pub(super) enum RetainedRowPhase {
    Before,
    During,
}

impl FreshRecheckControl<'_> {
    /// Retained evidence keeps its original-owner phase gates. Legacy rows
    /// use admission-only controls and do not enter this sibling.
    pub(super) fn check_retained_row(
        self,
        now: &mut dyn FnMut() -> Instant,
        obligation: &ChcCheckedReplayObligation,
        phase: RetainedRowPhase,
    ) -> ChcResult<()> {
        self.check_cancellation()?;
        let expired = now() >= self.deadline;
        self.check_cancellation()?;
        if expired {
            let phase = match phase {
                RetainedRowPhase::Before => "before",
                RetainedRowPhase::During => "during",
            };
            return Err(verification_error(format!(
                "checked replay fresh AY recheck budget exhausted {phase} obligation {}",
                obligation.name
            )));
        }
        Ok(())
    }

    fn check_retained_final(self, now: &mut dyn FnMut() -> Instant) -> ChcResult<()> {
        self.check_cancellation()?;
        let expired = now() >= self.deadline;
        self.check_cancellation()?;
        if expired {
            return Err(verification_error(
                "checked replay fresh AY recheck budget exhausted after final obligation",
            ));
        }
        Ok(())
    }
}

/// Keep the retained lane's final original-owner control after its request
/// state is destroyed. A legacy-only completed check does not sample either
/// the clock or cancellation here.
pub(super) fn finish_request(
    progress: Option<RetainedReplayProgress<'_>>,
    control: FreshRecheckControl<'_>,
    now: &mut dyn FnMut() -> Instant,
) -> ChcResult<()> {
    if progress.is_none() {
        return Ok(());
    }
    drop(progress);
    control.check_retained_final(now)
}

pub(super) fn recheck_retained_payload_with_control(
    item: &ChcCheckedReplayObligationPayload<'_>,
    progress: &mut RetainedReplayProgress<'_>,
    control: FreshRecheckControl<'_>,
    now: &mut dyn FnMut() -> Instant,
) -> ChcResult<()> {
    let obligation = item.obligation();
    // Each retained row is one obligation: one row's work envelope, with
    // its transient proof bytes settled when their owners drop.
    progress.begin_obligation().map_err(verification_error)?;
    // One NEW consumer request owner spans every offline replay
    // and its mandatory independent original-query redischarge.
    // A malformed v4 never reaches that second stage or v3.
    item.payload
        .validate_retained_with_resources(obligation, progress)?;
    control.check_retained_row(now, obligation, RetainedRowPhase::Before)?;
    let query = item
        .smt_query_bytes()
        .ok_or_else(|| verification_error("retained strict obligation has no original query"))?;
    let query = std::str::from_utf8(query)
        .map_err(|error| verification_error(format!("retained strict query UTF-8: {error}")))?;
    let fresh = crate::smt::executor_adapter::check_plain_unsat_retained_native_with_progress(
        query, progress,
    )
    .map_err(verification_error)?;
    drop(fresh);
    progress.check().map_err(verification_error)?;
    control.check_retained_row(now, obligation, RetainedRowPhase::During)
}

fn identity(
    row: &ChcCheckedReplayObligation,
    progress: &mut RetainedReplayProgress<'_>,
) -> ChcResult<String> {
    // Existing identity formatting has opaque allocations. Pre-admit a
    // conservative escaped/intermediate text bound before entering it.
    let mut size = 4096usize;
    for text in [
        &row.name,
        &row.checker_command,
        &row.result.status,
        &row.query.sha256,
        &row.query.role,
    ] {
        size = text
            .len()
            .checked_mul(24)
            .and_then(|bytes| size.checked_add(bytes))
            .ok_or_else(|| verification_error("checked replay identity size overflow"))?;
    }
    if let Some(cert) = &row.strict_cert {
        for text in [
            &cert.proof_bundle_schema,
            &cert.bundle_sha256,
            &cert.verdict,
        ] {
            size = text
                .len()
                .checked_mul(24)
                .and_then(|bytes| size.checked_add(bytes))
                .ok_or_else(|| {
                    verification_error("checked replay certificate identity overflow")
                })?;
        }
        if let Some(alethe) = &cert.alethe_sha256 {
            size = alethe
                .len()
                .checked_mul(24)
                .and_then(|bytes| size.checked_add(bytes))
                .ok_or_else(|| verification_error("checked replay Alethe identity overflow"))?;
        }
    }
    if let Some(path) = &row.query.path {
        size = path
            .len()
            .checked_mul(24)
            .and_then(|bytes| size.checked_add(bytes))
            .ok_or_else(|| verification_error("checked replay artifact path identity overflow"))?;
    }
    retained_resources::admit(&mut |work, bytes| progress.charge(work, bytes), size, size)?;
    let text = row.identity_input();
    retained_resources::hash(text.as_bytes(), &mut |work, bytes| {
        progress.charge(work, bytes)
    })
}

impl SealedReplayObligationPayload {
    pub(in super::super) fn try_new_retained(
        obligation: &ChcCheckedReplayObligation,
        bound: BoundRetainedProofBytes,
        progress: &mut RetainedReplayProgress<'_>,
    ) -> ChcResult<Self> {
        bound.admit(progress).map_err(verification_error)?;
        if !matches!(bound.strict_verdict(),
            ay_dpll::api::StrictProofVerdict::Verified(quality) if quality.is_complete())
        {
            return Err(verification_error(
                "retained capability lacks complete strict authority",
            ));
        }
        let obligation_identity_sha256 = identity(obligation, progress)?;
        let (query_bytes, bundle_bytes) = bound.into_parts();
        let payload = Self::Smt {
            obligation_identity_sha256,
            query_bytes,
            strict_bundle_bytes: Some(bundle_bytes),
            alethe_bytes: None,
            source_authority: SmtSourceAuthority::RetainedLiveQuery,
        };
        let result = payload.validate_retained_with_resources(obligation, progress);
        if let Err(error) = result {
            drop(payload);
            return finish_validation(progress, Err(error));
        }
        progress.check().map_err(verification_error)?;
        Ok(payload)
    }

    pub(super) fn validate_retained_with_resources(
        &self,
        obligation: &ChcCheckedReplayObligation,
        progress: &mut RetainedReplayProgress<'_>,
    ) -> ChcResult<()> {
        progress.check().map_err(verification_error)?;
        // This validation's identity text, parsed owner and replay report all
        // live in the closure below; its settlement drops only after them.
        let settlement = progress.settlement().map_err(verification_error)?;
        let result = (|| {
            let Self::Smt {
                obligation_identity_sha256,
                query_bytes,
                strict_bundle_bytes,
                alethe_bytes,
                source_authority,
            } = self
            else {
                return Err(verification_error("retained strict row has no SMT payload"));
            };
            if *source_authority != SmtSourceAuthority::RetainedLiveQuery
                || obligation.payload_format != ChcReplayPayloadFormat::SmtlibV1
                || super::expected_verdict(obligation.kind) != "unsat"
                || obligation_identity_sha256 != &identity(obligation, progress)?
            {
                return Err(verification_error(
                    "retained strict row lacks aligned live-query authority",
                ));
            }
            validate_descriptors(
                obligation,
                query_bytes,
                strict_bundle_bytes.as_deref(),
                alethe_bytes.as_deref(),
                progress,
            )
        })();
        drop(settlement);
        // Parsed owners and reports from the operation are gone before this
        // original-request terminal admission. No refusal selects legacy v3.
        finish_validation(progress, result)
    }
}

/// Poll after local-owner cleanup without replacing an already rejected row's
/// cause. Only successful results can be published, and they still require
/// the SAME original owner's terminal admission. No refusal is cleared.
fn finish_validation<T>(
    progress: &mut RetainedReplayProgress<'_>,
    result: ChcResult<T>,
) -> ChcResult<T> {
    let terminal = progress.check().map_err(verification_error);
    match result {
        Ok(value) => terminal.map(|()| value),
        Err(error) => Err(error),
    }
}

fn validate_descriptors(
    obligation: &ChcCheckedReplayObligation,
    query_bytes: &[u8],
    bundle_bytes: Option<&[u8]>,
    alethe_bytes: Option<&[u8]>,
    progress: &mut RetainedReplayProgress<'_>,
) -> ChcResult<()> {
    let cert = obligation
        .strict_cert
        .as_ref()
        .ok_or_else(|| verification_error("retained strict row omitted its certificate"))?;
    if !cert.is_retained_bundle_commitment()
        || cert.proof_bundle_schema != ay_dpll::api::RETAINED_PROOF_BUNDLE_SCHEMA
        || cert.verdict != "verified"
        || cert.alethe_sha256.is_some()
        || alethe_bytes.is_some()
    {
        return Err(verification_error(
            "retained strict row has mismatched certificate authority",
        ));
    }
    retained_resources::admit(
        &mut |work, bytes| progress.charge(work, bytes),
        query_bytes.len(),
        query_bytes.len(),
    )?;
    if query_bytes.is_empty()
        || std::str::from_utf8(query_bytes).is_err()
        || obligation.query.schema != crate::CHC_PROOF_ARTIFACT_DIGEST_SCHEMA
        || obligation.query.role != "replay-obligation"
        || obligation.query.bytes != query_bytes.len() as u64
        || obligation.query.sha256
            != retained_resources::hash(query_bytes, &mut |work, bytes| {
                progress.charge(work, bytes)
            })?
    {
        return Err(verification_error(
            "retained strict row query descriptor mismatch",
        ));
    }
    let bytes =
        bundle_bytes.ok_or_else(|| verification_error("retained strict row omitted v4 bytes"))?;
    if cert.bundle_sha256
        != retained_resources::hash(bytes, &mut |work, bytes| progress.charge(work, bytes))?
    {
        return Err(verification_error(
            "retained strict row bundle digest mismatch",
        ));
    }
    retained_resources::admit(
        &mut |work, bytes| progress.charge(work, bytes),
        bytes.len(),
        bytes.len(),
    )?;
    let limits = progress.transport_limits();
    let deadline = progress.deadline();
    #[cfg(test)]
    let _census = progress.census_stage("walk-4-strict-byte-replay");
    let mut read_diagnostics = ay_dpll::api::RetainedReadDiagnostics::default();
    let read_result =
        ay_dpll::api::read_retained_proof_bundle_with_resource_control_and_diagnostics(
            bytes,
            limits,
            deadline,
            &mut |work, bytes| progress.charge(work, bytes),
            &mut read_diagnostics,
        );
    // The callback's temporary mutable borrow is gone. Read the SAME owner's
    // already-recorded first cause without another control sample or debit.
    let (bundle, checked) = read_result.map_err(|error| {
        verification_error(format!(
            "retained strict row v4 replay: {error}; first={:?}; terminal={:?}; reported={:?}; owner={:?}",
            read_diagnostics.first_failure(),
            read_diagnostics.terminal(),
            read_diagnostics.reported_error(),
            progress.diagnostic_refusal(),
        ))
    })?;
    let unique = progress
        .ordered_unique(&checked.assume_terms)
        .map_err(verification_error)?;
    if !checked.quality.is_complete()
        || unique.is_empty()
        || bundle.schema() != cert.proof_bundle_schema
        || !progress.equal_ids(&unique, bundle.obligation_assertions())
    {
        return Err(verification_error(
            "retained strict row lacks complete exact internal inventory",
        ));
    }
    drop(unique);
    drop(checked);
    drop(bundle);
    progress.check().map_err(verification_error)
}
