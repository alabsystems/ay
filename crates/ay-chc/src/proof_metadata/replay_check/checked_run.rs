// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-only views over an atomically bound checked-replay result.

use super::{expected_verdict, verification_error, ChcCheckedReplayRun};
use crate::smt::executor_adapter::{ReplayCancellation, ReplayLimit};
use crate::{
    CancellationToken, ChcCheckedReplayObligation, ChcCheckedReplaySummary, ChcPdrProofRun,
    ChcProofArtifactDigest, ChcProofEvidenceManifest, ChcReplayObligationKind,
    ChcReplayPayloadFormat, ChcResult, ChcValidatedGroundDerivation,
};
use ay_core::time::Instant;
use std::time::Duration;

#[cfg(test)]
mod budget_tests;
#[cfg(test)]
mod cancellation_tests;
mod compact;
mod retained;

/// Exact retained byte payload paired with one checked replay obligation.
///
/// This view can only be obtained from
/// [`ChcCheckedReplayRun::obligation_payloads`], which pairs every payload with
/// the immutable summary row whose digests sealed it. For UNSAT rows the
/// proof-bundle bytes are a producer-independent strict proof; the pairing to
/// the external SMT query is an in-memory fact established by AY's opaque
/// exact-query capability when the checked run was constructed. The serialized
/// bundle schema does not by itself provide a portable, untrusted
/// query-to-bundle binding.
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct ChcCheckedReplayObligationPayload<'a> {
    obligation: &'a ChcCheckedReplayObligation,
    payload: &'a SealedReplayObligationPayload,
}

impl<'a> ChcCheckedReplayObligationPayload<'a> {
    /// Return the immutable checked-summary row paired with these bytes.
    pub fn obligation(&self) -> &'a ChcCheckedReplayObligation {
        self.obligation
    }

    /// Return the exact digest-bound payload bytes for this row.
    ///
    /// Inspect [`ChcCheckedReplayObligation::payload_format`] or prefer the
    /// typed accessors below before interpreting these bytes.
    pub fn payload_bytes(&self) -> &'a [u8] {
        match self.payload {
            SealedReplayObligationPayload::Smt { query_bytes, .. } => query_bytes,
            SealedReplayObligationPayload::GroundDerivation { artifact_bytes, .. } => {
                artifact_bytes
            }
        }
    }

    /// Compatibility alias for [`Self::payload_bytes`].
    ///
    /// Historically every retained payload was an SMT query. New code should
    /// use [`Self::smt_query_bytes`] or
    /// [`Self::ground_derivation_artifact_bytes`] before interpreting bytes.
    #[deprecated(note = "use payload_bytes or a typed payload accessor")]
    pub fn query_bytes(&self) -> &'a [u8] {
        self.payload_bytes()
    }

    /// Return the exact SMT-LIB query bytes executed for this row, or `None`
    /// when this Unsafe row carries a deciding ground derivation instead.
    pub fn smt_query_bytes(&self) -> Option<&'a [u8]> {
        match self.payload {
            SealedReplayObligationPayload::Smt { query_bytes, .. } => Some(query_bytes),
            SealedReplayObligationPayload::GroundDerivation { .. } => None,
        }
    }

    /// Return the canonical source-bound ground-derivation artifact, or
    /// `None` for an SMT-LIB replay row.
    pub fn ground_derivation_artifact_bytes(&self) -> Option<&'a [u8]> {
        if self.obligation.payload_format == ChcReplayPayloadFormat::CompactGroundDerivationV1 {
            return None;
        }
        match self.payload {
            SealedReplayObligationPayload::GroundDerivation { artifact_bytes, .. } => {
                Some(artifact_bytes)
            }
            SealedReplayObligationPayload::Smt { .. } => None,
        }
    }

    /// Return standalone compact DAG evidence, never recursive v1/v2 bytes.
    /// Validate against the consumer's original source before using its views.
    pub fn compact_ground_derivation_artifact_bytes(&self) -> Option<&'a [u8]> {
        if self.obligation.payload_format != ChcReplayPayloadFormat::CompactGroundDerivationV1 {
            return None;
        }
        match self.payload {
            SealedReplayObligationPayload::GroundDerivation { artifact_bytes, .. } => {
                Some(artifact_bytes)
            }
            SealedReplayObligationPayload::Smt { .. } => None,
        }
    }

    /// Return the serialized strict AY proof bundle for an UNSAT row.
    ///
    /// Trace-validity rows expect SAT and therefore return `None`.
    pub fn strict_bundle_bytes(&self) -> Option<&'a [u8]> {
        match self.payload {
            SealedReplayObligationPayload::Smt {
                strict_bundle_bytes,
                ..
            } => strict_bundle_bytes.as_deref(),
            SealedReplayObligationPayload::GroundDerivation { .. } => None,
        }
    }

    /// Return optional Alethe presentation bytes for an UNSAT row.
    ///
    /// These bytes are diagnostic; the native strict bundle is authoritative.
    pub fn alethe_bytes(&self) -> Option<&'a [u8]> {
        match self.payload {
            SealedReplayObligationPayload::Smt { alethe_bytes, .. } => alethe_bytes.as_deref(),
            SealedReplayObligationPayload::GroundDerivation { .. } => None,
        }
    }
}

#[derive(Debug, Clone)]
pub(super) enum SealedReplayObligationPayload {
    Smt {
        obligation_identity_sha256: String,
        query_bytes: Vec<u8>,
        strict_bundle_bytes: Option<Vec<u8>>,
        alethe_bytes: Option<Vec<u8>>,
        source_authority: SmtSourceAuthority,
    },
    GroundDerivation {
        obligation_identity_sha256: String,
        artifact_bytes: Vec<u8>,
    },
}

/// Retained authority is established only by consuming the adapter's opaque
/// live-query capability, never by hashing or internally rechecking raw bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SmtSourceAuthority {
    Legacy,
    RetainedLiveQuery,
}

impl SealedReplayObligationPayload {
    #[cfg(test)]
    pub(super) fn try_new_smt(
        obligation: &ChcCheckedReplayObligation,
        query_bytes: Vec<u8>,
        strict_bundle_bytes: Option<Vec<u8>>,
        alethe_bytes: Option<Vec<u8>>,
    ) -> ChcResult<Self> {
        Self::try_new_smt_with_progress(
            obligation,
            query_bytes,
            strict_bundle_bytes,
            alethe_bytes,
            &mut || true,
        )
    }

    pub(super) fn try_new_smt_with_progress(
        obligation: &ChcCheckedReplayObligation,
        query_bytes: Vec<u8>,
        strict_bundle_bytes: Option<Vec<u8>>,
        alethe_bytes: Option<Vec<u8>>,
        progress: &mut dyn FnMut() -> bool,
    ) -> ChcResult<Self> {
        poll_payload_progress(progress)?;
        if obligation
            .strict_cert
            .as_ref()
            .is_some_and(|cert| cert.is_retained_bundle_commitment())
        {
            return Err(verification_error(
                "retained-v4 sealing requires a live exact-query capability",
            ));
        }
        let payload = Self::Smt {
            obligation_identity_sha256: obligation.identity_sha256(),
            query_bytes,
            strict_bundle_bytes,
            alethe_bytes,
            source_authority: SmtSourceAuthority::Legacy,
        };
        poll_payload_progress(progress)?;
        payload.validate_with_progress(obligation, progress)?;
        poll_payload_progress(progress)?;
        Ok(payload)
    }

    pub(super) fn try_new_ground_derivation(
        obligation: &ChcCheckedReplayObligation,
        validated: &ChcValidatedGroundDerivation,
        artifact_bytes: Vec<u8>,
    ) -> ChcResult<Self> {
        let payload = Self::GroundDerivation {
            obligation_identity_sha256: obligation.identity_sha256(),
            artifact_bytes,
        };
        payload.validate(obligation)?;
        if validated.artifact_sha256() != obligation.query.sha256 {
            return Err(verification_error(format!(
                "checked replay obligation {} ground derivation capability digest mismatch",
                obligation.name
            )));
        }
        if validated.artifact_role() != obligation.query.role.as_str() {
            return Err(verification_error(format!(
                "checked replay obligation {} ground derivation capability role mismatch",
                obligation.name
            )));
        }
        if validated.artifact_bytes() != obligation.query.bytes {
            return Err(verification_error(format!(
                "checked replay obligation {} ground derivation capability byte length mismatch",
                obligation.name
            )));
        }
        let expected_schema = match obligation.payload_format {
            ChcReplayPayloadFormat::GroundDerivationV1 => {
                crate::CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA
            }
            ChcReplayPayloadFormat::GroundDerivationV2 => {
                crate::CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA
            }
            ChcReplayPayloadFormat::SmtlibV1
            | ChcReplayPayloadFormat::CompactGroundDerivationV1 => {
                return Err(verification_error(format!(
                    "checked replay obligation {} labels a ground derivation as SMT-LIB",
                    obligation.name
                )));
            }
        };
        if validated.artifact_schema() != expected_schema {
            return Err(verification_error(format!(
                "checked replay obligation {} ground derivation capability schema mismatch",
                obligation.name
            )));
        }
        Ok(payload)
    }

    fn validate(&self, obligation: &ChcCheckedReplayObligation) -> ChcResult<()> {
        self.validate_with_progress(obligation, &mut || true)
    }

    fn validate_with_progress(
        &self,
        obligation: &ChcCheckedReplayObligation,
        progress: &mut dyn FnMut() -> bool,
    ) -> ChcResult<()> {
        let mut stopped = false;
        let mut poll = || {
            if stopped {
                return false;
            }
            // An inner panic guard must not let a swallowed callback panic
            // resurrect this same validation attempt.
            stopped = true;
            let allowed = progress();
            stopped = !allowed;
            allowed
        };
        payload_phase(&mut poll, |progress| {
            self.validate_controlled(obligation, progress)
        })
    }

    fn validate_controlled(
        &self,
        obligation: &ChcCheckedReplayObligation,
        progress: &mut dyn FnMut() -> bool,
    ) -> ChcResult<()> {
        let obligation_identity_sha256 = match self {
            Self::Smt {
                obligation_identity_sha256,
                ..
            }
            | Self::GroundDerivation {
                obligation_identity_sha256,
                ..
            } => obligation_identity_sha256,
        };
        let identity_matches = obligation_identity_sha256 == &obligation.identity_sha256();
        poll_payload_progress(progress)?;
        if !identity_matches {
            return Err(verification_error(format!(
                "checked replay retained payload is not aligned with obligation {}",
                obligation.name
            )));
        }
        match self {
            Self::Smt {
                query_bytes,
                strict_bundle_bytes,
                alethe_bytes,
                ..
            } => {
                if obligation.payload_format != ChcReplayPayloadFormat::SmtlibV1 {
                    return Err(verification_error(format!(
                        "checked replay obligation {} labels SMT bytes as {}",
                        obligation.name,
                        obligation.payload_format.as_str()
                    )));
                }
                payload_phase(progress, |_| {
                    validate_payload_descriptor(obligation, query_bytes)
                })?;
                match expected_verdict(obligation.kind) {
                    "unsat" => Self::validate_strict_bundle(
                        obligation,
                        strict_bundle_bytes.as_deref(),
                        alethe_bytes.as_deref(),
                        progress,
                    ),
                    "sat" => {
                        Self::validate_sat_payload(obligation, strict_bundle_bytes, alethe_bytes)
                    }
                    expected => Err(verification_error(format!(
                        "checked replay obligation {} has unsupported expected verdict {expected}",
                        obligation.name
                    ))),
                }
            }
            Self::GroundDerivation { artifact_bytes, .. } => {
                if !matches!(
                    obligation.payload_format,
                    ChcReplayPayloadFormat::GroundDerivationV1
                        | ChcReplayPayloadFormat::GroundDerivationV2
                        | ChcReplayPayloadFormat::CompactGroundDerivationV1
                ) || obligation.kind != ChcReplayObligationKind::TraceValidity
                    || obligation.strict_cert.is_some()
                {
                    return Err(verification_error(format!(
                        "checked replay obligation {} has an invalid ground-derivation row",
                        obligation.name
                    )));
                }
                payload_phase(progress, |_| {
                    validate_payload_descriptor(obligation, artifact_bytes)
                })
            }
        }
    }

    fn validate_strict_bundle(
        obligation: &ChcCheckedReplayObligation,
        strict_bundle_bytes: Option<&[u8]>,
        alethe_bytes: Option<&[u8]>,
        progress: &mut dyn FnMut() -> bool,
    ) -> ChcResult<()> {
        payload_phase(progress, |progress| {
            Self::validate_strict_bundle_controlled(
                obligation,
                strict_bundle_bytes,
                alethe_bytes,
                progress,
            )
        })
    }

    fn validate_strict_bundle_controlled(
        obligation: &ChcCheckedReplayObligation,
        strict_bundle_bytes: Option<&[u8]>,
        alethe_bytes: Option<&[u8]>,
        progress: &mut dyn FnMut() -> bool,
    ) -> ChcResult<()> {
        let cert = obligation.strict_cert.as_ref().ok_or_else(|| {
            verification_error(format!(
                "checked replay UNSAT obligation {} has no strict certificate",
                obligation.name
            ))
        })?;
        if !cert.is_current_bundle_commitment()
            || cert.proof_bundle_schema != ay_dpll::api::PROOF_BUNDLE_SCHEMA
            || cert.verdict != "verified"
        {
            return Err(verification_error(format!(
                "checked replay obligation {} has no current verified bundle commitment",
                obligation.name
            )));
        }
        let bundle_bytes = strict_bundle_bytes.ok_or_else(|| {
            verification_error(format!(
                "checked replay obligation {} omitted retained strict bundle bytes",
                obligation.name
            ))
        })?;
        let digest_matches = cert.bundle_sha256 == super::super::sha256_hex(bundle_bytes);
        poll_payload_progress(progress)?;
        if !digest_matches {
            return Err(verification_error(format!(
                "checked replay obligation {} retained strict bundle digest mismatch",
                obligation.name
            )));
        }
        let bundle = serde_json::from_slice::<ay_dpll::api::SerializableProofBundle>(bundle_bytes);
        poll_payload_progress(progress)?;
        let bundle = bundle.map_err(|error| {
            verification_error(format!(
                "checked replay obligation {} retained strict bundle parse: {error}",
                obligation.name
            ))
        })?;
        if bundle.schema != cert.proof_bundle_schema {
            return Err(verification_error(format!(
                "checked replay obligation {} retained strict bundle schema mismatch",
                obligation.name
            )));
        }
        let checked = ay_dpll::api::re_check_bundle_strict_with_cancellation(&bundle, progress);
        poll_payload_progress(progress)?;
        let checked = checked.map_err(|error| {
            verification_error(format!(
                "checked replay obligation {} retained strict bundle recheck: {error}",
                obligation.name
            ))
        })?;
        let exact_authority = checked.quality.is_complete()
            && !checked.assume_terms.is_empty()
            && ordered_unique(&checked.assume_terms) == bundle.obligation_assertions;
        poll_payload_progress(progress)?;
        if !exact_authority {
            return Err(verification_error(format!(
                "checked replay obligation {} retained strict bundle lacks complete exact assumption authority",
                obligation.name
            )));
        }
        payload_phase(progress, |_| {
            validate_alethe_bytes(obligation, cert.alethe_sha256.as_deref(), alethe_bytes)
        })
    }

    fn validate_sat_payload(
        obligation: &ChcCheckedReplayObligation,
        strict_bundle_bytes: &Option<Vec<u8>>,
        alethe_bytes: &Option<Vec<u8>>,
    ) -> ChcResult<()> {
        if obligation.strict_cert.is_some()
            || strict_bundle_bytes.is_some()
            || alethe_bytes.is_some()
        {
            return Err(verification_error(format!(
                "checked replay SAT obligation {} carries UNSAT certificate payload",
                obligation.name
            )));
        }
        Ok(())
    }
}

fn poll_payload_progress(progress: &mut dyn FnMut() -> bool) -> ChcResult<()> {
    if !progress() {
        return Err(verification_error(
            "checked replay retained payload validation interrupted",
        ));
    }
    Ok(())
}

fn payload_phase<T>(
    progress: &mut dyn FnMut() -> bool,
    operation: impl FnOnce(&mut dyn FnMut() -> bool) -> ChcResult<T>,
) -> ChcResult<T> {
    poll_payload_progress(progress)?;
    let result = operation(progress);
    // Locals belonging to the opaque operation, including the parsed proof
    // and fresh checker result, are already destroyed before this admission.
    poll_payload_progress(progress)?;
    result
}

fn validate_payload_descriptor(
    obligation: &ChcCheckedReplayObligation,
    payload_bytes: &[u8],
) -> ChcResult<()> {
    if payload_bytes.is_empty() || std::str::from_utf8(payload_bytes).is_err() {
        return Err(verification_error(format!(
            "checked replay obligation {} retained payload is empty or not UTF-8",
            obligation.name
        )));
    }
    let actual = ChcProofArtifactDigest::from_bytes(
        super::super::replay_payload_role(obligation.payload_format),
        payload_bytes,
    );
    if obligation.query.schema != crate::CHC_PROOF_ARTIFACT_DIGEST_SCHEMA
        || obligation.query.schema != actual.schema
        || obligation.query.role != actual.role
        || obligation.query.sha256 != actual.sha256
        || obligation.query.bytes != actual.bytes
    {
        return Err(verification_error(format!(
            "checked replay obligation {} retained payload descriptor mismatch",
            obligation.name
        )));
    }
    Ok(())
}

fn validate_alethe_bytes(
    obligation: &ChcCheckedReplayObligation,
    expected_sha256: Option<&str>,
    alethe_bytes: Option<&[u8]>,
) -> ChcResult<()> {
    match (expected_sha256, alethe_bytes) {
        (None, None) => Ok(()),
        (Some(expected), Some(bytes))
            if !bytes.is_empty()
                && std::str::from_utf8(bytes).is_ok()
                && expected == super::super::sha256_hex(bytes) =>
        {
            Ok(())
        }
        _ => Err(verification_error(format!(
            "checked replay obligation {} retained Alethe presence or digest mismatch",
            obligation.name
        ))),
    }
}

fn ordered_unique(terms: &[ay_core::TermId]) -> Vec<ay_core::TermId> {
    let mut unique = Vec::new();
    for term in terms {
        if !unique.contains(term) {
            unique.push(*term);
        }
    }
    unique
}

fn fresh_recheck_deadline(start: Instant, budget: Duration) -> ChcResult<Instant> {
    start.checked_add(budget).ok_or_else(|| {
        verification_error("checked replay fresh AY recheck deadline is not representable")
    })
}

#[derive(Clone, Copy)]
struct FreshRecheckControl<'a> {
    deadline: Instant,
    cancellation: Option<&'a ReplayCancellation>,
}

impl<'a> FreshRecheckControl<'a> {
    fn limit(self) -> ReplayLimit<'a> {
        match self.cancellation {
            Some(cancellation) => ReplayLimit::Cancellable {
                deadline: self.deadline,
                cancellation,
            },
            None => ReplayLimit::Until(self.deadline),
        }
    }

    fn cancelled(self) -> bool {
        self.cancellation
            .is_some_and(ReplayCancellation::is_cancelled)
    }

    fn check_cancellation(self) -> ChcResult<()> {
        if self.cancelled() {
            return Err(verification_error(
                "checked replay fresh AY recheck interrupted by cancellation",
            ));
        }
        Ok(())
    }

    fn allows(self, now: &mut dyn FnMut() -> Instant) -> bool {
        if self.cancelled() {
            return false;
        }
        let expired = now() >= self.deadline;
        let cancelled = self.cancelled();
        !expired && !cancelled
    }

    /// Admit the next unit of a legacy row's work. Its fresh adapters and
    /// readers poll the same wall inside their work. A legacy-only request
    /// has no post-completion clock sample (#completed-check-accepted): its
    /// cleanup is debited at the NEXT row's admission, and the last row's at
    /// none. Retained rows keep their separate original-owner phase gates.
    fn admit(
        self,
        now: &mut dyn FnMut() -> Instant,
        obligation: &ChcCheckedReplayObligation,
    ) -> ChcResult<()> {
        self.check_cancellation()?;
        let expired = now() >= self.deadline;
        self.check_cancellation()?;
        if expired {
            return Err(verification_error(format!(
                "checked replay fresh AY recheck budget exhausted before obligation {}",
                obligation.name
            )));
        }
        Ok(())
    }
}

fn validate_payload_with_control(
    payload: &SealedReplayObligationPayload,
    obligation: &ChcCheckedReplayObligation,
    control: FreshRecheckControl<'_>,
    now: &mut dyn FnMut() -> Instant,
) -> ChcResult<()> {
    // Descriptor validation may hash or strictly recheck a retained proof.
    // Admit that work before starting it, then debit its elapsed time before
    // admitting the fresh solver or ground-derivation check. This does not
    // make hashing or deserialization internally interruptible. The offline
    // strict reader receives the same control at its actual progress boundaries.
    control.admit(now, obligation)?;
    let validated =
        payload.validate_with_progress(obligation, &mut || control.allows(&mut Instant::now));
    // Refusal is terminal even when validation also failed. If its inner
    // polls stayed live, retain validation-error-before-post-clock precedence.
    control.check_cancellation()?;
    validated?;
    control.admit(now, obligation)
}

/// Freshly solve one retained SMT row under the row's control.
///
/// #completed-check-accepted — the control is consulted to ADMIT the solve
/// (and by the adapters inside it), and after it only to name why a solve that
/// did not produce the required verdict failed. A solve that produced it, and
/// for UNSAT an exact-query certificate the independent strict reader
/// accepted, is a completed check: a cancellation or deadline that arrives
/// afterwards does not discard it. (This used to re-poll both after dropping
/// the result, so the verdict on a finished recheck depended on the clock.)
fn recheck_smt_payload_with_control(
    query_bytes: &[u8],
    obligation: &ChcCheckedReplayObligation,
    control: FreshRecheckControl<'_>,
) -> ChcResult<()> {
    control.check_cancellation()?;
    let query = std::str::from_utf8(query_bytes).map_err(|error| {
        verification_error(format!(
            "checked replay obligation {} retained query UTF-8: {error}",
            obligation.name
        ))
    })?;
    let expected = expected_verdict(obligation.kind);
    if expected == "unsat" {
        // This fresh certificate is checked and discarded below, not published
        // as diagnostic evidence. Keep native authority but omit unused text.
        let cert = crate::smt::executor_adapter::smtlib_strict_unsat_cert_native_only_with_limit(
            query,
            control.limit(),
        );
        if cert.is_none() {
            control.check_cancellation()?;
            return Err(verification_error(format!(
                "checked replay obligation {} fresh AY recheck expected unsat, got <execution-or-proof-error>",
                obligation.name
            )));
        }
        Ok(())
    } else {
        let actual = crate::smt::executor_adapter::smtlib_first_verdict_via_executor_with_limit(
            query,
            control.limit(),
            None,
        );
        if actual.as_deref() != Some(expected) {
            control.check_cancellation()?;
            return Err(verification_error(format!(
                "checked replay obligation {} fresh AY recheck expected {expected}, got {}",
                obligation.name,
                actual.as_deref().unwrap_or("<execution-error>")
            )));
        }
        Ok(())
    }
}

#[cfg(test)]
fn recheck_ground_with_budget(
    problem: &crate::ChcProblem,
    obligation: &ChcCheckedReplayObligation,
    artifact_bytes: &[u8],
    budget: Duration,
    start: &Instant,
) -> ChcResult<ChcValidatedGroundDerivation> {
    recheck_ground_with_control(
        problem,
        obligation,
        artifact_bytes,
        FreshRecheckControl {
            deadline: fresh_recheck_deadline(*start, budget)?,
            cancellation: None,
        },
        &mut Instant::now,
    )
}

fn recheck_ground_with_control(
    problem: &crate::ChcProblem,
    obligation: &ChcCheckedReplayObligation,
    artifact_bytes: &[u8],
    control: FreshRecheckControl<'_>,
    now: &mut dyn FnMut() -> Instant,
) -> ChcResult<ChcValidatedGroundDerivation> {
    // Every reader callback shares this original deadline and the same sticky
    // parent-aware token as both active SMT adapters. No per-row reset.
    recheck_ground_with_progress(problem, obligation, artifact_bytes, &mut || {
        control.allows(now)
    })
}

fn recheck_ground_with_progress(
    problem: &crate::ChcProblem,
    obligation: &ChcCheckedReplayObligation,
    artifact_bytes: &[u8],
    progress: &mut dyn FnMut() -> bool,
) -> ChcResult<ChcValidatedGroundDerivation> {
    // The sealed row selects exactly one format. Interruption or any other
    // refusal is terminal: no version probing or solver fallback follows it.
    let checked = match obligation.payload_format {
        ChcReplayPayloadFormat::GroundDerivationV1 => {
            crate::validate_chc_ground_derivation_artifact_with_progress(
                problem,
                artifact_bytes,
                progress,
            )
        }
        ChcReplayPayloadFormat::GroundDerivationV2 => {
            crate::validate_chc_ground_derivation_artifact_v2_with_progress(
                problem,
                artifact_bytes,
                progress,
            )
        }
        ChcReplayPayloadFormat::SmtlibV1 | ChcReplayPayloadFormat::CompactGroundDerivationV1 => {
            return Err(verification_error(format!(
                "checked replay obligation {} labels a ground derivation as SMT-LIB",
                obligation.name
            )));
        }
    };
    checked.map_err(|error| {
        verification_error(format!(
            "checked replay obligation {} ground derivation recheck: {error}",
            obligation.name
        ))
    })
}

/// Immutable checked-replay run access.
///
/// The run, manifest, summary, and bytes form one validated bundle. Callers
/// cannot substitute any constituent after checked replay succeeds:
///
/// ```compile_fail
/// use ay_chc::{ChcCheckedReplayRun, ChcPdrProofRun};
///
/// fn replace_run(checked: &mut ChcCheckedReplayRun, run: ChcPdrProofRun) {
///     checked.proof_run = run;
/// }
/// ```
impl ChcCheckedReplayRun {
    /// Return the upgraded problem-bound proof run.
    pub fn proof_run(&self) -> &ChcPdrProofRun {
        &self.proof_run
    }

    /// Return the admitted evidence manifest.
    pub fn manifest(&self) -> &ChcProofEvidenceManifest {
        &self.manifest
    }

    /// Return the validated checked replay summary.
    pub fn summary(&self) -> &ChcCheckedReplaySummary {
        &self.summary
    }

    /// Return normalized problem artifact bytes.
    pub fn problem_bytes(&self) -> &[u8] {
        &self.problem_bytes
    }

    /// Return certificate artifact bytes.
    pub fn certificate_bytes(&self) -> &[u8] {
        &self.certificate_bytes
    }

    /// Return solver transcript bytes produced by this pass, when present.
    pub fn run_log_bytes(&self) -> Option<&[u8]> {
        self.run_log_bytes.as_deref()
    }

    /// Return the replay-log artifact bytes.
    pub fn replay_log_bytes(&self) -> &[u8] {
        &self.replay_log_bytes
    }

    /// Return the checked-report artifact bytes.
    pub fn checked_report_bytes(&self) -> &[u8] {
        &self.checked_report_bytes
    }

    /// Iterate over checked-summary rows paired with their exact retained
    /// query and proof payloads.
    ///
    /// No unpaired payload accessor is exposed: the immutable row/payload
    /// association is the in-memory query-binding evidence established during
    /// checked-run construction.
    pub fn obligation_payloads(
        &self,
    ) -> impl ExactSizeIterator<Item = ChcCheckedReplayObligationPayload<'_>> + '_ {
        self.summary
            .obligations
            .iter()
            .zip(&self.obligation_payloads)
            .map(|(obligation, payload)| ChcCheckedReplayObligationPayload {
                obligation,
                payload,
            })
    }

    /// Revalidate every retained byte payload under `budget` admission.
    ///
    /// UNSAT rows first undergo a producer-independent strict recheck of their
    /// retained serialized bundle, then a fresh exact-query-bound AY proof run.
    /// SMT trace-validity rows are freshly solved and must remain SAT. Ground
    /// derivation rows are freshly parsed and decided against the source
    /// problem without solver search. Ground validation cooperatively polls
    /// the same original budget at phase/chunk boundaries. Both SMT adapters
    /// receive one absolute deadline including earlier payload work, and expiry
    /// is checked when each row and each of its rechecks is admitted. A
    /// legacy-only recheck that completed every row is accepted: nothing
    /// consults the deadline or cancellation after its last recheck returned
    /// (#completed-check-accepted). Retained-v4 rows intentionally keep their
    /// original-owner phase and final control gates, including after fresh
    /// evidence and retained request state have been destroyed.
    /// Offline strict replay receives the same control throughout its existing
    /// structural, copying, authentication and checker traversals. Its remaining
    /// semantic BV checks, empty-set demand census and some rule validators,
    /// together with source hashes, serde internals, arithmetic and individual
    /// allocation/destruction operations, still contain opaque intervals.
    /// Earlier producer export is not retroactively made interruptible.
    /// This is not a hard deadline or a 100 ms response guarantee. It is an
    /// in-memory recheck of a sealed
    /// [`ChcCheckedReplayRun`]; it does not claim that a separately transported
    /// schema-v3 or retained-v4 bundle can authenticate arbitrary external query text by
    /// itself. Retained rows use one finite cumulative work/byte owner across
    /// every offline replay and mandatory original-query redischarge. Neither
    /// a row nor a transport operation renews it; legacy rows keep their prior
    /// checker policy. Public `Clone` is outside this controlled request and is
    /// not an allocator-accounted duplication API.
    pub fn recheck_with_fresh_ay(&self, budget: Duration) -> ChcResult<()> {
        self.recheck_with_fresh_ay_using_clock(budget, &mut Instant::now)
    }

    /// Recheck retained evidence using the original budget and an owned
    /// snapshot of `cancellation`, including its already-linked parents.
    ///
    /// Cancellation is sticky for this attempt: resetting a caller flag after
    /// AY observes it cannot resume validation or select another format. It
    /// reaches active SAT and strict-UNSAT solving and every ground-reader
    /// progress boundary. Retained payload validation also passes cancellation
    /// into its offline strict reader. Hashing/deserialization and other opaque
    /// intervals listed in [`Self::recheck_with_fresh_ay`] remain phase-polled.
    /// Retained-v4 fresh evidence and request state are destroyed before that
    /// lane's final original-owner gate. Legacy-only checks have no
    /// post-completion gate. Neither path is a hard whole-call latency
    /// guarantee. The existing checked run and
    /// its metadata are never modified, including on refusal.
    ///
    /// As in the deadline-only API, zero budget, incomplete payload alignment
    /// and an unrepresentable deadline are rejected before starting replay.
    pub fn recheck_with_fresh_ay_with_cancellation(
        &self,
        budget: Duration,
        cancellation: &CancellationToken,
    ) -> ChcResult<()> {
        self.recheck_with_fresh_ay_with_controls(budget, Some(cancellation), &mut Instant::now)
    }

    fn recheck_with_fresh_ay_using_clock(
        &self,
        budget: Duration,
        now: &mut dyn FnMut() -> Instant,
    ) -> ChcResult<()> {
        self.recheck_with_fresh_ay_with_controls(budget, None, now)
    }

    /// Retained rows in this run: how many obligations the single request
    /// owner may declare (one work envelope each, bytes settled).
    fn retained_row_count(&self) -> usize {
        self.obligation_payloads()
            .filter(|item| {
                item.obligation()
                    .strict_cert
                    .as_ref()
                    .is_some_and(|cert| cert.is_retained_bundle_commitment())
            })
            .count()
    }

    fn recheck_with_fresh_ay_with_controls(
        &self,
        budget: Duration,
        cancellation: Option<&CancellationToken>,
        now: &mut dyn FnMut() -> Instant,
    ) -> ChcResult<()> {
        if budget.is_zero() {
            return Err(verification_error(
                "checked replay fresh AY recheck budget is zero",
            ));
        }
        if self.summary.obligations.is_empty()
            || self.summary.obligations.len() != self.obligation_payloads.len()
        {
            return Err(verification_error(
                "checked replay retained payload alignment is incomplete",
            ));
        }
        let start = now();
        let deadline = fresh_recheck_deadline(start, budget)?;
        let cancellation = cancellation.map(ReplayCancellation::new);
        let control = FreshRecheckControl {
            deadline,
            cancellation: cancellation.as_ref(),
        };
        control.check_cancellation()?;
        let mut live = || true;
        // Move the single callback reference at most once, AFTER row
        // admission. Legacy/ground-only requests retain their prior numeric
        // policy and injected-clock/error precedence.
        let mut retained_callback: Option<&mut dyn FnMut() -> bool> = Some(&mut live);
        let mut retained_progress = None;
        let retained_rows = self.retained_row_count();
        for item in self.obligation_payloads() {
            let obligation = item.obligation();
            if obligation
                .strict_cert
                .as_ref()
                .is_some_and(|cert| cert.is_retained_bundle_commitment())
            {
                control.check_retained_row(now, obligation, retained::RetainedRowPhase::Before)?;
                if retained_progress.is_none() {
                    let callback = retained_callback.take().ok_or_else(|| {
                        verification_error("retained request owner cannot be renewed")
                    })?;
                    retained_progress = Some(
                        crate::smt::executor_adapter::RetainedReplayProgress::new_for_retained_rows(
                            control.limit(),
                            callback,
                            retained_rows,
                        )
                        .map_err(verification_error)?,
                    );
                }
                let progress = retained_progress.as_mut().ok_or_else(|| {
                    verification_error("retained strict row has no request resource owner")
                })?;
                retained::recheck_retained_payload_with_control(&item, progress, control, now)?;
                // Preserve separate cleanup and whole-row admission points,
                // including the existing injected-clock observation order.
                control.check_retained_row(now, obligation, retained::RetainedRowPhase::During)?;
                continue;
            }
            validate_payload_with_control(item.payload, obligation, control, now)?;
            // #completed-check-accepted: in a legacy-only request, this
            // recheck is the row's last work that consults the control. Its
            // cleanup is debited at the next row's admission, not after the
            // last row. A request that also entered retained-v4 still owns
            // that lane's explicit final original-owner gate below.
            match item.payload {
                SealedReplayObligationPayload::Smt { query_bytes, .. } => {
                    recheck_smt_payload_with_control(query_bytes, obligation, control)?;
                }
                SealedReplayObligationPayload::GroundDerivation { artifact_bytes, .. } => {
                    if obligation.payload_format
                        == ChcReplayPayloadFormat::CompactGroundDerivationV1
                    {
                        compact::recheck(
                            self.proof_run.problem(),
                            obligation,
                            artifact_bytes,
                            control,
                            now,
                        )?;
                        continue;
                    }
                    // Checked, then discarded: the fresh recheck publishes nothing.
                    let _validated = recheck_ground_with_control(
                        self.proof_run.problem(),
                        obligation,
                        artifact_bytes,
                        control,
                        &mut Instant::now,
                    )?;
                }
            }
        }
        retained::finish_request(retained_progress, control, now)
    }

    pub(crate) fn into_proof_run(self) -> ChcPdrProofRun {
        self.proof_run
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{engines, AdaptiveConfig, AdaptivePortfolio, BmcConfig, ChcParser, PdrConfig};

    fn checked_fixture() -> ChcCheckedReplayRun {
        let problem = ChcParser::parse(
            r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#,
        )
        .expect("checked payload fixture parse");
        let run = engines::solve_pdr_proof(problem, PdrConfig::default())
            .expect("checked payload fixture solve");
        run.run_checked_replay(Duration::from_mins(1))
            .expect("checked payload fixture replay")
    }

    fn ground_checked_fixture() -> ChcCheckedReplayRun {
        let problem = ChcParser::parse(
            r#"(set-logic HORN)
(declare-fun Ground0 (Int) Bool)
(declare-fun Ground1 (Int) Bool)
(assert (Ground0 0))
(assert (forall ((x Int)) (=> (Ground0 x) (Ground1 (+ x 1)))))
(assert (forall ((x Int)) (=> (and (Ground1 x) (= x 1)) false)))
(check-sat)
"#,
        )
        .expect("ground payload fixture parse");
        let result = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::test_default())
            .solve_bmc_only(BmcConfig {
                max_depth: 2,
                acyclic_safe: true,
                prefer_exact_acyclic_first: true,
                time_budget: Some(Duration::from_secs(20)),
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                ..BmcConfig::default()
            });
        let run = ChcPdrProofRun::new(problem, result, "bmc");
        run.run_checked_replay(Duration::from_mins(1))
            .expect("ground payload fixture replay")
    }

    #[test]
    fn retained_payload_tampering_and_misalignment_fail_closed() {
        let checked = checked_fixture();
        assert!(checked.recheck_with_fresh_ay(Duration::ZERO).is_err());

        let mut query_tamper = checked.clone();
        match &mut query_tamper.obligation_payloads[0] {
            SealedReplayObligationPayload::Smt { query_bytes, .. } => query_bytes[0] ^= 1,
            SealedReplayObligationPayload::GroundDerivation { .. } => {
                panic!("safe fixture must carry SMT replay")
            }
        }
        assert!(query_tamper
            .recheck_with_fresh_ay(Duration::from_mins(1))
            .is_err());

        let mut bundle_tamper = checked.clone();
        let SealedReplayObligationPayload::Smt {
            strict_bundle_bytes,
            ..
        } = &mut bundle_tamper.obligation_payloads[0]
        else {
            panic!("safe fixture must carry SMT replay");
        };
        let bundle = strict_bundle_bytes
            .as_mut()
            .expect("safe row strict bundle bytes");
        bundle[0] ^= 1;
        assert!(bundle_tamper
            .recheck_with_fresh_ay(Duration::from_mins(1))
            .is_err());

        let mut alethe_tamper = checked.clone();
        let SealedReplayObligationPayload::Smt { alethe_bytes, .. } =
            &mut alethe_tamper.obligation_payloads[0]
        else {
            panic!("safe fixture must carry SMT replay");
        };
        match alethe_bytes {
            Some(bytes) => bytes.push(b' '),
            slot @ None => *slot = Some(b"(step forged)".to_vec()),
        }
        assert!(alethe_tamper
            .recheck_with_fresh_ay(Duration::from_mins(1))
            .is_err());

        assert!(checked.obligation_payloads.len() > 1);
        let mut misaligned = checked;
        misaligned.obligation_payloads.swap(0, 1);
        assert!(misaligned
            .recheck_with_fresh_ay(Duration::from_mins(1))
            .is_err());
    }

    #[test]
    fn retained_ground_payload_tampering_and_variant_mismatch_fail_closed() {
        let checked = ground_checked_fixture();
        assert_eq!(checked.obligation_payloads.len(), 1);

        let artifact_bytes = match &checked.obligation_payloads[0] {
            SealedReplayObligationPayload::GroundDerivation { artifact_bytes, .. } => {
                artifact_bytes.clone()
            }
            SealedReplayObligationPayload::Smt { .. } => {
                panic!("ground fixture must retain a ground derivation")
            }
        };
        let validated = crate::validate_chc_ground_derivation_artifact(
            checked.proof_run.problem(),
            &artifact_bytes,
        )
        .expect("fixture ground bytes should validate");

        let mut forged_schema = checked.summary.obligations[0].clone();
        forged_schema.query.schema = "ay.invalid-artifact-digest/v0";
        assert!(SealedReplayObligationPayload::try_new_ground_derivation(
            &forged_schema,
            &validated,
            artifact_bytes.clone(),
        )
        .is_err());
        let schema_admission = checked
            .manifest
            .clone()
            .try_with_validated_ground_replay_summary(
                ChcCheckedReplaySummary {
                    obligations: vec![forged_schema],
                    ..checked.summary.clone()
                },
                &validated,
            )
            .expect_err("forged artifact descriptor schema must fail public admission");
        assert!(schema_admission
            .reasons()
            .iter()
            .any(|reason| reason.contains("artifact descriptor schema mismatch")));

        let mut forged_length = checked.summary.obligations[0].clone();
        forged_length.query.bytes += 1;
        assert!(SealedReplayObligationPayload::try_new_ground_derivation(
            &forged_length,
            &validated,
            artifact_bytes.clone(),
        )
        .is_err());
        let length_admission = checked
            .manifest
            .clone()
            .try_with_validated_ground_replay_summary(
                ChcCheckedReplaySummary {
                    obligations: vec![forged_length],
                    ..checked.summary.clone()
                },
                &validated,
            )
            .expect_err("forged artifact byte length must fail public admission");
        assert!(length_admission
            .reasons()
            .iter()
            .any(|reason| reason.contains("artifact byte length mismatch")));

        let mut forged_role = checked.summary.obligations[0].clone();
        forged_role.query.role = "replay-obligation".to_string();
        assert!(SealedReplayObligationPayload::try_new_ground_derivation(
            &forged_role,
            &validated,
            artifact_bytes.clone(),
        )
        .is_err());
        let role_admission = checked
            .manifest
            .clone()
            .try_with_validated_ground_replay_summary(
                ChcCheckedReplaySummary {
                    obligations: vec![forged_role],
                    ..checked.summary.clone()
                },
                &validated,
            )
            .expect_err("forged artifact role must fail public admission");
        assert!(role_admission
            .reasons()
            .iter()
            .any(|reason| reason.contains("artifact role mismatch")));

        let mut bytes_tamper = checked.clone();
        let SealedReplayObligationPayload::GroundDerivation { artifact_bytes, .. } =
            &mut bytes_tamper.obligation_payloads[0]
        else {
            panic!("ground fixture must retain a ground derivation");
        };
        artifact_bytes[0] ^= 1;
        assert!(bytes_tamper
            .recheck_with_fresh_ay(Duration::from_mins(1))
            .is_err());

        let mut variant_tamper = checked;
        let identity = variant_tamper.summary.obligations[0].identity_sha256();
        let artifact_bytes = match &variant_tamper.obligation_payloads[0] {
            SealedReplayObligationPayload::GroundDerivation { artifact_bytes, .. } => {
                artifact_bytes.clone()
            }
            SealedReplayObligationPayload::Smt { .. } => {
                panic!("ground fixture must retain a ground derivation")
            }
        };
        variant_tamper.obligation_payloads[0] = SealedReplayObligationPayload::Smt {
            obligation_identity_sha256: identity,
            query_bytes: artifact_bytes,
            strict_bundle_bytes: None,
            alethe_bytes: None,
            source_authority: SmtSourceAuthority::Legacy,
        };
        assert!(variant_tamper
            .recheck_with_fresh_ay(Duration::from_mins(1))
            .is_err());
    }
}
