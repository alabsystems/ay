// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-only views over an atomically bound checked-replay result.

use super::{expected_verdict, verification_error, ChcCheckedReplayRun};
use crate::{
    ChcCheckedReplayObligation, ChcCheckedReplaySummary, ChcPdrProofRun, ChcProofArtifactDigest,
    ChcProofEvidenceManifest, ChcReplayObligationKind, ChcReplayPayloadFormat, ChcResult,
    ChcValidatedGroundDerivation,
};
use ay_core::time::Instant;
use std::time::Duration;

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
    },
    GroundDerivation {
        obligation_identity_sha256: String,
        artifact_bytes: Vec<u8>,
    },
}

impl SealedReplayObligationPayload {
    pub(super) fn try_new_smt(
        obligation: &ChcCheckedReplayObligation,
        query_bytes: Vec<u8>,
        strict_bundle_bytes: Option<Vec<u8>>,
        alethe_bytes: Option<Vec<u8>>,
    ) -> ChcResult<Self> {
        let payload = Self::Smt {
            obligation_identity_sha256: obligation.identity_sha256(),
            query_bytes,
            strict_bundle_bytes,
            alethe_bytes,
        };
        payload.validate(obligation)?;
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
            ChcReplayPayloadFormat::SmtlibV1 => {
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
        if obligation_identity_sha256 != &obligation.identity_sha256() {
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
                validate_payload_descriptor(obligation, query_bytes)?;
                match expected_verdict(obligation.kind) {
                    "unsat" => Self::validate_strict_bundle(
                        obligation,
                        strict_bundle_bytes.as_deref(),
                        alethe_bytes.as_deref(),
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
                ) || obligation.kind != ChcReplayObligationKind::TraceValidity
                    || obligation.strict_cert.is_some()
                {
                    return Err(verification_error(format!(
                        "checked replay obligation {} has an invalid ground-derivation row",
                        obligation.name
                    )));
                }
                validate_payload_descriptor(obligation, artifact_bytes)
            }
        }
    }

    fn validate_strict_bundle(
        obligation: &ChcCheckedReplayObligation,
        strict_bundle_bytes: Option<&[u8]>,
        alethe_bytes: Option<&[u8]>,
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
        if cert.bundle_sha256 != super::super::sha256_hex(bundle_bytes) {
            return Err(verification_error(format!(
                "checked replay obligation {} retained strict bundle digest mismatch",
                obligation.name
            )));
        }
        let bundle: ay_dpll::api::SerializableProofBundle = serde_json::from_slice(bundle_bytes)
            .map_err(|error| {
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
        let checked = ay_dpll::api::re_check_bundle_strict(&bundle).map_err(|error| {
            verification_error(format!(
                "checked replay obligation {} retained strict bundle recheck: {error}",
                obligation.name
            ))
        })?;
        if !checked.quality.is_complete()
            || checked.assume_terms.is_empty()
            || ordered_unique(&checked.assume_terms) != bundle.obligation_assertions
        {
            return Err(verification_error(format!(
                "checked replay obligation {} retained strict bundle lacks complete exact assumption authority",
                obligation.name
            )));
        }
        validate_alethe_bytes(obligation, cert.alethe_sha256.as_deref(), alethe_bytes)
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

fn remaining_budget(
    budget: Duration,
    start: &Instant,
    obligation: &ChcCheckedReplayObligation,
) -> ChcResult<Duration> {
    budget
        .checked_sub(start.elapsed())
        .filter(|remaining| !remaining.is_zero())
        .ok_or_else(|| {
            verification_error(format!(
                "checked replay fresh AY recheck budget exhausted before obligation {}",
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
    /// problem without solver search. Ground parsing is resource-bounded and
    /// checked against elapsed time before and after, but is not interruptible
    /// mid-validation. This is an in-memory recheck of a sealed
    /// [`ChcCheckedReplayRun`]; it does not claim that a separately transported
    /// schema-v3 bundle can authenticate arbitrary external query text by
    /// itself.
    pub fn recheck_with_fresh_ay(&self, budget: Duration) -> ChcResult<()> {
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
        let start = Instant::now();
        for item in self.obligation_payloads() {
            let obligation = item.obligation();
            item.payload.validate(obligation)?;
            let remaining = remaining_budget(budget, &start, obligation)?;
            match item.payload {
                SealedReplayObligationPayload::Smt { query_bytes, .. } => {
                    let query = std::str::from_utf8(query_bytes).map_err(|error| {
                        verification_error(format!(
                            "checked replay obligation {} retained query UTF-8: {error}",
                            obligation.name
                        ))
                    })?;
                    let expected = expected_verdict(obligation.kind);
                    if expected == "unsat" {
                        if crate::smt::executor_adapter::smtlib_strict_unsat_cert_via_executor(
                            query,
                            Some(remaining),
                        )
                        .is_none()
                        {
                            return Err(verification_error(format!(
                                "checked replay obligation {} fresh AY recheck expected unsat, got <execution-or-proof-error>",
                                obligation.name
                            )));
                        }
                    } else {
                        let actual =
                            crate::smt::executor_adapter::smtlib_first_verdict_via_executor(
                                query,
                                Some(remaining),
                            );
                        if actual.as_deref() != Some(expected) {
                            return Err(verification_error(format!(
                                "checked replay obligation {} fresh AY recheck expected {expected}, got {}",
                                obligation.name,
                                actual.as_deref().unwrap_or("<execution-error>")
                            )));
                        }
                    }
                }
                SealedReplayObligationPayload::GroundDerivation { artifact_bytes, .. } => {
                    // `remaining` is intentionally computed before this
                    // branch: even pure proof checking is budget-admitted at
                    // the same row boundary as solver-backed replay.
                    let _ = remaining;
                    let _validated = match obligation.payload_format {
                        ChcReplayPayloadFormat::GroundDerivationV1 => {
                            crate::validate_chc_ground_derivation_artifact(
                                self.proof_run.problem(),
                                artifact_bytes,
                            )
                        }
                        ChcReplayPayloadFormat::GroundDerivationV2 => {
                            crate::validate_chc_ground_derivation_artifact_v2(
                                self.proof_run.problem(),
                                artifact_bytes,
                            )
                        }
                        ChcReplayPayloadFormat::SmtlibV1 => {
                            return Err(verification_error(format!(
                                "checked replay obligation {} labels a ground derivation as SMT-LIB",
                                obligation.name
                            )));
                        }
                    }
                    .map_err(|error| {
                        verification_error(format!(
                            "checked replay obligation {} ground derivation recheck: {error}",
                            obligation.name
                        ))
                    })?;
                    if budget
                        .checked_sub(start.elapsed())
                        .filter(|remaining| !remaining.is_zero())
                        .is_none()
                    {
                        return Err(verification_error(format!(
                            "checked replay fresh AY recheck budget exhausted during obligation {}",
                            obligation.name
                        )));
                    }
                }
            }
        }
        Ok(())
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
        };
        assert!(variant_tamper
            .recheck_with_fresh_ay(Duration::from_mins(1))
            .is_err());
    }
}
