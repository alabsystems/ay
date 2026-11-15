// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Post-solve CHECKED replay pass for CHC proof runs.
//!
//! This is the executor that was missing between AY's replay-obligation
//! exporters (`InvariantModel::replay_obligations`,
//! `Counterexample::trace_validity_replay_obligations`,
//! `engines::chc_safe_replay_obligations`) and the fail-closed checked-replay
//! admission schema (`ChcCheckedReplaySummary` /
//! `try_with_checked_replay_summary`). It re-executes every digest-bound
//! SMT obligation query on a FRESH `ay-dpll` executor — independent of the
//! solving run. Multi-predicate Unsafe evidence instead uses AY's canonical
//! source-bound ground derivation and deciding evaluator, avoiding another
//! incomplete solver search. Only when every selected check passes does this
//! module assemble the checked replay artifacts, validate them against an
//! evidence manifest, and upgrade the proof transcript metadata to
//! `replayable` with concrete
//! transcript/replay/checked-report SHA-256 digests.
//!
//! SOUNDNESS: this pass never changes a solve verdict. It can only ever
//! ADMIT (attach checked evidence to) a result that was already sealed as
//! verified Safe/Unsafe, and every failure path — budget exhaustion, a parse
//! error, an executor panic, a single obligation returning anything other
//! than its expected verdict, or any digest-binding mismatch — leaves the run
//! exactly as metadata-only (non-admissible), which is the pre-existing
//! behavior. MODEL_CHECKER_CONSUMER-style consumers treat non-admissible transcripts as
//! demotion-net rejections, so "fail closed to metadata-only" is the safe
//! direction.
//!
//! Retained UNSAT replay uses one finite logical work/storage allowance across
//! all rows, live exact export, v4 transport, byte replay and artifact writing.
//! It accounts controlled proof operations, byte-buffer admission, row-vector
//! reservations, chunked hashes and output backing reservations. Intermediate
//! metadata JSON construction, source seals and result/summary clones still
//! have opaque, phase-polled allocation intervals. This is not complete
//! allocator accounting, a whole-call RSS ceiling or a hard latency guarantee.

use super::{
    ChcCheckedReplayArtifacts, ChcCheckedReplayObligation, ChcCheckedReplaySummary,
    ChcObligationStrictCert, ChcPdrProofRun, ChcProofArtifactDigest, ChcProofEvidenceManifest,
    ChcProofEvidenceOptions, ChcProofSolverIdentity, ChcProofTranscriptMetadata,
    ChcReplayCheckResult, ChcReplayCheckerIdentity, ChcReplayEvidence, ChcReplayObligationArtifact,
    CHC_IN_PROCESS_REPLAY_CHECKER_NAME,
};
use crate::classifier::ProblemClassifier;
use crate::pdr::{ChcReplayObligation, ChcReplayObligationKind};
use crate::smt::executor_adapter::{
    collect_uninterpreted_function_declarations, emit_declare_uninterpreted_function,
    smtlib_first_verdict_via_executor_with_limit as replay_smt_verdict, ReplayCancellation,
    ReplayLimit,
};
use crate::{
    ChcError, ChcExpr, ChcProblem, ChcResult, ChcSort, ChcVar, ClauseHead, PredicateId,
    VerifiedChcResult,
};
use ay_core::quote_symbol;
use ay_core::time::Instant;
use std::collections::BTreeMap;
use std::time::Duration;

mod checked_run;
mod compact_ground;
mod ground_export;
pub(crate) mod phase_probe;
#[cfg(test)]
mod progress_tests;
mod retained_resources;
mod strict_bundle;
pub use checked_run::ChcCheckedReplayObligationPayload;
use checked_run::SealedReplayObligationPayload;

/// Cap on clause instantiations while expanding an acyclic clause system into
/// one quantifier-free error-reachability query. Prevents pathological DAG
/// sharing from blowing up the synthesized obligation; exceeding the cap fails
/// closed to metadata-only.
const ACYCLIC_EXPANSION_MAX_INSTANTIATIONS: usize = 10_000;

/// Cap on predicate nesting depth during acyclic expansion (belt-and-braces
/// alongside the classifier's cycle check and the explicit occurs check).
const ACYCLIC_EXPANSION_MAX_DEPTH: usize = 128;

/// Solver-backed or proof-object-backed work selected for one checked run.
enum CheckedReplayPlan {
    Smt(Vec<ChcReplayObligation>),
    GroundDerivation {
        format: super::ChcReplayPayloadFormat,
        artifact_bytes: Vec<u8>,
    },
}

/// Owned caller binding, separate from the one call-wide progress allowance.
struct CheckedReplayBinding {
    options: ChcProofEvidenceOptions,
    solver: ChcProofSolverIdentity,
    obligation_id: String,
    base_evidence: Option<ChcReplayEvidence>,
}

fn replay_deadline(start: Instant, budget: Duration) -> ChcResult<Instant> {
    start.checked_add(budget).ok_or_else(|| {
        verification_error("checked replay budget cannot be represented as an absolute deadline")
    })
}

impl CheckedReplayPlan {
    fn len(&self) -> usize {
        match self {
            Self::Smt(obligations) => obligations.len(),
            Self::GroundDerivation { .. } => 1,
        }
    }

    fn is_empty(&self) -> bool {
        matches!(self, Self::Smt(obligations) if obligations.is_empty())
    }
}

/// Result of a successful post-solve checked replay pass.
///
/// Everything in here is bound together fail-closed: `manifest` admitted the
/// validated `summary` via `try_with_checked_replay_summary`, and
/// `proof_run.metadata()` is the upgraded (`replayable`) transcript whose
/// digests point at the byte payloads carried alongside.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ChcCheckedReplayRun {
    /// The sealed proof run with UPGRADED transcript metadata
    /// (`replay.status == transcript.status == "replayable"`,
    /// `trust_full_verifier_admissible() == true`).
    proof_run: ChcPdrProofRun,
    /// Evidence manifest with the checked replay summary attached
    /// (`trust_full_verifier_admissible() == true`).
    manifest: ChcProofEvidenceManifest,
    /// The validated checked replay summary.
    summary: ChcCheckedReplaySummary,
    /// Normalized CHC input bytes (the `problem` artifact).
    problem_bytes: Vec<u8>,
    /// Certificate bytes (the `proof-certificate` artifact).
    certificate_bytes: Vec<u8>,
    /// Deterministic solver run-log bytes (the `solver-transcript` artifact),
    /// when produced by this pass. `None` when the caller-supplied evidence
    /// already carried a solver transcript (e.g. the CLI trace file), whose
    /// bytes live at that artifact's recorded path.
    run_log_bytes: Option<Vec<u8>>,
    /// Replay log bytes: the per-obligation pass record (the `replay-report`
    /// artifact).
    replay_log_bytes: Vec<u8>,
    /// Checked proof report bytes: the summary JSON whose SHA-256 is emitted
    /// as `checked_report.sha256` in the transcript metadata.
    checked_report_bytes: Vec<u8>,
    /// Exact query/proof bytes sealed in one-to-one summary-row order.
    obligation_payloads: Vec<SealedReplayObligationPayload>,
}

fn verification_error(message: impl Into<String>) -> ChcError {
    ChcError::Verification(message.into())
}

fn dump_failed_obligation(obligation: &ChcReplayObligation) {
    let Some(dir) = ay_core::misc_cli_flags()
        .chc_dump_failed_replay_obligation
        .as_deref()
    else {
        return;
    };
    let path = format!("{dir}/{}.smt2", obligation.name);
    if std::fs::write(&path, &obligation.smtlib).is_ok() {
        eprintln!("[ay-chc] wrote failing replay obligation to {path}");
    }
}

/// Expected executor verdict for one replay obligation kind.
///
/// Safe-certificate obligations (initiation/consecution/safety — including
/// synthesized acyclic-exhaustion safety obligations and ghost-pair
/// discharges) assert a clause VIOLATION and must be `unsat`. The unsafe
/// SMT trace-validity obligation conjoins the unrolled system with the concrete
/// counterexample assignments and must be `sat`. Ground-derivation rows bypass
/// this mapping and are decided by the source-bound artifact validator.
fn expected_verdict(kind: ChcReplayObligationKind) -> &'static str {
    match kind {
        ChcReplayObligationKind::TraceValidity => "sat",
        _ => "unsat",
    }
}

impl ChcPdrProofRun {
    /// Run the post-solve CHECKED replay pass with default manifest binding.
    ///
    /// Renders the replay obligations for this sealed Safe/Unsafe result,
    /// re-executes each SMT query on a fresh executor with the remaining
    /// `budget`, and — only if every obligation returns its expected verdict — returns a
    /// [`ChcCheckedReplayRun`] whose transcript metadata is `replayable` and
    /// Trust-full-verifier admissible.
    ///
    /// Fail-closed: `Unknown` results, budget exhaustion, any obligation
    /// failure, and any digest-binding mismatch return `Err`, and callers must
    /// keep using the original metadata-only run.
    pub fn run_checked_replay(&self, budget: Duration) -> ChcResult<ChcCheckedReplayRun> {
        self.run_checked_replay_with_progress(budget, &mut || true)
    }

    /// Run checked replay with a caller-owned cooperative cancellation callback.
    ///
    /// Returning `false` permanently rejects this attempt without changing the
    /// original run. One time budget and callback cover default binding setup,
    /// ground export/validation and final checked-evidence publication. Ground
    /// interruption never selects a different format or an SMT fallback.
    ///
    /// SMT solving observes the original absolute deadline, but the borrowed
    /// callback is not polled asynchronously there. Metadata, strict bundle
    /// export/rechecking, arithmetic, serde and cleanup retain opaque intervals.
    /// Post-phase checks include worker cleanup; no hard deadline or 100 ms
    /// latency is guaranteed. Zero or unrepresentable budgets reject before
    /// invoking the callback.
    pub fn run_checked_replay_with_progress(
        &self,
        budget: Duration,
        callback: &mut dyn FnMut() -> bool,
    ) -> ChcResult<ChcCheckedReplayRun> {
        self.run_checked_replay_with_progress_and_cancellation(budget, callback, None)
    }

    /// Run checked replay with a thread-safe caller cancellation token.
    ///
    /// The token and its inherited parent flags reach active SMT search and
    /// mandatory certification as well as cooperative replay boundaries. An
    /// observed request is sticky for this attempt, even after caller reset.
    /// Caller tokens are never set or reset by replay. Opaque export, offline
    /// checking, serialization and cleanup remain; no hard return-time or
    /// approximately 100 ms latency guarantee is made.
    pub fn run_checked_replay_with_cancellation(
        &self,
        budget: Duration,
        cancellation: &crate::CancellationToken,
    ) -> ChcResult<ChcCheckedReplayRun> {
        self.run_checked_replay_with_progress_and_cancellation(
            budget,
            &mut || true,
            Some(cancellation),
        )
    }

    pub(crate) fn run_checked_replay_with_progress_and_cancellation(
        &self,
        budget: Duration,
        callback: &mut dyn FnMut() -> bool,
        cancellation: Option<&crate::CancellationToken>,
    ) -> ChcResult<ChcCheckedReplayRun> {
        self.run_checked_replay_with_controls_started_at(
            Instant::now(),
            budget,
            callback,
            cancellation,
        )
    }

    pub(crate) fn run_checked_replay_with_controls_started_at(
        &self,
        start: Instant,
        budget: Duration,
        callback: &mut dyn FnMut() -> bool,
        cancellation: Option<&crate::CancellationToken>,
    ) -> ChcResult<ChcCheckedReplayRun> {
        self.run_checked_replay_with_binding_factory(start, budget, callback, cancellation, || {
            let engine = self.metadata.engine.clone();
            let mut options = ChcProofEvidenceOptions::pdr_strict(&crate::PdrConfig::default());
            options.proof_mode = format!("checked-replay:{engine}");
            CheckedReplayBinding {
                options,
                solver: ChcProofSolverIdentity::new(engine),
                obligation_id: format!(
                    "ay-chc:checked-replay:{}",
                    self.metadata.normalized_input_sha256
                ),
                base_evidence: None,
            }
        })
    }

    fn run_checked_replay_with_binding_factory(
        &self,
        start: Instant,
        budget: Duration,
        callback: &mut dyn FnMut() -> bool,
        cancellation: Option<&crate::CancellationToken>,
        binding: impl FnOnce() -> CheckedReplayBinding,
    ) -> ChcResult<ChcCheckedReplayRun> {
        if budget.is_zero() {
            return Err(verification_error(
                "checked replay budget is zero; staying metadata-only",
            ));
        }
        let original_deadline = replay_deadline(start, budget)?;
        // Snapshot the later caller's controls before any retained callback
        // can remove or replace their ambient scopes.
        let caller_interrupt = crate::smt::deadline::lane_interrupt_flag();
        let control = crate::smt::replay_control::ScopedReplayControl::install_until(
            original_deadline,
            cancellation,
        );
        let mut compact_owner = match &self.result {
            VerifiedChcResult::Unsafe(cex) => cex
                .counterexample()
                .compact_evidence()
                .map(|evidence| evidence.owner()),
            _ => None,
        };
        let caller_stop = compact_ground::capture_caller(compact_owner.as_mut())?;
        compact_ground::admit_control(
            compact_owner.as_mut(),
            &control,
            caller_interrupt.as_deref(),
        )?;
        // Install the retained observer before any later admission can consume
        // a one-shot original callback without latching the witness owner.
        let _compact_scope = compact_owner.as_ref().map(|owner| owner.enter());
        if let Some(owner) = &mut compact_owner {
            owner
                .poll()
                .map_err(|error| verification_error(error.to_string()))?;
        }
        compact_ground::admit_control(
            compact_owner.as_mut(),
            &control,
            caller_interrupt.as_deref(),
        )?;
        let deadline = control.deadline();
        let cancellation = control.cancellation().map(ReplayCancellation::new);
        let limit = match &cancellation {
            Some(cancellation) => ReplayLimit::Cancellable {
                deadline,
                cancellation,
            },
            None => ReplayLimit::Until(deadline),
        };
        let mut continuation = compact_ground::continuation(
            compact_owner.as_ref(),
            callback,
            caller_stop,
            &control,
            caller_interrupt,
        );
        // One retained row per original clause at most: the single request
        // owner may declare that many obligations, one work envelope each.
        let mut progress = ground_export::ReplayProgress::new_retained_for_rows(
            limit,
            &mut continuation,
            self.problem().clauses().len(),
        )
        .map_err(|error| {
            // Admission can reject an elapsed limit before its first
            // callback. That refusal still belongs to the witness.
            if let Some(owner) = &mut compact_owner {
                let _ = owner.refuse::<()>(crate::ground_derivation::compact::Error::Stopped);
            }
            error
        })?;
        if let Some(owner) = compact_owner {
            progress.retain_compact_owner(owner)?;
        }
        progress.check()?;
        // Binding construction (including caller-defined ID conversion) occurs
        // only after entry admission. The worker checks again before use.
        let checked = self.run_checked_replay_with_control(binding(), limit, &mut progress)?;
        // The worker's plan, proof/report intermediates and other locals have
        // now been destroyed. Charge that cleanup before public admission.
        progress.check()?;
        Ok(checked)
    }

    /// Run the checked replay pass against caller-supplied manifest binding
    /// parts (options/solver/obligation id) and optional pre-built replay
    /// evidence (e.g. the CLI's evidence carrying a trace-file transcript and
    /// on-disk obligation artifact paths).
    ///
    /// When `base_evidence` already carries replay obligation artifacts, their
    /// digest set must exactly match the obligations this pass renders and
    /// executes — otherwise the pass fails closed.
    ///
    /// Ground export and validation cooperatively poll the same original
    /// `budget`; cancellation never selects another format or an SMT fallback.
    /// Rendering, metadata authentication, strict SMT bundles, arithmetic,
    /// serialization internals and allocation/destruction retain opaque phases.
    /// Post-phase and final checks reject observed budget exhaustion before
    /// publishing checked evidence; they do not promise a hard deadline or a
    /// 100 ms response time.
    pub fn run_checked_replay_with_binding(
        &self,
        options: ChcProofEvidenceOptions,
        solver: ChcProofSolverIdentity,
        obligation_id: impl Into<String>,
        base_evidence: Option<ChcReplayEvidence>,
        budget: Duration,
    ) -> ChcResult<ChcCheckedReplayRun> {
        self.run_checked_replay_with_binding_and_progress(
            options,
            solver,
            obligation_id,
            base_evidence,
            budget,
            &mut || true,
        )
    }

    /// Run caller-bound checked replay with cooperative cancellation.
    ///
    /// This preserves [`Self::run_checked_replay_with_binding`]'s exact source
    /// and artifact admission rules. A callback refusal is sticky across every
    /// selected ground format and fresh validation, and prevents publication.
    /// The original budget begins before converting `obligation_id`; no inner
    /// phase receives a fresh duration. Zero or unrepresentable budgets reject
    /// before conversion or callback. Supplied options/evidence remain
    /// untrusted binding inputs.
    ///
    /// Opaque SMT, metadata, arithmetic, serde and allocation/cleanup phases
    /// remain; see [`Self::run_checked_replay_with_progress`]. This API does not
    /// promise a hard wall-clock deadline or asynchronous caller cancellation
    /// inside SMT. The original deadline is enforced independently there.
    pub fn run_checked_replay_with_binding_and_progress(
        &self,
        options: ChcProofEvidenceOptions,
        solver: ChcProofSolverIdentity,
        obligation_id: impl Into<String>,
        base_evidence: Option<ChcReplayEvidence>,
        budget: Duration,
        callback: &mut dyn FnMut() -> bool,
    ) -> ChcResult<ChcCheckedReplayRun> {
        self.run_checked_replay_with_binding_factory(Instant::now(), budget, callback, None, || {
            CheckedReplayBinding {
                options,
                solver,
                obligation_id: obligation_id.into(),
                base_evidence,
            }
        })
    }

    /// Run caller-bound replay with an owned observation of a cancellation token.
    ///
    /// Exact manifest, source, payload and proof admission rules match
    /// [`Self::run_checked_replay_with_binding`]. The full token, including
    /// inherited parents, reaches active SMT and cooperative ground validation.
    /// Observed refusal is sticky and never selects a different format or
    /// fallback. This call does not set or reset the supplied token.
    ///
    /// One original wall starts before supplied-ID conversion. Zero or
    /// unrepresentable budgets and pre-cancellation refuse before conversion;
    /// a request observed after conversion still prevents publication.
    /// Conversion and opaque intervals within offline proof checking are not
    /// forcibly interrupted. No hard return-time or 100 ms guarantee is made.
    pub fn run_checked_replay_with_binding_and_cancellation(
        &self,
        options: ChcProofEvidenceOptions,
        solver: ChcProofSolverIdentity,
        obligation_id: impl Into<String>,
        base_evidence: Option<ChcReplayEvidence>,
        budget: Duration,
        cancellation: &crate::CancellationToken,
    ) -> ChcResult<ChcCheckedReplayRun> {
        self.run_checked_replay_with_binding_factory(
            Instant::now(),
            budget,
            &mut || true,
            Some(cancellation),
            || CheckedReplayBinding {
                options,
                solver,
                obligation_id: obligation_id.into(),
                base_evidence,
            },
        )
    }

    fn run_checked_replay_with_control(
        &self,
        binding: CheckedReplayBinding,
        limit: ReplayLimit<'_>,
        progress: &mut ground_export::ReplayProgress<'_>,
    ) -> ChcResult<ChcCheckedReplayRun> {
        let CheckedReplayBinding {
            options,
            solver,
            obligation_id,
            base_evidence,
        } = binding;
        let problem = self.problem();
        progress.check()?;
        let preferred_ground_format = match &base_evidence {
            Some(evidence) if !evidence.replay_obligations.is_empty() => evidence
                .replay_obligations
                .iter()
                .find_map(|artifact| match artifact.payload_format {
                    format @ (super::ChcReplayPayloadFormat::GroundDerivationV1
                    | super::ChcReplayPayloadFormat::GroundDerivationV2
                    | super::ChcReplayPayloadFormat::CompactGroundDerivationV1) => {
                        Some(Some(format))
                    }
                    super::ChcReplayPayloadFormat::SmtlibV1 => None,
                })
                .unwrap_or(None),
            _ => Some(super::ChcReplayPayloadFormat::SmtlibV1),
        };
        progress.check()?;

        // 1. Render the obligations for this sealed result.
        let (certificate, plan) = phase_probe::result(phase_probe::Phase::Render, limit, || {
            Ok(match &self.result {
                VerifiedChcResult::Safe(inv) => {
                    let certificate = inv.model().to_certificate(problem);
                    progress.check()?;
                    let mut obligations =
                        crate::engines::chc_safe_replay_obligations(problem, inv.model())?;
                    progress.check()?;
                    if obligations.is_empty() {
                        // Empty-model acyclic-exhaustion certificate: the sound
                        // replay set is the depth-exhaustion UNSAT check itself,
                        // synthesized as one Safety obligation per query clause.
                        obligations = acyclic_exhaustion_replay_obligations(problem)?;
                    }
                    (certificate, CheckedReplayPlan::Smt(obligations))
                }
                VerifiedChcResult::Unsafe(cex) => {
                    let certificate = cex.counterexample().to_certificate(problem);
                    progress.check()?;
                    if let Some(plan) =
                        compact_ground::select_plan(self, preferred_ground_format, progress)?
                    {
                        return Ok((certificate, plan));
                    }
                    let plan = ground_export::select_plan(
                        preferred_ground_format,
                        |format, progress| {
                            match format {
                        super::ChcReplayPayloadFormat::GroundDerivationV1 => {
                            self.unsafe_ground_derivation_artifact_bytes_with_progress(progress)
                        }
                        super::ChcReplayPayloadFormat::GroundDerivationV2 => {
                            self.unsafe_ground_derivation_artifact_v2_bytes_with_progress(progress)
                        }
                        super::ChcReplayPayloadFormat::CompactGroundDerivationV1 => {
                            self.unsafe_compact_ground_derivation_artifact_bytes_with_progress(progress)
                        }
                        super::ChcReplayPayloadFormat::SmtlibV1 => {
                            Err(crate::ChcGroundDerivationArtifactError {
                                reason:
                                    crate::ChcGroundDerivationArtifactErrorReason::SchemaMismatch,
                                reason_code: "schema_mismatch",
                                detail: "ground exporter cannot select SMT-LIB".to_string(),
                            })
                        }
                    }
                        },
                        || {
                            cex.counterexample()
                                .trace_validity_replay_obligations(problem)
                        },
                        progress,
                    )?;
                    (certificate, plan)
                }
                _ => {
                    return Err(verification_error(
                        "checked replay requires a verified Safe/Unsafe proof result",
                    ));
                }
            })
        })?;
        phase_probe::rendered_rows(plan.len(), limit);
        progress.check()?;
        if plan.is_empty() {
            return Err(verification_error(
                "checked replay found no obligations to execute",
            ));
        }

        // 2. Check every obligation. SMT executors receive the SAME absolute
        // deadline, including time already spent preparing this row. Ground
        // export and validation share it through the caller's progress polls.
        let mut checked_rows = retained_resources::vector(plan.len(), &mut |work, bytes| {
            progress.charge(work, bytes)
        })?;
        let mut obligation_payloads =
            retained_resources::vector(plan.len(), &mut |work, bytes| {
                progress.charge(work, bytes)
            })?;
        let mut replay_records = retained_resources::vector(plan.len(), &mut |work, bytes| {
            progress.charge(work, bytes)
        })?;
        if let CheckedReplayPlan::Smt(obligations) = &plan {
            for (row_index, obligation) in obligations.iter().enumerate() {
                progress.check()?;
                if limit.check().is_none() {
                    return Err(verification_error(format!(
                        "checked replay budget exhausted or interrupted before obligation {}",
                        obligation.name
                    )));
                }
                let expected = expected_verdict(obligation.kind);
                let _row_scope = phase_probe::row_scope(phase_probe::Row {
                    row: row_index,
                    clause: obligation.clause_index,
                    kind: match obligation.kind {
                        ChcReplayObligationKind::Initiation => 1,
                        ChcReplayObligationKind::Consecution => 2,
                        ChcReplayObligationKind::Safety => 3,
                        ChcReplayObligationKind::TraceValidity => 4,
                    },
                    bytes: obligation.smtlib.len(),
                });

                let (checker_command, strict_cert, bound_retained) = if expected == "unsat" {
                    let strict_bundle::RetainedDischarge {
                        cert,
                        bound,
                        checker_command,
                    } = strict_bundle::discharge_retained(obligation, progress.retained_mut()?)?;
                    (checker_command, Some(cert), Some(bound))
                } else {
                    // SAT trace-validity obligations have no UNSAT proof. The
                    // executor checks their concrete witness by verdict.
                    let verdict = replay_smt_verdict(&obligation.smtlib, limit, None);
                    if verdict.as_deref() != Some(expected) {
                        return Err(verification_error(format!(
                            "checked replay obligation {} expected {expected}, got {}",
                            obligation.name,
                            verdict.as_deref().unwrap_or("<execution-error>")
                        )));
                    }
                    (
                        format!(
                            "{CHC_IN_PROCESS_REPLAY_CHECKER_NAME} --expect {expected} {}",
                            obligation.name
                        ),
                        None,
                        None,
                    )
                };
                progress.check()?;
                let query = retained_resources::artifact(
                    "replay-obligation",
                    obligation.smtlib.as_bytes(),
                    &mut |work, bytes| progress.charge(work, bytes),
                )?;
                let row_bytes = obligation
                    .name
                    .len()
                    .checked_mul(12)
                    .and_then(|bytes| bytes.checked_add(8192))
                    .ok_or_else(|| verification_error("checked replay record size overflow"))?;
                retained_resources::admit(
                    &mut |work, bytes| progress.charge(work, bytes),
                    row_bytes,
                    row_bytes,
                )?;
                replay_records.push(serde_json::json!({
                    "name": obligation.name,
                    "kind": obligation.kind.as_str(),
                    "payload_format": "smtlib-v1",
                    "clause_index": obligation.clause_index,
                    "query_sha256": query.sha256,
                    "expected": expected,
                    "verdict": expected,
                    "status": "pass",
                    "strict_bundle": strict_cert.is_some(),
                    "strict_alethe": strict_cert
                        .as_ref()
                        .is_some_and(|cert| cert.alethe_sha256.is_some()),
                    "strict_cert": strict_cert.as_ref().map(ChcObligationStrictCert::to_json_value),
                }));
                let mut row = ChcCheckedReplayObligation::new(
                    obligation.name.clone(),
                    obligation.kind,
                    query,
                    checker_command,
                    ChcReplayCheckResult::pass(),
                );
                if let Some(cert) = strict_cert {
                    row = row.with_strict_cert(cert);
                }
                let payload = match bound_retained {
                    Some(bound) => SealedReplayObligationPayload::try_new_retained(
                        &row,
                        bound,
                        progress.retained_mut()?,
                    )?,
                    None => {
                        retained_resources::admit(
                            &mut |work, bytes| progress.charge(work, bytes),
                            obligation.smtlib.len(),
                            obligation.smtlib.len(),
                        )?;
                        SealedReplayObligationPayload::try_new_smt_with_progress(
                            &row,
                            obligation.smtlib.as_bytes().to_vec(),
                            None,
                            None,
                            &mut || progress.poll(),
                        )?
                    }
                };
                checked_rows.push(row);
                obligation_payloads.push(payload);
                progress.check()?;
            }
        }
        if let CheckedReplayPlan::GroundDerivation {
            format,
            artifact_bytes,
        } = plan
        {
            if format == super::ChcReplayPayloadFormat::CompactGroundDerivationV1 {
                let (row, payload, record) =
                    compact_ground::check_row(self, artifact_bytes, progress)?;
                checked_rows.push(row);
                obligation_payloads.push(payload);
                replay_records.push(record);
            } else {
                let validated =
                    ground_export::validate_ground(problem, format, &artifact_bytes, progress)?;
                let name = super::replay_payload_role(format);
                let expected = "valid";
                let query = ChcProofArtifactDigest::from_bytes(name, &artifact_bytes);
                let checker_command = format!(
                    "{CHC_IN_PROCESS_REPLAY_CHECKER_NAME} --validate-{} {name}",
                    format.as_str()
                );
                replay_records.push(serde_json::json!({
                    "name": name,
                    "kind": ChcReplayObligationKind::TraceValidity.as_str(),
                    "payload_format": format.as_str(),
                    "query_sha256": query.sha256,
                    "expected": expected,
                    "verdict": expected,
                    "status": "pass",
                    "step_count": validated.step_count(),
                    "strict_bundle": false,
                    "strict_alethe": false,
                    "strict_cert": null,
                }));
                let row = ChcCheckedReplayObligation::new(
                    name,
                    ChcReplayObligationKind::TraceValidity,
                    query,
                    checker_command,
                    ChcReplayCheckResult::pass(),
                );
                let row = match format {
                    super::ChcReplayPayloadFormat::GroundDerivationV1 => {
                        row.with_ground_derivation_payload()
                    }
                    super::ChcReplayPayloadFormat::GroundDerivationV2 => {
                        row.with_ground_derivation_v2_payload()
                    }
                    super::ChcReplayPayloadFormat::SmtlibV1
                    | super::ChcReplayPayloadFormat::CompactGroundDerivationV1 => {
                        unreachable!("ground replay plan cannot contain an SMT payload")
                    }
                };
                let payload = SealedReplayObligationPayload::try_new_ground_derivation(
                    &row,
                    &validated,
                    artifact_bytes,
                )?;
                progress.check()?;
                checked_rows.push(row);
                obligation_payloads.push(payload);
            }
        }

        // 3. Assemble the checked replay artifacts.
        progress.check()?;
        let normalized = super::normalized_chc_input(problem);
        let problem_bytes = normalized.into_bytes();
        let problem_digest =
            retained_resources::artifact("problem", &problem_bytes, &mut |work, bytes| {
                progress.charge(work, bytes)
            })?;
        let certificate_bytes = certificate.into_bytes();
        progress.check()?;

        let checker = ChcReplayCheckerIdentity::new(
            CHC_IN_PROCESS_REPLAY_CHECKER_NAME,
            format!("ay-chc {}", env!("CARGO_PKG_VERSION")),
            false,
        );
        let command = format!(
            "{CHC_IN_PROCESS_REPLAY_CHECKER_NAME} --engine {} --obligations {}",
            self.metadata.engine,
            checked_rows.len()
        );
        let has_typed_ground_payload = checked_rows
            .iter()
            .any(|row| super::is_ground_derivation_payload(row.payload_format));

        let mut evidence = base_evidence.unwrap_or_else(|| {
            ChcReplayEvidence::new(
                problem_digest.sha256.clone(),
                options.identity_sha256(),
                solver.identity_sha256(),
                obligation_id.clone(),
                self.metadata.result.clone(),
                self.metadata.proof_status.clone(),
            )
        });

        // Bind or cross-check the obligation artifact set.
        if evidence.replay_obligations.is_empty() {
            for row in &checked_rows {
                evidence = evidence.with_replay_obligation(
                    ChcReplayObligationArtifact::new(row.kind, row.query.clone())
                        .with_payload_format(row.payload_format),
                );
            }
        } else {
            let mut evidence_set: Vec<_> = evidence
                .replay_obligations
                .iter()
                .map(|artifact| {
                    (
                        artifact.kind.as_str().to_string(),
                        artifact.payload_format.as_str().to_string(),
                        artifact.query.sha256.clone(),
                        artifact.query.bytes,
                    )
                })
                .collect();
            let mut executed_set: Vec<_> = checked_rows
                .iter()
                .map(|row| {
                    (
                        row.kind.as_str().to_string(),
                        row.payload_format.as_str().to_string(),
                        row.query.sha256.clone(),
                        row.query.bytes,
                    )
                })
                .collect();
            evidence_set.sort();
            executed_set.sort();
            if evidence_set != executed_set {
                return Err(verification_error(
                    "checked replay executed obligations do not match the supplied replay evidence obligation artifacts",
                ));
            }
        }
        progress.check()?;

        // Certificate artifact: reuse the evidence binding when present (the
        // CLI wrote the identical certificate text to disk), else attach ours.
        let certificate_digest = match evidence.proof.clone() {
            Some(existing) => {
                let ours = retained_resources::artifact(
                    "proof-certificate",
                    &certificate_bytes,
                    &mut |work, bytes| progress.charge(work, bytes),
                )?;
                if existing.sha256 != ours.sha256 || existing.bytes != ours.bytes {
                    return Err(verification_error(
                        "checked replay certificate does not match the supplied proof artifact digest",
                    ));
                }
                existing
            }
            None => {
                let digest = retained_resources::artifact(
                    "proof-certificate",
                    &certificate_bytes,
                    &mut |work, bytes| progress.charge(work, bytes),
                )?;
                evidence = evidence.with_proof(digest.clone());
                digest
            }
        };

        // Solver transcript (run log): reuse the evidence transcript when the
        // caller already recorded one (e.g. the CLI trace file); otherwise
        // synthesize a deterministic run-log artifact from the sealed run.
        let (run_log_digest, run_log_bytes) = match evidence.solver_transcript.clone() {
            Some(existing) => (existing, None),
            None => {
                let run_log_value = serde_json::json!({
                    "schema": if has_typed_ground_payload {
                        "ay.chc-checked-replay-run-log/v2"
                    } else {
                        "ay.chc-checked-replay-run-log/v1"
                    },
                    "schema_version": if has_typed_ground_payload { 2 } else { 1 },
                    "engine": self.metadata.engine,
                    "result": self.metadata.result,
                    "proof_status": self.metadata.proof_status,
                    "normalized_input_sha256": self.metadata.normalized_input_sha256,
                    "obligation_count": checked_rows.len(),
                    "obligations": checked_rows
                        .iter()
                        .map(|row| serde_json::json!({
                            "name": row.name,
                            "kind": row.kind.as_str(),
                            "payload_format": row.payload_format.as_str(),
                            "query_sha256": row.query.sha256,
                        }))
                        .collect::<Vec<_>>(),
                });
                let bytes = retained_resources::encode(&run_log_value, &mut |work, bytes| {
                    progress.charge(work, bytes)
                })?;
                let digest = retained_resources::artifact(
                    "solver-transcript",
                    &bytes,
                    &mut |work, bytes| progress.charge(work, bytes),
                )?;
                evidence = evidence.with_solver_transcript(digest.clone());
                (digest, Some(bytes))
            }
        };
        progress.check()?;

        // Replay log (the pass record) is always produced by this pass and
        // replaces any placeholder replay report on the supplied evidence.
        let replay_log_value = serde_json::json!({
            "schema": if has_typed_ground_payload {
                "ay.chc-checked-replay-log/v2"
            } else {
                "ay.chc-checked-replay-log/v1"
            },
            "schema_version": if has_typed_ground_payload { 2 } else { 1 },
            "status": "pass",
            "checker": checker.to_json_value(),
            "command": command,
            "problem_sha256": problem_digest.sha256,
            "obligations": replay_records,
        });
        let replay_log_bytes =
            retained_resources::encode(&replay_log_value, &mut |work, bytes| {
                progress.charge(work, bytes)
            })?;
        let replay_log_digest = retained_resources::artifact(
            "replay-report",
            &replay_log_bytes,
            &mut |work, bytes| progress.charge(work, bytes),
        )?;
        evidence.replay_report = Some(replay_log_digest.clone());
        progress.check()?;

        // 4. Build the manifest, validate the summary against it, and admit.
        let manifest =
            self.evidence_manifest_with_replay_evidence(options, solver, obligation_id, evidence);
        let artifacts = ChcCheckedReplayArtifacts::new(
            problem_digest,
            certificate_digest,
            run_log_digest,
            replay_log_digest,
        );
        let summary = ChcCheckedReplaySummary::from_passed_manifest_replay(
            &manifest,
            artifacts,
            checker,
            command,
            checked_rows,
        )
        .map_err(|error| verification_error(error.to_string()))?;
        progress.check()?;
        let in_process_seal = super::ChcInProcessReplaySeal::new(&summary, problem);
        let checked_report_bytes =
            retained_resources::encode(&summary.to_json_value(), &mut |work, bytes| {
                progress.charge(work, bytes)
            })?;
        let checked_report_sha256 =
            retained_resources::hash(&checked_report_bytes, &mut |work, bytes| {
                progress.charge(work, bytes)
            })?;
        let manifest = manifest
            .try_with_in_process_checked_replay_summary(summary.clone(), in_process_seal)
            .map_err(|error| verification_error(error.to_string()))?;
        progress.check()?;

        // 5. Upgrade the transcript metadata (fail-closed constructor).
        let metadata = ChcProofTranscriptMetadata::for_checked_run(
            &self.metadata,
            &manifest,
            &checked_report_sha256,
        )
        .ok_or_else(|| {
            verification_error("checked replay metadata upgrade rejected; staying metadata-only")
        })?;

        let checked = ChcCheckedReplayRun {
            proof_run: self.with_metadata(metadata),
            manifest,
            summary,
            problem_bytes,
            certificate_bytes,
            run_log_bytes,
            replay_log_bytes,
            checked_report_bytes,
            obligation_payloads,
        };
        // `with_metadata` clones the retained result and metadata. Poll after
        // that opaque work too, before the local capability can escape.
        progress.check()?;
        Ok(checked)
    }
}

/// Synthesize the checked-replay obligations for an empty-model
/// acyclic-exhaustion SAFE certificate: one Safety-kind obligation per query
/// clause encoding the depth-exhaustion UNSAT check.
///
/// The obligation formula is the full acyclic inlining of the query clause's
/// error-reachability condition: every body predicate occurrence is replaced
/// by the disjunction over its defining clauses (constraint + head-argument
/// equations + recursively inlined body predicates), with every clause
/// instantiation renamed apart into fresh constants. Because the clause system
/// is acyclic, the inlining terminates and, because the resulting sentence is
/// purely existential, the fresh constants are exact skolem witnesses — the
/// query is satisfiable iff a real derivation of the error state exists. An
/// `unsat` verdict on every obligation therefore independently re-establishes
/// exactly what the exhaustive acyclic BMC certificate claims.
///
/// Query-irrelevant dead-end cycles are removed with the same deterministic,
/// verdict-preserving transform used by the acyclic certificate solve and
/// validation paths. The original problem still owns query clause indices and
/// normalized-input binding; only cycle classification and recursive expansion
/// use the stripped clone.
///
/// Fail-closed guards: cycles remaining in the query cone after that transform,
/// non-scalar sorts (arrays, reals, datatypes, uninterpreted sorts), missing
/// query clauses, and expansions exceeding
/// [`ACYCLIC_EXPANSION_MAX_INSTANTIATIONS`] all return `Err`, which keeps the
/// run metadata-only.
pub(crate) fn acyclic_exhaustion_replay_obligations(
    problem: &ChcProblem,
) -> ChcResult<Vec<ChcReplayObligation>> {
    if problem.has_array_sorts() || problem.has_real_sorts() || problem.has_datatype_sorts() {
        return Err(verification_error(
            "acyclic-exhaustion replay export supports scalar (Bool/Int/BitVec) problems only",
        ));
    }
    for predicate in problem.predicates() {
        for sort in &predicate.arg_sorts {
            if !is_scalar_sort(sort) {
                return Err(verification_error(
                    "acyclic-exhaustion replay export supports scalar (Bool/Int/BitVec) problems only",
                ));
            }
        }
    }
    let mut obligations = Vec::new();
    for (clause_index, formula) in acyclic_exhaustion_query_formulas(problem)? {
        let name = format!("clause-{clause_index}-safety-acyclic-exhaustion");
        let smtlib = render_acyclic_exhaustion_obligation(problem, &name, clause_index, &formula)?;
        obligations.push(ChcReplayObligation {
            name,
            kind: ChcReplayObligationKind::Safety,
            clause_index,
            smtlib,
        });
    }
    Ok(obligations)
}

/// The per-query-clause inlining formulas behind
/// [`acyclic_exhaustion_replay_obligations`], as `(clause_index, formula)`,
/// without that exporter's scalar-sort rendering guard. Each formula is
/// satisfiable iff a derivation of that query exists. The independent
/// empty-model check (`crate::empty_acyclic_safe_check`) decides these for
/// nonlinear query cones; its callers own their theory admission.
pub(crate) fn acyclic_exhaustion_query_formulas(
    problem: &ChcProblem,
) -> ChcResult<Vec<(usize, ChcExpr)>> {
    let mut expansion_problem = problem.clone();
    expansion_problem.strip_dead_end_cycle_predicates();
    let features = ProblemClassifier::classify(&expansion_problem);
    if features.has_cycles {
        return Err(verification_error(
            "acyclic-exhaustion replay export requires an acyclic clause system",
        ));
    }

    let mut formulas = Vec::new();
    let mut expansion = AcyclicExpansion::default();
    for (clause_index, clause) in problem.clauses().iter().enumerate() {
        if !matches!(clause.head, ClauseHead::False) {
            continue;
        }
        let subst = expansion.fresh_substitution(clause);
        let mut conjuncts = Vec::new();
        if let Some(constraint) = &clause.body.constraint {
            conjuncts.push(constraint.substitute(&subst));
        }
        for (pred_id, args) in &clause.body.predicates {
            let renamed_args: Vec<ChcExpr> =
                args.iter().map(|arg| arg.substitute(&subst)).collect();
            conjuncts.push(expansion.expand_predicate(
                &expansion_problem,
                *pred_id,
                &renamed_args,
                &mut Vec::new(),
            )?);
        }
        formulas.push((clause_index, ChcExpr::and_all(conjuncts)));
    }
    if formulas.is_empty() {
        return Err(verification_error(
            "acyclic-exhaustion replay export found no query clause",
        ));
    }
    Ok(formulas)
}

fn is_scalar_sort(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Bool | ChcSort::Int | ChcSort::BitVec(_))
}

#[derive(Default)]
struct AcyclicExpansion {
    instantiations: usize,
}

impl AcyclicExpansion {
    fn fresh_substitution(&mut self, clause: &crate::HornClause) -> Vec<(ChcVar, ChcExpr)> {
        let instance = self.instantiations;
        self.instantiations += 1;
        clause
            .vars()
            .into_iter()
            .map(|var| {
                let fresh = ChcVar::new(format!("__acx{instance}_{}", var.name), var.sort.clone());
                (var, ChcExpr::var(fresh))
            })
            .collect()
    }

    fn expand_predicate(
        &mut self,
        problem: &ChcProblem,
        pred_id: PredicateId,
        args: &[ChcExpr],
        stack: &mut Vec<PredicateId>,
    ) -> ChcResult<ChcExpr> {
        if stack.contains(&pred_id) {
            return Err(verification_error(
                "acyclic-exhaustion replay export hit a predicate cycle",
            ));
        }
        if stack.len() >= ACYCLIC_EXPANSION_MAX_DEPTH {
            return Err(verification_error(
                "acyclic-exhaustion replay export exceeded the expansion depth cap",
            ));
        }
        stack.push(pred_id);
        let mut disjuncts = Vec::new();
        for clause in problem.clauses() {
            let ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
                continue;
            };
            if *head_pred != pred_id {
                continue;
            }
            if head_args.len() != args.len() {
                stack.pop();
                return Err(verification_error(
                    "acyclic-exhaustion replay export found a head arity mismatch",
                ));
            }
            if self.instantiations >= ACYCLIC_EXPANSION_MAX_INSTANTIATIONS {
                stack.pop();
                return Err(verification_error(
                    "acyclic-exhaustion replay export exceeded the expansion size cap",
                ));
            }
            let subst = self.fresh_substitution(clause);
            let mut conjuncts = Vec::new();
            for (head_arg, actual) in head_args.iter().zip(args.iter()) {
                conjuncts.push(ChcExpr::eq(head_arg.substitute(&subst), actual.clone()));
            }
            if let Some(constraint) = &clause.body.constraint {
                conjuncts.push(constraint.substitute(&subst));
            }
            for (body_pred, body_args) in &clause.body.predicates {
                let renamed_args: Vec<ChcExpr> =
                    body_args.iter().map(|arg| arg.substitute(&subst)).collect();
                conjuncts.push(self.expand_predicate(problem, *body_pred, &renamed_args, stack)?);
            }
            disjuncts.push(ChcExpr::and_all(conjuncts));
        }
        stack.pop();
        if disjuncts.is_empty() {
            // Predicate with no defining clause is unreachable/underivable.
            return Ok(ChcExpr::Bool(false));
        }
        Ok(ChcExpr::or_all(disjuncts))
    }
}

fn render_acyclic_exhaustion_obligation(
    problem: &ChcProblem,
    name: &str,
    clause_index: usize,
    formula: &ChcExpr,
) -> ChcResult<String> {
    use std::fmt::Write;

    let mut vars = BTreeMap::new();
    for var in formula.vars() {
        vars.insert(var.name.clone(), var.sort);
    }

    let mut out = String::new();
    let _ = writeln!(out, "; AY CHC certificate replay obligation: {name}");
    let _ = writeln!(out, "; kind: safety");
    let _ = writeln!(out, "; class: acyclic-exhaustion");
    let _ = writeln!(out, "; clause: {clause_index}");
    let _ = writeln!(out, "; expected-result: unsat");
    let _ = writeln!(
        out,
        "; normalized-input-sha256: {}",
        super::normalized_chc_input_sha256(problem)
    );
    let _ = writeln!(out, "(set-logic ALL)");
    out.push('\n');
    let declarations = collect_uninterpreted_function_declarations(formula)?;
    for declaration in &declarations {
        out.push_str(&emit_declare_uninterpreted_function(declaration));
    }
    for (var_name, sort) in vars {
        let _ = writeln!(out, "(declare-const {} {})", quote_symbol(&var_name), sort);
    }
    let _ = writeln!(
        out,
        "(assert {})",
        crate::InvariantModel::expr_to_smtlib(formula)
    );
    let _ = writeln!(out, "(check-sat)");
    let _ = writeln!(out, "(exit)");
    Ok(out)
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "replay_check_tests.rs"]
mod tests;
