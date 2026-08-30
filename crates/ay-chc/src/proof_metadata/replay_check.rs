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
//! obligation query on a FRESH `ay-dpll` executor — independent of the solving
//! run — and, only when every obligation passes, assembles the checked replay
//! artifacts, validates them against an evidence manifest, and upgrades the
//! proof transcript metadata to `replayable` with concrete
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

use super::{
    ChcCheckedReplayArtifacts, ChcCheckedReplayObligation, ChcCheckedReplaySummary,
    ChcObligationStrictCert, ChcPdrProofRun, ChcProofArtifactDigest, ChcProofEvidenceManifest,
    ChcProofEvidenceOptions, ChcProofSolverIdentity, ChcProofTranscriptMetadata,
    ChcReplayCheckResult, ChcReplayCheckerIdentity, ChcReplayEvidence, ChcReplayObligationArtifact,
    CHC_IN_PROCESS_REPLAY_CHECKER_NAME,
};
use crate::classifier::ProblemClassifier;
use crate::pdr::{ChcReplayObligation, ChcReplayObligationKind};
use crate::{
    ChcError, ChcExpr, ChcProblem, ChcResult, ChcSort, ChcVar, ClauseHead, PredicateId,
    VerifiedChcResult,
};
use ay_core::quote_symbol;
use ay_core::time::Instant;
use std::collections::BTreeMap;
use std::time::Duration;

mod checked_run;
mod strict_bundle;

/// Cap on clause instantiations while expanding an acyclic clause system into
/// one quantifier-free error-reachability query. Prevents pathological DAG
/// sharing from blowing up the synthesized obligation; exceeding the cap fails
/// closed to metadata-only.
const ACYCLIC_EXPANSION_MAX_INSTANTIATIONS: usize = 10_000;

/// Cap on predicate nesting depth during acyclic expansion (belt-and-braces
/// alongside the classifier's cycle check and the explicit occurs check).
const ACYCLIC_EXPANSION_MAX_DEPTH: usize = 128;

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
/// trace-validity obligation conjoins the unrolled system with the concrete
/// counterexample assignments and must be `sat`.
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
    /// re-executes each on a fresh SMT executor within `budget`, and — only if
    /// every obligation returns its expected verdict — returns a
    /// [`ChcCheckedReplayRun`] whose transcript metadata is `replayable` and
    /// Trust-full-verifier admissible.
    ///
    /// Fail-closed: `Unknown` results, budget exhaustion, any obligation
    /// failure, and any digest-binding mismatch return `Err`, and callers must
    /// keep using the original metadata-only run.
    pub fn run_checked_replay(&self, budget: Duration) -> ChcResult<ChcCheckedReplayRun> {
        let engine = self.metadata.engine.clone();
        let mut options = ChcProofEvidenceOptions::pdr_strict(&crate::PdrConfig::default());
        options.proof_mode = format!("checked-replay:{engine}");
        let solver = ChcProofSolverIdentity::new(engine);
        let obligation_id = format!(
            "ay-chc:checked-replay:{}",
            self.metadata.normalized_input_sha256
        );
        self.run_checked_replay_with_binding(options, solver, obligation_id, None, budget)
    }

    /// Run the checked replay pass against caller-supplied manifest binding
    /// parts (options/solver/obligation id) and optional pre-built replay
    /// evidence (e.g. the CLI's evidence carrying a trace-file transcript and
    /// on-disk obligation artifact paths).
    ///
    /// When `base_evidence` already carries replay obligation artifacts, their
    /// digest set must exactly match the obligations this pass renders and
    /// executes — otherwise the pass fails closed.
    pub fn run_checked_replay_with_binding(
        &self,
        options: ChcProofEvidenceOptions,
        solver: ChcProofSolverIdentity,
        obligation_id: impl Into<String>,
        base_evidence: Option<ChcReplayEvidence>,
        budget: Duration,
    ) -> ChcResult<ChcCheckedReplayRun> {
        let problem = self.problem();
        let obligation_id = obligation_id.into();
        if budget.is_zero() {
            return Err(verification_error(
                "checked replay budget is zero; staying metadata-only",
            ));
        }
        let start = Instant::now();

        // 1. Render the obligations for this sealed result.
        let (certificate, obligations) = match &self.result {
            VerifiedChcResult::Safe(inv) => {
                let certificate = inv.model().to_certificate(problem);
                let mut obligations =
                    crate::engines::chc_safe_replay_obligations(problem, inv.model())?;
                if obligations.is_empty() {
                    // Empty-model acyclic-exhaustion certificate: the sound
                    // replay set is the depth-exhaustion UNSAT check itself,
                    // synthesized as one Safety obligation per query clause.
                    obligations = acyclic_exhaustion_replay_obligations(problem)?;
                }
                (certificate, obligations)
            }
            VerifiedChcResult::Unsafe(cex) => {
                let certificate = cex.counterexample().to_certificate(problem);
                let obligations = cex
                    .counterexample()
                    .trace_validity_replay_obligations(problem)?;
                (certificate, obligations)
            }
            _ => {
                return Err(verification_error(
                    "checked replay requires a verified Safe/Unsafe proof result",
                ));
            }
        };
        if obligations.is_empty() {
            return Err(verification_error(
                "checked replay found no obligations to execute",
            ));
        }

        // 2. Execute every obligation on a fresh executor, budget-capped.
        let mut checked_rows = Vec::with_capacity(obligations.len());
        let mut replay_records = Vec::with_capacity(obligations.len());
        for obligation in &obligations {
            let Some(remaining) = budget.checked_sub(start.elapsed()) else {
                return Err(verification_error(format!(
                    "checked replay budget exhausted before obligation {}",
                    obligation.name
                )));
            };
            if remaining.is_zero() {
                return Err(verification_error(format!(
                    "checked replay budget exhausted before obligation {}",
                    obligation.name
                )));
            }
            let expected = expected_verdict(obligation.kind);

            let checker_command;
            let strict_cert = if expected == "unsat" {
                let (cert, command) = strict_bundle::discharge(obligation, remaining, expected)?;
                checker_command = command;
                Some(cert)
            } else {
                // SAT trace-validity obligations have no UNSAT proof. The
                // executor checks their concrete witness by verdict.
                let verdict = crate::smt::executor_adapter::smtlib_first_verdict_via_executor(
                    &obligation.smtlib,
                    Some(remaining),
                );
                if verdict.as_deref() != Some(expected) {
                    return Err(verification_error(format!(
                        "checked replay obligation {} expected {expected}, got {}",
                        obligation.name,
                        verdict.as_deref().unwrap_or("<execution-error>")
                    )));
                }
                checker_command = format!(
                    "{CHC_IN_PROCESS_REPLAY_CHECKER_NAME} --expect {expected} {}",
                    obligation.name
                );
                None
            };
            let query = ChcProofArtifactDigest::from_bytes(
                "replay-obligation",
                obligation.smtlib.as_bytes(),
            );
            replay_records.push(serde_json::json!({
                "name": obligation.name,
                "kind": obligation.kind.as_str(),
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
            checked_rows.push(row);
        }

        // 3. Assemble the checked replay artifacts.
        let normalized = super::normalized_chc_input(problem);
        let problem_bytes = normalized.into_bytes();
        let problem_digest = ChcProofArtifactDigest::from_bytes("problem", &problem_bytes);
        let certificate_bytes = certificate.into_bytes();

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
                evidence = evidence.with_replay_obligation(ChcReplayObligationArtifact::new(
                    row.kind,
                    row.query.clone(),
                ));
            }
        } else {
            let mut evidence_set: Vec<_> = evidence
                .replay_obligations
                .iter()
                .map(|artifact| {
                    (
                        artifact.kind.as_str().to_string(),
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

        // Certificate artifact: reuse the evidence binding when present (the
        // CLI wrote the identical certificate text to disk), else attach ours.
        let certificate_digest = match evidence.proof.clone() {
            Some(existing) => {
                let ours =
                    ChcProofArtifactDigest::from_bytes("proof-certificate", &certificate_bytes);
                if existing.sha256 != ours.sha256 || existing.bytes != ours.bytes {
                    return Err(verification_error(
                        "checked replay certificate does not match the supplied proof artifact digest",
                    ));
                }
                existing
            }
            None => {
                let digest =
                    ChcProofArtifactDigest::from_bytes("proof-certificate", &certificate_bytes);
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
                    "schema": "ay.chc-checked-replay-run-log/v1",
                    "schema_version": 1,
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
                            "query_sha256": row.query.sha256,
                        }))
                        .collect::<Vec<_>>(),
                });
                let bytes = serde_json::to_vec(&run_log_value).map_err(|error| {
                    verification_error(format!("checked replay run log serialization: {error}"))
                })?;
                let digest = ChcProofArtifactDigest::from_bytes("solver-transcript", &bytes);
                evidence = evidence.with_solver_transcript(digest.clone());
                (digest, Some(bytes))
            }
        };

        // Replay log (the pass record) is always produced by this pass and
        // replaces any placeholder replay report on the supplied evidence.
        let replay_log_value = serde_json::json!({
            "schema": "ay.chc-checked-replay-log/v1",
            "schema_version": 1,
            "status": "pass",
            "checker": checker.to_json_value(),
            "command": command,
            "problem_sha256": problem_digest.sha256,
            "obligations": replay_records,
        });
        let replay_log_bytes = serde_json::to_vec(&replay_log_value).map_err(|error| {
            verification_error(format!("checked replay log serialization: {error}"))
        })?;
        let replay_log_digest =
            ChcProofArtifactDigest::from_bytes("replay-report", &replay_log_bytes);
        evidence.replay_report = Some(replay_log_digest.clone());

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
        let checked_report_bytes =
            serde_json::to_vec(&summary.to_json_value()).map_err(|error| {
                verification_error(format!("checked replay report serialization: {error}"))
            })?;
        let checked_report_sha256 = super::sha256_hex(&checked_report_bytes);
        let manifest = manifest
            .try_with_checked_replay_summary(summary.clone())
            .map_err(|error| verification_error(error.to_string()))?;

        // 5. Upgrade the transcript metadata (fail-closed constructor).
        let metadata = ChcProofTranscriptMetadata::for_checked_run(
            &self.metadata,
            &manifest,
            &checked_report_sha256,
        )
        .ok_or_else(|| {
            verification_error("checked replay metadata upgrade rejected; staying metadata-only")
        })?;

        Ok(ChcCheckedReplayRun {
            proof_run: self.with_metadata(metadata),
            manifest,
            summary,
            problem_bytes,
            certificate_bytes,
            run_log_bytes,
            replay_log_bytes,
            checked_report_bytes,
        })
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
    let mut expansion_problem = problem.clone();
    expansion_problem.strip_dead_end_cycle_predicates();
    let features = ProblemClassifier::classify(&expansion_problem);
    if features.has_cycles {
        return Err(verification_error(
            "acyclic-exhaustion replay export requires an acyclic clause system",
        ));
    }

    let mut obligations = Vec::new();
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
        let formula = ChcExpr::and_all(conjuncts);
        let name = format!("clause-{clause_index}-safety-acyclic-exhaustion");
        let smtlib = render_acyclic_exhaustion_obligation(problem, &name, clause_index, &formula);
        obligations.push(ChcReplayObligation {
            name,
            kind: ChcReplayObligationKind::Safety,
            clause_index,
            smtlib,
        });
    }
    if obligations.is_empty() {
        return Err(verification_error(
            "acyclic-exhaustion replay export found no query clause",
        ));
    }
    Ok(obligations)
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
) -> String {
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
    out
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "replay_check_tests.rs"]
mod tests;
