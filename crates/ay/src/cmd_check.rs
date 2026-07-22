// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay check` subcommand — proof verification.
//!
//! Verifies DRAT and LRAT proofs against DIMACS CNF formulas.
//! Replaces the standalone ay-drat-check and ay-lrat-check binaries.

use std::fs::File;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use anyhow::Context;
use ay_chc::quotient_certificate::check_recursive_lia_quotient_certificate;
use ay_chc::ChcParser;
use ay_sat::dimacs_core::{parse_dimacs_events, DimacsCoreError, DimacsEvent, DimacsRecordRef};
use ay_sat::fmla_runtime_ledger::{
    replay_fmla_postcheck_admission,
    validate_fmla_learned_lrat_main_proof_authority_from_json_postcheck_replay,
    ExternalProofCheckerVerdictArtifactRef, FmlaLearnedLratMainProofAuthorityReplayRecord,
    FmlaPostCheckAdmissionReplayInput, FmlaPostCheckAdmissionReplayRecord,
    FmlaPostCheckAdmissionReplayReject, FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA,
    FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT,
    FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA,
    FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA,
};
use clap::Subcommand;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use crate::stats_output;

const AY_CHECK_EVIDENCE_SCHEMA: &str = "ay.satcomp-proof-check-evidence/v1";
// This persisted replay-report schema predates the public API. Its exact wire
// value is frozen for backward compatibility and is asserted by CLI tests; do
// not rename the string while neutralizing development-only identifiers.
const RESTRICTED_RULE_SUBSET_ARTIFACT_REPLAY_SCHEMA: &str = "lean5-artifact-replay-report-v1";
const CHC_QUOTIENT_CHECK_REPORT_SCHEMA: &str = "ay.chc.quotient-certificate-check/v1";

// clap subcommand enum: constructed once at CLI parse; boxing arg fields would
// break the derive and buys nothing at this scale.
#[allow(clippy::large_enum_variant)]
#[derive(Subcommand)]
pub(crate) enum CheckCommand {
    #[cfg(ay_internal_tools)]
    /// Run the fail-closed recursive-LIA CHC quotient certificate checker.
    ///
    /// Emits exactly one JSON report to stdout. A structurally valid certificate
    /// exits 2, not 0, until trusted quotient replay and lift checking exist.
    ChcQuotient {
        /// CHC problem in SMT-LIB/HORN syntax.
        #[arg(long, value_name = "PATH")]
        problem: PathBuf,
        /// Quotient certificate JSON path.
        #[arg(long, value_name = "PATH")]
        certificate: PathBuf,
        /// Report schema to emit.
        #[arg(
            long,
            value_name = "SCHEMA",
            default_value = "ay.chc.quotient-certificate-check/v1"
        )]
        emit: String,
        /// Emit the quotient checker JSON report.
        #[arg(long, action = clap::ArgAction::SetTrue, required = true)]
        json: bool,
    },

    /// Verify a DRAT/DRUP proof against a DIMACS CNF formula.
    ///
    /// Reads a DIMACS CNF file and a DRAT proof file. Outputs "s VERIFIED"
    /// (exit 0) if valid, "s NOT VERIFIED" (exit 1) if invalid.
    /// RAT checking is enabled by default (full DRAT). Use --rup-only for DRUP.
    Drat {
        /// DIMACS CNF formula file
        formula: PathBuf,
        /// DRAT proof file
        proof: PathBuf,
        /// Restrict to RUP checking only (DRUP mode)
        #[arg(long)]
        rup_only: bool,
        /// Use backward checking (verify only needed clauses)
        #[arg(long)]
        backward: bool,
        /// Print verification statistics
        #[arg(long)]
        stats: bool,
        /// Write a SAT-COMP proof-check evidence JSON sidecar.
        #[arg(long, value_name = "PATH")]
        evidence_json: Option<PathBuf>,
        /// Project name to include in the evidence JSON sidecar.
        #[arg(long, value_name = "PROJECT")]
        evidence_project: Option<String>,
        /// Obligation fingerprint to link in the evidence JSON sidecar.
        #[arg(long, value_name = "FINGERPRINT")]
        evidence_linked_obligation: Vec<String>,
        /// Artifact path to report in evidence JSON instead of the proof path.
        #[arg(long, value_name = "PATH")]
        evidence_artifact_path: Option<PathBuf>,
        /// Write a proof-artifact-v1 replay envelope after successful replay.
        #[arg(long, value_name = "PATH")]
        proof_artifact_json: Option<PathBuf>,
    },

    /// Verify an LRAT proof against a DIMACS CNF formula.
    ///
    /// Reads a DIMACS CNF file and an LRAT proof file (text or binary,
    /// auto-detected). Outputs "s VERIFIED" (exit 0) if valid,
    /// "s NOT VERIFIED" (exit 1) if invalid.
    Lrat {
        /// DIMACS CNF formula file
        formula: PathBuf,
        /// LRAT proof file
        proof: PathBuf,
        /// Write a SAT-COMP proof-check evidence JSON sidecar.
        #[arg(long, value_name = "PATH")]
        evidence_json: Option<PathBuf>,
        /// Project name to include in the evidence JSON sidecar.
        #[arg(long, value_name = "PROJECT")]
        evidence_project: Option<String>,
        /// Obligation fingerprint to link in the evidence JSON sidecar.
        #[arg(long, value_name = "FINGERPRINT")]
        evidence_linked_obligation: Vec<String>,
        /// Artifact path to report in evidence JSON instead of the proof path.
        #[arg(long, value_name = "PATH")]
        evidence_artifact_path: Option<PathBuf>,
        /// Write a proof-artifact-v1 replay envelope after successful replay.
        #[arg(long, value_name = "PATH")]
        proof_artifact_json: Option<PathBuf>,
    },

    /// Verify a PR/DPR (LPR) proof against a DIMACS CNF formula using the
    /// EXTERNAL VERIFIED `cake_lpr` checker (the trust anchor).
    ///
    /// The built-in DRAT/RAT checker (`ay check drat`) deliberately FAILS CLOSED
    /// on PR steps — propagation-redundant clauses (the lex-leader symmetry SBP)
    /// are outside the RUP/RAT trusted fragment. PR additions are instead
    /// certified by `cake_lpr`, the HOL4/CakeML formally verified LPR checker
    /// (vendored under `third_party/cake_lpr/`). A buggy AY PR emitter is *caught*
    /// (cake_lpr rejects), never silently trusted.
    ///
    /// The proof file is in `cake_lpr`'s native LPR format (the hinted form of a
    /// PR/DPR proof; a raw unhinted DPR proof is converted to LPR by `dpr-trim`
    /// before this step). Outputs "s VERIFIED" (exit 0) when cake_lpr prints
    /// `s VERIFIED UNSAT`, "s NOT VERIFIED" (exit 1) otherwise.
    Dpr {
        /// DIMACS CNF formula file.
        formula: PathBuf,
        /// LPR proof file (cake_lpr native format).
        proof: PathBuf,
        /// Path to the verified `cake_lpr` binary. Defaults to the `CAKE_LPR`
        /// environment variable, then the vendored `third_party/cake_lpr/cake_lpr`.
        #[arg(long, value_name = "PATH")]
        checker: Option<PathBuf>,
    },

    /// Verify a PR/SR (DPR/DSR) proof against a DIMACS CNF formula using the
    /// NATIVE Rust PR/SR checker (no external binary on the trust path).
    ///
    /// Handles both the partial-assignment witness (PR/DPR, the `j=0` lex-leader
    /// SBP / LPR fragment) and the full substitution witness (SR/DSR symmetry
    /// proofs AY emits via `DratWriter::add_sr`). The single trusted kernel
    /// `ay_drat_check::SrChecker` re-derives every redundancy by reverse unit
    /// propagation, so a corrupted witness is caught (it cannot yield a false
    /// VERIFIED). Outputs "s VERIFIED" (exit 0) or "s NOT VERIFIED" (exit 1).
    Sr {
        /// DIMACS CNF formula file.
        formula: PathBuf,
        /// PR/SR proof file (DPR/DSR `a`-line clause+witness format, text or binary).
        proof: PathBuf,
        /// Print verification statistics.
        #[arg(long)]
        stats: bool,
    },

    /// Verify SAT-COMP SAT model lines against a DIMACS CNF formula.
    ///
    /// The formula is streamed, so this handles huge CNF rows without
    /// materializing all clauses in memory. The model stdout file is expected
    /// to contain SAT-COMP `v ... 0` model lines.
    Model {
        /// DIMACS CNF formula file, optionally .xz compressed.
        formula: PathBuf,
        /// Solver stdout containing SAT-COMP model lines.
        stdout: PathBuf,
        /// Emit a JSON report instead of a plain model_status line.
        #[arg(long)]
        json: bool,
    },

    #[cfg(ay_internal_tools)]
    /// Replay Fmla Main/LRAT admission after same-run external proof checking.
    ///
    /// This is evidence-only: it writes a checker-backed admission artifact when
    /// all preconditions hold, but never changes the solver answer.
    FmlaPostcheckAdmission {
        /// DIMACS input checked with proof.out.
        #[arg(long, value_name = "PATH")]
        dimacs: PathBuf,
        /// Solver/wrapper proof.out checked by the external proof checker.
        #[arg(long, value_name = "PATH")]
        proof_out: PathBuf,
        /// Retained external checker verdict artifact from this proof directory.
        #[arg(long, value_name = "PATH")]
        external_checker_artifact: PathBuf,
        /// SHA256 for the retained external checker verdict artifact.
        #[arg(long, value_name = "HEX")]
        external_checker_artifact_sha256: String,
        /// Solver-exported learned-LRAT dry-run proof artifact JSON.
        #[arg(long, value_name = "PATH")]
        learned_lrat_dry_run_artifact: Option<PathBuf>,
        /// ay internal LRAT checker status for proof.out.
        #[arg(long, value_name = "STATUS")]
        ay_lrat_status: String,
        /// External proof checker status for proof.out.
        #[arg(long, value_name = "STATUS")]
        proof_checker_status: String,
        /// Path where the committed replay artifact should be written.
        #[arg(long, value_name = "PATH")]
        replay_artifact: PathBuf,
        /// Optional shell TSV summary path for matrix ingestion.
        #[arg(long, value_name = "PATH")]
        summary_tsv: Option<PathBuf>,
        /// Solver-side materializer attempts counter.
        #[arg(long, value_name = "N")]
        materializer_attempts: String,
        /// Solver-side materializer proof rows seen counter.
        #[arg(long, value_name = "N")]
        materializer_proof_emit_records_seen: String,
        /// Solver-side materializer rows counter.
        #[arg(long, value_name = "N")]
        materializer_records: String,
        /// Solver-side materializer fail-closed counter.
        #[arg(long, value_name = "N")]
        materializer_fail_closed: String,
        /// Solver-side materializer missing-runtime-record counter.
        #[arg(long, value_name = "N")]
        materializer_missing_runtime_records: String,
        /// Solver-side preprocessing transaction fail-closed counter.
        #[arg(long, value_name = "N")]
        preprocess_tx_fail_closed: String,
        /// Solver-side preprocessing transaction committed counter.
        #[arg(long, value_name = "N")]
        preprocess_tx_committed: String,
        /// Emit the replay report JSON to stdout.
        #[arg(long, action = clap::ArgAction::SetTrue, required = true)]
        json: bool,
    },
}

#[derive(Clone, Debug, Default)]
struct EvidenceConfig {
    json_path: Option<PathBuf>,
    project: Option<String>,
    linked_obligations: Vec<String>,
    artifact_path: Option<PathBuf>,
    proof_artifact_json: Option<PathBuf>,
}

#[derive(Clone, Debug)]
struct ModelCheckReport {
    model_status: String,
    num_vars: Option<usize>,
    clauses_checked: u64,
    first_unsatisfied_clause: Option<u64>,
    elapsed_ms: u128,
}

impl ModelCheckReport {
    fn valid(&self) -> bool {
        self.model_status == "valid"
    }
}

#[derive(Clone, Debug)]
struct FmlaPostcheckAdmissionCliInput {
    dimacs: PathBuf,
    proof_out: PathBuf,
    external_checker_artifact: PathBuf,
    external_checker_artifact_sha256: String,
    learned_lrat_dry_run_artifact: Option<PathBuf>,
    ay_lrat_status: String,
    proof_checker_status: String,
    replay_artifact: PathBuf,
    summary_tsv: Option<PathBuf>,
    materializer_attempts: String,
    materializer_proof_emit_records_seen: String,
    materializer_records: String,
    materializer_fail_closed: String,
    materializer_missing_runtime_records: String,
    preprocess_tx_fail_closed: String,
    preprocess_tx_committed: String,
    emit_json: bool,
}

#[derive(Clone, Debug)]
struct FmlaPostcheckAdmissionOutcome {
    status: &'static str,
    reason: Option<String>,
    replay: Option<FmlaPostCheckAdmissionReplayRecord>,
    learned_lrat_authority: Option<FmlaLearnedLratMainProofAuthorityReplayRecord>,
}

/// Entry point for `ay check` subcommands.
pub(crate) fn run(command: CheckCommand) -> anyhow::Result<()> {
    match command {
        #[cfg(ay_internal_tools)]
        CheckCommand::ChcQuotient {
            problem,
            certificate,
            emit,
            json: _,
        } => run_chc_quotient_check(&problem, &certificate, &emit),
        CheckCommand::Drat {
            formula,
            proof,
            rup_only,
            backward,
            stats,
            evidence_json,
            evidence_project,
            evidence_linked_obligation,
            evidence_artifact_path,
            proof_artifact_json,
        } => run_drat_check(
            &formula,
            &proof,
            !rup_only,
            backward,
            stats,
            EvidenceConfig {
                json_path: evidence_json,
                project: evidence_project,
                linked_obligations: evidence_linked_obligation,
                artifact_path: evidence_artifact_path,
                proof_artifact_json,
            },
        ),
        CheckCommand::Lrat {
            formula,
            proof,
            evidence_json,
            evidence_project,
            evidence_linked_obligation,
            evidence_artifact_path,
            proof_artifact_json,
        } => run_lrat_check(
            &formula,
            &proof,
            EvidenceConfig {
                json_path: evidence_json,
                project: evidence_project,
                linked_obligations: evidence_linked_obligation,
                artifact_path: evidence_artifact_path,
                proof_artifact_json,
            },
        ),
        CheckCommand::Dpr {
            formula,
            proof,
            checker,
        } => run_dpr_check(&formula, &proof, checker.as_deref()),
        CheckCommand::Sr {
            formula,
            proof,
            stats,
        } => run_sr_check(&formula, &proof, stats),
        CheckCommand::Model {
            formula,
            stdout,
            json,
        } => run_model_check(&formula, &stdout, json),
        #[cfg(ay_internal_tools)]
        CheckCommand::FmlaPostcheckAdmission {
            dimacs,
            proof_out,
            external_checker_artifact,
            external_checker_artifact_sha256,
            learned_lrat_dry_run_artifact,
            ay_lrat_status,
            proof_checker_status,
            replay_artifact,
            summary_tsv,
            materializer_attempts,
            materializer_proof_emit_records_seen,
            materializer_records,
            materializer_fail_closed,
            materializer_missing_runtime_records,
            preprocess_tx_fail_closed,
            preprocess_tx_committed,
            json,
        } => run_fmla_postcheck_admission(FmlaPostcheckAdmissionCliInput {
            dimacs,
            proof_out,
            external_checker_artifact,
            external_checker_artifact_sha256,
            learned_lrat_dry_run_artifact,
            ay_lrat_status,
            proof_checker_status,
            replay_artifact,
            summary_tsv,
            materializer_attempts,
            materializer_proof_emit_records_seen,
            materializer_records,
            materializer_fail_closed,
            materializer_missing_runtime_records,
            preprocess_tx_fail_closed,
            preprocess_tx_committed,
            emit_json: json,
        }),
    }
}

fn run_model_check(formula: &Path, stdout: &Path, emit_json: bool) -> anyhow::Result<()> {
    let report = check_dimacs_model(formula, stdout);
    if emit_json {
        let valid = report.valid();
        let value = json!({
            "schema": "ay.satcomp-model-check/v1",
            "formula": formula.display().to_string(),
            "stdout": stdout.display().to_string(),
            "model_status": &report.model_status,
            "valid": valid,
            "num_vars": report.num_vars,
            "clauses_checked": report.clauses_checked,
            "first_unsatisfied_clause": report.first_unsatisfied_clause,
            "elapsed_ms": report.elapsed_ms,
            "ay_build": stats_output::BUILD_PROVENANCE.json_value(),
        });
        println!("{}", serde_json::to_string(&value)?);
    } else {
        println!("{}", report.model_status);
    }
    std::process::exit(if report.valid() { 0 } else { 1 });
}

fn run_fmla_postcheck_admission(input: FmlaPostcheckAdmissionCliInput) -> anyhow::Result<()> {
    let outcome = evaluate_fmla_postcheck_admission(&input);
    let replay_payload = outcome.replay.as_ref().map(|replay| {
        fmla_postcheck_admission_replay_payload(replay, outcome.learned_lrat_authority.as_ref())
    });
    if let Some(payload) = replay_payload.as_ref() {
        write_evidence_json(&input.replay_artifact, payload)?;
    } else {
        let _ = std::fs::remove_file(&input.replay_artifact);
    }

    let replay_artifact_sha256 = if replay_payload.is_some() {
        sha256_file_hex(&input.replay_artifact)?
    } else {
        String::new()
    };
    let report = fmla_postcheck_admission_report_value(
        &input,
        &outcome,
        replay_payload.as_ref(),
        &replay_artifact_sha256,
    );
    if let Some(summary_tsv) = input.summary_tsv.as_deref() {
        write_fmla_postcheck_summary_tsv(
            summary_tsv,
            &input.replay_artifact,
            &outcome,
            &replay_artifact_sha256,
        )?;
    }
    if input.emit_json {
        let mut out =
            serde_json::to_vec_pretty(&report).context("cannot serialize Fmla replay report")?;
        out.push(b'\n');
        std::io::stdout()
            .write_all(&out)
            .context("cannot write Fmla replay report to stdout")?;
    }
    Ok(())
}

fn evaluate_fmla_postcheck_admission(
    input: &FmlaPostcheckAdmissionCliInput,
) -> FmlaPostcheckAdmissionOutcome {
    if input.ay_lrat_status != "ok" {
        return fmla_no_replay("ay_lrat_status_not_ok");
    }
    if input.proof_checker_status != "ok" {
        return fmla_no_replay("proof_checker_status_not_ok");
    }
    let Some(materializer_attempts) = parse_nonnegative_counter(&input.materializer_attempts)
    else {
        return fmla_no_replay("materializer_attempts_missing");
    };
    let Some(materializer_proof_emit_records_seen) =
        parse_nonnegative_counter(&input.materializer_proof_emit_records_seen)
    else {
        return fmla_no_replay("materializer_proof_emit_records_seen_missing");
    };
    let Some(materializer_records) = parse_nonnegative_counter(&input.materializer_records) else {
        return fmla_no_replay("materializer_records_missing");
    };
    let Some(materializer_fail_closed) = parse_nonnegative_counter(&input.materializer_fail_closed)
    else {
        return fmla_no_replay("materializer_fail_closed_missing");
    };
    let Some(materializer_missing_runtime_records) =
        parse_nonnegative_counter(&input.materializer_missing_runtime_records)
    else {
        return fmla_no_replay("materializer_missing_runtime_records_missing");
    };
    let Some(preprocess_tx_fail_closed) =
        parse_nonnegative_counter(&input.preprocess_tx_fail_closed)
    else {
        return fmla_no_replay("preprocess_tx_fail_closed_missing");
    };
    let Some(preprocess_tx_committed) = parse_nonnegative_counter(&input.preprocess_tx_committed)
    else {
        return fmla_no_replay("preprocess_tx_committed_missing");
    };

    let artifact = match read_fmla_external_checker_artifact(
        &input.external_checker_artifact,
        &input.external_checker_artifact_sha256,
        &input.proof_out,
        &input.dimacs,
    ) {
        Ok(artifact) => artifact,
        Err(reason) => return fmla_rejected(reason),
    };
    let replay_input = FmlaPostCheckAdmissionReplayInput {
        materializer_attempts,
        materializer_proof_emit_records_seen,
        materializer_records,
        materializer_fail_closed,
        materializer_missing_runtime_records,
        preprocess_tx_fail_closed,
        preprocess_tx_committed,
    };
    match replay_fmla_postcheck_admission(replay_input, Some(artifact)) {
        Ok(replay) => {
            let learned_lrat_authority = match input.learned_lrat_dry_run_artifact.as_deref() {
                Some(path) => match validate_fmla_learned_lrat_dry_run_authority(
                    path,
                    &input.proof_out,
                    &replay,
                ) {
                    Ok(authority) if authority.authorizes_main_proof_out => Some(authority),
                    Ok(authority) => {
                        let reason = authority.reason.clone().unwrap_or_else(|| {
                            "learned_lrat_main_proof_authority_fail_closed".to_string()
                        });
                        return FmlaPostcheckAdmissionOutcome {
                            status: "no_replay",
                            reason: Some(reason),
                            replay: None,
                            learned_lrat_authority: Some(authority),
                        };
                    }
                    Err(reason) => return fmla_no_replay(reason),
                },
                None => None,
            };
            FmlaPostcheckAdmissionOutcome {
                status: "committed_checker_backed_admission",
                reason: None,
                replay: Some(replay),
                learned_lrat_authority,
            }
        }
        Err(reject) => {
            let reason = fmla_replay_reject_reason(&reject).to_string();
            match reject {
                FmlaPostCheckAdmissionReplayReject::MissingExternalCheckerVerdict
                | FmlaPostCheckAdmissionReplayReject::ExternalCheckerVerdictNotAccepted {
                    ..
                } => fmla_rejected(reason),
                _ => fmla_no_replay(reason),
            }
        }
    }
}

fn validate_fmla_learned_lrat_dry_run_authority(
    dry_run_artifact: &Path,
    proof_out: &Path,
    replay: &FmlaPostCheckAdmissionReplayRecord,
) -> Result<FmlaLearnedLratMainProofAuthorityReplayRecord, String> {
    if !dry_run_artifact.is_file() {
        return Err("learned_lrat_dry_run_artifact_missing".to_string());
    }
    let payload_text = std::fs::read_to_string(dry_run_artifact)
        .map_err(|_| "learned_lrat_dry_run_artifact_unreadable".to_string())?;
    let payload: Value = serde_json::from_str(&payload_text)
        .map_err(|_| "learned_lrat_dry_run_artifact_json_invalid".to_string())?;
    let proof_out_path =
        canonical_string(proof_out).map_err(|_| "proof_out_missing".to_string())?;
    let proof_out_bytes =
        std::fs::read(proof_out).map_err(|_| "proof_out_unreadable".to_string())?;
    Ok(
        validate_fmla_learned_lrat_main_proof_authority_from_json_postcheck_replay(
            &payload,
            replay,
            &proof_out_path,
            &proof_out_bytes,
        ),
    )
}

fn fmla_no_replay(reason: impl Into<String>) -> FmlaPostcheckAdmissionOutcome {
    FmlaPostcheckAdmissionOutcome {
        status: "no_replay",
        reason: Some(reason.into()),
        replay: None,
        learned_lrat_authority: None,
    }
}

fn fmla_rejected(reason: impl Into<String>) -> FmlaPostcheckAdmissionOutcome {
    FmlaPostcheckAdmissionOutcome {
        status: "rejected",
        reason: Some(reason.into()),
        replay: None,
        learned_lrat_authority: None,
    }
}

fn parse_nonnegative_counter(value: &str) -> Option<u64> {
    value.trim().parse::<u64>().ok()
}

fn read_fmla_external_checker_artifact(
    artifact_path: &Path,
    expected_artifact_sha256: &str,
    proof_out: &Path,
    dimacs: &Path,
) -> Result<ExternalProofCheckerVerdictArtifactRef, String> {
    let requirement = FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT;
    if artifact_path.file_name().and_then(|name| name.to_str())
        != Some(requirement.artifact_file_name)
    {
        return Err("external_checker_verdict_artifact_path_mismatch".to_string());
    }
    if proof_out.file_name().and_then(|name| name.to_str()) != Some(requirement.proof_out_file_name)
    {
        return Err("proof_out_path_not_wrapper_proof_out".to_string());
    }
    let artifact_dir = canonical_parent(artifact_path)
        .map_err(|_| "external_checker_verdict_artifact_parent_missing".to_string())?;
    let proof_dir =
        canonical_parent(proof_out).map_err(|_| "proof_out_parent_missing".to_string())?;
    if artifact_dir != proof_dir {
        return Err("external_checker_verdict_artifact_not_in_proof_dir".to_string());
    }
    if !artifact_path.is_file() {
        return Err("external_checker_verdict_artifact_missing".to_string());
    }
    if !proof_out.is_file() {
        return Err("proof_out_missing".to_string());
    }
    if !dimacs.is_file() {
        return Err("checked_dimacs_missing".to_string());
    }
    let actual_artifact_sha256 = sha256_file_hex(artifact_path)
        .map_err(|_| "external_checker_verdict_artifact_unreadable")?;
    if actual_artifact_sha256 != expected_artifact_sha256 {
        return Err("external_checker_verdict_artifact_sha256_mismatch".to_string());
    }

    let artifact_text = std::fs::read_to_string(artifact_path)
        .map_err(|_| "external_checker_verdict_artifact_unreadable".to_string())?;
    let payload: Value = serde_json::from_str(&artifact_text)
        .map_err(|_| "external_checker_verdict_artifact_json_invalid".to_string())?;
    let artifact_resolved = canonical_string(artifact_path)
        .map_err(|_| "external_checker_verdict_artifact_missing".to_string())?;
    let proof_resolved =
        canonical_string(proof_out).map_err(|_| "proof_out_missing".to_string())?;
    let dimacs_resolved =
        canonical_string(dimacs).map_err(|_| "checked_dimacs_missing".to_string())?;
    let proof_out_sha256 =
        sha256_file_hex(proof_out).map_err(|_| "proof_out_unreadable".to_string())?;
    let dimacs_sha256 =
        sha256_file_hex(dimacs).map_err(|_| "checked_dimacs_unreadable".to_string())?;

    let schema = json_string(&payload, "schema")?;
    let runtime_field = json_string(&payload, "runtime_field")?;
    let verdict = json_string(&payload, "verdict")?;
    let payload_artifact_path = json_path_string(&payload, "artifact_path")?;
    let checker_path = json_string(&payload, "checker_path")?;
    let checker_sha256 = json_string(&payload, "checker_sha256")?;
    let checker_command = json_string(&payload, "checker_command")?;
    let checker_argv = json_string_array(&payload, "checker_argv")?;
    let checker_exit_code = json_i32(&payload, "checker_exit_code")?;
    let payload_proof_out_path = json_path_string(&payload, "proof_out_path")?;
    let payload_proof_out_sha256 = json_string(&payload, "proof_out_sha256")?;
    let payload_dimacs_path = json_path_string(&payload, "checked_dimacs_path")?;
    let payload_dimacs_sha256 = json_string(&payload, "checked_dimacs_sha256")?;

    if schema != FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA {
        return Err("external_checker_verdict_schema_mismatch".to_string());
    }
    if runtime_field != requirement.runtime_field {
        return Err("external_checker_verdict_runtime_field_mismatch".to_string());
    }
    if verdict != requirement.accepted_verdict {
        return Err("external_checker_verdict_not_verified_unsat".to_string());
    }
    if payload_artifact_path != artifact_resolved {
        return Err("external_checker_verdict_artifact_payload_path_mismatch".to_string());
    }
    if checker_exit_code != requirement.checker_exit_code {
        return Err("external_checker_verdict_nonzero_exit_code".to_string());
    }
    if payload_proof_out_path != proof_resolved {
        return Err("proof_out_payload_path_mismatch".to_string());
    }
    if payload_dimacs_path != dimacs_resolved {
        return Err("checked_dimacs_payload_path_mismatch".to_string());
    }
    if checker_argv
        != [
            checker_path.clone(),
            dimacs_resolved.clone(),
            proof_resolved.clone(),
        ]
    {
        return Err("checker_argv_mismatch".to_string());
    }
    if payload_proof_out_sha256 != proof_out_sha256 {
        return Err("proof_out_sha256_mismatch".to_string());
    }
    if payload_dimacs_sha256 != dimacs_sha256 {
        return Err("checked_dimacs_sha256_mismatch".to_string());
    }

    Ok(ExternalProofCheckerVerdictArtifactRef {
        schema,
        runtime_field,
        artifact_path: artifact_resolved,
        artifact_sha256: actual_artifact_sha256,
        checker_path,
        checker_sha256,
        checker_command,
        checker_argv,
        checker_exit_code,
        proof_out_path: proof_resolved,
        proof_out_sha256,
        checked_dimacs_path: dimacs_resolved,
        checked_dimacs_sha256: dimacs_sha256,
        verdict,
    })
}

fn fmla_postcheck_admission_replay_payload(
    replay: &FmlaPostCheckAdmissionReplayRecord,
    learned_lrat_authority: Option<&FmlaLearnedLratMainProofAuthorityReplayRecord>,
) -> Value {
    let mut payload = json!({
        "schema": replay.schema,
        "status": replay.status,
        "solver_answer_authority": false,
        "admission_phase": "post_solve_post_external_check",
        "proof_obligation_rows": replay.proof_obligation_rows,
        "external_proof_checker_verdict_artifact_rows": replay.external_checker_verdict_artifact_rows,
        "pre_replay_materializer_fail_closed": replay.pre_replay_materializer_fail_closed,
        "pre_replay_preprocess_tx_fail_closed": replay.pre_replay_preprocess_tx_fail_closed,
        "post_replay_preprocess_tx_committed": replay.post_replay_preprocess_tx_committed,
        "external_proof_checker_verdict_artifact": replay.external_checker_verdict_artifact.artifact_path,
        "external_proof_checker_verdict_artifact_sha256": replay.external_checker_verdict_artifact.artifact_sha256,
        "external_proof_checker_verdict_artifact_schema": replay.external_checker_verdict_artifact.schema,
        "external_proof_checker_verdict_artifact_runtime_field": replay.external_checker_verdict_artifact.runtime_field,
        "external_proof_checker_verdict": replay.external_checker_verdict_artifact.verdict,
        "external_proof_checker_path": replay.external_checker_verdict_artifact.checker_path,
        "external_proof_checker_sha256": replay.external_checker_verdict_artifact.checker_sha256,
        "external_proof_checker_command": replay.external_checker_verdict_artifact.checker_command,
        "external_proof_checker_argv": replay.external_checker_verdict_artifact.checker_argv,
        "external_proof_checker_proof_out_path": replay.external_checker_verdict_artifact.proof_out_path,
        "external_proof_checker_dimacs_path": replay.external_checker_verdict_artifact.checked_dimacs_path,
        "external_proof_checker_dimacs_sha256": replay.external_checker_verdict_artifact.checked_dimacs_sha256,
        "checker_exit_code": replay.external_checker_verdict_artifact.checker_exit_code,
    });
    add_learned_lrat_authority_report_fields(&mut payload, learned_lrat_authority);
    payload
}

fn fmla_postcheck_admission_report_value(
    input: &FmlaPostcheckAdmissionCliInput,
    outcome: &FmlaPostcheckAdmissionOutcome,
    replay_payload: Option<&Value>,
    replay_artifact_sha256: &str,
) -> Value {
    let mut report = replay_payload.cloned().unwrap_or_else(|| {
        json!({
            "schema": FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA,
            "status": outcome.status,
            "reason": outcome.reason,
            "solver_answer_authority": false,
            "admission_phase": "post_solve_post_external_check",
        })
    });
    report["replay_artifact"] = json!(input.replay_artifact.display().to_string());
    report["replay_artifact_sha256"] = json!(replay_artifact_sha256);
    report["ay_lrat_status"] = json!(input.ay_lrat_status);
    report["proof_checker_status"] = json!(input.proof_checker_status);
    if let Some(path) = input.learned_lrat_dry_run_artifact.as_ref() {
        report["learned_lrat_dry_run_artifact"] = json!(path.display().to_string());
        report["learned_lrat_dry_run_artifact_schema"] =
            json!(FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA);
    }
    add_learned_lrat_authority_report_fields(&mut report, outcome.learned_lrat_authority.as_ref());
    if outcome.status != "committed_checker_backed_admission" {
        report["reason"] = json!(outcome.reason);
    }
    report
}

fn add_learned_lrat_authority_report_fields(
    report: &mut Value,
    authority: Option<&FmlaLearnedLratMainProofAuthorityReplayRecord>,
) {
    if let Some(authority) = authority {
        report["learned_lrat_main_proof_authority_status"] = json!(authority.status);
        report["learned_lrat_main_proof_authority_reason"] = json!(authority.reason);
        report["learned_lrat_main_proof_authority_checker_visible_id"] =
            json!(authority.checker_visible_id);
        report["learned_lrat_main_proof_authority_proof_out_path"] =
            json!(authority.proof_out_path);
        report["learned_lrat_main_proof_authority_proof_out_sha256"] =
            json!(authority.proof_out_sha256);
        report["learned_lrat_main_proof_authority_external_checker_verified"] =
            json!(authority.external_checker_verified);
        report["learned_lrat_main_proof_authority_proof_out_contains_lrat_fragment"] =
            json!(authority.proof_out_contains_lrat_fragment);
        report["learned_lrat_main_proof_authority_authorizes_main_proof_out"] =
            json!(authority.authorizes_main_proof_out);
    } else {
        report["learned_lrat_main_proof_authority_status"] = json!("not_requested");
        report["learned_lrat_main_proof_authority_authorizes_main_proof_out"] = json!(false);
    }
}

fn write_fmla_postcheck_summary_tsv(
    path: &Path,
    replay_artifact: &Path,
    outcome: &FmlaPostcheckAdmissionOutcome,
    replay_artifact_sha256: &str,
) -> anyhow::Result<()> {
    let line = if let Some(replay) = outcome.replay.as_ref() {
        format!(
            "{}\t{}\t{}\t{}\t{}\t{}\n",
            replay.status,
            replay_artifact.display(),
            replay_artifact_sha256,
            replay.proof_obligation_rows,
            replay.external_checker_verdict_artifact_rows,
            replay.post_replay_preprocess_tx_committed
        )
    } else if outcome.status == "rejected" {
        "rejected\t\t\t\t\t\n".to_string()
    } else {
        "\t\t\t\t\t\n".to_string()
    };
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        std::fs::create_dir_all(parent)
            .with_context(|| format!("cannot create summary directory '{}'", parent.display()))?;
    }
    std::fs::write(path, line)
        .with_context(|| format!("cannot write Fmla replay summary '{}'", path.display()))
}

fn fmla_replay_reject_reason(reject: &FmlaPostCheckAdmissionReplayReject) -> &'static str {
    match reject {
        FmlaPostCheckAdmissionReplayReject::MaterializerNotExercised => {
            "materializer_not_exercised"
        }
        FmlaPostCheckAdmissionReplayReject::MissingMaterializedRows => "missing_materialized_rows",
        FmlaPostCheckAdmissionReplayReject::MissingRuntimeRows => "missing_runtime_rows",
        FmlaPostCheckAdmissionReplayReject::AlreadyCommitted => "already_committed",
        FmlaPostCheckAdmissionReplayReject::NotFailClosed => "not_fail_closed",
        FmlaPostCheckAdmissionReplayReject::MissingExternalCheckerVerdict => {
            "missing_external_checker_verdict"
        }
        FmlaPostCheckAdmissionReplayReject::ExternalCheckerVerdictNotAccepted { reason } => reason,
    }
}

fn canonical_parent(path: &Path) -> std::io::Result<PathBuf> {
    path.parent()
        .unwrap_or_else(|| Path::new("."))
        .canonicalize()
}

fn canonical_string(path: &Path) -> std::io::Result<String> {
    path.canonicalize().map(|path| path.display().to_string())
}

fn json_string(payload: &Value, key: &str) -> Result<String, String> {
    payload
        .get(key)
        .and_then(Value::as_str)
        .map(ToOwned::to_owned)
        .ok_or_else(|| format!("{key}_missing"))
}

fn json_path_string(payload: &Value, key: &str) -> Result<String, String> {
    let value = json_string(payload, key)?;
    canonical_string(Path::new(&value)).map_err(|_| format!("{key}_path_missing"))
}

fn json_i32(payload: &Value, key: &str) -> Result<i32, String> {
    let value = payload.get(key).ok_or_else(|| format!("{key}_missing"))?;
    let parsed = value.as_i64().ok_or_else(|| format!("{key}_not_integer"))?;
    i32::try_from(parsed).map_err(|_| format!("{key}_out_of_range"))
}

fn json_string_array(payload: &Value, key: &str) -> Result<Vec<String>, String> {
    payload
        .get(key)
        .and_then(Value::as_array)
        .ok_or_else(|| format!("{key}_missing"))?
        .iter()
        .map(|item| {
            item.as_str()
                .map(ToOwned::to_owned)
                .ok_or_else(|| format!("{key}_not_string_array"))
        })
        .collect()
}

fn sha256_file_hex(path: &Path) -> anyhow::Result<String> {
    let mut file = File::open(path).with_context(|| format!("cannot read '{}'", path.display()))?;
    let mut digest = Sha256::new();
    let mut buffer = vec![0_u8; 1024 * 64];
    loop {
        let read = file
            .read(&mut buffer)
            .with_context(|| format!("cannot read '{}'", path.display()))?;
        if read == 0 {
            break;
        }
        digest.update(&buffer[..read]);
    }
    Ok(hex_encode(&digest.finalize()))
}

fn check_dimacs_model(formula: &Path, stdout: &Path) -> ModelCheckReport {
    let start = Instant::now();
    let mut report = ModelCheckReport {
        model_status: "valid".to_owned(),
        num_vars: None,
        clauses_checked: 0,
        first_unsatisfied_clause: None,
        elapsed_ms: 0,
    };

    let header = match read_dimacs_header_path(formula) {
        Ok(header) => header,
        Err(status) => {
            report.model_status = status;
            report.elapsed_ms = start.elapsed().as_millis();
            return report;
        }
    };
    report.num_vars = Some(header.num_vars);

    let assignment = match parse_satcomp_model_stdout(stdout, header.num_vars) {
        Ok(assignment) => assignment,
        Err(status) => {
            report.model_status = status;
            report.elapsed_ms = start.elapsed().as_millis();
            return report;
        }
    };

    if let Err(status) = stream_check_dimacs_clauses(formula, &assignment, &mut report) {
        report.model_status = status;
    } else if report.first_unsatisfied_clause.is_some() {
        report.model_status = "invalid".to_owned();
    }
    report.elapsed_ms = start.elapsed().as_millis();
    report
}

fn read_dimacs_header_path(path: &Path) -> Result<ay_sat::dimacs_core::DimacsHeader, String> {
    stream_dimacs_path(path, |reader| read_dimacs_header(reader))
}

fn read_dimacs_header<R: Read>(reader: R) -> Result<ay_sat::dimacs_core::DimacsHeader, String> {
    let mut reader = BufReader::new(reader);
    let mut line = String::new();
    let mut line_number = 0usize;
    loop {
        line.clear();
        let read = reader
            .read_line(&mut line)
            .map_err(|error| format!("error:{error}"))?;
        if read == 0 {
            return Err("error:missing problem line".to_owned());
        }
        line_number += 1;
        let stripped = line.trim();
        if stripped.is_empty() || stripped.starts_with('c') {
            continue;
        }
        if stripped.starts_with('%') {
            return Err("error:missing problem line".to_owned());
        }
        let parts: Vec<_> = stripped.split_whitespace().collect();
        if parts.len() >= 4 && parts[0] == "p" && parts[1] == "cnf" {
            let num_vars = parts[2]
                .parse::<usize>()
                .map_err(|_| format!("error:line {line_number}: invalid problem line"))?;
            let num_clauses = parts[3]
                .parse::<usize>()
                .map_err(|_| format!("error:line {line_number}: invalid problem line"))?;
            return Ok(ay_sat::dimacs_core::DimacsHeader {
                num_vars,
                num_clauses,
            });
        }
        return Err(format!("error:line {line_number}: invalid problem line"));
    }
}

fn parse_satcomp_model_stdout(path: &Path, num_vars: usize) -> Result<Vec<i8>, String> {
    let file = File::open(path).map_err(|error| format!("error:{error}"))?;
    parse_satcomp_model_reader(BufReader::new(file), num_vars)
}

fn parse_satcomp_model_reader<R: BufRead>(reader: R, num_vars: usize) -> Result<Vec<i8>, String> {
    let mut assignment = vec![0i8; num_vars + 1];
    let mut saw_model_line = false;
    let mut saw_assignment = false;
    let mut saw_terminator = false;

    for (line_index, line) in reader.lines().enumerate() {
        let line_no = line_index + 1;
        let line = line.map_err(|error| format!("error:{error}"))?;
        if !line.starts_with('v') {
            continue;
        }
        saw_model_line = true;
        if line != "v" && !line.starts_with("v ") {
            return Err(format!("malformed:{line_no}"));
        }
        let tokens: Vec<&str> = line[1..].split_whitespace().collect();
        if tokens.is_empty() {
            return Err(format!("malformed:{line_no}"));
        }
        if saw_terminator {
            for token in tokens {
                let lit = parse_model_lit(token, line_no)?;
                if lit == 0 {
                    return Err(format!("duplicate-terminator:{line_no}"));
                }
            }
            return Err(format!("malformed:{line_no}"));
        }
        for (token_index, token) in tokens.iter().enumerate() {
            let lit = parse_model_lit(token, line_no)?;
            if lit == 0 {
                if token_index != tokens.len() - 1 {
                    for trailing in &tokens[token_index + 1..] {
                        let trailing_lit = parse_model_lit(trailing, line_no)?;
                        if trailing_lit == 0 {
                            return Err(format!("duplicate-terminator:{line_no}"));
                        }
                    }
                    return Err(format!("malformed:{line_no}"));
                }
                saw_terminator = true;
                break;
            }

            let var = lit.unsigned_abs() as usize;
            if var == 0 || var > num_vars {
                return Err("invalid".to_owned());
            }
            let value = if lit > 0 { 1 } else { -1 };
            match assignment[var] {
                0 => {
                    assignment[var] = value;
                    saw_assignment = true;
                }
                previous if previous != value => return Err("contradictory".to_owned()),
                _ => return Err(format!("duplicate-assignment:{line_no}")),
            }
        }
    }

    if !saw_model_line || (!saw_assignment && num_vars != 0) {
        return Err("missing".to_owned());
    }
    if !saw_terminator {
        return Err("unterminated".to_owned());
    }
    Ok(assignment)
}

fn parse_model_lit(token: &str, line_no: usize) -> Result<i32, String> {
    token
        .parse::<i32>()
        .map_err(|_| format!("malformed:{line_no}"))
}

fn stream_check_dimacs_clauses(
    formula: &Path,
    assignment: &[i8],
    report: &mut ModelCheckReport,
) -> Result<(), String> {
    stream_dimacs_path(formula, |reader| {
        parse_dimacs_events(reader, |event| {
            match event {
                DimacsEvent::Header(_) => {}
                DimacsEvent::Record(DimacsRecordRef::Clause(clause)) => {
                    report.clauses_checked = report.clauses_checked.saturating_add(1);
                    if report.first_unsatisfied_clause.is_none()
                        && !clause_satisfied_by_assignment(clause, assignment)
                    {
                        report.first_unsatisfied_clause = Some(report.clauses_checked);
                    }
                }
                DimacsEvent::Record(DimacsRecordRef::Tagged { tag, .. }) => {
                    return Err(DimacsCoreError::IoError(format!(
                        "unsupported tagged DIMACS record '{tag}'"
                    )));
                }
                _ => {
                    return Err(DimacsCoreError::IoError(
                        "unsupported DIMACS parser event".to_owned(),
                    ));
                }
            }
            Ok(())
        })
        .map_err(|error| format!("error:{error}"))?;
        Ok(())
    })
}

fn clause_satisfied_by_assignment(clause: &[i32], assignment: &[i8]) -> bool {
    clause.iter().any(|&lit| {
        let var = lit.unsigned_abs() as usize;
        let Some(&value) = assignment.get(var) else {
            return false;
        };
        value != 0 && (value > 0) == (lit > 0)
    })
}

fn stream_dimacs_path<T, F>(path: &Path, f: F) -> Result<T, String>
where
    F: FnOnce(&mut dyn Read) -> Result<T, String>,
{
    if path
        .extension()
        .is_some_and(|extension| extension.eq_ignore_ascii_case("xz"))
    {
        let mut child = Command::new("xz")
            .arg("-dc")
            .arg(path)
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|error| format!("error:failed to run xz: {error}"))?;
        let mut stdout = child
            .stdout
            .take()
            .ok_or_else(|| "error:failed to capture xz stdout".to_owned())?;
        let result = f(&mut stdout);
        drop(stdout);
        let status = child
            .wait()
            .map_err(|error| format!("error:failed to wait for xz: {error}"))?;
        if !xz_status_success_or_sigpipe(&status) {
            return Err(format!("error:xz exited with {status}"));
        }
        return result;
    }

    let mut file = File::open(path).map_err(|error| format!("error:{error}"))?;
    f(&mut file)
}

fn xz_status_success_or_sigpipe(status: &ExitStatus) -> bool {
    if status.success() {
        return true;
    }

    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;

        // Header-only reads intentionally close xz stdout early.
        const SIGPIPE: i32 = 13;
        status.signal() == Some(SIGPIPE)
    }

    #[cfg(not(unix))]
    {
        false
    }
}

fn run_chc_quotient_check(problem: &Path, certificate: &Path, emit: &str) -> anyhow::Result<()> {
    if emit != CHC_QUOTIENT_CHECK_REPORT_SCHEMA {
        safe_eprintln!(
            "Error: unsupported --emit '{emit}', expected {CHC_QUOTIENT_CHECK_REPORT_SCHEMA}"
        );
        std::process::exit(64);
    }

    let problem_text = std::fs::read_to_string(problem)
        .with_context(|| format!("cannot read CHC problem {}", problem.display()))?;
    let parsed_problem = match ChcParser::parse(&problem_text) {
        Ok(problem) => problem,
        Err(error) => {
            safe_eprintln!(
                "Error: cannot parse CHC problem {}: {error}",
                problem.display()
            );
            std::process::exit(65);
        }
    };
    let certificate_text = std::fs::read_to_string(certificate)
        .with_context(|| format!("cannot read quotient certificate {}", certificate.display()))?;

    let report = check_recursive_lia_quotient_certificate(&parsed_problem, &certificate_text);
    let mut output = serde_json::to_vec_pretty(&report.to_json_value())
        .context("cannot serialize CHC quotient checker report")?;
    output.push(b'\n');
    if let Err(error) = std::io::stdout().write_all(&output) {
        safe_eprintln!("Error: failed to write CHC quotient checker JSON: {error}");
        std::process::exit(74);
    }

    std::process::exit(if report.accepted() {
        0
    } else if report.structurally_valid() {
        2
    } else {
        1
    });
}

/// Run an observational cross-check using `ay-replay`'s `SequentialReplayer`
/// and log whether the two verdicts agree.
///
/// Phase 2 of the ay-replay design (AUDIT-2 Y6, #8789): the `replay-jit`
/// feature wires in ay-replay's DRAT path as a second opinion. The cross-check
/// is **observational only** — it does not change the exit code or the verdict
/// printed to stdout. Differences are logged on stderr with a `c replay-jit:`
/// prefix so downstream tooling can grep for them.
///
/// `native_verified` is the native checker's verdict (`Ok(())` → verified).
/// On any internal error (parse failure inside ay-replay, degenerate CNF),
/// the function logs the error and returns without touching the verdict.
#[cfg(feature = "replay-jit")]
fn replay_cross_check(
    err: &mut impl Write,
    cnf_bytes: &[u8],
    proof_bytes: &[u8],
    native_verified: bool,
) -> std::io::Result<()> {
    use ay_replay::drat::{DratReplayInput, SequentialReplayer};

    let replayer = SequentialReplayer::new();
    let input = DratReplayInput {
        cnf: cnf_bytes,
        proof: proof_bytes,
    };
    let plan = match replayer.load(&input) {
        Ok(p) => p,
        Err(e) => {
            writeln!(err, "c replay-jit: load error: {e}")?;
            return Ok(());
        }
    };
    let outcome = match replayer.replay(&plan) {
        Ok(o) => o,
        Err(e) => {
            writeln!(err, "c replay-jit: replay error: {e}")?;
            return Ok(());
        }
    };
    let replay_verified = outcome.is_verified();
    writeln!(
        err,
        "c replay-jit: native={} replay={} agree={} steps={} add={} del={}",
        native_verified,
        replay_verified,
        native_verified == replay_verified,
        plan.step_count(),
        outcome.add_steps_verified,
        outcome.delete_steps_applied,
    )?;
    if native_verified != replay_verified {
        writeln!(
            err,
            "c replay-jit: DISAGREEMENT — native and replay verdicts differ"
        )?;
        if let Some(reason) = outcome.failure_reason.as_deref() {
            writeln!(err, "c replay-jit: replay failure reason: {reason}")?;
        }
    }
    Ok(())
}

/// Print DRAT verification statistics to stderr.
fn print_drat_stats(
    err: &mut impl Write,
    s: &ay_drat_check::Stats,
    secs: f64,
) -> std::io::Result<()> {
    writeln!(err, "c original clauses:  {}", s.original)?;
    writeln!(err, "c proof additions:   {}", s.additions)?;
    writeln!(err, "c proof deletions:   {}", s.deletions)?;
    writeln!(err, "c RUP checks:        {}", s.checks)?;
    writeln!(err, "c RAT checks:        {}", s.rat_checks)?;
    writeln!(err, "c propagations:      {}", s.propagations)?;
    writeln!(err, "c failures:          {}", s.failures)?;
    writeln!(err, "c missed deletes:    {}", s.missed_deletes)?;
    writeln!(err, "c time:              {secs:.3}s")
}

fn write_build_provenance(err: &mut impl Write) -> std::io::Result<()> {
    writeln!(err, "{}", stats_output::BUILD_PROVENANCE.comment_line())
}

fn sha256_prefixed(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    format!("sha256:{}", hex_encode(&digest))
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

fn generated_at_unix_ms() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis()
}

fn write_evidence_json(path: &Path, value: &Value) -> anyhow::Result<()> {
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        std::fs::create_dir_all(parent)
            .with_context(|| format!("cannot create evidence directory '{}'", parent.display()))?;
    }
    let mut data = serde_json::to_vec_pretty(value).context("cannot serialize evidence JSON")?;
    data.push(b'\n');
    std::fs::write(path, data)
        .with_context(|| format!("cannot write evidence JSON '{}'", path.display()))
}

fn evidence_artifact_path<'a>(
    proof: &'a Path,
    evidence: &'a EvidenceConfig,
    verified: bool,
) -> &'a Path {
    evidence
        .artifact_path
        .as_deref()
        .or_else(|| {
            verified
                .then_some(evidence.proof_artifact_json.as_deref())
                .flatten()
        })
        .unwrap_or(proof)
}

fn evidence_project_name(evidence: &EvidenceConfig) -> &str {
    evidence.project.as_deref().unwrap_or("ay-sat-research")
}

fn maybe_write_replay_proof_artifact(
    evidence: &EvidenceConfig,
    proof_format: &str,
    formula: &Path,
    proof: &Path,
    cnf_data: &[u8],
    proof_data: &[u8],
    verified: bool,
) -> anyhow::Result<()> {
    let Some(path) = evidence.proof_artifact_json.as_deref() else {
        return Ok(());
    };
    if !verified {
        return Ok(());
    }

    let dimacs = std::str::from_utf8(cnf_data)
        .context("proof-artifact-v1 replay envelope requires UTF-8 DIMACS input")?;
    let proof_text = std::str::from_utf8(proof_data).with_context(|| {
        format!(
            "proof-artifact-v1 replay envelope requires text {proof_format} proof; binary proofs are not supported by this text replay envelope"
        )
    })?;
    if proof_text.trim().is_empty() {
        return Err(anyhow::anyhow!(
            "proof-artifact-v1 replay envelope requires a non-empty text {proof_format} proof"
        ));
    }
    let problem_hash = sha256_prefixed(cnf_data);
    let proof_hash = sha256_prefixed(proof_data);
    let mut metadata = json!({
        "dimacs": dimacs,
        "input_path": formula.display().to_string(),
        "proof_path": proof.display().to_string(),
        "proof_format": proof_format,
        "ay_check_schema": AY_CHECK_EVIDENCE_SCHEMA
    });
    if let Some(evidence_json) = evidence.json_path.as_deref() {
        metadata["ay_check_evidence_path"] = json!(evidence_json.display().to_string());
    }

    let artifact = json!({
        "version": "proof-artifact-v1",
        "producer": {
            "repo": env!("CARGO_PKG_REPOSITORY"),
            "commit": stats_output::BUILD_PROVENANCE.commit,
            "name": "ay",
            "version": stats_output::BUILD_PROVENANCE.version
        },
        "source_system": "sat-pb",
        "problem_hash": &problem_hash,
        "model_hash": &problem_hash,
        "proof_hash": &proof_hash,
        "certification": {
            "evidence_kind": "replay_only"
        },
        "artifact_kind": proof_format,
        "verifier_constants": [],
        "certificate": {
            "format": proof_format,
            "encoding": "text",
            "payload_hash": &proof_hash,
            "payload": proof_text
        },
        "metadata": metadata
    });
    write_evidence_json(path, &artifact)
}

fn maybe_write_drat_evidence(
    evidence: &EvidenceConfig,
    formula: &Path,
    proof: &Path,
    cnf_data: &[u8],
    proof_data: &[u8],
    cnf: &ay_drat_check::cnf_parser::CnfFormula,
    steps: &[ay_drat_check::drat_parser::ProofStep],
    stats: &ay_drat_check::Stats,
    check_rat: bool,
    backward: bool,
    verified: bool,
    failure_reason: Option<String>,
    elapsed_ms: u128,
) -> anyhow::Result<()> {
    let Some(path) = evidence.json_path.as_deref() else {
        return Ok(());
    };

    let add_step_count = steps
        .iter()
        .filter(|step| matches!(step, ay_drat_check::drat_parser::ProofStep::Add(_)))
        .count();
    let delete_step_count = steps
        .iter()
        .filter(|step| matches!(step, ay_drat_check::drat_parser::ProofStep::Delete(_)))
        .count();
    let cnf_hash = sha256_prefixed(cnf_data);
    let proof_hash = sha256_prefixed(proof_data);
    let replay_status = if verified { "pass" } else { "fail" };
    let ay_replay_status = if verified {
        "verified_unsat"
    } else {
        "proof_rejected"
    };
    let proof_strength = if verified {
        if check_rat {
            "drat_kernel_checked"
        } else {
            "drat_rup_kernel_checked"
        }
    } else {
        "rejected"
    };
    let proof_kernel = if check_rat {
        "ay-drat-check"
    } else {
        "ay-drat-rup-check"
    };
    let artifact_path = evidence_artifact_path(proof, evidence, verified);

    let value = json!({
        "schema": AY_CHECK_EVIDENCE_SCHEMA,
        "schema_version": RESTRICTED_RULE_SUBSET_ARTIFACT_REPLAY_SCHEMA,
        "generated_at_unix_ms": generated_at_unix_ms(),
        "satcomp": {
            "track": "main",
            "result_kind": "unsat-proof-replay",
            "deterministic_replay": true
        },
        "project": evidence_project_name(evidence),
        "source_system": "sat-pb",
        "artifact_kind": "drat",
        "artifact_path": artifact_path.display().to_string(),
        "problem_hash": &cnf_hash,
        "proof_hash": &proof_hash,
        "certificate_format": "drat",
        "evidence_kind": "replay_only",
        "kernel_certified": false,
        "replay_status": replay_status,
        "ay_replay_status": ay_replay_status,
        "proof_strength": proof_strength,
        "replay_engine": "sat-pb-drat-v1",
        "linked_obligations": &evidence.linked_obligations,
        "trusted_assumptions": [],
        "ay_build": stats_output::BUILD_PROVENANCE.json_value(),
        "solver_mode": "dimacs-sat",
        "theory_set": ["sat"],
        "resource_policy": {
            "deterministic": true,
            "external_solver": false
        },
        "solver_status": "unsat",
        "artifact_hashes": {
            "cnf_sha256": &cnf_hash,
            "proof_sha256": &proof_hash
        },
        "checker_invocation": {
            "subcommand": "check drat",
            "formula_path": formula.display().to_string(),
            "proof_path": proof.display().to_string(),
            "options": {
                "rup_only": !check_rat,
                "check_rat": check_rat,
                "backward": backward
            }
        },
        "proof_metadata": {
            "proof_format": "drat",
            "proof_kernel": proof_kernel,
            "binary_proof": ay_drat_check::drat_parser::is_binary_drat(proof_data),
            "num_vars": cnf.num_vars,
            "original_clause_count": cnf.clauses.len(),
            "proof_step_count": steps.len(),
            "add_step_count": add_step_count,
            "delete_step_count": delete_step_count,
            "steps_replayed": steps.len(),
            "deterministic_replay": true
        },
        "result": {
            "verified": verified,
            "exit_code": if verified { 0 } else { 1 },
            "stdout_status_line": if verified { "s VERIFIED" } else { "s NOT VERIFIED" },
            "failure_reason": failure_reason,
            "elapsed_ms": elapsed_ms
        },
        "stats": {
            "original": stats.original,
            "additions": stats.additions,
            "deletions": stats.deletions,
            "checks": stats.checks,
            "rat_checks": stats.rat_checks,
            "propagations": stats.propagations,
            "failures": stats.failures,
            "missed_deletes": stats.missed_deletes,
            "reduced_literals": stats.reduced_literals,
            "pseudo_unit_skips": stats.pseudo_unit_skips
        },
        "details": [{
            "kind": "ay-check-drat",
            "verified": verified,
            "proof_strength": proof_strength,
            "proof_step_count": steps.len()
        }]
    });
    write_evidence_json(path, &value)
}

fn lrat_stats_value(stats: &ay_lrat_check::checker::Stats) -> Value {
    json!({
        "originals": stats.originals,
        "derived": stats.derived,
        "deleted": stats.deleted,
        "deleted_originals": stats.deleted_originals,
        "weakened": stats.weakened,
        "restored": stats.restored,
        "failures": stats.failures,
        "finalized": stats.finalized,
        "rup_ok": stats.rup_ok,
        "resolution_ok": stats.resolution_ok,
        "resolution_mismatch": stats.resolution_mismatch,
        "rat_ok": stats.rat_ok,
        "blocked_ok": stats.blocked_ok,
        "compactions": stats.compactions
    })
}

fn maybe_write_lrat_evidence(
    evidence: &EvidenceConfig,
    formula: &Path,
    proof: &Path,
    cnf_data: &[u8],
    proof_data: &[u8],
    cnf: &ay_lrat_check::dimacs::CnfFormulaWithIds,
    steps: &[ay_lrat_check::lrat_parser::LratStep],
    stats: &ay_lrat_check::checker::Stats,
    verified: bool,
    failure_reason: Option<String>,
    elapsed_ms: u128,
) -> anyhow::Result<()> {
    let Some(path) = evidence.json_path.as_deref() else {
        return Ok(());
    };

    let add_step_count = steps
        .iter()
        .filter(|step| matches!(step, ay_lrat_check::lrat_parser::LratStep::Add { .. }))
        .count();
    let delete_step_count = steps
        .iter()
        .filter(|step| matches!(step, ay_lrat_check::lrat_parser::LratStep::Delete { .. }))
        .count();
    let cnf_hash = sha256_prefixed(cnf_data);
    let proof_hash = sha256_prefixed(proof_data);
    let replay_status = if verified { "pass" } else { "fail" };
    let ay_replay_status = if verified {
        "verified_unsat"
    } else {
        "proof_rejected"
    };
    let proof_strength = if verified {
        "lrat_kernel_checked"
    } else {
        "rejected"
    };
    let artifact_path = evidence_artifact_path(proof, evidence, verified);

    let value = json!({
        "schema": AY_CHECK_EVIDENCE_SCHEMA,
        "schema_version": RESTRICTED_RULE_SUBSET_ARTIFACT_REPLAY_SCHEMA,
        "generated_at_unix_ms": generated_at_unix_ms(),
        "satcomp": {
            "track": "main",
            "result_kind": "unsat-proof-replay",
            "deterministic_replay": true
        },
        "project": evidence_project_name(evidence),
        "source_system": "sat-pb",
        "artifact_kind": "lrat",
        "artifact_path": artifact_path.display().to_string(),
        "problem_hash": &cnf_hash,
        "proof_hash": &proof_hash,
        "certificate_format": "lrat",
        "evidence_kind": "replay_only",
        "kernel_certified": false,
        "replay_status": replay_status,
        "ay_replay_status": ay_replay_status,
        "proof_strength": proof_strength,
        "replay_engine": "sat-pb-lrat-v1",
        "linked_obligations": &evidence.linked_obligations,
        "trusted_assumptions": [],
        "ay_build": stats_output::BUILD_PROVENANCE.json_value(),
        "solver_mode": "dimacs-sat",
        "theory_set": ["sat"],
        "resource_policy": {
            "deterministic": true,
            "external_solver": false
        },
        "solver_status": "unsat",
        "artifact_hashes": {
            "cnf_sha256": &cnf_hash,
            "proof_sha256": &proof_hash
        },
        "checker_invocation": {
            "subcommand": "check lrat",
            "formula_path": formula.display().to_string(),
            "proof_path": proof.display().to_string(),
            "options": {}
        },
        "proof_metadata": {
            "proof_format": "lrat",
            "proof_kernel": "ay-lrat-check",
            "binary_proof": ay_lrat_check::lrat_parser::is_binary_lrat(proof_data),
            "num_vars": cnf.num_vars,
            "original_clause_count": cnf.clauses.len(),
            "proof_step_count": steps.len(),
            "add_step_count": add_step_count,
            "delete_step_count": delete_step_count,
            "steps_replayed": steps.len(),
            "deterministic_replay": true
        },
        "result": {
            "verified": verified,
            "exit_code": if verified { 0 } else { 1 },
            "stdout_status_line": if verified { "s VERIFIED" } else { "s NOT VERIFIED" },
            "failure_reason": failure_reason,
            "elapsed_ms": elapsed_ms
        },
        "stats": lrat_stats_value(stats),
        "details": [{
            "kind": "ay-check-lrat",
            "verified": verified,
            "proof_strength": proof_strength,
            "proof_step_count": steps.len()
        }]
    });
    write_evidence_json(path, &value)
}

/// DRAT/DRUP proof verification.
///
/// Ported from `crates/ay-drat-check/src/main.rs::run()`.
fn run_drat_check(
    formula: &Path,
    proof: &Path,
    check_rat: bool,
    backward: bool,
    show_stats: bool,
    evidence: EvidenceConfig,
) -> anyhow::Result<()> {
    let start = Instant::now();

    let cnf_data =
        std::fs::read(formula).with_context(|| format!("cannot read '{}'", formula.display()))?;
    let cnf =
        ay_drat_check::cnf_parser::parse_cnf(&cnf_data[..]).map_err(|e| anyhow::anyhow!("{e}"))?;
    anyhow::ensure!(
        cnf.num_vars <= ay_drat_check::checker::MAX_DENSE_VARS,
        "formula variable count {} exceeds DRAT checker's dense maximum {}",
        cnf.num_vars,
        ay_drat_check::checker::MAX_DENSE_VARS
    );

    let proof_data =
        std::fs::read(proof).with_context(|| format!("cannot read '{}'", proof.display()))?;
    let steps =
        ay_drat_check::drat_parser::parse_drat(&proof_data).map_err(|e| anyhow::anyhow!("{e}"))?;

    let (result, stats) = if backward {
        let mut chk =
            ay_drat_check::checker::backward::BackwardChecker::new(cnf.num_vars, check_rat);
        let r = chk.verify(&cnf.clauses, &steps);
        (r, chk.stats().clone())
    } else {
        let mut chk = ay_drat_check::checker::DratChecker::new(cnf.num_vars, check_rat);
        let r = chk.verify(&cnf.clauses, &steps);
        (r, chk.stats().clone())
    };

    let secs = start.elapsed().as_secs_f64();
    let mut out = std::io::stdout();
    let mut err = std::io::stderr();
    write_build_provenance(&mut err)?;

    // Observational replay cross-check (opt-in; OFF by default).
    // Does NOT change the verdict or exit code.
    #[cfg(feature = "replay-jit")]
    {
        let native_verified = result.is_ok();
        replay_cross_check(&mut err, &cnf_data, &proof_data, native_verified)?;
    }

    let elapsed_ms = start.elapsed().as_millis();
    let verified = result.is_ok();
    let failure_reason = result.as_ref().err().map(ToString::to_string);
    maybe_write_replay_proof_artifact(
        &evidence,
        "drat",
        formula,
        proof,
        &cnf_data,
        &proof_data,
        verified,
    )?;
    maybe_write_drat_evidence(
        &evidence,
        formula,
        proof,
        &cnf_data,
        &proof_data,
        &cnf,
        &steps,
        &stats,
        check_rat,
        backward,
        verified,
        failure_reason.clone(),
        elapsed_ms,
    )?;

    match result {
        Ok(()) => {
            writeln!(out, "s VERIFIED")?;
            if show_stats {
                print_drat_stats(&mut err, &stats, secs)?;
            }
            std::process::exit(0);
        }
        Err(msg) => {
            writeln!(out, "s NOT VERIFIED")?;
            writeln!(err, "c verification failed: {msg}")?;
            if show_stats {
                print_drat_stats(&mut err, &stats, secs)?;
            }
            std::process::exit(1);
        }
    }
}

/// Locate the vendored/external `cake_lpr` verified checker binary.
///
/// Resolution order: explicit `--checker`, then `$CAKE_LPR`, then the vendored
/// `third_party/cake_lpr/cake_lpr` relative to the repo root (derived from
/// `CARGO_MANIFEST_DIR` at build time, falling back to the current directory).
fn resolve_cake_lpr(explicit: Option<&Path>) -> Option<PathBuf> {
    if let Some(p) = explicit {
        return Some(p.to_path_buf());
    }
    if let Some(p) = std::env::var_os("CAKE_LPR") {
        return Some(PathBuf::from(p));
    }
    // crates/ay/ -> repo root is two levels up.
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut candidates = Vec::new();
    if let Some(root) = manifest.parent().and_then(Path::parent) {
        candidates.push(root.join("third_party/cake_lpr/cake_lpr"));
    }
    candidates.push(PathBuf::from("third_party/cake_lpr/cake_lpr"));
    candidates.into_iter().find(|p| p.exists())
}

/// PR/DPR proof verification via the external verified `cake_lpr` LPR checker.
///
/// This is the soundness trust anchor for propagation-redundant clause additions
/// (the lex-leader symmetry SBP): the built-in RUP/RAT checker fails closed on
/// PR, so PR proofs are delegated to the formally verified `cake_lpr`. The
/// verdict is parsed from cake_lpr's stdout (`s VERIFIED UNSAT`), not its exit
/// code — cake_lpr exits 0 even on rejection, printing the error to stderr.
fn run_dpr_check(formula: &Path, proof: &Path, checker: Option<&Path>) -> anyhow::Result<()> {
    let start = Instant::now();
    let mut out = std::io::stdout();
    let mut err = std::io::stderr();
    write_build_provenance(&mut err)?;

    let Some(bin) = resolve_cake_lpr(checker) else {
        writeln!(out, "s NOT VERIFIED")?;
        writeln!(
            err,
            "c cake_lpr checker not found (pass --checker PATH, set $CAKE_LPR, \
             or build third_party/cake_lpr: `make -C third_party/cake_lpr cake_lpr_arm8`)"
        )?;
        std::process::exit(1);
    };

    let output = Command::new(&bin)
        .arg(formula)
        .arg(proof)
        .stdin(Stdio::null())
        .output()
        .with_context(|| format!("failed to run cake_lpr at '{}'", bin.display()))?;

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    let stderr_str = String::from_utf8_lossy(&output.stderr);
    // cake_lpr's verified verdict line. Anything else (including a missing line,
    // a parse error, or "s VERIFIED" for a transformation rather than UNSAT) is
    // NOT a sound UNSAT certificate and must fail closed.
    let verified = stdout_str.lines().any(|l| l.trim() == "s VERIFIED UNSAT");

    let secs = start.elapsed().as_secs_f64();
    writeln!(err, "c cake_lpr: {}", bin.display())?;
    for line in stdout_str.lines() {
        writeln!(err, "c cake_lpr stdout: {line}")?;
    }
    for line in stderr_str.lines() {
        writeln!(err, "c cake_lpr stderr: {line}")?;
    }
    writeln!(err, "c cake_lpr elapsed: {secs:.3}s")?;

    if verified {
        writeln!(out, "s VERIFIED")?;
        std::process::exit(0);
    }
    writeln!(out, "s NOT VERIFIED")?;
    std::process::exit(1);
}

/// PR/SR proof verification via the NATIVE Rust checker (`ay_drat_check::SrChecker`).
///
/// This is the in-tree replacement for delegating PR/SR proofs to external
/// `dsr-trim`/`cake_lpr`: the substitution-redundancy redundancy check is ported
/// onto the same watched-literal BCP engine the DRAT checker uses, with a small
/// trusted kernel (`sr_redundant_step`) deciding each step by reverse unit
/// propagation. No external binary is on the trust path. Mirrors
/// `run_drat_check` (native, fail-closed), NOT `run_dpr_check` (shells out).
fn run_sr_check(formula: &Path, proof: &Path, show_stats: bool) -> anyhow::Result<()> {
    let start = Instant::now();

    let cnf_data =
        std::fs::read(formula).with_context(|| format!("cannot read '{}'", formula.display()))?;
    let cnf =
        ay_drat_check::cnf_parser::parse_cnf(&cnf_data[..]).map_err(|e| anyhow::anyhow!("{e}"))?;
    anyhow::ensure!(
        cnf.num_vars <= ay_drat_check::checker::MAX_DENSE_VARS,
        "formula variable count {} exceeds SR checker's dense maximum {}",
        cnf.num_vars,
        ay_drat_check::checker::MAX_DENSE_VARS
    );

    let proof_data =
        std::fs::read(proof).with_context(|| format!("cannot read '{}'", proof.display()))?;
    let steps =
        ay_drat_check::drat_parser::parse_drat(&proof_data).map_err(|e| anyhow::anyhow!("{e}"))?;

    let mut chk = ay_drat_check::SrChecker::new(cnf.num_vars, true);
    let result = chk.verify(&cnf.clauses, &steps);
    let stats = chk.stats().clone();

    let secs = start.elapsed().as_secs_f64();
    let mut out = std::io::stdout();
    let mut err = std::io::stderr();
    write_build_provenance(&mut err)?;

    match result {
        Ok(()) => {
            writeln!(out, "s VERIFIED")?;
            if show_stats {
                print_drat_stats(&mut err, &stats, secs)?;
            }
            std::process::exit(0);
        }
        Err(msg) => {
            writeln!(out, "s NOT VERIFIED")?;
            writeln!(err, "c verification failed: {msg}")?;
            if show_stats {
                print_drat_stats(&mut err, &stats, secs)?;
            }
            std::process::exit(1);
        }
    }
}

/// LRAT proof verification.
///
/// Ported from `crates/ay-lrat-check/src/main.rs::run()`.
fn run_lrat_check(formula: &Path, proof: &Path, evidence: EvidenceConfig) -> anyhow::Result<()> {
    let start = Instant::now();
    let cnf_data =
        std::fs::read(formula).with_context(|| format!("cannot read '{}'", formula.display()))?;
    let cnf = ay_lrat_check::dimacs::parse_cnf_with_ids(&cnf_data[..])
        .map_err(|e| anyhow::anyhow!("{e}"))?;
    anyhow::ensure!(
        cnf.num_vars <= ay_lrat_check::checker::MAX_DENSE_VARS,
        "formula variable count {} exceeds LRAT checker's dense maximum {}",
        cnf.num_vars,
        ay_lrat_check::checker::MAX_DENSE_VARS
    );

    let proof_data =
        std::fs::read(proof).with_context(|| format!("cannot read '{}'", proof.display()))?;

    let is_binary = ay_lrat_check::lrat_parser::is_binary_lrat(&proof_data);
    let steps = if is_binary {
        ay_lrat_check::lrat_parser::parse_binary_lrat(&proof_data)
            .map_err(|e| anyhow::anyhow!("{e}"))?
    } else {
        let proof_text =
            std::str::from_utf8(&proof_data).context("proof file is not valid UTF-8")?;
        ay_lrat_check::lrat_parser::parse_text_lrat(proof_text)
            .map_err(|e| anyhow::anyhow!("{e}"))?
    };

    let mut chk = ay_lrat_check::checker::LratChecker::new(cnf.num_vars);
    let mut out = std::io::stdout();
    let mut err = std::io::stderr();
    write_build_provenance(&mut err)?;

    for (id, clause) in &cnf.clauses {
        if !chk.add_original(*id, clause) {
            let stats = chk.stats().clone();
            maybe_write_lrat_evidence(
                &evidence,
                formula,
                proof,
                &cnf_data,
                &proof_data,
                &cnf,
                &steps,
                &stats,
                false,
                Some(format!("failed to add original clause {id}")),
                start.elapsed().as_millis(),
            )?;
            let _ = writeln!(err, "c {}", chk.stats_summary());
            writeln!(out, "s NOT VERIFIED")?;
            std::process::exit(1);
        }
    }

    let result = chk.verify_proof(&steps);
    let stats = chk.stats().clone();
    maybe_write_replay_proof_artifact(
        &evidence,
        "lrat",
        formula,
        proof,
        &cnf_data,
        &proof_data,
        result,
    )?;
    maybe_write_lrat_evidence(
        &evidence,
        formula,
        proof,
        &cnf_data,
        &proof_data,
        &cnf,
        &steps,
        &stats,
        result,
        (!result).then(|| "lrat proof rejected".to_owned()),
        start.elapsed().as_millis(),
    )?;
    let _ = writeln!(err, "c {}", chk.stats_summary());

    if result {
        writeln!(out, "s VERIFIED")?;
        std::process::exit(0);
    } else {
        writeln!(out, "s NOT VERIFIED")?;
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write_fixture(dir: &tempfile::TempDir, name: &str, text: &str) -> PathBuf {
        let path = dir.path().join(name);
        std::fs::write(&path, text).expect("write fixture");
        path
    }

    fn sha256_hex_bytes(bytes: &[u8]) -> String {
        hex_encode(&Sha256::digest(bytes))
    }

    fn fmla_dry_run_lrat_fragment() -> &'static str {
        "9 1 5 0 1 6 3 0\n10 1 -2 0 6 9 1 0\n"
    }

    fn write_fmla_dry_run_artifact(dir: &tempfile::TempDir) -> PathBuf {
        let fragment = fmla_dry_run_lrat_fragment();
        let payload = json!({
            "schema": FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA,
            "checker_visible_id": 10,
            "materialization_status": "retained_dependencies_complete",
            "rows": [
                {
                    "kind": "materializer_add",
                    "checker_visible_id": 9,
                    "clause_lits_dimacs": [1, 5],
                    "checker_visible_lrat_hints": [1, 6, 3],
                    "lrat_line": "9 1 5 0 1 6 3 0\n",
                },
                {
                    "kind": "learned_add",
                    "checker_visible_id": 10,
                    "clause_lits_dimacs": [1, -2],
                    "checker_visible_lrat_hints": [6, 9, 1],
                    "lrat_line": "10 1 -2 0 6 9 1 0\n",
                },
            ],
            "lrat_fragment": fragment,
            "lrat_fragment_sha256": sha256_hex_bytes(fragment.as_bytes()),
            "proof_out_emitted": false,
            "proof_writer_io_error": false,
            "external_checker_required": true,
            "external_checker_verified": false,
            "main_proof_authority_reason": "external_checker_required",
            "authorizes_main_proof_out": false,
        });
        let path = dir
            .path()
            .join("fmla-learned-lrat-dry-run-proof-artifact.json");
        std::fs::write(
            &path,
            serde_json::to_vec_pretty(&payload).expect("serialize dry-run"),
        )
        .expect("write dry-run artifact");
        path
    }

    fn write_fmla_external_checker_artifact(
        dir: &tempfile::TempDir,
        dimacs: &Path,
        proof_out: &Path,
    ) -> (PathBuf, String) {
        let artifact = dir
            .path()
            .join(FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.artifact_file_name);
        let artifact_path = dir
            .path()
            .canonicalize()
            .expect("canonical tempdir")
            .join(FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.artifact_file_name)
            .display()
            .to_string();
        let dimacs_path = dimacs
            .canonicalize()
            .expect("canonical dimacs")
            .display()
            .to_string();
        let proof_out_path = proof_out
            .canonicalize()
            .expect("canonical proof_out")
            .display()
            .to_string();
        let dimacs_sha256 = sha256_file_hex(dimacs).expect("hash dimacs");
        let proof_out_sha256 = sha256_file_hex(proof_out).expect("hash proof_out");
        let checker_path = "/opt/satcomp/bin/cake_lpr";
        let payload = json!({
            "schema": FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA,
            "runtime_field": FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.runtime_field,
            "artifact_path": artifact_path,
            "checker_path": checker_path,
            "checker_sha256": "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
            "checker_command": format!("{checker_path} {dimacs_path} {proof_out_path}"),
            "checker_argv": [checker_path, dimacs_path, proof_out_path],
            "checker_exit_code": 0,
            "proof_out_path": proof_out.canonicalize().expect("canonical proof_out").display().to_string(),
            "proof_out_sha256": proof_out_sha256,
            "checked_dimacs_path": dimacs.canonicalize().expect("canonical dimacs").display().to_string(),
            "checked_dimacs_sha256": dimacs_sha256,
            "verdict": FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.accepted_verdict,
        });
        std::fs::write(
            &artifact,
            serde_json::to_vec_pretty(&payload).expect("serialize checker artifact"),
        )
        .expect("write checker artifact");
        let sha256 = sha256_file_hex(&artifact).expect("hash checker artifact");
        (artifact, sha256)
    }

    fn fmla_postcheck_input(
        dir: &tempfile::TempDir,
        proof_out_body: &str,
        dry_run_artifact: Option<PathBuf>,
    ) -> FmlaPostcheckAdmissionCliInput {
        let dimacs = write_fixture(
            dir,
            "FmlaEquivChain_4_6_6.sanitized.cnf",
            "p cnf 2 1\n1 0\n",
        );
        let proof_out = write_fixture(dir, "proof.out", proof_out_body);
        let (external_checker_artifact, external_checker_artifact_sha256) =
            write_fmla_external_checker_artifact(dir, &dimacs, &proof_out);
        FmlaPostcheckAdmissionCliInput {
            dimacs,
            proof_out,
            external_checker_artifact,
            external_checker_artifact_sha256,
            learned_lrat_dry_run_artifact: dry_run_artifact,
            ay_lrat_status: "ok".to_string(),
            proof_checker_status: "ok".to_string(),
            replay_artifact: dir.path().join("fmla-postcheck-replay.json"),
            summary_tsv: None,
            materializer_attempts: "1".to_string(),
            materializer_proof_emit_records_seen: "2".to_string(),
            materializer_records: "2".to_string(),
            materializer_fail_closed: "1".to_string(),
            materializer_missing_runtime_records: "0".to_string(),
            preprocess_tx_fail_closed: "1".to_string(),
            preprocess_tx_committed: "0".to_string(),
            emit_json: true,
        }
    }

    #[test]
    fn test_check_dimacs_model_accepts_valid_satcomp_model() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cnf = write_fixture(&dir, "valid.cnf", "p cnf 2 2\n1 -2 0\n2 0\n");
        let stdout = write_fixture(&dir, "stdout.txt", "s SATISFIABLE\nv 1 2 0\n");

        let report = check_dimacs_model(&cnf, &stdout);

        assert_eq!(report.model_status, "valid");
        assert_eq!(report.num_vars, Some(2));
        assert_eq!(report.clauses_checked, 2);
        assert_eq!(report.first_unsatisfied_clause, None);
    }

    #[test]
    fn test_check_dimacs_model_accepts_empty_model_for_zero_variable_cnf() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cnf = write_fixture(&dir, "empty.cnf", "p cnf 0 0\n");
        let stdout = write_fixture(&dir, "stdout.txt", "s SATISFIABLE\nv 0\n");

        let report = check_dimacs_model(&cnf, &stdout);

        assert_eq!(report.model_status, "valid");
        assert_eq!(report.num_vars, Some(0));
        assert_eq!(report.clauses_checked, 0);
    }

    #[test]
    fn test_check_dimacs_model_accepts_valid_xz_satcomp_model() {
        let xz_available = Command::new("xz")
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
        if !matches!(xz_available, Ok(status) if status.success()) {
            return;
        }

        let dir = tempfile::tempdir().expect("tempdir");
        let cnf = write_fixture(&dir, "valid.cnf", "p cnf 2 2\n1 -2 0\n2 0\n");
        let stdout = write_fixture(&dir, "stdout.txt", "s SATISFIABLE\nv 1 2 0\n");
        let status = Command::new("xz")
            .arg("-z")
            .arg("-k")
            .arg(&cnf)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .expect("run xz");
        assert!(status.success());
        let cnf_xz = cnf.with_extension("cnf.xz");

        let report = check_dimacs_model(&cnf_xz, &stdout);

        assert_eq!(report.model_status, "valid");
        assert_eq!(report.num_vars, Some(2));
        assert_eq!(report.clauses_checked, 2);
        assert_eq!(report.first_unsatisfied_clause, None);
    }

    #[test]
    fn test_check_dimacs_model_rejects_unsatisfied_clause() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cnf = write_fixture(&dir, "invalid.cnf", "p cnf 1 1\n1 0\n");
        let stdout = write_fixture(&dir, "stdout.txt", "s SATISFIABLE\nv -1 0\n");

        let report = check_dimacs_model(&cnf, &stdout);

        assert_eq!(report.model_status, "invalid");
        assert_eq!(report.clauses_checked, 1);
        assert_eq!(report.first_unsatisfied_clause, Some(1));
    }

    #[test]
    fn test_fmla_postcheck_admission_authorizes_imported_learned_lrat_dry_run_artifact() {
        let dir = tempfile::tempdir().expect("tempdir");
        let dry_run_artifact = write_fmla_dry_run_artifact(&dir);
        let proof_out = format!("c retained proof.out\n{}", fmla_dry_run_lrat_fragment());
        let input = fmla_postcheck_input(&dir, &proof_out, Some(dry_run_artifact));

        let outcome = evaluate_fmla_postcheck_admission(&input);

        assert_eq!(
            outcome.status, "committed_checker_backed_admission",
            "{:?}",
            outcome.reason
        );
        assert!(outcome.replay.is_some());
        let authority = outcome
            .learned_lrat_authority
            .expect("dry-run artifact should produce an authority record");
        assert_eq!(authority.status, "authorized");
        assert_eq!(authority.checker_visible_id, Some(10));
        assert!(authority.external_checker_verified);
        assert!(authority.proof_out_contains_lrat_fragment);
        assert!(authority.authorizes_main_proof_out);
    }

    #[test]
    fn test_fmla_postcheck_admission_fail_closes_when_dry_run_fragment_not_in_proof_out() {
        let dir = tempfile::tempdir().expect("tempdir");
        let dry_run_artifact = write_fmla_dry_run_artifact(&dir);
        let input = fmla_postcheck_input(
            &dir,
            "c retained proof.out without imported fragment\n11 0 1 0\n",
            Some(dry_run_artifact),
        );

        let outcome = evaluate_fmla_postcheck_admission(&input);

        assert_eq!(outcome.status, "no_replay", "{:?}", outcome.reason);
        assert_eq!(
            outcome.reason.as_deref(),
            Some("proof_out_missing_dry_run_fragment")
        );
        assert!(outcome.replay.is_none());
        let authority = outcome
            .learned_lrat_authority
            .expect("fail-closed authority record should be retained for reporting");
        assert_eq!(authority.status, "fail_closed");
        assert!(!authority.authorizes_main_proof_out);
    }

    #[test]
    fn test_parse_satcomp_model_matches_matrix_duplicate_assignment_status() {
        let status =
            parse_satcomp_model_reader(b"v 1 1 0\n".as_slice(), 1).expect_err("reject duplicate");

        assert_eq!(status, "duplicate-assignment:1");
    }

    #[test]
    fn test_parse_satcomp_model_matches_matrix_duplicate_terminator_status() {
        let status = parse_satcomp_model_reader(b"v 1 0\nv 0\n".as_slice(), 1)
            .expect_err("reject duplicate");

        assert_eq!(status, "duplicate-terminator:2");
    }
}
