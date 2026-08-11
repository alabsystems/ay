// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Registered semantic validator for the closed Unknown/artifact policy.
//!
//! The validator never trusts the parity process's linked `ay-dpll` as evidence
//! for AY.  It stages the manifest-bound AY executable by hash, invokes the
//! executable's hidden self-test under the standard RSS watchdog, and binds the
//! exact positive and negative-control transcripts into receipt-v2 rows.

use super::*;
use ay_dpll::{UnknownOrigin, UnknownReason};

pub(super) const VALIDATOR_ID: &str = "builtin.unknown-policy.v1";

const REQUIREMENT_ID: &str = "results.unknown-policy.closed-reasons";
const PROBE_SCHEMA: &str = "ay.unknown-policy-probe/v2";
const APPLY_MODE: &str = "publish-origin";
const NEGATIVE_MODE: &str = "retain-negative-control";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct ProbeReport {
    schema: String,
    mode: String,
    registry_codes: Vec<String>,
    registry_origins: Vec<String>,
    passed: bool,
    cases: Vec<ReasonProbe>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct ReasonProbe {
    origin_code: String,
    production_chokepoint: String,
    reason_code: String,
    reason_name: String,
    reason_smtlib: String,
    transition_applied: bool,
    unknown_installed: bool,
    observed_origin_code: Option<String>,
    trigger_kind: String,
    artifact_transition_kind: String,
    fixture_id: String,
    artifacts: ArtifactMatrix,
    policy_satisfied: bool,
    negative_control_detected: bool,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct ArtifactMatrix {
    model: ArtifactObservation,
    proof: ArtifactObservation,
    core: ArtifactObservation,
    assumptions: ArtifactObservation,
    optimum: ArtifactObservation,
}

impl ArtifactMatrix {
    fn observations(&self) -> [&ArtifactObservation; 5] {
        [
            &self.model,
            &self.proof,
            &self.core,
            &self.assumptions,
            &self.optimum,
        ]
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct ArtifactObservation {
    scenario_id: String,
    execution_ordinal: u64,
    available_before: bool,
    revoked_after: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct Execution {
    ay_sha256: String,
    resource_envelope: String,
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

#[derive(Clone, Copy)]
enum RunMode {
    Apply,
    Negative,
}

impl RunMode {
    fn code(self) -> &'static str {
        match self {
            Self::Apply => APPLY_MODE,
            Self::Negative => NEGATIVE_MODE,
        }
    }

    fn case_suffix(self) -> &'static str {
        match self {
            Self::Apply => "revoke",
            Self::Negative => "retain-control",
        }
    }

    fn argv(self) -> &'static [&'static str] {
        match self {
            Self::Apply => &["unknown-policy-probe"],
            Self::Negative => &["unknown-policy-probe", "--negative-control"],
        }
    }

    fn expected_transition(self) -> bool {
        matches!(self, Self::Apply)
    }
}

/// Independent oracle for the production registry exposed by the authenticated
/// AY executable.  Do not derive any string in this table from `UnknownOrigin`
/// or `UnknownReason`: doing so would let the producer and validator drift in
/// lockstep and manufacture a false PASS.
#[derive(Clone, Copy)]
struct ExpectedOrigin {
    origin: UnknownOrigin,
    origin_code: &'static str,
    reason: UnknownReason,
    reason_code: &'static str,
    reason_name: &'static str,
    reason_smtlib: &'static str,
    production_chokepoint: &'static str,
    trigger_kind: &'static str,
    fixture: &'static str,
}

const EXPECTED_ORIGINS: [ExpectedOrigin; 18] = [
    ExpectedOrigin {
        origin: UnknownOrigin::SolveDeadline,
        origin_code: "solve_deadline",
        reason: UnknownReason::Timeout,
        reason_code: "timeout",
        reason_name: "Timeout",
        reason_smtlib: "timeout",
        production_chokepoint: "executor/check_sat.rs::should_abort_theory_loop",
        trigger_kind: "natural-public-query",
        fixture: "natural.check-sat.zero-deadline",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::DeterministicResourceBudget,
        origin_code: "deterministic_resource_budget",
        reason: UnknownReason::ResourceLimit,
        reason_code: "resource_limit",
        reason_name: "Resource limit",
        reason_smtlib: "resourceout",
        production_chokepoint: "executor/theories/model_helpers.rs::record_sat_unknown_reason",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.deterministic-resource-budget.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::MemoryBudget,
        origin_code: "memory_budget",
        reason: UnknownReason::MemoryLimit,
        reason_code: "memory_limit",
        reason_name: "Memory limit",
        reason_smtlib: "memout",
        production_chokepoint: "executor/check_sat.rs::should_abort_theory_loop",
        trigger_kind: "natural-public-query",
        fixture: "natural.check-sat.one-byte-memory-limit",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::InterruptFlag,
        origin_code: "interrupt_flag",
        reason: UnknownReason::Interrupted,
        reason_code: "interrupted",
        reason_name: "Interrupted",
        reason_smtlib: "interrupted",
        production_chokepoint: "executor/check_sat.rs::should_abort_theory_loop",
        trigger_kind: "natural-public-query",
        fixture: "natural.check-sat.pre-set-interrupt",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::IncompleteSolverLane,
        origin_code: "incomplete_solver_lane",
        reason: UnknownReason::Incomplete,
        reason_code: "incomplete",
        reason_name: "Incomplete",
        reason_smtlib: "incomplete",
        production_chokepoint: "executor/check_sat.rs::check_sat_guarded",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.incomplete-solver-lane.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::VerdictCertification,
        origin_code: "verdict_certification",
        reason: UnknownReason::SelfCheckRejected,
        reason_code: "self_check_rejected",
        reason_name: "Self-check REJECTED a computed verdict",
        reason_smtlib: "(incomplete self-check-rejected)",
        production_chokepoint: "executor/unsat_cert.rs::reject_uncertified_verdict_for_publication",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.verdict-certification.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::EmatchingRoundBudget,
        origin_code: "ematching_round_budget",
        reason: UnknownReason::QuantifierRoundLimit,
        reason_code: "quantifier_round_limit",
        reason_name: "Quantifier round limit",
        reason_smtlib: "(incomplete quantifier-round-limit)",
        production_chokepoint: "executor/quantifier_loop/result_mapping.rs::map_quantifier_result",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.ematching-round-budget.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::DeferredInstantiation,
        origin_code: "deferred_instantiation",
        reason: UnknownReason::QuantifierDeferred,
        reason_code: "quantifier_deferred",
        reason_name: "Quantifier deferred",
        reason_smtlib: "(incomplete quantifier-deferred)",
        production_chokepoint: "executor/quantifier_loop/result_mapping.rs::map_quantifier_result",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.deferred-instantiation.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::UnhandledQuantifier,
        origin_code: "unhandled_quantifier",
        reason: UnknownReason::QuantifierUnhandled,
        reason_code: "quantifier_unhandled",
        reason_name: "Quantifier unhandled",
        reason_smtlib: "(incomplete quantifier-unhandled)",
        production_chokepoint: "executor/quantifier_loop/result_mapping.rs::map_quantifier_result",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.unhandled-quantifier.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::CegqiRefinement,
        origin_code: "cegqi_refinement",
        reason: UnknownReason::QuantifierCegqiIncomplete,
        reason_code: "quantifier_cegqi_incomplete",
        reason_name: "Quantifier CEGQI incomplete",
        reason_smtlib: "(incomplete quantifier-cegqi)",
        production_chokepoint:
            "executor/quantifier_loop/cegqi_refinement.rs::try_cegqi_arith_refinement",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.cegqi-refinement.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::ExistentialEmatching,
        origin_code: "existential_ematching",
        reason: UnknownReason::QuantifierEmatchingExistsIncomplete,
        reason_code: "quantifier_ematching_exists_incomplete",
        reason_name: "Quantifier E-matching exists incomplete",
        reason_smtlib: "(incomplete quantifier-ematching-exists)",
        production_chokepoint: "executor/quantifier_loop/result_mapping.rs::map_quantifier_result",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.existential-ematching.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::TheorySplitBudget,
        origin_code: "theory_split_budget",
        reason: UnknownReason::SplitLimit,
        reason_code: "split_limit",
        reason_name: "Split limit",
        reason_smtlib: "incomplete",
        production_chokepoint: "pipeline_incremental_split_assume_macros.rs::split_loop",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.theory-split-budget.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::UnsupportedExpressionSplit,
        origin_code: "unsupported_expression_split",
        reason: UnknownReason::ExpressionSplit,
        reason_code: "expression_split",
        reason_name: "Expression split",
        reason_smtlib: "incomplete",
        production_chokepoint:
            "pipeline_incremental_split_eager_shared_macros.rs::create_expression_split_atoms",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.unsupported-expression-split.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::UnsupportedFeature,
        origin_code: "unsupported_feature",
        reason: UnknownReason::Unsupported,
        reason_code: "unsupported",
        reason_name: "Unsupported",
        reason_smtlib: "unsupported",
        production_chokepoint: "executor.rs::execute_stack_guarded",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.unsupported-feature.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::UnsupportedArithmeticFragment,
        origin_code: "unsupported_arithmetic_fragment",
        reason: UnknownReason::UnsupportedArithmetic,
        reason_code: "unsupported_arithmetic",
        reason_name: "Unsupported arithmetic",
        reason_smtlib: "(unsupported arithmetic)",
        production_chokepoint: "executor/check_sat.rs::contains_symbolic_integer_power",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.unsupported-arithmetic-fragment.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::UnsupportedMixedCollection,
        origin_code: "unsupported_mixed_collection",
        reason: UnknownReason::UnsupportedMixedCollection,
        reason_code: "unsupported_mixed_collection",
        reason_name: "Unsupported mixed collection",
        reason_smtlib: "(unsupported mixed-collection)",
        production_chokepoint: "executor/theories/seq.rs::solve_seq_auflia",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.unsupported-mixed-collection.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::ExecutorFailure,
        origin_code: "executor_failure",
        reason: UnknownReason::InternalError,
        reason_code: "internal_error",
        reason_name: "Internal error",
        reason_smtlib: "internal-error",
        production_chokepoint: "api/solving/check.rs::record_executor_failure_unknown",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.executor-failure.authoritative-publication",
    },
    ExpectedOrigin {
        origin: UnknownOrigin::UntaggedSolverUnknown,
        origin_code: "untagged_solver_unknown",
        reason: UnknownReason::Unknown,
        reason_code: "unknown",
        reason_name: "Unknown",
        reason_smtlib: "unknown",
        production_chokepoint: "executor/lifecycle.rs::finalize_unknown_publication",
        trigger_kind: "authoritative-origin-publication-fault-injection",
        fixture: "fault.untagged-solver-unknown.authoritative-publication",
    },
];

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut ay_override: Option<PathBuf> = None;
    let mut timeout_secs = 10u64;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--receipt" => {
                index += 1;
                receipt_path = Some(PathBuf::from(
                    args.get(index).ok_or("--receipt needs a path")?,
                ));
            }
            "--ay" => {
                index += 1;
                ay_override = Some(PathBuf::from(args.get(index).ok_or("--ay needs a path")?));
            }
            "--timeout" => {
                index += 1;
                timeout_secs = args
                    .get(index)
                    .ok_or("--timeout needs seconds")?
                    .parse()
                    .map_err(|_| "--timeout must be a positive integer")?;
                if timeout_secs == 0 || timeout_secs > 3600 {
                    return Err("--timeout must be between 1 and 3600 seconds".to_string());
                }
            }
            flag if flag.starts_with("--") => {
                return Err(format!("unknown unknown-policy flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("unknown-policy takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }

    let manifest = manifest.ok_or("unknown-policy needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("unknown-policy requires --receipt <path>")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let contract_envelope = loaded
        .contract
        .resource_envelope
        .as_deref()
        .ok_or("unknown-policy requires contract.resource_envelope")?;
    let parsed_envelope = parse_resource_envelope(contract_envelope)?;
    if parsed_envelope.jobs != 1 {
        return Err("unknown-policy requires a one-job resource envelope".to_string());
    }
    if parsed_envelope.timeout != Duration::from_secs(timeout_secs) {
        return Err(format!(
            "--timeout does not match contract.resource_envelope: expected {:?}",
            parsed_envelope.timeout
        ));
    }
    let subject_ay = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("unknown-policy requires subject.ay_executable")?;
    let ay = ay_override.unwrap_or_else(|| artifact_path(&loaded.base, &subject_ay.path));
    let output_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let execution = execute(
        &loaded.contract,
        &ay,
        Duration::from_secs(timeout_secs),
        Some(contract_envelope),
    )?;
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let validator_sha = sha256_file(&current_exe, "parity validator")?;
    let dimension = unknown_dimension(&loaded.contract)?;
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: dimension.id.clone(),
        requirement_ids: vec![REQUIREMENT_ID.to_string()],
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: VALIDATOR_ID.to_string(),
            kind: ValidatorKind::UnknownPolicy,
            path: current_exe.to_string_lossy().into_owned(),
            sha256: validator_sha,
        },
        subject: ReceiptSubject {
            ay_executable_sha256: Some(execution.ay_sha256),
            ay_shared_library_sha256: loaded
                .contract
                .subject
                .ay_shared_library
                .as_ref()
                .map(|artifact| artifact.sha256.clone()),
        },
        z3_binary_sha256: None,
        z3_shared_library_sha256: None,
        reference_inputs: Vec::new(),
        auxiliary_tools: Vec::new(),
        source_provenance: None,
        resource_envelope: Some(execution.resource_envelope),
        exhaustive: true,
        result: execution.result,
        cases: execution.cases,
        case_results: execution.case_results,
    };
    let bytes = pretty_json(&receipt)?;
    atomic_write_new(&receipt_path, &bytes)?;
    let receipt_sha = sha256_bytes(&bytes);
    println!(
        "unknown-policy={} receipt={} sha256={}",
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        output_relative,
        receipt_sha
    );
    println!(
        "attach to {REQUIREMENT_ID}: {{\"path\":\"{output_relative}\",\"sha256\":\"{receipt_sha}\"}}"
    );
    if !report.complete {
        println!(
            "note: the rest of the contract remains incomplete ({} existing blockers)",
            report.blockers.len()
        );
    }
    Ok(i32::from(receipt.result != ValidatorResult::Pass))
}

pub(super) fn validate_and_replay(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    if receipt.validator.kind != ValidatorKind::UnknownPolicy
        || context.dimension.id != "results.unknown-policy"
        || receipt.requirement_ids != [REQUIREMENT_ID.to_string()]
        || !receipt.exhaustive
        || receipt.z3_binary_sha256.is_some()
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.reference_inputs.is_empty()
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
    {
        return Err(format!(
            "{VALIDATOR_ID} has invalid kind, dimension, coverage, exhaustive flag, or foreign bindings"
        ));
    }
    let expected_ids = expected_case_ids();
    let actual_ids = receipt
        .case_results
        .iter()
        .map(|row| row.id.clone())
        .collect::<Vec<_>>();
    if actual_ids != expected_ids {
        return Err(format!(
            "{VALIDATOR_ID} does not contain the exact closed reason/control inventory"
        ));
    }
    validate_receipt_row_shape(&receipt.case_results)?;

    if context.mode.replays_registered_validators() {
        let envelope = receipt
            .resource_envelope
            .as_deref()
            .ok_or("unknown-policy receipt has no resource envelope")?;
        let parsed = parse_resource_envelope(envelope)?;
        if parsed.jobs != 1 {
            return Err("unknown-policy receipts require a one-job resource envelope".to_string());
        }
        let subject = context
            .contract
            .subject
            .ay_executable
            .as_ref()
            .ok_or("unknown-policy replay requires subject.ay_executable")?;
        let ay = artifact_path(context.manifest_dir, &subject.path);
        let live = execute(context.contract, &ay, parsed.timeout, Some(envelope))?;
        if receipt.result != live.result
            || receipt.cases != live.cases
            || receipt.case_results != live.case_results
        {
            return Err(format!(
                "{VALIDATOR_ID} receipt does not match a fresh authenticated executable replay"
            ));
        }
    }
    Ok(())
}

fn execute(
    contract: &Contract,
    ay_source: &Path,
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<Execution, String> {
    if timeout.is_zero() || timeout > Duration::from_secs(3600) {
        return Err("unknown-policy timeout must be between 1ns and 3600 seconds".to_string());
    }
    let subject = contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("unknown-policy requires subject.ay_executable")?;
    let staged = stage_authenticated_executable(ay_source, &subject.sha256, "AY executable")?;
    let repo_root = locate_repo_root()?;
    let resources = PlannedResources::plan(
        &repo_root,
        1,
        "ay-z3-parity smtlib-conformance unknown-policy",
    )
    .map_err(|error| error.to_string())?;
    let resource_envelope = effective_execution_envelope(
        &resources.plan,
        ENFORCEMENT_RSS_WATCHDOG_V1,
        timeout.as_secs_f64(),
    )
    .map_err(|error| error.to_string())?;
    if let Some(expected) = required_envelope {
        if expected != resource_envelope {
            return Err(format!(
                "live unknown-policy replay resource envelope drift: expected {expected:?}, got {resource_envelope:?}"
            ));
        }
    }

    let apply = resources
        .run_external_transcript(
            &staged.path,
            RunMode::Apply.argv().iter().copied(),
            b"",
            timeout,
            "SMT-LIB Unknown policy: positive transition",
        )
        .map_err(|error| error.to_string())?;
    let negative = resources
        .run_external_transcript(
            &staged.path,
            RunMode::Negative.argv().iter().copied(),
            b"",
            timeout,
            "SMT-LIB Unknown policy: retained-artifact negative control",
        )
        .map_err(|error| error.to_string())?;
    let post_sha = sha256_file(&staged.path, "staged AY after Unknown-policy probes")?;
    if post_sha != subject.sha256 {
        return Err("authenticated AY bytes changed during Unknown-policy probes".to_string());
    }

    let mut rows = rows_from_output(RunMode::Apply, apply);
    rows.extend(rows_from_output(RunMode::Negative, negative));
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    if rows.iter().map(|row| row.id.clone()).collect::<Vec<_>>() != expected_case_ids() {
        return Err("internal Unknown-policy case inventory drift".to_string());
    }
    let cases = case_counts_from_rows(&rows)?;
    let result = overall_validator_result(&rows);
    Ok(Execution {
        ay_sha256: subject.sha256.clone(),
        resource_envelope,
        result,
        cases,
        case_results: rows,
    })
}

fn rows_from_output(mode: RunMode, output: GuardedTranscriptOutput) -> Vec<ValidatorCase> {
    let exit_code = output.status.as_ref().and_then(|status| status.code());
    let status_success = output
        .status
        .as_ref()
        .is_some_and(|status| status.success());
    let stdout_valid = String::from_utf8(output.stdout.clone());
    let stderr_valid = String::from_utf8(output.stderr.clone());
    let stdout = stdout_valid.as_ref().map_or_else(
        |error| String::from_utf8_lossy(error.as_bytes()).into_owned(),
        Clone::clone,
    );
    let stderr = stderr_valid.as_ref().map_or_else(
        |error| String::from_utf8_lossy(error.as_bytes()).into_owned(),
        Clone::clone,
    );
    let parsed = stdout_valid
        .as_ref()
        .map_err(|error| format!("stdout is not UTF-8: {error}"))
        .and_then(|text| {
            serde_json::from_str::<ProbeReport>(text.trim_end())
                .map_err(|error| format!("invalid probe JSON: {error}"))
        });
    let process = ProcessObservation {
        stdin_complete: output.stdin_complete,
        timed_out: output.timed_out,
        memout: output.memout,
        stdout_truncated: output.stdout_truncated,
        stderr_truncated: output.stderr_truncated,
    };
    let global_error = validate_report(parsed.as_ref().map_err(String::as_str), mode).err();

    EXPECTED_ORIGINS
        .iter()
        .copied()
        .map(|expected| {
            let probe = parsed.as_ref().ok().and_then(|report| {
                report
                    .cases
                    .iter()
                    .find(|case| case.reason_code == expected.reason_code)
            });
            let case_error = probe
                .ok_or_else(|| format!("missing reason {}", expected.reason_code))
                .and_then(|case| validate_reason_case(case, expected, mode));
            let outcome = if output.memout {
                ValidatorCaseOutcome::Memout
            } else if output.timed_out {
                ValidatorCaseOutcome::Timeout
            } else if !output.stdin_complete
                || output.stdout_truncated
                || output.stderr_truncated
                || stdout_valid.is_err()
                || stderr_valid.is_err()
            {
                ValidatorCaseOutcome::Fail
            } else if !status_success {
                ValidatorCaseOutcome::Crash
            } else if !stderr.is_empty() || global_error.is_some() || case_error.is_err() {
                ValidatorCaseOutcome::Fail
            } else {
                ValidatorCaseOutcome::Pass
            };
            let observed = match (&global_error, case_error) {
                (Some(error), _) => error.clone(),
                (None, Err(error)) => error,
                (None, Ok(())) => format!(
                    "authenticated executable reported exact {} matrix for origin={} reason={}",
                    mode.code(),
                    expected.origin_code,
                    expected.reason_code
                ),
            };
            ValidatorCase {
                id: case_id(expected, mode),
                input_sha256: case_input_sha(expected, mode),
                expected: format!(
                    "authenticated AY {} report covers origin={} reason={} and all five artifact families; exit=0; stderr=empty",
                    mode.code(),
                    expected.origin_code,
                    expected.reason_code
                ),
                observed,
                stdout: Some(stdout.clone()),
                stderr: Some(stderr.clone()),
                exit_code,
                process: Some(process.clone()),
                outcome,
            }
        })
        .collect()
}

fn validate_report(report: Result<&ProbeReport, &str>, mode: RunMode) -> Result<(), String> {
    let report = report.map_err(ToOwned::to_owned)?;
    if EXPECTED_ORIGINS.map(|expected| expected.origin) != UnknownOrigin::ALL
        || EXPECTED_ORIGINS.map(|expected| expected.reason) != UnknownReason::ALL
    {
        return Err("validator's independent closed origin/reason oracle is stale".to_string());
    }
    let expected_codes = EXPECTED_ORIGINS
        .iter()
        .map(|expected| expected.reason_code.to_string())
        .collect::<Vec<_>>();
    let expected_origins = EXPECTED_ORIGINS
        .iter()
        .map(|expected| expected.origin_code.to_string())
        .collect::<Vec<_>>();
    if report.schema != PROBE_SCHEMA
        || report.mode != mode.code()
        || report.registry_codes != expected_codes
        || report.registry_origins != expected_origins
        || report.cases.len() != EXPECTED_ORIGINS.len()
        || !report.passed
    {
        return Err(
            "probe report schema, mode, registry, cardinality, or pass flag drift".to_string(),
        );
    }
    let actual_codes = report
        .cases
        .iter()
        .map(|case| case.reason_code.as_str())
        .collect::<Vec<_>>();
    let oracle_codes = EXPECTED_ORIGINS
        .iter()
        .map(|expected| expected.reason_code)
        .collect::<Vec<_>>();
    if actual_codes != oracle_codes {
        return Err("probe report reason order is not the exact closed registry".to_string());
    }
    let execution_ordinals = report
        .cases
        .iter()
        .flat_map(|case| case.artifacts.observations())
        .map(|artifact| artifact.execution_ordinal)
        .collect::<BTreeSet<_>>();
    let expected_execution_count = (EXPECTED_ORIGINS.len() * 5) as u64;
    if execution_ordinals != (0..expected_execution_count).collect::<BTreeSet<_>>() {
        return Err(
            "probe did not execute one distinct artifact scenario per origin/family".to_string(),
        );
    }
    Ok(())
}

fn validate_reason_case(
    case: &ReasonProbe,
    expected: ExpectedOrigin,
    mode: RunMode,
) -> Result<(), String> {
    if case.reason_code != expected.reason_code
        || case.origin_code != expected.origin_code
        || case.production_chokepoint != expected.production_chokepoint
        || case.reason_name != expected.reason_name
        || case.reason_smtlib != expected.reason_smtlib
        || case.transition_applied != mode.expected_transition()
        || case.fixture_id != format!("{}:{}", expected.fixture, mode.code())
        || case.trigger_kind != expected.trigger_kind
        || case.artifact_transition_kind != "authoritative-origin-publication"
    {
        return Err(format!(
            "reason identity or transition flag drift for {}",
            expected.reason_code
        ));
    }
    if !case
        .artifacts
        .observations()
        .into_iter()
        .all(|artifact| artifact.available_before)
    {
        return Err(format!(
            "one or more artifact families were not established before reason {}",
            expected.reason_code
        ));
    }
    let origin_index = EXPECTED_ORIGINS
        .iter()
        .position(|candidate| candidate.origin_code == expected.origin_code)
        .expect("expected origin comes from the closed oracle");
    for (family_index, (family, artifact)) in ["model", "proof", "core", "assumptions", "optimum"]
        .into_iter()
        .zip(case.artifacts.observations())
        .enumerate()
    {
        let expected_scenario = format!("{}:{}:{}", expected.origin_code, family, mode.code());
        let expected_ordinal = (origin_index * 5 + family_index) as u64;
        if artifact.scenario_id != expected_scenario
            || artifact.execution_ordinal != expected_ordinal
        {
            return Err(format!(
                "artifact scenario identity/ordinal drift for origin={} family={family}",
                expected.origin_code
            ));
        }
    }
    match mode {
        RunMode::Apply
            if case.unknown_installed
                && case.observed_origin_code.as_deref() == Some(expected.origin_code)
                && case.policy_satisfied
                && !case.negative_control_detected
                && case
                    .artifacts
                    .observations()
                    .into_iter()
                    .all(|artifact| artifact.revoked_after) =>
        {
            Ok(())
        }
        RunMode::Negative
            if !case.unknown_installed
                && case.observed_origin_code.is_none()
                && !case.policy_satisfied
                && case.negative_control_detected
                && case
                    .artifacts
                    .observations()
                    .into_iter()
                    .all(|artifact| !artifact.revoked_after) =>
        {
            Ok(())
        }
        _ => Err(format!(
            "artifact revocation/control matrix drift for {} in {} mode",
            expected.reason_code,
            mode.code()
        )),
    }
}

fn validate_receipt_row_shape(rows: &[ValidatorCase]) -> Result<(), String> {
    for mode in [RunMode::Apply, RunMode::Negative] {
        for expected in EXPECTED_ORIGINS {
            let id = case_id(expected, mode);
            let row = rows
                .iter()
                .find(|row| row.id == id)
                .ok_or_else(|| format!("{VALIDATOR_ID} is missing {id}"))?;
            if row.input_sha256 != case_input_sha(expected, mode)
                || row.process.is_none()
                || row.stdout.is_none()
                || row.stderr.is_none()
                || (row.outcome == ValidatorCaseOutcome::Pass
                    && (row.exit_code != Some(0) || row.stderr.as_deref() != Some("")))
            {
                return Err(format!(
                    "{VALIDATOR_ID} row {id} has invalid executable evidence"
                ));
            }
        }
    }
    Ok(())
}

fn case_id(expected: ExpectedOrigin, mode: RunMode) -> String {
    format!(
        "unknown.{}.{}.{}",
        expected.origin_code,
        expected.reason_code,
        mode.case_suffix()
    )
}

fn case_input_sha(expected: ExpectedOrigin, mode: RunMode) -> String {
    sha256_bytes(
        format!(
            "{VALIDATOR_ID}\nmode={}\norigin={}\nreason={}\n",
            mode.code(),
            expected.origin_code,
            expected.reason_code
        )
        .as_bytes(),
    )
}

fn expected_case_ids() -> Vec<String> {
    let mut ids = [RunMode::Apply, RunMode::Negative]
        .into_iter()
        .flat_map(|mode| {
            EXPECTED_ORIGINS
                .into_iter()
                .map(move |expected| case_id(expected, mode))
        })
        .collect::<Vec<_>>();
    ids.sort();
    ids
}

fn unknown_dimension(contract: &Contract) -> Result<&Dimension, String> {
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == "results.unknown-policy")
        .ok_or_else(|| "closed results.unknown-policy dimension is missing".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closed_case_inventory_has_two_cases_per_reason() {
        let ids = expected_case_ids();
        assert_eq!(ids.len(), EXPECTED_ORIGINS.len() * 2);
        assert!(ids.windows(2).all(|pair| pair[0] < pair[1]));
    }

    #[test]
    fn independent_oracle_is_closed_unique_and_has_three_natural_fixtures() {
        assert_eq!(EXPECTED_ORIGINS.len(), 18);
        assert_eq!(
            EXPECTED_ORIGINS
                .iter()
                .map(|expected| expected.origin_code)
                .collect::<BTreeSet<_>>()
                .len(),
            EXPECTED_ORIGINS.len()
        );
        assert_eq!(
            EXPECTED_ORIGINS
                .iter()
                .map(|expected| expected.reason_code)
                .collect::<BTreeSet<_>>()
                .len(),
            EXPECTED_ORIGINS.len()
        );
        assert_eq!(
            EXPECTED_ORIGINS
                .iter()
                .filter(|expected| expected.trigger_kind == "natural-public-query")
                .count(),
            3
        );
        for expected in EXPECTED_ORIGINS {
            assert_eq!(expected.origin.code(), expected.origin_code);
            assert_eq!(expected.origin.reason(), expected.reason);
            assert_eq!(
                expected.origin.production_chokepoint(),
                expected.production_chokepoint
            );
            assert_eq!(expected.reason.code(), expected.reason_code);
            assert_eq!(expected.reason.name(), expected.reason_name);
            assert_eq!(expected.reason.to_string(), expected.reason_smtlib);
        }
    }

    #[test]
    fn negative_matrix_cannot_claim_policy_satisfaction() {
        let expected = EXPECTED_ORIGINS[0];
        let artifact = |family: &str, execution_ordinal| ArtifactObservation {
            scenario_id: format!(
                "{}:{family}:{}",
                expected.origin_code,
                RunMode::Negative.code()
            ),
            execution_ordinal,
            available_before: true,
            revoked_after: false,
        };
        let case = ReasonProbe {
            origin_code: expected.origin_code.to_string(),
            production_chokepoint: expected.production_chokepoint.to_string(),
            reason_code: expected.reason_code.to_string(),
            reason_name: expected.reason_name.to_string(),
            reason_smtlib: expected.reason_smtlib.to_string(),
            transition_applied: false,
            unknown_installed: false,
            observed_origin_code: None,
            trigger_kind: "natural-public-query".to_string(),
            artifact_transition_kind: "authoritative-origin-publication".to_string(),
            fixture_id: format!("{}:{}", expected.fixture, RunMode::Negative.code()),
            artifacts: ArtifactMatrix {
                model: artifact("model", 0),
                proof: artifact("proof", 1),
                core: artifact("core", 2),
                assumptions: artifact("assumptions", 3),
                optimum: artifact("optimum", 4),
            },
            policy_satisfied: true,
            negative_control_detected: true,
        };
        let error = validate_reason_case(&case, expected, RunMode::Negative)
            .expect_err("spoofed negative control must fail");
        assert!(error.contains("matrix drift"));
    }
}
