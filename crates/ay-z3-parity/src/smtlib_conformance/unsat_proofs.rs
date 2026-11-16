// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Registered independent replay gate for SMT-LIB UNSAT proofs.
//!
//! AY's in-process strict checker is a publication precondition, not the
//! independent oracle.  This validator retains the exact Alethe bytes emitted
//! by a hash-authenticated AY executable and replays them against the exact
//! authored problem with a separately staged, commit-pinned Carcara binary.

use super::*;

pub(super) const VALIDATOR_ID: &str = "builtin.unsat-proofs.v1";

const DIMENSION_ID: &str = "results.unsat-proofs";
const REQUIREMENT_ID: &str = "results.unsat-proofs.independent-replay";
pub(super) const CARCARA_ID: &str = "carcara.1.1.0-9a352ee";
const CARCARA_ROLE: &str = "independent strict Alethe proof parser and semantic checker";
// Resolved at runtime: $CARCARA_PATH, else ~/.cargo/bin/carcara. A literal
// developer home path here is forbidden content for the public export.
const CARCARA_DEFAULT_RELATIVE: &str = ".cargo/bin/carcara";
const MAX_RETAINED_PROOF_BYTES: u64 = 1024 * 1024;

const FOREIGN_PROBLEM: &str = "(set-logic QF_UF)\n\
(declare-const foreign Bool)\n\
(assert foreign)\n\
(check-sat)\n";

#[derive(Clone, Copy)]
struct Fixture {
    id: &'static str,
    problem: &'static str,
    expected_stdout: &'static str,
}

const FIXTURES: [Fixture; 8] = [
    Fixture {
        id: "bool-contradiction",
        problem: "(set-logic QF_UF)\n\
(declare-const p Bool)\n\
(assert p)\n\
(assert (not p))\n\
(check-sat)\n",
        expected_stdout: "unsat\n",
    },
    Fixture {
        id: "uf-transitivity",
        problem: "(set-logic QF_UF)\n\
(declare-sort U 0)\n\
(declare-const a U)\n\
(declare-const b U)\n\
(declare-const c U)\n\
(assert (= a b))\n\
(assert (= b c))\n\
(assert (not (= a c)))\n\
(check-sat)\n",
        expected_stdout: "unsat\n",
    },
    Fixture {
        id: "lia-bounds",
        problem: "(set-logic QF_LIA)\n\
(declare-const x Int)\n\
(assert (<= x 5))\n\
(assert (>= x 10))\n\
(check-sat)\n",
        expected_stdout: "unsat\n",
    },
    Fixture {
        id: "lra-bounds",
        problem: "(set-logic QF_LRA)\n\
(declare-const x Real)\n\
(assert (<= x 5))\n\
(assert (>= x 10))\n\
(check-sat)\n",
        expected_stdout: "unsat\n",
    },
    Fixture {
        id: "check-sat-assuming",
        problem: "(set-logic QF_UF)\n\
(declare-const p Bool)\n\
(assert p)\n\
(check-sat-assuming ((not p)))\n",
        expected_stdout: "unsat\n",
    },
    Fixture {
        id: "incremental-push",
        problem: "(set-logic QF_UF)\n\
(declare-const p Bool)\n\
(declare-const q Bool)\n\
(assert (or p q))\n\
(check-sat)\n\
(push 1)\n\
(assert (not p))\n\
(assert (not q))\n\
(check-sat)\n",
        expected_stdout: "sat\nunsat\n",
    },
    Fixture {
        id: "incremental-pop-new-epoch",
        problem: "(set-logic QF_UF)\n\
(declare-const p Bool)\n\
(push 1)\n\
(assert p)\n\
(check-sat)\n\
(pop 1)\n\
(push 1)\n\
(assert p)\n\
(assert (not p))\n\
(check-sat)\n",
        expected_stdout: "sat\nunsat\n",
    },
    Fixture {
        id: "reset-new-epoch",
        problem: "(set-logic QF_UF)\n\
(declare-const old Bool)\n\
(assert old)\n\
(check-sat)\n\
(reset)\n\
(set-logic QF_UF)\n\
(declare-const fresh Bool)\n\
(assert fresh)\n\
(assert (not fresh))\n\
(check-sat)\n",
        expected_stdout: "sat\nunsat\n",
    },
];

#[derive(Debug, Eq, PartialEq)]
struct Execution {
    ay_sha256: String,
    carcara_sha256: String,
    carcara_version: String,
    resource_envelope: String,
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

#[derive(Clone)]
struct CapturedProcess {
    stdout: String,
    stderr: String,
    stdout_valid: bool,
    stderr_valid: bool,
    exit_code: Option<i32>,
    success: bool,
    process: ProcessObservation,
}

struct FixtureOutput {
    rows: Vec<ValidatorCase>,
    proof: Option<Vec<u8>>,
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut ay_override: Option<PathBuf> = None;
    let mut carcara = std::env::var_os("CARCARA_PATH")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| PathBuf::from(home).join(CARCARA_DEFAULT_RELATIVE))
        })
        .unwrap_or_else(|| PathBuf::from(CARCARA_DEFAULT_RELATIVE));
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
            "--carcara" => {
                index += 1;
                carcara = PathBuf::from(args.get(index).ok_or("--carcara needs a path")?);
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
                return Err(format!("unknown unsat-proofs flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("unsat-proofs takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }

    let manifest = manifest.ok_or("unsat-proofs needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("unsat-proofs requires --receipt <path>")?;
    if fs::symlink_metadata(&receipt_path).is_ok() {
        return Err(format!(
            "refusing to overwrite existing receipt {}",
            receipt_path.display()
        ));
    }
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let contract_envelope = loaded
        .contract
        .resource_envelope
        .as_deref()
        .ok_or("unsat-proofs requires contract.resource_envelope")?;
    let parsed_envelope = parse_resource_envelope(contract_envelope)?;
    if parsed_envelope.jobs != 1 {
        return Err("unsat-proofs requires a one-job resource envelope".to_string());
    }
    if parsed_envelope.timeout != Duration::from_secs(timeout_secs) {
        return Err(format!(
            "--timeout does not match contract.resource_envelope: expected {:?}",
            parsed_envelope.timeout
        ));
    }
    let subject = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("unsat-proofs requires subject.ay_executable")?;
    let ay = ay_override.unwrap_or_else(|| artifact_path(&loaded.base, &subject.path));
    let checker_artifact = retain_carcara(&carcara, &loaded.base, &receipt_path)?;
    let retained_carcara = artifact_path(&loaded.base, &checker_artifact.path);
    let output_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let execution = execute(
        &loaded.contract,
        &ay,
        &retained_carcara,
        Duration::from_secs(timeout_secs),
        Some(contract_envelope),
    )?;
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let validator_sha = sha256_file(&current_exe, "parity validator")?;
    let dimension = proof_dimension(&loaded.contract)?;
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
            kind: ValidatorKind::IndependentProofChecker,
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
        auxiliary_tools: vec![AuxiliaryTool {
            id: CARCARA_ID.to_string(),
            role: CARCARA_ROLE.to_string(),
            artifact: checker_artifact,
            version_output: execution.carcara_version,
        }],
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
        "unsat-proofs={} receipt={} sha256={} carcara_sha256={}",
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        output_relative,
        receipt_sha,
        execution.carcara_sha256
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
    if receipt.validator.kind != ValidatorKind::IndependentProofChecker
        || context.dimension.id != DIMENSION_ID
        || receipt.requirement_ids != [REQUIREMENT_ID.to_string()]
        || !receipt.exhaustive
        || receipt.z3_binary_sha256.is_some()
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.reference_inputs.is_empty()
        || receipt.source_provenance.is_some()
        || receipt.auxiliary_tools.len() != 1
    {
        return Err(format!(
            "{VALIDATOR_ID} has invalid kind, dimension, coverage, exhaustive flag, or foreign bindings"
        ));
    }
    let tool = &receipt.auxiliary_tools[0];
    if tool.id != CARCARA_ID
        || tool.role != CARCARA_ROLE
        || checker_cohort::version_for_sha(&tool.artifact.sha256)
            != Some(tool.version_output.as_str())
    {
        return Err(format!(
            "{VALIDATOR_ID} is not bound to the exact pinned Carcara checker"
        ));
    }
    validate_receipt_rows(&receipt.case_results, &tool.artifact.sha256)?;

    if context.mode.replays_registered_validators() {
        let envelope = receipt
            .resource_envelope
            .as_deref()
            .ok_or("unsat-proofs receipt has no resource envelope")?;
        let parsed = parse_resource_envelope(envelope)?;
        if parsed.jobs != 1 {
            return Err("unsat-proofs receipts require a one-job resource envelope".to_string());
        }
        let subject = context
            .contract
            .subject
            .ay_executable
            .as_ref()
            .ok_or("unsat-proofs replay requires subject.ay_executable")?;
        let ay = artifact_path(context.manifest_dir, &subject.path);
        let carcara = resolve_relative_evidence_path(context.manifest_dir, &tool.artifact.path)?;
        let live = execute(
            context.contract,
            &ay,
            &carcara,
            parsed.timeout,
            Some(envelope),
        )?;
        if receipt.result != live.result
            || receipt.cases != live.cases
            || receipt.case_results != live.case_results
            || live.carcara_sha256 != tool.artifact.sha256
            || live.carcara_version != tool.version_output
        {
            return Err(format!(
                "{VALIDATOR_ID} receipt does not match a fresh authenticated AY/Carcara replay"
            ));
        }
    }
    Ok(())
}

fn retain_carcara(source: &Path, base: &Path, receipt_path: &Path) -> Result<Artifact, String> {
    let identity = checker_cohort::authenticate(source)?;
    let source_sha = identity.sha256;
    let bytes = read_bounded_bytes(source, 16 * 1024 * 1024, "pinned Carcara executable", true)?;
    let parent = receipt_path
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let retained = parent.join(format!("carcara-1.1.0-9a352ee-{source_sha}.bin"));
    match fs::symlink_metadata(&retained) {
        Ok(metadata) => {
            if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
                return Err(format!(
                    "retained Carcara artifact is not a non-symlink regular file: {}",
                    retained.display()
                ));
            }
            let actual = sha256_file(&retained, "retained Carcara artifact")?;
            if actual != source_sha {
                return Err(format!(
                    "retained Carcara artifact hash mismatch at {}",
                    retained.display()
                ));
            }
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            atomic_write_new(&retained, &bytes)?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt as _;
                fs::set_permissions(&retained, fs::Permissions::from_mode(0o500)).map_err(
                    |error| {
                        format!(
                            "securing retained Carcara artifact {}: {error}",
                            retained.display()
                        )
                    },
                )?;
            }
        }
        Err(error) => {
            return Err(format!(
                "inspecting retained Carcara artifact {}: {error}",
                retained.display()
            ));
        }
    }
    let relative = future_relative_output(base, &retained)?;
    Ok(Artifact {
        path: relative,
        sha256: source_sha,
    })
}

fn execute(
    contract: &Contract,
    ay_source: &Path,
    carcara_source: &Path,
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<Execution, String> {
    if timeout.is_zero() || timeout > Duration::from_hours(1) {
        return Err("unsat-proofs timeout must be between 1ns and 3600 seconds".to_string());
    }
    let subject = contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("unsat-proofs requires subject.ay_executable")?;
    let staged_ay = stage_authenticated_executable(ay_source, &subject.sha256, "AY executable")?;
    let checker_identity = checker_cohort::authenticate(carcara_source)?;
    let staged_carcara = stage_authenticated_executable(
        carcara_source,
        &checker_identity.sha256,
        "Carcara executable",
    )?;
    let repo_root = locate_repo_root()?;
    let resources = PlannedResources::plan(
        &repo_root,
        1,
        "ay-z3-parity smtlib-conformance unsat-proofs",
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
                "live unsat-proofs replay resource envelope drift: expected {expected:?}, got {resource_envelope:?}"
            ));
        }
    }

    let work = tempfile::Builder::new()
        .prefix("ay-unsat-proof-gate-")
        .tempdir()
        .map_err(|error| format!("creating UNSAT proof gate directory: {error}"))?;
    let version_output = resources
        .run_external_transcript_scrubbed(
            &staged_carcara.path,
            ["--version"],
            b"",
            timeout,
            "UNSAT proof gate: Carcara identity",
        )
        .map_err(|error| error.to_string())?;
    let mut rows = vec![version_row(
        capture(version_output),
        &checker_identity.sha256,
        checker_identity.expected_version,
    )];
    let mut first_proof: Option<Vec<u8>> = None;

    for fixture in FIXTURES {
        let output = execute_fixture(
            fixture,
            work.path(),
            &staged_ay.path,
            &staged_carcara.path,
            &resources,
            timeout,
        )?;
        if first_proof.is_none() && fixture.id == FIXTURES[0].id {
            first_proof = output.proof.clone();
        }
        rows.extend(output.rows);
    }
    rows.extend(control_rows(
        first_proof.as_deref(),
        work.path(),
        &staged_carcara.path,
        &resources,
        timeout,
    )?);
    let diagnostic_paths = current_abi::StagingPaths::new(&[
        (work.path(), "@UNSAT_FIXTURES@"),
        (
            staged_ay.path.parent().ok_or("AY staging root missing")?,
            "@UNSAT_AY@",
        ),
        (
            staged_carcara
                .path
                .parent()
                .ok_or("Carcara staging root missing")?,
            "@UNSAT_CARCARA@",
        ),
    ])?;
    normalize_diagnostic_rows(&mut rows, &diagnostic_paths)?;
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    if rows.iter().map(|row| row.id.clone()).collect::<Vec<_>>() != expected_case_ids() {
        return Err("internal UNSAT-proof case inventory drift".to_string());
    }
    let ay_after = sha256_file(&staged_ay.path, "staged AY after proof gate")?;
    if ay_after != subject.sha256 {
        return Err("authenticated AY bytes changed during UNSAT proof gate".to_string());
    }
    let carcara_after = sha256_file(&staged_carcara.path, "staged Carcara after proof gate")?;
    if carcara_after != checker_identity.sha256 {
        return Err("authenticated Carcara bytes changed during UNSAT proof gate".to_string());
    }
    let cases = case_counts_from_rows(&rows)?;
    let result = overall_validator_result(&rows);
    Ok(Execution {
        ay_sha256: subject.sha256.clone(),
        carcara_sha256: carcara_after,
        carcara_version: checker_identity.expected_version.to_string(),
        resource_envelope,
        result,
        cases,
        case_results: rows,
    })
}

/// Verdicts and strictness are computed from original outputs before this is
/// called. Retain nonempty diagnostics and all semantic values, replacing
/// only known owned locations so replay need not reproduce a random tempdir.
/// Alethe bytes and all proof/problem bindings are deliberately untouched.
fn normalize_diagnostic_rows(
    rows: &mut [ValidatorCase],
    paths: &current_abi::StagingPaths,
) -> Result<(), String> {
    for row in rows {
        #[expect(
            clippy::case_sensitive_file_extension_comparisons,
            reason = ".proof is an exact row-ID schema token, not a filesystem extension"
        )]
        if row.id.starts_with("fixture.") && row.id.ends_with(".proof") {
            continue;
        }
        let normalized_control_prefix = if matches!(
            row.id.as_str(),
            "control.corrupt-proof" | "control.foreign-problem"
        ) {
            row.stderr
                .as_ref()
                .map(|stderr| {
                    let suffix = format!(";stderr-sha256={}", sha256_bytes(stderr.as_bytes()));
                    row.observed
                        .strip_suffix(&suffix)
                        .map(str::to_string)
                        .ok_or_else(|| {
                            "negative-control diagnostic digest does not bind original stderr"
                                .to_string()
                        })
                })
                .transpose()?
        } else {
            None
        };
        if let Some(stdout) = &mut row.stdout {
            *stdout = paths.normalize(stdout);
        }
        if let Some(stderr) = &mut row.stderr {
            *stderr = paths.normalize(stderr);
        }
        row.observed = if let Some(prefix) = normalized_control_prefix {
            format!(
                "{};stderr-sha256={}",
                paths.normalize(&prefix),
                sha256_bytes(row.stderr.as_deref().unwrap_or_default().as_bytes())
            )
        } else {
            paths.normalize(&row.observed)
        };
    }
    Ok(())
}

fn execute_fixture(
    fixture: Fixture,
    work: &Path,
    ay: &Path,
    carcara: &Path,
    resources: &PlannedResources,
    timeout: Duration,
) -> Result<FixtureOutput, String> {
    let problem_path = work.join(format!("{}.smt2", fixture.id));
    let proof_path = work.join(format!("{}.alethe", fixture.id));
    fs::write(&problem_path, fixture.problem.as_bytes()).map_err(|error| {
        format!(
            "writing authored proof fixture {}: {error}",
            problem_path.display()
        )
    })?;
    let memory = resources.plan.memlimit_mb_per_child.to_string();
    let ay_args = vec![
        std::ffi::OsString::from("--quiet"),
        std::ffi::OsString::from("--strict-proofs"),
        std::ffi::OsString::from("--self-check"),
        std::ffi::OsString::from("--proof"),
        proof_path.as_os_str().to_owned(),
        std::ffi::OsString::from("--memory"),
        std::ffi::OsString::from(memory),
        problem_path.as_os_str().to_owned(),
    ];
    let output = resources
        .run_external_transcript_scrubbed_with_file_limit(
            ay,
            &ay_args,
            b"",
            timeout,
            &format!("UNSAT proof gate: AY fixture {}", fixture.id),
            MAX_RETAINED_PROOF_BYTES,
        )
        .map_err(|error| error.to_string())?;
    let captured = capture(output);
    let proof = read_bounded_bytes(
        &proof_path,
        MAX_RETAINED_PROOF_BYTES,
        &format!("{} Alethe proof", fixture.id),
        true,
    )
    .ok();
    let ay_row = ay_fixture_row(fixture, &captured, proof.as_deref());
    let proof_row = proof_fixture_row(fixture, &captured, proof.as_deref());
    let checker_row = if let Some(proof) = proof.as_deref() {
        let checker = run_carcara(
            carcara,
            &proof_path,
            &problem_path,
            resources,
            timeout,
            &format!("UNSAT proof gate: Carcara fixture {}", fixture.id),
        )?;
        checker_fixture_row(fixture, proof, capture(checker))
    } else {
        unavailable_checker_row(fixture, ay_row.outcome)
    };
    Ok(FixtureOutput {
        rows: vec![ay_row, proof_row, checker_row],
        proof,
    })
}

fn run_carcara(
    carcara: &Path,
    proof: &Path,
    problem: &Path,
    resources: &PlannedResources,
    timeout: Duration,
    label: &str,
) -> Result<GuardedTranscriptOutput, String> {
    let args = vec![
        std::ffi::OsString::from("check"),
        std::ffi::OsString::from("--strict-parsing"),
        std::ffi::OsString::from("--expand-let-bindings"),
        std::ffi::OsString::from("--"),
        proof.as_os_str().to_owned(),
        problem.as_os_str().to_owned(),
    ];
    resources
        .run_external_transcript_scrubbed(carcara, &args, b"", timeout, label)
        .map_err(|error| error.to_string())
}

fn control_rows(
    proof: Option<&[u8]>,
    work: &Path,
    carcara: &Path,
    resources: &PlannedResources,
    timeout: Duration,
) -> Result<Vec<ValidatorCase>, String> {
    let Some(proof) = proof else {
        return Ok(vec![
            unavailable_control_row("control.corrupt-proof", "source proof unavailable"),
            unavailable_control_row("control.foreign-problem", "source proof unavailable"),
        ]);
    };
    let corrupted = corrupt_first_rule(proof)?;
    let corrupt_proof_path = work.join("control-corrupt.alethe");
    let exact_problem_path = work.join("control-exact.smt2");
    fs::write(&corrupt_proof_path, &corrupted)
        .map_err(|error| format!("writing corrupted proof control: {error}"))?;
    fs::write(&exact_problem_path, FIXTURES[0].problem.as_bytes())
        .map_err(|error| format!("writing exact problem control: {error}"))?;
    let corrupt_output = run_carcara(
        carcara,
        &corrupt_proof_path,
        &exact_problem_path,
        resources,
        timeout,
        "UNSAT proof gate: corrupted-proof negative control",
    )?;

    let exact_proof_path = work.join("control-exact.alethe");
    let foreign_problem_path = work.join("control-foreign.smt2");
    fs::write(&exact_proof_path, proof)
        .map_err(|error| format!("writing exact proof control: {error}"))?;
    fs::write(&foreign_problem_path, FOREIGN_PROBLEM.as_bytes())
        .map_err(|error| format!("writing foreign problem control: {error}"))?;
    let foreign_output = run_carcara(
        carcara,
        &exact_proof_path,
        &foreign_problem_path,
        resources,
        timeout,
        "UNSAT proof gate: foreign-problem negative control",
    )?;
    Ok(vec![
        rejection_control_row(
            "control.corrupt-proof",
            FIXTURES[0].problem.as_bytes(),
            &corrupted,
            capture(corrupt_output),
            "strict Carcara rejects a deterministic unknown-rule mutation of an otherwise valid proof",
        ),
        rejection_control_row(
            "control.foreign-problem",
            FOREIGN_PROBLEM.as_bytes(),
            proof,
            capture(foreign_output),
            "strict Carcara rejects the valid proof when replayed against a foreign authored problem",
        ),
    ])
}

fn capture(output: GuardedTranscriptOutput) -> CapturedProcess {
    let success = output
        .status
        .as_ref()
        .is_some_and(|status| status.success());
    let exit_code = output.status.as_ref().and_then(|status| status.code());
    let stdout_result = String::from_utf8(output.stdout);
    let stderr_result = String::from_utf8(output.stderr);
    let (stdout, stdout_valid) = match stdout_result {
        Ok(value) => (value, true),
        Err(error) => (
            String::from_utf8_lossy(error.as_bytes()).into_owned(),
            false,
        ),
    };
    let (stderr, stderr_valid) = match stderr_result {
        Ok(value) => (value, true),
        Err(error) => (
            String::from_utf8_lossy(error.as_bytes()).into_owned(),
            false,
        ),
    };
    CapturedProcess {
        stdout,
        stderr,
        stdout_valid,
        stderr_valid,
        exit_code,
        success,
        process: ProcessObservation {
            stdin_complete: output.stdin_complete,
            timed_out: output.timed_out,
            memout: output.memout,
            stdout_truncated: output.stdout_truncated,
            stderr_truncated: output.stderr_truncated,
        },
    }
}

fn process_failure(capture: &CapturedProcess) -> Option<ValidatorCaseOutcome> {
    if capture.process.memout {
        Some(ValidatorCaseOutcome::Memout)
    } else if capture.process.timed_out {
        Some(ValidatorCaseOutcome::Timeout)
    } else if !capture.process.stdin_complete
        || capture.process.stdout_truncated
        || capture.process.stderr_truncated
        || !capture.stdout_valid
        || !capture.stderr_valid
    {
        Some(ValidatorCaseOutcome::Fail)
    } else if capture.exit_code.is_none() {
        Some(ValidatorCaseOutcome::Crash)
    } else {
        None
    }
}

fn version_row(capture: CapturedProcess, checker_sha: &str, version: &str) -> ValidatorCase {
    let expected_stdout = format!("{version}\n");
    let outcome = process_failure(&capture).unwrap_or_else(|| {
        if capture.success && capture.stdout == expected_stdout && capture.stderr.is_empty() {
            ValidatorCaseOutcome::Pass
        } else {
            ValidatorCaseOutcome::Fail
        }
    });
    ValidatorCase {
        id: "carcara.identity".to_string(),
        input_sha256: checker_identity_input_sha(checker_sha, version),
        expected: format!(
            "authenticated checker sha256={checker_sha}; --version stdout={version:?}; stderr-empty; exit=0"
        ),
        observed: process_observed(&capture),
        stdout: Some(capture.stdout),
        stderr: Some(capture.stderr),
        exit_code: capture.exit_code,
        process: Some(capture.process),
        outcome,
    }
}

fn ay_fixture_row(
    fixture: Fixture,
    capture: &CapturedProcess,
    proof: Option<&[u8]>,
) -> ValidatorCase {
    let proof_sha = proof.map(sha256_bytes);
    let outcome = process_failure(capture).unwrap_or_else(|| {
        if capture.stdout.lines().any(|line| line == "unknown") {
            ValidatorCaseOutcome::Unknown
        } else if !capture.success {
            ValidatorCaseOutcome::Crash
        } else if capture.success
            && capture.stdout == fixture.expected_stdout
            && capture.stderr.is_empty()
            && proof.is_some()
        {
            ValidatorCaseOutcome::Pass
        } else {
            ValidatorCaseOutcome::Fail
        }
    });
    ValidatorCase {
        id: format!("fixture.{}.ay", fixture.id),
        input_sha256: sha256_bytes(fixture.problem.as_bytes()),
        expected: format!(
            "hash-authenticated AY --quiet --strict-proofs --self-check --proof --memory; exact authored stdout={:?}; stderr-empty; exit=0; nonempty proof",
            fixture.expected_stdout
        ),
        observed: format!(
            "{};stdout-match={};stderr-empty={};proof-sha256={}",
            process_observed(capture),
            capture.stdout == fixture.expected_stdout,
            capture.stderr.is_empty(),
            proof_sha.as_deref().unwrap_or("missing")
        ),
        stdout: Some(capture.stdout.clone()),
        stderr: Some(capture.stderr.clone()),
        exit_code: capture.exit_code,
        process: Some(capture.process.clone()),
        outcome,
    }
}

fn proof_fixture_row(
    fixture: Fixture,
    capture: &CapturedProcess,
    proof: Option<&[u8]>,
) -> ValidatorCase {
    let analysis = proof.map(analyze_proof);
    let process_outcome = process_failure(capture);
    let (proof_text, proof_sha, proof_ok, detail) = match analysis {
        Some(Ok(analysis)) => (
            Some(analysis.text),
            analysis.sha256,
            analysis.strict,
            format!(
                "bytes={};empty-clause={};hole-free={};trust-free={}",
                analysis.bytes, analysis.empty_clause, analysis.hole_free, analysis.trust_free
            ),
        ),
        Some(Err(error)) => (
            proof.map(|bytes| String::from_utf8_lossy(bytes).into_owned()),
            proof.map_or_else(|| missing_proof_sha(fixture), sha256_bytes),
            false,
            format!("invalid={}", sha256_bytes(error.as_bytes())),
        ),
        None => (
            None,
            missing_proof_sha(fixture),
            false,
            "missing=true".to_string(),
        ),
    };
    let outcome = process_outcome.unwrap_or(if !capture.success {
        ValidatorCaseOutcome::Crash
    } else if proof_ok {
        ValidatorCaseOutcome::Pass
    } else {
        ValidatorCaseOutcome::Fail
    });
    ValidatorCase {
        id: format!("fixture.{}.proof", fixture.id),
        input_sha256: proof_binding_sha(fixture.problem.as_bytes(), &proof_sha),
        expected: "exact retained UTF-8 Alethe artifact is nonempty, ends in an empty-clause derivation, contains no hole/trust rule, and is bound to the authored problem".to_string(),
        observed: format!("proof-sha256={proof_sha};{detail}"),
        stdout: proof_text,
        stderr: None,
        exit_code: capture.exit_code,
        process: Some(capture.process.clone()),
        outcome,
    }
}

struct ProofAnalysis {
    text: String,
    sha256: String,
    bytes: usize,
    empty_clause: bool,
    hole_free: bool,
    trust_free: bool,
    strict: bool,
}

fn analyze_proof(proof: &[u8]) -> Result<ProofAnalysis, String> {
    let text = String::from_utf8(proof.to_vec())
        .map_err(|error| format!("Alethe proof is not UTF-8: {error}"))?;
    let empty_clause = text.contains("(cl)");
    let hole_free = !text.contains(":rule hole");
    let trust_free = !text.contains(":rule trust");
    let strict = !text.trim().is_empty() && empty_clause && hole_free && trust_free;
    Ok(ProofAnalysis {
        text,
        sha256: sha256_bytes(proof),
        bytes: proof.len(),
        empty_clause,
        hole_free,
        trust_free,
        strict,
    })
}

/// `Ok` when pinned Carcara's verdict on the pair can count at all: no
/// `evaluate` or `aci_simp` step it misjudges and no binder it misreads
/// (`ay_core::pinned_carcara`, the scan every Carcara gate shares). On such a
/// pair its `valid` is not evidence, so the fixture fails. A proof that is not
/// UTF-8 cannot be scanned and fails closed.
pub(super) fn pinned_carcara_can_judge(problem: &str, proof: &[u8]) -> Result<(), String> {
    let proof = std::str::from_utf8(proof).map_err(|_| "proof-not-utf8".to_string())?;
    ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof).map_err(|misjudged| {
        format!(
            "pinned-carcara-misjudged-aci-simp-steps={};\
             pinned-carcara-misjudged-evaluate-steps={};pinned-carcara-misread-binders={}",
            misjudged.aci_simp_steps.len(),
            misjudged.evaluate_steps.len(),
            misjudged.binders.len()
        )
    })
}

fn checker_fixture_row(fixture: Fixture, proof: &[u8], capture: CapturedProcess) -> ValidatorCase {
    let proof_sha = sha256_bytes(proof);
    let judgeable = pinned_carcara_can_judge(fixture.problem, proof);
    let outcome = process_failure(&capture).unwrap_or_else(|| {
        if capture.success
            && capture.stdout == "valid\n"
            && capture.stderr.is_empty()
            && judgeable.is_ok()
        {
            ValidatorCaseOutcome::Pass
        } else {
            ValidatorCaseOutcome::Fail
        }
    });
    ValidatorCase {
        id: format!("fixture.{}.carcara", fixture.id),
        input_sha256: checker_binding_sha(fixture.problem.as_bytes(), &proof_sha),
        expected: "pinned Carcara check --strict-parsing --expand-let-bindings over exact proof and exact authored problem; stdout=valid; stderr-empty; exit=0; no allowed or ignored rules; no evaluate step or binder pinned Carcara misjudges".to_string(),
        observed: format!(
            "{};problem-sha256={};proof-sha256={proof_sha};strict-verdict={}{}",
            process_observed(&capture),
            sha256_bytes(fixture.problem.as_bytes()),
            capture.stdout.trim_end(),
            judgeable.err().map(|refusal| format!(";{refusal}")).unwrap_or_default()
        ),
        stdout: Some(capture.stdout),
        stderr: Some(capture.stderr),
        exit_code: capture.exit_code,
        process: Some(capture.process),
        outcome,
    }
}

fn unavailable_checker_row(fixture: Fixture, upstream: ValidatorCaseOutcome) -> ValidatorCase {
    ValidatorCase {
        id: format!("fixture.{}.carcara", fixture.id),
        input_sha256: checker_binding_sha(fixture.problem.as_bytes(), &missing_proof_sha(fixture)),
        expected: "pinned Carcara strict replay requires the exact emitted proof".to_string(),
        observed: "proof-unavailable".to_string(),
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome: if matches!(
            upstream,
            ValidatorCaseOutcome::Timeout
                | ValidatorCaseOutcome::Memout
                | ValidatorCaseOutcome::Unknown
        ) {
            upstream
        } else {
            ValidatorCaseOutcome::Unavailable
        },
    }
}

fn rejection_control_row(
    id: &str,
    problem: &[u8],
    proof: &[u8],
    capture: CapturedProcess,
    expectation: &str,
) -> ValidatorCase {
    let proof_sha = sha256_bytes(proof);
    let outcome = process_failure(&capture).unwrap_or_else(|| {
        if !capture.success && capture.exit_code == Some(1) && capture.stdout == "invalid\n" {
            ValidatorCaseOutcome::Pass
        } else {
            ValidatorCaseOutcome::Fail
        }
    });
    ValidatorCase {
        id: id.to_string(),
        input_sha256: checker_binding_sha(problem, &proof_sha),
        expected: format!("{expectation}; stdout=invalid; exit=1; guarded strict checker"),
        observed: format!(
            "{};problem-sha256={};proof-sha256={proof_sha};stderr-sha256={}",
            process_observed(&capture),
            sha256_bytes(problem),
            sha256_bytes(capture.stderr.as_bytes())
        ),
        stdout: Some(capture.stdout),
        stderr: Some(capture.stderr),
        exit_code: capture.exit_code,
        process: Some(capture.process),
        outcome,
    }
}

fn unavailable_control_row(id: &str, reason: &str) -> ValidatorCase {
    ValidatorCase {
        id: id.to_string(),
        input_sha256: sha256_bytes(format!("{VALIDATOR_ID}\n{id}\nmissing\n").as_bytes()),
        expected: "negative checker control must execute and be rejected".to_string(),
        observed: reason.to_string(),
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome: ValidatorCaseOutcome::Unavailable,
    }
}

fn process_observed(capture: &CapturedProcess) -> String {
    format!(
        "exit={:?};success={};stdin-complete={};timeout={};memout={};stdout-truncated={};stderr-truncated={};stdout-utf8={};stderr-utf8={}",
        capture.exit_code,
        capture.success,
        capture.process.stdin_complete,
        capture.process.timed_out,
        capture.process.memout,
        capture.process.stdout_truncated,
        capture.process.stderr_truncated,
        capture.stdout_valid,
        capture.stderr_valid
    )
}

fn corrupt_first_rule(proof: &[u8]) -> Result<Vec<u8>, String> {
    let text = std::str::from_utf8(proof)
        .map_err(|error| format!("cannot corrupt non-UTF-8 proof: {error}"))?;
    let marker = ":rule ";
    let start = text
        .find(marker)
        .map(|index| index + marker.len())
        .ok_or("proof negative control found no :rule token")?;
    let end = text[start..]
        .find(|character: char| character.is_whitespace() || character == ')')
        .map(|offset| start + offset)
        .ok_or("proof negative control found unterminated rule token")?;
    let mut corrupted = String::with_capacity(text.len() + 32);
    corrupted.push_str(&text[..start]);
    corrupted.push_str("__ay_corrupted_rule__");
    corrupted.push_str(&text[end..]);
    if corrupted.as_bytes() == proof {
        return Err("proof negative-control mutation was a no-op".to_string());
    }
    Ok(corrupted.into_bytes())
}

fn checker_identity_input_sha(checker_sha: &str, version: &str) -> String {
    sha256_bytes(
        format!("{VALIDATOR_ID}\nchecker={checker_sha}\nargv=--version\nexpected={version}\n")
            .as_bytes(),
    )
}

fn proof_binding_sha(problem: &[u8], proof_sha: &str) -> String {
    sha256_bytes(
        format!(
            "{VALIDATOR_ID}\nartifact=alethe\nproblem-sha256={}\nproof-sha256={proof_sha}\n",
            sha256_bytes(problem)
        )
        .as_bytes(),
    )
}

fn checker_binding_sha(problem: &[u8], proof_sha: &str) -> String {
    sha256_bytes(
        format!(
            "{VALIDATOR_ID}\nchecker-source=9a352eea6c935ad35cb8ec22e521a7620ec5d474\nargv=check --strict-parsing --expand-let-bindings -- PROOF PROBLEM\nproblem-sha256={}\nproof-sha256={proof_sha}\n",
            sha256_bytes(problem)
        )
        .as_bytes(),
    )
}

fn missing_proof_sha(fixture: Fixture) -> String {
    sha256_bytes(format!("{VALIDATOR_ID}\nfixture={}\nmissing-proof\n", fixture.id).as_bytes())
}

fn expected_case_ids() -> Vec<String> {
    let mut ids = vec![
        "carcara.identity".to_string(),
        "control.corrupt-proof".to_string(),
        "control.foreign-problem".to_string(),
    ];
    for fixture in FIXTURES {
        ids.push(format!("fixture.{}.ay", fixture.id));
        ids.push(format!("fixture.{}.carcara", fixture.id));
        ids.push(format!("fixture.{}.proof", fixture.id));
    }
    ids.sort();
    ids
}

fn validate_receipt_rows(rows: &[ValidatorCase], checker_sha: &str) -> Result<(), String> {
    let version = checker_cohort::version_for_sha(checker_sha)
        .ok_or("unqualified checker in proof receipt")?;
    let ids = rows.iter().map(|row| row.id.clone()).collect::<Vec<_>>();
    if ids != expected_case_ids() {
        return Err(format!(
            "{VALIDATOR_ID} does not contain the exact authored fixture and negative-control inventory"
        ));
    }
    let identity = row(rows, "carcara.identity")?;
    let expected_version_stdout = format!("{version}\n");
    if identity.input_sha256 != checker_identity_input_sha(checker_sha, version)
        || (identity.outcome == ValidatorCaseOutcome::Pass
            && (identity.exit_code != Some(0)
                || identity.stdout.as_deref() != Some(expected_version_stdout.as_str())
                || identity.stderr.as_deref() != Some("")
                || identity.process.is_none()))
    {
        return Err(format!(
            "{VALIDATOR_ID} has invalid Carcara identity evidence"
        ));
    }
    for fixture in FIXTURES {
        let ay = row(rows, &format!("fixture.{}.ay", fixture.id))?;
        if ay.input_sha256 != sha256_bytes(fixture.problem.as_bytes())
            || (ay.outcome == ValidatorCaseOutcome::Pass
                && (ay.exit_code != Some(0)
                    || ay.stdout.as_deref() != Some(fixture.expected_stdout)
                    || ay.stderr.as_deref() != Some("")
                    || ay.process.is_none()))
        {
            return Err(format!(
                "{VALIDATOR_ID} fixture {} has invalid AY evidence",
                fixture.id
            ));
        }
        let proof_row = row(rows, &format!("fixture.{}.proof", fixture.id))?;
        let proof_sha = if let Some(text) = proof_row.stdout.as_deref() {
            let analysis = analyze_proof(text.as_bytes())?;
            if proof_row.outcome == ValidatorCaseOutcome::Pass && !analysis.strict {
                return Err(format!(
                    "{VALIDATOR_ID} fixture {} claims a non-strict proof passes",
                    fixture.id
                ));
            }
            analysis.sha256
        } else {
            missing_proof_sha(fixture)
        };
        if proof_row.input_sha256 != proof_binding_sha(fixture.problem.as_bytes(), &proof_sha) {
            return Err(format!(
                "{VALIDATOR_ID} fixture {} proof/problem binding drift",
                fixture.id
            ));
        }
        if proof_row.outcome == ValidatorCaseOutcome::Pass
            && (proof_row.exit_code != Some(0) || proof_row.process.is_none())
        {
            return Err(format!(
                "{VALIDATOR_ID} fixture {} proof artifact lacks successful guarded AY provenance",
                fixture.id
            ));
        }
        let checker = row(rows, &format!("fixture.{}.carcara", fixture.id))?;
        // A `valid` counts only over retained proof bytes the shared scan finds
        // clean; with no retained proof there is nothing to scan, so it fails.
        let judgeable = proof_row.stdout.as_deref().is_some_and(|proof| {
            pinned_carcara_can_judge(fixture.problem, proof.as_bytes()).is_ok()
        });
        if checker.input_sha256 != checker_binding_sha(fixture.problem.as_bytes(), &proof_sha)
            || (checker.outcome == ValidatorCaseOutcome::Pass
                && (checker.exit_code != Some(0)
                    || checker.stdout.as_deref() != Some("valid\n")
                    || checker.stderr.as_deref() != Some("")
                    || checker.process.is_none()
                    || !judgeable))
        {
            return Err(format!(
                "{VALIDATOR_ID} fixture {} has invalid independent replay evidence",
                fixture.id
            ));
        }
    }
    validate_control_rows(rows)?;
    Ok(())
}

fn validate_control_rows(rows: &[ValidatorCase]) -> Result<(), String> {
    let source = row(rows, &format!("fixture.{}.proof", FIXTURES[0].id))?;
    let Some(proof) = source.stdout.as_deref() else {
        return Ok(());
    };
    let corrupted = corrupt_first_rule(proof.as_bytes())?;
    let controls = [
        (
            "control.corrupt-proof",
            FIXTURES[0].problem.as_bytes(),
            sha256_bytes(&corrupted),
        ),
        (
            "control.foreign-problem",
            FOREIGN_PROBLEM.as_bytes(),
            sha256_bytes(proof.as_bytes()),
        ),
    ];
    for (id, problem, proof_sha) in controls {
        let control = row(rows, id)?;
        if control.input_sha256 != checker_binding_sha(problem, &proof_sha)
            || (control.outcome == ValidatorCaseOutcome::Pass
                && (control.exit_code != Some(1)
                    || control.stdout.as_deref() != Some("invalid\n")
                    || control.process.is_none()))
        {
            return Err(format!("{VALIDATOR_ID} negative control {id} is invalid"));
        }
    }
    Ok(())
}

fn row<'a>(rows: &'a [ValidatorCase], id: &str) -> Result<&'a ValidatorCase, String> {
    rows.iter()
        .find(|row| row.id == id)
        .ok_or_else(|| format!("{VALIDATOR_ID} is missing case {id}"))
}

fn proof_dimension(contract: &Contract) -> Result<&Dimension, String> {
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == DIMENSION_ID)
        .ok_or_else(|| format!("closed {DIMENSION_ID} dimension is missing"))
}

#[cfg(test)]
mod pinned_carcara_tests;

#[cfg(test)]
mod tests {
    use super::*;

    fn completed_capture(stdout: &str, stderr: String, exit_code: i32) -> CapturedProcess {
        CapturedProcess {
            stdout: stdout.to_string(),
            stderr,
            stdout_valid: true,
            stderr_valid: true,
            exit_code: Some(exit_code),
            success: exit_code == 0,
            process: ProcessObservation {
                stdin_complete: true,
                timed_out: false,
                memout: false,
                stdout_truncated: false,
                stderr_truncated: false,
            },
        }
    }

    #[test]
    fn owned_proof_path_diagnostics_replay_without_hiding_stderr_failure() {
        fn row(directory: &Path, steps: usize) -> ValidatorCase {
            let fixture = FIXTURES[0];
            let capture = completed_capture(
                fixture.expected_stdout,
                format!(
                    "c ay.proof.certificate path={} unproved_steps={steps}\n",
                    directory.join("fixture.alethe").display()
                ),
                0,
            );
            let mut rows = vec![ay_fixture_row(
                fixture,
                &capture,
                Some(b"(step t0 (cl) :rule false)\n"),
            )];
            let paths = current_abi::StagingPaths::new(&[(directory, "@UNSAT_FIXTURES@")])
                .expect("owned paths");
            normalize_diagnostic_rows(&mut rows, &paths).expect("normalize diagnostic");
            rows.remove(0)
        }
        let first_directory = tempfile::tempdir().expect("first fixture directory");
        let second_directory = tempfile::tempdir().expect("second fixture directory");
        let first = row(first_directory.path(), 0);
        let second = row(second_directory.path(), 0);
        assert_eq!(first, second);
        assert_eq!(first.outcome, ValidatorCaseOutcome::Fail);
        assert!(first.observed.contains("stderr-empty=false"));
        assert!(first
            .stderr
            .as_deref()
            .is_some_and(|stderr| stderr.contains("@UNSAT_FIXTURES@/fixture.alethe")));
        assert_ne!(first, row(second_directory.path(), 1));
    }

    #[test]
    fn normalized_control_diagnostic_hash_remains_bound_to_retained_stderr() {
        fn row(directory: &Path, reason: &str) -> ValidatorCase {
            let capture = completed_capture(
                "invalid\n",
                format!("{}: {reason}\n", directory.join("control.alethe").display()),
                1,
            );
            let mut rows = vec![rejection_control_row(
                "control.corrupt-proof",
                FIXTURES[0].problem.as_bytes(),
                b"(step t0 (cl) :rule __ay_corrupted_rule__)\n",
                capture,
                "reject corrupted rule",
            )];
            let paths = current_abi::StagingPaths::new(&[(directory, "@UNSAT_FIXTURES@")])
                .expect("owned paths");
            normalize_diagnostic_rows(&mut rows, &paths).expect("normalize diagnostic");
            rows.remove(0)
        }
        let first_directory = tempfile::tempdir().expect("first fixture directory");
        let second_directory = tempfile::tempdir().expect("second fixture directory");
        let first = row(first_directory.path(), "unknown rule");
        assert_eq!(first, row(second_directory.path(), "unknown rule"));
        assert_eq!(first.outcome, ValidatorCaseOutcome::Pass);
        let stderr = first.stderr.as_deref().expect("retained diagnostic");
        assert!(first.observed.ends_with(&format!(
            ";stderr-sha256={}",
            sha256_bytes(stderr.as_bytes())
        )));
        assert_ne!(first, row(second_directory.path(), "unknown term"));

        let paths = current_abi::StagingPaths::new(&[(first_directory.path(), "@UNSAT_FIXTURES@")])
            .expect("owned paths");
        let mut tampered = vec![first];
        tampered[0].stderr = Some("altered diagnostic".to_string());
        assert!(normalize_diagnostic_rows(&mut tampered, &paths).is_err());
    }

    #[test]
    fn diagnostic_normalization_leaves_exact_proof_and_binding_untouched() {
        let directory = tempfile::tempdir().expect("fixture directory");
        let proof = format!(
            "; literal {}\n(step t0 (cl) :rule false)\n",
            directory.path().join("artifact").display()
        );
        let capture = completed_capture(FIXTURES[0].expected_stdout, String::new(), 0);
        let original = proof_fixture_row(FIXTURES[0], &capture, Some(proof.as_bytes()));
        let mut rows = vec![original.clone()];
        let paths = current_abi::StagingPaths::new(&[(directory.path(), "@UNSAT_FIXTURES@")])
            .expect("owned paths");
        normalize_diagnostic_rows(&mut rows, &paths).expect("normalize diagnostics");
        assert_eq!(rows, vec![original]);
        assert_eq!(rows[0].stdout.as_deref(), Some(proof.as_str()));
    }

    #[test]
    fn uppercase_proof_suffix_does_not_take_row_schema_exemption() {
        let directory = tempfile::tempdir().expect("fixture directory");
        let proof = format!(
            "; literal {}\n(step t0 (cl) :rule false)\n",
            directory.path().join("artifact").display()
        );
        let capture = completed_capture(FIXTURES[0].expected_stdout, String::new(), 0);
        let mut row = proof_fixture_row(FIXTURES[0], &capture, Some(proof.as_bytes()));
        row.id = row.id.replace(".proof", ".PROOF");
        let paths = current_abi::StagingPaths::new(&[(directory.path(), "@UNSAT_FIXTURES@")])
            .expect("owned paths");
        normalize_diagnostic_rows(std::slice::from_mut(&mut row), &paths)
            .expect("normalize diagnostics");
        assert_eq!(row.id, format!("fixture.{}.PROOF", FIXTURES[0].id));
        let stdout = row.stdout.as_deref().unwrap();
        assert!(stdout.contains("@UNSAT_FIXTURES@/artifact"));
        assert!(!stdout.contains(directory.path().to_str().unwrap()));
    }

    #[test]
    fn case_inventory_is_closed_and_sorted() {
        let ids = expected_case_ids();
        assert_eq!(ids.len(), FIXTURES.len() * 3 + 3);
        assert!(ids.windows(2).all(|pair| pair[0] < pair[1]));
    }

    #[test]
    fn mutation_changes_a_real_rule_name() {
        let proof = b"(step t0 (cl false) :rule assume)\n";
        let corrupted = corrupt_first_rule(proof).expect("mutation");
        assert_ne!(corrupted, proof);
        assert!(String::from_utf8(corrupted)
            .expect("UTF-8")
            .contains(":rule __ay_corrupted_rule__"));
    }

    #[test]
    fn every_fixture_has_exactly_one_public_unsat() {
        for fixture in FIXTURES {
            assert_eq!(
                fixture
                    .expected_stdout
                    .lines()
                    .filter(|line| *line == "unsat")
                    .count(),
                1,
                "{}",
                fixture.id
            );
        }
    }
}
