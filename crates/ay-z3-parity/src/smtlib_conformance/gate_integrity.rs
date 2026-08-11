// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Registered negative controls for the full-replacement gate itself.
//!
//! A conformance receipt is useful only if malformed contracts and forged
//! evidence are rejected for the reason the contract claims.  These controls
//! exercise the same private validation functions used by `check`; the public
//! receipt is replayed from scratch instead of trusting its aggregate result.

use super::*;

pub(super) const VALIDATOR_ID: &str = "builtin.gate-integrity.v1";

const REQUIREMENT_ID: &str = "gate.integrity.negative-controls";
const CONTROL_IDS: [&str; 19] = [
    "gate.aggregate-spoof",
    "gate.artifact-hash-drift",
    "gate.aux-tool-duplicate",
    "gate.aux-tool-hash-drift",
    "gate.case-duplicate",
    "gate.case-truncated",
    "gate.contract-duplicate-dimension",
    "gate.contract-duplicate-row",
    "gate.contract-invented-row",
    "gate.contract-removed-dimension",
    "gate.evidence-foreign-profile",
    "gate.evidence-hash-drift",
    "gate.evidence-stale-campaign",
    "gate.evidence-unknown-validator",
    "gate.interrupted-outcomes",
    "gate.missing-bindings",
    "gate.profile-drift",
    "gate.reference-input-duplicate",
    "gate.reference-snapshot-hash-drift",
];

#[derive(Debug, Eq, PartialEq)]
struct Execution {
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--receipt" => {
                index += 1;
                receipt_path = Some(PathBuf::from(
                    args.get(index).ok_or("--receipt needs a path")?,
                ));
            }
            flag if flag.starts_with("--") => {
                return Err(format!("unknown gate-integrity flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("gate-integrity takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }

    let manifest = manifest.ok_or("gate-integrity needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("gate-integrity requires --receipt <path>")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let envelope = loaded
        .contract
        .resource_envelope
        .as_deref()
        .ok_or("gate-integrity requires contract.resource_envelope")?;
    validate_resource_envelope(envelope)?;
    let executable = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("gate-integrity requires subject.ay_executable")?;
    let output_relative = future_relative_output(&loaded.base, &receipt_path)?;

    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let validator_sha = sha256_file(&current_exe, "parity validator")?;
    let execution = execute()?;
    let gate = gate_dimension(&loaded.contract)?;
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: gate.id.clone(),
        requirement_ids: vec![REQUIREMENT_ID.to_string()],
        inventory_sha256: gate.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: VALIDATOR_ID.to_string(),
            kind: ValidatorKind::GateNegativeControl,
            path: current_exe.to_string_lossy().into_owned(),
            sha256: validator_sha,
        },
        subject: ReceiptSubject {
            ay_executable_sha256: Some(executable.sha256.clone()),
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
        resource_envelope: Some(envelope.to_string()),
        exhaustive: true,
        result: execution.result,
        cases: execution.cases,
        case_results: execution.case_results,
    };
    let bytes = pretty_json(&receipt)?;
    atomic_write_new(&receipt_path, &bytes)?;
    let receipt_sha = sha256_bytes(&bytes);
    println!(
        "gate-integrity={} receipt={} sha256={}",
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
    if receipt.validator.kind != ValidatorKind::GateNegativeControl
        || context.dimension.id != "gate.integrity"
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
    let actual_ids = receipt
        .case_results
        .iter()
        .map(|row| row.id.as_str())
        .collect::<Vec<_>>();
    if actual_ids != CONTROL_IDS {
        return Err(format!(
            "{VALIDATOR_ID} does not contain the exact closed negative-control inventory"
        ));
    }
    if context.mode.replays_registered_validators() {
        let live = execute()?;
        if receipt.result != live.result
            || receipt.cases != live.cases
            || receipt.case_results != live.case_results
        {
            return Err(format!(
                "{VALIDATOR_ID} receipt does not match a fresh in-process mutation replay"
            ));
        }
    }
    Ok(())
}

fn execute() -> Result<Execution, String> {
    let mut rows = Vec::with_capacity(CONTROL_IDS.len());

    rows.push(control(
        "gate.aggregate-spoof",
        b"aggregate says pass while detailed row says skipped",
        "aggregate counts do not match recomputed detailed rows",
        aggregate_spoof(),
    ));
    rows.push(control(
        "gate.artifact-hash-drift",
        b"manifest-bound artifact bytes changed",
        "hash mismatch",
        artifact_hash_drift(),
    ));
    rows.push(control(
        "gate.aux-tool-duplicate",
        b"two auxiliary checker bindings use the same identity",
        "sorted and duplicate-free",
        duplicate_auxiliary_tools(),
    ));
    rows.push(control(
        "gate.aux-tool-hash-drift",
        b"independent checker bytes changed after receipt creation",
        "hash mismatch",
        auxiliary_tool_hash_drift(),
    ));
    rows.push(control(
        "gate.case-duplicate",
        b"duplicate detailed validator case identifier",
        "sorted and duplicate-free",
        duplicate_cases(),
    ));
    rows.push(control(
        "gate.case-truncated",
        b"receipt total exceeds retained detailed rows",
        "detailed-row count",
        truncated_cases(),
    ));

    let mut duplicate_dimension = starter_contract(Subject::default())?;
    duplicate_dimension.dimensions[1] = duplicate_dimension.dimensions[0].clone();
    rows.push(contract_control(
        "gate.contract-duplicate-dimension",
        &duplicate_dimension,
        "duplicate dimension id",
    )?);

    let mut duplicate_row = starter_contract(Subject::default())?;
    let commands = dimension_mut(&mut duplicate_row, "language.commands")?;
    commands
        .requirements
        .insert(1, commands.requirements[0].clone());
    refresh_inventory(commands)?;
    rows.push(contract_control(
        "gate.contract-duplicate-row",
        &duplicate_row,
        "sorted by unique id",
    )?);

    let mut invented_row = starter_contract(Subject::default())?;
    let commands = dimension_mut(&mut invented_row, "language.commands")?;
    let mut invented = commands.requirements[0].clone();
    invented.id = "language.commands.zz-invented".to_string();
    commands.requirements.push(invented);
    commands
        .requirements
        .sort_by(|left, right| left.id.cmp(&right.id));
    refresh_inventory(commands)?;
    rows.push(contract_control(
        "gate.contract-invented-row",
        &invented_row,
        "invented or missing rows",
    )?);

    let mut removed_dimension = starter_contract(Subject::default())?;
    removed_dimension.dimensions.pop();
    rows.push(contract_control(
        "gate.contract-removed-dimension",
        &removed_dimension,
        "closed dimension mismatch",
    )?);

    let (receipt_contract, validator_path, validator_sha) = receipt_fixture()?;
    let gate = gate_dimension(&receipt_contract)?;
    let context = EvidenceContext {
        contract: &receipt_contract,
        manifest_dir: Path::new("."),
        dimension: gate,
        expected_kind: ValidatorKind::GateNegativeControl,
        required_requirement_id: Some(REQUIREMENT_ID),
        exact_requirement_ids: None,
        mode: ValidationMode::Structural,
    };
    let base_receipt = synthetic_receipt(&receipt_contract, validator_path, validator_sha)?;

    let mut foreign = base_receipt.clone();
    foreign.profile_sha256 = "f".repeat(64);
    rows.push(receipt_control(
        "gate.evidence-foreign-profile",
        &foreign,
        context,
        "profile digest mismatch",
    )?);
    rows.push(control(
        "gate.evidence-hash-drift",
        b"evidence reference hash does not match receipt bytes",
        "receipt hash mismatch",
        evidence_hash_drift(&base_receipt),
    ));
    let mut stale = base_receipt.clone();
    stale.campaign_id = "stale-campaign".to_string();
    rows.push(receipt_control(
        "gate.evidence-stale-campaign",
        &stale,
        context,
        "evidence belongs to campaign",
    )?);
    // The unregistered-validator control must differ from an otherwise VALID
    // receipt in exactly one way: the validator id. `resolve_validator_artifact`
    // grants the absolute-path exemption only to the built-in ids, so reusing
    // the built-in fixture's absolute `validator.path` left this receipt
    // malformed a SECOND way, and the gate rejected it on the path shape before
    // it could ever reach the unregistered-id dispatch. Give the forged checker
    // a well-formed relative artifact so the id is the only defect left and the
    // control proves the check it names.
    let forged_directory = tempfile::tempdir().map_err(|error| error.to_string())?;
    let forged_relative = "forged-external-checker.bin";
    let forged_artifact = forged_directory.path().join(forged_relative);
    fs::write(&forged_artifact, b"forged external checker\n")
        .map_err(|error| format!("writing forged checker artifact: {error}"))?;
    let mut unknown_validator = base_receipt;
    unknown_validator.validator.id = "forged.external-checker".to_string();
    unknown_validator.validator.path = forged_relative.to_string();
    unknown_validator.validator.sha256 = sha256_file(&forged_artifact, "forged checker")?;
    rows.push(receipt_control(
        "gate.evidence-unknown-validator",
        &unknown_validator,
        EvidenceContext {
            manifest_dir: forged_directory.path(),
            ..context
        },
        "unregistered validator",
    )?);

    rows.push(control(
        "gate.interrupted-outcomes",
        b"fail skipped unavailable timeout memout crash are all non-passing",
        "all interrupted outcomes remain non-passing",
        interrupted_outcomes(),
    ));

    let missing = starter_contract(Subject::default())?;
    rows.push(control(
        "gate.missing-bindings",
        &serde_json::to_vec(&missing).map_err(|error| error.to_string())?,
        "campaign, artifacts, and envelope remain blockers",
        missing_bindings(&missing),
    ));

    let mut profile_drift = starter_contract(Subject::default())?;
    profile_drift.profile.z3_overlay.version = "not-5.0.0".to_string();
    rows.push(contract_control(
        "gate.profile-drift",
        &profile_drift,
        "profile drift",
    )?);

    rows.push(control(
        "gate.reference-input-duplicate",
        b"two normative source bindings use the same identity",
        "sorted and duplicate-free",
        duplicate_reference_inputs(),
    ));
    rows.push(control(
        "gate.reference-snapshot-hash-drift",
        b"normative source snapshot bytes changed after receipt creation",
        "hash mismatch",
        reference_snapshot_hash_drift(),
    ));

    rows.sort_by(|left, right| left.id.cmp(&right.id));
    let actual_ids = rows.iter().map(|row| row.id.as_str()).collect::<Vec<_>>();
    if actual_ids != CONTROL_IDS {
        return Err("internal gate-integrity control inventory drift".to_string());
    }
    let cases = case_counts_from_rows(&rows)?;
    let result = overall_validator_result(&rows);
    Ok(Execution {
        result,
        cases,
        case_results: rows,
    })
}

fn gate_dimension(contract: &Contract) -> Result<&Dimension, String> {
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == "gate.integrity")
        .ok_or_else(|| "closed gate.integrity dimension is missing".to_string())
}

fn dimension_mut<'a>(contract: &'a mut Contract, id: &str) -> Result<&'a mut Dimension, String> {
    contract
        .dimensions
        .iter_mut()
        .find(|dimension| dimension.id == id)
        .ok_or_else(|| format!("closed {id} dimension is missing"))
}

fn refresh_inventory(dimension: &mut Dimension) -> Result<(), String> {
    dimension.inventory.item_count = dimension.requirements.len();
    dimension.inventory.sha256 = inventory_sha256(&dimension.requirements)?;
    Ok(())
}

fn contract_control(
    id: &str,
    contract: &Contract,
    expected: &str,
) -> Result<ValidatorCase, String> {
    let input = serde_json::to_vec(contract)
        .map_err(|error| format!("serializing negative-control contract: {error}"))?;
    Ok(control(
        id,
        &input,
        expected,
        validate_contract(contract, Path::new("."), ValidationMode::Structural).map(|_| ()),
    ))
}

fn receipt_control(
    id: &str,
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
    expected: &str,
) -> Result<ValidatorCase, String> {
    let input = serde_json::to_vec(receipt)
        .map_err(|error| format!("serializing negative-control receipt: {error}"))?;
    Ok(control(
        id,
        &input,
        expected,
        validate_validator_receipt(receipt, context).map(|_| ()),
    ))
}

fn control(id: &str, input: &[u8], expected: &str, rejection: Result<(), String>) -> ValidatorCase {
    let (observed, outcome) = match rejection {
        Err(error) if error.contains(expected) => (error, ValidatorCaseOutcome::Pass),
        Err(error) => (
            format!("wrong rejection reason: {error}"),
            ValidatorCaseOutcome::Fail,
        ),
        Ok(()) => (
            "mutation was incorrectly accepted".to_string(),
            ValidatorCaseOutcome::Fail,
        ),
    };
    ValidatorCase {
        id: id.to_string(),
        input_sha256: sha256_bytes(input),
        expected: format!("gate rejects mutation with diagnostic containing {expected:?}"),
        observed,
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome,
    }
}

fn aggregate_spoof() -> Result<(), String> {
    let row = ValidatorCase {
        id: "spoof.skipped".to_string(),
        input_sha256: "1".repeat(64),
        expected: "pass".to_string(),
        observed: "skipped".to_string(),
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome: ValidatorCaseOutcome::Skipped,
    };
    validate_case_results(
        &[row],
        &CaseCounts {
            total: 1,
            passed: 1,
            failed: 0,
            skipped: 0,
            unknown: 0,
            timed_out: 0,
            memout: 0,
            crashed: 0,
            unavailable: 0,
        },
    )
}

fn artifact_hash_drift() -> Result<(), String> {
    let directory = tempfile::tempdir().map_err(|error| error.to_string())?;
    let path = directory.path().join("ay");
    fs::write(&path, b"changed bytes").map_err(|error| error.to_string())?;
    validate_optional_artifact(
        Some(&Artifact {
            path: "ay".to_string(),
            sha256: "0".repeat(64),
        }),
        directory.path(),
        "AY executable",
    )
}

fn auxiliary_tool_hash_drift() -> Result<(), String> {
    let directory = tempfile::tempdir().map_err(|error| error.to_string())?;
    fs::write(directory.path().join("checker"), b"changed checker bytes")
        .map_err(|error| error.to_string())?;
    validate_auxiliary_tool_rows(
        &[AuxiliaryTool {
            id: "independent-checker".to_string(),
            role: "strict proof replay".to_string(),
            artifact: Artifact {
                path: "checker".to_string(),
                sha256: "0".repeat(64),
            },
            version_output: "checker 1.0".to_string(),
        }],
        directory.path(),
    )
}

fn duplicate_auxiliary_tools() -> Result<(), String> {
    let directory = tempfile::tempdir().map_err(|error| error.to_string())?;
    fs::write(directory.path().join("checker-a"), b"checker a")
        .map_err(|error| error.to_string())?;
    fs::write(directory.path().join("checker-b"), b"checker b")
        .map_err(|error| error.to_string())?;
    let tool = AuxiliaryTool {
        id: "independent-checker".to_string(),
        role: "strict proof replay".to_string(),
        artifact: Artifact {
            path: "checker-a".to_string(),
            sha256: sha256_bytes(b"checker a"),
        },
        version_output: "checker 1.0".to_string(),
    };
    let mut duplicate = tool.clone();
    duplicate.artifact.path = "checker-b".to_string();
    duplicate.artifact.sha256 = sha256_bytes(b"checker b");
    validate_auxiliary_tool_rows(&[tool, duplicate], directory.path())
}

fn reference_snapshot_hash_drift() -> Result<(), String> {
    let directory = tempfile::tempdir().map_err(|error| error.to_string())?;
    fs::write(
        directory.path().join("source.json"),
        b"changed source bytes",
    )
    .map_err(|error| error.to_string())?;
    validate_reference_input_rows(
        &[fixture_reference_input("smtlib-language", "source.json")],
        directory.path(),
    )
}

fn duplicate_reference_inputs() -> Result<(), String> {
    let directory = tempfile::tempdir().map_err(|error| error.to_string())?;
    fs::write(directory.path().join("source-a.json"), b"source a")
        .map_err(|error| error.to_string())?;
    fs::write(directory.path().join("source-b.json"), b"source b")
        .map_err(|error| error.to_string())?;
    let mut first = fixture_reference_input("smtlib-language", "source-a.json");
    first.snapshot.sha256 = sha256_bytes(b"source a");
    let mut duplicate = first.clone();
    duplicate.snapshot.path = "source-b.json".to_string();
    duplicate.snapshot.sha256 = sha256_bytes(b"source b");
    validate_reference_input_rows(&[first, duplicate], directory.path())
}

fn fixture_reference_input(id: &str, path: &str) -> ReferenceInput {
    ReferenceInput {
        id: id.to_string(),
        cohort: SourceCohort::SmtlibLanguage,
        repository: "https://github.com/SMT-LIB/SMT-LIB-2".to_string(),
        revision: "0".repeat(40),
        selection: "closed fixture selection".to_string(),
        item_count: 1,
        digest_kind: "fixture".to_string(),
        selection_sha256: "0".repeat(64),
        snapshot: Artifact {
            path: path.to_string(),
            sha256: "0".repeat(64),
        },
    }
}

fn duplicate_cases() -> Result<(), String> {
    let row = passing_fixture_row("duplicate");
    let rows = vec![row.clone(), row];
    let counts = CaseCounts {
        total: 2,
        passed: 2,
        failed: 0,
        skipped: 0,
        unknown: 0,
        timed_out: 0,
        memout: 0,
        crashed: 0,
        unavailable: 0,
    };
    validate_case_results(&rows, &counts)
}

fn truncated_cases() -> Result<(), String> {
    validate_case_results(
        &[passing_fixture_row("retained")],
        &CaseCounts {
            total: 2,
            passed: 2,
            failed: 0,
            skipped: 0,
            unknown: 0,
            timed_out: 0,
            memout: 0,
            crashed: 0,
            unavailable: 0,
        },
    )
}

fn evidence_hash_drift(receipt: &ValidatorReceipt) -> Result<(), String> {
    let directory = tempfile::tempdir().map_err(|error| error.to_string())?;
    let path = directory.path().join("receipt.json");
    let bytes = pretty_json(receipt)?;
    fs::write(&path, bytes).map_err(|error| error.to_string())?;
    let reference = EvidenceRef {
        path: "receipt.json".to_string(),
        sha256: "0".repeat(64),
    };
    let mut cache = ReceiptCache::default();
    load_validator_receipt(&reference, directory.path(), &mut cache).map(|_| ())
}

fn interrupted_outcomes() -> Result<(), String> {
    let non_passing = [
        ValidatorResult::Fail,
        ValidatorResult::Skipped,
        ValidatorResult::Unavailable,
        ValidatorResult::Timeout,
        ValidatorResult::Memout,
        ValidatorResult::Crash,
    ];
    if non_passing
        .into_iter()
        .any(|result| result == ValidatorResult::Pass)
    {
        Ok(())
    } else {
        Err("all interrupted outcomes remain non-passing".to_string())
    }
}

fn missing_bindings(contract: &Contract) -> Result<(), String> {
    let report = validate_contract(contract, Path::new("."), ValidationMode::Structural)?;
    let required = [
        "campaign_id is still `unassigned`",
        "subject.ay_executable is not bound",
        "subject.ay_shared_library is not bound",
        "resource_envelope is not bound",
    ];
    if required
        .iter()
        .all(|expected| report.blockers.iter().any(|actual| actual == expected))
    {
        Err("campaign, artifacts, and envelope remain blockers".to_string())
    } else {
        Ok(())
    }
}

fn receipt_fixture() -> Result<(Contract, String, String), String> {
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let validator_sha = sha256_file(&current_exe, "parity validator")?;
    let mut contract = starter_contract(Subject {
        ay_executable: Some(Artifact {
            path: current_exe.to_string_lossy().into_owned(),
            sha256: validator_sha.clone(),
        }),
        ay_shared_library: None,
    })?;
    contract.campaign_id = "gate-fixture".to_string();
    contract.resource_envelope = Some(
        "oom-guard-v2:jobs=1;memlimit_mb=1024;nbcore=1;headroom_mb=512;timeout_ns=1000000000;enforcement=ay-resource-v1:rss-watchdog-zero-grace;aggregate=ay-host-exclusive-flock-v1"
            .to_string(),
    );
    Ok((
        contract,
        current_exe.to_string_lossy().into_owned(),
        validator_sha,
    ))
}

fn synthetic_receipt(
    contract: &Contract,
    validator_path: String,
    validator_sha: String,
) -> Result<ValidatorReceipt, String> {
    let gate = gate_dimension(contract)?;
    let row = passing_fixture_row("fixture.pass");
    let cases = case_counts_from_rows(std::slice::from_ref(&row))?;
    Ok(ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: gate.id.clone(),
        requirement_ids: vec![REQUIREMENT_ID.to_string()],
        inventory_sha256: gate.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: VALIDATOR_ID.to_string(),
            kind: ValidatorKind::GateNegativeControl,
            path: validator_path,
            sha256: validator_sha,
        },
        subject: ReceiptSubject {
            ay_executable_sha256: contract
                .subject
                .ay_executable
                .as_ref()
                .map(|artifact| artifact.sha256.clone()),
            ay_shared_library_sha256: None,
        },
        z3_binary_sha256: None,
        z3_shared_library_sha256: None,
        reference_inputs: Vec::new(),
        auxiliary_tools: Vec::new(),
        source_provenance: None,
        resource_envelope: contract.resource_envelope.clone(),
        exhaustive: true,
        result: ValidatorResult::Pass,
        cases,
        case_results: vec![row],
    })
}

fn passing_fixture_row(id: &str) -> ValidatorCase {
    ValidatorCase {
        id: id.to_string(),
        input_sha256: sha256_bytes(id.as_bytes()),
        expected: "pass".to_string(),
        observed: "pass".to_string(),
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome: ValidatorCaseOutcome::Pass,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closed_negative_control_inventory_passes() {
        let execution = execute().expect("negative-control execution");
        assert_eq!(execution.result, ValidatorResult::Pass);
        assert_eq!(execution.cases.total, CONTROL_IDS.len());
        assert_eq!(execution.cases.passed, CONTROL_IDS.len());
        assert_eq!(
            execution
                .case_results
                .iter()
                .map(|row| row.id.as_str())
                .collect::<Vec<_>>(),
            CONTROL_IDS
        );
    }

    #[test]
    fn interrupted_result_classes_never_equal_pass() {
        let error = interrupted_outcomes().expect_err("non-pass matrix must be rejected");
        assert!(error.contains("all interrupted outcomes remain non-passing"));
    }
}
