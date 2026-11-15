// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Registered custody for the current ABI measurement. The exhaustive claim
//! concerns the population of open function contracts, not their completion.

use super::*;

pub(super) const VALIDATOR_ID: &str = "builtin.z3-abi-5.3.3.v1";
const DIMENSION_ID: &str = "overlay.z3-5.3.3";
const REQUIREMENT_ID: &str = "overlay.z3-5.3.3.c-abi";
const REPORT_INPUT_ID: &str = "z3-5.3.3-abi-measurement";
const REPORT_SELECTION: &str = "Current 817-function ABI measurement: exact public source types, provider symbols, compiler and consumer identities, AY header/source coherence, finite observations, and every incomplete full-domain semantic contract";

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    if args == ["--help"] || args == ["-h"] {
        println!("Usage: ay-z3-parity smtlib-conformance run z3-abi-current <manifest> --source DIR --receipt FILE [--ay-library FILE] [--z3-library FILE] [--timeout SECONDS] [--measurement-report FILE]\n\nRetain the current 817-function ABI measurement and emit a registered receipt. An existing report may be reused only with identical source, provider, compiler, profile and validator bindings; attachment still replays it. Every incomplete full-domain function contract remains a failed row even when all named finite observations pass.");
        return Ok(0);
    }
    let mut manifest = None;
    let mut source = None;
    let mut receipt_path = None;
    let mut ay_override = None;
    let mut z3_override = None;
    let mut timeout = None;
    let mut measurement = None;
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        match argument.as_str() {
            "--source"
            | "--receipt"
            | "--ay-library"
            | "--z3-library"
            | "--measurement-report"
            | "--timeout" => {
                index += 1;
                let value = args
                    .get(index)
                    .ok_or_else(|| format!("{argument} needs a value"))?;
                match argument.as_str() {
                    "--source" => set_path(&mut source, value, argument)?,
                    "--receipt" => set_path(&mut receipt_path, value, argument)?,
                    "--ay-library" => set_path(&mut ay_override, value, argument)?,
                    "--z3-library" => set_path(&mut z3_override, value, argument)?,
                    "--measurement-report" => set_path(&mut measurement, value, argument)?,
                    _ => {
                        let seconds: u64 = value
                            .parse()
                            .map_err(|_| "--timeout needs integer seconds")?;
                        if seconds == 0
                            || seconds > 3600
                            || timeout.replace(Duration::from_secs(seconds)).is_some()
                        {
                            return Err(
                                "--timeout must occur once and be between 1 and 3600 seconds"
                                    .to_string(),
                            );
                        }
                    }
                }
            }
            value if value.starts_with('-') => {
                return Err(format!("unknown current ABI receipt argument {value:?}"))
            }
            value => set_path(&mut manifest, value, "manifest")?,
        }
        index += 1;
    }
    let manifest = manifest.ok_or("z3-abi-current needs a manifest path")?;
    let source =
        source.ok_or("z3-abi-current requires --source DIR with the complete pinned checkout")?;
    let receipt_path = receipt_path.ok_or("z3-abi-current requires --receipt FILE")?;
    let loaded = load_contract(&manifest)?;
    validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real campaign id before producing ABI evidence".to_string());
    }
    let subject = loaded
        .contract
        .subject
        .ay_shared_library
        .as_ref()
        .ok_or("z3-abi-current requires subject.ay_shared_library")?;
    let ay = ay_override.unwrap_or_else(|| artifact_path(&loaded.base, &subject.path));
    let z3 = match z3_override {
        Some(path) => path,
        None => reference_library_path()?,
    };
    let source =
        fs::canonicalize(source).map_err(|error| format!("canonicalize pinned source: {error}"))?;
    let ay = fs::canonicalize(ay).map_err(|error| format!("canonicalize AY library: {error}"))?;
    let z3 = fs::canonicalize(z3).map_err(|error| format!("canonicalize Z3 library: {error}"))?;
    if sha256_file(&ay, "registered ABI AY library")? != subject.sha256 {
        return Err("selected ABI AY library differs from the contract".to_string());
    }
    let contract_timeout = loaded
        .contract
        .resource_envelope
        .as_deref()
        .map(parse_resource_envelope)
        .transpose()?
        .map(|envelope| envelope.timeout);
    let timeout = timeout.or(contract_timeout).unwrap_or(TIMEOUT);
    if contract_timeout.is_some_and(|expected| expected != timeout) {
        return Err("ABI timeout differs from the contract resource envelope".to_string());
    }
    let report = if let Some(path) = measurement {
        let report: Report =
            serde_json::from_slice(&read_bounded(&path)?).map_err(|error| error.to_string())?;
        if report.source != source || report.ay_library != ay || report.z3_library != z3 {
            return Err(
                "existing ABI measurement selects different source or library paths".to_string(),
            );
        }
        report
    } else {
        measure_with_timeout(&source, &ay, &z3, timeout)?
    };
    let validator = fs::canonicalize(std::env::current_exe().map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())?;
    let validator_sha256 = sha256_file(&validator, "registered ABI validator")?;
    validate_bindings(&report, &loaded.contract, &validator_sha256, timeout)?;
    let dimension = loaded
        .contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == DIMENSION_ID)
        .ok_or("current ABI overlay dimension is missing")?;
    let receipt_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let report_path = receipt_path.with_extension("measurement.json");
    let report_relative = future_relative_output(&loaded.base, &report_path)?;
    let report_bytes = pretty_json(&report)?;
    if report_bytes.len() as u64 > MAX_REPORT_BYTES {
        return Err("registered ABI measurement exceeds its byte bound".to_string());
    }
    let report_artifact = Artifact {
        path: report_relative,
        sha256: sha256_bytes(&report_bytes),
    };
    let mut receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: DIMENSION_ID.to_string(),
        requirement_ids: vec![REQUIREMENT_ID.to_string()],
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: VALIDATOR_ID.to_string(),
            kind: ValidatorKind::Z3Differential,
            path: validator
                .to_str()
                .ok_or("ABI validator path is not UTF-8")?
                .to_string(),
            sha256: validator_sha256,
        },
        subject: ReceiptSubject {
            ay_executable_sha256: loaded
                .contract
                .subject
                .ay_executable
                .as_ref()
                .map(|artifact| artifact.sha256.clone()),
            ay_shared_library_sha256: Some(report.ay_library_sha256.clone()),
        },
        z3_binary_sha256: Some(
            loaded
                .contract
                .profile
                .z3_overlay
                .reference_executable
                .sha256
                .clone(),
        ),
        z3_shared_library_sha256: Some(report.z3_library_sha256.clone()),
        reference_inputs: vec![report_input(&loaded.contract.profile, report_artifact)],
        auxiliary_tools: Vec::new(),
        source_provenance: None,
        resource_envelope: Some(report.resource_envelope.clone()),
        exhaustive: true,
        result: ValidatorResult::Fail,
        cases: case_counts_from_rows(&[])?,
        case_results: Vec::new(),
    };
    receipt.case_results = case_rows(&report, &receipt)?;
    receipt.cases = case_counts_from_rows(&receipt.case_results)?;
    receipt.result = overall_validator_result(&receipt.case_results);
    let bytes = pretty_json(&receipt)?;
    if bytes.len() as u64 > MAX_VALIDATOR_RECEIPT_BYTES {
        return Err("current ABI receipt exceeds its fixed byte bound".to_string());
    }
    atomic_write_new(&report_path, &report_bytes)?;
    atomic_write_new(&receipt_path, &bytes)?;
    let receipt_sha256 = sha256_bytes(&bytes);
    println!("z3-abi-current=FAIL functions={} full_domain_unresolved={} finite_registered={} finite_passed={} receipt={receipt_relative} sha256={receipt_sha256}",
        report.functions.len(), report.functions.iter().filter(|function| !function.semantic_contract_complete).count(),
        report.semantic_contracts.registered_functions, report.semantic_contracts.passed_functions);
    println!("attach to {REQUIREMENT_ID}: {{\"path\":\"{receipt_relative}\",\"sha256\":\"{receipt_sha256}\"}}");
    Ok(1)
}

fn set_path(target: &mut Option<PathBuf>, value: &str, label: &str) -> Result<(), String> {
    if target.replace(PathBuf::from(value)).is_some() {
        return Err(format!("{label} must occur exactly once"));
    }
    Ok(())
}

fn report_input(profile: &Profile, artifact: Artifact) -> ReferenceInput {
    ReferenceInput {
        id: REPORT_INPUT_ID.to_string(),
        cohort: SourceCohort::Z3Source,
        repository: profile.z3_overlay.source_repository.clone(),
        revision: profile.z3_overlay.source_commit.clone(),
        selection: REPORT_SELECTION.to_string(),
        item_count: 817,
        digest_kind: profile.z3_overlay.tracked_source_tree_digest_kind.clone(),
        selection_sha256: profile.z3_overlay.tracked_source_tree_sha256.clone(),
        snapshot: artifact,
    }
}

fn validate_bindings(
    report: &Report,
    contract: &Contract,
    validator_sha256: &str,
    timeout: Duration,
) -> Result<(), String> {
    validate_report(report)?;
    let subject = contract
        .subject
        .ay_shared_library
        .as_ref()
        .ok_or("ABI contract has no AY library")?;
    let envelope = parse_resource_envelope(&report.resource_envelope)?;
    let source = &report.reference_source_inventory;
    if report.validator_sha256 != validator_sha256
        || report.profile_sha256 != canonical_profile_sha256()?
        || report.ay_library_sha256 != subject.sha256
        || report.z3_library_sha256 != contract.profile.z3_overlay.reference_shared_library.sha256
        || envelope.jobs != 1
        || envelope.timeout != timeout
        || contract
            .resource_envelope
            .as_ref()
            .is_some_and(|expected| expected != &report.resource_envelope)
        || source["source_commit"].as_str()
            != Some(contract.profile.z3_overlay.source_commit.as_str())
        || source["schema"].as_str() != Some("ay-current-z3-source-inventory/v1")
        || source["profile_id"].as_str() != Some(contract.profile.id.as_str())
        || source["profile_sha256"].as_str() != Some(report.profile_sha256.as_str())
        || source["source_repository"].as_str()
            != Some(contract.profile.z3_overlay.source_repository.as_str())
        || source["source_path"].as_str() != report.source.to_str()
        || source["source_files"].as_array().map(Vec::len)
            != Some(contract.profile.z3_overlay.tracked_source_file_count)
        || source["enum_constants"]
            .as_object()
            .map(serde_json::Map::len)
            != Some(370)
        || source["source_bytes_authenticated"].as_bool() != Some(true)
        || source["measured_public_metadata_complete"].as_bool() != Some(true)
        || source["source_semantics_inventory_complete"].as_bool() != Some(false)
        || source["ay_behavior_validated"].as_bool() != Some(false)
        || source["source_tree_sha256"].as_str()
            != Some(
                contract
                    .profile
                    .z3_overlay
                    .tracked_source_tree_sha256
                    .as_str(),
            )
        || source["z3_executable_sha256"].as_str()
            != Some(
                contract
                    .profile
                    .z3_overlay
                    .reference_executable
                    .sha256
                    .as_str(),
            )
    {
        return Err("current ABI measurement profile, source, provider, validator or resource binding differs from the campaign".to_string());
    }
    verify_artifact(
        &Artifact {
            path: report.ay_library.to_string_lossy().into_owned(),
            sha256: report.ay_library_sha256.clone(),
        },
        Path::new("."),
        "current ABI AY provider",
    )?;
    verify_artifact(
        &Artifact {
            path: report.z3_library.to_string_lossy().into_owned(),
            sha256: report.z3_library_sha256.clone(),
        },
        Path::new("."),
        "current ABI Z3 provider",
    )?;
    let declarations = source["declarations"]
        .as_object()
        .ok_or("ABI report lacks source declarations")?;
    if declarations.len() != report.functions.len()
        || report
            .functions
            .iter()
            .any(|function| declarations.get(&function.name) != Some(&function.reference_signature))
    {
        return Err(
            "ABI report function inventory differs from its retained source declarations"
                .to_string(),
        );
    }
    Ok(())
}

fn case_rows(report: &Report, receipt: &ValidatorReceipt) -> Result<Vec<ValidatorCase>, String> {
    let report_hash = &receipt
        .reference_inputs
        .first()
        .ok_or("ABI receipt has no report")?
        .snapshot
        .sha256;
    let binding = serde_json::to_vec(&(
        &receipt.campaign_id,
        &receipt.profile_sha256,
        &receipt.inventory_sha256,
        &receipt.validator.sha256,
        &receipt.subject,
        &receipt.z3_shared_library_sha256,
        &receipt.resource_envelope,
        report_hash,
    ))
    .map_err(|error| error.to_string())?;
    let mut rows = Vec::new();
    for function in &report.functions {
        rows.push(function_case(function, &binding)?);
    }
    for family in &report.semantic_contracts.families {
        rows.push(metadata_case(&format!("abi.finite.{}", family.id), "Both providers satisfy every named finite input/state assertion and the reference rejects the inverted final check; full-domain contracts remain open", family, &binding, family.passed)?);
    }
    rows.push(metadata_case(
        "abi.fragment",
        "Exact public types, exports and finite probes agree; this is only a measured fragment",
        &report.fragment_passed,
        &binding,
        report.fragment_passed,
    )?);
    rows.push(metadata_case(
        "abi.header-provenance",
        "Captured AY headers match the source revision declared by the tested AY library",
        &report.ay_header_provenance,
        &binding,
        report
            .ay_header_provenance
            .headers_match_library_source_commit,
    )?);
    for capture in &report.captures {
        let summary = serde_json::json!({
            "id": capture.id, "exit_code": capture.exit_code,
            "timed_out": capture.timed_out, "memout": capture.memout,
            "stdin_complete": capture.stdin_complete,
            "stdout_truncated": capture.stdout_truncated,
            "stderr_truncated": capture.stderr_truncated,
            "stdout_sha256": sha256_bytes(capture.stdout.as_bytes()),
            "stderr_sha256": sha256_bytes(capture.stderr.as_bytes()),
        });
        let mut row = metadata_case(
            &format!("abi.capture.{}", capture.id),
            "Complete bounded capture with its registered expected exit and exact negative-control protocol where applicable",
            &summary,
            &binding,
            semantic_contracts::negative_capture_passed(capture)
                .unwrap_or_else(|| capture.process_completed()),
        )?;
        // The exact streams live in the authenticated report. Do not duplicate
        // potentially large compiler output inside a bounded receipt row.
        row.exit_code = capture.exit_code;
        row.process = Some(ProcessObservation {
            stdin_complete: capture.stdin_complete,
            timed_out: capture.timed_out,
            memout: capture.memout,
            stdout_truncated: capture.stdout_truncated,
            stderr_truncated: capture.stderr_truncated,
        });
        row.outcome = if capture.memout {
            ValidatorCaseOutcome::Memout
        } else if capture.timed_out {
            ValidatorCaseOutcome::Timeout
        } else if capture.exit_code.is_none() {
            ValidatorCaseOutcome::Crash
        } else {
            row.outcome
        };
        rows.push(row);
    }
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    if rows.windows(2).any(|pair| pair[0].id >= pair[1].id) {
        return Err("current ABI receipt case identities are not unique".to_string());
    }
    Ok(rows)
}

fn function_case(function: &Function, binding: &[u8]) -> Result<ValidatorCase, String> {
    // There is deliberately no finite-probe shortcut to this outcome. The
    // The producer/validator reject semantic_contract_complete=true in v6.
    let observed = serde_json::json!({
        "function": function.name,
        "function_record_sha256": sha256_bytes(&serde_json::to_vec(function).map_err(|error| error.to_string())?),
        "signature_matches": function.signature_matches,
        "reference_symbol_resolves": function.reference_symbol_resolves,
        "ay_symbol_resolves": function.ay_symbol_resolves,
        "linked_consumer_exercised": function.linked_consumer_exercised,
        "registered_obligations": function.semantic_contract.obligations.len(),
        "registered_obligations_passed": function.semantic_contract.registered_obligations_passed,
        "unregistered_aspects": function.semantic_contract.unregistered_aspects,
        "semantic_contract_complete": function.semantic_contract_complete,
        "remaining": function.remaining,
    });
    metadata_case(&format!("abi.function.{}", function.name),
        "Complete the full-domain input, lifetime, context, state, invalid-argument and result contract; finite observations alone do not establish this", &observed, binding, false)
}

fn metadata_case<T: Serialize>(
    id: &str,
    expected: &str,
    observed: &T,
    binding: &[u8],
    passed: bool,
) -> Result<ValidatorCase, String> {
    let input_sha256 = sha256_bytes(&[binding, id.as_bytes(), expected.as_bytes()].concat());
    Ok(ValidatorCase {
        id: id.to_string(),
        input_sha256,
        expected: expected.to_string(),
        observed: serde_json::to_string(observed).map_err(|error| error.to_string())?,
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome: if passed {
            ValidatorCaseOutcome::Pass
        } else {
            ValidatorCaseOutcome::Fail
        },
    })
}

pub(super) fn validate_and_replay(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    if receipt.validator.id != VALIDATOR_ID
        || receipt.validator.kind != ValidatorKind::Z3Differential
        || context.dimension.id != DIMENSION_ID
        || receipt.requirement_ids != [REQUIREMENT_ID.to_string()]
        || !receipt.exhaustive
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
        || receipt.z3_binary_sha256.as_deref()
            != Some(
                context
                    .contract
                    .profile
                    .z3_overlay
                    .reference_executable
                    .sha256
                    .as_str(),
            )
        || receipt.z3_shared_library_sha256.as_deref()
            != Some(
                context
                    .contract
                    .profile
                    .z3_overlay
                    .reference_shared_library
                    .sha256
                    .as_str(),
            )
    {
        return Err("current ABI receipt has invalid scope or provider bindings".to_string());
    }
    let [input] = receipt.reference_inputs.as_slice() else {
        return Err(
            "current ABI receipt requires exactly one retained measurement report".to_string(),
        );
    };
    if input != &report_input(&context.contract.profile, input.snapshot.clone()) {
        return Err(
            "current ABI report source binding differs from the pinned population".to_string(),
        );
    }
    let path = resolve_relative_evidence_path(context.manifest_dir, &input.snapshot.path)?;
    let bytes = read_bounded(&path)?;
    if sha256_bytes(&bytes) != input.snapshot.sha256 {
        return Err("current ABI report hash mismatch".to_string());
    }
    let report: Report = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    let envelope = receipt
        .resource_envelope
        .as_deref()
        .ok_or("current ABI receipt has no resource envelope")?;
    let parsed = parse_resource_envelope(envelope)?;
    validate_bindings(
        &report,
        context.contract,
        &receipt.validator.sha256,
        parsed.timeout,
    )?;
    if report.resource_envelope != envelope
        || receipt.subject.ay_shared_library_sha256.as_deref()
            != Some(report.ay_library_sha256.as_str())
    {
        return Err(
            "current ABI receipt differs from its retained measurement bindings".to_string(),
        );
    }
    let rows = case_rows(&report, receipt)?;
    validate_exact_rows(&receipt.case_results, &rows)?;
    if receipt.cases != case_counts_from_rows(&rows)?
        || receipt.result != overall_validator_result(&rows)
    {
        return Err(
            "current ABI receipt differs from its exact retained function/finite/capture evidence"
                .to_string(),
        );
    }
    if context.mode.replays_registered_validators() {
        let fresh = measure_with_timeout(
            &report.source,
            &report.ay_library,
            &report.z3_library,
            parsed.timeout,
        )?;
        if fresh != report {
            return Err(
                "current ABI receipt does not match fresh authenticated execution".to_string(),
            );
        }
    }
    Ok(())
}

fn validate_exact_rows(actual: &[ValidatorCase], expected: &[ValidatorCase]) -> Result<(), String> {
    if actual != expected {
        return Err("current ABI receipt differs from its exact retained case rows".to_string());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finite_obligations_never_complete_the_full_function_contract() {
        let execution = semantic_contracts::Execution {
            contract_version: "fixture".to_string(),
            inventory_sha256: "0".repeat(64),
            // A declaration can gain obligations in additional families.
            // This fixture supplies every registered family as passing while
            // testing the full-domain classification of just this function.
            families: semantic_contracts::sources()
                .map(|(id, source)| semantic_contracts::FamilyResult {
                    id: id.to_string(),
                    source_sha256: sha256_bytes(source),
                    check_ids: Vec::new(),
                    negative_check_id: "fixture".to_string(),
                    reference_source_sha256: "0".repeat(64),
                    reference_mode_refusal_passed: true,
                    reference_negative_control_passed: true,
                    reference_passed: true,
                    ay_passed: true,
                    passed: true,
                })
                .collect(),
            registered_functions: 1,
            passed_functions: 1,
            uncovered_functions: 0,
            passed: true,
        };
        let function = Function {
            name: "Z3_solver_check".to_string(),
            reference_signature: Value::Null,
            ay_signature: Some(Value::Null),
            signature_matches: true,
            reference_symbol_resolves: true,
            ay_symbol_resolves: true,
            linked_consumer_exercised: true,
            semantic_contract: semantic_contracts::function_contract("Z3_solver_check", &execution),
            semantic_contract_complete: false,
            remaining: "Full-domain contract is open".to_string(),
        };
        let row = function_case(&function, b"exact measurement binding").expect("function case");
        assert_eq!(row.outcome, ValidatorCaseOutcome::Fail);
        assert!(row
            .observed
            .contains("\"semantic_contract_complete\":false"));
        assert!(row.observed.contains("\"linked_consumer_exercised\":true"));
        assert!(row
            .observed
            .contains("\"registered_obligations_passed\":true"));
    }

    #[test]
    fn measurement_and_campaign_identity_change_every_bound_case() {
        let first = metadata_case(
            "abi.fragment",
            "fragment only",
            &true,
            b"campaign-a report-1",
            true,
        )
        .expect("case");
        let second = metadata_case(
            "abi.fragment",
            "fragment only",
            &true,
            b"campaign-a report-2",
            true,
        )
        .expect("case");
        let foreign = metadata_case(
            "abi.fragment",
            "fragment only",
            &true,
            b"campaign-b report-1",
            true,
        )
        .expect("case");
        assert_ne!(first.input_sha256, second.input_sha256);
        assert_ne!(first.input_sha256, foreign.input_sha256);
    }

    #[test]
    fn exact_replay_refuses_omitted_reordered_or_fabricated_case_outcomes() {
        let first = metadata_case(
            "abi.function.Z3_a",
            "open contract",
            &false,
            b"binding",
            false,
        )
        .expect("case");
        let second = metadata_case(
            "abi.function.Z3_b",
            "open contract",
            &false,
            b"binding",
            false,
        )
        .expect("case");
        let expected = vec![first.clone(), second.clone()];
        validate_exact_rows(&expected, &expected).expect("same rows");
        assert!(validate_exact_rows(&[first.clone()], &expected).is_err());
        assert!(validate_exact_rows(&[second, first], &expected).is_err());
        let mut fabricated = expected.clone();
        fabricated[0].outcome = ValidatorCaseOutcome::Pass;
        assert!(validate_exact_rows(&fabricated, &expected).is_err());
        let mut changed = expected.clone();
        changed[0].observed.push_str("altered");
        assert!(validate_exact_rows(&changed, &expected).is_err());
    }
}
