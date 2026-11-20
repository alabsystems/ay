// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inspect the current ABI registry's recorded evidence on any supported host.

use super::*;

#[derive(Default, Serialize)]
struct Coverage {
    registered_families: usize,
    confirmed_families: usize,
    registered_checks: usize,
    confirmed_checks: usize,
}

#[derive(Default, Serialize)]
struct Gaps<'a> {
    missing_ay_declarations: Vec<&'a str>,
    signature_mismatches: Vec<&'a str>,
    missing_ay_exports: Vec<&'a str>,
    unavailable_reference_exports: Vec<&'a str>,
    functions_without_linked_witness: Vec<&'a str>,
    functions_without_confirmed_linked_behavior: Vec<&'a str>,
    functions_without_registered_obligations: Vec<&'a str>,
    functions_with_unconfirmed_obligations: Vec<&'a str>,
}

#[derive(Serialize)]
struct Comparison<'a> {
    previous_report_sha256: &'a str,
    newly_confirmed_functions: Vec<&'a str>,
    lost_confirmed_functions: Vec<&'a str>,
}

#[derive(Serialize)]
struct Inspection<'a> {
    schema: &'static str,
    mode: &'static str,
    report_sha256: &'a str,
    contract_version: &'a str,
    reference_platform: &'static str,
    function_count: usize,
    finite_semantic_coverage: Coverage,
    #[serde(flatten)]
    gaps: Gaps<'a>,
    enum_differences: &'a [String],
    probe_differences: &'a [String],
    failed_families: Vec<&'a semantic_contracts::FamilyResult>,
    function: Option<&'a Function>,
    changes: Option<Comparison<'a>>,
    blockers: &'a [String],
}

fn has_linked_behavior(row: &Function) -> bool {
    row.linked_consumer_exercised
        || row
            .semantic_contract
            .obligations
            .iter()
            .any(|obligation| obligation.passed)
}

impl<'a> Gaps<'a> {
    fn record(&mut self, row: &'a Function) {
        let name = row.name.as_str();
        if row.ay_signature.is_none() {
            self.missing_ay_declarations.push(name);
        } else if !row.signature_matches {
            self.signature_mismatches.push(name);
        }
        if !row.ay_symbol_resolves {
            self.missing_ay_exports.push(name);
        }
        if !row.reference_symbol_resolves {
            self.unavailable_reference_exports.push(name);
        }
        if !row.linked_consumer_exercised {
            self.functions_without_linked_witness.push(name);
        }
        if !has_linked_behavior(row) {
            self.functions_without_confirmed_linked_behavior.push(name);
        }
        let obligations = &row.semantic_contract.obligations;
        if obligations.is_empty() {
            self.functions_without_registered_obligations.push(name);
        } else if obligations.iter().any(|obligation| !obligation.passed) {
            self.functions_with_unconfirmed_obligations.push(name);
        }
    }
}

fn recorded_stock_witnesses(report: &Report) -> Result<BTreeSet<String>, String> {
    let mut witnesses = BTreeSet::new();
    for probe in crate::z3_abi_500::stock_c_probes() {
        if report.consumer_source_sha256.get(probe.id) != Some(&sha256_bytes(probe.source)) {
            return Err(format!(
                "ABI stock consumer source identity drift for {}",
                probe.id
            ));
        }
        let expected = crate::z3_abi_500::stock_c_probe_expected_stdout(&probe);
        if ["z3", "ay"].iter().all(|subject| {
            [
                (format!("build.{}.{subject}", probe.id), &[][..]),
                (
                    format!("consumer.{}.{subject}", probe.id),
                    expected.as_slice(),
                ),
            ]
            .into_iter()
            .all(|(id, stdout)| {
                report
                    .captures
                    .iter()
                    .any(|capture| capture.id == id && capture.exact_stdout(stdout))
            })
        }) {
            witnesses.extend(crate::z3_abi_500::stock_c_probe_callability_symbols(&probe));
        }
    }
    Ok(witnesses)
}

fn recorded_platform(report: &Report) -> Result<&'static str, String> {
    for platform in reference_platform::Platform::ALL {
        let profile = canonical_profile_for(platform.release()?)?;
        if profile_sha256(&profile)? == report.profile_sha256
            && profile.z3_overlay.reference_shared_library.sha256 == report.z3_library_sha256
        {
            current_release::validate_recorded_source(
                &report.reference_source_inventory,
                &profile,
            )?;
            return Ok(platform.row());
        }
    }
    Err("ABI report profile and reference library do not name the same pinned platform".into())
}

fn verify_export_record(
    capture: &Capture,
    provider: Provider,
    recorded: Option<&LibraryObservation>,
) -> Result<(), String> {
    let observed = parse_observation(capture, provider)?;
    if observed
        .as_ref()
        .map(|entry| &entry.required_resolvable_symbols)
        != recorded.map(|entry| &entry.required_resolvable_symbols)
    {
        return Err(format!("ABI export record differs from {}", capture.id));
    }
    Ok(())
}

fn load_report(path: &Path) -> Result<(String, Report, &'static str), String> {
    let (digest, report): (String, Report) =
        observed_json::read_hashed_json(path, MAX_REPORT_BYTES, "current ABI report")?;
    validate_observation(&report)?;
    let platform = recorded_platform(&report)?;
    validate_sha256(&report.ay_library_sha256, "AY library SHA-256")?;
    validate_sha256(&report.validator_sha256, "ABI validator SHA-256")?;
    validate_sha256(&report.semantic_compiler.sha256, "ABI compiler SHA-256")?;
    parse_resource_envelope_for(&report.resource_envelope, ResourceEnvelopeUse::Observation)?;
    let declarations = report.reference_source_inventory["declarations"]
        .as_object()
        .ok_or("ABI report lacks the reference declaration inventory")?;
    let captures: BTreeMap<_, _> = report
        .captures
        .iter()
        .map(|capture| (capture.id.as_str(), capture))
        .collect();
    if declarations.len() != report.functions.len() || captures.len() != report.captures.len() {
        return Err("ABI report has an inconsistent inventory or duplicate captures".into());
    }
    for (id, provider, observation) in [
        (
            "z3.symbols-and-finite-sets",
            Provider::Z3,
            report.reference_observation.as_ref(),
        ),
        (
            "ay.symbols-and-finite-sets",
            Provider::Ay,
            report.ay_observation.as_ref(),
        ),
    ] {
        let capture = captures
            .get(id)
            .ok_or_else(|| format!("ABI report lacks {id}"))?;
        verify_export_record(capture, provider, observation)?;
    }
    let witnesses = recorded_stock_witnesses(&report)?;
    for row in &report.functions {
        if declarations.get(&row.name) != Some(&row.reference_signature)
            || row.signature_matches
                != (row.ay_signature.as_ref() == Some(&row.reference_signature))
            || row.reference_symbol_resolves
                != observation_resolves(report.reference_observation.as_ref(), &row.name)
            || row.ay_symbol_resolves
                != observation_resolves(report.ay_observation.as_ref(), &row.name)
            || row.linked_consumer_exercised != witnesses.contains(&row.name)
        {
            return Err(format!(
                "ABI report has inconsistent evidence for {}",
                row.name
            ));
        }
    }
    Ok((digest, report, platform))
}

fn compare<'a>(
    report: &'a Report,
    previous: &Report,
    previous_report_sha256: &'a str,
) -> Result<Comparison<'a>, String> {
    if previous.profile_sha256 != report.profile_sha256
        || previous.semantic_contracts.contract_version
            != report.semantic_contracts.contract_version
        || previous.reference_source_inventory["declarations"]
            != report.reference_source_inventory["declarations"]
        || previous.resource_envelope != report.resource_envelope
        || previous.semantic_compiler.sha256 != report.semantic_compiler.sha256
    {
        return Err(
            "ABI comparison requires the same reference, registry, compiler, and resource envelope"
                .into(),
        );
    }
    let mut changes = Comparison {
        previous_report_sha256,
        newly_confirmed_functions: Vec::new(),
        lost_confirmed_functions: Vec::new(),
    };
    for (row, earlier) in report.functions.iter().zip(&previous.functions) {
        match (has_linked_behavior(earlier), has_linked_behavior(row)) {
            (false, true) => changes.newly_confirmed_functions.push(&row.name),
            (true, false) => changes.lost_confirmed_functions.push(&row.name),
            _ => {}
        }
    }
    Ok(changes)
}

pub(in crate::smtlib_conformance) fn run(args: &[String]) -> Result<i32, String> {
    const USAGE: &str = "abi-gaps FILE [--function Z3_NAME] [--against FILE] [--json]";
    if args
        .iter()
        .any(|arg| matches!(arg.as_str(), "--help" | "-h"))
    {
        println!(
            "{USAGE}\nInspect a bounded, recorded current ABI report. Use current-abi-check for independent execution."
        );
        return Ok(0);
    }
    let (path, rest) = args.split_first().ok_or(USAGE)?;
    let mut name = None;
    let mut previous_path = None;
    let mut json_output = false;
    let mut args = rest.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--function" if name.is_none() => name = Some(args.next().ok_or(USAGE)?),
            "--against" if previous_path.is_none() => {
                previous_path = Some(args.next().ok_or(USAGE)?)
            }
            "--json" if !json_output => json_output = true,
            _ => return Err(format!("unexpected argument {arg:?}\n{USAGE}")),
        }
    }
    let (digest, report, reference_platform) = load_report(Path::new(path))?;
    let previous = previous_path
        .map(|path| load_report(Path::new(path)))
        .transpose()?;
    let changes = previous
        .as_ref()
        .map(|(sha, previous, _)| compare(&report, previous, sha))
        .transpose()?;
    let function = name
        .map(|name| {
            report
                .functions
                .iter()
                .find(|row| row.name == *name)
                .ok_or_else(|| format!("unknown Z3 function {name:?}"))
        })
        .transpose()?;
    let mut gaps = Gaps::default();
    for row in &report.functions {
        gaps.record(row);
    }
    let families = &report.semantic_contracts.families;
    let mut coverage = Coverage {
        registered_families: families.len(),
        ..Coverage::default()
    };
    let mut failed_families = Vec::new();
    for family in families {
        coverage.registered_checks += family.check_ids.len();
        if family.passed {
            coverage.confirmed_families += 1;
            coverage.confirmed_checks += family.check_ids.len();
        } else {
            failed_families.push(family);
        }
    }
    let inspection = Inspection {
        schema: "ay-current-z3-abi-gaps/v1",
        mode: "recorded report inspection",
        report_sha256: &digest,
        contract_version: &report.semantic_contracts.contract_version,
        reference_platform,
        function_count: report.functions.len(),
        finite_semantic_coverage: coverage,
        gaps,
        enum_differences: &report.enum_differences,
        probe_differences: &report.probe_differences,
        failed_families,
        function,
        changes,
        blockers: &report.blockers,
    };
    if json_output {
        print!(
            "{}",
            String::from_utf8(pretty_json(&inspection)?).map_err(|error| error.to_string())?
        );
    } else {
        print_text(&inspection);
    }
    Ok(0)
}

fn print_text(inspection: &Inspection<'_>) {
    let coverage = &inspection.finite_semantic_coverage;
    let gaps = &inspection.gaps;
    println!(
        "{} ({}, {})\n{}/{} finite checks passed in {}/{} families; {} functions",
        inspection.mode,
        inspection.reference_platform,
        inspection.contract_version,
        coverage.confirmed_checks,
        coverage.registered_checks,
        coverage.confirmed_families,
        coverage.registered_families,
        inspection.function_count,
    );
    for (label, names) in [
        ("Missing AY declarations", &gaps.missing_ay_declarations),
        ("Signature mismatches", &gaps.signature_mismatches),
        ("Missing AY exports", &gaps.missing_ay_exports),
        (
            "Unavailable Z3 exports",
            &gaps.unavailable_reference_exports,
        ),
        (
            "Functions without confirmed linked behavior",
            &gaps.functions_without_confirmed_linked_behavior,
        ),
        (
            "Functions with unconfirmed obligations",
            &gaps.functions_with_unconfirmed_obligations,
        ),
    ] {
        println!("{label} ({}) {}", names.len(), names.join(" "));
    }
    for family in &inspection.failed_families {
        println!(
            "{} reference_controls={} reference={} ay={}",
            family.id,
            family.reference_negative_control_passed && family.reference_mode_refusal_passed,
            family.reference_passed,
            family.ay_passed,
        );
    }
    for (name, differences) in [
        ("Enum differences", inspection.enum_differences),
        ("Probe differences", inspection.probe_differences),
    ] {
        if !differences.is_empty() {
            println!("{name} {}", differences.join(" "));
        }
    }
    if let Some(row) = inspection.function {
        println!(
            "{} stock_consumer={}",
            row.name, row.linked_consumer_exercised
        );
        for obligation in &row.semantic_contract.obligations {
            println!(
                "  {} {} ({}/{})",
                if obligation.passed { "PASS" } else { "OPEN" },
                obligation.statement,
                obligation.family,
                obligation.check
            );
        }
        println!(
            "  Unregistered aspects {:?}",
            row.semantic_contract.unregistered_aspects
        );
    }
    if let Some(changes) = &inspection.changes {
        println!(
            "Newly confirmed ({}) {}",
            changes.newly_confirmed_functions.len(),
            changes.newly_confirmed_functions.join(" ")
        );
        println!(
            "Lost confirmation ({}) {}",
            changes.lost_confirmed_functions.len(),
            changes.lost_confirmed_functions.join(" ")
        );
    }
    for blocker in inspection.blockers {
        println!("  {blocker}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn export_credit_must_match_the_retained_child_capture() {
        let mut observation = LibraryObservation {
            exported_z3_symbols: vec!["Z3_example".into()],
            required_resolvable_symbols: vec!["Z3_example".into()],
            full_version: None,
            ay_build_stamp: None,
            probes: BTreeMap::new(),
        };
        let mut capture = Capture {
            id: "ay.symbols-and-finite-sets".into(),
            exit_code: Some(0),
            timed_out: false,
            memout: false,
            stdin_complete: true,
            stdout_truncated: false,
            stderr_truncated: false,
            stdout: serde_json::to_string(&observation).unwrap(),
            stderr: String::new(),
        };
        assert!(verify_export_record(&capture, Provider::Ay, Some(&observation)).is_ok());
        observation
            .required_resolvable_symbols
            .push("Z3_forged".into());
        assert!(verify_export_record(&capture, Provider::Ay, Some(&observation)).is_err());
        capture.stdout_truncated = true;
        assert!(verify_export_record(&capture, Provider::Ay, Some(&observation)).is_err());
        assert!(verify_export_record(&capture, Provider::Ay, None).is_ok());
    }

    #[test]
    fn failed_registered_check_and_stock_only_witness_have_distinct_gaps() {
        let mut row = Function {
            name: "Z3_example".into(),
            reference_signature: Value::Null,
            ay_signature: Some(Value::Null),
            signature_matches: true,
            reference_symbol_resolves: true,
            ay_symbol_resolves: true,
            linked_consumer_exercised: false,
            semantic_contract: semantic_contracts::FunctionContract {
                upstream_declaration: "Z3_example".into(),
                obligations: vec![semantic_contracts::Obligation {
                    id: "output".into(),
                    aspect: semantic_contracts::Aspect::Output,
                    statement: "Evaluate the known input".into(),
                    family: "example".into(),
                    check: "output".into(),
                    passed: false,
                }],
                unregistered_aspects: vec![],
                registered_obligations_passed: false,
                remaining_scope: String::new(),
            },
            semantic_contract_complete: false,
            remaining: "Full input domain".into(),
        };
        let mut gaps = Gaps::default();
        gaps.record(&row);
        assert_eq!(
            gaps.functions_without_confirmed_linked_behavior,
            ["Z3_example"]
        );
        assert_eq!(gaps.functions_with_unconfirmed_obligations, ["Z3_example"]);

        row.linked_consumer_exercised = true;
        let mut gaps = Gaps::default();
        gaps.record(&row);
        assert!(gaps.functions_without_confirmed_linked_behavior.is_empty());
        assert_eq!(gaps.functions_with_unconfirmed_obligations, ["Z3_example"]);

        row.linked_consumer_exercised = false;
        row.semantic_contract.obligations[0].passed = true;
        let mut gaps = Gaps::default();
        gaps.record(&row);
        assert!(gaps.functions_without_confirmed_linked_behavior.is_empty());
        assert_eq!(gaps.functions_without_linked_witness, ["Z3_example"]);
        assert!(gaps.functions_with_unconfirmed_obligations.is_empty());
    }
}
