// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed source and transcript inventory for the nine official theories.
//!
//! Theory declarations mix machine-readable `:sorts`/`:funs` entries with
//! prose `:sorts-description`/`:funs-description` signature schemas.  Both are
//! normative.  This validator authenticates the pinned registry snapshot,
//! owns every top-level field (including the historical singular `:sort` and
//! `:fun` spellings), expands every prose schema into a finite family catalog,
//! and gives each signature a positive typing, negative typing, and semantic
//! transcript.  Unknowns and unsupported theory features are recorded as
//! failures of replacement coverage; they are never silently skipped.

use super::reference_inventory::{self, RegistryTheoryDeclaration};
use super::*;
use ay_frontend::SExpr;

pub(super) const VALIDATOR_ID: &str = "builtin.theory-registry.v1";

const DIMENSION_ID: &str = "registry.theories";
const DEFAULT_TIMEOUT_SECS: u64 = 10;
const TOP_LEVEL_FIELD_COUNT: usize = 148;
const EMBEDDED_FIELD_COUNT: usize = 1;
const SOURCE_FIELD_COUNT: usize = TOP_LEVEL_FIELD_COUNT + EMBEDDED_FIELD_COUNT;
const MACHINE_SIGNATURE_COUNT: usize = 123;
/// Prose-signature families in [`description_catalog`], summed over every
/// `:sorts-description` / `:funs-description` occurrence of the nine theories:
/// FixedSizeBitVectors 1 + 18, FloatingPoint 2 + 40, Ints 1, Reals_Ints 1,
/// Strings 2. Both the runtime inventory (`description_signature_count`) and
/// `field_and_description_catalog_counts_are_closed` recompute the sum from the
/// catalog, so this constant is the closure check on it, not its source.
const DESCRIPTION_SIGNATURE_COUNT: usize = 65;
const SIGNATURE_COUNT: usize = MACHINE_SIGNATURE_COUNT + DESCRIPTION_SIGNATURE_COUNT;
const PROCESS_CASE_COUNT: usize = SIGNATURE_COUNT * 3;
const DETAILED_CASE_COUNT: usize = SOURCE_FIELD_COUNT + SIGNATURE_COUNT + PROCESS_CASE_COUNT;

#[derive(Clone, Debug)]
struct SourceSignature {
    id: String,
    declaration: String,
    source_field_sha256: String,
    witness: Witness,
}

#[derive(Clone, Debug)]
struct Witness {
    positive: String,
    negative: String,
    semantic: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProcessExpectation {
    ExactStdout(&'static str),
    Rejection,
}

#[derive(Debug)]
struct ProcessCase {
    id: String,
    input: Vec<u8>,
    expectation: ProcessExpectation,
    obligation: String,
}

impl ProcessCase {
    fn expected(&self) -> String {
        match self.expectation {
            ProcessExpectation::ExactStdout(stdout) => format!(
                "{}; stdout={stdout:?}; stderr=\"\"; exit=0",
                self.obligation
            ),
            ProcessExpectation::Rejection => format!(
                "{}; exactly one SMT-LIB `(error \"...\")` response; no verdict; stderr=\"\"; exit=0-or-1",
                self.obligation
            ),
        }
    }
}

#[derive(Debug)]
struct PreparedCampaign {
    catalog_rows: Vec<ValidatorCase>,
    process_cases: Vec<ProcessCase>,
}

#[derive(Debug, Eq, PartialEq)]
struct Execution {
    ay_sha256: String,
    resource_envelope: String,
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

struct ParsedField {
    key: String,
    occurrence: usize,
    value: Option<SExpr>,
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut snapshot_path: Option<PathBuf> = None;
    let mut ay_override: Option<PathBuf> = None;
    let mut timeout_secs = DEFAULT_TIMEOUT_SECS;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--receipt" => {
                index += 1;
                receipt_path = Some(PathBuf::from(
                    args.get(index).ok_or("--receipt needs a path")?,
                ));
            }
            "--source-snapshot" => {
                index += 1;
                snapshot_path = Some(PathBuf::from(
                    args.get(index).ok_or("--source-snapshot needs a path")?,
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
                return Err(format!("unknown theory-registry flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("theory-registry takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }

    let manifest = manifest.ok_or("theory-registry needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("theory-registry requires --receipt <path>")?;
    let snapshot_path = snapshot_path.ok_or("theory-registry requires --source-snapshot <path>")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let dimension = theory_dimension(&loaded.contract)?;
    if dimension.inventory.granularity != InventoryGranularity::ItemLevel {
        return Err("registry.theories must retain its closed item-level inventory".to_string());
    }
    let subject = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("theory-registry requires subject.ay_executable")?;
    let ay = ay_override.unwrap_or_else(|| artifact_path(&loaded.base, &subject.path));
    let source = reference_inventory::load_registry_theories(
        &loaded.contract,
        dimension,
        &loaded.base,
        Some(&snapshot_path),
    )?;
    let execution = execute(
        &ay,
        &subject.sha256,
        &source.declarations,
        Duration::from_secs(timeout_secs),
        loaded.contract.resource_envelope.as_deref(),
    )?;
    let output_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let validator_sha = sha256_file(&current_exe, "parity validator")?;
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: DIMENSION_ID.to_string(),
        requirement_ids: dimension
            .requirements
            .iter()
            .map(|row| row.id.clone())
            .collect(),
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: VALIDATOR_ID.to_string(),
            kind: ValidatorKind::TranscriptConformance,
            path: current_exe.to_string_lossy().into_owned(),
            sha256: validator_sha,
        },
        subject: ReceiptSubject {
            ay_executable_sha256: Some(execution.ay_sha256.clone()),
            ay_shared_library_sha256: loaded
                .contract
                .subject
                .ay_shared_library
                .as_ref()
                .map(|artifact| artifact.sha256.clone()),
        },
        z3_binary_sha256: None,
        z3_shared_library_sha256: None,
        reference_inputs: vec![source.binding],
        auxiliary_tools: Vec::new(),
        source_provenance: None,
        resource_envelope: Some(execution.resource_envelope.clone()),
        exhaustive: true,
        result: execution.result,
        cases: execution.cases,
        case_results: execution.case_results,
    };
    let bytes = pretty_json(&receipt)?;
    atomic_write_new(&receipt_path, &bytes)?;
    let receipt_sha = sha256_bytes(&bytes);
    println!(
        "theory-registry={} receipt={} sha256={}",
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        output_relative,
        receipt_sha
    );
    println!(
        "coverage=9-theories source-fields={SOURCE_FIELD_COUNT} machine-signatures={MACHINE_SIGNATURE_COUNT} description-signatures={DESCRIPTION_SIGNATURE_COUNT} transcript-cases={PROCESS_CASE_COUNT} detailed-cases={} catalog=closed",
        receipt.cases.total,
    );
    println!(
        "attach with: ay-z3-parity smtlib-conformance attach {} {} --out <new-manifest>",
        manifest.display(),
        receipt_path.display()
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
    let expected_ids = context
        .dimension
        .requirements
        .iter()
        .map(|row| row.id.clone())
        .collect::<Vec<_>>();
    if receipt.validator.kind != ValidatorKind::TranscriptConformance
        || context.dimension.id != DIMENSION_ID
        || receipt.requirement_ids != expected_ids
        || !receipt.exhaustive
        || receipt.z3_binary_sha256.is_some()
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
    {
        return Err(format!(
            "{VALIDATOR_ID} has invalid kind, dimension, coverage, exhaustive flag, or foreign bindings"
        ));
    }
    let [input] = receipt.reference_inputs.as_slice() else {
        return Err(format!(
            "{VALIDATOR_ID} requires exactly one authenticated registry snapshot"
        ));
    };
    if input.id != "smtlib-registry" || input.cohort != SourceCohort::SmtlibRegistry {
        return Err(format!(
            "{VALIDATOR_ID} is not bound to the authenticated SMT-LIB registry"
        ));
    }
    let declarations = reference_inventory::load_bound_registry_theories(
        input,
        context.manifest_dir,
        &canonical_profile(),
    )?;
    let prepared = prepare_campaign(&declarations)?;
    validate_recorded_shape(receipt, &prepared)?;
    if context.mode.replays_registered_validators() {
        let envelope = receipt
            .resource_envelope
            .as_deref()
            .ok_or("theory-registry receipt has no resource envelope")?;
        let parsed = parse_resource_envelope(envelope)?;
        if parsed.jobs != 1 {
            return Err("theory-registry receipts require a one-job resource envelope".to_string());
        }
        let subject = context
            .contract
            .subject
            .ay_executable
            .as_ref()
            .ok_or("theory-registry replay requires subject.ay_executable")?;
        let ay = artifact_path(context.manifest_dir, &subject.path);
        let live = execute(
            &ay,
            &subject.sha256,
            &declarations,
            parsed.timeout,
            Some(envelope),
        )?;
        if receipt.result != live.result
            || receipt.cases != live.cases
            || receipt.case_results != live.case_results
        {
            return Err(format!(
                "{VALIDATOR_ID} receipt does not match a fresh authenticated AY replay"
            ));
        }
    }
    Ok(())
}

fn theory_dimension(contract: &Contract) -> Result<&Dimension, String> {
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == DIMENSION_ID)
        .ok_or_else(|| "closed registry.theories dimension is missing".to_string())
}

fn execute(
    ay_source: &Path,
    expected_ay_sha256: &str,
    declarations: &[RegistryTheoryDeclaration],
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<Execution, String> {
    if timeout.is_zero() || timeout > Duration::from_hours(1) {
        return Err("theory-registry timeout must be between 1ns and 3600 seconds".to_string());
    }
    let prepared = prepare_campaign(declarations)?;
    let staged = stage_authenticated_executable(
        ay_source,
        expected_ay_sha256,
        "theory-registry AY executable",
    )?;
    let repo_root = locate_repo_root()?;
    let resources = PlannedResources::plan(
        &repo_root,
        1,
        "ay-z3-parity smtlib-conformance theory-registry",
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
                "live theory-registry resource envelope drift: expected {expected:?}, got {resource_envelope:?}"
            ));
        }
    }

    let mut rows = prepared.catalog_rows;
    for case in prepared.process_cases {
        let output = resources
            .run_external_transcript(
                &staged.path,
                ["--z3-mode", "--quiet", "-in"],
                &case.input,
                timeout,
                &format!("SMT-LIB theory conformance: {}", case.id),
            )
            .map_err(|error| error.to_string())?;
        rows.push(process_case_result(&case, output));
    }
    let post_sha = sha256_file(&staged.path, "staged AY after theory-registry run")?;
    if post_sha != expected_ay_sha256 {
        return Err("authenticated AY staging bytes changed during theory replay".to_string());
    }
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    let cases = case_counts_from_rows(&rows)?;
    let result = overall_validator_result(&rows);
    Ok(Execution {
        ay_sha256: expected_ay_sha256.to_string(),
        resource_envelope,
        result,
        cases,
        case_results: rows,
    })
}

fn prepare_campaign(
    declarations: &[RegistryTheoryDeclaration],
) -> Result<PreparedCampaign, String> {
    if declarations.len() != SMTLIB_THEORIES.len() {
        return Err(format!(
            "theory source count drift: expected {}, got {}",
            SMTLIB_THEORIES.len(),
            declarations.len()
        ));
    }
    let expected_names = SMTLIB_THEORIES
        .iter()
        .map(|(name, _)| *name)
        .collect::<Vec<_>>();
    let actual_names = declarations
        .iter()
        .map(|declaration| declaration.name.as_str())
        .collect::<Vec<_>>();
    if actual_names != expected_names {
        return Err("authenticated theory order differs from the closed catalog".to_string());
    }

    let mut catalog_rows = Vec::new();
    let mut signatures = Vec::new();
    let mut top_level_field_count = 0usize;
    let mut embedded_field_count = 0usize;
    let mut machine_signature_count = 0usize;
    let mut description_signature_count = 0usize;
    for declaration in declarations {
        let fields = parse_theory_fields(declaration)?;
        validate_field_shape(&declaration.name, &fields)?;
        top_level_field_count += fields.len();
        for field in &fields {
            let field_id = format!(
                "registry.theories.{}.source-field.{}.{}",
                declaration.name,
                field.key.trim_start_matches(':'),
                field.occurrence
            );
            let value = field
                .value
                .as_ref()
                .map_or_else(|| "<valueless>".to_string(), SExpr::to_raw_string);
            let field_sha256 = sha256_bytes(value.as_bytes());
            catalog_rows.push(source_catalog_row(
                declaration,
                &field_id,
                value.as_bytes(),
                format!(
                    "authenticated top-level field {}[{}] is explicitly owned",
                    field.key, field.occurrence
                ),
            ));
            match field.key.as_str() {
                ":sorts" | ":sort" | ":funs" | ":fun" => {
                    let (mut machine, embedded) =
                        machine_signatures(declaration, field, &field_sha256, &mut catalog_rows)?;
                    machine_signature_count += machine.len();
                    embedded_field_count += embedded;
                    signatures.append(&mut machine);
                }
                ":sorts-description" | ":funs-description" => {
                    let mut described = description_signatures(declaration, field, &field_sha256)?;
                    description_signature_count += described.len();
                    signatures.append(&mut described);
                }
                _ => {}
            }
        }
    }

    if top_level_field_count != TOP_LEVEL_FIELD_COUNT
        || embedded_field_count != EMBEDDED_FIELD_COUNT
        || top_level_field_count + embedded_field_count != SOURCE_FIELD_COUNT
        || machine_signature_count != MACHINE_SIGNATURE_COUNT
        || description_signature_count != DESCRIPTION_SIGNATURE_COUNT
        || signatures.len() != SIGNATURE_COUNT
    {
        return Err(format!(
            "closed theory source inventory drift: top-level-fields={top_level_field_count}/{TOP_LEVEL_FIELD_COUNT}, embedded-fields={embedded_field_count}/{EMBEDDED_FIELD_COUNT}, machine-signatures={machine_signature_count}/{MACHINE_SIGNATURE_COUNT}, description-signatures={description_signature_count}/{DESCRIPTION_SIGNATURE_COUNT}"
        ));
    }

    signatures.sort_by(|left, right| left.id.cmp(&right.id));
    for pair in signatures.windows(2) {
        if pair[0].id >= pair[1].id {
            return Err(format!(
                "theory signature catalog contains duplicate id {:?}",
                pair[0].id
            ));
        }
    }
    let signature_ids = signatures
        .iter()
        .map(|signature| signature.id.as_str())
        .collect::<Vec<_>>()
        .join("\n");
    let witness_catalog_sha256 = sha256_bytes(signature_ids.as_bytes());
    let mut process_cases = Vec::with_capacity(PROCESS_CASE_COUNT);
    for signature in signatures {
        let declaration = declarations
            .iter()
            .find(|declaration| {
                signature
                    .id
                    .starts_with(&format!("registry.theories.{}.", declaration.name))
            })
            .ok_or_else(|| format!("signature {} has no source declaration", signature.id))?;
        let signature_bytes = grounded_bytes(
            declaration,
            &signature.source_field_sha256,
            &signature.id,
            signature.declaration.as_bytes(),
        );
        catalog_rows.push(ValidatorCase {
            id: format!("{}.catalog", signature.id),
            input_sha256: sha256_bytes(&signature_bytes),
            expected: format!(
                "authenticated full signature is owned by witness catalog {witness_catalog_sha256}"
            ),
            observed: format!(
                "path={}; git_blob={}; content_sha256={}; source-field-sha256={}; signature={}",
                declaration.path,
                declaration.git_blob,
                declaration.content_sha256,
                signature.source_field_sha256,
                signature.declaration,
            ),
            stdout: None,
            stderr: None,
            exit_code: None,
            process: None,
            outcome: ValidatorCaseOutcome::Pass,
        });
        process_cases.extend(process_cases_for_signature(declaration, &signature));
    }
    if process_cases.len() != PROCESS_CASE_COUNT
        || catalog_rows.len() != SOURCE_FIELD_COUNT + SIGNATURE_COUNT
        || catalog_rows.len() + process_cases.len() != DETAILED_CASE_COUNT
    {
        return Err(format!(
            "closed theory detailed-case drift: catalog={}, processes={}, total={}",
            catalog_rows.len(),
            process_cases.len(),
            catalog_rows.len() + process_cases.len()
        ));
    }
    process_cases.sort_by(|left, right| left.id.cmp(&right.id));
    for pair in process_cases.windows(2) {
        if pair[0].id >= pair[1].id {
            return Err("generated theory transcript IDs are not unique".to_string());
        }
    }
    catalog_rows.sort_by(|left, right| left.id.cmp(&right.id));
    Ok(PreparedCampaign {
        catalog_rows,
        process_cases,
    })
}

fn parse_theory_fields(
    declaration: &RegistryTheoryDeclaration,
) -> Result<Vec<ParsedField>, String> {
    let parsed = ay_frontend::sexp::parse_sexp(&declaration.content)
        .map_err(|error| format!("parsing authenticated {}: {error}", declaration.path))?;
    let items = parsed
        .as_list()
        .ok_or_else(|| format!("{} is not one registry list", declaration.path))?;
    if items.len() < 3
        || !items[0].is_symbol("theory")
        || items[1].as_symbol() != Some(declaration.name.as_str())
    {
        return Err(format!(
            "{} has an invalid theory declaration header",
            declaration.path
        ));
    }
    let mut fields = Vec::new();
    let mut counts = BTreeMap::<String, usize>::new();
    let mut index = 2usize;
    while index < items.len() {
        let SExpr::Keyword(key) = &items[index] else {
            return Err(format!(
                "{} contains an unowned top-level non-keyword at item {index}",
                declaration.path
            ));
        };
        let count = counts.entry(key.clone()).or_default();
        let occurrence = *count;
        *count += 1;
        let value = if items
            .get(index + 1)
            .is_some_and(|value| !matches!(value, SExpr::Keyword(_)))
        {
            index += 2;
            Some(items[index - 1].clone())
        } else {
            index += 1;
            None
        };
        fields.push(ParsedField {
            key: key.clone(),
            occurrence,
            value,
        });
    }
    Ok(fields)
}

fn expected_field_shape(theory: &str) -> Result<Vec<(&'static str, usize)>, String> {
    let metadata = [
        (":date", 1),
        (":last-updated", 1),
        (":smt-lib-release", 1),
        (":smt-lib-version", 1),
        (":update-history", 1),
        (":written-by", 1),
    ];
    let mut shape = metadata.to_vec();
    match theory {
        "ArraysEx" => shape.extend([
            (":definition", 1),
            (":funs", 1),
            (":notes", 1),
            (":sorts", 1),
            (":values", 1),
        ]),
        "Core" => shape.extend([
            (":definition", 1),
            (":funs", 1),
            (":sorts", 1),
            (":values", 1),
        ]),
        "FixedSizeBitVectors" => shape.extend([
            (":definition", 1),
            (":funs-description", 6),
            (":notes", 2),
            (":sorts-description", 1),
            (":values", 1),
        ]),
        "FloatingPoint" => shape.extend([
            (":definition", 1),
            (":funs", 1),
            (":funs-description", 8),
            (":note", 4),
            (":notes", 7),
            (":sort", 1),
            (":sorts", 1),
            (":sorts-description", 2),
            (":values", 1),
        ]),
        "HO-Core" => shape.extend([
            (":definition", 1),
            (":funs", 1),
            (":notes", 1),
            (":sorts", 1),
            (":values", 1),
        ]),
        "Ints" => shape.extend([
            (":definition", 1),
            (":funs", 1),
            (":funs-description", 1),
            (":notes", 2),
            (":sorts", 1),
            (":values", 1),
        ]),
        "Reals" => shape.extend([
            (":definition", 1),
            (":funs", 1),
            (":notes", 2),
            (":sorts", 1),
            (":values", 1),
        ]),
        "Reals_Ints" => shape.extend([
            (":definition", 1),
            (":funs", 1),
            (":funs-description", 1),
            (":notes", 2),
            (":sorts", 1),
            (":values", 1),
        ]),
        "Strings" => {
            shape.retain(|(key, _)| *key != ":smt-lib-release");
            shape.extend([
                (":definition", 1),
                (":fun", 2),
                (":funs", 2),
                (":funs-description", 2),
                (":notes", 15),
                (":sorts", 1),
                (":values", 1),
            ]);
        }
        other => return Err(format!("unowned theory field shape {other:?}")),
    }
    shape.sort_by_key(|(key, _)| *key);
    Ok(shape)
}

fn validate_field_shape(theory: &str, fields: &[ParsedField]) -> Result<(), String> {
    let mut actual = BTreeMap::<&str, usize>::new();
    for field in fields {
        *actual.entry(field.key.as_str()).or_default() += 1;
    }
    let actual = actual.into_iter().collect::<Vec<_>>();
    let expected = expected_field_shape(theory)?;
    if actual != expected {
        return Err(format!(
            "{theory} top-level source-field drift: source={actual:?}, catalog={expected:?}"
        ));
    }
    for field in fields {
        let valueless = field.value.is_none();
        if valueless != (theory == "HO-Core" && field.key == ":update-history") {
            return Err(format!(
                "{theory} {}[{}] has unowned value presence",
                field.key, field.occurrence
            ));
        }
        match field.key.as_str() {
            ":sorts" | ":sort" | ":funs" | ":fun" => {
                if field
                    .value
                    .as_ref()
                    .is_none_or(|value| value.as_list().is_none())
                {
                    return Err(format!(
                        "{theory} {}[{}] is not a machine declaration list",
                        field.key, field.occurrence
                    ));
                }
            }
            ":sorts-description" | ":funs-description" | ":definition" | ":values" | ":notes"
            | ":note" => {
                if !matches!(field.value.as_ref(), Some(SExpr::String(_))) {
                    return Err(format!(
                        "{theory} {}[{}] is not a prose string",
                        field.key, field.occurrence
                    ));
                }
            }
            ":update-history" if theory == "HO-Core" => {}
            ":smt-lib-version" | ":smt-lib-release" | ":written-by" | ":date" | ":last-updated"
            | ":update-history" => {
                if field.value.is_none() {
                    return Err(format!(
                        "{theory} {}[{}] unexpectedly has no value",
                        field.key, field.occurrence
                    ));
                }
            }
            other => return Err(format!("{theory} has unowned source field {other:?}")),
        }
    }
    Ok(())
}

fn machine_signatures(
    declaration: &RegistryTheoryDeclaration,
    field: &ParsedField,
    field_sha256: &str,
    catalog_rows: &mut Vec<ValidatorCase>,
) -> Result<(Vec<SourceSignature>, usize), String> {
    let items = field
        .value
        .as_ref()
        .and_then(SExpr::as_list)
        .ok_or_else(|| format!("{} {} is not a list", declaration.name, field.key))?;
    let mut signatures = Vec::new();
    let mut embedded = 0usize;
    let mut index = 0usize;
    while index < items.len() {
        match &items[index] {
            SExpr::List(_) => {
                let raw = items[index].to_raw_string();
                let symbol = signature_symbol(&items[index])?;
                let signature_id = format!(
                    "registry.theories.{}.machine.{}.{}.{}.{}",
                    declaration.name,
                    field.key.trim_start_matches(':'),
                    field.occurrence,
                    signatures.len(),
                    id_component(&symbol),
                );
                let witness = machine_witness(&declaration.name, &symbol, &raw)?;
                signatures.push(SourceSignature {
                    id: signature_id,
                    declaration: raw,
                    source_field_sha256: field_sha256.to_string(),
                    witness,
                });
                index += 1;
            }
            SExpr::Keyword(key)
                if declaration.name == "Strings"
                    && field.key == ":fun"
                    && field.occurrence == 1
                    && key == ":notes" =>
            {
                let Some(SExpr::String(value)) = items.get(index + 1) else {
                    return Err("Strings embedded :notes has no string value".to_string());
                };
                let id = "registry.theories.Strings.source-field.fun.1.embedded.notes.0";
                catalog_rows.push(source_catalog_row(
                    declaration,
                    id,
                    value.as_bytes(),
                    "authenticated embedded :notes field is explicitly owned".to_string(),
                ));
                embedded += 1;
                index += 2;
            }
            other => {
                return Err(format!(
                    "{} {}[{}] contains unowned machine-list item {}",
                    declaration.name,
                    field.key,
                    field.occurrence,
                    other.to_raw_string()
                ))
            }
        }
    }
    Ok((signatures, embedded))
}

fn signature_symbol(signature: &SExpr) -> Result<String, String> {
    let items = signature
        .as_list()
        .ok_or("machine signature is not a list")?;
    let head = if items.first().is_some_and(|head| head.is_symbol("par")) {
        items
            .get(2)
            .and_then(SExpr::as_list)
            .and_then(|inner| inner.first())
            .ok_or("polymorphic signature has no declaration head")?
    } else {
        items.first().ok_or("empty machine signature")?
    };
    match head {
        SExpr::Symbol(symbol) => Ok(symbol.clone()),
        SExpr::List(indexed) => indexed
            .get(1)
            .and_then(SExpr::as_symbol)
            .map(str::to_string)
            .ok_or_else(|| "indexed signature has no symbol".to_string()),
        other => Err(format!(
            "machine signature has unowned head {}",
            other.to_raw_string()
        )),
    }
}

fn id_component(value: &str) -> String {
    value
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || matches!(character, '-' | '_' | '.') {
                character
            } else {
                '_'
            }
        })
        .collect()
}

fn source_catalog_row(
    declaration: &RegistryTheoryDeclaration,
    id: &str,
    value: &[u8],
    obligation: String,
) -> ValidatorCase {
    let input = grounded_bytes(declaration, &declaration.content_sha256, id, value);
    ValidatorCase {
        id: id.to_string(),
        input_sha256: sha256_bytes(&input),
        expected: obligation,
        observed: format!(
            "path={}; git_blob={}; content_sha256={}; value_sha256={}",
            declaration.path,
            declaration.git_blob,
            declaration.content_sha256,
            sha256_bytes(value)
        ),
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome: ValidatorCaseOutcome::Pass,
    }
}

fn grounded_bytes(
    declaration: &RegistryTheoryDeclaration,
    field_sha256: &str,
    id: &str,
    value: &[u8],
) -> Vec<u8> {
    let mut bytes = format!(
        "{}\n{}\n{}\n{}\n{}\n",
        declaration.path, declaration.git_blob, declaration.content_sha256, field_sha256, id
    )
    .into_bytes();
    bytes.extend_from_slice(value);
    bytes
}

fn process_cases_for_signature(
    declaration: &RegistryTheoryDeclaration,
    signature: &SourceSignature,
) -> [ProcessCase; 3] {
    let positive_id = format!("{}.typing.positive", signature.id);
    let negative_id = format!("{}.typing.negative", signature.id);
    let semantic_id = format!("{}.semantic", signature.id);
    [
        ProcessCase {
            input: theory_script(
                declaration,
                signature,
                &positive_id,
                &signature.witness.positive,
                true,
            )
            .into_bytes(),
            id: positive_id,
            expectation: ProcessExpectation::ExactStdout("sat\n"),
            obligation: format!(
                "full signature {} accepts a well-sorted application",
                signature.declaration
            ),
        },
        ProcessCase {
            input: theory_script(
                declaration,
                signature,
                &negative_id,
                &signature.witness.negative,
                false,
            )
            .into_bytes(),
            id: negative_id,
            expectation: ProcessExpectation::Rejection,
            obligation: format!(
                "full signature {} rejects its cataloged arity, sort, or index violation",
                signature.declaration
            ),
        },
        ProcessCase {
            input: theory_script(
                declaration,
                signature,
                &semantic_id,
                &signature.witness.semantic,
                true,
            )
            .into_bytes(),
            id: semantic_id,
            expectation: ProcessExpectation::ExactStdout("unsat\n"),
            obligation: format!(
                "full signature {} satisfies its pinned semantic witness",
                signature.declaration
            ),
        },
    ]
}

fn theory_script(
    declaration: &RegistryTheoryDeclaration,
    signature: &SourceSignature,
    case_id: &str,
    body: &str,
    check_sat: bool,
) -> String {
    let suffix = if check_sat {
        "(check-sat)\n(exit)\n"
    } else {
        "(exit)\n"
    };
    format!(
        "; ay-smtlib-theory-catalog/v1\n; source-path={}\n; source-git-blob={}\n; source-content-sha256={}\n; source-field-sha256={}\n; signature={}\n; case={}\n(set-option :print-success false)\n{}{}",
        declaration.path,
        declaration.git_blob,
        declaration.content_sha256,
        signature.source_field_sha256,
        signature.declaration,
        case_id,
        body,
        suffix,
    )
}

fn term_witness(term: &str, invalid_term: &str, semantic_assertion: &str) -> Witness {
    Witness {
        positive: format!("(assert (= {term} {term}))\n"),
        negative: format!("(assert (= {invalid_term} {invalid_term}))\n"),
        semantic: format!("{semantic_assertion}\n"),
    }
}

fn sort_witness(sort: &str, invalid_sort: &str) -> Witness {
    Witness {
        positive: format!(
            "(declare-const theory_sort_witness {sort})\n(assert (= theory_sort_witness theory_sort_witness))\n"
        ),
        negative: format!("(declare-const theory_bad_sort_witness {invalid_sort})\n"),
        semantic: format!(
            "(declare-const theory_semantic_sort_witness {sort})\n(assert (distinct theory_semantic_sort_witness theory_semantic_sort_witness))\n"
        ),
    }
}

fn machine_witness(theory: &str, symbol: &str, raw: &str) -> Result<Witness, String> {
    let sort = match (theory, raw) {
        ("ArraysEx", "(Array 2)") => Some(array_sort_witness()),
        ("Core", "(Bool 0)") => Some(bool_sort_witness()),
        ("FloatingPoint", "(RoundingMode 0)") => {
            Some(sort_witness("RoundingMode", "(RoundingMode Bool)"))
        }
        ("FloatingPoint", "(Real 0)") => Some(sort_witness("Real", "(Real Bool)")),
        ("FloatingPoint", "(Float16 0)") => Some(fp_alias_sort_witness("Float16", 5, 11)),
        ("FloatingPoint", "(Float32 0)") => Some(fp_alias_sort_witness("Float32", 8, 24)),
        ("FloatingPoint", "(Float64 0)") => Some(fp_alias_sort_witness("Float64", 11, 53)),
        ("FloatingPoint", "(Float128 0)") => Some(fp_alias_sort_witness("Float128", 15, 113)),
        ("HO-Core", "(-> 2 :right-assoc)") => Some(ho_sort_witness()),
        ("Ints", "(Int 0)") | ("Reals_Ints", "(Int 0)") => Some(sort_witness("Int", "(Int Bool)")),
        ("Reals", "(Real 0)") | ("Reals_Ints", "(Real 0)") => {
            Some(sort_witness("Real", "(Real Bool)"))
        }
        ("Strings", "(String 0)") => Some(sort_witness("String", "(String Bool)")),
        ("Strings", "(RegLan 0)") => Some(sort_witness("RegLan", "(RegLan Bool)")),
        ("Strings", "(Int 0)") => Some(sort_witness("Int", "(Int Bool)")),
        _ => None,
    };
    if let Some(witness) = sort {
        return Ok(witness);
    }
    let witness = match theory {
        "ArraysEx" => array_machine_witness(symbol),
        "Core" => core_machine_witness(symbol),
        "FloatingPoint" => rounding_mode_witness(symbol),
        "HO-Core" => ho_machine_witness(symbol),
        "Ints" | "Reals" | "Reals_Ints" => arithmetic_machine_witness(theory, symbol, raw),
        "Strings" => string_machine_witness(symbol),
        other => return Err(format!("unowned machine theory {other:?}")),
    };
    witness.ok_or_else(|| format!("unowned machine signature in {theory}: {raw}"))
}

fn fp_alias_sort_witness(alias: &str, eb: usize, sb: usize) -> Witness {
    Witness {
        positive: format!(
            "(define-const theory_sort_witness {alias} (_ +zero {eb} {sb}))\n(assert (= theory_sort_witness theory_sort_witness))\n"
        ),
        negative: format!("(declare-const theory_bad_sort_witness ({alias} Bool))\n"),
        semantic: format!(
            "(define-const theory_semantic_sort_witness {alias} (_ +zero {eb} {sb}))\n(assert (distinct theory_semantic_sort_witness (_ +zero {eb} {sb})))\n"
        ),
    }
}

fn array_sort_witness() -> Witness {
    Witness {
        positive: "(declare-const theory_sort_witness (Array Bool Int))\n(assert (= theory_sort_witness theory_sort_witness))\n".to_string(),
        negative: "(declare-const theory_bad_sort_witness (Array Bool))\n".to_string(),
        semantic: "(declare-const a (Array Bool Int))\n(declare-const b (Array Bool Int))\n(assert (forall ((i Bool)) (= (select a i) (select b i))))\n(assert (distinct a b))\n".to_string(),
    }
}

fn bool_sort_witness() -> Witness {
    Witness {
        positive: "(declare-const theory_sort_witness Bool)\n(assert (= theory_sort_witness theory_sort_witness))\n".to_string(),
        negative: "(declare-const theory_bad_sort_witness (Bool Bool))\n".to_string(),
        semantic: "(declare-const b Bool)\n(assert (distinct b true))\n(assert (distinct b false))\n".to_string(),
    }
}

fn ho_sort_witness() -> Witness {
    Witness {
        positive: "(declare-const theory_sort_witness (-> Bool Bool))\n(assert (= theory_sort_witness theory_sort_witness))\n".to_string(),
        negative: "(declare-const theory_bad_sort_witness (-> Bool))\n".to_string(),
        semantic: "(declare-const f (-> Bool Bool))\n(declare-const g (-> Bool Bool))\n(assert (forall ((x Bool)) (= (@ f x) (@ g x))))\n(assert (distinct f g))\n".to_string(),
    }
}

fn array_machine_witness(symbol: &str) -> Option<Witness> {
    match symbol {
        "select" => Some(Witness {
            positive: "(declare-const a (Array Bool Int))\n(assert (= (select a true) (select a true)))\n".to_string(),
            negative: "(declare-const a (Array Bool Int))\n(assert (= (select a 0) 0))\n".to_string(),
            semantic: "(declare-const a (Array Bool Int))\n(assert (distinct (select (store a true 7) true) 7))\n".to_string(),
        }),
        "store" => Some(Witness {
            positive: "(declare-const a (Array Bool Int))\n(assert (= (store a true 7) (store a true 7)))\n".to_string(),
            negative: "(declare-const a (Array Bool Int))\n(assert (= (store a 0 7) a))\n".to_string(),
            semantic: "(declare-const a (Array Bool Int))\n(assert (distinct (select (store a true 7) true) 7))\n".to_string(),
        }),
        _ => None,
    }
}

fn core_machine_witness(symbol: &str) -> Option<Witness> {
    match symbol {
        "true" => Some(term_witness("true", "(true false)", "(assert (not true))")),
        "false" => Some(term_witness("false", "(false true)", "(assert false)")),
        "not" => Some(term_witness(
            "(not true)",
            "(not 0)",
            "(assert (distinct (not true) false))",
        )),
        "=>" => Some(term_witness(
            "(=> true false true)",
            "(=> true 0)",
            "(assert (not (=> true false true)))",
        )),
        "and" => Some(term_witness(
            "(and true true true)",
            "(and true 0)",
            "(assert (not (and true true true)))",
        )),
        "or" => Some(term_witness(
            "(or false false false)",
            "(or false 0)",
            "(assert (or false false false))",
        )),
        "xor" => Some(term_witness(
            "(xor true true false)",
            "(xor true 0)",
            "(assert (xor true true false))",
        )),
        "=" => Some(term_witness("(= 1 1 1)", "(=)", "(assert (not (= 1 1 1)))")),
        "distinct" => Some(term_witness(
            "(distinct 1 2 3)",
            "(distinct)",
            "(assert (not (distinct 1 2 3)))",
        )),
        "ite" => Some(term_witness(
            "(ite true 1 2)",
            "(ite 0 1 2)",
            "(assert (distinct (ite true 1 2) 1))",
        )),
        _ => None,
    }
}

fn ho_machine_witness(symbol: &str) -> Option<Witness> {
    match symbol {
        "@" => Some(term_witness(
            "(@ (lambda ((x Bool)) x) true)",
            "(@ (lambda ((x Bool)) x) 0)",
            "(assert (distinct (@ (lambda ((x Bool)) x) true) true))",
        )),
        _ => None,
    }
}

fn rounding_mode_witness(symbol: &str) -> Option<Witness> {
    let (term, equivalent) = match symbol {
        "roundNearestTiesToEven" | "RNE" => (
            symbol,
            if symbol == "RNE" {
                "roundNearestTiesToEven"
            } else {
                "RNE"
            },
        ),
        "roundNearestTiesToAway" | "RNA" => (
            symbol,
            if symbol == "RNA" {
                "roundNearestTiesToAway"
            } else {
                "RNA"
            },
        ),
        "roundTowardPositive" | "RTP" => (
            symbol,
            if symbol == "RTP" {
                "roundTowardPositive"
            } else {
                "RTP"
            },
        ),
        "roundTowardNegative" | "RTN" => (
            symbol,
            if symbol == "RTN" {
                "roundTowardNegative"
            } else {
                "RTN"
            },
        ),
        "roundTowardZero" | "RTZ" => (
            symbol,
            if symbol == "RTZ" {
                "roundTowardZero"
            } else {
                "RTZ"
            },
        ),
        _ => return None,
    };
    Some(term_witness(
        term,
        &format!("({term} true)"),
        &format!("(assert (distinct {term} {equivalent}))"),
    ))
}

fn arithmetic_machine_witness(theory: &str, symbol: &str, raw: &str) -> Option<Witness> {
    let real = raw.contains(" Real") || symbol == "DECIMAL" || theory == "Reals";
    let one = if real { "1.0" } else { "1" };
    let two = if real { "2.0" } else { "2" };
    let three = if real { "3.0" } else { "3" };
    match symbol {
        "NUMERAL" => Some(term_witness(
            "7",
            "(_ numeral bad)",
            "(assert (distinct 7 (+ 3 4)))",
        )),
        "DECIMAL" => Some(term_witness(
            "1.25",
            "1.bad",
            "(assert (distinct 1.25 (/ 5.0 4.0)))",
        )),
        "-" if raw == "(- Int Int)" => Some(term_witness(
            "(- 3)",
            "(-)",
            "(assert (distinct (- 3) (- 0 3)))",
        )),
        "-" if raw == "(- Real Real)" => Some(term_witness(
            "(- 3.0)",
            "(-)",
            "(assert (distinct (- 3.0) (- 0.0 3.0)))",
        )),
        "-" => Some(term_witness(
            &format!("(- {three} {two} {one})"),
            "(-)",
            &format!("(assert (distinct (- {three} {two} {one}) 0.0))")
                .replace("0.0", if real { "0.0" } else { "0" }),
        )),
        "+" => Some(term_witness(
            &format!("(+ {one} {two} {three})"),
            "(+)",
            &format!("(assert (distinct (+ {one} {two} {three}) 6.0))")
                .replace("6.0", if real { "6.0" } else { "6" }),
        )),
        "*" => Some(term_witness(
            &format!("(* {one} {two} {three})"),
            "(*)",
            &format!("(assert (distinct (* {one} {two} {three}) 6.0))")
                .replace("6.0", if real { "6.0" } else { "6" }),
        )),
        "**" => Some(term_witness(
            "(** 3 2)",
            "(** 3 true)",
            "(assert (distinct (** 3 2) 9))",
        )),
        "div" => Some(term_witness(
            "(div 7 3 (- 2))",
            "(div)",
            "(assert (distinct (div 7 3) 2))",
        )),
        "mod" => Some(term_witness(
            "(mod (- 7) 3)",
            "(mod 7)",
            "(assert (distinct (mod (- 7) 3) 2))",
        )),
        "abs" => Some(term_witness(
            "(abs (- 7))",
            "(abs)",
            "(assert (distinct (abs (- 7)) 7))",
        )),
        "/" => Some(term_witness(
            "(/ 8.0 2.0 2.0)",
            "(/)",
            "(assert (distinct (/ 8.0 2.0 2.0) 2.0))",
        )),
        "<=" => Some(term_witness(
            &format!("(<= {one} {two} {three})"),
            "(<=)",
            &format!("(assert (not (<= {one} {two} {three})))"),
        )),
        "<" => Some(term_witness(
            &format!("(< {one} {two} {three})"),
            "(<)",
            &format!("(assert (not (< {one} {two} {three})))"),
        )),
        ">=" => Some(term_witness(
            &format!("(>= {three} {two} {one})"),
            "(>=)",
            &format!("(assert (not (>= {three} {two} {one})))"),
        )),
        ">" => Some(term_witness(
            &format!("(> {three} {two} {one})"),
            "(>)",
            &format!("(assert (not (> {three} {two} {one})))"),
        )),
        "to_real" => Some(term_witness(
            "(to_real 3)",
            "(to_real)",
            "(assert (distinct (to_real 3) 3.0))",
        )),
        "to_int" => Some(term_witness(
            "(to_int 3.7)",
            "(to_int)",
            "(assert (distinct (to_int (- 1.3)) (- 2)))",
        )),
        "is_int" => Some(term_witness(
            "(is_int 3.0)",
            "(is_int)",
            "(assert (not (is_int 3.0)))",
        )),
        _ => None,
    }
}

fn string_machine_witness(symbol: &str) -> Option<Witness> {
    let witness = match symbol {
        "str.++" => term_witness(
            "(str.++ \"a\" \"b\" \"c\")",
            "(str.++ \"a\" 0)",
            "(assert (distinct (str.++ \"a\" \"b\" \"c\") \"abc\"))",
        ),
        "str.len" => term_witness(
            "(str.len \"abc\")",
            "(str.len 0)",
            "(assert (distinct (str.len \"abc\") 3))",
        ),
        "str.<" => term_witness(
            "(str.< \"a\" \"b\" \"c\")",
            "(str.< \"a\" 0)",
            "(assert (not (str.< \"a\" \"b\" \"c\")))",
        ),
        "str.to_re" => term_witness(
            "(str.to_re \"a\")",
            "(str.to_re 0)",
            "(assert (not (str.in_re \"a\" (str.to_re \"a\"))))",
        ),
        "str.in_re" => term_witness(
            "(str.in_re \"a\" (str.to_re \"a\"))",
            "(str.in_re 0 (str.to_re \"a\"))",
            "(assert (not (str.in_re \"a\" (str.to_re \"a\"))))",
        ),
        "re.none" => term_witness(
            "re.none",
            "(re.none true)",
            "(assert (str.in_re \"a\" re.none))",
        ),
        "re.all" => term_witness(
            "re.all",
            "(re.all true)",
            "(assert (not (str.in_re \"anything\" re.all)))",
        ),
        "re.allchar" => term_witness(
            "re.allchar",
            "(re.allchar true)",
            "(assert (not (str.in_re \"a\" re.allchar)))",
        ),
        "re.++" => term_witness(
            "(re.++ (str.to_re \"a\") (str.to_re \"b\") (str.to_re \"c\"))",
            "(re.++ (str.to_re \"a\") 0)",
            "(assert (not (str.in_re \"abc\" (re.++ (str.to_re \"a\") (str.to_re \"b\") (str.to_re \"c\")))))",
        ),
        "re.union" => term_witness(
            "(re.union (str.to_re \"a\") (str.to_re \"b\") (str.to_re \"c\"))",
            "(re.union (str.to_re \"a\") 0)",
            "(assert (not (str.in_re \"b\" (re.union (str.to_re \"a\") (str.to_re \"b\") (str.to_re \"c\")))))",
        ),
        "re.inter" => term_witness(
            "(re.inter re.all (str.to_re \"a\") re.all)",
            "(re.inter re.all 0)",
            "(assert (not (str.in_re \"a\" (re.inter re.all (str.to_re \"a\") re.all))))",
        ),
        "re.*" => term_witness(
            "(re.* (str.to_re \"a\"))",
            "(re.* 0)",
            "(assert (not (str.in_re \"aaa\" (re.* (str.to_re \"a\")))))",
        ),
        "str.<=" => term_witness(
            "(str.<= \"a\" \"a\" \"b\")",
            "(str.<= \"a\" 0)",
            "(assert (not (str.<= \"a\" \"a\" \"b\")))",
        ),
        "str.at" => term_witness(
            "(str.at \"abc\" 1)",
            "(str.at \"abc\" true)",
            "(assert (distinct (str.at \"abc\" 1) \"b\"))",
        ),
        "str.substr" => term_witness(
            "(str.substr \"abcd\" 1 2)",
            "(str.substr \"abcd\" true 2)",
            "(assert (distinct (str.substr \"abcd\" 1 2) \"bc\"))",
        ),
        "str.prefixof" => term_witness(
            "(str.prefixof \"ab\" \"abc\")",
            "(str.prefixof 0 \"abc\")",
            "(assert (not (str.prefixof \"ab\" \"abc\")))",
        ),
        "str.suffixof" => term_witness(
            "(str.suffixof \"bc\" \"abc\")",
            "(str.suffixof 0 \"abc\")",
            "(assert (not (str.suffixof \"bc\" \"abc\")))",
        ),
        "str.contains" => term_witness(
            "(str.contains \"abc\" \"b\")",
            "(str.contains 0 \"b\")",
            "(assert (not (str.contains \"abc\" \"b\")))",
        ),
        "str.indexof" => term_witness(
            "(str.indexof \"abcabc\" \"bc\" 0)",
            "(str.indexof \"abc\" \"b\" true)",
            "(assert (distinct (str.indexof \"abcabc\" \"bc\" 0) 1))",
        ),
        "str.replace" => term_witness(
            "(str.replace \"abcabc\" \"ab\" \"X\")",
            "(str.replace \"abc\" 0 \"X\")",
            "(assert (distinct (str.replace \"abcabc\" \"ab\" \"X\") \"Xcabc\"))",
        ),
        "str.replace_all" => term_witness(
            "(str.replace_all \"abcabc\" \"ab\" \"X\")",
            "(str.replace_all \"abc\" 0 \"X\")",
            "(assert (distinct (str.replace_all \"abcabc\" \"ab\" \"X\") \"XcXc\"))",
        ),
        "str.replace_re" => term_witness(
            "(str.replace_re \"abc\" (str.to_re \"b\") \"X\")",
            "(str.replace_re \"abc\" 0 \"X\")",
            "(assert (distinct (str.replace_re \"abc\" (str.to_re \"b\") \"X\") \"aXc\"))",
        ),
        "str.replace_re_all" => term_witness(
            "(str.replace_re_all \"aba\" (str.to_re \"a\") \"X\")",
            "(str.replace_re_all \"aba\" 0 \"X\")",
            "(assert (distinct (str.replace_re_all \"aba\" (str.to_re \"a\") \"X\") \"XbX\"))",
        ),
        "re.comp" => term_witness(
            "(re.comp (str.to_re \"a\"))",
            "(re.comp 0)",
            "(assert (str.in_re \"a\" (re.comp (str.to_re \"a\"))))",
        ),
        "re.diff" => term_witness(
            "(re.diff re.all (str.to_re \"a\") (str.to_re \"b\"))",
            "(re.diff re.all 0)",
            "(assert (str.in_re \"a\" (re.diff re.all (str.to_re \"a\") (str.to_re \"b\"))))",
        ),
        "re.+" => term_witness(
            "(re.+ (str.to_re \"a\"))",
            "(re.+ 0)",
            "(assert (not (str.in_re \"aa\" (re.+ (str.to_re \"a\")))))",
        ),
        "re.opt" => term_witness(
            "(re.opt (str.to_re \"a\"))",
            "(re.opt 0)",
            "(assert (not (str.in_re \"\" (re.opt (str.to_re \"a\")))))",
        ),
        "re.range" => term_witness(
            "(re.range \"a\" \"c\")",
            "(re.range 0 \"c\")",
            "(assert (not (str.in_re \"b\" (re.range \"a\" \"c\"))))",
        ),
        "re.^" => term_witness(
            "((_ re.^ 2) (str.to_re \"a\"))",
            "((_ re.^ bad) (str.to_re \"a\"))",
            "(assert (not (str.in_re \"aa\" ((_ re.^ 2) (str.to_re \"a\")))))",
        ),
        "re.loop" => term_witness(
            "((_ re.loop 2 3) (str.to_re \"a\"))",
            "((_ re.loop bad 3) (str.to_re \"a\"))",
            "(assert (not (str.in_re \"aaa\" ((_ re.loop 2 3) (str.to_re \"a\")))))",
        ),
        "str.is_digit" => term_witness(
            "(str.is_digit \"7\")",
            "(str.is_digit 7)",
            "(assert (not (str.is_digit \"7\")))",
        ),
        "str.to_code" => term_witness(
            "(str.to_code \"A\")",
            "(str.to_code 0)",
            "(assert (distinct (str.to_code \"A\") 65))",
        ),
        "str.from_code" => term_witness(
            "(str.from_code 65)",
            "(str.from_code true)",
            "(assert (distinct (str.from_code 65) \"A\"))",
        ),
        "str.to_int" => term_witness(
            "(str.to_int \"00123\")",
            "(str.to_int 123)",
            "(assert (distinct (str.to_int \"00123\") 123))",
        ),
        "str.from_int" => term_witness(
            "(str.from_int 123)",
            "(str.from_int true)",
            "(assert (distinct (str.from_int 123) \"123\"))",
        ),
        _ => return None,
    };
    Some(witness)
}

fn description_signatures(
    declaration: &RegistryTheoryDeclaration,
    field: &ParsedField,
    field_sha256: &str,
) -> Result<Vec<SourceSignature>, String> {
    let Some(SExpr::String(text)) = field.value.as_ref() else {
        return Err(format!(
            "{} {}[{}] is not a description string",
            declaration.name, field.key, field.occurrence
        ));
    };
    let (expected_sha256, families) =
        description_catalog(&declaration.name, field.key.as_str(), field.occurrence)?;
    let actual_sha256 = sha256_bytes(text.as_bytes());
    if actual_sha256 != expected_sha256 || actual_sha256 != field_sha256 {
        return Err(format!(
            "{} {}[{}] prose signature field drift: expected {expected_sha256}, got {actual_sha256}",
            declaration.name, field.key, field.occurrence
        ));
    }
    families
        .iter()
        .map(|family| {
            if !description_anchor_present(text, family) {
                return Err(format!(
                    "{} {}[{}] no longer contains cataloged family {family:?}",
                    declaration.name, field.key, field.occurrence
                ));
            }
            Ok(SourceSignature {
                id: format!(
                    "registry.theories.{}.description.{}.{}.{}",
                    declaration.name,
                    field.key.trim_start_matches(':'),
                    field.occurrence,
                    id_component(family)
                ),
                declaration: format!("prose-family:{family}"),
                source_field_sha256: field_sha256.to_string(),
                witness: description_witness(&declaration.name, family)?,
            })
        })
        .collect()
}

fn description_catalog(
    theory: &str,
    key: &str,
    occurrence: usize,
) -> Result<(&'static str, &'static [&'static str]), String> {
    let row = match (theory, key, occurrence) {
        ("FixedSizeBitVectors", ":sorts-description", 0) => (
            "a84b4f3e6209b96ae2a226b68f4fd8a055ce34c688405c4f8256fe3a4b676543",
            &["sort.BitVec"][..],
        ),
        ("FixedSizeBitVectors", ":funs-description", 0) => (
            "3b3270b147253d1170256419145051edb482e8ad72a38a0cd878421245dff42c",
            &["literal.binary", "literal.hexadecimal"][..],
        ),
        ("FixedSizeBitVectors", ":funs-description", 1) => (
            "ea1048479824d0dd2e02f882776bb2bde28474ee0eed3825190161e83829eb5a",
            &["concat"][..],
        ),
        ("FixedSizeBitVectors", ":funs-description", 2) => (
            "ec1785d3827b6ce558273d652a89c340785d42be4bc6f4dd8248c9599c37ae21",
            &["extract"][..],
        ),
        ("FixedSizeBitVectors", ":funs-description", 3) => (
            "ebb23397ce6ccfcdcdd5e1e105c0aa044d8cd333e26526620767a7f772e9c53c",
            &[
                "bvnot", "bvneg", "bvand", "bvor", "bvadd", "bvmul", "bvudiv", "bvurem", "bvshl",
                "bvlshr",
            ][..],
        ),
        ("FixedSizeBitVectors", ":funs-description", 4) => (
            "502788a8f894e465092e897e9c46c065980d8e5ef4a31219d21b606ae13c0d7c",
            &["bvult"][..],
        ),
        ("FixedSizeBitVectors", ":funs-description", 5) => (
            "ae23e5c7805db5b1ffd40b0619e4d72d60cfb0c99fa78bf8d11823a62bb050d6",
            &["ubv_to_int", "sbv_to_int", "int_to_bv"][..],
        ),
        ("FloatingPoint", ":sorts-description", 0) => (
            "245867dde0412b4f12bb4aa3f15e0534878cb5970fb7d22286c16d0f9b67e1bf",
            &["sort.BitVec"][..],
        ),
        ("FloatingPoint", ":sorts-description", 1) => (
            "fa1c6db8459c779ff0f597be0273ad257dfb822c461800bbbb99a0c533e77808",
            &["sort.FloatingPoint"][..],
        ),
        ("FloatingPoint", ":funs-description", 0) => (
            "92edf2dc1ee4e3f0f0ef1e27d90c55470f8a4c955882478fc12b1e3c87901ffb",
            &["literal.binary", "literal.hexadecimal"][..],
        ),
        ("FloatingPoint", ":funs-description", 1) => (
            "6824ae4b225c7f11c3cfe576bda9282643b607f62de8762785fb5a30591714b2",
            &["fp"][..],
        ),
        ("FloatingPoint", ":funs-description", 2) => (
            "5526213a3d9ac542104b13ba47d8012d15b4886a878e4df170a7ee58d53c36e0",
            &["+oo", "-oo"][..],
        ),
        ("FloatingPoint", ":funs-description", 3) => (
            "ca5f8bbc5d2863abda6163507ecdc602c3dd3900f60886922628cdcbfb528b24",
            &["+zero", "-zero"][..],
        ),
        ("FloatingPoint", ":funs-description", 4) => (
            "4b23bf69d47aa85f847cbed565ef7e3f5f4bcd51d8655dc37d2913e5868fafb2",
            &["NaN"][..],
        ),
        ("FloatingPoint", ":funs-description", 5) => (
            "7e4465ba857c57737a4a192777d174fcb9b8ea45c19792b21c5d49849018cbdf",
            &[
                "fp.abs",
                "fp.neg",
                "fp.add",
                "fp.sub",
                "fp.mul",
                "fp.div",
                "fp.fma",
                "fp.sqrt",
                "fp.rem",
                "fp.roundToIntegral",
                "fp.min",
                "fp.max",
                "fp.leq",
                "fp.lt",
                "fp.geq",
                "fp.gt",
                "fp.eq",
                "fp.isNormal",
                "fp.isSubnormal",
                "fp.isZero",
                "fp.isInfinite",
                "fp.isNaN",
                "fp.isNegative",
                "fp.isPositive",
            ][..],
        ),
        ("FloatingPoint", ":funs-description", 6) => (
            "406e056db03d9f9085cd4bb3b59cf825de3f40a9e6100e3601330825098eabe3",
            &[
                "to_fp.bitvector",
                "to_fp.floatingpoint",
                "to_fp.real",
                "to_fp.signed-bitvector",
                "to_fp_unsigned",
            ][..],
        ),
        ("FloatingPoint", ":funs-description", 7) => (
            "af834c6177046e8e1e5eb1392fc17fb031697c0bfbafff3dfbdae94be91118e7",
            &["fp.to_ubv", "fp.to_sbv", "fp.to_real"][..],
        ),
        ("Ints" | "Reals_Ints", ":funs-description", 0) => (
            "799f8a93f1670114029077a05258e7b2700661aca7be85edbd3d30cfcc4aad7b",
            &["divisible"][..],
        ),
        ("Strings", ":funs-description", 0) => (
            "c206b3ba73eba37cf3000fd5b5750ff917616965738f3d9241698c92df6b5935",
            &["char"][..],
        ),
        ("Strings", ":funs-description", 1) => (
            "76c6b8ae1b4085d0b6c4189cb16d481b4072a2e19f13e341f2811dd045565e47",
            &["literal.string"][..],
        ),
        _ => {
            return Err(format!(
                "unowned prose signature field {theory} {key}[{occurrence}]"
            ))
        }
    };
    Ok(row)
}

fn description_anchor_present(text: &str, family: &str) -> bool {
    let anchor = match family {
        "sort.BitVec" => "BitVec",
        "sort.FloatingPoint" => "FloatingPoint",
        "literal.binary" => "binaries",
        "literal.hexadecimal" => "hex",
        "to_fp.bitvector" | "to_fp.floatingpoint" | "to_fp.real" | "to_fp.signed-bitvector" => {
            "to_fp"
        }
        "literal.string" => "string literals",
        other => other,
    };
    text.contains(anchor)
}

fn description_witness(theory: &str, family: &str) -> Result<Witness, String> {
    let witness = match theory {
        "FixedSizeBitVectors" => bitvector_description_witness(family),
        "FloatingPoint" => floating_point_description_witness(family),
        "Ints" | "Reals_Ints" if family == "divisible" => Some(term_witness(
            "((_ divisible 3) 6)",
            "((_ divisible 0) 6)",
            "(assert (not ((_ divisible 3) 6)))",
        )),
        "Strings" if family == "char" => Some(term_witness(
            "(_ char #x41)",
            "(_ char #x30000)",
            "(assert (distinct (_ char #x41) \"A\"))",
        )),
        "Strings" if family == "literal.string" => Some(term_witness(
            "\"abc\"",
            "\"é\"",
            "(assert (distinct \"\\u{41}\" \"A\"))",
        )),
        _ => None,
    };
    witness.ok_or_else(|| format!("unowned description family {theory}.{family}"))
}

fn bitvector_description_witness(family: &str) -> Option<Witness> {
    let witness = match family {
        "sort.BitVec" => return Some(sort_witness("(_ BitVec 4)", "(_ BitVec 0)")),
        "literal.binary" => term_witness("#b1010", "#b102", "(assert (distinct #b1010 #xa))"),
        "literal.hexadecimal" => {
            term_witness("#x0f", "#x0g", "(assert (distinct #x0f #b00001111))")
        }
        "concat" => term_witness(
            "(concat #xa #x5)",
            "(concat #xa true)",
            "(assert (distinct (concat #xa #x5) #xa5))",
        ),
        "extract" => term_witness(
            "((_ extract 5 2) #b11100110)",
            "((_ extract 2 5) #b11100110)",
            "(assert (distinct ((_ extract 5 2) #b11100110) #b1001))",
        ),
        "bvnot" => term_witness(
            "(bvnot #b1010)",
            "(bvnot true)",
            "(assert (distinct (bvnot #b1010) #b0101))",
        ),
        "bvneg" => term_witness(
            "(bvneg #x01)",
            "(bvneg true)",
            "(assert (distinct (bvneg #x01) #xff))",
        ),
        "bvand" => term_witness(
            "(bvand #b1100 #b1010 #b1111)",
            "(bvand #b1100 #b10)",
            "(assert (distinct (bvand #b1100 #b1010 #b1111) #b1000))",
        ),
        "bvor" => term_witness(
            "(bvor #b1100 #b1010 #b0000)",
            "(bvor #b1100 #b10)",
            "(assert (distinct (bvor #b1100 #b1010 #b0000) #b1110))",
        ),
        "bvadd" => term_witness(
            "(bvadd #xff #x01 #x00)",
            "(bvadd #xff #x1)",
            "(assert (distinct (bvadd #xff #x01 #x00) #x00))",
        ),
        "bvmul" => term_witness(
            "(bvmul #x03 #x04 #x01)",
            "(bvmul #x03 #x4)",
            "(assert (distinct (bvmul #x03 #x04 #x01) #x0c))",
        ),
        "bvudiv" => term_witness(
            "(bvudiv #x07 #x02)",
            "(bvudiv #x07 #x2)",
            "(assert (distinct (bvudiv #x07 #x02) #x03))",
        ),
        "bvurem" => term_witness(
            "(bvurem #x07 #x02)",
            "(bvurem #x07 #x2)",
            "(assert (distinct (bvurem #x07 #x02) #x01))",
        ),
        "bvshl" => term_witness(
            "(bvshl #x01 #x02)",
            "(bvshl #x01 #x2)",
            "(assert (distinct (bvshl #x01 #x02) #x04))",
        ),
        "bvlshr" => term_witness(
            "(bvlshr #x08 #x02)",
            "(bvlshr #x08 #x2)",
            "(assert (distinct (bvlshr #x08 #x02) #x02))",
        ),
        "bvult" => term_witness(
            "(bvult #x01 #x02)",
            "(bvult #x01 #x2)",
            "(assert (not (bvult #x01 #x02)))",
        ),
        "ubv_to_int" => term_witness(
            "(ubv_to_int #xff)",
            "(ubv_to_int true)",
            "(assert (distinct (ubv_to_int #xff) 255))",
        ),
        "sbv_to_int" => term_witness(
            "(sbv_to_int #xff)",
            "(sbv_to_int true)",
            "(assert (distinct (sbv_to_int #xff) (- 1)))",
        ),
        "int_to_bv" => term_witness(
            "((_ int_to_bv 8) (- 1))",
            "((_ int_to_bv 0) 1)",
            "(assert (distinct ((_ int_to_bv 8) (- 1)) #xff))",
        ),
        _ => return None,
    };
    Some(witness)
}

fn floating_point_description_witness(family: &str) -> Option<Witness> {
    if matches!(
        family,
        "sort.BitVec" | "literal.binary" | "literal.hexadecimal"
    ) {
        return bitvector_description_witness(family);
    }
    let pz = "(_ +zero 3 3)";
    let nz = "(_ -zero 3 3)";
    let po = "(_ +oo 3 3)";
    let nan = "(_ NaN 3 3)";
    let witness = match family {
        "sort.FloatingPoint" => {
            return Some(sort_witness(
                "(_ FloatingPoint 3 3)",
                "(_ FloatingPoint 1 3)",
            ));
        }
        "fp" => term_witness(
            "(fp #b0 #b000 #b00)",
            "(fp #b00 #b000 #b00)",
            "(assert (distinct (fp #b0 #b000 #b00) (_ +zero 3 3)))",
        ),
        "+oo" => term_witness(
            po,
            "(_ +oo 1 3)",
            "(assert (not (fp.isInfinite (_ +oo 3 3))))",
        ),
        "-oo" => term_witness(
            "(_ -oo 3 3)",
            "(_ -oo 3 1)",
            "(assert (not (fp.isInfinite (_ -oo 3 3))))",
        ),
        "+zero" => term_witness(
            pz,
            "(_ +zero 1 3)",
            "(assert (not (fp.isZero (_ +zero 3 3))))",
        ),
        "-zero" => term_witness(
            nz,
            "(_ -zero 3 1)",
            "(assert (not (fp.isZero (_ -zero 3 3))))",
        ),
        "NaN" => term_witness(nan, "(_ NaN 1 3)", "(assert (not (fp.isNaN (_ NaN 3 3))))"),
        "fp.abs" => term_witness(
            &format!("(fp.abs {nz})"),
            "(fp.abs true)",
            &format!("(assert (distinct (fp.abs {nz}) {pz}))"),
        ),
        "fp.neg" => term_witness(
            &format!("(fp.neg {pz})"),
            "(fp.neg true)",
            &format!("(assert (distinct (fp.neg {pz}) {nz}))"),
        ),
        "fp.add" => term_witness(
            &format!("(fp.add RNE {pz} {pz})"),
            &format!("(fp.add true {pz} {pz})"),
            &format!("(assert (distinct (fp.add RNE {pz} {pz}) {pz}))"),
        ),
        "fp.sub" => term_witness(
            &format!("(fp.sub RNE {pz} {pz})"),
            &format!("(fp.sub true {pz} {pz})"),
            &format!("(assert (distinct (fp.sub RNE {pz} {pz}) {pz}))"),
        ),
        "fp.mul" => term_witness(
            &format!("(fp.mul RNE {pz} {pz})"),
            &format!("(fp.mul true {pz} {pz})"),
            &format!("(assert (distinct (fp.mul RNE {pz} {pz}) {pz}))"),
        ),
        "fp.div" => term_witness(
            &format!("(fp.div RNE {pz} {pz})"),
            &format!("(fp.div true {pz} {pz})"),
            &format!("(assert (distinct (fp.div RNE {pz} {pz}) {nan}))"),
        ),
        "fp.fma" => term_witness(
            &format!("(fp.fma RNE {pz} {pz} {pz})"),
            &format!("(fp.fma true {pz} {pz} {pz})"),
            &format!("(assert (distinct (fp.fma RNE {pz} {pz} {pz}) {pz}))"),
        ),
        "fp.sqrt" => term_witness(
            &format!("(fp.sqrt RNE {pz})"),
            &format!("(fp.sqrt true {pz})"),
            &format!("(assert (distinct (fp.sqrt RNE {pz}) {pz}))"),
        ),
        "fp.rem" => term_witness(
            &format!("(fp.rem {pz} {po})"),
            &format!("(fp.rem true {po})"),
            &format!("(assert (distinct (fp.rem {pz} {po}) {pz}))"),
        ),
        "fp.roundToIntegral" => term_witness(
            &format!("(fp.roundToIntegral RNE {pz})"),
            &format!("(fp.roundToIntegral true {pz})"),
            &format!("(assert (distinct (fp.roundToIntegral RNE {pz}) {pz}))"),
        ),
        "fp.min" => term_witness(
            &format!("(fp.min {pz} {pz})"),
            &format!("(fp.min true {pz})"),
            &format!("(assert (distinct (fp.min {pz} {pz}) {pz}))"),
        ),
        "fp.max" => term_witness(
            &format!("(fp.max {pz} {pz})"),
            &format!("(fp.max true {pz})"),
            &format!("(assert (distinct (fp.max {pz} {pz}) {pz}))"),
        ),
        "fp.leq" => term_witness(
            &format!("(fp.leq {nz} {pz} {po})"),
            &format!("(fp.leq true {pz})"),
            &format!("(assert (not (fp.leq {nz} {pz} {po})))"),
        ),
        "fp.lt" => term_witness(
            &format!("(fp.lt {pz} {po})"),
            &format!("(fp.lt true {po})"),
            &format!("(assert (not (fp.lt {pz} {po})))"),
        ),
        "fp.geq" => term_witness(
            &format!("(fp.geq {po} {pz} {nz})"),
            &format!("(fp.geq true {pz})"),
            &format!("(assert (not (fp.geq {po} {pz} {nz})))"),
        ),
        "fp.gt" => term_witness(
            &format!("(fp.gt {po} {pz})"),
            &format!("(fp.gt true {pz})"),
            &format!("(assert (not (fp.gt {po} {pz})))"),
        ),
        "fp.eq" => term_witness(
            &format!("(fp.eq {nz} {pz})"),
            &format!("(fp.eq true {pz})"),
            &format!("(assert (not (fp.eq {nz} {pz})))"),
        ),
        "fp.isNormal" => term_witness(
            &format!("(fp.isNormal {pz})"),
            "(fp.isNormal true)",
            &format!("(assert (fp.isNormal {pz}))"),
        ),
        "fp.isSubnormal" => term_witness(
            &format!("(fp.isSubnormal {pz})"),
            "(fp.isSubnormal true)",
            &format!("(assert (fp.isSubnormal {pz}))"),
        ),
        "fp.isZero" => term_witness(
            &format!("(fp.isZero {pz})"),
            "(fp.isZero true)",
            &format!("(assert (not (fp.isZero {pz})))"),
        ),
        "fp.isInfinite" => term_witness(
            &format!("(fp.isInfinite {po})"),
            "(fp.isInfinite true)",
            &format!("(assert (not (fp.isInfinite {po})))"),
        ),
        "fp.isNaN" => term_witness(
            &format!("(fp.isNaN {nan})"),
            "(fp.isNaN true)",
            &format!("(assert (not (fp.isNaN {nan})))"),
        ),
        "fp.isNegative" => term_witness(
            &format!("(fp.isNegative {nz})"),
            "(fp.isNegative true)",
            &format!("(assert (not (fp.isNegative {nz})))"),
        ),
        "fp.isPositive" => term_witness(
            &format!("(fp.isPositive {pz})"),
            "(fp.isPositive true)",
            &format!("(assert (not (fp.isPositive {pz})))"),
        ),
        "to_fp.bitvector" => term_witness(
            "((_ to_fp 3 3) #b000000)",
            "((_ to_fp 1 3) #b0000)",
            &format!("(assert (distinct ((_ to_fp 3 3) #b000000) {pz}))"),
        ),
        "to_fp.floatingpoint" => term_witness(
            &format!("((_ to_fp 4 4) RNE {pz})"),
            &format!("((_ to_fp 1 4) RNE {pz})"),
            "(assert (distinct ((_ to_fp 4 4) RNE (_ +zero 3 3)) (_ +zero 4 4)))",
        ),
        "to_fp.real" => term_witness(
            "((_ to_fp 3 3) RNE 0.0)",
            "((_ to_fp 3 3) true 0.0)",
            &format!("(assert (distinct ((_ to_fp 3 3) RNE 0.0) {pz}))"),
        ),
        "to_fp.signed-bitvector" => term_witness(
            "((_ to_fp 3 3) RNE #b0000)",
            "((_ to_fp 3 3) true #b0000)",
            &format!("(assert (distinct ((_ to_fp 3 3) RNE #b0000) {pz}))"),
        ),
        "to_fp_unsigned" => term_witness(
            "((_ to_fp_unsigned 3 3) RNE #b0000)",
            "((_ to_fp_unsigned 3 3) true #b0000)",
            &format!("(assert (distinct ((_ to_fp_unsigned 3 3) RNE #b0000) {pz}))"),
        ),
        "fp.to_ubv" => term_witness(
            &format!("((_ fp.to_ubv 4) RNE {pz})"),
            &format!("((_ fp.to_ubv 0) RNE {pz})"),
            &format!("(assert (distinct ((_ fp.to_ubv 4) RNE {pz}) #b0000))"),
        ),
        "fp.to_sbv" => term_witness(
            &format!("((_ fp.to_sbv 4) RNE {pz})"),
            &format!("((_ fp.to_sbv 0) RNE {pz})"),
            &format!("(assert (distinct ((_ fp.to_sbv 4) RNE {pz}) #b0000))"),
        ),
        "fp.to_real" => term_witness(
            &format!("(fp.to_real {pz})"),
            "(fp.to_real true)",
            &format!("(assert (distinct (fp.to_real {pz}) 0.0))"),
        ),
        _ => return None,
    };
    Some(witness)
}

fn process_case_result(case: &ProcessCase, output: GuardedTranscriptOutput) -> ValidatorCase {
    match case.expectation {
        ProcessExpectation::ExactStdout(stdout) => {
            let mut row = transcript_case(&case.id, &case.input, stdout, output, &case.obligation);
            if row.outcome == ValidatorCaseOutcome::Fail
                && row.exit_code == Some(0)
                && row.stdout.as_deref() == Some("unknown\n")
                && row.stderr.as_deref() == Some("")
                && row.process.as_ref().is_some_and(process_completed)
            {
                row.outcome = ValidatorCaseOutcome::Unknown;
                row.observed.push_str("; solver_result=unknown");
            }
            row
        }
        ProcessExpectation::Rejection => rejection_case(case, output),
    }
}

fn rejection_case(case: &ProcessCase, output: GuardedTranscriptOutput) -> ValidatorCase {
    let stdout_utf8 = String::from_utf8(output.stdout);
    let stderr_utf8 = String::from_utf8(output.stderr);
    let exit_code = output.status.and_then(|status| status.code());
    let (stdout, stdout_valid) = match stdout_utf8 {
        Ok(value) => (value, true),
        Err(error) => (
            String::from_utf8_lossy(error.as_bytes()).into_owned(),
            false,
        ),
    };
    let (stderr, stderr_valid) = match stderr_utf8 {
        Ok(value) => (value, true),
        Err(error) => (
            String::from_utf8_lossy(error.as_bytes()).into_owned(),
            false,
        ),
    };
    let rejection_match = stdout_valid
        && stderr_valid
        && stderr.is_empty()
        && matches!(exit_code, Some(0 | 1))
        && is_single_error_response(&stdout);
    let outcome = if output.memout {
        ValidatorCaseOutcome::Memout
    } else if output.timed_out {
        ValidatorCaseOutcome::Timeout
    } else if !output.stdin_complete
        || output.stdout_truncated
        || output.stderr_truncated
        || !stdout_valid
        || !stderr_valid
    {
        ValidatorCaseOutcome::Fail
    } else if rejection_match {
        ValidatorCaseOutcome::Pass
    } else if !output.status.is_some_and(|status| status.success()) {
        ValidatorCaseOutcome::Crash
    } else {
        ValidatorCaseOutcome::Fail
    };
    ValidatorCase {
        id: case.id.clone(),
        input_sha256: sha256_bytes(&case.input),
        expected: case.expected(),
        observed: format!(
            "status={exit_code:?}; timeout={}; memout={}; stdin_complete={}; stdout_truncated={}; stderr_truncated={}; single_error_response={rejection_match}; stderr_empty={}",
            output.timed_out,
            output.memout,
            output.stdin_complete,
            output.stdout_truncated,
            output.stderr_truncated,
            stderr.is_empty()
        ),
        stdout: Some(stdout),
        stderr: Some(stderr),
        exit_code,
        process: Some(ProcessObservation {
            stdin_complete: output.stdin_complete,
            timed_out: output.timed_out,
            memout: output.memout,
            stdout_truncated: output.stdout_truncated,
            stderr_truncated: output.stderr_truncated,
        }),
        outcome,
    }
}

fn is_single_error_response(stdout: &str) -> bool {
    let Ok(rows) = ay_frontend::sexp::parse_sexps(stdout) else {
        return false;
    };
    let [row] = rows.as_slice() else {
        return false;
    };
    let Some(items) = row.as_list() else {
        return false;
    };
    matches!(items, [head, SExpr::String(_)] if head.is_symbol("error"))
}

fn process_completed(process: &ProcessObservation) -> bool {
    process.stdin_complete
        && !process.timed_out
        && !process.memout
        && !process.stdout_truncated
        && !process.stderr_truncated
}

fn validate_recorded_shape(
    receipt: &ValidatorReceipt,
    prepared: &PreparedCampaign,
) -> Result<(), String> {
    let mut expected = prepared
        .catalog_rows
        .iter()
        .map(|row| {
            (
                row.id.clone(),
                row.input_sha256.clone(),
                row.expected.clone(),
                false,
                None,
            )
        })
        .collect::<Vec<_>>();
    expected.extend(prepared.process_cases.iter().map(|case| {
        (
            case.id.clone(),
            sha256_bytes(&case.input),
            case.expected(),
            true,
            Some(case.expectation),
        )
    }));
    expected.sort_by(|left, right| left.0.cmp(&right.0));
    if receipt.case_results.len() != expected.len() {
        return Err(format!(
            "{VALIDATOR_ID} detailed case inventory drift: expected {}, got {}",
            expected.len(),
            receipt.case_results.len()
        ));
    }
    for (row, (id, input_sha256, expected_text, process_required, expectation)) in
        receipt.case_results.iter().zip(expected)
    {
        if row.id != id || row.input_sha256 != input_sha256 || row.expected != expected_text {
            return Err(format!(
                "{VALIDATOR_ID} case identity, input, or obligation drift at {id}"
            ));
        }
        if process_required != row.process.is_some() {
            return Err(format!("{id} has the wrong process-observation shape"));
        }
        if row.outcome != ValidatorCaseOutcome::Pass {
            continue;
        }
        match expectation {
            None => {
                if row.stdout.is_some()
                    || row.stderr.is_some()
                    || row.exit_code.is_some()
                    || row.process.is_some()
                {
                    return Err(format!("{id} source-catalog row forged process data"));
                }
            }
            Some(ProcessExpectation::ExactStdout(stdout)) => {
                if row.exit_code != Some(0)
                    || row.stdout.as_deref() != Some(stdout)
                    || row.stderr.as_deref() != Some("")
                    || !row.process.as_ref().is_some_and(process_completed)
                {
                    return Err(format!(
                        "{id} claims pass without its exact solver transcript"
                    ));
                }
            }
            Some(ProcessExpectation::Rejection) => {
                if !matches!(row.exit_code, Some(0 | 1))
                    || !row.stdout.as_deref().is_some_and(is_single_error_response)
                    || row.stderr.as_deref() != Some("")
                    || !row.process.as_ref().is_some_and(process_completed)
                {
                    return Err(format!("{id} claims pass without an exact error response"));
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_and_description_catalog_counts_are_closed() {
        let top_level = SMTLIB_THEORIES
            .iter()
            .map(|(theory, _)| {
                expected_field_shape(theory)
                    .expect("field shape")
                    .iter()
                    .map(|(_, count)| count)
                    .sum::<usize>()
            })
            .sum::<usize>();
        assert_eq!(top_level, TOP_LEVEL_FIELD_COUNT);

        let description_fields = [
            ("FixedSizeBitVectors", ":sorts-description", 1usize),
            ("FixedSizeBitVectors", ":funs-description", 6),
            ("FloatingPoint", ":sorts-description", 2),
            ("FloatingPoint", ":funs-description", 8),
            ("Ints", ":funs-description", 1),
            ("Reals_Ints", ":funs-description", 1),
            ("Strings", ":funs-description", 2),
        ];
        let mut family_count = 0usize;
        let mut family_ids = BTreeSet::new();
        for (theory, key, count) in description_fields {
            for occurrence in 0..count {
                let (_, families) =
                    description_catalog(theory, key, occurrence).expect("description catalog");
                family_count += families.len();
                for family in families {
                    assert!(
                        family_ids.insert(format!("{theory}.{key}.{occurrence}.{family}")),
                        "duplicate family"
                    );
                    description_witness(theory, family).expect("family witness");
                }
            }
        }
        assert_eq!(family_count, DESCRIPTION_SIGNATURE_COUNT);
        assert_eq!(SIGNATURE_COUNT * 3, PROCESS_CASE_COUNT);
        assert_eq!(
            SOURCE_FIELD_COUNT + SIGNATURE_COUNT + PROCESS_CASE_COUNT,
            DETAILED_CASE_COUNT
        );
    }

    #[test]
    fn rejection_classifier_is_exact() {
        assert!(is_single_error_response("(error \"bad term\")\n"));
        assert!(!is_single_error_response(""));
        assert!(!is_single_error_response("unknown\n"));
        assert!(!is_single_error_response(
            "(error \"one\")\n(error \"two\")\n"
        ));
    }

    /// Z3 5.0.0's no-logic registry coerces Bool to Int/Real in arithmetic,
    /// so a Bool operand is not a valid negative typing control. Pin the
    /// genuinely invalid arity controls used by every affected signature.
    #[test]
    fn numeric_negative_witnesses_avoid_bool_coercions() {
        let cases = [
            ("Ints", "-", "(- Int Int)", "(-)"),
            ("Reals", "-", "(- Real Real)", "(-)"),
            ("Ints", "-", "(- Int Int Int :left-assoc)", "(-)"),
            ("Ints", "+", "(+ Int Int Int :left-assoc)", "(+)"),
            ("Ints", "*", "(* Int Int Int :left-assoc)", "(*)"),
            ("Ints", "div", "(div Int Int Int :left-assoc)", "(div)"),
            ("Ints", "mod", "(mod Int Int Int)", "(mod 7)"),
            ("Ints", "abs", "(abs Int Int)", "(abs)"),
            ("Reals", "/", "(/ Real Real Real :left-assoc)", "(/)"),
            ("Ints", "<=", "(<= Int Int Bool :chainable)", "(<=)"),
            ("Ints", "<", "(< Int Int Bool :chainable)", "(<)"),
            ("Ints", ">=", "(>= Int Int Bool :chainable)", "(>=)"),
            ("Ints", ">", "(> Int Int Bool :chainable)", "(>)"),
            ("Reals_Ints", "to_real", "(to_real Int Real)", "(to_real)"),
            ("Reals_Ints", "to_int", "(to_int Real Int)", "(to_int)"),
            ("Reals_Ints", "is_int", "(is_int Real Bool)", "(is_int)"),
        ];

        for (theory, symbol, raw, invalid_term) in cases {
            let witness = arithmetic_machine_witness(theory, symbol, raw)
                .unwrap_or_else(|| panic!("missing arithmetic witness for {theory}.{symbol}"));
            assert_eq!(
                witness.negative,
                format!("(assert (= {invalid_term} {invalid_term}))\n"),
                "wrong negative typing control for {theory}.{symbol}"
            );
            assert!(
                !witness.negative.contains("true"),
                "Bool is numerically coercible in Z3 5.0.0: {}",
                witness.negative
            );
        }

        for (symbol, invalid_term) in [("=", "(=)"), ("distinct", "(distinct)")] {
            let witness = core_machine_witness(symbol)
                .unwrap_or_else(|| panic!("missing Core witness for {symbol}"));
            assert_eq!(
                witness.negative,
                format!("(assert (= {invalid_term} {invalid_term}))\n"),
                "wrong negative typing control for Core.{symbol}"
            );
            assert!(
                !witness.negative.contains("true"),
                "Bool is numerically coercible in Z3 5.0.0: {}",
                witness.negative
            );
        }
    }
}
