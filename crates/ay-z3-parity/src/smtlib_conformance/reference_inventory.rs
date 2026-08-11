// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authenticated source snapshots and the first registered source extractor.
//!
//! The profile's source digest is a sorted `path<TAB>git-blob<TAB>size` manifest.
//! A snapshot retains those exact text blobs beside the campaign receipt.  On
//! every audit replay we recompute both the Git blob object id and the SHA-256
//! of each retained file, so a correct manifest cannot be paired with invented
//! source bytes.

use super::*;
use sha1::Sha1;

pub(super) const VALIDATOR_ID: &str = "builtin.reference-inventory.v1";

const SNAPSHOT_SCHEMA: &str = "ay-smtlib-source-snapshot/v1";
const MAX_SNAPSHOT_BYTES: u64 = 32 * 1024 * 1024;

const SUPPORTED_DIMENSIONS: [&str; 10] = [
    "gate.integrity",
    "language.lexical-and-grammar",
    "language.commands",
    "registry.logics",
    "registry.theories",
    "results.sat-models",
    "results.unknown-policy",
    "results.unsat-proofs",
    "semantics.command-state-machine",
    "semantics.typing-and-scope",
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SnapshotKind {
    Language,
    Registry,
}

impl SnapshotKind {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "language" => Ok(Self::Language),
            "registry" => Ok(Self::Registry),
            _ => Err("source-snapshot kind must be `language` or `registry`".to_string()),
        }
    }

    fn id(self) -> &'static str {
        match self {
            Self::Language => "smtlib-language",
            Self::Registry => "smtlib-registry",
        }
    }

    fn cohort(self) -> SourceCohort {
        match self {
            Self::Language => SourceCohort::SmtlibLanguage,
            Self::Registry => SourceCohort::SmtlibRegistry,
        }
    }

    fn pin(self, profile: &Profile) -> &SourcePin {
        match self {
            Self::Language => &profile.standard.language_sources,
            Self::Registry => &profile.standard.registry,
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct SourceSnapshot {
    schema: String,
    profile_id: String,
    source: SnapshotSource,
    files: Vec<SnapshotFile>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct SnapshotSource {
    id: String,
    cohort: SourceCohort,
    repository: String,
    revision: String,
    selection: String,
    item_count: usize,
    digest_kind: String,
    selection_sha256: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct SnapshotFile {
    path: String,
    git_blob: String,
    size: usize,
    content_sha256: String,
    content: String,
}

#[derive(Debug, Eq, PartialEq)]
struct Execution {
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

pub(super) fn snapshot(args: &[String]) -> Result<i32, String> {
    let mut positionals = Vec::new();
    let mut output: Option<PathBuf> = None;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--out" => {
                index += 1;
                output = Some(PathBuf::from(args.get(index).ok_or("--out needs a path")?));
            }
            flag if flag.starts_with("--") => {
                return Err(format!("unknown source-snapshot flag {flag:?}"));
            }
            value => positionals.push(value.to_string()),
        }
        index += 1;
    }
    if positionals.len() != 2 {
        return Err(
            "usage: smtlib-conformance source-snapshot <language|registry> <git-checkout> --out <path>"
                .to_string(),
        );
    }
    let kind = SnapshotKind::parse(&positionals[0])?;
    let checkout = PathBuf::from(&positionals[1]);
    let output = output.ok_or("source-snapshot requires --out <path>")?;
    let source_snapshot = create_snapshot(kind, &checkout, &canonical_profile())?;
    let bytes = pretty_json(&source_snapshot)?;
    atomic_write_new(&output, &bytes)?;
    println!(
        "source-snapshot={} files={} sha256={} path={}",
        kind.id(),
        source_snapshot.files.len(),
        sha256_bytes(&bytes),
        output.display()
    );
    Ok(0)
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut dimension_id: Option<String> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut snapshot_path: Option<PathBuf> = None;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--dimension" => {
                index += 1;
                dimension_id = Some(args.get(index).ok_or("--dimension needs an id")?.clone());
            }
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
            flag if flag.starts_with("--") => {
                return Err(format!("unknown reference-inventory flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("reference-inventory takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }

    let manifest = manifest.ok_or("reference-inventory needs a manifest path")?;
    let dimension_id = dimension_id.ok_or("reference-inventory requires --dimension <id>")?;
    let receipt_path = receipt_path.ok_or("reference-inventory requires --receipt <path>")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let dimension = supported_dimension(&loaded.contract, &dimension_id)?;
    if dimension.inventory.granularity != InventoryGranularity::ItemLevel {
        return Err(format!(
            "{} is still a coarse unresolved inventory; expand it to source-item rows before extracting it",
            dimension.id
        ));
    }

    let source = load_source_for_dimension(
        &loaded.contract,
        dimension,
        &loaded.base,
        snapshot_path.as_deref(),
    )?;
    let execution = execute(dimension, source.as_ref().map(|loaded| &loaded.snapshot))?;
    let output_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let validator_sha = sha256_file(&current_exe, "parity validator")?;
    let requirement_ids = dimension
        .requirements
        .iter()
        .map(|requirement| requirement.id.clone())
        .collect();
    let reference_inputs = source
        .map(|loaded| vec![loaded.binding])
        .unwrap_or_default();
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: dimension.id.clone(),
        requirement_ids,
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: VALIDATOR_ID.to_string(),
            kind: ValidatorKind::ReferenceExtractor,
            path: current_exe.to_string_lossy().into_owned(),
            sha256: validator_sha,
        },
        subject: ReceiptSubject {
            ay_executable_sha256: None,
            ay_shared_library_sha256: None,
        },
        z3_binary_sha256: None,
        z3_shared_library_sha256: None,
        reference_inputs,
        auxiliary_tools: Vec::new(),
        source_provenance: None,
        resource_envelope: None,
        exhaustive: true,
        result: execution.result,
        cases: execution.cases,
        case_results: execution.case_results,
    };
    let bytes = pretty_json(&receipt)?;
    atomic_write_new(&receipt_path, &bytes)?;
    let receipt_sha = sha256_bytes(&bytes);
    println!(
        "reference-inventory={} receipt={} sha256={}",
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        output_relative,
        receipt_sha
    );
    println!(
        "attach to {} inventory: {{\"path\":\"{output_relative}\",\"sha256\":\"{receipt_sha}\"}}",
        dimension.id
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
    if receipt.validator.kind != ValidatorKind::ReferenceExtractor
        || !SUPPORTED_DIMENSIONS.contains(&context.dimension.id.as_str())
        || !receipt.exhaustive
        || receipt.z3_binary_sha256.is_some()
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
        || receipt.resource_envelope.is_some()
    {
        return Err(format!(
            "{VALIDATOR_ID} has invalid kind, dimension, exhaustive flag, or semantic-only binding"
        ));
    }
    let expected_ids = context
        .dimension
        .requirements
        .iter()
        .map(|row| row.id.clone())
        .collect::<Vec<_>>();
    if receipt.requirement_ids != expected_ids {
        return Err(format!(
            "{VALIDATOR_ID} does not cover the exact closed requirement inventory"
        ));
    }
    let expected_kind = required_snapshot_kind(&context.dimension.id);
    match (expected_kind, receipt.reference_inputs.as_slice()) {
        (Some(kind), [input]) if input.id == kind.id() && input.cohort == kind.cohort() => {}
        (Some(_), _) => {
            return Err(format!(
                "{VALIDATOR_ID} is missing the exact authenticated source snapshot"
            ));
        }
        (None, []) => {}
        (None, _) => {
            return Err(format!(
                "{VALIDATOR_ID} attached foreign source inputs to a contract-defined inventory"
            ));
        }
    }
    if context.mode.replays_registered_validators() {
        let snapshot = match receipt.reference_inputs.as_slice() {
            [input] => Some(load_bound_snapshot(
                input,
                context.manifest_dir,
                &canonical_profile(),
            )?),
            [] => None,
            _ => return Err("reference inventory has an invalid source-input count".to_string()),
        };
        let live = execute(context.dimension, snapshot.as_ref())?;
        if receipt.result != live.result
            || receipt.cases != live.cases
            || receipt.case_results != live.case_results
        {
            return Err(format!(
                "{VALIDATOR_ID} receipt does not match a fresh authenticated source extraction"
            ));
        }
    }
    Ok(())
}

struct LoadedSource {
    binding: ReferenceInput,
    snapshot: SourceSnapshot,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LanguageSourceFile {
    pub(super) path: String,
    pub(super) git_blob: String,
    pub(super) content_sha256: String,
    pub(super) content: String,
}

pub(super) struct LoadedLanguageSource {
    pub(super) binding: ReferenceInput,
    pub(super) files: Vec<LanguageSourceFile>,
}

pub(super) fn load_language_source(
    contract: &Contract,
    dimension: &Dimension,
    base: &Path,
    snapshot_path: Option<&Path>,
) -> Result<LoadedLanguageSource, String> {
    if !matches!(
        dimension.id.as_str(),
        "semantics.typing-and-scope" | "semantics.command-state-machine"
    ) {
        return Err(
            "semantic source loader requires a typing/scope or command-state dimension".to_string(),
        );
    }
    let loaded = load_source_for_dimension(contract, dimension, base, snapshot_path)?
        .ok_or_else(|| format!("{} has no authenticated language snapshot", dimension.id))?;
    Ok(LoadedLanguageSource {
        binding: loaded.binding,
        files: language_source_files(&loaded.snapshot),
    })
}

pub(super) fn load_bound_language_source(
    input: &ReferenceInput,
    base: &Path,
    profile: &Profile,
) -> Result<LoadedLanguageSource, String> {
    let snapshot = load_bound_snapshot(input, base, profile)?;
    Ok(LoadedLanguageSource {
        binding: input.clone(),
        files: language_source_files(&snapshot),
    })
}

fn language_source_files(snapshot: &SourceSnapshot) -> Vec<LanguageSourceFile> {
    snapshot
        .files
        .iter()
        .map(|file| LanguageSourceFile {
            path: file.path.clone(),
            git_blob: file.git_blob.clone(),
            content_sha256: file.content_sha256.clone(),
            content: file.content.clone(),
        })
        .collect()
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LanguageCommandProduction {
    pub(super) name: String,
    pub(super) path: String,
    pub(super) git_blob: String,
    pub(super) content_sha256: String,
    pub(super) production_sha256: String,
    pub(super) production: String,
}

pub(super) struct LoadedLanguageCommands {
    pub(super) binding: ReferenceInput,
    pub(super) productions: Vec<LanguageCommandProduction>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LanguageGrammarProduction {
    pub(super) name: String,
    pub(super) macro_name: String,
    pub(super) path: String,
    pub(super) git_blob: String,
    pub(super) content_sha256: String,
    pub(super) production_sha256: String,
    pub(super) production: String,
}

pub(super) struct LoadedLanguageGrammar {
    pub(super) binding: ReferenceInput,
    pub(super) productions: Vec<LanguageGrammarProduction>,
}

pub(super) fn load_language_grammar(
    contract: &Contract,
    dimension: &Dimension,
    base: &Path,
    snapshot_path: Option<&Path>,
) -> Result<LoadedLanguageGrammar, String> {
    if dimension.id != "language.lexical-and-grammar" {
        return Err("grammar source loader requires language.lexical-and-grammar".to_string());
    }
    let loaded = load_source_for_dimension(contract, dimension, base, snapshot_path)?
        .ok_or("language.lexical-and-grammar has no authenticated language snapshot")?;
    let productions = language_grammar_productions(&loaded.snapshot)?;
    Ok(LoadedLanguageGrammar {
        binding: loaded.binding,
        productions,
    })
}

pub(super) fn load_bound_language_grammar(
    input: &ReferenceInput,
    base: &Path,
    profile: &Profile,
) -> Result<Vec<LanguageGrammarProduction>, String> {
    let snapshot = load_bound_snapshot(input, base, profile)?;
    language_grammar_productions(&snapshot)
}

pub(super) fn load_language_commands(
    contract: &Contract,
    dimension: &Dimension,
    base: &Path,
    snapshot_path: Option<&Path>,
) -> Result<LoadedLanguageCommands, String> {
    if dimension.id != "language.commands" {
        return Err("command source loader requires language.commands".to_string());
    }
    let loaded = load_source_for_dimension(contract, dimension, base, snapshot_path)?
        .ok_or("language.commands has no authenticated language snapshot")?;
    let productions = language_command_productions(&loaded.snapshot)?;
    Ok(LoadedLanguageCommands {
        binding: loaded.binding,
        productions,
    })
}

pub(super) fn load_bound_language_commands(
    input: &ReferenceInput,
    base: &Path,
    profile: &Profile,
) -> Result<Vec<LanguageCommandProduction>, String> {
    let snapshot = load_bound_snapshot(input, base, profile)?;
    language_command_productions(&snapshot)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct RegistryLogicDeclaration {
    pub(super) name: String,
    pub(super) path: String,
    pub(super) git_blob: String,
    pub(super) content_sha256: String,
    pub(super) content: String,
}

pub(super) struct LoadedRegistrySource {
    pub(super) binding: ReferenceInput,
    pub(super) declarations: Vec<RegistryLogicDeclaration>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct RegistryTheoryDeclaration {
    pub(super) name: String,
    pub(super) path: String,
    pub(super) git_blob: String,
    pub(super) content_sha256: String,
    pub(super) content: String,
}

pub(super) struct LoadedRegistryTheories {
    pub(super) binding: ReferenceInput,
    pub(super) declarations: Vec<RegistryTheoryDeclaration>,
}

pub(super) fn load_registry_theories(
    contract: &Contract,
    dimension: &Dimension,
    base: &Path,
    snapshot_path: Option<&Path>,
) -> Result<LoadedRegistryTheories, String> {
    if dimension.id != "registry.theories" {
        return Err("theory-registry source loader requires registry.theories".to_string());
    }
    let loaded = load_source_for_dimension(contract, dimension, base, snapshot_path)?
        .ok_or("registry.theories has no authenticated registry snapshot")?;
    let declarations = registry_theory_declarations(&loaded.snapshot)?;
    Ok(LoadedRegistryTheories {
        binding: loaded.binding,
        declarations,
    })
}

pub(super) fn load_bound_registry_theories(
    input: &ReferenceInput,
    base: &Path,
    profile: &Profile,
) -> Result<Vec<RegistryTheoryDeclaration>, String> {
    let snapshot = load_bound_snapshot(input, base, profile)?;
    registry_theory_declarations(&snapshot)
}

pub(super) fn load_registry_source(
    contract: &Contract,
    dimension: &Dimension,
    base: &Path,
    snapshot_path: Option<&Path>,
) -> Result<LoadedRegistrySource, String> {
    if dimension.id != "registry.logics" {
        return Err("logic-registry source loader requires registry.logics".to_string());
    }
    let loaded = load_source_for_dimension(contract, dimension, base, snapshot_path)?
        .ok_or("registry.logics has no authenticated registry snapshot")?;
    let declarations = registry_logic_declarations(&loaded.snapshot)?;
    Ok(LoadedRegistrySource {
        binding: loaded.binding,
        declarations,
    })
}

pub(super) fn load_bound_registry_source(
    input: &ReferenceInput,
    base: &Path,
    profile: &Profile,
) -> Result<Vec<RegistryLogicDeclaration>, String> {
    let snapshot = load_bound_snapshot(input, base, profile)?;
    registry_logic_declarations(&snapshot)
}

fn load_source_for_dimension(
    contract: &Contract,
    dimension: &Dimension,
    base: &Path,
    snapshot_path: Option<&Path>,
) -> Result<Option<LoadedSource>, String> {
    let Some(kind) = required_snapshot_kind(&dimension.id) else {
        if snapshot_path.is_some() {
            return Err(format!(
                "{} is contract-defined and must not attach a source snapshot",
                dimension.id
            ));
        }
        return Ok(None);
    };
    let path = snapshot_path.ok_or_else(|| {
        format!(
            "{} requires --source-snapshot for the pinned {} source",
            dimension.id,
            kind.id()
        )
    })?;
    let relative = existing_relative_file(base, path, "source snapshot")?;
    let resolved = resolve_relative_evidence_path(base, &relative)?;
    let bytes = read_bounded_bytes(&resolved, MAX_SNAPSHOT_BYTES, "source snapshot", true)?;
    let snapshot: SourceSnapshot = serde_json::from_slice(&bytes).map_err(|error| {
        format!(
            "invalid source snapshot JSON {}: {error}",
            resolved.display()
        )
    })?;
    validate_snapshot(kind, &snapshot, &contract.profile)?;
    let binding = reference_binding(&snapshot, relative, sha256_bytes(&bytes));
    Ok(Some(LoadedSource { binding, snapshot }))
}

fn load_bound_snapshot(
    input: &ReferenceInput,
    base: &Path,
    profile: &Profile,
) -> Result<SourceSnapshot, String> {
    let path = resolve_relative_evidence_path(base, &input.snapshot.path)?;
    let bytes = read_bounded_bytes(&path, MAX_SNAPSHOT_BYTES, "source snapshot", true)?;
    let actual_sha = sha256_bytes(&bytes);
    if actual_sha != input.snapshot.sha256 {
        return Err(format!(
            "reference input {} snapshot hash changed during replay",
            input.id
        ));
    }
    let snapshot: SourceSnapshot = serde_json::from_slice(&bytes)
        .map_err(|error| format!("invalid source snapshot JSON {}: {error}", path.display()))?;
    let kind = SnapshotKind::parse(input.id.trim_start_matches("smtlib-"))?;
    validate_snapshot(kind, &snapshot, profile)?;
    let rebound = reference_binding(&snapshot, input.snapshot.path.clone(), actual_sha);
    if &rebound != input {
        return Err(format!(
            "reference input {} metadata does not match its replayable snapshot",
            input.id
        ));
    }
    Ok(snapshot)
}

fn reference_binding(snapshot: &SourceSnapshot, path: String, sha256: String) -> ReferenceInput {
    ReferenceInput {
        id: snapshot.source.id.clone(),
        cohort: snapshot.source.cohort,
        repository: snapshot.source.repository.clone(),
        revision: snapshot.source.revision.clone(),
        selection: snapshot.source.selection.clone(),
        item_count: snapshot.source.item_count,
        digest_kind: snapshot.source.digest_kind.clone(),
        selection_sha256: snapshot.source.selection_sha256.clone(),
        snapshot: Artifact { path, sha256 },
    }
}

fn execute(dimension: &Dimension, snapshot: Option<&SourceSnapshot>) -> Result<Execution, String> {
    let mut rows = match dimension.id.as_str() {
        "language.lexical-and-grammar" => extract_grammar(
            dimension,
            snapshot.ok_or("language.lexical-and-grammar extractor has no language snapshot")?,
        )?,
        "language.commands" => extract_commands(
            dimension,
            snapshot.ok_or("language.commands extractor has no language snapshot")?,
        )?,
        "registry.logics" => extract_logics(
            dimension,
            snapshot.ok_or("registry.logics extractor has no registry snapshot")?,
        )?,
        "registry.theories" => extract_theories(
            dimension,
            snapshot.ok_or("registry.theories extractor has no registry snapshot")?,
        )?,
        "semantics.typing-and-scope" | "semantics.command-state-machine" => {
            let snapshot = snapshot.ok_or("semantic extractor has no language snapshot")?;
            language_semantics::inventory_rows(dimension, &language_source_files(snapshot))?
        }
        "gate.integrity"
        | "results.sat-models"
        | "results.unsat-proofs"
        | "results.unknown-policy" => extract_contract_rows(dimension)?,
        other => {
            return Err(format!(
                "unsupported reference-inventory dimension {other:?}"
            ))
        }
    };
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    let cases = case_counts_from_rows(&rows)?;
    Ok(Execution {
        result: overall_validator_result(&rows),
        cases,
        case_results: rows,
    })
}

fn extract_grammar(
    dimension: &Dimension,
    snapshot: &SourceSnapshot,
) -> Result<Vec<ValidatorCase>, String> {
    let productions = language_grammar_productions(snapshot)?
        .into_iter()
        .map(|production| (production.name.clone(), production))
        .collect::<BTreeMap<_, _>>();
    dimension
        .requirements
        .iter()
        .map(|requirement| {
            let name = requirement
                .id
                .strip_prefix("language.lexical-and-grammar.")
                .ok_or("grammar requirement id has the wrong prefix")?;
            let production = productions
                .get(name)
                .ok_or_else(|| format!("source grammar {name:?} has no canonical row"))?;
            let input = format!(
                "{}\n{}\n{}\n{}\n{}",
                snapshot.source.selection_sha256,
                production.git_blob,
                production.macro_name,
                name,
                production.production_sha256
            );
            Ok(passing_inventory_case(
                requirement,
                input.as_bytes(),
                format!(
                    "authenticated {} at blob {} declares `{name}` in {}",
                    production.path, production.git_blob, production.macro_name
                ),
            ))
        })
        .collect()
}

fn extract_commands(
    dimension: &Dimension,
    snapshot: &SourceSnapshot,
) -> Result<Vec<ValidatorCase>, String> {
    let productions = language_command_productions(snapshot)?
        .into_iter()
        .map(|production| (production.name.clone(), production))
        .collect::<BTreeMap<_, _>>();
    dimension
        .requirements
        .iter()
        .map(|requirement| {
            let name = requirement
                .id
                .strip_prefix("language.commands.")
                .ok_or("command requirement id has the wrong prefix")?;
            let production = productions
                .get(name)
                .ok_or_else(|| format!("source command {name:?} has no canonical row"))?;
            let input = format!(
                "{}\n{}\n{}\n{}",
                snapshot.source.selection_sha256,
                production.git_blob,
                name,
                production.production_sha256
            );
            Ok(passing_inventory_case(
                requirement,
                input.as_bytes(),
                format!(
                    "authenticated {} at blob {} declares command `{name}`",
                    production.path, production.git_blob
                ),
            ))
        })
        .collect()
}

fn extract_logics(
    dimension: &Dimension,
    snapshot: &SourceSnapshot,
) -> Result<Vec<ValidatorCase>, String> {
    let declarations = registry_logic_declarations(snapshot)?
        .into_iter()
        .map(|declaration| (declaration.name.clone(), declaration))
        .collect::<BTreeMap<_, _>>();
    dimension
        .requirements
        .iter()
        .map(|requirement| {
            let name = requirement
                .id
                .strip_prefix("registry.logics.")
                .ok_or("logic requirement id has the wrong prefix")?;
            let declaration = declarations
                .get(name)
                .ok_or_else(|| format!("authenticated registry has no logic {name:?}"))?;
            Ok(passing_inventory_case(
                requirement,
                declaration.content_sha256.as_bytes(),
                format!(
                    "authenticated {} blob {} declares logic `{name}`",
                    declaration.path, declaration.git_blob
                ),
            ))
        })
        .collect()
}

fn extract_theories(
    dimension: &Dimension,
    snapshot: &SourceSnapshot,
) -> Result<Vec<ValidatorCase>, String> {
    let declarations = registry_theory_declarations(snapshot)?
        .into_iter()
        .map(|declaration| (declaration.name.clone(), declaration))
        .collect::<BTreeMap<_, _>>();
    dimension
        .requirements
        .iter()
        .map(|requirement| {
            let name = requirement
                .id
                .strip_prefix("registry.theories.")
                .ok_or("theory requirement id has the wrong prefix")?;
            let declaration = declarations
                .get(name)
                .ok_or_else(|| format!("authenticated registry has no theory {name:?}"))?;
            Ok(passing_inventory_case(
                requirement,
                declaration.content_sha256.as_bytes(),
                format!(
                    "authenticated {} blob {} declares theory `{name}`",
                    declaration.path, declaration.git_blob
                ),
            ))
        })
        .collect()
}

fn registry_logic_declarations(
    snapshot: &SourceSnapshot,
) -> Result<Vec<RegistryLogicDeclaration>, String> {
    let actual_paths = snapshot
        .files
        .iter()
        .filter(|file| file.path.starts_with("Logics/") && file.path.ends_with(".smt2"))
        .map(|file| file.path.clone())
        .collect::<BTreeSet<_>>();
    let expected_paths = SMTLIB_LOGICS
        .iter()
        .map(|name| format!("Logics/{name}.smt2"))
        .collect::<BTreeSet<_>>();
    if actual_paths != expected_paths {
        return Err(
            "authenticated registry snapshot does not contain exactly 25 logic files".to_string(),
        );
    }
    SMTLIB_LOGICS
        .iter()
        .map(|name| {
            let path = format!("Logics/{name}.smt2");
            let file = snapshot_file(snapshot, &path)?;
            let declared = declared_registry_name(&file.content, "logic")?;
            if declared != *name {
                return Err(format!(
                    "registry file {path} declares logic {declared:?}, expected {name:?}"
                ));
            }
            Ok(RegistryLogicDeclaration {
                name: (*name).to_string(),
                path,
                git_blob: file.git_blob.clone(),
                content_sha256: file.content_sha256.clone(),
                content: file.content.clone(),
            })
        })
        .collect()
}

fn registry_theory_declarations(
    snapshot: &SourceSnapshot,
) -> Result<Vec<RegistryTheoryDeclaration>, String> {
    let actual_paths = snapshot
        .files
        .iter()
        .filter(|file| file.path.starts_with("Theories/") && file.path.ends_with(".smt2"))
        .map(|file| file.path.clone())
        .collect::<BTreeSet<_>>();
    let expected_paths = SMTLIB_THEORIES
        .iter()
        .map(|(_, path)| (*path).to_string())
        .collect::<BTreeSet<_>>();
    if actual_paths != expected_paths {
        return Err(
            "authenticated registry snapshot does not contain exactly nine non-draft theory files"
                .to_string(),
        );
    }
    SMTLIB_THEORIES
        .iter()
        .map(|(name, path)| {
            let file = snapshot_file(snapshot, path)?;
            let declared = declared_registry_name(&file.content, "theory")?;
            if declared != *name {
                return Err(format!(
                    "registry file {path} declares theory {declared:?}, expected {name:?}"
                ));
            }
            Ok(RegistryTheoryDeclaration {
                name: (*name).to_string(),
                path: (*path).to_string(),
                git_blob: file.git_blob.clone(),
                content_sha256: file.content_sha256.clone(),
                content: file.content.clone(),
            })
        })
        .collect()
}

fn extract_contract_rows(dimension: &Dimension) -> Result<Vec<ValidatorCase>, String> {
    dimension
        .requirements
        .iter()
        .map(|requirement| {
            let bytes = serde_json::to_vec(requirement)
                .map_err(|error| format!("serializing contract inventory row: {error}"))?;
            Ok(passing_inventory_case(
                requirement,
                &bytes,
                format!("closed contract owns canonical row {}", requirement.id),
            ))
        })
        .collect()
}

fn passing_inventory_case(
    requirement: &Requirement,
    input: &[u8],
    observed: String,
) -> ValidatorCase {
    ValidatorCase {
        id: format!("inventory.{}", requirement.id),
        input_sha256: sha256_bytes(input),
        expected: format!(
            "one authenticated source item is owned by {} at {}",
            requirement.id, requirement.source.locator
        ),
        observed,
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome: ValidatorCaseOutcome::Pass,
    }
}

fn language_grammar_productions(
    snapshot: &SourceSnapshot,
) -> Result<Vec<LanguageGrammarProduction>, String> {
    let syntax = snapshot_file(snapshot, "Reference/syntax-macros.tex")?;
    let specs = [
        (
            "aLexical",
            "tokens",
            &lexical_grammar::PRODUCTION_NAMES[0..4],
        ),
        (
            "tokens",
            "sexpressions",
            &lexical_grammar::PRODUCTION_NAMES[4..12],
        ),
        (
            "sexpressions",
            "cIdentifiers",
            &lexical_grammar::PRODUCTION_NAMES[12..14],
        ),
        (
            "cIdentifiers",
            "cSorts",
            &lexical_grammar::PRODUCTION_NAMES[14..16],
        ),
        (
            "cSorts",
            "cAttributes",
            &lexical_grammar::PRODUCTION_NAMES[16..17],
        ),
        (
            "cAttributes",
            "cTerms",
            &lexical_grammar::PRODUCTION_NAMES[17..19],
        ),
        (
            "cTerms",
            "cTheories",
            &lexical_grammar::PRODUCTION_NAMES[19..26],
        ),
        (
            "cResponsesI",
            "cGeneralResponse",
            &lexical_grammar::PRODUCTION_NAMES[26..32],
        ),
        (
            "cResponsesII",
            "sortterms",
            &lexical_grammar::PRODUCTION_NAMES[32..44],
        ),
        (
            "cGeneralResponse",
            "cResponsesII",
            &lexical_grammar::PRODUCTION_NAMES[44..45],
        ),
    ];
    let mut by_name = BTreeMap::new();
    for (macro_name, next_macro, expected_names) in specs {
        let body = tex_macro_body(&syntax.content, macro_name, next_macro)?;
        for (name, production) in grammar_macro_productions(body, macro_name, expected_names)? {
            if lexical_grammar::source_macro_name(&name) != Some(macro_name) {
                return Err(format!(
                    "grammar production {name:?} was extracted from unexpected macro {macro_name}"
                ));
            }
            let row = LanguageGrammarProduction {
                name: name.clone(),
                macro_name: macro_name.to_string(),
                path: syntax.path.clone(),
                git_blob: syntax.git_blob.clone(),
                content_sha256: syntax.content_sha256.clone(),
                production_sha256: sha256_bytes(production.as_bytes()),
                production,
            };
            if by_name.insert(name.clone(), row).is_some() {
                return Err(format!(
                    "duplicate grammar production {name:?} in authenticated source"
                ));
            }
        }
    }

    let mut productions = Vec::with_capacity(lexical_grammar::PRODUCTION_NAMES.len());
    for name in lexical_grammar::PRODUCTION_NAMES {
        productions.push(
            by_name
                .remove(name)
                .ok_or_else(|| format!("authenticated source has no {name:?} production"))?,
        );
    }
    if !by_name.is_empty() {
        return Err(format!(
            "authenticated source exposed unexpected grammar productions: {:?}",
            by_name.keys().collect::<Vec<_>>()
        ));
    }
    Ok(productions)
}

fn tex_macro_body<'a>(
    source: &'a str,
    macro_name: &str,
    next_macro: &str,
) -> Result<&'a str, String> {
    let start_marker = format!("\\newcommand{{\\{macro_name}}}{{");
    let start = source
        .find(&start_marker)
        .ok_or_else(|| format!("syntax source has no {macro_name} macro"))?
        + start_marker.len();
    let end_marker = format!("\\newcommand{{\\{next_macro}}}");
    let end = source[start..]
        .find(&end_marker)
        .ok_or_else(|| format!("syntax source has no {next_macro} boundary after {macro_name}"))?
        + start;
    Ok(&source[start..end])
}

fn grammar_macro_productions(
    body: &str,
    macro_name: &str,
    expected_names: &[&str],
) -> Result<Vec<(String, String)>, String> {
    let offsets = grammar_lhs_offsets(body, macro_name)?;
    let actual_names = offsets
        .iter()
        .map(|(name, _)| name.as_str())
        .collect::<Vec<_>>();
    if actual_names != expected_names {
        return Err(format!(
            "pinned {macro_name} production drift: expected {expected_names:?}, got {actual_names:?}"
        ));
    }
    offsets
        .iter()
        .enumerate()
        .map(|(index, (name, start))| {
            let end = offsets.get(index + 1).map_or(body.len(), |(_, next)| *next);
            let production = body[*start..end].trim().to_string();
            if production.is_empty() {
                return Err(format!(
                    "authenticated {macro_name} production {name:?} is empty"
                ));
            }
            Ok((name.clone(), production))
        })
        .collect()
}

fn grammar_lhs_offsets(body: &str, macro_name: &str) -> Result<Vec<(String, usize)>, String> {
    let mut rows = Vec::new();
    let mut pending: Option<(String, usize)> = None;
    let mut body_offset = 0usize;
    for raw_line in body.split_inclusive('\n') {
        let line = raw_line
            .split_once('%')
            .map_or(raw_line, |(prefix, _)| prefix);
        if let Some(offset) = line.find("\\nter") {
            let ampersand = line.find('&');
            if ampersand.is_none_or(|separator| offset < separator) {
                if pending.is_some() {
                    return Err(format!(
                        "{macro_name} starts a new production before the previous `::=`"
                    ));
                }
                pending = Some((tex_nonterminal_at(line, offset)?, body_offset + offset));
            }
        }
        if line.contains("::=") || line.contains(":=") {
            rows.push(pending.take().ok_or_else(|| {
                format!("{macro_name} has a production operator without a left-hand side")
            })?);
        }
        body_offset += raw_line.len();
    }
    if let Some((name, _)) = pending {
        return Err(format!(
            "{macro_name} production {name:?} has no `::=` operator"
        ));
    }
    Ok(rows)
}

fn tex_nonterminal_at(line: &str, offset: usize) -> Result<String, String> {
    let mut remainder = line
        .get(offset + "\\nter".len()..)
        .ok_or("invalid nonterminal byte offset")?;
    if let Some(after_open) = remainder.strip_prefix('[') {
        let close = after_open
            .find(']')
            .ok_or("unterminated nonterminal multiplicity")?;
        remainder = &after_open[close + 1..];
    }
    let remainder = remainder
        .strip_prefix('{')
        .ok_or("nonterminal has no opening brace")?;
    let close = remainder
        .find('}')
        .ok_or("nonterminal has no closing brace")?;
    let name = remainder[..close].replace("\\_", "_");
    if name.is_empty() {
        return Err("nonterminal has an empty name".to_string());
    }
    Ok(name)
}

fn command_productions_from_source(source: &str) -> Result<Vec<(String, String)>, String> {
    let start = source
        .find("\\nter{command}")
        .ok_or("syntax source has no command production")?;
    let tail = &source[start..];
    let end = tail
        .find("\\nter{script}")
        .ok_or("syntax source has no script production after command")?;
    let production = &tail[..end];
    let marker = "\\ter{(} \\ter{";
    let mut alternatives = Vec::new();
    let mut current: Option<(String, String)> = None;
    for line in production.lines() {
        if let Some(offset) = line.find(marker) {
            if let Some(finished) = current.take() {
                alternatives.push(finished);
            }
            let name_start = offset + marker.len();
            let remainder = &line[name_start..];
            let name_end = remainder
                .find('}')
                .ok_or("unterminated command token in syntax source")?;
            current = Some((
                remainder[..name_end].to_string(),
                line.split_whitespace().collect::<Vec<_>>().join(" "),
            ));
        } else if let Some((_, text)) = current.as_mut() {
            let continuation = line.split_whitespace().collect::<Vec<_>>().join(" ");
            if !continuation.is_empty() {
                text.push(' ');
                text.push_str(&continuation);
            }
        }
    }
    if let Some(finished) = current {
        alternatives.push(finished);
    }
    let mut names = BTreeSet::new();
    for (name, _) in &alternatives {
        if !names.insert(name.clone()) {
            return Err(format!(
                "duplicate command alternative {name:?} in syntax source"
            ));
        }
    }
    Ok(alternatives)
}

fn command_names_from_source(source: &str) -> Result<BTreeSet<String>, String> {
    Ok(command_productions_from_source(source)?
        .into_iter()
        .map(|(name, _)| name)
        .collect())
}

fn language_command_productions(
    snapshot: &SourceSnapshot,
) -> Result<Vec<LanguageCommandProduction>, String> {
    let syntax = snapshot_file(snapshot, "Reference/syntax-macros.tex")?;
    let alternatives = command_productions_from_source(&syntax.content)?;
    let actual = alternatives
        .iter()
        .map(|(name, _)| name.clone())
        .collect::<BTreeSet<_>>();
    let expected = SMTLIB_COMMANDS
        .iter()
        .map(|name| (*name).to_string())
        .collect::<BTreeSet<_>>();
    if actual != expected || alternatives.len() != SMTLIB_COMMANDS.len() {
        let missing = expected.difference(&actual).collect::<Vec<_>>();
        let unexpected = actual.difference(&expected).collect::<Vec<_>>();
        return Err(format!(
            "pinned command production drift: missing={missing:?}; unexpected={unexpected:?}"
        ));
    }
    let mut productions = alternatives
        .into_iter()
        .map(|(name, production)| LanguageCommandProduction {
            name,
            path: syntax.path.clone(),
            git_blob: syntax.git_blob.clone(),
            content_sha256: syntax.content_sha256.clone(),
            production_sha256: sha256_bytes(production.as_bytes()),
            production,
        })
        .collect::<Vec<_>>();
    productions.sort_by(|left, right| left.name.cmp(&right.name));
    Ok(productions)
}

fn declared_registry_name<'a>(source: &'a str, form: &str) -> Result<&'a str, String> {
    let trimmed = source.trim_start();
    let prefix = format!("({form} ");
    let remainder = trimmed
        .strip_prefix(&prefix)
        .ok_or_else(|| format!("registry file does not start with `({form} <name>`"))?;
    remainder
        .split(|character: char| character.is_whitespace() || character == ')')
        .next()
        .filter(|name| !name.is_empty())
        .ok_or_else(|| format!("registry {form} declaration has no name"))
}

fn snapshot_file<'a>(snapshot: &'a SourceSnapshot, path: &str) -> Result<&'a SnapshotFile, String> {
    snapshot
        .files
        .binary_search_by(|file| file.path.as_str().cmp(path))
        .ok()
        .and_then(|index| snapshot.files.get(index))
        .ok_or_else(|| format!("source snapshot is missing {path}"))
}

fn supported_dimension<'a>(contract: &'a Contract, id: &str) -> Result<&'a Dimension, String> {
    if !SUPPORTED_DIMENSIONS.contains(&id) {
        return Err(format!(
            "reference-inventory does not yet implement {id:?}; supported dimensions are {SUPPORTED_DIMENSIONS:?}"
        ));
    }
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == id)
        .ok_or_else(|| format!("closed dimension {id:?} is missing"))
}

fn required_snapshot_kind(dimension_id: &str) -> Option<SnapshotKind> {
    match dimension_id {
        "language.lexical-and-grammar"
        | "language.commands"
        | "semantics.typing-and-scope"
        | "semantics.command-state-machine" => Some(SnapshotKind::Language),
        "registry.logics" | "registry.theories" => Some(SnapshotKind::Registry),
        _ => None,
    }
}

fn create_snapshot(
    kind: SnapshotKind,
    checkout: &Path,
    profile: &Profile,
) -> Result<SourceSnapshot, String> {
    let checkout = fs::canonicalize(checkout).map_err(|error| {
        format!(
            "canonicalizing source checkout {}: {error}",
            checkout.display()
        )
    })?;
    let pin = kind.pin(profile);
    let head = git_text(&checkout, &["rev-parse", "HEAD"], "source HEAD")?;
    if head.trim() != pin.revision {
        return Err(format!(
            "{} checkout HEAD is {}, expected pinned revision {}",
            kind.id(),
            head.trim(),
            pin.revision
        ));
    }
    let tree = git_text(
        &checkout,
        &["ls-tree", "-r", "-l", &pin.revision],
        "selected source tree",
    )?;
    let entries = selected_tree_entries(kind, &tree)?;
    let expected_paths = selected_paths(kind);
    let actual_paths = entries
        .iter()
        .map(|entry| entry.path.clone())
        .collect::<BTreeSet<_>>();
    if actual_paths != expected_paths {
        let missing = expected_paths.difference(&actual_paths).collect::<Vec<_>>();
        let unexpected = actual_paths.difference(&expected_paths).collect::<Vec<_>>();
        return Err(format!(
            "{} selected source paths drifted: missing={missing:?}; unexpected={unexpected:?}",
            kind.id()
        ));
    }
    let selection_sha256 = tree_manifest_sha256(&entries);
    if entries.len() != pin.item_count || selection_sha256 != pin.sha256 {
        return Err(format!(
            "{} selected source manifest mismatch: count={}/{} sha256={}/{}",
            kind.id(),
            entries.len(),
            pin.item_count,
            selection_sha256,
            pin.sha256
        ));
    }

    let mut files = Vec::with_capacity(entries.len());
    for entry in entries {
        let object = format!("{}:{}", pin.revision, entry.path);
        let bytes = git_bytes(&checkout, &["show", &object], "source blob")?;
        if bytes.len() != entry.size {
            return Err(format!(
                "source blob {} size mismatch: tree={}, bytes={}",
                entry.path,
                entry.size,
                bytes.len()
            ));
        }
        let actual_blob = git_blob_sha1(&bytes);
        if actual_blob != entry.git_blob {
            return Err(format!(
                "source blob {} Git object mismatch: tree={}, bytes={actual_blob}",
                entry.path, entry.git_blob
            ));
        }
        let content = String::from_utf8(bytes)
            .map_err(|_| format!("selected source {} is not UTF-8", entry.path))?;
        files.push(SnapshotFile {
            path: entry.path,
            git_blob: entry.git_blob,
            size: entry.size,
            content_sha256: sha256_bytes(content.as_bytes()),
            content,
        });
    }
    let snapshot = SourceSnapshot {
        schema: SNAPSHOT_SCHEMA.to_string(),
        profile_id: PROFILE_ID.to_string(),
        source: SnapshotSource {
            id: kind.id().to_string(),
            cohort: kind.cohort(),
            repository: pin.repository.clone(),
            revision: pin.revision.clone(),
            selection: pin.selection.clone(),
            item_count: pin.item_count,
            digest_kind: pin.digest_kind.clone(),
            selection_sha256: pin.sha256.clone(),
        },
        files,
    };
    validate_snapshot(kind, &snapshot, profile)?;
    Ok(snapshot)
}

fn validate_snapshot(
    kind: SnapshotKind,
    snapshot: &SourceSnapshot,
    profile: &Profile,
) -> Result<(), String> {
    if snapshot.schema != SNAPSHOT_SCHEMA || snapshot.profile_id != PROFILE_ID {
        return Err("source snapshot schema or profile mismatch".to_string());
    }
    let pin = kind.pin(profile);
    let expected_source = SnapshotSource {
        id: kind.id().to_string(),
        cohort: kind.cohort(),
        repository: pin.repository.clone(),
        revision: pin.revision.clone(),
        selection: pin.selection.clone(),
        item_count: pin.item_count,
        digest_kind: pin.digest_kind.clone(),
        selection_sha256: pin.sha256.clone(),
    };
    if snapshot.source != expected_source {
        return Err(format!(
            "{} snapshot source metadata differs from the immutable profile",
            kind.id()
        ));
    }
    if snapshot.files.len() != pin.item_count {
        return Err(format!(
            "{} snapshot has {} files, expected {}",
            kind.id(),
            snapshot.files.len(),
            pin.item_count
        ));
    }
    let expected_paths = selected_paths(kind);
    let mut actual_paths = BTreeSet::new();
    let mut entries = Vec::with_capacity(snapshot.files.len());
    let mut previous: Option<&str> = None;
    for file in &snapshot.files {
        validate_relative_path(&file.path, "snapshot source path")?;
        if previous.is_some_and(|prior| prior >= file.path.as_str()) {
            return Err("snapshot files must be sorted and duplicate-free".to_string());
        }
        previous = Some(&file.path);
        validate_git_object_id(&file.git_blob)?;
        if file.size != file.content.len() {
            return Err(format!("snapshot file {} size mismatch", file.path));
        }
        let content_sha = sha256_bytes(file.content.as_bytes());
        if content_sha != file.content_sha256 {
            return Err(format!("snapshot file {} content hash mismatch", file.path));
        }
        let git_blob = git_blob_sha1(file.content.as_bytes());
        if git_blob != file.git_blob {
            return Err(format!(
                "snapshot file {} content does not match Git blob {}",
                file.path, file.git_blob
            ));
        }
        actual_paths.insert(file.path.clone());
        entries.push(TreeEntry {
            path: file.path.clone(),
            git_blob: file.git_blob.clone(),
            size: file.size,
        });
    }
    if actual_paths != expected_paths {
        return Err(format!(
            "{} snapshot selected path set differs from the immutable profile",
            kind.id()
        ));
    }
    let digest = tree_manifest_sha256(&entries);
    if digest != pin.sha256 {
        return Err(format!(
            "{} snapshot source-manifest digest mismatch",
            kind.id()
        ));
    }
    Ok(())
}

#[derive(Debug)]
struct TreeEntry {
    path: String,
    git_blob: String,
    size: usize,
}

fn selected_tree_entries(kind: SnapshotKind, tree: &str) -> Result<Vec<TreeEntry>, String> {
    let selected = selected_paths(kind);
    let mut entries = Vec::new();
    for line in tree.lines() {
        let (metadata, path) = line
            .split_once('\t')
            .ok_or("git ls-tree emitted a line without a tab-delimited path")?;
        if !selected.contains(path) {
            continue;
        }
        let fields = metadata.split_whitespace().collect::<Vec<_>>();
        if fields.len() != 4 || fields[0] != "100644" || fields[1] != "blob" {
            return Err(format!("selected source {path} is not a regular Git blob"));
        }
        validate_git_object_id(fields[2])?;
        let size = fields[3]
            .parse::<usize>()
            .map_err(|_| format!("selected source {path} has an invalid Git size"))?;
        entries.push(TreeEntry {
            path: path.to_string(),
            git_blob: fields[2].to_string(),
            size,
        });
    }
    entries.sort_by(|left, right| left.path.cmp(&right.path));
    Ok(entries)
}

fn selected_paths(kind: SnapshotKind) -> BTreeSet<String> {
    match kind {
        SnapshotKind::Language => [
            "Reference/acknowledgments.tex",
            "Reference/basic-assumptions.tex",
            "Reference/biblio.bib",
            "Reference/concrete-syntax.tex",
            "Reference/concrete-to-abstract.tex",
            "Reference/design-notes.tex",
            "Reference/endnotes-fix.tex",
            "Reference/general-info.tex",
            "Reference/logical-semantics.tex",
            "Reference/macros.tex",
            "Reference/main.tex",
            "Reference/operational-semantics.tex",
            "Reference/preface.tex",
            "Reference/state-machine.tex",
            "Reference/syntax-macros.tex",
            "Reference/syntax-summary.tex",
            "Reference/theories-logics.tex",
        ]
        .into_iter()
        .map(str::to_string)
        .collect(),
        SnapshotKind::Registry => {
            let mut paths = SMTLIB_LOGICS
                .iter()
                .map(|name| format!("Logics/{name}.smt2"))
                .collect::<BTreeSet<_>>();
            paths.extend(SMTLIB_THEORIES.iter().map(|(_, path)| (*path).to_string()));
            paths
        }
    }
}

fn tree_manifest_sha256(entries: &[TreeEntry]) -> String {
    let mut hasher = Sha256::new();
    for entry in entries {
        hasher.update(entry.path.as_bytes());
        hasher.update(b"\t");
        hasher.update(entry.git_blob.as_bytes());
        hasher.update(b"\t");
        hasher.update(entry.size.to_string().as_bytes());
        hasher.update(b"\n");
    }
    format!("{:x}", hasher.finalize())
}

fn git_blob_sha1(bytes: &[u8]) -> String {
    let mut hasher = Sha1::new();
    hasher.update(format!("blob {}\0", bytes.len()).as_bytes());
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}

fn validate_git_object_id(value: &str) -> Result<(), String> {
    if value.len() != 40
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("Git blob id must be exactly 40 lowercase hexadecimal characters".to_string());
    }
    Ok(())
}

fn git_text(checkout: &Path, args: &[&str], label: &str) -> Result<String, String> {
    let bytes = git_bytes(checkout, args, label)?;
    String::from_utf8(bytes).map_err(|_| format!("git {label} output is not UTF-8"))
}

fn git_bytes(checkout: &Path, args: &[&str], label: &str) -> Result<Vec<u8>, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(checkout)
        .args(args)
        .output()
        .map_err(|error| format!("running git for {label}: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "git {label} failed with status {:?}: {}",
            output.status.code(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(output.stdout)
}

fn existing_relative_file(base: &Path, path: &Path, label: &str) -> Result<String, String> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("inspecting {label} {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
        return Err(format!(
            "{label} must be a non-symlink regular file: {}",
            path.display()
        ));
    }
    let canonical_base = fs::canonicalize(base)
        .map_err(|error| format!("canonicalizing manifest directory: {error}"))?;
    let canonical_path = fs::canonicalize(path)
        .map_err(|error| format!("canonicalizing {label} {}: {error}", path.display()))?;
    let relative = canonical_path.strip_prefix(&canonical_base).map_err(|_| {
        format!(
            "{label} {} must be inside manifest directory {}",
            canonical_path.display(),
            canonical_base.display()
        )
    })?;
    let value = relative
        .to_str()
        .ok_or_else(|| format!("{label} relative path is not UTF-8"))?
        .to_string();
    validate_relative_path(&value, label)?;
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn profile_manifest_hash_algorithm_is_frozen() {
        let entries = vec![TreeEntry {
            path: "Reference/example.tex".to_string(),
            git_blob: "1".repeat(40),
            size: 7,
        }];
        assert_eq!(
            tree_manifest_sha256(&entries),
            sha256_bytes(format!("Reference/example.tex\t{}\t7\n", "1".repeat(40)).as_bytes())
        );
    }

    #[test]
    fn git_blob_identity_includes_header_and_bytes() {
        assert_eq!(
            git_blob_sha1(b"test\n"),
            "9daeafb9864cf43055ae93beb0afd6c7d144bfa4"
        );
    }

    #[test]
    fn command_extractor_owns_every_canonical_alternative() {
        let alternatives = SMTLIB_COMMANDS
            .iter()
            .map(|name| format!(" & \\alt & \\ter{{(}} \\ter{{{name}}} \\ter{{)}}"))
            .collect::<Vec<_>>()
            .join("\n");
        let source = format!("\\nter{{command}}\n{alternatives}\n\\nter{{script}}");
        let actual = command_names_from_source(&source).expect("command alternatives");
        let expected = SMTLIB_COMMANDS
            .iter()
            .map(|name| (*name).to_string())
            .collect::<BTreeSet<_>>();
        assert_eq!(actual, expected);
    }

    #[test]
    fn grammar_extractor_owns_only_left_hand_side_productions() {
        let source = r"
 \nter{first\_row} & ::= & \nter{second\_row}
 \\[1ex]
% \nter{commented\_row} & ::= & \nter{first\_row}
 \nter{second\_row}
   & ::= & \ter{x} \alt \nter{first\_row}
";
        let expected = ["first_row", "second_row"];
        let rows =
            grammar_macro_productions(source, "fixture", &expected).expect("grammar productions");
        assert_eq!(
            rows.iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>(),
            expected
        );
        assert!(rows[0].1.contains("second\\_row"));
        assert!(!rows[1].1.contains("commented\\_row"));
    }

    #[test]
    fn grammar_catalog_maps_every_production_to_a_source_macro() {
        for name in lexical_grammar::PRODUCTION_NAMES {
            assert!(lexical_grammar::source_macro_name(name).is_some(), "{name}");
        }
    }
}
