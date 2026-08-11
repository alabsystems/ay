// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed, fail-closed execution of the official SMT-LIB 2024 corpus.
//!
//! The small corpus committed under `benchmarks/` is intentionally not accepted
//! here.  A campaign first creates an immutable manifest from every file in all
//! 84 archives of Zenodo record 11061097.  The manifest records every file byte
//! hash and every decision-query epoch.  Inventory and semantic receipts retain
//! that manifest as a content-addressed input.  Semantic receipts additionally
//! retain a per-file/per-query result artifact because the generic receipt's
//! bounded detailed-case section cannot honestly hold roughly 438,000 rows.
//!
//! Every AY child uses both `--memory` and the repository RSS watchdog.  Z3 has
//! no memory flag, so its RSS watchdog is the enforced per-child budget.  The
//! oracle and subject run sequentially under one planner-admitted job.

use super::*;
use std::ffi::OsString;
use std::io::Read;
use std::process::Stdio;

pub(super) const INVENTORY_VALIDATOR_ID: &str = "builtin.official-corpus-inventory.v1";
pub(super) const VALIDATOR_ID: &str = "builtin.official-corpus-z3-5.0.0.v1";

const DIMENSION_ID: &str = "coverage.corpus";
const REQUIREMENT_ID: &str = "coverage.corpus.closed-query-manifest";
const CORPUS_MANIFEST_SCHEMA: &str = "ay-official-smtlib-corpus-manifest/v1";
const RUN_RESULTS_SCHEMA: &str = "ay-official-smtlib-corpus-results/v1";
const RECORD_ID: &str = "11061097";
const RECORD_DOI: &str = "10.5281/zenodo.11061097";
const RECORD_API: &str = "https://zenodo.org/api/records/11061097";
const SOURCE_SELECTION: &str =
    "all 84 SMT-LIB 2024 non-incremental division archives; every extracted .smt2 file and every decision query; no divisions, files, or queries excluded";
const EXPECTED_ARCHIVE_COUNT: usize = 84;
const EXPECTED_RECORD_METADATA_SHA256: &str =
    "ab864ac1985eea00a4866cb328dbcb839277bb58c206215fc176611941518027";
const EXPECTED_ARCHIVE_MANIFEST_SHA256: &str =
    "337c6b0468e5f08175773c21864ed2712299678132f6204d8b5b08f8ad51a942";
const EXPECTED_FILE_COUNT: usize = 438_631;
const EXPECTED_QUERY_COUNT: usize = 438_631;
const EXPECTED_SOURCE_SELECTION_SHA256: &str =
    "109f19f3f835aea7f1272a73a7c78b306b53cb86abb5e5b6c16423d17b4116e7";
const SOURCE_SELECTION_DESCRIPTOR: &str = "record=11061097;metadata=ab864ac1985eea00a4866cb328dbcb839277bb58c206215fc176611941518027;archives=337c6b0468e5f08175773c21864ed2712299678132f6204d8b5b08f8ad51a942;files=438631;queries=438631;mapping=archive-path-slash-to-double-underscore;query-scanner=v1";
const MAX_CORPUS_MANIFEST_BYTES: u64 = 1024 * 1024 * 1024;
const MAX_CORPUS_RESULTS_BYTES: u64 = 2 * 1024 * 1024 * 1024;
const MAX_CORPUS_FILE_BYTES: u64 = 1024 * 1024 * 1024;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct OfficialCorpusManifest {
    schema: String,
    profile_id: String,
    source: CorpusSource,
    /// Canonical absolute materialization used for replay.  Moving the corpus
    /// requires a new manifest and therefore cannot silently reuse evidence.
    corpus_root: String,
    /// Canonical absolute directory holding the exact 84 source archives.
    archive_root: String,
    file_count: usize,
    query_count: usize,
    selection_sha256: String,
    files: Vec<CorpusFile>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct CorpusSource {
    name: String,
    record_id: String,
    doi: String,
    api_url: String,
    record_metadata_sha256: String,
    selection: String,
    source_selection_sha256: String,
    archive_count: usize,
    archive_manifest_sha256: String,
    archives: Vec<CorpusArchive>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct CorpusArchive {
    division: String,
    key: String,
    size: u64,
    checksum: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct CorpusFile {
    path: String,
    size: u64,
    sha256: String,
    queries: Vec<CorpusQuery>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct CorpusQuery {
    ordinal: usize,
    command: String,
    byte_start: u64,
    byte_end: u64,
    command_sha256: String,
    prefix_sha256: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum CorpusVerdict {
    Sat,
    Unsat,
    Unknown,
}

impl CorpusVerdict {
    fn parse(line: &str) -> Option<Self> {
        match line.trim() {
            "sat" => Some(Self::Sat),
            "unsat" => Some(Self::Unsat),
            "unknown" => Some(Self::Unknown),
            _ => None,
        }
    }

    const fn decided(self) -> bool {
        !matches!(self, Self::Unknown)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ProcessRun {
    exit_code: Option<i32>,
    stdin_complete: bool,
    timed_out: bool,
    memout: bool,
    stdout_truncated: bool,
    stderr_truncated: bool,
    stdout_utf8: bool,
    stderr_utf8: bool,
    error_diagnostic: bool,
    harness_error: Option<String>,
    stdout_sha256: String,
    stderr_sha256: String,
    observed_ns: u64,
    verdicts: Vec<CorpusVerdict>,
}

impl ProcessRun {
    fn unavailable(error: String) -> Self {
        Self {
            exit_code: None,
            stdin_complete: false,
            timed_out: false,
            memout: false,
            stdout_truncated: false,
            stderr_truncated: false,
            stdout_utf8: true,
            stderr_utf8: true,
            error_diagnostic: false,
            harness_error: Some(error),
            stdout_sha256: sha256_bytes(b""),
            stderr_sha256: sha256_bytes(b""),
            observed_ns: 0,
            verdicts: Vec::new(),
        }
    }

    fn is_complete(&self) -> bool {
        self.exit_code == Some(0)
            && self.stdin_complete
            && !self.timed_out
            && !self.memout
            && !self.stdout_truncated
            && !self.stderr_truncated
            && self.stdout_utf8
            && self.stderr_utf8
            && !self.error_diagnostic
            && self.harness_error.is_none()
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum QueryOutcome {
    Pass,
    Wrong,
    Missing,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct QueryRun {
    ordinal: usize,
    command: String,
    prefix_sha256: String,
    z3: Option<CorpusVerdict>,
    ay: Option<CorpusVerdict>,
    certification: String,
    outcome: QueryOutcome,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum FileOutcome {
    Pass,
    Fail,
    Timeout,
    Memout,
    Crash,
    Unavailable,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct FileRun {
    path: String,
    input_sha256: String,
    query_count: usize,
    ay: ProcessRun,
    z3: ProcessRun,
    queries: Vec<QueryRun>,
    outcome: FileOutcome,
}

#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct CorpusRunCounts {
    files_total: usize,
    files_passed: usize,
    files_failed: usize,
    queries_total: usize,
    parity_passed: usize,
    wrong: usize,
    missing: usize,
    oracle_unknown: usize,
    z3_decided_ay_missing: usize,
    ay_sat: usize,
    ay_unsat: usize,
    timed_out: usize,
    memout: usize,
    crashed: usize,
    unavailable: usize,
    diagnostic_errors: usize,
    truncated_outputs: usize,
}

impl CorpusRunCounts {
    fn complete(&self) -> bool {
        self.files_total > 0
            && self.queries_total > 0
            && self.files_passed == self.files_total
            && self.files_failed == 0
            && self.parity_passed == self.queries_total
            && self.wrong == 0
            && self.missing == 0
            && self.z3_decided_ay_missing == 0
            && self.timed_out == 0
            && self.memout == 0
            && self.crashed == 0
            && self.unavailable == 0
            && self.diagnostic_errors == 0
            && self.truncated_outputs == 0
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct CorpusRunResults {
    schema: String,
    created_unix_ms: u128,
    campaign_id: String,
    profile_id: String,
    profile_sha256: String,
    inventory_sha256: String,
    corpus_manifest_sha256: String,
    corpus_selection_sha256: String,
    corpus_root: String,
    ay_sha256: String,
    z3_sha256: String,
    resource_envelope: String,
    ay_mode: String,
    z3_mode: String,
    counts: CorpusRunCounts,
    files: Vec<FileRun>,
}

#[derive(Debug)]
struct SemanticExecution {
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
    run_results: CorpusRunResults,
}

pub(super) fn create_manifest(args: &[String]) -> Result<i32, String> {
    let mut root: Option<PathBuf> = None;
    let mut archive_root: Option<PathBuf> = None;
    let mut metadata: Option<PathBuf> = None;
    let mut output: Option<PathBuf> = None;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--record-metadata" => {
                index += 1;
                metadata = Some(PathBuf::from(
                    args.get(index).ok_or("--record-metadata needs a path")?,
                ));
            }
            "--archive-root" => {
                index += 1;
                archive_root = Some(PathBuf::from(
                    args.get(index).ok_or("--archive-root needs a path")?,
                ));
            }
            "--out" => {
                index += 1;
                output = Some(PathBuf::from(args.get(index).ok_or("--out needs a path")?));
            }
            flag if flag.starts_with("--") => {
                return Err(format!("unknown official-corpus-manifest flag {flag:?}"));
            }
            value => {
                if root.replace(PathBuf::from(value)).is_some() {
                    return Err(
                        "official-corpus-manifest takes exactly one corpus root".to_string()
                    );
                }
            }
        }
        index += 1;
    }
    let root = root.ok_or("official-corpus-manifest needs a corpus root")?;
    let archive_root = archive_root.ok_or("official-corpus-manifest requires --archive-root")?;
    let metadata = metadata.ok_or("official-corpus-manifest requires --record-metadata")?;
    let output = output.ok_or("official-corpus-manifest requires --out")?;
    let metadata_bytes =
        read_bounded_bytes(&metadata, 64 * 1024 * 1024, "Zenodo record metadata", true)?;
    let source = source_from_metadata(&metadata_bytes)?;
    let corpus_root = canonical_corpus_root(&root)?;
    let archive_root = canonical_archive_root(&archive_root)?;
    let files = collect_corpus_files(&corpus_root)?;
    let archive_files = collect_archive_files(&source, &archive_root)?;
    if files != archive_files {
        return Err(
            "materialized corpus is not a byte-and-query-exact bijection of all authenticated archive members"
                .to_string(),
        );
    }
    let query_count = files.iter().try_fold(0usize, |count, file| {
        count
            .checked_add(file.queries.len())
            .ok_or("official corpus query count overflow")
    })?;
    let manifest = OfficialCorpusManifest {
        schema: CORPUS_MANIFEST_SCHEMA.to_string(),
        profile_id: PROFILE_ID.to_string(),
        source,
        corpus_root: corpus_root.to_string_lossy().into_owned(),
        archive_root: archive_root.to_string_lossy().into_owned(),
        file_count: files.len(),
        query_count,
        selection_sha256: selection_sha256(&files)?,
        files,
    };
    validate_manifest(&manifest)?;
    let bytes = pretty_json(&manifest)?;
    atomic_write_new(&output, &bytes)?;
    println!(
        "wrote {} (record={}, archives={}, files={}, queries={}, selection-sha256={})",
        output.display(),
        manifest.source.record_id,
        manifest.source.archive_count,
        manifest.file_count,
        manifest.query_count,
        manifest.selection_sha256
    );
    Ok(0)
}

pub(super) fn run_inventory(args: &[String]) -> Result<i32, String> {
    let common = parse_inventory_args(args)?;
    let loaded = load_contract(&common.manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let dimension = corpus_dimension(&loaded.contract)?;
    let (corpus_manifest, corpus_bytes) = load_corpus_manifest(&common.corpus_manifest)?;
    verify_materialization(&corpus_manifest)?;
    let snapshot_relative = existing_relative_artifact(&loaded.base, &common.corpus_manifest)?;
    let snapshot_sha256 = sha256_bytes(&corpus_bytes);
    let reference_input =
        manifest_reference_input(&corpus_manifest, snapshot_relative, snapshot_sha256.clone());
    let case_results = inventory_cases(&corpus_manifest, &snapshot_sha256);
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: DIMENSION_ID.to_string(),
        requirement_ids: vec![REQUIREMENT_ID.to_string()],
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: current_validator(INVENTORY_VALIDATOR_ID, ValidatorKind::ReferenceExtractor)?,
        subject: ReceiptSubject {
            ay_executable_sha256: None,
            ay_shared_library_sha256: None,
        },
        z3_binary_sha256: None,
        z3_shared_library_sha256: None,
        reference_inputs: vec![reference_input],
        auxiliary_tools: Vec::new(),
        source_provenance: None,
        resource_envelope: None,
        exhaustive: true,
        result: ValidatorResult::Pass,
        cases: case_counts_from_rows(&case_results)?,
        case_results,
    };
    write_receipt_and_report(
        &loaded,
        &common.receipt,
        &receipt,
        "official-corpus-inventory",
        &report,
    )
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    let options = parse_run_args(args)?;
    let loaded = load_contract(&options.manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let dimension = corpus_dimension(&loaded.contract)?;
    let envelope = loaded
        .contract
        .resource_envelope
        .as_deref()
        .ok_or("official-corpus requires contract.resource_envelope")?;
    let parsed = parse_resource_envelope(envelope)?;
    if parsed.jobs != 1 {
        return Err("official-corpus requires a one-job campaign envelope".to_string());
    }
    if parsed.timeout != Duration::from_secs(options.timeout_secs) {
        return Err("--timeout differs from contract.resource_envelope".to_string());
    }
    let subject = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("official-corpus requires subject.ay_executable")?;
    let ay = options
        .ay
        .unwrap_or_else(|| artifact_path(&loaded.base, &subject.path));
    let z3 = options.z3.unwrap_or_else(|| {
        PathBuf::from(&loaded.contract.profile.z3_overlay.reference_executable.path)
    });
    let (corpus_manifest, corpus_bytes) = load_corpus_manifest(&options.corpus_manifest)?;
    let corpus_manifest_sha256 = sha256_bytes(&corpus_bytes);
    let execution = execute_semantic(
        &loaded.contract,
        &dimension.inventory.sha256,
        &corpus_manifest,
        &corpus_manifest_sha256,
        &ay,
        &z3,
        parsed.timeout,
        Some(envelope),
    )?;
    let results_bytes = serde_json::to_vec(&execution.run_results)
        .map_err(|error| format!("serializing official corpus results: {error}"))?;
    atomic_write_new(&options.results, &results_bytes)?;

    let manifest_relative = existing_relative_artifact(&loaded.base, &options.corpus_manifest)?;
    let results_relative = existing_relative_artifact(&loaded.base, &options.results)?;
    let results_sha256 = sha256_bytes(&results_bytes);
    let reference_inputs = vec![
        manifest_reference_input(
            &corpus_manifest,
            manifest_relative,
            corpus_manifest_sha256.clone(),
        ),
        results_reference_input(
            &loaded.contract,
            &corpus_manifest,
            results_relative,
            results_sha256,
        ),
    ];
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: DIMENSION_ID.to_string(),
        requirement_ids: vec![REQUIREMENT_ID.to_string()],
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: current_validator(VALIDATOR_ID, ValidatorKind::OfficialCorpus)?,
        subject: ReceiptSubject {
            ay_executable_sha256: Some(subject.sha256.clone()),
            ay_shared_library_sha256: loaded
                .contract
                .subject
                .ay_shared_library
                .as_ref()
                .map(|artifact| artifact.sha256.clone()),
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
        z3_shared_library_sha256: None,
        reference_inputs,
        auxiliary_tools: Vec::new(),
        source_provenance: None,
        resource_envelope: Some(execution.run_results.resource_envelope.clone()),
        exhaustive: true,
        result: execution.result,
        cases: execution.cases,
        case_results: execution.case_results,
    };
    write_receipt_and_report(
        &loaded,
        &options.receipt,
        &receipt,
        "official-corpus",
        &report,
    )
}

pub(super) fn validate_inventory_and_replay(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    if receipt.validator.kind != ValidatorKind::ReferenceExtractor
        || context.dimension.id != DIMENSION_ID
        || receipt.requirement_ids != [REQUIREMENT_ID.to_string()]
        || !receipt.exhaustive
        || receipt.subject.ay_executable_sha256.is_some()
        || receipt.subject.ay_shared_library_sha256.is_some()
        || receipt.z3_binary_sha256.is_some()
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
        || receipt.resource_envelope.is_some()
        || receipt.reference_inputs.len() != 1
    {
        return Err(format!("{INVENTORY_VALIDATOR_ID} has invalid bindings"));
    }
    let (manifest, bytes) = manifest_from_reference(receipt, context.manifest_dir, 0)?;
    validate_manifest_reference(&receipt.reference_inputs[0], &manifest, &bytes)?;
    let expected = inventory_cases(&manifest, &sha256_bytes(&bytes));
    if receipt.result != ValidatorResult::Pass
        || receipt.case_results != expected
        || receipt.cases != case_counts_from_rows(&expected)?
    {
        return Err(format!(
            "{INVENTORY_VALIDATOR_ID} receipt does not match its immutable corpus manifest"
        ));
    }
    if context.mode.replays_registered_validators() {
        verify_materialization(&manifest)?;
    }
    Ok(())
}

pub(super) fn validate_and_replay(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    if receipt.validator.kind != ValidatorKind::OfficialCorpus
        || context.dimension.id != DIMENSION_ID
        || receipt.requirement_ids != [REQUIREMENT_ID.to_string()]
        || !receipt.exhaustive
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
        || receipt.reference_inputs.len() != 2
    {
        return Err(format!("{VALIDATOR_ID} has invalid bindings"));
    }
    let (manifest, manifest_bytes) = manifest_from_reference(receipt, context.manifest_dir, 0)?;
    validate_manifest_reference(&receipt.reference_inputs[0], &manifest, &manifest_bytes)?;
    let (results, result_bytes) = results_from_reference(receipt, context.manifest_dir, 1)?;
    validate_results_reference(
        &receipt.reference_inputs[1],
        context.contract,
        &manifest,
        &results,
        &result_bytes,
    )?;
    validate_run_results(
        &results,
        context.contract,
        &context.dimension.inventory.sha256,
        &manifest,
        &sha256_bytes(&manifest_bytes),
    )?;
    let expected_rows = aggregate_cases(&results.counts, &manifest.selection_sha256);
    if receipt.result != overall_validator_result(&expected_rows)
        || receipt.cases != case_counts_from_rows(&expected_rows)?
        || receipt.case_results != expected_rows
    {
        return Err(format!(
            "{VALIDATOR_ID} aggregate receipt does not match retained per-query results"
        ));
    }
    if context.mode.replays_registered_validators() {
        let envelope = receipt
            .resource_envelope
            .as_deref()
            .ok_or("official corpus receipt has no resource envelope")?;
        let parsed = parse_resource_envelope(envelope)?;
        if parsed.jobs != 1 {
            return Err("official corpus replay requires jobs=1".to_string());
        }
        let subject = context
            .contract
            .subject
            .ay_executable
            .as_ref()
            .ok_or("official corpus replay requires subject.ay_executable")?;
        let live = execute_semantic(
            context.contract,
            &context.dimension.inventory.sha256,
            &manifest,
            &sha256_bytes(&manifest_bytes),
            &artifact_path(context.manifest_dir, &subject.path),
            Path::new(
                &context
                    .contract
                    .profile
                    .z3_overlay
                    .reference_executable
                    .path,
            ),
            parsed.timeout,
            Some(envelope),
        )?;
        if semantic_signature(&live.run_results) != semantic_signature(&results) {
            return Err(format!(
                "{VALIDATOR_ID} retained results do not match a fresh complete replay"
            ));
        }
    }
    Ok(())
}

#[derive(Debug)]
struct InventoryArgs {
    manifest: PathBuf,
    corpus_manifest: PathBuf,
    receipt: PathBuf,
}

fn parse_inventory_args(args: &[String]) -> Result<InventoryArgs, String> {
    let mut manifest = None;
    let mut corpus_manifest = None;
    let mut receipt = None;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--corpus-manifest" => {
                index += 1;
                corpus_manifest = Some(PathBuf::from(
                    args.get(index).ok_or("--corpus-manifest needs a path")?,
                ));
            }
            "--receipt" => {
                index += 1;
                receipt = Some(PathBuf::from(
                    args.get(index).ok_or("--receipt needs a path")?,
                ));
            }
            flag if flag.starts_with("--") => {
                return Err(format!("unknown official-corpus-inventory flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("official-corpus-inventory takes one contract".to_string());
                }
            }
        }
        index += 1;
    }
    Ok(InventoryArgs {
        manifest: manifest.ok_or("official-corpus-inventory needs a contract")?,
        corpus_manifest: corpus_manifest
            .ok_or("official-corpus-inventory requires --corpus-manifest")?,
        receipt: receipt.ok_or("official-corpus-inventory requires --receipt")?,
    })
}

#[derive(Debug)]
struct RunArgs {
    manifest: PathBuf,
    corpus_manifest: PathBuf,
    receipt: PathBuf,
    results: PathBuf,
    ay: Option<PathBuf>,
    z3: Option<PathBuf>,
    timeout_secs: u64,
}

fn parse_run_args(args: &[String]) -> Result<RunArgs, String> {
    let mut manifest = None;
    let mut corpus_manifest = None;
    let mut receipt = None;
    let mut results = None;
    let mut ay = None;
    let mut z3 = None;
    let mut timeout_secs = 10u64;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--corpus-manifest" => {
                index += 1;
                corpus_manifest = Some(PathBuf::from(
                    args.get(index).ok_or("--corpus-manifest needs a path")?,
                ));
            }
            "--receipt" => {
                index += 1;
                receipt = Some(PathBuf::from(
                    args.get(index).ok_or("--receipt needs a path")?,
                ));
            }
            "--results" => {
                index += 1;
                results = Some(PathBuf::from(
                    args.get(index).ok_or("--results needs a path")?,
                ));
            }
            "--ay" => {
                index += 1;
                ay = Some(PathBuf::from(args.get(index).ok_or("--ay needs a path")?));
            }
            "--z3" => {
                index += 1;
                z3 = Some(PathBuf::from(args.get(index).ok_or("--z3 needs a path")?));
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
                return Err(format!("unknown official-corpus flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("official-corpus takes one contract".to_string());
                }
            }
        }
        index += 1;
    }
    Ok(RunArgs {
        manifest: manifest.ok_or("official-corpus needs a contract")?,
        corpus_manifest: corpus_manifest.ok_or("official-corpus requires --corpus-manifest")?,
        receipt: receipt.ok_or("official-corpus requires --receipt")?,
        results: results.ok_or("official-corpus requires --results")?,
        ay,
        z3,
        timeout_secs,
    })
}

fn source_from_metadata(bytes: &[u8]) -> Result<CorpusSource, String> {
    if sha256_bytes(bytes) != EXPECTED_RECORD_METADATA_SHA256 {
        return Err(format!(
            "Zenodo metadata bytes do not match pinned snapshot {EXPECTED_RECORD_METADATA_SHA256}"
        ));
    }
    let value: serde_json::Value = serde_json::from_slice(bytes)
        .map_err(|error| format!("invalid Zenodo record metadata JSON: {error}"))?;
    let id_matches = value
        .get("id")
        .and_then(serde_json::Value::as_u64)
        .is_some_and(|id| id.to_string() == RECORD_ID);
    if !id_matches {
        return Err(format!(
            "Zenodo metadata is not immutable record {RECORD_ID}"
        ));
    }
    if value.get("doi").and_then(serde_json::Value::as_str) != Some(RECORD_DOI) {
        return Err(format!("Zenodo metadata DOI is not {RECORD_DOI}"));
    }
    let files = value
        .get("files")
        .and_then(serde_json::Value::as_array)
        .ok_or("Zenodo metadata has no files array")?;
    let mut archives = Vec::new();
    for file in files {
        let key = file
            .get("key")
            .and_then(serde_json::Value::as_str)
            .ok_or("Zenodo file has no key")?;
        let Some(division) = key.strip_suffix(".tar.zst") else {
            continue;
        };
        validate_division(division)?;
        let size = file
            .get("size")
            .and_then(serde_json::Value::as_u64)
            .ok_or_else(|| format!("Zenodo archive {key:?} has no byte size"))?;
        if size == 0 {
            return Err(format!("Zenodo archive {key:?} is empty"));
        }
        let checksum = file
            .get("checksum")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| format!("Zenodo archive {key:?} has no checksum"))?;
        validate_md5(checksum)?;
        archives.push(CorpusArchive {
            division: division.to_string(),
            key: key.to_string(),
            size,
            checksum: checksum.to_string(),
        });
    }
    archives.sort_by(|left, right| left.division.cmp(&right.division));
    if archives.len() != EXPECTED_ARCHIVE_COUNT {
        return Err(format!(
            "record {RECORD_ID} must expose exactly {EXPECTED_ARCHIVE_COUNT} division archives; metadata has {}",
            archives.len()
        ));
    }
    if archives
        .windows(2)
        .any(|pair| pair[0].division >= pair[1].division)
    {
        return Err("Zenodo metadata repeats or misorders a division".to_string());
    }
    let archive_manifest_sha256 = archive_sha256(&archives)?;
    if archive_manifest_sha256 != EXPECTED_ARCHIVE_MANIFEST_SHA256 {
        return Err(format!(
            "Zenodo archive rows do not match pinned digest {EXPECTED_ARCHIVE_MANIFEST_SHA256}"
        ));
    }
    Ok(CorpusSource {
        name: "SMT-LIB 2024 non-incremental benchmark release".to_string(),
        record_id: RECORD_ID.to_string(),
        doi: RECORD_DOI.to_string(),
        api_url: RECORD_API.to_string(),
        record_metadata_sha256: EXPECTED_RECORD_METADATA_SHA256.to_string(),
        selection: SOURCE_SELECTION.to_string(),
        source_selection_sha256: EXPECTED_SOURCE_SELECTION_SHA256.to_string(),
        archive_count: archives.len(),
        archive_manifest_sha256,
        archives,
    })
}

fn validate_manifest(manifest: &OfficialCorpusManifest) -> Result<(), String> {
    if sha256_bytes(SOURCE_SELECTION_DESCRIPTOR.as_bytes()) != EXPECTED_SOURCE_SELECTION_SHA256 {
        return Err("compiled official corpus source-selection identity drift".to_string());
    }
    if manifest.schema != CORPUS_MANIFEST_SCHEMA || manifest.profile_id != PROFILE_ID {
        return Err("official corpus manifest schema or profile drift".to_string());
    }
    let source = &manifest.source;
    if source.name != "SMT-LIB 2024 non-incremental benchmark release"
        || source.record_id != RECORD_ID
        || source.doi != RECORD_DOI
        || source.api_url != RECORD_API
        || source.record_metadata_sha256 != EXPECTED_RECORD_METADATA_SHA256
        || source.selection != SOURCE_SELECTION
        || source.source_selection_sha256 != EXPECTED_SOURCE_SELECTION_SHA256
        || source.archive_count != EXPECTED_ARCHIVE_COUNT
        || source.archives.len() != EXPECTED_ARCHIVE_COUNT
    {
        return Err("official corpus source identity or all-archive selection drift".to_string());
    }
    if source.archive_manifest_sha256 != EXPECTED_ARCHIVE_MANIFEST_SHA256
        || source.archive_manifest_sha256 != archive_sha256(&source.archives)?
    {
        return Err("official corpus archive manifest digest mismatch".to_string());
    }
    let mut archive_divisions = BTreeSet::new();
    let mut previous_archive: Option<&str> = None;
    for archive in &source.archives {
        validate_division(&archive.division)?;
        if archive.key != format!("{}.tar.zst", archive.division)
            || archive.size == 0
            || previous_archive.is_some_and(|prior| prior >= archive.division.as_str())
        {
            return Err("official corpus archive inventory is malformed".to_string());
        }
        validate_md5(&archive.checksum)?;
        previous_archive = Some(&archive.division);
        archive_divisions.insert(archive.division.as_str());
    }
    let root = Path::new(&manifest.corpus_root);
    let archive_root = Path::new(&manifest.archive_root);
    if !root.is_absolute() || !archive_root.is_absolute() {
        return Err("official corpus manifest roots must be absolute".to_string());
    }
    validate_text(&manifest.corpus_root, "official corpus root")?;
    validate_text(&manifest.archive_root, "official corpus archive root")?;
    if manifest.file_count != EXPECTED_FILE_COUNT
        || manifest.query_count != EXPECTED_QUERY_COUNT
        || manifest.file_count != manifest.files.len()
    {
        return Err("official corpus manifest has empty or inconsistent counts".to_string());
    }
    let mut query_count = 0usize;
    let mut seen_divisions = BTreeSet::new();
    let mut previous_file: Option<&str> = None;
    for file in &manifest.files {
        validate_relative_path(&file.path, "official corpus file path")?;
        if previous_file.is_some_and(|prior| prior >= file.path.as_str())
            || file.size == 0
            || file.queries.is_empty()
        {
            return Err("official corpus file inventory is empty, duplicated, or unsorted".into());
        }
        previous_file = Some(&file.path);
        validate_sha256(&file.sha256, "official corpus file sha256")?;
        let mut components = Path::new(&file.path).components();
        let division = components
            .next()
            .and_then(|component| match component {
                Component::Normal(value) => value.to_str(),
                _ => None,
            })
            .ok_or("official corpus file has no division")?;
        if !archive_divisions.contains(division) || components.count() != 1 {
            return Err(format!(
                "official corpus path {:?} is not one flat file in an authenticated division",
                file.path
            ));
        }
        if Path::new(&file.path)
            .extension()
            .and_then(|value| value.to_str())
            != Some("smt2")
        {
            return Err(format!("official corpus path {:?} is not .smt2", file.path));
        }
        seen_divisions.insert(division.to_string());
        for (index, query) in file.queries.iter().enumerate() {
            if query.ordinal != index + 1
                || !matches!(
                    query.command.as_str(),
                    "check-sat" | "check-sat-assuming" | "check-sat-using"
                )
                || query.byte_start >= query.byte_end
                || query.byte_end > file.size
            {
                return Err(format!("malformed query row in {:?}", file.path));
            }
            validate_sha256(&query.command_sha256, "query command sha256")?;
            validate_sha256(&query.prefix_sha256, "query prefix sha256")?;
        }
        query_count = query_count
            .checked_add(file.queries.len())
            .ok_or("official corpus query count overflow")?;
    }
    if seen_divisions.len() != EXPECTED_ARCHIVE_COUNT
        || !source
            .archives
            .iter()
            .all(|archive| seen_divisions.contains(&archive.division))
    {
        return Err("one or more authenticated official divisions has no corpus file".to_string());
    }
    if query_count != manifest.query_count
        || manifest.selection_sha256 != selection_sha256(&manifest.files)?
    {
        return Err("official corpus per-file/per-query selection digest mismatch".to_string());
    }
    Ok(())
}

fn verify_materialization(manifest: &OfficialCorpusManifest) -> Result<(), String> {
    validate_manifest(manifest)?;
    let root = canonical_corpus_root(Path::new(&manifest.corpus_root))?;
    let archive_root = canonical_archive_root(Path::new(&manifest.archive_root))?;
    if root.to_string_lossy() != manifest.corpus_root {
        return Err("official corpus materialization root identity changed".to_string());
    }
    if archive_root.to_string_lossy() != manifest.archive_root {
        return Err("official corpus archive root identity changed".to_string());
    }
    let actual = collect_corpus_files(&root)?;
    let from_archives = collect_archive_files(&manifest.source, &archive_root)?;
    let actual_after_archive_replay = collect_corpus_files(&root)?;
    if actual != manifest.files
        || from_archives != manifest.files
        || actual_after_archive_replay != manifest.files
    {
        return Err(
            "official corpus materialization has missing, unexpected, changed, or query-drifted files"
                .to_string(),
        );
    }
    Ok(())
}

fn canonical_corpus_root(path: &Path) -> Result<PathBuf, String> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("inspecting corpus root {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_dir() {
        return Err(format!(
            "official corpus root must be a non-symlink directory: {}",
            path.display()
        ));
    }
    fs::canonicalize(path)
        .map_err(|error| format!("canonicalizing corpus root {}: {error}", path.display()))
}

fn canonical_archive_root(path: &Path) -> Result<PathBuf, String> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("inspecting archive root {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_dir() {
        return Err(format!(
            "official archive root must be a non-symlink directory: {}",
            path.display()
        ));
    }
    fs::canonicalize(path)
        .map_err(|error| format!("canonicalizing archive root {}: {error}", path.display()))
}

fn collect_archive_files(
    source: &CorpusSource,
    archive_root: &Path,
) -> Result<Vec<CorpusFile>, String> {
    let expected_names = source
        .archives
        .iter()
        .map(|archive| archive.key.as_str())
        .collect::<BTreeSet<_>>();
    let mut actual_names = BTreeSet::new();
    for entry in fs::read_dir(archive_root)
        .map_err(|error| format!("reading archive root {}: {error}", archive_root.display()))?
    {
        let entry = entry.map_err(|error| format!("reading archive root entry: {error}"))?;
        let path = entry.path();
        let metadata = fs::symlink_metadata(&path)
            .map_err(|error| format!("inspecting archive artifact {}: {error}", path.display()))?;
        if metadata.file_type().is_symlink() {
            return Err(format!(
                "official archive root contains a symlink: {}",
                path.display()
            ));
        }
        if metadata.is_file()
            && path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.ends_with(".tar.zst"))
        {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or_else(|| format!("archive name is not UTF-8: {}", path.display()))?;
            actual_names.insert(name.to_string());
        }
    }
    if actual_names
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>()
        != expected_names
    {
        return Err(
            "official archive root has a missing or unexpected .tar.zst artifact".to_string(),
        );
    }

    let mut files = Vec::new();
    for archive in &source.archives {
        let path = archive_root.join(&archive.key);
        let metadata = fs::symlink_metadata(&path)
            .map_err(|error| format!("inspecting archive {}: {error}", path.display()))?;
        if metadata.file_type().is_symlink()
            || !metadata.file_type().is_file()
            || metadata.len() != archive.size
        {
            return Err(format!(
                "official archive {} is absent, linked, non-regular, or has wrong size",
                path.display()
            ));
        }
        let expected_md5 = archive
            .checksum
            .strip_prefix("md5:")
            .ok_or("authenticated archive row lost its md5 prefix")?;
        let actual_md5 = md5_of(&path)?;
        if actual_md5 != expected_md5 {
            return Err(format!(
                "official archive {} md5 mismatch: expected {expected_md5}, got {actual_md5}",
                path.display()
            ));
        }
        files.extend(read_archive_members(&path, &archive.division)?);
        let post_metadata = fs::symlink_metadata(&path).map_err(|error| {
            format!(
                "re-inspecting archive {} after decode: {error}",
                path.display()
            )
        })?;
        if post_metadata.file_type().is_symlink()
            || !post_metadata.file_type().is_file()
            || post_metadata.len() != archive.size
            || md5_of(&path)? != expected_md5
        {
            return Err(format!(
                "official archive {} changed while its members were authenticated",
                path.display()
            ));
        }
    }
    files.sort_by(|left, right| left.path.cmp(&right.path));
    if files.is_empty() || files.windows(2).any(|pair| pair[0].path >= pair[1].path) {
        return Err(
            "authenticated official archives contain no SMT-LIB files or flattening collisions"
                .to_string(),
        );
    }
    Ok(files)
}

fn read_archive_members(path: &Path, division: &str) -> Result<Vec<CorpusFile>, String> {
    let mut child = Command::new("unzstd")
        .arg("-c")
        .arg("--")
        .arg(path)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|error| format!("starting unzstd for {}: {error}", path.display()))?;
    let mut stdout = child
        .stdout
        .take()
        .ok_or_else(|| format!("unzstd has no stdout for {}", path.display()))?;
    let parsed = parse_tar_stream(&mut stdout, division);
    drop(stdout);
    if parsed.is_err() {
        let _ = child.kill();
    }
    let status = child
        .wait()
        .map_err(|error| format!("waiting for unzstd {}: {error}", path.display()))?;
    let files = parsed?;
    if !status.success() {
        return Err(format!(
            "unzstd failed for authenticated archive {} ({status})",
            path.display()
        ));
    }
    if files.is_empty() {
        return Err(format!(
            "authenticated archive {} contains no .smt2 members",
            path.display()
        ));
    }
    Ok(files)
}

fn parse_tar_stream(reader: &mut impl Read, division: &str) -> Result<Vec<CorpusFile>, String> {
    let mut files = Vec::new();
    loop {
        let mut header = [0u8; 512];
        reader
            .read_exact(&mut header)
            .map_err(|error| format!("reading tar header: {error}"))?;
        if header.iter().all(|byte| *byte == 0) {
            break;
        }
        validate_tar_checksum(&header)?;
        let name = tar_member_name(&header)?;
        let size = tar_octal(&header[124..136], "tar member size")?;
        let kind = header[156];
        if !matches!(kind, 0 | b'0' | b'5') {
            return Err(format!(
                "authenticated archive contains unsupported tar entry type {kind:?} at {name:?}"
            ));
        }
        let is_regular = matches!(kind, 0 | b'0');
        let is_smt2 = is_regular
            && Path::new(&name)
                .extension()
                .and_then(|value| value.to_str())
                == Some("smt2");
        if size > MAX_CORPUS_FILE_BYTES && is_smt2 {
            return Err(format!(
                "archive member {name:?} exceeds the fixed file limit"
            ));
        }
        if is_smt2 {
            let size_usize = usize::try_from(size)
                .map_err(|_| format!("archive member {name:?} does not fit memory"))?;
            let mut bytes = vec![0u8; size_usize];
            reader
                .read_exact(&mut bytes)
                .map_err(|error| format!("reading archive member {name:?}: {error}"))?;
            if bytes.is_empty() {
                return Err(format!("official archive member {name:?} is empty"));
            }
            let normalized = normalized_tar_member(&name)?;
            let flat = normalized.replace('/', "__");
            let queries = scan_queries(&bytes)
                .map_err(|error| format!("scanning archive member {name:?}: {error}"))?;
            if queries.is_empty() {
                return Err(format!("official archive member {name:?} has no query"));
            }
            files.push(CorpusFile {
                path: format!("{division}/{flat}"),
                size,
                sha256: sha256_bytes(&bytes),
                queries,
            });
        } else {
            let mut limited = reader.by_ref().take(size);
            let copied = std::io::copy(&mut limited, &mut std::io::sink())
                .map_err(|error| format!("discarding archive member {name:?}: {error}"))?;
            if copied != size {
                return Err(format!("archive member {name:?} is truncated"));
            }
        }
        let padding = (512 - (size % 512)) % 512;
        if padding > 0 {
            let mut limited = reader.by_ref().take(padding);
            let copied = std::io::copy(&mut limited, &mut std::io::sink())
                .map_err(|error| format!("discarding tar padding after {name:?}: {error}"))?;
            if copied != padding {
                return Err(format!("tar padding after {name:?} is truncated"));
            }
        }
    }
    files.sort_by(|left, right| left.path.cmp(&right.path));
    if files.windows(2).any(|pair| pair[0].path >= pair[1].path) {
        return Err(format!(
            "archive division {division} has a duplicate flattened SMT-LIB member"
        ));
    }
    Ok(files)
}

fn tar_member_name(header: &[u8; 512]) -> Result<String, String> {
    let name = tar_text(&header[..100], "tar member name")?;
    let prefix = tar_text(&header[345..500], "tar member prefix")?;
    if name.is_empty() {
        return Err("tar entry has an empty member name".to_string());
    }
    let joined = if prefix.is_empty() {
        name
    } else {
        format!("{prefix}/{name}")
    };
    normalized_tar_member(&joined)
}

fn tar_text(bytes: &[u8], label: &str) -> Result<String, String> {
    let end = bytes
        .iter()
        .position(|byte| *byte == 0)
        .unwrap_or(bytes.len());
    std::str::from_utf8(&bytes[..end])
        .map(str::to_string)
        .map_err(|_| format!("{label} is not UTF-8"))
}

fn normalized_tar_member(value: &str) -> Result<String, String> {
    let path = Path::new(value);
    if path.is_absolute() {
        return Err(format!("tar member is absolute: {value:?}"));
    }
    let mut parts = Vec::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::Normal(part) => parts.push(
                part.to_str()
                    .ok_or("tar member path is not UTF-8")?
                    .to_string(),
            ),
            _ => return Err(format!("unsafe tar member path {value:?}")),
        }
    }
    if parts.is_empty() {
        return Err(format!("empty normalized tar member path {value:?}"));
    }
    Ok(parts.join("/"))
}

fn tar_octal(bytes: &[u8], label: &str) -> Result<u64, String> {
    let text = std::str::from_utf8(bytes).map_err(|_| format!("{label} is not ASCII"))?;
    let text = text.trim_matches(|character| matches!(character, '\0' | ' '));
    if text.is_empty() {
        return Ok(0);
    }
    if !text.bytes().all(|byte| (b'0'..=b'7').contains(&byte)) {
        return Err(format!("{label} is not octal"));
    }
    u64::from_str_radix(text, 8).map_err(|_| format!("{label} overflows u64"))
}

fn validate_tar_checksum(header: &[u8; 512]) -> Result<(), String> {
    let expected = tar_octal(&header[148..156], "tar checksum")?;
    let actual = header
        .iter()
        .enumerate()
        .try_fold(0u64, |sum, (index, byte)| {
            let value = if (148..156).contains(&index) {
                u64::from(b' ')
            } else {
                u64::from(*byte)
            };
            sum.checked_add(value).ok_or("tar checksum overflow")
        })?;
    if actual != expected {
        return Err(format!(
            "tar header checksum mismatch: expected {expected}, got {actual}"
        ));
    }
    Ok(())
}

fn md5_of(path: &Path) -> Result<String, String> {
    match Command::new("md5").arg("-q").arg(path).output() {
        Ok(output) if output.status.success() => Ok(String::from_utf8_lossy(&output.stdout)
            .trim()
            .to_ascii_lowercase()),
        Ok(output) => Err(format!(
            "md5 -q failed for {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            let output = Command::new("md5sum")
                .arg(path)
                .output()
                .map_err(|error| format!("starting md5sum for {}: {error}", path.display()))?;
            if !output.status.success() {
                return Err(format!(
                    "md5sum failed for {}: {}",
                    path.display(),
                    String::from_utf8_lossy(&output.stderr).trim()
                ));
            }
            String::from_utf8_lossy(&output.stdout)
                .split_whitespace()
                .next()
                .map(str::to_ascii_lowercase)
                .ok_or_else(|| format!("md5sum produced no digest for {}", path.display()))
        }
        Err(error) => Err(format!("starting md5 for {}: {error}", path.display())),
    }
}

fn collect_corpus_files(root: &Path) -> Result<Vec<CorpusFile>, String> {
    let mut paths = Vec::new();
    collect_smt2_paths(root, root, &mut paths)?;
    paths.sort();
    if paths.is_empty() {
        return Err("official corpus root contains no .smt2 files".to_string());
    }
    let mut files = Vec::with_capacity(paths.len());
    for relative in paths {
        let full = root.join(&relative);
        let bytes = read_bounded_bytes(
            &full,
            MAX_CORPUS_FILE_BYTES,
            "official corpus SMT-LIB file",
            true,
        )?;
        if bytes.is_empty() {
            return Err(format!("official corpus file is empty: {}", full.display()));
        }
        let queries = scan_queries(&bytes).map_err(|error| {
            format!(
                "enumerating decision queries in {}: {error}",
                full.display()
            )
        })?;
        if queries.is_empty() {
            return Err(format!(
                "official corpus file has no decision query: {}",
                full.display()
            ));
        }
        files.push(CorpusFile {
            path: relative
                .to_str()
                .ok_or_else(|| format!("corpus path is not UTF-8: {}", relative.display()))?
                .replace(std::path::MAIN_SEPARATOR, "/"),
            size: u64::try_from(bytes.len())
                .map_err(|_| "official corpus file size does not fit u64")?,
            sha256: sha256_bytes(&bytes),
            queries,
        });
    }
    files.sort_by(|left, right| left.path.cmp(&right.path));
    Ok(files)
}

fn collect_smt2_paths(root: &Path, directory: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let mut entries = fs::read_dir(directory)
        .map_err(|error| format!("reading corpus directory {}: {error}", directory.display()))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("reading corpus directory {}: {error}", directory.display()))?;
    entries.sort_by_key(fs::DirEntry::file_name);
    for entry in entries {
        let path = entry.path();
        let metadata = fs::symlink_metadata(&path)
            .map_err(|error| format!("inspecting corpus entry {}: {error}", path.display()))?;
        if metadata.file_type().is_symlink() {
            return Err(format!(
                "official corpus materialization contains a symlink: {}",
                path.display()
            ));
        }
        if metadata.is_dir() {
            collect_smt2_paths(root, &path, out)?;
        } else if metadata.is_file()
            && path.extension().and_then(|extension| extension.to_str()) == Some("smt2")
        {
            let relative = path
                .strip_prefix(root)
                .map_err(|_| format!("corpus path escapes root: {}", path.display()))?;
            out.push(relative.to_path_buf());
        }
    }
    Ok(())
}

fn scan_queries(bytes: &[u8]) -> Result<Vec<CorpusQuery>, String> {
    let mut queries = Vec::new();
    let mut depth = 0usize;
    let mut expression_start = None;
    let mut expression_head: Option<String> = None;
    let mut index = 0usize;
    while index < bytes.len() {
        match bytes[index] {
            b';' => skip_comment(bytes, &mut index),
            b'"' => skip_string(bytes, &mut index)?,
            b'|' => skip_quoted_symbol(bytes, &mut index)?,
            b'(' => {
                if depth == 0 {
                    expression_start = Some(index);
                    expression_head = top_level_head(bytes, index + 1)?;
                }
                depth = depth.checked_add(1).ok_or("parenthesis depth overflow")?;
                index += 1;
            }
            b')' => {
                if depth == 0 {
                    return Err(format!("unexpected `)` at byte {index}"));
                }
                depth -= 1;
                index += 1;
                if depth == 0 {
                    let start = expression_start.take().ok_or("missing expression start")?;
                    if let Some(command) = expression_head.take().filter(|head| {
                        matches!(
                            head.as_str(),
                            "check-sat" | "check-sat-assuming" | "check-sat-using"
                        )
                    }) {
                        let end = index;
                        queries.push(CorpusQuery {
                            ordinal: queries.len() + 1,
                            command,
                            byte_start: u64::try_from(start)
                                .map_err(|_| "query start does not fit u64")?,
                            byte_end: u64::try_from(end)
                                .map_err(|_| "query end does not fit u64")?,
                            command_sha256: sha256_bytes(&bytes[start..end]),
                            prefix_sha256: sha256_bytes(&bytes[..end]),
                        });
                    }
                }
            }
            byte if depth == 0 && !byte.is_ascii_whitespace() => {
                return Err(format!(
                    "top-level SMT-LIB input is not a parenthesized command at byte {index}"
                ));
            }
            _ => index += 1,
        }
    }
    if depth != 0 {
        return Err("unterminated top-level S-expression".to_string());
    }
    Ok(queries)
}

fn top_level_head(bytes: &[u8], mut index: usize) -> Result<Option<String>, String> {
    loop {
        while index < bytes.len() && bytes[index].is_ascii_whitespace() {
            index += 1;
        }
        if index < bytes.len() && bytes[index] == b';' {
            skip_comment(bytes, &mut index);
            continue;
        }
        break;
    }
    if index >= bytes.len() || bytes[index] == b')' {
        return Ok(None);
    }
    if matches!(bytes[index], b'(' | b'"' | b'|') {
        return Ok(None);
    }
    let start = index;
    while index < bytes.len()
        && !bytes[index].is_ascii_whitespace()
        && !matches!(bytes[index], b'(' | b')' | b';')
    {
        index += 1;
    }
    let head = std::str::from_utf8(&bytes[start..index])
        .map_err(|_| "top-level command head is not UTF-8")?;
    Ok(Some(head.to_string()))
}

fn skip_comment(bytes: &[u8], index: &mut usize) {
    while *index < bytes.len() && !matches!(bytes[*index], b'\n' | b'\r') {
        *index += 1;
    }
}

fn skip_string(bytes: &[u8], index: &mut usize) -> Result<(), String> {
    *index += 1;
    while *index < bytes.len() {
        if bytes[*index] == b'"' {
            if bytes.get(*index + 1) == Some(&b'"') {
                *index += 2;
            } else {
                *index += 1;
                return Ok(());
            }
        } else if bytes[*index] == b'\\' && bytes.get(*index + 1).is_some() {
            // Older SMT-LIB corpora contain the pre-2.6 backslash spelling.
            *index += 2;
        } else {
            *index += 1;
        }
    }
    Err("unterminated string literal".to_string())
}

fn skip_quoted_symbol(bytes: &[u8], index: &mut usize) -> Result<(), String> {
    *index += 1;
    while *index < bytes.len() {
        if bytes[*index] == b'|' {
            *index += 1;
            return Ok(());
        }
        if bytes[*index] == b'\\' && bytes.get(*index + 1).is_some() {
            *index += 2;
        } else {
            *index += 1;
        }
    }
    Err("unterminated quoted symbol".to_string())
}

fn execute_semantic(
    contract: &Contract,
    inventory_sha256: &str,
    manifest: &OfficialCorpusManifest,
    manifest_sha256: &str,
    ay_source: &Path,
    z3_source: &Path,
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<SemanticExecution, String> {
    verify_materialization(manifest)?;
    let subject = contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("official corpus requires subject.ay_executable")?;
    let z3_sha256 = &contract.profile.z3_overlay.reference_executable.sha256;
    let staged_ay = stage_authenticated_executable(ay_source, &subject.sha256, "AY executable")?;
    let staged_z3 = stage_authenticated_executable(z3_source, z3_sha256, "Z3 5.0.0 executable")?;
    let repo_root = locate_repo_root()?;
    let resources = PlannedResources::plan(
        &repo_root,
        1,
        "ay-z3-parity smtlib-conformance official-corpus",
    )
    .map_err(|error| error.to_string())?;
    let resource_envelope = effective_execution_envelope(
        &resources.plan,
        ENFORCEMENT_RSS_WATCHDOG_V1,
        timeout.as_secs_f64(),
    )
    .map_err(|error| error.to_string())?;
    if required_envelope.is_some_and(|expected| expected != resource_envelope) {
        return Err("live official-corpus resource envelope drift".to_string());
    }
    if resources.plan.jobs != 1 {
        return Err(
            "official corpus planner did not preserve the required one-job run".to_string(),
        );
    }

    let root = PathBuf::from(&manifest.corpus_root);
    let mut files = Vec::with_capacity(manifest.files.len());
    for file in &manifest.files {
        files.push(run_file(
            &resources,
            &staged_ay.path,
            &staged_z3.path,
            &root.join(&file.path),
            file,
            timeout,
        ));
    }
    if sha256_file(&staged_ay.path, "staged AY after official corpus")? != subject.sha256
        || sha256_file(&staged_z3.path, "staged Z3 after official corpus")? != *z3_sha256
    {
        return Err("authenticated solver bytes changed during official corpus run".to_string());
    }
    // A second full closure scan detects mutation, deletion, replacement, or
    // additions that happened while the long campaign was running.
    verify_materialization(manifest)?;
    let counts = derive_run_counts(&files)?;
    let run_results = CorpusRunResults {
        schema: RUN_RESULTS_SCHEMA.to_string(),
        created_unix_ms: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| format!("reading system clock: {error}"))?
            .as_millis(),
        campaign_id: contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        inventory_sha256: inventory_sha256.to_string(),
        corpus_manifest_sha256: manifest_sha256.to_string(),
        corpus_selection_sha256: manifest.selection_sha256.clone(),
        corpus_root: manifest.corpus_root.clone(),
        ay_sha256: subject.sha256.clone(),
        z3_sha256: z3_sha256.clone(),
        resource_envelope,
        ay_mode: "solve --quiet --competition --strict-proofs --self-check --memory <planned-MiB> <file>; rss-watchdog".to_string(),
        z3_mode: "z3-5.0.0 -smt2 <file>; rss-watchdog".to_string(),
        counts,
        files,
    };
    let case_results = aggregate_cases(&run_results.counts, &manifest.selection_sha256);
    Ok(SemanticExecution {
        result: overall_validator_result(&case_results),
        cases: case_counts_from_rows(&case_results)?,
        case_results,
        run_results,
    })
}

fn run_file(
    resources: &PlannedResources,
    ay: &Path,
    z3: &Path,
    path: &Path,
    file: &CorpusFile,
    timeout: Duration,
) -> FileRun {
    // Sequential oracle/subject execution is load-bearing: the planner admitted
    // one child, so two simultaneous processes would make its budget fiction.
    let z3_args = [OsString::from("-smt2"), path.as_os_str().to_owned()];
    let z3_run = match resources.run_external_transcript(
        z3,
        z3_args,
        b"",
        timeout,
        &format!("official corpus Z3 {}", file.path),
    ) {
        Ok(output) => process_run(output),
        Err(error) => ProcessRun::unavailable(error.to_string()),
    };
    let ay_args = [
        OsString::from("solve"),
        OsString::from("--quiet"),
        OsString::from("--competition"),
        OsString::from("--strict-proofs"),
        OsString::from("--self-check"),
        OsString::from("--memory"),
        OsString::from(resources.plan.memlimit_mb_per_child.to_string()),
        path.as_os_str().to_owned(),
    ];
    let ay_run = match resources.run_external_transcript(
        ay,
        ay_args,
        b"",
        timeout,
        &format!("official corpus AY {}", file.path),
    ) {
        Ok(output) => process_run(output),
        Err(error) => ProcessRun::unavailable(error.to_string()),
    };
    classify_file(file, ay_run, z3_run)
}

fn process_run(output: GuardedTranscriptOutput) -> ProcessRun {
    let stdout_sha256 = sha256_bytes(&output.stdout);
    let stderr_sha256 = sha256_bytes(&output.stderr);
    let stdout = String::from_utf8(output.stdout);
    let stderr = String::from_utf8(output.stderr);
    let stdout_utf8 = stdout.is_ok();
    let stderr_utf8 = stderr.is_ok();
    let stdout_text = stdout.unwrap_or_default();
    let stderr_text = stderr.unwrap_or_default();
    let error_diagnostic = stdout_text
        .lines()
        .chain(stderr_text.lines())
        .any(is_error_diagnostic);
    let observed_ns = u64::try_from(output.observed.as_nanos()).unwrap_or(u64::MAX);
    ProcessRun {
        exit_code: output.status.and_then(|status| status.code()),
        stdin_complete: output.stdin_complete,
        timed_out: output.timed_out,
        memout: output.memout,
        stdout_truncated: output.stdout_truncated,
        stderr_truncated: output.stderr_truncated,
        stdout_utf8,
        stderr_utf8,
        error_diagnostic,
        harness_error: None,
        stdout_sha256,
        stderr_sha256,
        observed_ns,
        verdicts: stdout_text
            .lines()
            .filter_map(CorpusVerdict::parse)
            .collect(),
    }
}

fn is_error_diagnostic(line: &str) -> bool {
    let line = line.trim_start();
    line.starts_with("(error")
        || line.starts_with("error:")
        || line.starts_with("Error:")
        || line.starts_with("unsupported")
}

fn classify_file(file: &CorpusFile, ay: ProcessRun, z3: ProcessRun) -> FileRun {
    let mut queries = Vec::with_capacity(file.queries.len());
    for query in &file.queries {
        let z3_verdict = z3.verdicts.get(query.ordinal - 1).copied();
        let ay_verdict = ay.verdicts.get(query.ordinal - 1).copied();
        let outcome = match (z3_verdict, ay_verdict) {
            (Some(expected), Some(observed)) if expected == observed => QueryOutcome::Pass,
            (Some(_), Some(_)) => QueryOutcome::Wrong,
            _ => QueryOutcome::Missing,
        };
        let certification = match ay_verdict {
            Some(CorpusVerdict::Sat) => {
                "sat emitted while --self-check was requested; independent authority is owned by results.sat-models, not this corpus receipt"
            }
            Some(CorpusVerdict::Unsat) => {
                "unsat emitted while --self-check --strict-proofs were requested; independent authority is owned by results.unsat-proofs, not this corpus receipt"
            }
            Some(CorpusVerdict::Unknown) => "no decided AY artifact published",
            None => "AY published no verdict for query epoch",
        }
        .to_string();
        queries.push(QueryRun {
            ordinal: query.ordinal,
            command: query.command.clone(),
            prefix_sha256: query.prefix_sha256.clone(),
            z3: z3_verdict,
            ay: ay_verdict,
            certification,
            outcome,
        });
    }
    let outcome = classify_file_outcome(file, &ay, &z3, &queries);
    FileRun {
        path: file.path.clone(),
        input_sha256: file.sha256.clone(),
        query_count: file.queries.len(),
        ay,
        z3,
        queries,
        outcome,
    }
}

fn classify_file_outcome(
    file: &CorpusFile,
    ay: &ProcessRun,
    z3: &ProcessRun,
    queries: &[QueryRun],
) -> FileOutcome {
    let expected_query_count = file.queries.len();
    if ay.memout || z3.memout {
        FileOutcome::Memout
    } else if ay.timed_out || z3.timed_out {
        FileOutcome::Timeout
    } else if ay.harness_error.is_some() || z3.harness_error.is_some() {
        FileOutcome::Unavailable
    } else if ay.exit_code.is_none() || z3.exit_code.is_none() {
        FileOutcome::Crash
    } else if !ay.is_complete()
        || !z3.is_complete()
        || ay.verdicts.len() != expected_query_count
        || z3.verdicts.len() != expected_query_count
        || queries
            .iter()
            .any(|query| query.outcome != QueryOutcome::Pass)
    {
        FileOutcome::Fail
    } else {
        FileOutcome::Pass
    }
}

fn derive_run_counts(files: &[FileRun]) -> Result<CorpusRunCounts, String> {
    let mut counts = CorpusRunCounts {
        files_total: files.len(),
        ..CorpusRunCounts::default()
    };
    for file in files {
        if file.outcome == FileOutcome::Pass {
            counts.files_passed += 1;
        } else {
            counts.files_failed += 1;
        }
        counts.timed_out += usize::from(file.outcome == FileOutcome::Timeout);
        counts.memout += usize::from(file.outcome == FileOutcome::Memout);
        counts.crashed += usize::from(file.outcome == FileOutcome::Crash);
        counts.unavailable += usize::from(file.outcome == FileOutcome::Unavailable);
        counts.diagnostic_errors +=
            usize::from(file.ay.error_diagnostic) + usize::from(file.z3.error_diagnostic);
        counts.truncated_outputs += usize::from(file.ay.stdout_truncated)
            + usize::from(file.ay.stderr_truncated)
            + usize::from(file.z3.stdout_truncated)
            + usize::from(file.z3.stderr_truncated);
        counts.queries_total = counts
            .queries_total
            .checked_add(file.queries.len())
            .ok_or("official corpus result query count overflow")?;
        for query in &file.queries {
            match query.outcome {
                QueryOutcome::Pass => counts.parity_passed += 1,
                QueryOutcome::Wrong => counts.wrong += 1,
                QueryOutcome::Missing => counts.missing += 1,
            }
            if query.z3 == Some(CorpusVerdict::Unknown) {
                counts.oracle_unknown += 1;
            }
            if query.z3.is_some_and(CorpusVerdict::decided)
                && !query.ay.is_some_and(CorpusVerdict::decided)
            {
                counts.z3_decided_ay_missing += 1;
            }
            match query.ay {
                Some(CorpusVerdict::Sat) => counts.ay_sat += 1,
                Some(CorpusVerdict::Unsat) => counts.ay_unsat += 1,
                Some(CorpusVerdict::Unknown) | None => {}
            }
        }
        let extra_ay = file.ay.verdicts.len().saturating_sub(file.query_count);
        let extra_z3 = file.z3.verdicts.len().saturating_sub(file.query_count);
        counts.missing = counts
            .missing
            .checked_add(extra_ay)
            .and_then(|value| value.checked_add(extra_z3))
            .ok_or("official corpus extra-verdict count overflow")?;
    }
    Ok(counts)
}

fn validate_run_results(
    results: &CorpusRunResults,
    contract: &Contract,
    inventory_sha256: &str,
    manifest: &OfficialCorpusManifest,
    manifest_sha256: &str,
) -> Result<(), String> {
    if results.schema != RUN_RESULTS_SCHEMA
        || results.campaign_id != contract.campaign_id
        || results.profile_id != PROFILE_ID
        || results.profile_sha256 != canonical_profile_sha256()?
        || results.inventory_sha256 != inventory_sha256
        || results.corpus_manifest_sha256 != manifest_sha256
        || results.corpus_selection_sha256 != manifest.selection_sha256
        || results.corpus_root != manifest.corpus_root
        || results.resource_envelope != contract.resource_envelope.as_deref().unwrap_or_default()
        || results.ay_mode
            != "solve --quiet --competition --strict-proofs --self-check --memory <planned-MiB> <file>; rss-watchdog"
        || results.z3_mode != "z3-5.0.0 -smt2 <file>; rss-watchdog"
    {
        return Err("official corpus result campaign/profile/mode binding drift".to_string());
    }
    let subject = contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("official corpus results require subject.ay_executable")?;
    if results.ay_sha256 != subject.sha256
        || results.z3_sha256 != contract.profile.z3_overlay.reference_executable.sha256
        || results.files.len() != manifest.files.len()
    {
        return Err("official corpus result artifact or file count binding drift".to_string());
    }
    for (result, file) in results.files.iter().zip(&manifest.files) {
        let expected_input_sha256 = file.sha256.as_str();
        if result.path != file.path
            || result.input_sha256.as_str() != expected_input_sha256
            || result.query_count != file.queries.len()
            || result.queries.len() != file.queries.len()
        {
            return Err(format!(
                "official corpus result row drift for {:?}",
                file.path
            ));
        }
        for (query_result, query) in result.queries.iter().zip(&file.queries) {
            if query_result.ordinal != query.ordinal
                || query_result.command != query.command
                || query_result.prefix_sha256 != query.prefix_sha256
            {
                return Err(format!(
                    "official corpus query identity drift in {:?}",
                    file.path
                ));
            }
        }
        let canonical = classify_file(file, result.ay.clone(), result.z3.clone());
        if canonical.queries != result.queries || canonical.outcome != result.outcome {
            return Err(format!(
                "official corpus result classification was forged for {:?}",
                file.path
            ));
        }
    }
    let derived = derive_run_counts(&results.files)?;
    if results.counts != derived {
        return Err("official corpus aggregate counts do not match per-query rows".to_string());
    }
    Ok(())
}

fn aggregate_cases(counts: &CorpusRunCounts, input_sha256: &str) -> Vec<ValidatorCase> {
    let execution_outcome = if counts.memout > 0 {
        ValidatorCaseOutcome::Memout
    } else if counts.timed_out > 0 {
        ValidatorCaseOutcome::Timeout
    } else if counts.crashed > 0 {
        ValidatorCaseOutcome::Crash
    } else if counts.unavailable > 0 {
        ValidatorCaseOutcome::Unavailable
    } else if counts.files_failed > 0
        || counts.diagnostic_errors > 0
        || counts.truncated_outputs > 0
    {
        ValidatorCaseOutcome::Fail
    } else {
        ValidatorCaseOutcome::Pass
    };
    let parity_ok = counts.parity_passed == counts.queries_total
        && counts.wrong == 0
        && counts.missing == 0
        && counts.z3_decided_ay_missing == 0;
    let mut rows = vec![
        aggregate_case(
            "corpus.execution.children",
            input_sha256,
            "all AY and Z3 children complete under the persisted watchdog envelope",
            format!(
                "files={};failed={};timeout={};memout={};crash={};unavailable={};diagnostics={};truncated={}",
                counts.files_total,
                counts.files_failed,
                counts.timed_out,
                counts.memout,
                counts.crashed,
                counts.unavailable,
                counts.diagnostic_errors,
                counts.truncated_outputs
            ),
            execution_outcome,
        ),
        aggregate_case(
            "corpus.parity.verdicts",
            input_sha256,
            "every manifest query has exact ordered AY/Z3 verdict parity, including unknown",
            format!(
                "queries={};parity={};wrong={};missing={};z3-decided-ay-missing={};z3-unknown={};ay-sat={};ay-unsat={}",
                counts.queries_total,
                counts.parity_passed,
                counts.wrong,
                counts.missing,
                counts.z3_decided_ay_missing,
                counts.oracle_unknown,
                counts.ay_sat,
                counts.ay_unsat
            ),
            if parity_ok {
                ValidatorCaseOutcome::Pass
            } else {
                ValidatorCaseOutcome::Fail
            },
        ),
        aggregate_case(
            "corpus.selection.closed",
            input_sha256,
            "all immutable manifest files and queries are represented exactly once",
            format!(
                "files={};queries={};complete={}",
                counts.files_total,
                counts.queries_total,
                counts.complete()
            ),
            if counts.complete() {
                ValidatorCaseOutcome::Pass
            } else {
                ValidatorCaseOutcome::Fail
            },
        ),
    ];
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    rows
}

fn aggregate_case(
    id: &str,
    input_sha256: &str,
    expected: &str,
    observed: String,
    outcome: ValidatorCaseOutcome,
) -> ValidatorCase {
    ValidatorCase {
        id: id.to_string(),
        input_sha256: input_sha256.to_string(),
        expected: expected.to_string(),
        observed,
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome,
    }
}

fn inventory_cases(manifest: &OfficialCorpusManifest, manifest_sha256: &str) -> Vec<ValidatorCase> {
    let mut rows = vec![
        aggregate_case(
            "corpus.inventory.archive-source",
            manifest_sha256,
            "exact immutable Zenodo 11061097 identity and all 84 archive metadata rows",
            format!(
                "record={};doi={};archives={};archive-sha256={}",
                manifest.source.record_id,
                manifest.source.doi,
                manifest.source.archive_count,
                manifest.source.archive_manifest_sha256
            ),
            ValidatorCaseOutcome::Pass,
        ),
        aggregate_case(
            "corpus.inventory.files",
            manifest_sha256,
            "every materialized .smt2 file is sorted, unique, and content-addressed",
            format!("files={}", manifest.file_count),
            ValidatorCaseOutcome::Pass,
        ),
        aggregate_case(
            "corpus.inventory.materialization",
            manifest_sha256,
            "the live corpus root has zero missing, unexpected, symlinked, or changed .smt2 files",
            format!("root={};closed=true", manifest.corpus_root),
            ValidatorCaseOutcome::Pass,
        ),
        aggregate_case(
            "corpus.inventory.queries",
            manifest_sha256,
            "every decision-query epoch has command, byte range, command hash, and prefix hash",
            format!("queries={}", manifest.query_count),
            ValidatorCaseOutcome::Pass,
        ),
        aggregate_case(
            "corpus.inventory.selection-digest",
            manifest_sha256,
            "the complete per-file/per-query selection has one canonical digest",
            format!("selection-sha256={}", manifest.selection_sha256),
            ValidatorCaseOutcome::Pass,
        ),
    ];
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    rows
}

fn archive_sha256(archives: &[CorpusArchive]) -> Result<String, String> {
    canonical_rows_sha256(archives, "archive manifest")
}

fn selection_sha256(files: &[CorpusFile]) -> Result<String, String> {
    canonical_rows_sha256(files, "official corpus selection")
}

fn canonical_rows_sha256<T: Serialize>(rows: &[T], label: &str) -> Result<String, String> {
    let mut hasher = Sha256::new();
    for row in rows {
        let bytes =
            serde_json::to_vec(row).map_err(|error| format!("serializing {label} row: {error}"))?;
        hasher.update(bytes);
        hasher.update(b"\n");
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn validate_division(value: &str) -> Result<(), String> {
    if value.is_empty()
        || value.len() > 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_uppercase() || byte.is_ascii_digit() || byte == b'_')
    {
        return Err(format!("invalid official SMT-LIB division name {value:?}"));
    }
    Ok(())
}

fn validate_md5(value: &str) -> Result<(), String> {
    let digest = value
        .strip_prefix("md5:")
        .ok_or("official archive checksum must use md5:<hex>")?;
    if digest.len() != 32
        || !digest
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("official archive md5 is malformed".to_string());
    }
    Ok(())
}

fn load_corpus_manifest(path: &Path) -> Result<(OfficialCorpusManifest, Vec<u8>), String> {
    let bytes = read_bounded_bytes(
        path,
        MAX_CORPUS_MANIFEST_BYTES,
        "official corpus manifest",
        true,
    )?;
    let manifest: OfficialCorpusManifest = serde_json::from_slice(&bytes).map_err(|error| {
        format!(
            "invalid official corpus manifest {}: {error}",
            path.display()
        )
    })?;
    validate_manifest(&manifest)?;
    Ok((manifest, bytes))
}

fn manifest_from_reference(
    receipt: &ValidatorReceipt,
    base: &Path,
    index: usize,
) -> Result<(OfficialCorpusManifest, Vec<u8>), String> {
    let input = receipt
        .reference_inputs
        .get(index)
        .ok_or("official corpus manifest reference is missing")?;
    let path = resolve_relative_evidence_path(base, &input.snapshot.path)?;
    load_corpus_manifest(&path)
}

fn results_from_reference(
    receipt: &ValidatorReceipt,
    base: &Path,
    index: usize,
) -> Result<(CorpusRunResults, Vec<u8>), String> {
    let input = receipt
        .reference_inputs
        .get(index)
        .ok_or("official corpus results reference is missing")?;
    let path = resolve_relative_evidence_path(base, &input.snapshot.path)?;
    let bytes = read_bounded_bytes(
        &path,
        MAX_CORPUS_RESULTS_BYTES,
        "official corpus results",
        true,
    )?;
    let results = serde_json::from_slice(&bytes).map_err(|error| {
        format!(
            "invalid official corpus results {}: {error}",
            path.display()
        )
    })?;
    Ok((results, bytes))
}

fn manifest_reference_input(
    manifest: &OfficialCorpusManifest,
    path: String,
    artifact_sha256: String,
) -> ReferenceInput {
    ReferenceInput {
        id: "official-corpus-manifest".to_string(),
        cohort: SourceCohort::OfficialCorpus,
        repository: RECORD_API.to_string(),
        revision: format!(
            "record={};metadata-sha256={}",
            RECORD_ID, manifest.source.record_metadata_sha256
        ),
        selection: SOURCE_SELECTION.to_string(),
        item_count: manifest.query_count,
        digest_kind: "canonical-per-file-per-query-json-lines-sha256/v1".to_string(),
        selection_sha256: manifest.selection_sha256.clone(),
        snapshot: Artifact {
            path,
            sha256: artifact_sha256,
        },
    }
}

fn results_reference_input(
    contract: &Contract,
    manifest: &OfficialCorpusManifest,
    path: String,
    artifact_sha256: String,
) -> ReferenceInput {
    ReferenceInput {
        id: "official-corpus-results".to_string(),
        cohort: SourceCohort::OfficialCorpus,
        repository: format!("generated-by:{VALIDATOR_ID}"),
        revision: contract.campaign_id.clone(),
        selection: "one retained result row for every immutable manifest file and query"
            .to_string(),
        item_count: manifest.query_count,
        digest_kind: "ay-official-smtlib-corpus-results/v1-json-sha256".to_string(),
        selection_sha256: artifact_sha256.clone(),
        snapshot: Artifact {
            path,
            sha256: artifact_sha256,
        },
    }
}

fn validate_manifest_reference(
    input: &ReferenceInput,
    manifest: &OfficialCorpusManifest,
    bytes: &[u8],
) -> Result<(), String> {
    let expected =
        manifest_reference_input(manifest, input.snapshot.path.clone(), sha256_bytes(bytes));
    if input != &expected {
        return Err("official corpus manifest ReferenceInput binding drift".to_string());
    }
    Ok(())
}

fn validate_results_reference(
    input: &ReferenceInput,
    contract: &Contract,
    manifest: &OfficialCorpusManifest,
    _results: &CorpusRunResults,
    bytes: &[u8],
) -> Result<(), String> {
    let expected = results_reference_input(
        contract,
        manifest,
        input.snapshot.path.clone(),
        sha256_bytes(bytes),
    );
    if input != &expected {
        return Err("official corpus results ReferenceInput binding drift".to_string());
    }
    Ok(())
}

fn current_validator(id: &str, kind: ValidatorKind) -> Result<ValidatorIdentity, String> {
    let path = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    Ok(ValidatorIdentity {
        id: id.to_string(),
        kind,
        path: path.to_string_lossy().into_owned(),
        sha256: sha256_file(&path, "parity validator")?,
    })
}

fn existing_relative_artifact(base: &Path, path: &Path) -> Result<String, String> {
    let relative = future_relative_output(base, path)?;
    let _ = resolve_relative_evidence_path(base, &relative)?;
    Ok(relative)
}

fn corpus_dimension(contract: &Contract) -> Result<&Dimension, String> {
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == DIMENSION_ID)
        .ok_or_else(|| format!("closed dimension {DIMENSION_ID:?} is missing"))
}

fn write_receipt_and_report(
    loaded: &LoadedContract,
    path: &Path,
    receipt: &ValidatorReceipt,
    label: &str,
    report: &AuditReport,
) -> Result<i32, String> {
    let bytes = pretty_json(receipt)?;
    atomic_write_new(path, &bytes)?;
    let relative = future_relative_output(&loaded.base, path)?;
    let receipt_sha256 = sha256_bytes(&bytes);
    println!(
        "{label}={} receipt={} sha256={}",
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        relative,
        receipt_sha256
    );
    println!(
        "attach to {REQUIREMENT_ID}: {{\"path\":\"{relative}\",\"sha256\":\"{receipt_sha256}\"}}"
    );
    if !report.complete {
        println!(
            "note: the rest of the contract remains incomplete ({} existing blockers)",
            report.blockers.len()
        );
    }
    Ok(i32::from(receipt.result != ValidatorResult::Pass))
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SemanticSignature {
    counts: CorpusRunCounts,
    files: Vec<(String, FileOutcome, Vec<QueryRun>)>,
}

fn semantic_signature(results: &CorpusRunResults) -> SemanticSignature {
    SemanticSignature {
        counts: results.counts.clone(),
        files: results
            .files
            .iter()
            .map(|file| (file.path.clone(), file.outcome, file.queries.clone()))
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn query_scanner_ignores_comments_strings_and_quoted_symbols() {
        let input = br#"
; (check-sat)
(set-info :source "(check-sat) and ""quoted""")
(declare-const |(check-sat)| Bool)
(check-sat)
(push 1)
(check-sat-assuming (|(check-sat)|))
"#;
        let rows = scan_queries(input).expect("scan");
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].command, "check-sat");
        assert_eq!(rows[1].command, "check-sat-assuming");
        assert_eq!(rows[0].ordinal, 1);
        assert_eq!(rows[1].ordinal, 2);
        assert!(rows[0].byte_end < rows[1].byte_end);
    }

    #[test]
    fn query_scanner_rejects_unbalanced_scripts() {
        assert!(scan_queries(b"(check-sat").is_err());
        assert!(scan_queries(b") (check-sat)").is_err());
        assert!(scan_queries(b"check-sat").is_err());
    }

    #[test]
    fn decided_excludes_unknown() {
        assert!(CorpusVerdict::Sat.decided());
        assert!(CorpusVerdict::Unsat.decided());
        assert!(!CorpusVerdict::Unknown.decided());
    }
}
