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
//! Each published UNSAT additionally needs a retained proof independently
//! accepted over the exact original query prefix. SAT models must independently
//! satisfy consistency and implication checks under the pinned reference.

use super::*;
use std::ffi::OsString;
use std::io::Read;

#[path = "official_corpus/checkpoint_gaps.rs"]
mod checkpoint_gaps;
pub(super) use checkpoint_gaps::gaps;

#[path = "official_corpus_records.rs"]
mod records;
#[path = "official_corpus/resume.rs"]
mod resume;
#[path = "sat_evidence.rs"]
mod sat_evidence;
#[path = "official_corpus_stream.rs"]
mod stream;

pub(super) const INVENTORY_VALIDATOR_ID: &str = "builtin.official-corpus-inventory.v1";
pub(super) const VALIDATOR_ID: &str = "builtin.official-corpus-z3-5.3.3.v1";

const DIMENSION_ID: &str = "coverage.corpus";
const REQUIREMENT_ID: &str = "coverage.corpus.closed-query-manifest";
const CORPUS_MANIFEST_SCHEMA: &str = "ay-official-smtlib-corpus-manifest/v1";
const CHECKPOINT_CORPUS_MANIFEST_SCHEMA: &str = "ay-official-smtlib-corpus-manifest/v2";
const LEGACY_RUN_RESULTS_SCHEMA: &str = "ay-official-smtlib-corpus-results/v3";
const RUN_RESULTS_SCHEMA: &str = "ay-official-smtlib-corpus-results/v4";
const MAX_QUERY_PROOF_BYTES: u64 = 64 * 1024 * 1024;
const RECORD_ID: &str = "11061097";
const RECORD_DOI: &str = "10.5281/zenodo.11061097";
const RECORD_API: &str = "https://zenodo.org/api/records/11061097";
const SOURCE_SELECTION: &str =
    "all 84 SMT-LIB 2024 non-incremental division archives; every extracted .smt2 file and every decision query; no divisions, files, or queries excluded";
const EXPECTED_ARCHIVE_COUNT: usize = 84;
const EXPECTED_ARCHIVE_MANIFEST_SHA256: &str =
    "337c6b0468e5f08175773c21864ed2712299678132f6204d8b5b08f8ad51a942";
const EXPECTED_FILE_COUNT: usize = 438_631;
const EXPECTED_QUERY_COUNT: usize = 438_631;
const EXPECTED_SOURCE_SELECTION_SHA256: &str =
    "109f19f3f835aea7f1272a73a7c78b306b53cb86abb5e5b6c16423d17b4116e7";
const SOURCE_SELECTION_DESCRIPTOR: &str = "record=11061097;metadata=ab864ac1985eea00a4866cb328dbcb839277bb58c206215fc176611941518027;archives=337c6b0468e5f08175773c21864ed2712299678132f6204d8b5b08f8ad51a942;files=438631;queries=438631;mapping=archive-path-slash-to-double-underscore;query-scanner=v1";
const MAX_CORPUS_MANIFEST_BYTES: u64 = 1024 * 1024 * 1024;
const MAX_CORPUS_RESULTS_BYTES: u64 = 16 * 1024 * 1024;
// Whole-prefix certificate transport is a separate bounded capability. The
// complete input population and decision scanner have no per-file 1 GiB cap.
const MAX_IN_MEMORY_QUERY_BYTES: u64 = 1024 * 1024 * 1024;

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

/// Require a real value when a v2-only field is present. On v1, the schema's
/// readers reject presence and continue to accept exactly the legacy fields.
fn deserialize_checkpoint_field<'de, D, T>(input: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    T::deserialize(input).map(Some)
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct CorpusFile {
    path: String,
    size: u64,
    sha256: String,
    queries: Vec<CorpusQuery>,
    #[serde(
        default,
        deserialize_with = "deserialize_checkpoint_field",
        skip_serializing_if = "Option::is_none"
    )]
    echoes: Option<Vec<CorpusEcho>>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct CorpusEcho {
    byte_start: u64,
    byte_end: u64,
    command_sha256: String,
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
    evidence: QueryEvidence,
    outcome: QueryOutcome,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum EvidenceStatus {
    NotDecided,
    UncertifiedSat,
    UnsupportedQuery,
    Unavailable,
    Rejected,
    AcceptedUnsat,
    AcceptedSat,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct EvidenceTranscript {
    process: ProcessRun,
    stdout: String,
    stderr: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum CheckerProblemKind {
    CanonicalFp32RneV1,
    Z3RemainderV1,
    ScopedPlainV1,
    ScopedSignedV1,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct QueryEvidence {
    status: EvidenceStatus,
    reason: String,
    problem: Option<Artifact>,
    #[serde(
        default,
        deserialize_with = "deserialize_checkpoint_field",
        skip_serializing_if = "Option::is_none"
    )]
    checker_problem: Option<Artifact>,
    #[serde(
        default,
        deserialize_with = "deserialize_checkpoint_field",
        skip_serializing_if = "Option::is_none"
    )]
    checker_problem_kind: Option<CheckerProblemKind>,
    proof: Option<Artifact>,
    producer: Option<EvidenceTranscript>,
    checker: Option<EvidenceTranscript>,
    sat: Option<sat_evidence::Evidence>,
}

impl QueryEvidence {
    fn absent(verdict: Option<CorpusVerdict>) -> Self {
        Self {
            status: match verdict {
                Some(CorpusVerdict::Sat) => EvidenceStatus::UncertifiedSat,
                Some(CorpusVerdict::Unsat) => EvidenceStatus::Unavailable,
                _ => EvidenceStatus::NotDecided,
            },
            reason: match verdict {
                Some(CorpusVerdict::Sat) => "no independent per-query SAT model evidence available",
                Some(CorpusVerdict::Unsat) => "no independent per-query UNSAT evidence available",
                _ => "no decided AY verdict",
            }
            .to_string(),
            problem: None,
            checker_problem: None,
            checker_problem_kind: None,
            proof: None,
            producer: None,
            checker: None,
            sat: None,
        }
    }

    fn has_proof_evidence(&self) -> bool {
        self.problem.is_some() || self.has_certificate_artifacts()
    }

    fn has_certificate_artifacts(&self) -> bool {
        self.checker_problem.is_some()
            || self.checker_problem_kind.is_some()
            || self.proof.is_some()
            || self.producer.is_some()
            || self.checker.is_some()
    }

    fn satisfies(&self, verdict: Option<CorpusVerdict>) -> bool {
        match verdict {
            Some(CorpusVerdict::Unsat) => self.status == EvidenceStatus::AcceptedUnsat,
            Some(CorpusVerdict::Sat) => {
                self.status == EvidenceStatus::AcceptedSat
                    && self
                        .sat
                        .as_ref()
                        .is_some_and(sat_evidence::Evidence::accepted)
            }
            Some(CorpusVerdict::Unknown) | None => self.status == EvidenceStatus::NotDecided,
        }
    }
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
    #[serde(
        default,
        deserialize_with = "deserialize_checkpoint_field",
        skip_serializing_if = "Option::is_none"
    )]
    input_size: Option<u64>,
    query_count: usize,
    ay: ProcessRun,
    z3: ProcessRun,
    #[serde(
        default,
        deserialize_with = "deserialize_checkpoint_field",
        skip_serializing_if = "Option::is_none"
    )]
    echo_streams: Option<RecordedEchoStreams>,
    queries: Vec<QueryRun>,
    outcome: FileOutcome,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct RecordedEchoStreams {
    ay: Option<EvidenceTranscript>,
    z3: Option<EvidenceTranscript>,
}

impl FileRun {
    fn has_extended_observation_fields(&self) -> bool {
        self.echo_streams.is_some()
            || self.queries.iter().any(|query| {
                let evidence = &query.evidence;
                evidence.checker_problem.is_some()
                    || evidence.checker_problem_kind.is_some()
                    || evidence
                        .sat
                        .as_ref()
                        .is_some_and(sat_evidence::Evidence::has_checkpoint_fields)
            })
    }
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
    independently_checked_unsat: usize,
    independently_checked_sat: usize,
    uncertified_decisions: usize,
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
            && self.uncertified_decisions == 0
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
    #[serde(default, skip_serializing_if = "Option::is_none")]
    evaluator_sha256: Option<String>,
    resource_envelope: String,
    ay_mode: String,
    z3_mode: String,
    query_proof_mode: String,
    query_checker_mode: String,
    query_model_mode: String,
    query_proof_file_limit_bytes: u64,
    artifact_root: String,
    checker: Option<Artifact>,
    checker_identity: Option<EvidenceTranscript>,
    checker_error: Option<String>,
    counts: CorpusRunCounts,
    records: records::Manifest,
}

#[derive(Debug)]
struct SemanticExecution {
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
    run_results: CorpusRunResults,
}

enum SemanticAccess<'a> {
    Replay,
    Fresh(&'a resume::Campaign),
    Resume(&'a resume::Campaign),
    Published(&'a resume::Campaign, &'a CorpusRunResults),
}

impl SemanticAccess<'_> {
    fn custody(&self) -> Option<&resume::Campaign> {
        match self {
            Self::Replay => None,
            Self::Fresh(campaign) | Self::Resume(campaign) | Self::Published(campaign, _) => {
                Some(campaign)
            }
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct CorpusCreateInputs {
    pub(super) root: PathBuf,
    pub(super) archive_root: PathBuf,
    pub(super) metadata: PathBuf,
    pub(super) output: PathBuf,
}

pub(super) fn create_manifest(args: &[String]) -> Result<i32, String> {
    let inputs = parse_create_inputs(args)?;
    provision::create_corpus_manifest(&inputs)?;
    Ok(0)
}

fn parse_create_inputs(args: &[String]) -> Result<CorpusCreateInputs, String> {
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
    Ok(CorpusCreateInputs {
        root: root.ok_or("official-corpus-manifest needs a corpus root")?,
        archive_root: archive_root.ok_or("official-corpus-manifest requires --archive-root")?,
        metadata: metadata.ok_or("official-corpus-manifest requires --record-metadata")?,
        output: output.ok_or("official-corpus-manifest requires --out")?,
    })
}

/// Only the bounded corpus worker calls this raw creation operation.
pub(super) fn create_manifest_child(inputs: &CorpusCreateInputs) -> Result<(), String> {
    let metadata_bytes = read_bounded_bytes(
        &inputs.metadata,
        64 * 1024 * 1024,
        "Zenodo record metadata",
        true,
    )?;
    let source = source_from_metadata(&metadata_bytes)?;
    let corpus_root = canonical_corpus_root(&inputs.root)?;
    let archive_root = canonical_archive_root(&inputs.archive_root)?;
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
    atomic_write_new(&inputs.output, &bytes)?;
    println!(
        "wrote {} (record={}, archives={}, files={}, queries={}, selection-sha256={})",
        inputs.output.display(),
        manifest.source.record_id,
        manifest.source.archive_count,
        manifest.file_count,
        manifest.query_count,
        manifest.selection_sha256
    );
    Ok(())
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
    provision::authenticate_corpus_manifest(
        &common.corpus_manifest,
        &sha256_bytes(&corpus_bytes),
        None,
    )?;
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
        .clone()
        .unwrap_or_else(|| artifact_path(&loaded.base, &subject.path));
    let z3 = match options.z3.clone() {
        Some(path) => path,
        None => {
            reference_artifact_path(&loaded.contract.profile.z3_overlay.reference_executable.path)?
        }
    };
    let (corpus_manifest, corpus_bytes) = load_corpus_manifest(&options.corpus_manifest)?;
    let corpus_manifest_sha256 = sha256_bytes(&corpus_bytes);
    let manifest_relative = existing_relative_artifact(&loaded.base, &options.corpus_manifest)?;
    let validator = current_validator(VALIDATOR_ID, ValidatorKind::OfficialCorpus)?;
    let custody = resume::Campaign::open(
        &options,
        &loaded.base,
        &loaded.sha256,
        &validator.sha256,
        &corpus_manifest_sha256,
    )?;
    let published = if options.resume && resume::publication_exists(&custody.results)? {
        let bytes = resume::read_publication(&custody.results, MAX_CORPUS_RESULTS_BYTES)?;
        let results: CorpusRunResults = serde_json::from_slice(&bytes)
            .map_err(|error| format!("invalid published official corpus results: {error}"))?;
        Some((results, bytes))
    } else {
        None
    };
    let access = match (&published, options.resume) {
        (Some((results, _)), _) => SemanticAccess::Published(&custody, results),
        (None, true) => SemanticAccess::Resume(&custody),
        (None, false) => SemanticAccess::Fresh(&custody),
    };
    let checker_source = options
        .carcara
        .or_else(|| std::env::var_os("CARCARA_PATH").map(PathBuf::from))
        .or_else(|| {
            std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".cargo/bin/carcara"))
        });
    let execution = execute_semantic(
        &loaded.contract,
        &dimension.inventory.sha256,
        &corpus_manifest,
        &options.corpus_manifest,
        &corpus_manifest_sha256,
        &ay,
        &z3,
        parsed.timeout,
        Some(envelope),
        &loaded.base,
        &custody.evidence,
        checker_source.as_deref(),
        access,
    )?;
    if execution.run_results.evaluator_sha256.as_deref() != Some(validator.sha256.as_str())
        || sha256_file(
            Path::new(&validator.path),
            "official corpus evaluator at publication",
        )? != validator.sha256
    {
        return Err("official corpus evaluator changed before receipt publication".into());
    }
    custody.check()?;
    let results_bytes = if let Some((_, bytes)) = published {
        bytes
    } else {
        let bytes = serde_json::to_vec(&execution.run_results)
            .map_err(|error| format!("serializing official corpus results: {error}"))?;
        atomic_write_new(&custody.results, &bytes)?;
        bytes
    };

    let results_relative = existing_relative_artifact(&loaded.base, &custody.results)?;
    let results_sha256 = sha256_bytes(&results_bytes);
    if sha256_bytes(&resume::read_publication(
        &custody.results,
        MAX_CORPUS_RESULTS_BYTES,
    )?) != results_sha256
    {
        return Err("official corpus results changed before receipt publication".into());
    }
    let reference_inputs = vec![
        manifest_reference_input(
            &corpus_manifest,
            manifest_relative,
            corpus_manifest_sha256.clone(),
        ),
        results_reference_input(
            &loaded.contract,
            &corpus_manifest,
            &execution.run_results,
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
        validator,
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
        auxiliary_tools: corpus_auxiliary_tools(&execution.run_results)?,
        source_provenance: None,
        resource_envelope: Some(execution.run_results.resource_envelope.clone()),
        exhaustive: true,
        result: execution.result,
        cases: execution.cases,
        case_results: execution.case_results,
    };
    custody.check()?;
    if options.resume && resume::publication_exists(&custody.receipt)? {
        let bytes = resume::read_publication(&custody.receipt, MAX_VALIDATOR_RECEIPT_BYTES)?;
        let observed: ValidatorReceipt = serde_json::from_slice(&bytes)
            .map_err(|error| format!("invalid existing official corpus receipt: {error}"))?;
        if observed != receipt {
            return Err("existing official corpus receipt differs from validated results".into());
        }
        return report_written_receipt(
            &loaded,
            &custody.receipt,
            &receipt,
            "official-corpus",
            &report,
            &bytes,
        );
    }
    write_receipt_and_report(
        &loaded,
        &custody.receipt,
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
        provision::authenticate_corpus_manifest(
            &resolve_relative_evidence_path(
                context.manifest_dir,
                &receipt.reference_inputs[0].snapshot.path,
            )?,
            &sha256_bytes(&bytes),
            None,
        )?;
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
        || receipt.source_provenance.is_some()
        || receipt.reference_inputs.len() != 2
    {
        return Err(format!("{VALIDATOR_ID} has invalid bindings"));
    }
    let (manifest, manifest_bytes) = manifest_from_reference(receipt, context.manifest_dir, 0)?;
    validate_manifest_reference(&receipt.reference_inputs[0], &manifest, &manifest_bytes)?;
    let (results, result_bytes) = results_from_reference(receipt, context.manifest_dir, 1)?;
    if results
        .evaluator_sha256
        .as_ref()
        .is_some_and(|evaluator| evaluator != &receipt.validator.sha256)
    {
        return Err("official corpus results and validator evaluator differ".into());
    }
    if receipt.auxiliary_tools != corpus_auxiliary_tools(&results)? {
        return Err("official corpus independent checker authority drift".to_string());
    }
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
        context.manifest_dir,
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
        let replay_directory = tempfile::tempdir_in(context.manifest_dir)
            .map_err(|error| format!("create query evidence replay directory: {error}"))?;
        let retained_checker = results
            .checker
            .as_ref()
            .map(|artifact| artifact_path(context.manifest_dir, &artifact.path));
        replay_retained_proofs(&results, context.manifest_dir, parsed.timeout)?;
        let live = execute_semantic(
            context.contract,
            &context.dimension.inventory.sha256,
            &manifest,
            &resolve_relative_evidence_path(
                context.manifest_dir,
                &receipt.reference_inputs[0].snapshot.path,
            )?,
            &sha256_bytes(&manifest_bytes),
            &artifact_path(context.manifest_dir, &subject.path),
            &reference_artifact_path(
                &context
                    .contract
                    .profile
                    .z3_overlay
                    .reference_executable
                    .path,
            )?,
            parsed.timeout,
            Some(envelope),
            context.manifest_dir,
            replay_directory.path(),
            retained_checker.as_deref(),
            SemanticAccess::Replay,
        )?;
        if semantic_signature(&live.run_results) != semantic_signature(&results) {
            return Err(format!(
                "{VALIDATOR_ID} retained results do not match a fresh complete replay"
            ));
        }
    }
    Ok(())
}

/// Coverage is derived from authenticated per-query artifacts, never from a
/// canary receipt or a caller-supplied aggregate. The overall corpus receipt
/// may fail for unrelated capability/parity reasons while one evidence kind
/// is fully covered; callers must retain those other completion blockers.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub(super) struct QueryEvidenceCoverage {
    pub(super) receipt_sha256: String,
    pub(super) queries: usize,
    pub(super) sat: usize,
    pub(super) sat_checked: usize,
    pub(super) unsat: usize,
    pub(super) unsat_checked: usize,
    pub(super) unknown_or_missing: usize,
    pub(super) shared_unknown: usize,
    pub(super) invalid_or_regressed: usize,
}

impl QueryEvidenceCoverage {
    pub(super) fn sat_complete(&self) -> bool {
        self.queries > 0
            && self.sat > 0
            && self.invalid_or_regressed == 0
            && self.sat == self.sat_checked
    }

    pub(super) fn unsat_complete(&self) -> bool {
        self.queries > 0
            && self.unsat > 0
            && self.invalid_or_regressed == 0
            && self.unsat == self.unsat_checked
    }
}

/// Passing Completion here performs the normal fresh corpus/model/proof replay.
/// A caller that has just validated every contract receipt in Completion mode
/// may use Structural to derive counters without repeating that same campaign.
pub(super) fn query_evidence_coverage(
    contract: &Contract,
    base: &Path,
    mode: ValidationMode,
) -> Result<QueryEvidenceCoverage, String> {
    let dimension = corpus_dimension(contract)?;
    let requirement = dimension
        .requirements
        .iter()
        .find(|row| row.id == REQUIREMENT_ID)
        .ok_or("official corpus evidence requirement missing")?;
    if requirement.evidence.len() != 1 {
        return Err("per-query coverage requires exactly one authenticated corpus receipt; missing or ambiguous campaigns do not qualify".to_string());
    }
    let reference = &requirement.evidence[0];
    let mut cache = ReceiptCache::default();
    let receipt = load_validator_receipt(reference, base, &mut cache)?.clone();
    if receipt.validator.id != VALIDATOR_ID {
        return Err(
            "per-query coverage requires the registered official corpus validator".to_string(),
        );
    }
    // A valid failing receipt is still useful evidence of the actual gap.
    validate_validator_receipt(
        &receipt,
        EvidenceContext {
            contract,
            manifest_dir: base,
            dimension,
            expected_kind: ValidatorKind::OfficialCorpus,
            required_requirement_id: Some(REQUIREMENT_ID),
            exact_requirement_ids: None,
            mode,
        },
    )?;
    let (manifest, _) = manifest_from_reference(&receipt, base, 0)?;
    let (results, _) = results_from_reference(&receipt, base, 1)?;
    let mut coverage = QueryEvidenceCoverage {
        receipt_sha256: reference.sha256.clone(),
        queries: manifest.query_count,
        sat: 0,
        sat_checked: 0,
        unsat: 0,
        unsat_checked: 0,
        unknown_or_missing: 0,
        shared_unknown: 0,
        invalid_or_regressed: 0,
    };
    records::visit(
        &results.records,
        base,
        &records::Header::new(&results, manifest.files.len()),
        |_, file| {
            for query in &file.queries {
                coverage.invalid_or_regressed += usize::from(query.outcome != QueryOutcome::Pass);
                coverage.shared_unknown += usize::from(
                    query.ay == Some(CorpusVerdict::Unknown)
                        && query.z3 == Some(CorpusVerdict::Unknown),
                );
                match query.ay {
                    Some(CorpusVerdict::Sat) => {
                        coverage.sat += 1;
                        coverage.sat_checked += usize::from(query.evidence.satisfies(query.ay));
                    }
                    Some(CorpusVerdict::Unsat) => {
                        coverage.unsat += 1;
                        coverage.unsat_checked += usize::from(query.evidence.satisfies(query.ay));
                    }
                    Some(CorpusVerdict::Unknown) | None => coverage.unknown_or_missing += 1,
                }
            }
            Ok(())
        },
    )?;
    if coverage.sat + coverage.unsat + coverage.unknown_or_missing != coverage.queries {
        return Err("per-query coverage does not match the closed corpus population".to_string());
    }
    Ok(coverage)
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
    carcara: Option<PathBuf>,
    timeout_secs: u64,
    resume: bool,
}

fn parse_run_args(args: &[String]) -> Result<RunArgs, String> {
    let mut manifest = None;
    let mut corpus_manifest = None;
    let mut receipt = None;
    let mut results = None;
    let mut ay = None;
    let mut z3 = None;
    let mut carcara = None;
    let mut timeout_secs = 10u64;
    let mut resume = false;
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
            "--carcara" => {
                index += 1;
                carcara = Some(PathBuf::from(
                    args.get(index).ok_or("--carcara needs a path")?,
                ));
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
            "--resume" => {
                if resume {
                    return Err("official-corpus takes at most one --resume".into());
                }
                resume = true;
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
        carcara,
        timeout_secs,
        resume,
    })
}

fn source_from_metadata(bytes: &[u8]) -> Result<CorpusSource, String> {
    // View/download statistics change in the API response. Authenticate the
    // record, DOI and exact immutable archive rows below, and retain the raw
    // response's observed hash as provenance, not as a mutable-content pin.
    let value: Value = serde_json::from_slice(bytes)
        .map_err(|error| format!("invalid Zenodo record metadata JSON: {error}"))?;
    let id_matches = value
        .get("id")
        .and_then(Value::as_u64)
        .is_some_and(|id| id.to_string() == RECORD_ID);
    if !id_matches {
        return Err(format!(
            "Zenodo metadata is not immutable record {RECORD_ID}"
        ));
    }
    if value.get("doi").and_then(Value::as_str) != Some(RECORD_DOI) {
        return Err(format!("Zenodo metadata DOI is not {RECORD_DOI}"));
    }
    let files = value
        .get("files")
        .and_then(Value::as_array)
        .ok_or("Zenodo metadata has no files array")?;
    let mut archives = Vec::new();
    for file in files {
        let key = file
            .get("key")
            .and_then(Value::as_str)
            .ok_or("Zenodo file has no key")?;
        let Some(division) = key.strip_suffix(".tar.zst") else {
            continue;
        };
        validate_division(division)?;
        let size = file
            .get("size")
            .and_then(Value::as_u64)
            .ok_or_else(|| format!("Zenodo archive {key:?} has no byte size"))?;
        if size == 0 {
            return Err(format!("Zenodo archive {key:?} is empty"));
        }
        let checksum = file
            .get("checksum")
            .and_then(Value::as_str)
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
        record_metadata_sha256: sha256_bytes(bytes),
        selection: SOURCE_SELECTION.to_string(),
        source_selection_sha256: EXPECTED_SOURCE_SELECTION_SHA256.to_string(),
        archive_count: archives.len(),
        archive_manifest_sha256,
        archives,
    })
}

fn validate_manifest(manifest: &OfficialCorpusManifest) -> Result<(), String> {
    validate_manifest_for_use(manifest, ManifestUse::LegacyReceipt)
}

#[derive(Clone, Copy)]
enum ManifestUse {
    LegacyReceipt,
    Checkpoint,
}

fn validate_manifest_for_use(
    manifest: &OfficialCorpusManifest,
    usage: ManifestUse,
) -> Result<(), String> {
    if sha256_bytes(SOURCE_SELECTION_DESCRIPTOR.as_bytes()) != EXPECTED_SOURCE_SELECTION_SHA256 {
        return Err("compiled official corpus source-selection identity drift".to_string());
    }
    let indexed_echoes = matches!(usage, ManifestUse::Checkpoint)
        && manifest.schema == CHECKPOINT_CORPUS_MANIFEST_SCHEMA;
    if (!indexed_echoes && manifest.schema != CORPUS_MANIFEST_SCHEMA)
        || manifest.profile_id != PROFILE_ID
    {
        return Err("official corpus manifest schema or profile drift".to_string());
    }
    let source = &manifest.source;
    if source.name != "SMT-LIB 2024 non-incremental benchmark release"
        || source.record_id != RECORD_ID
        || source.doi != RECORD_DOI
        || source.api_url != RECORD_API
        || source.selection != SOURCE_SELECTION
        || source.source_selection_sha256 != EXPECTED_SOURCE_SELECTION_SHA256
        || source.archive_count != EXPECTED_ARCHIVE_COUNT
        || source.archives.len() != EXPECTED_ARCHIVE_COUNT
    {
        return Err("official corpus source identity or all-archive selection drift".to_string());
    }
    validate_sha256(&source.record_metadata_sha256, "observed Zenodo metadata")?;
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
        let mut previous_query_end = 0;
        for (index, query) in file.queries.iter().enumerate() {
            if query.ordinal != index + 1
                || !matches!(
                    query.command.as_str(),
                    "check-sat" | "check-sat-assuming" | "check-sat-using"
                )
                || (indexed_echoes && query.byte_start < previous_query_end)
                || query.byte_start >= query.byte_end
                || query.byte_end > file.size
            {
                return Err(format!("malformed query row in {:?}", file.path));
            }
            validate_sha256(&query.command_sha256, "query command sha256")?;
            validate_sha256(&query.prefix_sha256, "query prefix sha256")?;
            previous_query_end = query.byte_end;
        }
        let echoes = file.echoes.as_deref().unwrap_or_default();
        if file.echoes.is_some() && (!indexed_echoes || echoes.is_empty()) {
            return Err("invalid echo spans for the official corpus manifest schema".into());
        }
        let mut previous_echo_end = 0;
        for echo in echoes {
            let following = file
                .queries
                .partition_point(|query| query.byte_end <= echo.byte_start);
            if echo.byte_start < previous_echo_end
                || echo.byte_start >= echo.byte_end
                || echo.byte_end > file.size
                || file
                    .queries
                    .get(following)
                    .is_some_and(|query| query.byte_start < echo.byte_end)
            {
                return Err(format!("malformed echo command span in {:?}", file.path));
            }
            validate_sha256(&echo.command_sha256, "echo command sha256")?;
            previous_echo_end = echo.byte_end;
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

/// One fully authenticated corpus file with its exact decision-query count.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PerformanceFile {
    pub(super) path: String,
    pub(super) query_count: usize,
}

/// Authenticate the complete population for the separate performance lane.
/// Counts alone never establish a complete corpus.
pub(super) fn performance_population(
    path: &Path,
) -> Result<(PathBuf, Vec<PerformanceFile>, String), String> {
    let (manifest, bytes) = load_corpus_manifest(path)?;
    provision::authenticate_corpus_manifest(path, &sha256_bytes(&bytes), None)?;
    let root = PathBuf::from(&manifest.corpus_root);
    let paths = manifest
        .files
        .iter()
        .map(|file| PerformanceFile {
            path: root.join(&file.path).to_string_lossy().into_owned(),
            query_count: file.queries.len(),
        })
        .collect();
    Ok((root, paths, sha256_bytes(&bytes)))
}

/// Internal worker entry. The caller must already be supervised by the
/// provision owner; public consuming paths call its guarded entry instead.
pub(super) fn authenticate_materialization_child(path: &Path) -> Result<String, String> {
    let (manifest, bytes) = load_corpus_manifest(path)?;
    verify_materialization(&manifest)?;
    Ok(sha256_bytes(&bytes))
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
    let mut reader = crate::fetch::open_official_archive(path)?;
    let budget = reader.byte_limit();
    let files = parse_tar_stream(&mut reader, division, budget)?;
    crate::fetch::finish_official_archive(&mut reader)?;
    if files.is_empty() {
        return Err(format!(
            "authenticated archive {} contains no .smt2 members",
            path.display()
        ));
    }
    Ok(files)
}

fn parse_tar_stream(
    reader: &mut impl Read,
    division: &str,
    budget: u64,
) -> Result<Vec<CorpusFile>, String> {
    let mut files = Vec::new();
    let mut declared_bytes = 0u64;
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
        let padding = (512 - (size % 512)) % 512;
        declared_bytes = declared_bytes
            .checked_add(512)
            .and_then(|count| count.checked_add(size))
            .and_then(|count| count.checked_add(padding))
            .ok_or("archive member byte count overflow")?;
        if declared_bytes > budget {
            return Err("archive members exceed authenticated expansion budget".to_string());
        }
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
        if is_smt2 {
            let scanned = stream::scan(&mut reader.by_ref().take(size), size)
                .map_err(|error| format!("scanning archive member {name:?}: {error}"))?;
            if scanned.size != size {
                return Err(format!("archive member {name:?} is truncated"));
            }
            if scanned.size == 0 {
                return Err(format!("official archive member {name:?} is empty"));
            }
            let normalized = normalized_tar_member(&name)?;
            let flat = normalized.replace('/', "__");
            if scanned.queries.is_empty() {
                return Err(format!("official archive member {name:?} has no query"));
            }
            files.push(CorpusFile {
                path: format!("{division}/{flat}"),
                size,
                sha256: scanned.sha256,
                queries: scanned.queries,
                echoes: None,
            });
        } else {
            let mut limited = reader.by_ref().take(size);
            let copied = std::io::copy(&mut limited, &mut std::io::sink())
                .map_err(|error| format!("discarding archive member {name:?}: {error}"))?;
            if copied != size {
                return Err(format!("archive member {name:?} is truncated"));
            }
        }
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
    // All raw archive operations run inside the admitted corpus worker. This
    // known leaf inherits its group and aggregate RSS limit; local capture adds
    // a ten-minute wall deadline and 4096-byte stream bounds without escaping
    // the outer supervisor's cancellation custody.
    let output =
        ay_sys::metadata_capture::inherited_leaf::capture_md5(path, Duration::from_secs(600))
            .map_err(|error| format!("bounded MD5 of {}: {error}", path.display()))?;
    if !output.status.success()
        || output.timed_out
        || output.output_limit_reached
        || output.stdout.incomplete
        || output.stderr.incomplete
        || !output.stderr.text.is_empty()
    {
        return Err(format!(
            "bounded MD5 failed for {}: status={}, timeout={}, output_limit={}, stdout_incomplete={}, stderr_incomplete={}; stdout={:?}; stderr={:?}",
            path.display(), output.status, output.timed_out, output.output_limit_reached,
            output.stdout.incomplete, output.stderr.incomplete, output.stdout.text, output.stderr.text
        ));
    }
    parse_md5_digest(&output.stdout.text)
        .map_err(|error| format!("MD5 output for {}: {error}", path.display()))
}

fn parse_md5_digest(output: &str) -> Result<String, String> {
    let digest = output.get(..32).ok_or("digest is shorter than 32 bytes")?;
    if !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("digest is not 32 hexadecimal digits".to_string());
    }
    let remainder = &output[32..];
    // macOS emits just a line; GNU --zero emits one unescaped filename record.
    // A diagnostic or an additional record never qualifies as a digest.
    if remainder != "\n"
        && !(remainder.starts_with("  ")
            && remainder.ends_with('\0')
            && remainder.bytes().filter(|byte| *byte == 0).count() == 1)
    {
        return Err("expected exactly one native MD5 output record".to_string());
    }
    Ok(digest.to_ascii_lowercase())
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
        let metadata = fs::symlink_metadata(&full)
            .map_err(|error| format!("inspecting corpus file {}: {error}", full.display()))?;
        if metadata.file_type().is_symlink() || !metadata.is_file() {
            return Err(format!(
                "corpus file is not a regular non-symlink: {}",
                full.display()
            ));
        }
        if metadata.len() > crate::fetch::official_archive_expansion_budget(u64::MAX) {
            return Err(format!(
                "corpus file exceeds the authenticated archive expansion ceiling: {}",
                full.display()
            ));
        }
        let mut input = fs::File::open(&full)
            .map_err(|error| format!("opening corpus file {}: {error}", full.display()))?;
        let scanned = stream::scan(&mut input, metadata.len()).map_err(|error| {
            format!(
                "enumerating decision queries in {}: {error}",
                full.display()
            )
        })?;
        let after = fs::symlink_metadata(&full)
            .map_err(|error| format!("re-inspecting corpus file {}: {error}", full.display()))?;
        if after.file_type().is_symlink()
            || !after.is_file()
            || after.len() != metadata.len()
            || scanned.size != metadata.len()
        {
            return Err(format!(
                "corpus file changed while scanning: {}",
                full.display()
            ));
        }
        if scanned.size == 0 {
            return Err(format!("official corpus file is empty: {}", full.display()));
        }
        if scanned.queries.is_empty() {
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
            size: scanned.size,
            sha256: scanned.sha256,
            queries: scanned.queries,
            echoes: None,
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
    Ok(stream::scan(&mut std::io::Cursor::new(bytes), bytes.len() as u64)?.queries)
}

#[cfg(test)]
fn scan_queries_legacy(bytes: &[u8]) -> Result<Vec<CorpusQuery>, String> {
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
    manifest_path: &Path,
    manifest_sha256: &str,
    ay_source: &Path,
    z3_source: &Path,
    timeout: Duration,
    required_envelope: Option<&str>,
    artifact_base: &Path,
    evidence_directory: &Path,
    checker_source: Option<&Path>,
    access: SemanticAccess<'_>,
) -> Result<SemanticExecution, String> {
    let subject = contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("official corpus requires subject.ay_executable")?;
    let z3_sha256 = &contract.profile.z3_overlay.reference_executable.sha256;
    let staged_ay = stage_authenticated_executable(ay_source, &subject.sha256, "AY executable")?;
    let staged_z3 = stage_authenticated_executable(z3_source, z3_sha256, "Z3 5.3.3 executable")?;
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

    provision::authenticate_corpus_manifest(manifest_path, manifest_sha256, Some(&resources))?;

    if let Some(custody) = access.custody() {
        custody.check()?;
    }
    let attempt = tempfile::Builder::new()
        .prefix("attempt-")
        .tempdir_in(evidence_directory)
        .map_err(|error| format!("create fresh official corpus attempt: {error}"))?;
    let (checker, checker_identity, checker_error) = prepare_corpus_checker(
        checker_source,
        attempt.path(),
        artifact_base,
        &resources,
        timeout,
    );
    let checker_path = checker
        .as_ref()
        .map(|artifact| artifact_path(artifact_base, &artifact.path));

    let mut run_results = CorpusRunResults {
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
        evaluator_sha256: Some(sha256_file(
            &std::env::current_exe().map_err(|error| error.to_string())?,
            "official corpus evaluator",
        )?),
        resource_envelope,
        ay_mode: "solve --quiet --competition --strict-proofs --self-check --memory <planned-MiB> <file>; rss-watchdog".to_string(),
        z3_mode: "z3-5.3.3 -smt2 <file>; rss-watchdog".to_string(),
        query_proof_mode: "solve --quiet --strict-proofs --self-check --alethe-dialect pinned-carcara --proof <query-proof> --memory <planned-MiB> <exact-query-prefix>; rss-watchdog; rlimit-fsize".to_string(),
        query_checker_mode: "carcara check --strict-parsing -- <query-proof> <exact-query-prefix>; rss-watchdog".to_string(),
        query_model_mode: "AY get-model over exact query; Z3 model-constraint consistency SAT then original-assertion counterexample UNSAT; rss-watchdog".to_string(),
        query_proof_file_limit_bytes: MAX_QUERY_PROOF_BYTES,
        artifact_root: existing_relative_artifact_directory(artifact_base, evidence_directory)?,
        checker,
        checker_identity,
        checker_error,
        counts: CorpusRunCounts::default(),
        records: records::Manifest {
            artifact: Artifact { path: String::new(), sha256: String::new() },
            bytes: 0, rows: 0, semantic_sha256: String::new(),
        },
    };
    let root = PathBuf::from(&manifest.corpus_root);
    let record_path = evidence_directory.join("records.jsonl");
    let relative = future_relative_output(artifact_base, &record_path)?;
    let authority = RetainedReplay {
        base: artifact_base,
        ay: &staged_ay.path,
        z3: &staged_z3.path,
        checker: checker_path.as_deref(),
        checker_sha256: run_results
            .checker
            .as_ref()
            .map(|tool| tool.sha256.as_str()),
        resources: &resources,
        timeout,
    };
    let header = records::Header::new(&run_results, manifest.files.len());
    if let SemanticAccess::Published(custody, published) = &access {
        if published.schema != RUN_RESULTS_SCHEMA
            || published.evaluator_sha256 != run_results.evaluator_sha256
            || published.artifact_root != run_results.artifact_root
            || published.records.artifact.path != relative
            || published.checker.as_ref().map(|checker| &checker.sha256)
                != run_results.checker.as_ref().map(|checker| &checker.sha256)
        {
            return Err("published results differ from the exact official corpus producer".into());
        }
        if !resume::publication_exists(&record_path)? {
            return Err("published results are missing their official corpus record stream".into());
        }
        validate_run_results(
            published,
            contract,
            inventory_sha256,
            manifest,
            manifest_sha256,
            artifact_base,
        )?;
        records::visit(
            &published.records,
            artifact_base,
            &header,
            |index, result| authority.replay(&result, &manifest.files[index], &root),
        )?;
        custody.check()?;
        provision::authenticate_corpus_manifest(manifest_path, manifest_sha256, Some(&resources))?;
        authority.check_tools(&subject.sha256, z3_sha256)?;
        return semantic_execution((**published).clone(), &manifest.selection_sha256);
    }
    let mut counts = CorpusRunCounts::default();
    let mut writer = match &access {
        SemanticAccess::Resume(custody) if resume::publication_exists(&record_path)? => {
            let writer = records::Writer::resume(
                &record_path,
                relative,
                &header,
                |index, result| {
                    let file = &manifest.files[index];
                    validate_file_result(
                        result,
                        file,
                        &manifest.corpus_root,
                        artifact_base,
                        &run_results.artifact_root,
                        run_results.checker.as_ref(),
                    )?;
                    authority.replay(result, file, &root)?;
                    accumulate_run_counts(&mut counts, result)
                },
                || {
                    custody.check()?;
                    authority.check_tools(&subject.sha256, z3_sha256)
                },
            )?;
            eprintln!(
                "official corpus verified {} retained rows",
                counts.files_total
            );
            writer
        }
        _ => records::Writer::create(&record_path, relative, &header)?,
    };
    let attempt = attempt.keep();
    sync_corpus_directory(evidence_directory)?;
    for file in &manifest.files[counts.files_total..] {
        let mut result = run_file(
            &resources,
            &staged_ay.path,
            &staged_z3.path,
            &root.join(&file.path),
            file,
            timeout,
        );
        certify_file_queries(
            &mut result,
            file,
            &root.join(&file.path),
            &resources,
            &staged_ay.path,
            &staged_z3.path,
            checker_path.as_deref(),
            &attempt,
            artifact_base,
            timeout,
        );
        result.input_size = Some(file.size);
        validate_file_result(
            &result,
            file,
            &manifest.corpus_root,
            artifact_base,
            &run_results.artifact_root,
            run_results.checker.as_ref(),
        )?;
        if let Some(custody) = access.custody() {
            custody.check()?;
        }
        // Sync the attempt's new query directory entries before its row
        // becomes durable in the checkpoint.
        sync_corpus_directory(&attempt)?;
        writer.append(&result)?;
        accumulate_run_counts(&mut counts, &result)?;
        if counts.files_total == 1
            || counts.files_total % 1_000 == 0
            || counts.files_total == manifest.files.len()
        {
            eprintln!(
                "official corpus {}/{} files: {} passed, {} wrong answers, {} missing answers, {} uncertified decisions",
                counts.files_total,
                manifest.files.len(),
                counts.files_passed,
                counts.wrong,
                counts.missing,
                counts.uncertified_decisions,
            );
        }
    }
    authority.check_tools(&subject.sha256, z3_sha256)?;
    // A second full closure scan detects mutation, deletion, replacement, or
    // additions that happened while the long campaign was running.
    provision::authenticate_corpus_manifest(manifest_path, manifest_sha256, Some(&resources))?;
    run_results.counts = counts;
    run_results.records = writer.finish()?;
    validate_run_results(
        &run_results,
        contract,
        inventory_sha256,
        manifest,
        manifest_sha256,
        artifact_base,
    )?;
    semantic_execution(run_results, &manifest.selection_sha256)
}

fn semantic_execution(
    run_results: CorpusRunResults,
    selection: &str,
) -> Result<SemanticExecution, String> {
    let case_results = aggregate_cases(&run_results.counts, selection);
    Ok(SemanticExecution {
        result: overall_validator_result(&case_results),
        cases: case_counts_from_rows(&case_results)?,
        case_results,
        run_results,
    })
}

fn sync_corpus_directory(path: &Path) -> Result<(), String> {
    #[cfg(unix)]
    fs::File::open(path)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| {
            format!(
                "persist official corpus directory {}: {error}",
                path.display()
            )
        })?;
    #[cfg(not(unix))]
    let _ = path;
    Ok(())
}

fn corpus_auxiliary_tools(results: &CorpusRunResults) -> Result<Vec<AuxiliaryTool>, String> {
    let Some(artifact) = &results.checker else {
        return Ok(Vec::new());
    };
    let version = checker_cohort::version_for_sha(&artifact.sha256)
        .ok_or("corpus checker is outside the independently authenticated source cohort")?;
    Ok(vec![AuxiliaryTool {
        id: unsat_proofs::CARCARA_ID.to_string(),
        role: "independent strict per-query Alethe checker".to_string(),
        artifact: artifact.clone(),
        version_output: version.to_string(),
    }])
}

fn evidence_transcript(output: GuardedTranscriptOutput) -> EvidenceTranscript {
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    EvidenceTranscript {
        process: process_run(output),
        stdout,
        stderr,
    }
}

fn existing_relative_artifact_directory(base: &Path, path: &Path) -> Result<String, String> {
    let path = fs::canonicalize(path)
        .map_err(|error| format!("canonicalize evidence directory: {error}"))?;
    let base =
        fs::canonicalize(base).map_err(|error| format!("canonicalize evidence base: {error}"))?;
    let relative = path
        .strip_prefix(&base)
        .map_err(|_| "query evidence directory must be within the contract directory")?;
    let value = relative
        .to_str()
        .ok_or("query evidence directory is not UTF-8")?
        .to_string();
    validate_relative_path(&value, "query evidence directory")?;
    Ok(value)
}

fn prepare_corpus_checker(
    source: Option<&Path>,
    directory: &Path,
    base: &Path,
    resources: &PlannedResources,
    timeout: Duration,
) -> (Option<Artifact>, Option<EvidenceTranscript>, Option<String>) {
    let mut identity = None;
    let result = (|| {
        let source = source.ok_or("no independent Carcara executable selected")?;
        let authority = checker_cohort::authenticate(source)?;
        let staged = stage_authenticated_executable(source, &authority.sha256, "corpus Carcara")?;
        let observed = evidence_transcript(
            resources
                .run_external_transcript_scrubbed(
                    &staged.path,
                    ["--version"],
                    b"",
                    timeout,
                    "official corpus Carcara identity",
                )
                .map_err(|error| error.to_string())?,
        );
        let valid = observed.process.is_complete()
            && observed.stdout == format!("{}\n", authority.expected_version)
            && observed.stderr.is_empty();
        identity = Some(observed);
        if !valid {
            return Err("independent Carcara identity transcript failed".to_string());
        }
        let target = directory.join("carcara.bin");
        fs::copy(&staged.path, &target)
            .map_err(|error| format!("retain corpus Carcara: {error}"))?;
        fs::File::open(&target)
            .and_then(|file| file.sync_all())
            .map_err(|error| format!("persist corpus Carcara: {error}"))?;
        if sha256_file(&target, "retained corpus Carcara")? != authority.sha256 {
            return Err("retained corpus Carcara digest changed".to_string());
        }
        Ok(Artifact {
            path: existing_relative_artifact(base, &target)?,
            sha256: authority.sha256,
        })
    })();
    match result {
        Ok(artifact) => (Some(artifact), identity, None),
        Err(error) => (None, identity, Some(error)),
    }
}

/// Carcara consumes an assertion document, not an incremental solver session.
/// Admit the original, single check-sat prefix only when every top-level command
/// preserves precisely that assertion scope. In particular, never replay all
/// assertions from a pushed/popped session or discard check-sat assumptions.
fn exact_unsat_problem<'a>(
    bytes: &'a [u8],
    file: &CorpusFile,
    query: &CorpusQuery,
) -> Result<&'a [u8], String> {
    if file.queries.len() != 1 || query.ordinal != 1 || query.command != "check-sat" {
        return Err("independent proof transport currently requires one plain check-sat epoch; incremental/assuming/using queries remain uncertified".to_string());
    }
    let end = usize::try_from(query.byte_end).map_err(|_| "query end exceeds address space")?;
    let prefix = bytes
        .get(..end)
        .ok_or("query prefix exceeds original file")?;
    if sha256_bytes(prefix) != query.prefix_sha256 || scan_queries(prefix)? != [query.clone()] {
        return Err("query prefix differs from immutable manifest".to_string());
    }
    let allowed = [
        "assert",
        "set-logic",
        "set-info",
        "set-option",
        "declare-sort",
        "define-sort",
        "declare-fun",
        "declare-const",
        "define-fun",
        "define-const",
        "declare-datatype",
        "declare-datatypes",
        "check-sat",
    ];
    let mut depth = 0usize;
    let mut index = 0usize;
    while index < prefix.len() {
        match prefix[index] {
            b';' => skip_comment(prefix, &mut index),
            b'"' => skip_string(prefix, &mut index)?,
            b'|' => skip_quoted_symbol(prefix, &mut index)?,
            b'(' => {
                if depth == 0 {
                    let head =
                        top_level_head(prefix, index + 1)?.ok_or("missing top-level command")?;
                    if !allowed.contains(&head.as_str()) {
                        return Err(format!("top-level command {head} lacks exact independent proof-scope transport"));
                    }
                }
                depth += 1;
                index += 1;
            }
            b')' => {
                depth = depth.checked_sub(1).ok_or("unbalanced query prefix")?;
                index += 1;
            }
            _ => index += 1,
        }
    }
    Ok(prefix)
}

fn read_query_prefix(
    path: &Path,
    file: &CorpusFile,
    query: &CorpusQuery,
) -> Result<Vec<u8>, String> {
    if query.byte_end > MAX_IN_MEMORY_QUERY_BYTES {
        return Err(format!(
            "independent query certification remains incomplete: exact prefix has {} bytes, exceeding the existing {}-byte in-memory proof/model transport; the file and query remain in the full corpus population",
            query.byte_end, MAX_IN_MEMORY_QUERY_BYTES
        ));
    }
    let before = fs::symlink_metadata(path)
        .map_err(|error| format!("inspecting exact query source: {error}"))?;
    if before.file_type().is_symlink()
        || !before.is_file()
        || before.len() != file.size
        || query.byte_end > file.size
    {
        return Err("exact query source is linked, non-regular, or size changed".to_string());
    }
    let input =
        fs::File::open(path).map_err(|error| format!("opening exact query source: {error}"))?;
    let end = usize::try_from(query.byte_end).map_err(|_| "query prefix exceeds address space")?;
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(end)
        .map_err(|error| format!("reserving bounded exact query prefix: {error}"))?;
    input
        .take(query.byte_end)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("reading exact query prefix: {error}"))?;
    let after = fs::symlink_metadata(path)
        .map_err(|error| format!("re-inspecting exact query source: {error}"))?;
    if after.file_type().is_symlink()
        || !after.is_file()
        || after.len() != file.size
        || bytes.len() != end
        || sha256_bytes(&bytes) != query.prefix_sha256
    {
        return Err("exact query prefix changed or was truncated".to_string());
    }
    Ok(bytes)
}

fn certify_file_queries(
    result: &mut FileRun,
    file: &CorpusFile,
    path: &Path,
    resources: &PlannedResources,
    ay: &Path,
    z3: &Path,
    checker: Option<&Path>,
    directory: &Path,
    base: &Path,
    timeout: Duration,
) {
    for (query_result, query) in result.queries.iter_mut().zip(&file.queries) {
        if !query_result.ay.is_some_and(CorpusVerdict::decided) {
            continue;
        }
        // Read only this bounded prefix. A very large file can have a small
        // certifiable query followed by large comments or trailing commands.
        let bytes = read_query_prefix(path, file, query);
        if query_result.ay == Some(CorpusVerdict::Sat) {
            let mut evidence = QueryEvidence::absent(query_result.ay);
            match bytes
                .as_ref()
                .map_err(Clone::clone)
                .and_then(|bytes| exact_unsat_problem(bytes, file, query))
            {
                Ok(prefix) => {
                    let query_directory = directory.join(format!(
                        "{}-{}",
                        sha256_bytes(file.path.as_bytes()),
                        query.ordinal
                    ));
                    let checked = sat_evidence::run(
                        prefix,
                        &query_directory,
                        base,
                        ay,
                        z3,
                        resources,
                        timeout,
                    );
                    if checked.accepted() {
                        evidence.status = EvidenceStatus::AcceptedSat;
                        evidence.reason = "exported model is independently consistent and entails every original assertion".to_string();
                    } else {
                        evidence.reason = checked.error.clone().unwrap_or_else(|| {
                            "independent model validation incomplete".to_string()
                        });
                    }
                    evidence.sat = Some(checked);
                }
                Err(error) => evidence.reason = error,
            }
            query_result.certification = format!("{:?}: {}", evidence.status, evidence.reason);
            query_result.evidence = evidence;
            continue;
        }
        if query_result.ay != Some(CorpusVerdict::Unsat) {
            continue;
        }
        let mut evidence = QueryEvidence::absent(query_result.ay);
        let result = (|| {
            let bytes = bytes.as_ref().map_err(Clone::clone)?;
            let query_directory = directory.join(format!(
                "{}-{}",
                sha256_bytes(file.path.as_bytes()),
                query.ordinal
            ));
            fs::create_dir(&query_directory)
                .map_err(|error| format!("create query artifact directory: {error}"))?;
            let problem = query_directory.join("problem.smt2");
            let end =
                usize::try_from(query.byte_end).map_err(|_| "query end exceeds address space")?;
            let prefix = bytes
                .get(..end)
                .ok_or("query prefix exceeds original file")?;
            if sha256_bytes(prefix) != query.prefix_sha256 {
                return Err("query prefix digest changed".to_string());
            }
            atomic_write_new(&problem, prefix)?;
            evidence.problem = Some(Artifact {
                path: existing_relative_artifact(base, &problem)?,
                sha256: query.prefix_sha256.clone(),
            });
            if let Err(error) = exact_unsat_problem(bytes, file, query) {
                evidence.status = EvidenceStatus::UnsupportedQuery;
                return Err(error);
            }
            let checker = checker.ok_or("pinned independent checker unavailable")?;
            let proof = query_directory.join("proof.alethe");
            let args = [
                OsString::from("solve"),
                OsString::from("--quiet"),
                OsString::from("--strict-proofs"),
                OsString::from("--self-check"),
                OsString::from("--alethe-dialect"),
                OsString::from("pinned-carcara"),
                OsString::from("--proof"),
                proof.as_os_str().to_owned(),
                OsString::from("--memory"),
                OsString::from(resources.plan.memlimit_mb_per_child.to_string()),
                problem.as_os_str().to_owned(),
            ];
            let producer = resources
                .run_external_transcript_scrubbed_with_file_limit(
                    ay,
                    args,
                    b"",
                    timeout,
                    "official corpus exact query proof emission",
                    MAX_QUERY_PROOF_BYTES,
                )
                .map_err(|error| error.to_string())?;
            evidence.producer = Some(evidence_transcript(producer));
            evidence.status = EvidenceStatus::Rejected;
            let proof_bytes =
                read_bounded_bytes(&proof, MAX_QUERY_PROOF_BYTES, "query Alethe proof", true)?;
            fs::File::open(&proof)
                .and_then(|file| file.sync_all())
                .map_err(|error| format!("persist query Alethe proof: {error}"))?;
            sync_corpus_directory(&query_directory)?;
            evidence.proof = Some(Artifact {
                path: existing_relative_artifact(base, &proof)?,
                sha256: sha256_bytes(&proof_bytes),
            });
            let producer = evidence
                .producer
                .as_ref()
                .ok_or("missing proof producer transcript")?;
            if !producer.process.is_complete()
                || producer.process.verdicts != [CorpusVerdict::Unsat]
            {
                return Err(
                    "proof producer did not complete with exactly the retained UNSAT verdict"
                        .to_string(),
                );
            }
            let problem_text =
                std::str::from_utf8(prefix).map_err(|_| "query proof problem is not UTF-8")?;
            unsat_proofs::pinned_carcara_can_judge(problem_text, &proof_bytes)?;
            let observed = evidence_transcript(run_query_checker(
                checker, &proof, &problem, resources, timeout,
            )?);
            let accepted = observed.process.is_complete()
                && observed.stdout == "valid\n"
                && observed.stderr.is_empty();
            evidence.checker = Some(observed);
            if !accepted {
                return Err(
                    "independent strict Carcara did not accept the exact query proof".to_string(),
                );
            }
            evidence.status = EvidenceStatus::AcceptedUnsat;
            evidence.reason =
                "exact original query-prefix proof accepted by authenticated independent Carcara"
                    .to_string();
            Ok(())
        })();
        if let Err(error) = result {
            evidence.reason = error;
        }
        query_result.certification = format!("{:?}: {}", evidence.status, evidence.reason);
        query_result.evidence = evidence;
    }
    for query in &mut result.queries {
        query.outcome = query_outcome(query.z3, query.ay, &query.evidence);
    }
    result.outcome = classify_file_outcome(file, &result.ay, &result.z3, &result.queries);
}

fn run_query_checker(
    checker: &Path,
    proof: &Path,
    problem: &Path,
    resources: &PlannedResources,
    timeout: Duration,
) -> Result<GuardedTranscriptOutput, String> {
    // No let expansion: the exact problem's let bindings are owned by proof
    // steps, and the pinned checker changes rule admission under expansion.
    resources
        .run_external_transcript_scrubbed(
            checker,
            [
                OsString::from("check"),
                OsString::from("--strict-parsing"),
                OsString::from("--"),
                proof.as_os_str().to_owned(),
                problem.as_os_str().to_owned(),
            ],
            b"",
            timeout,
            "official corpus independent exact query proof replay",
        )
        .map_err(|error| error.to_string())
}

fn validate_evidence_transcript(transcript: &EvidenceTranscript) -> Result<(), String> {
    if transcript.stdout.len() > 1024 * 1024
        || transcript.stderr.len() > 1024 * 1024
        || sha256_bytes(transcript.stdout.as_bytes()) != transcript.process.stdout_sha256
        || sha256_bytes(transcript.stderr.as_bytes()) != transcript.process.stderr_sha256
        || transcript
            .stdout
            .lines()
            .filter_map(CorpusVerdict::parse)
            .collect::<Vec<_>>()
            != transcript.process.verdicts
        || transcript
            .stdout
            .lines()
            .chain(transcript.stderr.lines())
            .any(is_error_diagnostic)
            != transcript.process.error_diagnostic
    {
        return Err(
            "query evidence transcript differs from its bounded process record".to_string(),
        );
    }
    Ok(())
}

fn validate_query_evidence(
    query: &CorpusQuery,
    result: &QueryRun,
    file: &CorpusFile,
    bytes: &[u8],
    base: &Path,
    checker: Option<&Artifact>,
) -> Result<(), String> {
    let evidence = &result.evidence;
    if result.ay == Some(CorpusVerdict::Sat) {
        if evidence.problem.is_some()
            || evidence.proof.is_some()
            || evidence.producer.is_some()
            || evidence.checker.is_some()
        {
            return Err("SAT query carries foreign UNSAT evidence fields".to_string());
        }
        if !matches!(
            evidence.status,
            EvidenceStatus::UncertifiedSat | EvidenceStatus::AcceptedSat
        ) {
            return Err("SAT query has a foreign evidence classification".to_string());
        }
        if let Some(checked) = &evidence.sat {
            let prefix = if checked.accepted() {
                exact_unsat_problem(bytes, file, query)?
            } else {
                &[]
            };
            sat_evidence::validate(checked, prefix, base)?;
            if checked.accepted() != (evidence.status == EvidenceStatus::AcceptedSat) {
                return Err(
                    "SAT query classification disagrees with its independent validation"
                        .to_string(),
                );
            }
        } else if evidence.status == EvidenceStatus::AcceptedSat {
            return Err("accepted SAT query has no independent model evidence".to_string());
        }
        return Ok(());
    } else if evidence.sat.is_some() || evidence.status == EvidenceStatus::AcceptedSat {
        return Err("SAT model evidence attached to another verdict".to_string());
    }
    if !result.ay.is_some_and(CorpusVerdict::decided)
        && (evidence.problem.is_some()
            || evidence.proof.is_some()
            || evidence.producer.is_some()
            || evidence.checker.is_some())
    {
        return Err("undecided query retained stale decided-artifact evidence".to_string());
    }
    for artifact in [evidence.problem.as_ref(), evidence.proof.as_ref()]
        .into_iter()
        .flatten()
    {
        let path = resolve_relative_evidence_path(base, &artifact.path)?;
        if sha256_file(&path, "retained query artifact")? != artifact.sha256 {
            return Err("retained query artifact digest mismatch".to_string());
        }
    }
    for transcript in [evidence.producer.as_ref(), evidence.checker.as_ref()]
        .into_iter()
        .flatten()
    {
        validate_evidence_transcript(transcript)?;
    }
    if evidence.status != EvidenceStatus::AcceptedUnsat {
        if !result.ay.is_some_and(CorpusVerdict::decided)
            && evidence.status != EvidenceStatus::NotDecided
        {
            return Err("undecided query cannot claim decided-artifact evidence".to_string());
        }
        return Ok(());
    }
    if result.ay != Some(CorpusVerdict::Unsat) {
        return Err("UNSAT evidence attached to a different published verdict".to_string());
    }
    let checker = checker.ok_or("accepted query proof has no authenticated checker")?;
    if checker_cohort::version_for_sha(&checker.sha256).is_none() {
        return Err("query checker authority differs from declared pin".to_string());
    }
    let prefix = exact_unsat_problem(bytes, file, query)?;
    let problem = evidence
        .problem
        .as_ref()
        .ok_or("accepted query proof has no problem")?;
    let problem_path = resolve_relative_evidence_path(base, &problem.path)?;
    if problem.sha256 != query.prefix_sha256
        || read_bounded_bytes(
            &problem_path,
            MAX_IN_MEMORY_QUERY_BYTES,
            "retained exact query",
            true,
        )? != prefix
    {
        return Err("proof problem is not the exact original query prefix".to_string());
    }
    let proof = evidence
        .proof
        .as_ref()
        .ok_or("accepted query proof has no certificate")?;
    let proof_path = resolve_relative_evidence_path(base, &proof.path)?;
    let proof_bytes = read_bounded_bytes(
        &proof_path,
        MAX_QUERY_PROOF_BYTES,
        "retained query proof",
        true,
    )?;
    unsat_proofs::pinned_carcara_can_judge(
        std::str::from_utf8(prefix).map_err(|_| "query prefix is not UTF-8")?,
        &proof_bytes,
    )?;
    let producer = evidence
        .producer
        .as_ref()
        .ok_or("accepted query proof has no producer transcript")?;
    let observed = evidence
        .checker
        .as_ref()
        .ok_or("accepted query proof has no checker transcript")?;
    if !producer.process.is_complete()
        || producer.process.verdicts != [CorpusVerdict::Unsat]
        || !observed.process.is_complete()
        || observed.stdout != "valid\n"
        || !observed.stderr.is_empty()
    {
        return Err(
            "accepted query proof has a failing producer or checker transcript".to_string(),
        );
    }
    Ok(())
}

fn replay_retained_proofs(
    results: &CorpusRunResults,
    base: &Path,
    timeout: Duration,
) -> Result<(), String> {
    let has_models = results.counts.independently_checked_sat > 0;
    let has_proofs = results.counts.independently_checked_unsat > 0;
    if !has_models && !has_proofs {
        return Ok(());
    }
    let staged = if has_proofs {
        let checker = results
            .checker
            .as_ref()
            .ok_or("retained query proof checker missing")?;
        Some(stage_authenticated_executable(
            &resolve_relative_evidence_path(base, &checker.path)?,
            &checker.sha256,
            "retained query proof checker",
        )?)
    } else {
        None
    };
    let z3 = if has_models {
        let reference = canonical_profile()?.z3_overlay.reference_executable;
        Some(stage_authenticated_executable(
            &reference_artifact_path(&reference.path)?,
            &reference.sha256,
            "retained model checker",
        )?)
    } else {
        None
    };
    let root = locate_repo_root()?;
    let resources = PlannedResources::plan(&root, 1, "official corpus retained query proof replay")
        .map_err(|error| error.to_string())?;
    let envelope = effective_execution_envelope(
        &resources.plan,
        ENFORCEMENT_RSS_WATCHDOG_V1,
        timeout.as_secs_f64(),
    )
    .map_err(|error| error.to_string())?;
    if envelope != results.resource_envelope {
        return Err("retained query proof replay envelope drift".to_string());
    }
    records::visit(
        &results.records,
        base,
        &records::Header::new(results, results.counts.files_total),
        |_, file| {
            replay_accepted_row(
                &file,
                base,
                z3.as_ref().map(|tool| tool.path.as_path()),
                staged.as_ref().map(|tool| tool.path.as_path()),
                &resources,
                timeout,
            )
        },
    )
}

fn replay_accepted_row(
    file: &FileRun,
    base: &Path,
    z3: Option<&Path>,
    checker: Option<&Path>,
    resources: &PlannedResources,
    timeout: Duration,
) -> Result<(), String> {
    for query in &file.queries {
        match query.evidence.status {
            EvidenceStatus::AcceptedSat => sat_evidence::replay(
                query
                    .evidence
                    .sat
                    .as_ref()
                    .ok_or("retained SAT evidence missing")?,
                base,
                z3.ok_or("retained model checker missing")?,
                resources,
                timeout,
            )?,
            EvidenceStatus::AcceptedUnsat => {
                let problem = query
                    .evidence
                    .problem
                    .as_ref()
                    .ok_or("retained query problem missing")?;
                let proof = query
                    .evidence
                    .proof
                    .as_ref()
                    .ok_or("retained query proof missing")?;
                let directory = tempfile::tempdir()
                    .map_err(|error| format!("create private UNSAT replay directory: {error}"))?;
                let problem_path = directory.path().join("problem.smt2");
                let proof_path = directory.path().join("proof.alethe");
                stage_replay_artifact(base, problem, &problem_path, MAX_IN_MEMORY_QUERY_BYTES)?;
                stage_replay_artifact(base, proof, &proof_path, MAX_QUERY_PROOF_BYTES)?;
                let observed = evidence_transcript(run_query_checker(
                    checker.ok_or("retained proof checker missing")?,
                    &proof_path,
                    &problem_path,
                    resources,
                    timeout,
                )?);
                if !observed.process.is_complete()
                    || observed.stdout != "valid\n"
                    || !observed.stderr.is_empty()
                {
                    return Err(format!(
                        "retained query certificate fails independent replay: {}",
                        proof.path
                    ));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn stage_replay_artifact(
    base: &Path,
    artifact: &Artifact,
    stage: &Path,
    limit: u64,
) -> Result<(), String> {
    let input = resolve_relative_evidence_path(base, &artifact.path)?;
    let bytes = read_bounded_bytes(&input, limit, "retained corpus proof input", true)?;
    if sha256_bytes(&bytes) != artifact.sha256 {
        return Err(format!(
            "retained corpus proof input digest changed: {}",
            artifact.path
        ));
    }
    fs::write(stage, bytes)
        .map_err(|error| format!("stage authenticated corpus proof input: {error}"))
}

struct RetainedReplay<'a> {
    base: &'a Path,
    ay: &'a Path,
    z3: &'a Path,
    checker: Option<&'a Path>,
    checker_sha256: Option<&'a str>,
    resources: &'a PlannedResources,
    timeout: Duration,
}

impl RetainedReplay<'_> {
    fn replay(&self, result: &FileRun, file: &CorpusFile, root: &Path) -> Result<(), String> {
        replay_accepted_row(
            result,
            self.base,
            Some(self.z3),
            self.checker,
            self.resources,
            self.timeout,
        )?;
        // A certificate proves its logical claim. Clean child execution,
        // the reference decision and shared unknown need live observations.
        if requires_decision_replay(result) {
            let path = root.join(&file.path);
            check_retained_decision_input(&path, file)?;
            let current = run_file(self.resources, self.ay, self.z3, &path, file, self.timeout);
            check_retained_decision_input(&path, file)?;
            if !same_decision_observation(&result.ay, &current.ay)
                || !same_decision_observation(&result.z3, &current.z3)
            {
                return Err(format!(
                    "retained official corpus decision did not replay: {}",
                    file.path
                ));
            }
        }
        Ok(())
    }

    fn check_tools(&self, ay_sha256: &str, z3_sha256: &str) -> Result<(), String> {
        if sha256_file(self.ay, "staged AY after official corpus")? != ay_sha256
            || sha256_file(self.z3, "staged Z3 after official corpus")? != z3_sha256
        {
            return Err("authenticated solver bytes changed during official corpus run".into());
        }
        if let Some((checker, digest)) = self.checker.zip(self.checker_sha256) {
            if sha256_file(checker, "staged official corpus checker")? != digest {
                return Err(
                    "authenticated checker bytes changed during official corpus run".into(),
                );
            }
        }
        Ok(())
    }
}

fn requires_decision_replay(result: &FileRun) -> bool {
    result.outcome == FileOutcome::Pass
        || result
            .queries
            .iter()
            .any(|query| query.outcome == QueryOutcome::Pass)
}

fn check_retained_decision_input(path: &Path, file: &CorpusFile) -> Result<(), String> {
    let metadata = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    if !metadata.is_file()
        || metadata.len() != file.size
        || sha256_file(path, "official corpus retained decision input")? != file.sha256
    {
        return Err(format!(
            "official corpus decision input changed: {}",
            file.path
        ));
    }
    Ok(())
}

fn same_decision_observation(retained: &ProcessRun, observed: &ProcessRun) -> bool {
    // Compare decision and process facts independently of runtime measurements.
    retained.verdicts == observed.verdicts
        && retained.exit_code == observed.exit_code
        && retained.stdin_complete == observed.stdin_complete
        && retained.timed_out == observed.timed_out
        && retained.memout == observed.memout
        && retained.stdout_truncated == observed.stdout_truncated
        && retained.stderr_truncated == observed.stderr_truncated
        && retained.stdout_utf8 == observed.stdout_utf8
        && retained.stderr_utf8 == observed.stderr_utf8
        && retained.error_diagnostic == observed.error_diagnostic
        && retained.harness_error == observed.harness_error
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
    let z3_run = match resources.run_external_transcript_scrubbed(
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
    let ay_run = match resources.run_external_transcript_scrubbed(
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

fn query_outcome(
    reference: Option<CorpusVerdict>,
    subject: Option<CorpusVerdict>,
    evidence: &QueryEvidence,
) -> QueryOutcome {
    match (reference, subject) {
        (Some(a), Some(b)) if a == b => QueryOutcome::Pass,
        (Some(CorpusVerdict::Unknown), Some(value))
            if value.decided() && evidence.satisfies(subject) =>
        {
            QueryOutcome::Pass
        }
        (Some(a), Some(b)) if a.decided() && b.decided() => QueryOutcome::Wrong,
        _ => QueryOutcome::Missing,
    }
}

fn classify_file(file: &CorpusFile, ay: ProcessRun, z3: ProcessRun) -> FileRun {
    let mut queries = Vec::with_capacity(file.queries.len());
    for query in &file.queries {
        let z3_verdict = z3.verdicts.get(query.ordinal - 1).copied();
        let ay_verdict = ay.verdicts.get(query.ordinal - 1).copied();
        let evidence = QueryEvidence::absent(ay_verdict);
        let outcome = query_outcome(z3_verdict, ay_verdict, &evidence);
        let certification = format!("{:?}: {}", evidence.status, evidence.reason);
        queries.push(QueryRun {
            ordinal: query.ordinal,
            command: query.command.clone(),
            prefix_sha256: query.prefix_sha256.clone(),
            z3: z3_verdict,
            ay: ay_verdict,
            certification,
            evidence,
            outcome,
        });
    }
    let outcome = classify_file_outcome(file, &ay, &z3, &queries);
    FileRun {
        path: file.path.clone(),
        input_sha256: file.sha256.clone(),
        input_size: None,
        query_count: file.queries.len(),
        ay,
        z3,
        echo_streams: None,
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
        || queries
            .iter()
            .any(|query| !query.evidence.satisfies(query.ay))
    {
        FileOutcome::Fail
    } else {
        FileOutcome::Pass
    }
}

fn accumulate_run_counts(counts: &mut CorpusRunCounts, file: &FileRun) -> Result<(), String> {
    counts.files_total = counts
        .files_total
        .checked_add(1)
        .ok_or("corpus file count overflow")?;
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
        counts.independently_checked_unsat +=
            usize::from(query.evidence.status == EvidenceStatus::AcceptedUnsat);
        counts.independently_checked_sat +=
            usize::from(query.evidence.status == EvidenceStatus::AcceptedSat);
        counts.uncertified_decisions += usize::from(
            query.ay.is_some_and(CorpusVerdict::decided) && !query.evidence.satisfies(query.ay),
        );
    }
    let extra_ay = file.ay.verdicts.len().saturating_sub(file.query_count);
    let extra_z3 = file.z3.verdicts.len().saturating_sub(file.query_count);
    counts.missing = counts
        .missing
        .checked_add(extra_ay)
        .and_then(|value| value.checked_add(extra_z3))
        .ok_or("official corpus extra-verdict count overflow")?;
    Ok(())
}

#[cfg(test)]
fn derive_run_counts(files: &[FileRun]) -> Result<CorpusRunCounts, String> {
    let mut counts = CorpusRunCounts::default();
    for file in files {
        accumulate_run_counts(&mut counts, file)?;
    }
    Ok(counts)
}

fn validate_run_results(
    results: &CorpusRunResults,
    contract: &Contract,
    inventory_sha256: &str,
    manifest: &OfficialCorpusManifest,
    manifest_sha256: &str,
    artifact_base: &Path,
) -> Result<(), String> {
    match (results.schema.as_str(), &results.evaluator_sha256) {
        (LEGACY_RUN_RESULTS_SCHEMA, None) => {}
        (RUN_RESULTS_SCHEMA, Some(evaluator)) => validate_sha256(evaluator, "corpus evaluator")?,
        _ => return Err("official corpus results schema or producer binding mismatch".into()),
    }
    if results.campaign_id != contract.campaign_id
        || results.profile_id != PROFILE_ID
        || results.profile_sha256 != canonical_profile_sha256()?
        || results.inventory_sha256 != inventory_sha256
        || results.corpus_manifest_sha256 != manifest_sha256
        || results.corpus_selection_sha256 != manifest.selection_sha256
        || results.corpus_root != manifest.corpus_root
        || results.resource_envelope != contract.resource_envelope.as_deref().unwrap_or_default()
        || results.ay_mode
            != "solve --quiet --competition --strict-proofs --self-check --memory <planned-MiB> <file>; rss-watchdog"
        || results.z3_mode != "z3-5.3.3 -smt2 <file>; rss-watchdog"
        || results.query_proof_mode != "solve --quiet --strict-proofs --self-check --alethe-dialect pinned-carcara --proof <query-proof> --memory <planned-MiB> <exact-query-prefix>; rss-watchdog; rlimit-fsize"
        || results.query_checker_mode != "carcara check --strict-parsing -- <query-proof> <exact-query-prefix>; rss-watchdog"
        || results.query_model_mode != "AY get-model over exact query; Z3 model-constraint consistency SAT then original-assertion counterexample UNSAT; rss-watchdog"
        || results.query_proof_file_limit_bytes != MAX_QUERY_PROOF_BYTES
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
        || results.records.rows != manifest.files.len()
    {
        return Err("official corpus result artifact or file count binding drift".to_string());
    }
    validate_relative_path(&results.artifact_root, "query evidence root")?;
    if !Path::new(&results.records.artifact.path).starts_with(&results.artifact_root) {
        return Err("corpus records escape their evidence root".to_string());
    }
    if let Some(checker) = &results.checker {
        let version = checker_cohort::version_for_sha(&checker.sha256)
            .ok_or("official corpus checker is outside authenticated cohort")?;
        if results.checker_error.is_some() {
            return Err("official corpus checker authority drift".to_string());
        }
        let path = corpus_artifact_path(artifact_base, &results.artifact_root, checker)?;
        if sha256_file(&path, "retained independent checker")? != checker.sha256 {
            return Err("retained independent checker digest/path drift".to_string());
        }
        let identity = results
            .checker_identity
            .as_ref()
            .ok_or("missing checker identity transcript")?;
        validate_evidence_transcript(identity)?;
        if !identity.process.is_complete()
            || identity.stdout != format!("{version}\n")
            || !identity.stderr.is_empty()
        {
            return Err("independent checker identity is not accepted".to_string());
        }
    } else if results.checker_error.is_none() {
        return Err("missing independent checker must carry an explicit error".to_string());
    }
    let mut derived = CorpusRunCounts::default();
    records::visit(
        &results.records,
        artifact_base,
        &records::Header::new(results, manifest.files.len()),
        |index, result| {
            let file = manifest
                .files
                .get(index)
                .ok_or("unexpected corpus record index")?;
            validate_file_result(
                &result,
                file,
                &manifest.corpus_root,
                artifact_base,
                &results.artifact_root,
                results.checker.as_ref(),
            )?;
            accumulate_run_counts(&mut derived, &result)
        },
    )?;
    if results.counts != derived {
        return Err("official corpus aggregate counts do not match per-query rows".to_string());
    }
    Ok(())
}

fn validate_file_result(
    result: &FileRun,
    file: &CorpusFile,
    corpus_root: &str,
    artifact_base: &Path,
    artifact_root: &str,
    checker: Option<&Artifact>,
) -> Result<(), String> {
    require_file_result_identity(result, file)?;
    for (query_result, query) in result.queries.iter().zip(&file.queries) {
        for artifact in [
            query_result.evidence.problem.as_ref(),
            query_result.evidence.proof.as_ref(),
        ]
        .into_iter()
        .flatten()
        {
            corpus_artifact_path(artifact_base, artifact_root, artifact)?;
        }
        if let Some(model) = &query_result.evidence.sat {
            for artifact in model.artifacts().into_iter().flatten() {
                corpus_artifact_path(artifact_base, artifact_root, artifact)?;
            }
        }
        let source = if matches!(
            query_result.evidence.status,
            EvidenceStatus::AcceptedUnsat | EvidenceStatus::AcceptedSat
        ) {
            read_query_prefix(&PathBuf::from(corpus_root).join(&file.path), file, query)?
        } else {
            Vec::new()
        };
        validate_query_evidence(query, query_result, file, &source, artifact_base, checker)?;
    }
    require_recorded_classification(result, file)
}

fn corpus_artifact_path(base: &Path, root: &str, artifact: &Artifact) -> Result<PathBuf, String> {
    let path = resolve_relative_evidence_path(base, &artifact.path)?;
    if !Path::new(&artifact.path).starts_with(root) || path != base.join(&artifact.path) {
        return Err(format!(
            "corpus artifact escapes or redirects its evidence path: {}",
            artifact.path
        ));
    }
    Ok(path)
}

fn require_file_result_identity(result: &FileRun, file: &CorpusFile) -> Result<(), String> {
    let expected_input_sha256 = file.sha256.as_str();
    if result.path != file.path
        || result.input_sha256.as_str() != expected_input_sha256
        || result.input_size.is_some_and(|size| size != file.size)
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
    Ok(())
}

fn require_recorded_classification(result: &FileRun, file: &CorpusFile) -> Result<(), String> {
    let queries_agree = result.queries.iter().all(|query| {
        let z3 = result.z3.verdicts.get(query.ordinal - 1).copied();
        let ay = result.ay.verdicts.get(query.ordinal - 1).copied();
        query.z3 == z3
            && query.ay == ay
            && query.outcome == query_outcome(z3, ay, &query.evidence)
            && query.certification
                == format!("{:?}: {}", query.evidence.status, query.evidence.reason)
    });
    if !queries_agree
        || classify_file_outcome(file, &result.ay, &result.z3, &result.queries) != result.outcome
    {
        return Err(format!(
            "official corpus result classification was forged for {:?}",
            file.path
        ));
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
            "every reference-decided query matches AY; stronger AY decisions carry independent evidence; shared unknown is preserved",
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
            "corpus.evidence.decisions",
            input_sha256,
            "every decided query has independent evidence for its exact original query scope; SAT model coverage is not supplied by canaries",
            format!("independently-checked-sat={};independently-checked-unsat={};uncertified-decisions={}", counts.independently_checked_sat, counts.independently_checked_unsat, counts.uncertified_decisions),
            if counts.uncertified_decisions == 0 { ValidatorCaseOutcome::Pass } else { ValidatorCaseOutcome::Fail },
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
    results: &CorpusRunResults,
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
        digest_kind: format!("{}-json-sha256", results.schema),
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
    results: &CorpusRunResults,
    bytes: &[u8],
) -> Result<(), String> {
    let expected = results_reference_input(
        contract,
        manifest,
        results,
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
    report_written_receipt(loaded, path, receipt, label, report, &bytes)
}

fn report_written_receipt(
    loaded: &LoadedContract,
    path: &Path,
    receipt: &ValidatorReceipt,
    label: &str,
    report: &AuditReport,
    bytes: &[u8],
) -> Result<i32, String> {
    let relative = future_relative_output(&loaded.base, path)?;
    let receipt_sha256 = sha256_bytes(bytes);
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
    rows_sha256: String,
}

fn semantic_signature(results: &CorpusRunResults) -> SemanticSignature {
    SemanticSignature {
        counts: results.counts.clone(),
        rows_sha256: results.records.semantic_sha256.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_md5_records_reject_diagnostics_and_additional_results() {
        let digest = "900150983cd24fb0d6963f7d28e17f72";
        assert_eq!(parse_md5_digest(&format!("{digest}\n")).unwrap(), digest);
        assert_eq!(
            parse_md5_digest(&format!("{digest}  /a path/with\na newline\0")).unwrap(),
            digest
        );
        for output in [
            format!("{digest}\n{digest}\n"),
            format!("{digest}  /first\0{digest}  /second\0"),
            format!("{digest} diagnostic"),
            "invalid digest\n".to_string(),
        ] {
            assert!(parse_md5_digest(&output).is_err());
        }
    }

    fn query_file(bytes: &[u8]) -> CorpusFile {
        CorpusFile {
            path: "QF_UF/control.smt2".to_string(),
            size: bytes.len() as u64,
            sha256: sha256_bytes(bytes),
            queries: scan_queries(bytes).unwrap(),
            echoes: None,
        }
    }

    #[test]
    fn large_sparse_file_retains_small_exact_query_prefix_without_whole_file_allocation() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("large.smt2");
        let prefix = b"(check-sat)";
        let mut disk = fs::File::create(&path).unwrap();
        std::io::Write::write_all(&mut disk, b"(check-sat)\n;").unwrap();
        let measured_size = 1_169_487_267;
        disk.set_len(measured_size).unwrap();
        let mut file = query_file(prefix);
        file.size = measured_size;
        assert_eq!(
            read_query_prefix(&path, &file, &file.queries[0]).unwrap(),
            prefix
        );
        file.queries[0].prefix_sha256 = "0".repeat(64);
        assert!(read_query_prefix(&path, &file, &file.queries[0])
            .unwrap_err()
            .contains("changed"));
        file.queries[0].byte_end = MAX_IN_MEMORY_QUERY_BYTES + 1;
        assert!(read_query_prefix(&path, &file, &file.queries[0])
            .unwrap_err()
            .contains("certification remains incomplete"));
    }

    #[test]
    fn bounded_prefix_does_not_replace_full_population_tail_integrity() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("tail.smt2");
        let original = b"(check-sat)\n; tail-one\n";
        fs::write(&path, original).unwrap();
        let before = collect_corpus_files(directory.path()).unwrap();
        let file = &before[0];
        let prefix = read_query_prefix(&path, file, &file.queries[0]).unwrap();
        fs::write(&path, b"(check-sat)\n; tail-two\n").unwrap();
        assert_eq!(
            read_query_prefix(&path, file, &file.queries[0]).unwrap(),
            prefix
        );
        let after = collect_corpus_files(directory.path()).unwrap();
        assert_eq!(before[0].queries, after[0].queries);
        assert_ne!(before[0].sha256, after[0].sha256);
        // verify_materialization compares this entire row population before
        // and after execution, so an unchanged prefix cannot hide tail drift.
        assert_ne!(before, after);
        fs::write(&path, b"(check-sat)").unwrap();
        assert!(read_query_prefix(&path, file, &file.queries[0]).is_err());
        fs::write(&path, b"(check-sat)\n; tail-one\nextra").unwrap();
        assert!(read_query_prefix(&path, file, &file.queries[0]).is_err());
    }

    #[test]
    fn oversized_tar_member_is_streamed_and_truncation_is_not_a_size_exclusion() {
        let mut header = [0u8; 512];
        let name = b"QF_ABV/2019-Mann/ridecore-qf_abv-bug.smt2";
        header[..name.len()].copy_from_slice(name);
        header[124..136].copy_from_slice(format!("{:011o}\0", 1_169_487_267u64).as_bytes());
        header[156] = b'0';
        header[148..156].fill(b' ');
        let checksum: u64 = header.iter().map(|byte| u64::from(*byte)).sum();
        header[148..156].copy_from_slice(format!("{checksum:06o}\0 ").as_bytes());
        let bytes = [header.as_slice(), b"(check-sat)\n"].concat();
        let mut input = std::io::Cursor::new(bytes);
        let error = parse_tar_stream(
            &mut input,
            "QF_ABV",
            crate::fetch::official_archive_expansion_budget(u64::MAX),
        )
        .unwrap_err();
        assert!(error.contains("truncated"), "{error}");
        let mut input = std::io::Cursor::new(header);
        let error = parse_tar_stream(&mut input, "QF_ABV", 1024).unwrap_err();
        assert!(error.contains("expansion budget"), "{error}");
    }

    fn completed_process(verdict: CorpusVerdict) -> ProcessRun {
        let text = match verdict {
            CorpusVerdict::Sat => b"sat\n".as_slice(),
            CorpusVerdict::Unsat => b"unsat\n".as_slice(),
            CorpusVerdict::Unknown => b"unknown\n".as_slice(),
        };
        ProcessRun {
            exit_code: Some(0),
            stdin_complete: true,
            timed_out: false,
            memout: false,
            stdout_truncated: false,
            stderr_truncated: false,
            stdout_utf8: true,
            stderr_utf8: true,
            error_diagnostic: false,
            harness_error: None,
            stdout_sha256: sha256_bytes(text),
            stderr_sha256: sha256_bytes(b""),
            observed_ns: 1,
            verdicts: vec![verdict],
        }
    }

    #[test]
    fn retained_shared_unknown_requires_fresh_bilateral_observation() {
        let file = query_file(b"(check-sat)");
        let recorded = classify_file(
            &file,
            completed_process(CorpusVerdict::Unknown),
            completed_process(CorpusVerdict::Unknown),
        );
        assert!(requires_decision_replay(&recorded));
        assert_eq!(recorded.queries[0].outcome, QueryOutcome::Pass);
        let mut fresh = completed_process(CorpusVerdict::Unknown);
        fresh.observed_ns = 760;
        assert!(same_decision_observation(&recorded.z3, &fresh));
        assert!(!same_decision_observation(
            &recorded.z3,
            &completed_process(CorpusVerdict::Sat),
        ));
        fresh.timed_out = true;
        assert!(!same_decision_observation(&recorded.z3, &fresh));
    }

    #[test]
    fn proof_problem_is_the_exact_bound_query_prefix() {
        let bytes = b"(set-info :source \"push and pop are only text\")\n(assert false)\n(check-sat)\n(exit)\n";
        let file = query_file(bytes);
        let query = &file.queries[0];
        let prefix = exact_unsat_problem(bytes, &file, query).unwrap();
        assert_eq!(prefix, &bytes[..query.byte_end as usize]);
        assert!(!prefix.ends_with(b"(exit)\n"));
        let foreign = b"(set-info :source \"push and pop are only text\")\n(assert true )\n(check-sat)\n(exit)\n";
        assert!(exact_unsat_problem(foreign, &file, query).is_err());
    }

    #[test]
    fn incremental_and_assumed_scopes_cannot_be_flattened_into_proofs() {
        for bytes in [
            b"(push 1)\n(assert false)\n(pop 1)\n(check-sat)".as_slice(),
            b"(assert false)\n(reset-assertions)\n(check-sat)".as_slice(),
            b"(declare-const p Bool)\n(check-sat-assuming (p (not p)))".as_slice(),
            b"(assert false)\n(check-sat)\n(check-sat)".as_slice(),
            b"(assert false)\n(check-sat-using smt)".as_slice(),
        ] {
            let file = query_file(bytes);
            assert!(exact_unsat_problem(bytes, &file, &file.queries[0]).is_err());
        }
    }

    #[test]
    fn agreed_sat_is_still_uncertified_without_a_per_query_model_check() {
        let file = query_file(b"(assert true)\n(check-sat)");
        let result = classify_file(
            &file,
            completed_process(CorpusVerdict::Sat),
            completed_process(CorpusVerdict::Sat),
        );
        assert_eq!(result.queries[0].outcome, QueryOutcome::Pass);
        assert_eq!(
            result.queries[0].evidence.status,
            EvidenceStatus::UncertifiedSat
        );
        assert_eq!(result.outcome, FileOutcome::Fail);
        let counts = derive_run_counts(&[result]).unwrap();
        assert_eq!(counts.parity_passed, 1);
        assert_eq!(counts.uncertified_decisions, 1);
        assert!(!counts.complete());
    }

    #[test]
    fn unsat_agreement_cannot_substitute_for_an_independent_proof() {
        let file = query_file(b"(assert false)\n(check-sat)");
        let result = classify_file(
            &file,
            completed_process(CorpusVerdict::Unsat),
            completed_process(CorpusVerdict::Unsat),
        );
        assert_eq!(result.queries[0].outcome, QueryOutcome::Pass);
        assert_eq!(result.outcome, FileOutcome::Fail);
        let counts = derive_run_counts(&[result]).unwrap();
        assert_eq!(counts.independently_checked_unsat, 0);
        assert_eq!(counts.uncertified_decisions, 1);
    }

    #[test]
    fn valid_word_with_a_different_captured_transcript_is_rejected() {
        let mut process = completed_process(CorpusVerdict::Unsat);
        process.verdicts.clear();
        process.stdout_sha256 = sha256_bytes(b"invalid\n");
        let forged = EvidenceTranscript {
            process,
            stdout: "valid\n".to_string(),
            stderr: String::new(),
        };
        assert!(validate_evidence_transcript(&forged).is_err());
    }

    #[test]
    fn correctly_hashed_foreign_problem_cannot_certify_the_original_query() {
        let original = b"(assert false)\n(check-sat)";
        let foreign = b"(assert true)\n(check-sat)";
        let file = query_file(original);
        let mut result = classify_file(
            &file,
            completed_process(CorpusVerdict::Unsat),
            completed_process(CorpusVerdict::Unsat),
        );
        let directory = tempfile::tempdir().unwrap();
        fs::write(directory.path().join("foreign.smt2"), foreign).unwrap();
        result.queries[0].evidence.status = EvidenceStatus::AcceptedUnsat;
        result.queries[0].evidence.problem = Some(Artifact {
            path: "foreign.smt2".to_string(),
            sha256: sha256_bytes(foreign),
        });
        let checker = Artifact {
            path: "checker".to_string(),
            sha256: checker_cohort::LEGACY_SHA256.to_string(),
        };
        let error = validate_query_evidence(
            &file.queries[0],
            &result.queries[0],
            &file,
            original,
            directory.path(),
            Some(&checker),
        )
        .unwrap_err();
        assert!(error.contains("exact original query prefix"), "{error}");
    }

    #[test]
    fn mutable_zenodo_statistics_do_not_change_the_authenticated_population() {
        let bytes = include_bytes!("official-corpus-metadata.json");
        let original = source_from_metadata(bytes).unwrap();
        let mut value: Value = serde_json::from_slice(bytes).unwrap();
        value["stats"] = json!({"downloads": 123456});
        let changed = source_from_metadata(&serde_json::to_vec(&value).unwrap()).unwrap();
        assert_eq!(original.archives, changed.archives);
        assert_ne!(
            original.record_metadata_sha256,
            changed.record_metadata_sha256
        );
        value["files"][0]["size"] = json!(1);
        assert!(source_from_metadata(&serde_json::to_vec(&value).unwrap()).is_err());
    }

    #[test]
    fn corpus_metadata_refuses_missing_extra_and_forged_archives() {
        let original: Value =
            serde_json::from_slice(include_bytes!("official-corpus-metadata.json")).unwrap();
        for operation in 0..4 {
            let mut value = original.clone();
            match operation {
                0 => {
                    value["files"].as_array_mut().unwrap().pop();
                }
                1 => {
                    let row = value["files"][0].clone();
                    value["files"].as_array_mut().unwrap().push(row);
                }
                2 => value["files"][0]["checksum"] = json!("md5:00000000000000000000000000000000"),
                _ => value["id"] = json!(1),
            }
            assert!(source_from_metadata(&serde_json::to_vec(&value).unwrap()).is_err());
        }
    }

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

    #[test]
    fn per_kind_coverage_cannot_close_on_empty_or_unresolved_population() {
        let mut coverage = QueryEvidenceCoverage {
            receipt_sha256: "0".repeat(64),
            queries: 2,
            sat: 1,
            sat_checked: 1,
            unsat: 1,
            unsat_checked: 1,
            unknown_or_missing: 0,
            shared_unknown: 0,
            invalid_or_regressed: 0,
        };
        assert!(coverage.sat_complete());
        assert!(coverage.unsat_complete());
        coverage.queries = 3;
        coverage.shared_unknown = 1;
        coverage.unknown_or_missing = 1;
        assert!(
            coverage.sat_complete(),
            "matching unknown has no SAT model obligation"
        );
        assert!(
            coverage.unsat_complete(),
            "matching unknown has no UNSAT proof obligation"
        );
        coverage.unknown_or_missing = 1;
        coverage.invalid_or_regressed = 1;
        assert!(!coverage.sat_complete());
        assert!(!coverage.unsat_complete());
        coverage.unknown_or_missing = 0;
        coverage.invalid_or_regressed = 0;
        coverage.sat = 0;
        coverage.sat_checked = 0;
        assert!(!coverage.sat_complete());
        coverage.unsat_checked = 0;
        assert!(!coverage.unsat_complete());
    }

    #[test]
    fn stronger_answers_need_independent_evidence_and_wrong_answers_never_pass() {
        let mut evidence = QueryEvidence::absent(Some(CorpusVerdict::Unsat));
        assert_eq!(
            query_outcome(
                Some(CorpusVerdict::Unknown),
                Some(CorpusVerdict::Unsat),
                &evidence
            ),
            QueryOutcome::Missing
        );
        evidence.status = EvidenceStatus::AcceptedUnsat;
        assert_eq!(
            query_outcome(
                Some(CorpusVerdict::Unknown),
                Some(CorpusVerdict::Unsat),
                &evidence
            ),
            QueryOutcome::Pass
        );
        assert_eq!(
            query_outcome(
                Some(CorpusVerdict::Sat),
                Some(CorpusVerdict::Unsat),
                &evidence
            ),
            QueryOutcome::Wrong
        );
        assert_eq!(
            query_outcome(
                Some(CorpusVerdict::Sat),
                Some(CorpusVerdict::Unknown),
                &evidence
            ),
            QueryOutcome::Missing
        );
        assert_eq!(
            query_outcome(
                Some(CorpusVerdict::Unknown),
                Some(CorpusVerdict::Unknown),
                &QueryEvidence::absent(Some(CorpusVerdict::Unknown))
            ),
            QueryOutcome::Pass
        );
    }

    #[test]
    fn unknown_query_cannot_retain_prior_decided_artifacts() {
        let file = query_file(b"(assert true)(check-sat)");
        let mut result = classify_file(
            &file,
            completed_process(CorpusVerdict::Unknown),
            completed_process(CorpusVerdict::Unknown),
        );
        result.queries[0].evidence.producer = Some(EvidenceTranscript {
            process: completed_process(CorpusVerdict::Unsat),
            stdout: "unsat\n".to_string(),
            stderr: String::new(),
        });
        let error = validate_query_evidence(
            &file.queries[0],
            &result.queries[0],
            &file,
            &[],
            Path::new("."),
            None,
        )
        .unwrap_err();
        assert!(error.contains("stale decided-artifact"));
    }
}
