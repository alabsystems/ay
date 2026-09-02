// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed, source-authenticated inventory of the Z3 5.1.0 CLI overlay.
//!
//! The full source tree is retained as bounded metadata, not as 2,756 copied
//! blobs.  Only the UTF-8 files that define the shell, SMT2 command registry,
//! and registry-generation mechanisms are retained verbatim.  Live registries
//! are read from the exact profile-pinned executable under the repository OOM
//! guard and are replayed on every non-structural audit.

use super::*;
use sha1::Sha1;

pub(super) const VALIDATOR_ID: &str = "builtin.z3-source-inventory.v1";
pub(super) const REFERENCE_VALIDATOR_ID: &str = "builtin.z3-reference-inventory.v1";

const SNAPSHOT_SCHEMA: &str = "ay-z3-source-metadata-snapshot/v1";
const SNAPSHOT_ID: &str = "z3-5.1.0-source-tree";
const SNAPSHOT_SELECTION: &str = "all 2,756 tracked files as path/git-blob/size metadata, the 43 UTF-8 C-API/shell/SMT2/registry/operator source blobs, and the pinned whole-tree registration-keyword scan over src and scripts";
const SNAPSHOT_DIGEST_KIND: &str = "sorted-path-git-blob-size-manifest/v1";
const MAX_SNAPSHOT_BYTES: u64 = 16 * 1024 * 1024;
const EXPECTED_TREE_FILES: usize = 2_756;
const EXPECTED_TREE_SHA256: &str =
    "df491d15649b581936f8422fbd704b0694831c160c01d1d339164c8a1441939b";
pub(super) const EXPECTED_OBSERVABLE_ITEMS: usize = 1_518;
pub(super) const EXPECTED_OBSERVABLE_SHA256: &str =
    "8a8d7ad916bca1530c39f7507adce5b4e7e279852d3c2de7c8802c9e85cace77";
const EXPECTED_PROCESS_CASES: usize = 8;
const REGISTRATION_SCAN_PATTERN: &str = r"tactic|probe|simplif|install_cmd|register_cmd|cmd_context|REG_PARAMS|gparams|parameter|IN_[A-Z_]+|is_option|strcmp\([^[:cntrl:]]*-|extension";
const EXPECTED_REGISTRATION_SCAN_LINES: usize = 12_681;
const EXPECTED_REGISTRATION_SCAN_SHA256: &str =
    "761e4140c263159e0e79589fa9f63ae0b19992a10b9eab1cfbfcd481cdb20bdb";
const EXPECTED_REGISTRATION_CLASSIFICATION_SHA256: &str =
    "4f31f4e821b78256a856d20e8f9209fe90d7dd287646dd6580c077c5f89815ed";
const EXPECTED_REGISTRATION_CLASSIFICATION_COUNTS: [(&str, usize); 16] = [
    ("nonobservable.build-metadata", 296),
    ("nonobservable.comment-or-documentation", 1_880),
    ("nonobservable.foreign-api-binding-or-implementation", 2_331),
    ("nonobservable.generator-or-maintenance-tool", 212),
    (
        "nonobservable.internal-declaration-or-schema-plumbing",
        1_911,
    ),
    ("nonobservable.internal-implementation-reference", 5_573),
    ("nonobservable.internal-test-only", 155),
    ("observable.cli-option-dispatch", 4),
    ("observable.command-registry-anchor", 30),
    ("observable.filename-extension-dispatch", 2),
    ("observable.input-mode-dispatch", 31),
    ("observable.parameter-module-registry-anchor", 2),
    ("observable.parameter-schema-anchor", 69),
    ("observable.probe-registration", 42),
    ("observable.simplifier-registration", 29),
    ("observable.tactic-registration", 114),
];

const SELECTED_SOURCE_PATHS: [&str; 43] = [
    "scripts/VERSION.txt",
    "scripts/mk_genfile_common.py",
    "scripts/mk_install_tactic_cpp.py",
    "src/api/z3_api.h",
    "src/api/z3_macros.h",
    "src/api/z3_replayer.cpp",
    "src/ast/arith_decl_plugin.cpp",
    "src/ast/array_decl_plugin.cpp",
    "src/ast/ast.cpp",
    "src/ast/bv_decl_plugin.cpp",
    "src/ast/char_decl_plugin.cpp",
    "src/ast/datatype_decl_plugin.cpp",
    "src/ast/dl_decl_plugin.cpp",
    "src/ast/finite_set_decl_plugin.cpp",
    "src/ast/fpa_decl_plugin.cpp",
    "src/ast/pb_decl_plugin.cpp",
    "src/ast/recfun_decl_plugin.cpp",
    "src/ast/seq_decl_plugin.cpp",
    "src/ast/special_relations_decl_plugin.cpp",
    "src/cmd_context/basic_cmds.cpp",
    "src/cmd_context/cmd_context.cpp",
    "src/cmd_context/eval_cmd.cpp",
    "src/cmd_context/extra_cmds/dbg_cmds.cpp",
    "src/cmd_context/extra_cmds/polynomial_cmds.cpp",
    "src/cmd_context/extra_cmds/proof_cmds.cpp",
    "src/cmd_context/extra_cmds/subpaving_cmds.cpp",
    "src/cmd_context/simplifier_cmds.cpp",
    "src/cmd_context/simplify_cmd.cpp",
    "src/cmd_context/tactic_cmds.cpp",
    "src/muz/fp/dl_cmds.cpp",
    "src/opt/opt_cmds.cpp",
    "src/parsers/smt2/smt2parser.cpp",
    "src/sat/dimacs.cpp",
    "src/shell/drat_frontend.cpp",
    "src/shell/main.cpp",
    "src/shell/smtlib_frontend.cpp",
    "src/shell/z3_log_frontend.cpp",
    "src/smt/smt2_extra_cmds.cpp",
    "src/smt/smt_setup.cpp",
    "src/solver/smt_logics.cpp",
    "src/solver/smt_logics.h",
    "src/util/gparams.cpp",
    "src/util/z3_version.h.in",
];

const EXTENSION_MODES: [(&str, &str); 16] = [
    ("cnf", "IN_DIMACS"),
    ("datalog", "IN_DATALOG"),
    ("dimacs", "IN_DIMACS"),
    ("dl", "IN_DATALOG"),
    ("drat", "IN_DRAT"),
    ("fof", "IN_TPTP"),
    ("lp", "IN_LP"),
    ("log", "IN_Z3_LOG"),
    ("opb", "IN_OPB"),
    ("p", "IN_TPTP"),
    ("smt", "IN_SMTLIB_2"),
    ("smt2", "IN_SMTLIB_2"),
    ("tff", "IN_TPTP"),
    ("thf", "IN_TPTP"),
    ("tptp", "IN_TPTP"),
    ("wcnf", "IN_WCNF"),
];

const CATEGORY_COUNTS: [(&str, usize); 17] = [
    ("cli-help-option", 27),
    ("cli-option", 33),
    ("declaration-builtin", 323),
    ("filename-extension", 16),
    ("global-parameter", 25),
    ("input-mode", 9),
    ("logic-recognizer-literal", 24),
    ("logic-strategy-alias", 33),
    ("module-parameter", 663),
    ("parameter-module", 22),
    ("probe", 42),
    ("simplifier", 36),
    ("smt-command", 94),
    ("smt-info-key", 11),
    ("smt-option-key", 20),
    ("smt-parser-token", 22),
    ("tactic", 118),
];

const DECLARATION_PLUGIN_PATHS: [&str; 13] = [
    "src/ast/arith_decl_plugin.cpp",
    "src/ast/array_decl_plugin.cpp",
    "src/ast/ast.cpp",
    "src/ast/bv_decl_plugin.cpp",
    "src/ast/char_decl_plugin.cpp",
    "src/ast/datatype_decl_plugin.cpp",
    "src/ast/dl_decl_plugin.cpp",
    "src/ast/finite_set_decl_plugin.cpp",
    "src/ast/fpa_decl_plugin.cpp",
    "src/ast/pb_decl_plugin.cpp",
    "src/ast/recfun_decl_plugin.cpp",
    "src/ast/seq_decl_plugin.cpp",
    "src/ast/special_relations_decl_plugin.cpp",
];

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Z3SourceSnapshot {
    schema: String,
    profile_id: String,
    source: Z3SnapshotSource,
    tree: Vec<Z3TreeEntry>,
    selected_files: Vec<Z3SelectedFile>,
    registration_scan: Z3RegistrationScan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Z3SnapshotSource {
    id: String,
    cohort: SourceCohort,
    repository: String,
    tag: String,
    revision: String,
    selection: String,
    item_count: usize,
    digest_kind: String,
    selection_sha256: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Z3TreeEntry {
    path: String,
    git_blob: String,
    size: usize,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Z3SelectedFile {
    path: String,
    git_blob: String,
    size: usize,
    content_sha256: String,
    content: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Z3RegistrationScan {
    pattern: String,
    scopes: Vec<String>,
    line_count: usize,
    content_sha256: String,
    content: String,
}

#[derive(Debug, Eq, PartialEq)]
struct RegistrationClassificationSummary {
    counts: BTreeMap<&'static str, usize>,
    content_sha256: String,
}

impl RegistrationClassificationSummary {
    fn counts_text(&self) -> String {
        self.counts
            .iter()
            .map(|(disposition, count)| format!("{disposition}={count}"))
            .collect::<Vec<_>>()
            .join(",")
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ObservableItem {
    pub(super) category: String,
    pub(super) name: String,
    pub(super) detail: String,
}

impl ObservableItem {
    pub(super) fn canonical_line(&self) -> String {
        format!("{}\t{}\t{}\n", self.category, self.name, self.detail)
    }
}

pub(super) struct ObservableTranscripts<'a> {
    pub(super) cli_help: &'a str,
    pub(super) command_help: &'a str,
    pub(super) tactics: &'a str,
    pub(super) probes: &'a str,
    pub(super) simplifiers: &'a str,
    pub(super) parameters: &'a str,
    pub(super) parameter_descriptions: &'a str,
}

#[derive(Debug)]
struct LiveCapture {
    id: &'static str,
    invocation: String,
    input: Vec<u8>,
    stdout: String,
    stderr: String,
    exit_code: Option<i32>,
    process: ProcessObservation,
    outcome: ValidatorCaseOutcome,
}

impl LiveCapture {
    fn require_pass(&self) -> Result<(), String> {
        if self.outcome != ValidatorCaseOutcome::Pass {
            return Err(format!(
                "pinned Z3 registry process {} did not complete cleanly: {:?}",
                self.id, self.outcome
            ));
        }
        Ok(())
    }

    fn into_case(self) -> ValidatorCase {
        let input_sha256 = invocation_sha256(&self.invocation, &self.input);
        ValidatorCase {
            id: format!("live.{}", self.id),
            input_sha256,
            expected: format!(
                "authenticated Z3 5.1.0 invocation {:?} exits 0 with complete UTF-8 stdout and empty stderr",
                self.invocation
            ),
            observed: format!(
                "status={:?};stdin-complete={};timeout={};memout={};stdout-truncated={};stderr-truncated={};stderr-empty={}",
                self.exit_code,
                self.process.stdin_complete,
                self.process.timed_out,
                self.process.memout,
                self.process.stdout_truncated,
                self.process.stderr_truncated,
                self.stderr.is_empty()
            ),
            stdout: Some(self.stdout),
            stderr: Some(self.stderr),
            exit_code: self.exit_code,
            process: Some(self.process),
            outcome: self.outcome,
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Execution {
    z3_sha256: String,
    resource_envelope: String,
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

pub(super) fn snapshot(args: &[String]) -> Result<i32, String> {
    let mut checkout: Option<PathBuf> = None;
    let mut output: Option<PathBuf> = None;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--out" => {
                index += 1;
                output = Some(PathBuf::from(args.get(index).ok_or("--out needs a path")?));
            }
            flag if flag.starts_with("--") => {
                return Err(format!("unknown z3-source-snapshot flag {flag:?}"));
            }
            value => {
                if checkout.replace(PathBuf::from(value)).is_some() {
                    return Err("z3-source-snapshot takes exactly one checkout".to_string());
                }
            }
        }
        index += 1;
    }
    let checkout = checkout.ok_or("z3-source-snapshot needs a Git checkout")?;
    let output = output.ok_or("z3-source-snapshot requires --out <path>")?;
    let snapshot = create_snapshot(&checkout, &canonical_profile())?;
    let bytes = pretty_json(&snapshot)?;
    atomic_write_new(&output, &bytes)?;
    println!(
        "z3-source-snapshot={} tree-files={} selected-files={} tree-sha256={} snapshot-sha256={} path={}",
        SNAPSHOT_ID,
        snapshot.tree.len(),
        snapshot.selected_files.len(),
        snapshot.source.selection_sha256,
        sha256_bytes(&bytes),
        output.display()
    );
    Ok(0)
}

/// Extract the four closed overlay requirement rows from the authenticated
/// Z3 source snapshot.  This is deliberately separate from [`run`]: a source
/// inventory defines the row universe, while the differential validator below
/// establishes behavior for one of those rows.  Treating the latter as its own
/// reference authority would be circular.
pub(super) fn run_reference(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut snapshot_path: Option<PathBuf> = None;
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
            flag if flag.starts_with("--") => {
                return Err(format!("unknown z3-reference-inventory flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("z3-reference-inventory takes exactly one manifest".to_string());
                }
            }
        }
        index += 1;
    }

    let manifest = manifest.ok_or("z3-reference-inventory needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("z3-reference-inventory requires --receipt <path>")?;
    let snapshot_path = snapshot_path.ok_or(
        "z3-reference-inventory requires --source-snapshot <path> from z3-source-snapshot",
    )?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let dimension = overlay_dimension(&loaded.contract)?;
    if dimension.inventory.granularity != InventoryGranularity::ItemLevel {
        return Err("overlay inventory must be item-level before extraction".to_string());
    }
    let loaded_source = load_snapshot_for_run(&loaded.contract, &loaded.base, &snapshot_path)?;
    let case_results = reference_inventory_cases(&loaded_source.snapshot)?;
    let cases = case_counts_from_rows(&case_results)?;
    let output_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: dimension.id.clone(),
        requirement_ids: dimension
            .requirements
            .iter()
            .map(|requirement| requirement.id.clone())
            .collect(),
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: REFERENCE_VALIDATOR_ID.to_string(),
            kind: ValidatorKind::ReferenceExtractor,
            path: current_exe.to_string_lossy().into_owned(),
            sha256: sha256_file(&current_exe, "parity validator")?,
        },
        subject: ReceiptSubject {
            ay_executable_sha256: None,
            ay_shared_library_sha256: None,
        },
        z3_binary_sha256: None,
        z3_shared_library_sha256: None,
        reference_inputs: vec![loaded_source.binding],
        auxiliary_tools: Vec::new(),
        source_provenance: None,
        resource_envelope: None,
        exhaustive: true,
        result: overall_validator_result(&case_results),
        cases,
        case_results,
    };
    let bytes = pretty_json(&receipt)?;
    atomic_write_new(&receipt_path, &bytes)?;
    let receipt_sha = sha256_bytes(&bytes);
    println!(
        "z3-reference-inventory={} rows={} receipt={} sha256={}",
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        receipt.cases.total,
        output_relative,
        receipt_sha
    );
    println!(
        "attach to overlay.z3-5.1.0 inventory: {{\"path\":\"{output_relative}\",\"sha256\":\"{receipt_sha}\"}}"
    );
    if !report.complete {
        println!(
            "note: the rest of the contract remains incomplete ({} existing blockers)",
            report.blockers.len()
        );
    }
    Ok(i32::from(receipt.result != ValidatorResult::Pass))
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut snapshot_path: Option<PathBuf> = None;
    let mut timeout_secs = 20u64;
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
            "--timeout" => {
                index += 1;
                timeout_secs = args
                    .get(index)
                    .ok_or("--timeout needs seconds")?
                    .parse()
                    .map_err(|_| "--timeout must be a positive integer")?;
                if timeout_secs == 0 || timeout_secs > 3_600 {
                    return Err("--timeout must be between 1 and 3600 seconds".to_string());
                }
            }
            flag if flag.starts_with("--") => {
                return Err(format!("unknown z3-source-inventory flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("z3-source-inventory takes exactly one manifest".to_string());
                }
            }
        }
        index += 1;
    }

    let manifest = manifest.ok_or("z3-source-inventory needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("z3-source-inventory requires --receipt <path>")?;
    let snapshot_path = snapshot_path
        .ok_or("z3-source-inventory requires --source-snapshot <path> from z3-source-snapshot")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let dimension = overlay_dimension(&loaded.contract)?;
    let loaded_source = load_snapshot_for_run(&loaded.contract, &loaded.base, &snapshot_path)?;
    let execution = execute(
        &loaded.contract,
        &loaded_source.snapshot,
        Duration::from_secs(timeout_secs),
        None,
    )?;
    let output_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: dimension.id.clone(),
        requirement_ids: vec!["overlay.z3-5.1.0.source-inventory".to_string()],
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: VALIDATOR_ID.to_string(),
            kind: ValidatorKind::Z3Differential,
            path: current_exe.to_string_lossy().into_owned(),
            sha256: sha256_file(&current_exe, "parity validator")?,
        },
        subject: ReceiptSubject {
            ay_executable_sha256: None,
            ay_shared_library_sha256: None,
        },
        z3_binary_sha256: Some(execution.z3_sha256),
        z3_shared_library_sha256: None,
        reference_inputs: vec![loaded_source.binding],
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
        "z3-source-inventory={} source-files={} commands=94 tactics=118 probes=42 simplifiers=36 parameters=688 observable-items={} receipt={} sha256={}",
        if receipt.result == ValidatorResult::Pass { "PASS" } else { "FAIL" },
        EXPECTED_TREE_FILES,
        EXPECTED_OBSERVABLE_ITEMS,
        output_relative,
        receipt_sha
    );
    println!(
        "attach to overlay.z3-5.1.0.source-inventory: {{\"path\":\"{output_relative}\",\"sha256\":\"{receipt_sha}\"}}"
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
    if receipt.validator.kind != ValidatorKind::Z3Differential
        || context.dimension.id != "overlay.z3-5.1.0"
        || receipt.requirement_ids != ["overlay.z3-5.1.0.source-inventory".to_string()]
        || !receipt.exhaustive
        || receipt.subject.ay_executable_sha256.is_some()
        || receipt.subject.ay_shared_library_sha256.is_some()
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
    {
        return Err(format!(
            "{VALIDATOR_ID} has invalid kind, dimension, coverage, or inventory-only bindings"
        ));
    }
    let [input] = receipt.reference_inputs.as_slice() else {
        return Err(format!(
            "{VALIDATOR_ID} requires exactly one authenticated Z3 source snapshot"
        ));
    };
    if input.id != SNAPSHOT_ID || input.cohort != SourceCohort::Z3Source {
        return Err(format!("{VALIDATOR_ID} has a foreign source snapshot"));
    }
    let expected_cases = EXPECTED_TREE_FILES
        + SELECTED_SOURCE_PATHS.len()
        + 1
        + EXPECTED_OBSERVABLE_ITEMS
        + EXPECTED_PROCESS_CASES;
    if receipt.case_results.len() != expected_cases {
        return Err(format!(
            "{VALIDATOR_ID} detailed inventory is not exact: expected {expected_cases}, got {}",
            receipt.case_results.len()
        ));
    }
    if context.mode.replays_registered_validators() {
        let snapshot = load_bound_snapshot(input, context.manifest_dir, &canonical_profile())?;
        let envelope = receipt
            .resource_envelope
            .as_deref()
            .ok_or("Z3 source inventory receipt has no resource envelope")?;
        let parsed = parse_resource_envelope(envelope)?;
        if parsed.jobs != 1 {
            return Err("Z3 source inventory requires a one-job resource envelope".to_string());
        }
        let live = execute(context.contract, &snapshot, parsed.timeout, Some(envelope))?;
        if receipt.result != live.result
            || receipt.cases != live.cases
            || receipt.case_results != live.case_results
        {
            return Err(format!(
                "{VALIDATOR_ID} receipt does not match a fresh authenticated source and live-registry replay"
            ));
        }
    }
    Ok(())
}

pub(super) fn validate_reference_and_replay(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    let expected_ids = context
        .dimension
        .requirements
        .iter()
        .map(|requirement| requirement.id.clone())
        .collect::<Vec<_>>();
    if receipt.validator.kind != ValidatorKind::ReferenceExtractor
        || context.dimension.id != "overlay.z3-5.1.0"
        || receipt.requirement_ids != expected_ids
        || !receipt.exhaustive
        || receipt.subject.ay_executable_sha256.is_some()
        || receipt.subject.ay_shared_library_sha256.is_some()
        || receipt.z3_binary_sha256.is_some()
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
        || receipt.resource_envelope.is_some()
    {
        return Err(format!(
            "{REFERENCE_VALIDATOR_ID} has invalid kind, dimension, coverage, or reference-only bindings"
        ));
    }
    let [input] = receipt.reference_inputs.as_slice() else {
        return Err(format!(
            "{REFERENCE_VALIDATOR_ID} requires exactly one authenticated Z3 source snapshot"
        ));
    };
    if input.id != SNAPSHOT_ID || input.cohort != SourceCohort::Z3Source {
        return Err(format!(
            "{REFERENCE_VALIDATOR_ID} has a foreign source snapshot"
        ));
    }
    let snapshot = load_bound_snapshot(input, context.manifest_dir, &canonical_profile())?;
    let expected = reference_inventory_cases(&snapshot)?;
    if receipt.result != ValidatorResult::Pass
        || receipt.case_results != expected
        || receipt.cases != case_counts_from_rows(&expected)?
    {
        return Err(format!(
            "{REFERENCE_VALIDATOR_ID} receipt does not match the authenticated Z3 source inventory"
        ));
    }
    Ok(())
}

pub(super) struct LoadedSnapshot {
    pub(super) binding: ReferenceInput,
    pub(super) snapshot: Z3SourceSnapshot,
}

fn overlay_dimension(contract: &Contract) -> Result<&Dimension, String> {
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == "overlay.z3-5.1.0")
        .ok_or("closed Z3 overlay dimension is missing".to_string())
}

fn create_snapshot(checkout: &Path, profile: &Profile) -> Result<Z3SourceSnapshot, String> {
    let checkout = fs::canonicalize(checkout).map_err(|error| {
        format!(
            "canonicalizing Z3 source checkout {}: {error}",
            checkout.display()
        )
    })?;
    let target = &profile.z3_overlay;
    let head = git_text(&checkout, &["rev-parse", "HEAD"], "Z3 source HEAD")?;
    if head.trim() != target.source_commit {
        return Err(format!(
            "Z3 checkout HEAD is {}, expected {}",
            head.trim(),
            target.source_commit
        ));
    }
    let tag_object = format!("{}^{{commit}}", target.source_tag);
    let tag = git_text(&checkout, &["rev-parse", &tag_object], "Z3 source tag")?;
    if tag.trim() != target.source_commit {
        return Err(format!(
            "Z3 tag {} resolves to {}, expected {}",
            target.source_tag,
            tag.trim(),
            target.source_commit
        ));
    }
    let dirty = git_bytes(
        &checkout,
        &["status", "--porcelain", "--untracked-files=no"],
        "Z3 tracked worktree status",
    )?;
    if !dirty.is_empty() {
        return Err("Z3 source checkout has modified tracked files".to_string());
    }
    let tree_bytes = git_bytes(
        &checkout,
        &["ls-tree", "-r", "-l", "-z", &target.source_commit],
        "Z3 source tree",
    )?;
    let tree = parse_tree(&tree_bytes)?;
    let tree_sha256 = tree_manifest_sha256(&tree);
    if tree.len() != EXPECTED_TREE_FILES || tree_sha256 != EXPECTED_TREE_SHA256 {
        return Err(format!(
            "Z3 source tree mismatch: count={}/{} sha256={}/{}",
            tree.len(),
            EXPECTED_TREE_FILES,
            tree_sha256,
            EXPECTED_TREE_SHA256
        ));
    }

    let by_path = tree
        .iter()
        .map(|entry| (entry.path.as_str(), entry))
        .collect::<BTreeMap<_, _>>();
    let mut selected_files = Vec::with_capacity(SELECTED_SOURCE_PATHS.len());
    for path in SELECTED_SOURCE_PATHS {
        let entry = by_path
            .get(path)
            .ok_or_else(|| format!("pinned Z3 source tree is missing selected file {path}"))?;
        let object = format!("{}:{path}", target.source_commit);
        let bytes = git_bytes(&checkout, &["show", &object], "selected Z3 source blob")?;
        if bytes.len() != entry.size || git_blob_sha1(&bytes) != entry.git_blob {
            return Err(format!(
                "selected Z3 source blob {path} does not match its tree entry"
            ));
        }
        let content = String::from_utf8(bytes)
            .map_err(|_| format!("selected Z3 source {path} is not UTF-8"))?;
        selected_files.push(Z3SelectedFile {
            path: path.to_string(),
            git_blob: entry.git_blob.clone(),
            size: entry.size,
            content_sha256: sha256_bytes(content.as_bytes()),
            content,
        });
    }
    // Search the complete pinned `src` + `scripts` source population, not only
    // the retained registry-owner files.  The deliberately broad vocabulary
    // captures registration mechanisms and their nearby declarations.  The
    // exact output digest is profile data; adding or moving any candidate site
    // forces an explicit inventory update instead of silently escaping the 23
    // selected-file extractor.
    let registration_scan_bytes = git_bytes(
        &checkout,
        &[
            "grep",
            "-n",
            "-I",
            "-E",
            REGISTRATION_SCAN_PATTERN,
            &target.source_commit,
            "--",
            "src",
            "scripts",
        ],
        "whole-tree Z3 registration scan",
    )?;
    let registration_scan_content = String::from_utf8(registration_scan_bytes)
        .map_err(|_| "whole-tree Z3 registration scan is not UTF-8".to_string())?;
    let registration_scan = Z3RegistrationScan {
        pattern: REGISTRATION_SCAN_PATTERN.to_string(),
        scopes: vec!["src".to_string(), "scripts".to_string()],
        line_count: registration_scan_content.lines().count(),
        content_sha256: sha256_bytes(registration_scan_content.as_bytes()),
        content: registration_scan_content,
    };
    let snapshot = Z3SourceSnapshot {
        schema: SNAPSHOT_SCHEMA.to_string(),
        profile_id: PROFILE_ID.to_string(),
        source: expected_snapshot_source(profile),
        tree,
        selected_files,
        registration_scan,
    };
    validate_snapshot(&snapshot, profile)?;
    Ok(snapshot)
}

fn expected_snapshot_source(profile: &Profile) -> Z3SnapshotSource {
    let target = &profile.z3_overlay;
    Z3SnapshotSource {
        id: SNAPSHOT_ID.to_string(),
        cohort: SourceCohort::Z3Source,
        repository: target.source_repository.clone(),
        tag: target.source_tag.clone(),
        revision: target.source_commit.clone(),
        selection: SNAPSHOT_SELECTION.to_string(),
        item_count: EXPECTED_TREE_FILES,
        digest_kind: target.tracked_source_tree_digest_kind.clone(),
        selection_sha256: EXPECTED_TREE_SHA256.to_string(),
    }
}

fn validate_snapshot(snapshot: &Z3SourceSnapshot, profile: &Profile) -> Result<(), String> {
    if profile.z3_overlay.tracked_source_tree_digest_kind != SNAPSHOT_DIGEST_KIND {
        return Err("Z3 profile source-tree digest algorithm is not canonical".to_string());
    }
    if snapshot.schema != SNAPSHOT_SCHEMA || snapshot.profile_id != PROFILE_ID {
        return Err("Z3 source snapshot schema or profile mismatch".to_string());
    }
    if snapshot.source != expected_snapshot_source(profile) {
        return Err("Z3 source snapshot metadata differs from the immutable profile".to_string());
    }
    if snapshot.tree.len() != EXPECTED_TREE_FILES {
        return Err(format!(
            "Z3 source snapshot has {} tree entries, expected {EXPECTED_TREE_FILES}",
            snapshot.tree.len()
        ));
    }
    let mut previous: Option<&str> = None;
    for entry in &snapshot.tree {
        validate_relative_path(&entry.path, "Z3 source tree path")?;
        if previous.is_some_and(|prior| prior >= entry.path.as_str()) {
            return Err("Z3 source tree must be sorted and duplicate-free".to_string());
        }
        previous = Some(&entry.path);
        validate_git_object_id(&entry.git_blob)?;
    }
    if tree_manifest_sha256(&snapshot.tree) != EXPECTED_TREE_SHA256 {
        return Err("Z3 source snapshot tree-manifest digest mismatch".to_string());
    }
    if snapshot.selected_files.len() != SELECTED_SOURCE_PATHS.len() {
        return Err("Z3 source snapshot selected-file count mismatch".to_string());
    }
    let by_path = snapshot
        .tree
        .iter()
        .map(|entry| (entry.path.as_str(), entry))
        .collect::<BTreeMap<_, _>>();
    for (file, expected_path) in snapshot.selected_files.iter().zip(SELECTED_SOURCE_PATHS) {
        if file.path != expected_path {
            return Err("Z3 source snapshot selected paths are not exact and sorted".to_string());
        }
        let entry = by_path
            .get(file.path.as_str())
            .ok_or_else(|| format!("selected file {} is absent from full tree", file.path))?;
        if file.git_blob != entry.git_blob
            || file.size != entry.size
            || file.content.len() != file.size
            || file.content_sha256 != sha256_bytes(file.content.as_bytes())
            || file.git_blob != git_blob_sha1(file.content.as_bytes())
        {
            return Err(format!(
                "selected Z3 source {} content or object binding mismatch",
                file.path
            ));
        }
    }
    let scan = &snapshot.registration_scan;
    if scan.pattern != REGISTRATION_SCAN_PATTERN
        || scan.scopes != ["src".to_string(), "scripts".to_string()]
        || scan.line_count != EXPECTED_REGISTRATION_SCAN_LINES
        || scan.content.lines().count() != EXPECTED_REGISTRATION_SCAN_LINES
        || scan.content_sha256 != EXPECTED_REGISTRATION_SCAN_SHA256
        || sha256_bytes(scan.content.as_bytes()) != EXPECTED_REGISTRATION_SCAN_SHA256
    {
        return Err(format!(
            "Z3 whole-tree registration scan mismatch: lines={}/{EXPECTED_REGISTRATION_SCAN_LINES} sha256={}/{EXPECTED_REGISTRATION_SCAN_SHA256}",
            scan.line_count, scan.content_sha256
        ));
    }
    let expected_prefix = format!("{}:", profile.z3_overlay.source_commit);
    for line in scan.content.lines() {
        let rest = line
            .strip_prefix(&expected_prefix)
            .ok_or("Z3 registration scan row is not commit-bound")?;
        let mut fields = rest.splitn(3, ':');
        let path = fields
            .next()
            .ok_or("Z3 registration scan row has no path")?;
        let line_number = fields
            .next()
            .ok_or("Z3 registration scan row has no line number")?;
        let text = fields
            .next()
            .ok_or("Z3 registration scan row has no source text")?;
        if !(path.starts_with("src/") || path.starts_with("scripts/"))
            || !by_path.contains_key(path)
            || line_number
                .parse::<usize>()
                .ok()
                .is_none_or(|line| line == 0)
            || text.is_empty()
        {
            return Err(format!(
                "invalid Z3 registration scan source mapping {path:?}:{line_number:?}"
            ));
        }
    }
    let classification = classify_registration_scan(scan, profile)?;
    let expected_counts = EXPECTED_REGISTRATION_CLASSIFICATION_COUNTS
        .into_iter()
        .collect::<BTreeMap<_, _>>();
    if classification.counts != expected_counts
        || classification.content_sha256 != EXPECTED_REGISTRATION_CLASSIFICATION_SHA256
    {
        return Err(format!(
            "Z3 registration scan classification drifted: counts={:?}/{expected_counts:?} sha256={}/{EXPECTED_REGISTRATION_CLASSIFICATION_SHA256}",
            classification.counts, classification.content_sha256
        ));
    }
    Ok(())
}

fn parse_registration_scan_row<'a>(
    line: &'a str,
    expected_prefix: &str,
) -> Result<(&'a str, usize, &'a str), String> {
    let rest = line
        .strip_prefix(expected_prefix)
        .ok_or("Z3 registration scan row is not commit-bound")?;
    let mut fields = rest.splitn(3, ':');
    let path = fields
        .next()
        .ok_or("Z3 registration scan row has no path")?;
    let line_number = fields
        .next()
        .ok_or("Z3 registration scan row has no line number")?
        .parse::<usize>()
        .ok()
        .filter(|line_number| *line_number > 0)
        .ok_or("Z3 registration scan row has an invalid line number")?;
    let text = fields
        .next()
        .filter(|text| !text.is_empty())
        .ok_or("Z3 registration scan row has no source text")?;
    Ok((path, line_number, text))
}

fn contains_uppercase_input_token(text: &str) -> bool {
    text.match_indices("IN_").any(|(offset, _)| {
        text.as_bytes()
            .get(offset + 3)
            .is_some_and(|byte| byte.is_ascii_uppercase() || *byte == b'_')
    })
}

fn has_registration_scan_lexeme(text: &str) -> bool {
    text.contains("tactic")
        || text.contains("probe")
        || text.contains("simplif")
        || text.contains("install_cmd")
        || text.contains("register_cmd")
        || text.contains("cmd_context")
        || text.contains("REG_PARAMS")
        || text.contains("gparams")
        || text.contains("parameter")
        || contains_uppercase_input_token(text)
        || text.contains("is_option")
        || (text.contains("strcmp(") && text.contains('-'))
        || text.contains("extension")
}

fn known_registration_path(path: &str) -> bool {
    if path.starts_with("scripts/") {
        return true;
    }
    let Some(rest) = path.strip_prefix("src/") else {
        return false;
    };
    let component = rest.split('/').next().unwrap_or_default();
    matches!(
        component,
        "CMakeLists.txt"
            | "ackermannization"
            | "api"
            | "ast"
            | "cmd_context"
            | "math"
            | "model"
            | "muz"
            | "nlsat"
            | "opt"
            | "params"
            | "parsers"
            | "qe"
            | "sat"
            | "shell"
            | "smt"
            | "solver"
            | "tactic"
            | "test"
            | "util"
    )
}

fn known_registration_extension(path: &str) -> bool {
    let extension = path.rsplit_once('.').map_or("", |(_, extension)| extension);
    matches!(
        extension,
        "cpp"
            | "h"
            | "py"
            | "ts"
            | "txt"
            | "cs"
            | "java"
            | "mli"
            | "go"
            | "ml"
            | "md"
            | "def"
            | "pyg"
            | "yml"
            | "d"
            | "pre"
            | "disabled"
            | "in"
    )
}

fn registration_disposition(path: &str, text: &str) -> Result<&'static str, String> {
    if !known_registration_path(path) || !known_registration_extension(path) {
        return Err(format!(
            "unclassified Z3 registration scan path class {path:?}"
        ));
    }
    if !has_registration_scan_lexeme(text) {
        return Err(format!(
            "Z3 registration scan row has no classified scan lexeme: {path:?}: {text:?}"
        ));
    }
    let trimmed = text.trim_start();
    if trimmed.starts_with("//")
        || trimmed.starts_with("/*")
        || trimmed.starts_with('*')
        || trimmed.starts_with('#')
    {
        return Ok("nonobservable.comment-or-documentation");
    }
    if path.starts_with("scripts/") {
        return Ok("nonobservable.generator-or-maintenance-tool");
    }
    if path.starts_with("src/api/") {
        return Ok("nonobservable.foreign-api-binding-or-implementation");
    }
    if path.starts_with("src/test/") {
        return Ok("nonobservable.internal-test-only");
    }
    if path.ends_with("CMakeLists.txt")
        || Path::new(path)
            .extension()
            .is_some_and(|extension| extension.eq_ignore_ascii_case("yml"))
    {
        return Ok("nonobservable.build-metadata");
    }
    if text.contains("ADD_TACTIC(\"") {
        return Ok("observable.tactic-registration");
    }
    if text.contains("ADD_PROBE(\"") {
        return Ok("observable.probe-registration");
    }
    if text.contains("ADD_SIMPLIFIER(\"") {
        return Ok("observable.simplifier-registration");
    }
    if path == "src/shell/main.cpp" && text.contains("strcmp(opt_name, \"") {
        return Ok("observable.cli-option-dispatch");
    }
    if path == "src/shell/main.cpp"
        && (text.contains("strcmp(ext, \"") || text.contains("is_tptp_extension"))
    {
        return Ok("observable.filename-extension-dispatch");
    }
    if path == "src/shell/main.cpp" && contains_uppercase_input_token(text) {
        return Ok("observable.input-mode-dispatch");
    }
    if path.starts_with("src/params/") || text.contains("REG_PARAMS(") {
        return Ok("observable.parameter-schema-anchor");
    }
    if path == "src/util/gparams.cpp" && text.contains("gparams::register_module") {
        return Ok("observable.parameter-module-registry-anchor");
    }
    let command_owner_path = path.starts_with("src/cmd_context/")
        || path == "src/opt/opt_cmds.cpp"
        || path == "src/muz/fp/dl_cmds.cpp"
        || path == "src/smt/smt2_extra_cmds.cpp";
    if command_owner_path
        && text.contains("install_")
        && (text.contains("cmd") || text.contains("command"))
    {
        return Ok("observable.command-registry-anchor");
    }
    if Path::new(path).extension().is_some_and(|extension| {
        ["h", "def", "pyg", "in"]
            .iter()
            .any(|candidate| extension.eq_ignore_ascii_case(candidate))
    }) {
        return Ok("nonobservable.internal-declaration-or-schema-plumbing");
    }
    Ok("nonobservable.internal-implementation-reference")
}

fn classify_registration_scan(
    scan: &Z3RegistrationScan,
    profile: &Profile,
) -> Result<RegistrationClassificationSummary, String> {
    let prefix = format!("{}:", profile.z3_overlay.source_commit);
    let mut counts = BTreeMap::<&'static str, usize>::new();
    let mut hasher = Sha256::new();
    let mut classified = 0usize;
    for line in scan.content.lines() {
        let (path, line_number, text) = parse_registration_scan_row(line, &prefix)?;
        let disposition = registration_disposition(path, text)?;
        *counts.entry(disposition).or_default() += 1;
        hasher.update(path.as_bytes());
        hasher.update(b"\t");
        hasher.update(line_number.to_string().as_bytes());
        hasher.update(b"\t");
        hasher.update(disposition.as_bytes());
        hasher.update(b"\n");
        classified += 1;
    }
    if classified != scan.line_count {
        return Err(format!(
            "Z3 registration classifier assigned {classified} rows for {} scan rows",
            scan.line_count
        ));
    }
    Ok(RegistrationClassificationSummary {
        counts,
        content_sha256: format!("{:x}", hasher.finalize()),
    })
}

pub(super) fn load_snapshot_for_run(
    contract: &Contract,
    base: &Path,
    path: &Path,
) -> Result<LoadedSnapshot, String> {
    let relative = existing_relative_file(base, path, "Z3 source snapshot")?;
    let resolved = resolve_relative_evidence_path(base, &relative)?;
    let bytes = read_bounded_bytes(&resolved, MAX_SNAPSHOT_BYTES, "Z3 source snapshot", true)?;
    let snapshot: Z3SourceSnapshot = serde_json::from_slice(&bytes)
        .map_err(|error| format!("invalid Z3 source snapshot JSON: {error}"))?;
    validate_snapshot(&snapshot, &contract.profile)?;
    Ok(LoadedSnapshot {
        binding: snapshot_binding(&snapshot, relative, sha256_bytes(&bytes)),
        snapshot,
    })
}

pub(super) fn load_bound_snapshot(
    input: &ReferenceInput,
    base: &Path,
    profile: &Profile,
) -> Result<Z3SourceSnapshot, String> {
    let path = resolve_relative_evidence_path(base, &input.snapshot.path)?;
    let bytes = read_bounded_bytes(&path, MAX_SNAPSHOT_BYTES, "Z3 source snapshot", true)?;
    if sha256_bytes(&bytes) != input.snapshot.sha256 {
        return Err("Z3 source snapshot hash changed during replay".to_string());
    }
    let snapshot: Z3SourceSnapshot = serde_json::from_slice(&bytes)
        .map_err(|error| format!("invalid Z3 source snapshot JSON: {error}"))?;
    validate_snapshot(&snapshot, profile)?;
    let rebound = snapshot_binding(&snapshot, input.snapshot.path.clone(), sha256_bytes(&bytes));
    if &rebound != input {
        return Err("Z3 source snapshot receipt metadata does not match its bytes".to_string());
    }
    Ok(snapshot)
}

fn snapshot_binding(snapshot: &Z3SourceSnapshot, path: String, sha256: String) -> ReferenceInput {
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

fn execute(
    contract: &Contract,
    snapshot: &Z3SourceSnapshot,
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<Execution, String> {
    if timeout.is_zero() || timeout > Duration::from_hours(1) {
        return Err("Z3 source-inventory timeout must be between 1ns and 3600 seconds".to_string());
    }
    validate_snapshot(snapshot, &contract.profile)?;
    let target = &contract.profile.z3_overlay;
    let source_z3 = PathBuf::from(&target.reference_executable.path);
    let staged_z3 = stage_authenticated_executable(
        &source_z3,
        &target.reference_executable.sha256,
        "Z3 5.1.0 executable",
    )?;
    let repo_root = locate_repo_root()?;
    let resources = PlannedResources::plan(
        &repo_root,
        1,
        "ay-z3-parity smtlib-conformance z3-source-inventory",
    )
    .map_err(|error| error.to_string())?;
    let resource_envelope = effective_execution_envelope(
        &resources.plan,
        ENFORCEMENT_RSS_WATCHDOG_V1,
        timeout.as_secs_f64(),
    )
    .map_err(|error| error.to_string())?;
    if required_envelope.is_some_and(|expected| expected != resource_envelope) {
        return Err(format!(
            "live Z3 source-inventory resource envelope drift: expected {required_envelope:?}, got {resource_envelope:?}"
        ));
    }

    let mut captures = Vec::with_capacity(EXPECTED_PROCESS_CASES);
    captures.push(run_capture(
        &resources,
        &staged_z3.path,
        "version",
        &["-version"],
        b"",
        timeout,
    )?);
    captures.push(run_capture(
        &resources,
        &staged_z3.path,
        "cli-help",
        &["-h"],
        b"",
        timeout,
    )?);
    captures.push(run_capture(
        &resources,
        &staged_z3.path,
        "command-help",
        &["-in"],
        b"(help)\n(exit)\n",
        timeout,
    )?);
    for (id, flag) in [
        ("tactics", "-tactics"),
        ("probes", "-probes"),
        ("simplifiers", "-simplifiers"),
        ("parameters", "-p"),
        ("parameter-descriptions", "-pd"),
    ] {
        captures.push(run_capture(
            &resources,
            &staged_z3.path,
            id,
            &[flag, "-in"],
            b"",
            timeout,
        )?);
    }
    for capture in &captures {
        capture.require_pass()?;
    }
    if captures[0].stdout != format!("{}\n", target.reference_executable.version_output) {
        return Err("authenticated Z3 executable version output drifted".to_string());
    }
    let post_sha = sha256_file(&staged_z3.path, "staged Z3 after source inventory")?;
    if post_sha != target.reference_executable.sha256 {
        return Err("authenticated Z3 bytes changed during registry discovery".to_string());
    }

    let observable = extract_observable_items(snapshot, &captures)?;
    let mut rows = source_cases(snapshot)?;
    rows.extend(observable_cases(&observable));
    rows.extend(captures.into_iter().map(LiveCapture::into_case));
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    let cases = case_counts_from_rows(&rows)?;
    Ok(Execution {
        z3_sha256: post_sha,
        resource_envelope,
        result: overall_validator_result(&rows),
        cases,
        case_results: rows,
    })
}

fn run_capture(
    resources: &PlannedResources,
    executable: &Path,
    id: &'static str,
    args: &[&str],
    input: &[u8],
    timeout: Duration,
) -> Result<LiveCapture, String> {
    let invocation = args.join(" ");
    let output = resources
        .run_external_transcript(
            executable,
            args.iter().copied(),
            input,
            timeout,
            &format!("Z3 5.1.0 source inventory: {id}"),
        )
        .map_err(|error| error.to_string())?;
    let stdout_utf8 = String::from_utf8(output.stdout);
    let stderr_utf8 = String::from_utf8(output.stderr);
    let stdout_valid = stdout_utf8.is_ok();
    let stderr_valid = stderr_utf8.is_ok();
    let stdout =
        stdout_utf8.unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned());
    let stderr =
        stderr_utf8.unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned());
    let exit_code = output.status.and_then(|status| status.code());
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
    } else if exit_code != Some(0) {
        ValidatorCaseOutcome::Crash
    } else if !stderr.is_empty() {
        ValidatorCaseOutcome::Fail
    } else {
        ValidatorCaseOutcome::Pass
    };
    Ok(LiveCapture {
        id,
        invocation,
        input: input.to_vec(),
        stdout,
        stderr,
        exit_code,
        process: ProcessObservation {
            stdin_complete: output.stdin_complete,
            timed_out: output.timed_out,
            memout: output.memout,
            stdout_truncated: output.stdout_truncated,
            stderr_truncated: output.stderr_truncated,
        },
        outcome,
    })
}

fn extract_observable_items(
    snapshot: &Z3SourceSnapshot,
    captures: &[LiveCapture],
) -> Result<Vec<ObservableItem>, String> {
    let capture = |id: &str| -> Result<&LiveCapture, String> {
        captures
            .iter()
            .find(|capture| capture.id == id)
            .ok_or_else(|| format!("missing live Z3 registry capture {id}"))
    };
    extract_observable_items_from_transcripts(
        snapshot,
        ObservableTranscripts {
            cli_help: &capture("cli-help")?.stdout,
            command_help: &capture("command-help")?.stdout,
            tactics: &capture("tactics")?.stdout,
            probes: &capture("probes")?.stdout,
            simplifiers: &capture("simplifiers")?.stdout,
            parameters: &capture("parameters")?.stdout,
            parameter_descriptions: &capture("parameter-descriptions")?.stdout,
        },
    )
}

pub(super) fn extract_observable_items_from_transcripts(
    snapshot: &Z3SourceSnapshot,
    transcripts: ObservableTranscripts<'_>,
) -> Result<Vec<ObservableItem>, String> {
    let main = source_text(snapshot, "src/shell/main.cpp")?;
    let parser = source_text(snapshot, "src/parsers/smt2/smt2parser.cpp")?;
    let basic_commands = source_text(snapshot, "src/cmd_context/basic_cmds.cpp")?;
    let mut items = BTreeMap::<(String, String), String>::new();

    let cli_options = extract_delimited(main, "strcmp(opt_name, \"", "\"");
    if cli_options.len() != 33 {
        return Err(format!(
            "Z3 shell source option inventory drifted: expected 33, got {}",
            cli_options.len()
        ));
    }
    for name in cli_options {
        insert_item(&mut items, "cli-option", &name, &name)?;
    }

    let help_lines = transcripts
        .cli_help
        .lines()
        .filter(|line| line.starts_with("  -"))
        .collect::<Vec<_>>();
    if help_lines.len() != 27 {
        return Err(format!(
            "Z3 live CLI help option inventory drifted: expected 27, got {}",
            help_lines.len()
        ));
    }
    for (index, line) in help_lines.into_iter().enumerate() {
        insert_item(
            &mut items,
            "cli-help-option",
            &format!("{index:02}"),
            line.trim(),
        )?;
    }

    let enum_start = main
        .find("typedef enum {")
        .ok_or("Z3 shell source has no input_kind enum")?;
    let enum_end = main[enum_start..]
        .find("} input_kind;")
        .map(|offset| enum_start + offset)
        .ok_or("Z3 shell input_kind enum is unterminated")?;
    let modes = main[enum_start + "typedef enum {".len()..enum_end]
        .split(',')
        .map(str::trim)
        .filter(|mode| *mode != "IN_UNSPECIFIED")
        .collect::<BTreeSet<_>>();
    if modes.len() != 9 {
        return Err(format!(
            "Z3 source input-mode inventory drifted: expected 9, got {}",
            modes.len()
        ));
    }
    for mode in modes {
        insert_item(&mut items, "input-mode", mode, mode)?;
    }

    let mut source_extensions = extract_delimited(main, "strcmp(ext, \"", "\"");
    let tptp_start = main
        .find("static char const* tptp_extensions[]")
        .ok_or("Z3 shell has no TPTP extension registry")?;
    let tptp_end = main[tptp_start..]
        .find("};")
        .map(|offset| tptp_start + offset)
        .ok_or("Z3 shell TPTP extension registry is unterminated")?;
    source_extensions.extend(extract_quoted_strings(&main[tptp_start..tptp_end]));
    let expected_extensions = EXTENSION_MODES
        .iter()
        .map(|(extension, _)| (*extension).to_string())
        .collect::<BTreeSet<_>>();
    if source_extensions != expected_extensions {
        return Err(format!(
            "Z3 filename-extension inventory drifted: expected {expected_extensions:?}, got {source_extensions:?}"
        ));
    }
    for (extension, mode) in EXTENSION_MODES {
        insert_item(&mut items, "filename-extension", extension, mode)?;
    }

    let registry_commands = parse_command_help(transcripts.command_help)?;
    if registry_commands.len() != 86 {
        return Err(format!(
            "Z3 live SMT2 command registry drifted: expected 86, got {}",
            registry_commands.len()
        ));
    }
    let native_commands = parse_native_commands(parser)?;
    if native_commands.len() != 20 {
        return Err(format!(
            "Z3 parser-native command inventory drifted: expected 20, got {}",
            native_commands.len()
        ));
    }
    let command_names = registry_commands
        .keys()
        .chain(native_commands.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    if command_names.len() != 94 {
        return Err(format!(
            "Z3 accepted SMT2 command union drifted: expected 94, got {}",
            command_names.len()
        ));
    }
    for name in &command_names {
        let live = registry_commands.get(name).map_or_else(
            || "live-registry=none".to_string(),
            |line| format!("live-registry={line}"),
        );
        let detail = format!(
            "{live};parser-native={}",
            native_commands.contains_key(name)
        );
        insert_item(&mut items, "smt-command", name, &detail)?;
    }

    let option_section = source_section(
        basic_commands,
        "class set_get_option_cmd",
        "class set_option_cmd",
        "SMT option-key registry",
    )?;
    let option_keys = extract_delimited(option_section, "(\"", "\")")
        .into_iter()
        .filter(|value| value.starts_with(':'))
        .collect::<BTreeSet<_>>();
    if option_keys.len() != 20 {
        return Err(format!(
            "Z3 source SMT option-key inventory drifted: expected 20, got {}",
            option_keys.len()
        ));
    }
    for key in option_keys {
        insert_item(
            &mut items,
            "smt-option-key",
            &key,
            "src/cmd_context/basic_cmds.cpp:set_get_option_cmd",
        )?;
    }

    let info_section = source_section(
        basic_commands,
        "class get_info_cmd",
        "class set_info_cmd",
        "SMT get-info key registry",
    )?;
    let info_keys = extract_delimited(info_section, "(\"", "\")")
        .into_iter()
        .filter(|value| value.starts_with(':'))
        .collect::<BTreeSet<_>>();
    if info_keys.len() != 11 {
        return Err(format!(
            "Z3 source SMT info-key inventory drifted: expected 11, got {}",
            info_keys.len()
        ));
    }
    for key in info_keys {
        insert_item(
            &mut items,
            "smt-info-key",
            &key,
            "src/cmd_context/basic_cmds.cpp:get_info_cmd",
        )?;
    }

    let parser_constructor = source_section(
        parser,
        "parser(cmd_context & ctx",
        "m_num_open_paren(0)",
        "SMT parser symbol constructor",
    )?;
    let parser_tokens = extract_delimited(parser_constructor, "(\"", "\")")
        .difference(&command_names)
        .cloned()
        .collect::<BTreeSet<_>>();
    if parser_tokens.len() != 22 {
        return Err(format!(
            "Z3 source SMT parser-token inventory drifted: expected 22, got {}",
            parser_tokens.len()
        ));
    }
    for token in parser_tokens {
        insert_item(
            &mut items,
            "smt-parser-token",
            &token,
            "src/parsers/smt2/smt2parser.cpp:parser-constructor",
        )?;
    }

    let mut logic_literals = BTreeMap::<String, BTreeSet<&str>>::new();
    for path in ["src/solver/smt_logics.cpp", "src/solver/smt_logics.h"] {
        for literal in extract_quoted_strings(source_text(snapshot, path)?) {
            if !literal.contains('/') {
                logic_literals.entry(literal).or_default().insert(path);
            }
        }
    }
    if logic_literals.len() != 24 {
        return Err(format!(
            "Z3 source logic-recognizer literal inventory drifted: expected 24, got {}",
            logic_literals.len()
        ));
    }
    for (literal, paths) in logic_literals {
        insert_item(
            &mut items,
            "logic-recognizer-literal",
            &literal,
            &format!(
                "source-logic-recognizer={}",
                paths.into_iter().collect::<Vec<_>>().join(",")
            ),
        )?;
    }

    let setup_path = "src/smt/smt_setup.cpp";
    let strategy_aliases =
        extract_delimited(source_text(snapshot, setup_path)?, "m_logic == \"", "\"");
    if strategy_aliases.len() != 33 {
        return Err(format!(
            "Z3 source logic-strategy alias inventory drifted: expected 33, got {}",
            strategy_aliases.len()
        ));
    }
    for alias in strategy_aliases {
        insert_item(
            &mut items,
            "logic-strategy-alias",
            &alias,
            "src/smt/smt_setup.cpp:m_logic-dispatch",
        )?;
    }

    let mut declaration_builtins = BTreeMap::<String, BTreeSet<&str>>::new();
    for path in DECLARATION_PLUGIN_PATHS {
        for symbol in extract_declaration_builtin_symbols(source_text(snapshot, path)?, path)? {
            declaration_builtins.entry(symbol).or_default().insert(path);
        }
    }
    if declaration_builtins.len() != 323 {
        return Err(format!(
            "Z3 declaration-plugin builtin inventory drifted: expected 323, got {}",
            declaration_builtins.len()
        ));
    }
    for (symbol, paths) in declaration_builtins {
        insert_item(
            &mut items,
            "declaration-builtin",
            &symbol,
            &format!(
                "source-builtin-registration={}",
                paths.into_iter().collect::<Vec<_>>().join(",")
            ),
        )?;
    }

    for (registry_output, category, expected) in [
        (transcripts.tactics, "tactic", 118usize),
        (transcripts.probes, "probe", 42usize),
        (transcripts.simplifiers, "simplifier", 37usize),
    ] {
        let registry = parse_dash_registry(registry_output)?;
        if registry.len() != expected {
            return Err(format!(
                "Z3 {category} registry drifted: expected {expected}, got {}",
                registry.len()
            ));
        }
        for (name, detail) in registry {
            insert_item(&mut items, category, &name, &detail)?;
        }
    }

    let parameters = parse_parameters(transcripts.parameters)?;
    let descriptions = parse_parameters(transcripts.parameter_descriptions)?;
    if parameters.keys().collect::<Vec<_>>() != descriptions.keys().collect::<Vec<_>>() {
        return Err("Z3 -p and -pd parameter key inventories differ".to_string());
    }
    for ((category, name), detail) in parameters {
        let described = descriptions
            .get(&(category.clone(), name.clone()))
            .ok_or("Z3 parameter description disappeared")?;
        insert_item(
            &mut items,
            &category,
            &name,
            &format!("{detail} | {described}"),
        )?;
    }

    let mut category_counts = BTreeMap::<&str, usize>::new();
    for (category, expected) in CATEGORY_COUNTS {
        category_counts.insert(category, expected);
    }
    for category in category_counts.keys().copied().collect::<Vec<_>>() {
        let actual = items
            .keys()
            .filter(|(item_category, _)| item_category == category)
            .count();
        if actual != category_counts[category] {
            return Err(format!(
                "Z3 observable category {category} drifted: expected {}, got {actual}",
                category_counts[category]
            ));
        }
    }
    let observable = items
        .into_iter()
        .map(|((category, name), detail)| ObservableItem {
            category,
            name,
            detail,
        })
        .collect::<Vec<_>>();
    if observable.len() != EXPECTED_OBSERVABLE_ITEMS {
        return Err(format!(
            "Z3 observable inventory drifted: expected {EXPECTED_OBSERVABLE_ITEMS}, got {}",
            observable.len()
        ));
    }
    let digest = observable_manifest_sha256(&observable);
    if digest != EXPECTED_OBSERVABLE_SHA256 {
        return Err(format!(
            "Z3 observable inventory digest drifted: expected {EXPECTED_OBSERVABLE_SHA256}, got {digest}"
        ));
    }
    Ok(observable)
}

fn insert_item(
    items: &mut BTreeMap<(String, String), String>,
    category: &str,
    name: &str,
    detail: &str,
) -> Result<(), String> {
    validate_text(name, "Z3 observable item name")?;
    validate_text(detail, "Z3 observable item detail")?;
    if items
        .insert((category.to_string(), name.to_string()), detail.to_string())
        .is_some()
    {
        return Err(format!("duplicate Z3 observable item {category}.{name}"));
    }
    Ok(())
}

fn parse_command_help(output: &str) -> Result<BTreeMap<String, String>, String> {
    let mut commands = BTreeMap::new();
    for line in output.lines() {
        let rest = line
            .strip_prefix("\" (")
            .or_else(|| line.strip_prefix(" ("));
        let Some(rest) = rest else { continue };
        let end = rest
            .find([' ', ')'])
            .ok_or("Z3 command help line has no command terminator")?;
        let name = &rest[..end];
        let detail = line.trim_start_matches(['\"', ' ']).trim().to_string();
        if commands.insert(name.to_string(), detail).is_some() {
            return Err(format!("duplicate live Z3 command {name}"));
        }
    }
    Ok(commands)
}

fn parse_native_commands(source: &str) -> Result<BTreeMap<String, String>, String> {
    let start = source
        .find("        void parse_cmd() {")
        .ok_or("Z3 SMT2 parser has no parse_cmd")?;
    let end = source[start..]
        .find("\n    public:")
        .map(|offset| start + offset)
        .ok_or("Z3 SMT2 parse_cmd body is unterminated")?;
    let ids = extract_delimited(&source[start..end], "if (s == m_", ")");
    let mut commands = BTreeMap::new();
    for id in ids {
        let prefix = format!("m_{id}(\"");
        let name = extract_delimited(source, &prefix, "\"")
            .into_iter()
            .next()
            .ok_or_else(|| format!("Z3 SMT2 parser command m_{id} has no symbol initializer"))?;
        if commands.insert(name.clone(), id.clone()).is_some() {
            return Err(format!("duplicate parser-native Z3 command {name}"));
        }
    }
    Ok(commands)
}

fn parse_dash_registry(output: &str) -> Result<BTreeMap<String, String>, String> {
    let mut result = BTreeMap::new();
    for line in output.lines() {
        let rest = line
            .strip_prefix("- ")
            .ok_or("Z3 named registry line does not start with `- `")?;
        let name = rest
            .split_once(' ')
            .map_or(rest, |(name, _)| name)
            .to_string();
        if result.insert(name.clone(), rest.to_string()).is_some() {
            return Err(format!("duplicate Z3 named registry item {name}"));
        }
    }
    Ok(result)
}

fn parse_parameters(output: &str) -> Result<BTreeMap<(String, String), String>, String> {
    let mut result = BTreeMap::new();
    let mut scope: Option<String> = None;
    for line in output.lines() {
        if line == "Global parameters" {
            scope = Some("global".to_string());
        } else if let Some(header) = line.strip_prefix("[module] ") {
            let module = header
                .split_once(',')
                .map_or(header, |(module, _)| module)
                .to_string();
            scope = Some(module.clone());
            result.insert(("parameter-module".to_string(), module), line.to_string());
        } else if let Some(detail) = line.strip_prefix("    ") {
            let scope = scope
                .as_deref()
                .ok_or("Z3 parameter line appears outside a parameter section")?;
            let parameter = detail
                .split_whitespace()
                .next()
                .ok_or("Z3 parameter line is empty")?;
            let (category, name) = if scope == "global" {
                ("global-parameter".to_string(), parameter.to_string())
            } else {
                (
                    "module-parameter".to_string(),
                    format!("{scope}.{parameter}"),
                )
            };
            if result
                .insert((category, name.clone()), detail.to_string())
                .is_some()
            {
                return Err(format!("duplicate Z3 parameter {name}"));
            }
        } else if !line.is_empty()
            && !line.starts_with("To set a module parameter")
            && !line.starts_with("Example:")
        {
            return Err(format!("unclassified Z3 parameter registry line {line:?}"));
        }
    }
    Ok(result)
}

fn source_section<'a>(
    source: &'a str,
    start_marker: &str,
    end_marker: &str,
    label: &str,
) -> Result<&'a str, String> {
    let start = source
        .find(start_marker)
        .ok_or_else(|| format!("Z3 source has no {label} start marker {start_marker:?}"))?;
    let end = source[start..]
        .find(end_marker)
        .map(|offset| start + offset)
        .ok_or_else(|| format!("Z3 source has no {label} end marker {end_marker:?}"))?;
    if end == start {
        return Err(format!("Z3 source {label} section is empty"));
    }
    Ok(&source[start..end])
}

fn extract_declaration_builtin_symbols(
    source: &str,
    path: &str,
) -> Result<BTreeSet<String>, String> {
    let active_source = strip_if_zero_regions(source, path)?;
    let arguments = extract_delimited(&active_source, "builtin_name(", ",");
    let mut symbols = BTreeSet::new();
    for raw_argument in arguments {
        let argument = raw_argument.trim();
        if let Some(quoted) = argument.strip_prefix('"') {
            let value = quoted.strip_suffix('"').ok_or_else(|| {
                format!(
                    "Z3 declaration-plugin builtin has malformed literal in {path}: {argument:?}"
                )
            })?;
            symbols.insert(value.to_string());
            continue;
        }
        match argument {
            "m_sigs[i]->m_name.str()" => {
                let values = extract_dynamic_signature_registry(&active_source, path)?;
                if values.is_empty() {
                    return Err(format!(
                        "Z3 declaration-plugin dynamic signature registry is empty in {path}"
                    ));
                }
                symbols.extend(values);
            }
            "std::string(m_names[i])" => {
                let values = extract_indexed_name_registry(&active_source, path)?;
                if values.is_empty() {
                    return Err(format!(
                        "Z3 declaration-plugin dynamic name registry is empty in {path}"
                    ));
                }
                symbols.extend(values);
            }
            _ if argument.starts_with("m_") && argument.ends_with(".str()") => {
                let member = argument
                    .strip_suffix(".str()")
                    .ok_or("internal declaration-plugin member parsing error")?;
                let values = extract_delimited(&active_source, &format!("{member}(\""), "\"");
                if values.len() != 1 {
                    return Err(format!(
                        "Z3 declaration-plugin builtin member {member} in {path} has {} initializers, expected one",
                        values.len()
                    ));
                }
                symbols.extend(values);
            }
            _ if argument
                .chars()
                .all(|character| character == '_' || character.is_ascii_uppercase()) =>
            {
                let values =
                    extract_delimited(&active_source, &format!("#define {argument} \""), "\"");
                if values.len() != 1 {
                    return Err(format!(
                        "Z3 declaration-plugin builtin macro {argument} in {path} has {} definitions, expected one",
                        values.len()
                    ));
                }
                symbols.extend(values);
            }
            _ => {
                return Err(format!(
                    "unclassified Z3 declaration-plugin builtin expression in {path}: {argument:?}"
                ));
            }
        }
    }
    Ok(symbols)
}

/// Remove source that the C++ preprocessor unconditionally disables.
///
/// This deliberately evaluates only the literal `#if 0` form used by the
/// pinned declaration plugins. Other conditions remain source-visible, so the
/// inventory continues to describe the union of builtins reachable through
/// logic and parameter choices. An alternate branch on `#if 0` is rejected
/// instead of guessing which preprocessor expression makes it active.
fn strip_if_zero_regions(source: &str, path: &str) -> Result<String, String> {
    let mut active = String::with_capacity(source.len());
    let mut disabled_depth = 0usize;

    for line in source.split_inclusive('\n') {
        let directive = line.trim();
        if disabled_depth == 0 {
            if directive == "#if 0" {
                disabled_depth = 1;
                if line.ends_with('\n') {
                    active.push('\n');
                }
            } else {
                active.push_str(line);
            }
            continue;
        }

        if directive.starts_with("#if ")
            || directive.starts_with("#ifdef ")
            || directive.starts_with("#ifndef ")
        {
            disabled_depth += 1;
        } else if directive == "#endif" {
            disabled_depth -= 1;
        } else if disabled_depth == 1 && (directive == "#else" || directive.starts_with("#elif ")) {
            return Err(format!(
                "Z3 declaration-plugin #if 0 region has an alternate branch in {path}"
            ));
        }
        if line.ends_with('\n') {
            active.push('\n');
        }
    }

    if disabled_depth != 0 {
        return Err(format!(
            "Z3 declaration-plugin has an unterminated #if 0 region in {path}"
        ));
    }
    Ok(active)
}

/// Extract only the string-valued `m_sigs[...]` assignments that initialize
/// the registry iterated by `get_op_names`. Unrelated `psig` allocations are
/// not declaration owners.
fn extract_dynamic_signature_registry(
    source: &str,
    path: &str,
) -> Result<BTreeSet<String>, String> {
    let mut values = BTreeSet::new();
    for line in source.lines() {
        let Some((_, assignment)) = line.split_once("m_sigs[") else {
            continue;
        };
        let Some((_, remainder)) = assignment.split_once(']') else {
            return Err(format!(
                "Z3 declaration-plugin dynamic signature has no closing bracket in {path}"
            ));
        };
        let Some(value) = remainder
            .trim_start()
            .strip_prefix('=')
            .map(str::trim_start)
            .and_then(|value| value.strip_prefix("alloc(psig, m, \""))
        else {
            continue;
        };
        let (value, _) = value.split_once('"').ok_or_else(|| {
            format!("Z3 declaration-plugin dynamic signature has no closing quote in {path}")
        })?;
        if value.is_empty() {
            return Err(format!(
                "Z3 declaration-plugin dynamic signature has an empty name in {path}"
            ));
        }
        values.insert(value.to_string());
    }
    Ok(values)
}

/// Extract an indexed `m_names` registry and apply the exclusions in the
/// actual `get_op_names` loop guard. This distinguishes internal names that
/// are initialized for direct AST construction from names exposed to SMT2.
fn extract_indexed_name_registry(source: &str, path: &str) -> Result<BTreeSet<String>, String> {
    let mut entries = BTreeMap::<String, String>::new();
    for line in source.lines() {
        let trimmed = line.trim();
        let Some(assignment) = trimmed.strip_prefix("m_names[") else {
            continue;
        };
        let Some((index, remainder)) = assignment.split_once(']') else {
            return Err(format!(
                "Z3 declaration-plugin indexed name has no closing bracket in {path}: {trimmed:?}"
            ));
        };
        let remainder = remainder.trim_start();
        if !remainder.starts_with('=') {
            continue;
        }
        let value = remainder
            .strip_prefix("= \"")
            .and_then(|value| value.split_once('"').map(|(value, _)| value))
            .ok_or_else(|| {
                format!(
                    "Z3 declaration-plugin indexed name has no string literal in {path}: {trimmed:?}"
                )
            })?;
        if index.is_empty()
            || !index
                .bytes()
                .all(|byte| byte == b'_' || byte.is_ascii_uppercase() || byte.is_ascii_digit())
            || value.is_empty()
        {
            return Err(format!(
                "Z3 declaration-plugin indexed name is malformed in {path}: {trimmed:?}"
            ));
        }
        if entries
            .insert(index.to_string(), value.to_string())
            .is_some()
        {
            return Err(format!(
                "Z3 declaration-plugin indexed name {index} is assigned twice in {path}"
            ));
        }
    }

    let guards = source
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            (trimmed.starts_with("if (") && trimmed.contains("m_names[i]")).then_some(trimmed)
        })
        .collect::<Vec<_>>();
    if guards.len() != 1 {
        return Err(format!(
            "Z3 declaration-plugin dynamic name registry in {path} has {} loop guards, expected one",
            guards.len()
        ));
    }
    let condition = guards[0]
        .strip_prefix("if (")
        .and_then(|condition| condition.strip_suffix(')'))
        .ok_or_else(|| {
            format!("Z3 declaration-plugin dynamic name registry has a malformed guard in {path}")
        })?;
    let mut exclusions = BTreeSet::new();
    for term in condition.split("&&").map(str::trim) {
        if term == "m_names[i]" {
            continue;
        }
        let excluded = term.strip_prefix("i != ").ok_or_else(|| {
            format!(
                "Z3 declaration-plugin dynamic name registry has an unclassified guard term in {path}: {term:?}"
            )
        })?;
        if !excluded
            .bytes()
            .all(|byte| byte == b'_' || byte.is_ascii_uppercase() || byte.is_ascii_digit())
        {
            return Err(format!(
                "Z3 declaration-plugin dynamic name registry has a malformed exclusion in {path}: {excluded:?}"
            ));
        }
        exclusions.insert(excluded.to_string());
    }
    for excluded in exclusions {
        if entries.remove(&excluded).is_none() {
            return Err(format!(
                "Z3 declaration-plugin dynamic name registry excludes unknown index {excluded} in {path}"
            ));
        }
    }
    Ok(entries.into_values().collect())
}

fn extract_delimited(source: &str, prefix: &str, suffix: &str) -> BTreeSet<String> {
    let mut result = BTreeSet::new();
    let mut rest = source;
    while let Some(start) = rest.find(prefix) {
        let value_start = start + prefix.len();
        let after = &rest[value_start..];
        let Some(end) = after.find(suffix) else { break };
        result.insert(after[..end].to_string());
        rest = &after[end + suffix.len()..];
    }
    result
}

fn extract_quoted_strings(source: &str) -> BTreeSet<String> {
    let mut result = BTreeSet::new();
    let mut rest = source;
    while let Some(start) = rest.find('\"') {
        let after = &rest[start + 1..];
        let Some(end) = after.find('\"') else { break };
        result.insert(after[..end].to_string());
        rest = &after[end + 1..];
    }
    result
}

fn source_text<'a>(snapshot: &'a Z3SourceSnapshot, path: &str) -> Result<&'a str, String> {
    snapshot
        .selected_files
        .iter()
        .find(|file| file.path == path)
        .map(|file| file.content.as_str())
        .ok_or_else(|| format!("Z3 source snapshot has no selected file {path}"))
}

pub(super) fn observable_manifest_sha256(items: &[ObservableItem]) -> String {
    let mut hasher = Sha256::new();
    for item in items {
        hasher.update(item.canonical_line().as_bytes());
    }
    format!("{:x}", hasher.finalize())
}

fn reference_inventory_cases(snapshot: &Z3SourceSnapshot) -> Result<Vec<ValidatorCase>, String> {
    validate_snapshot(snapshot, &canonical_profile())?;
    let tree_entry = |path: &str| {
        snapshot
            .tree
            .iter()
            .find(|entry| entry.path == path)
            .ok_or_else(|| format!("pinned Z3 source tree is missing {path}"))
    };
    let selected_manifest = |paths: &[&str]| -> Result<String, String> {
        let mut hasher = Sha256::new();
        for path in paths {
            let file = snapshot
                .selected_files
                .iter()
                .find(|file| file.path == *path)
                .ok_or_else(|| format!("pinned Z3 source snapshot is missing {path}"))?;
            hasher.update(file.path.as_bytes());
            hasher.update(b"\0");
            hasher.update(file.git_blob.as_bytes());
            hasher.update(b"\0");
            hasher.update(file.content_sha256.as_bytes());
            hasher.update(b"\n");
        }
        Ok(format!("{:x}", hasher.finalize()))
    };
    let pass = |id: &str, input_sha256: String, expected: &str, observed: String| ValidatorCase {
        id: id.to_string(),
        input_sha256,
        expected: expected.to_string(),
        observed,
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome: ValidatorCaseOutcome::Pass,
    };

    let abi = tree_entry("src/api/z3_api.h")?;
    let abi_source_digest = selected_manifest(&["src/api/z3_api.h", "src/api/z3_macros.h"])?;
    let behavior_paths = [
        "src/cmd_context/cmd_context.cpp",
        "src/cmd_context/simplifier_cmds.cpp",
        "src/cmd_context/tactic_cmds.cpp",
        "src/parsers/smt2/smt2parser.cpp",
        "src/shell/main.cpp",
        "src/shell/smtlib_frontend.cpp",
        "src/util/gparams.cpp",
    ];
    let behavior_digest = selected_manifest(&behavior_paths)?;
    let version = source_text(snapshot, "scripts/VERSION.txt")?.trim();
    if version != "5.1.0.0" {
        return Err(format!(
            "pinned Z3 VERSION.txt is {version:?}, expected \"5.1.0.0\""
        ));
    }
    let identity_digest = selected_manifest(&["scripts/VERSION.txt", "src/util/z3_version.h.in"])?;
    let selected_source_digest = selected_manifest(&SELECTED_SOURCE_PATHS)?;
    let source_digest = sha256_bytes(
        format!(
            "tree={EXPECTED_TREE_SHA256}\nselected={selected_source_digest}\nregistration-scan={}\n",
            snapshot.registration_scan.content_sha256
        )
        .as_bytes(),
    );

    let mut rows = vec![
        pass(
            "overlay.z3-5.1.0.behavioral-transcripts",
            behavior_digest.clone(),
            "pinned shell, parser, command, tactic, simplifier, and parameter source owners define the behavioral transcript row",
            format!(
                "source-files={};selected-source-manifest-sha256={behavior_digest}",
                behavior_paths.len()
            ),
        ),
        pass(
            "overlay.z3-5.1.0.c-abi",
            abi_source_digest.clone(),
            "the exact pinned Z3 5.1.0 z3_api.h and z3_macros.h source objects own the C ABI row",
            format!(
                "path={:?};git-blob={};size={};api-source-manifest-sha256={abi_source_digest}",
                abi.path, abi.git_blob, abi.size,
            ),
        ),
        pass(
            "overlay.z3-5.1.0.source-inventory",
            source_digest.clone(),
            "the complete source-tree manifest and retained registry-owner blobs define the observable overlay inventory row",
            format!(
                "tree-files={EXPECTED_TREE_FILES};tree-sha256={EXPECTED_TREE_SHA256};selected-files={};selected-source-manifest-sha256={selected_source_digest};registration-sites={};registration-scan-sha256={}",
                SELECTED_SOURCE_PATHS.len(),
                snapshot.registration_scan.line_count,
                snapshot.registration_scan.content_sha256
            ),
        ),
        pass(
            "overlay.z3-5.1.0.target-identity",
            identity_digest.clone(),
            "the pinned VERSION.txt and generated version-header template define the Z3 5.1.0 target-identity row",
            format!(
                "version={version};selected-source-manifest-sha256={identity_digest}"
            ),
        ),
    ];
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    Ok(rows)
}

fn source_cases(snapshot: &Z3SourceSnapshot) -> Result<Vec<ValidatorCase>, String> {
    let mut rows = Vec::with_capacity(snapshot.tree.len() + snapshot.selected_files.len() + 1);
    for (index, entry) in snapshot.tree.iter().enumerate() {
        let manifest = format!("{}\t{}\t{}\n", entry.path, entry.git_blob, entry.size);
        rows.push(ValidatorCase {
            id: format!(
                "source-tree.{index:04}.{}",
                &sha256_bytes(entry.path.as_bytes())[..12]
            ),
            input_sha256: sha256_bytes(manifest.as_bytes()),
            expected: "exact tracked path, Git blob object, and byte-size row in the pinned 2,756-file source manifest".to_string(),
            observed: format!(
                "path={:?};git-blob={};size={}",
                entry.path, entry.git_blob, entry.size
            ),
            stdout: None,
            stderr: None,
            exit_code: None,
            process: None,
            outcome: ValidatorCaseOutcome::Pass,
        });
    }
    for (index, file) in snapshot.selected_files.iter().enumerate() {
        rows.push(ValidatorCase {
            id: format!(
                "selected-source.{index:02}.{}",
                &sha256_bytes(file.path.as_bytes())[..12]
            ),
            input_sha256: file.content_sha256.clone(),
            expected: "retained UTF-8 registry source bytes match the pinned Git blob object"
                .to_string(),
            observed: format!(
                "path={:?};git-blob={};size={};content-sha256={}",
                file.path, file.git_blob, file.size, file.content_sha256
            ),
            stdout: None,
            stderr: None,
            exit_code: None,
            process: None,
            outcome: ValidatorCaseOutcome::Pass,
        });
    }
    let classification =
        classify_registration_scan(&snapshot.registration_scan, &canonical_profile())?;
    rows.push(ValidatorCase {
        id: "source-registration-scan.classified".to_string(),
        input_sha256: classification.content_sha256.clone(),
        expected: "every row in the broad pinned registration scan receives exactly one closed observable-owner or explicit non-observable disposition; unknown path and lexical classes abort validation".to_string(),
        observed: format!(
            "scopes=src,scripts;matches={};raw-sha256={};classification-counts={};classification-sha256={}",
            snapshot.registration_scan.line_count,
            snapshot.registration_scan.content_sha256,
            classification.counts_text(),
            classification.content_sha256,
        ),
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome: ValidatorCaseOutcome::Pass,
    });
    Ok(rows)
}

fn observable_cases(items: &[ObservableItem]) -> Vec<ValidatorCase> {
    items
        .iter()
        .enumerate()
        .map(|(index, item)| {
            let canonical = item.canonical_line();
            ValidatorCase {
                id: format!(
                    "inventory.{index:04}.{}.{}",
                    item.category,
                    &sha256_bytes(item.name.as_bytes())[..12]
                ),
                input_sha256: sha256_bytes(canonical.as_bytes()),
                expected: "exact sorted observable Z3 5.1.0 source/live-registry inventory item"
                    .to_string(),
                observed: format!(
                    "category={:?};name={:?};detail={:?}",
                    item.category, item.name, item.detail
                ),
                stdout: None,
                stderr: None,
                exit_code: None,
                process: None,
                outcome: ValidatorCaseOutcome::Pass,
            }
        })
        .collect()
}

fn invocation_sha256(invocation: &str, input: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(invocation.as_bytes());
    hasher.update(b"\0");
    hasher.update(input);
    format!("{:x}", hasher.finalize())
}

fn parse_tree(bytes: &[u8]) -> Result<Vec<Z3TreeEntry>, String> {
    let mut entries = Vec::new();
    for record in bytes
        .split(|byte| *byte == 0)
        .filter(|record| !record.is_empty())
    {
        let record = std::str::from_utf8(record)
            .map_err(|_| "git ls-tree emitted a non-UTF-8 tracked path")?;
        let (metadata, path) = record
            .split_once('\t')
            .ok_or("git ls-tree record has no tab-delimited path")?;
        let fields = metadata.split_whitespace().collect::<Vec<_>>();
        if fields.len() != 4 || fields[1] != "blob" {
            return Err(format!("Z3 tracked entry {path:?} is not a sized Git blob"));
        }
        validate_git_object_id(fields[2])?;
        let size = fields[3]
            .parse::<usize>()
            .map_err(|_| format!("Z3 tracked entry {path:?} has invalid size"))?;
        entries.push(Z3TreeEntry {
            path: path.to_string(),
            git_blob: fields[2].to_string(),
            size,
        });
    }
    entries.sort_by(|left, right| left.path.cmp(&right.path));
    Ok(entries)
}

fn tree_manifest_sha256(entries: &[Z3TreeEntry]) -> String {
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
        return Err("Git blob id must be 40 lowercase hexadecimal characters".to_string());
    }
    Ok(())
}

fn git_text(checkout: &Path, args: &[&str], label: &str) -> Result<String, String> {
    String::from_utf8(git_bytes(checkout, args, label)?)
        .map_err(|_| format!("git {label} output is not UTF-8"))
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
    fn full_tree_manifest_algorithm_is_frozen() {
        let entries = vec![Z3TreeEntry {
            path: "src/example.cpp".to_string(),
            git_blob: "1".repeat(40),
            size: 7,
        }];
        assert_eq!(
            tree_manifest_sha256(&entries),
            sha256_bytes(format!("src/example.cpp\t{}\t7\n", "1".repeat(40)).as_bytes())
        );
    }

    #[test]
    fn observable_manifest_algorithm_is_frozen() {
        let item = ObservableItem {
            category: "tactic".to_string(),
            name: "simplify".to_string(),
            detail: "simplify goal".to_string(),
        };
        assert_eq!(
            observable_manifest_sha256(std::slice::from_ref(&item)),
            sha256_bytes(b"tactic\tsimplify\tsimplify goal\n")
        );
    }

    #[test]
    fn declaration_builtin_extractor_ignores_nested_if_zero_regions() {
        let source = r#"
op_names.push_back(builtin_name("live", OP_LIVE));
#if 0
op_names.push_back(builtin_name("disabled", OP_DISABLED));
#ifdef NESTED
op_names.push_back(builtin_name("nested-disabled", OP_NESTED_DISABLED));
#endif
#endif
op_names.push_back(builtin_name("after", OP_AFTER));
"#;
        assert_eq!(
            extract_declaration_builtin_symbols(source, "synthetic.cpp").unwrap(),
            ["after".to_string(), "live".to_string()]
                .into_iter()
                .collect()
        );
        assert!(extract_declaration_builtin_symbols(
            "#if 0\nbuiltin_name(\"disabled\", OP_DISABLED)\n",
            "unterminated.cpp"
        )
        .is_err());
        assert!(extract_declaration_builtin_symbols(
            "#if 0\nbuiltin_name(\"disabled\", OP_DISABLED)\n#else\nbuiltin_name(\"active\", OP_ACTIVE)\n#endif\n",
            "alternate.cpp"
        )
        .is_err());
    }

    #[test]
    fn declaration_builtin_extractor_applies_indexed_registry_exclusions() {
        let source = r#"
m_names[OP_LIVE] = "live";
m_names[OP_INTERNAL] = "internal";
void plugin::get_op_names() {
    for (unsigned i = 0; i < m_names.size(); ++i)
        if (m_names[i] && i != OP_INTERNAL)
            op_names.push_back(builtin_name(std::string(m_names[i]), i));
}
"#;
        assert_eq!(
            extract_declaration_builtin_symbols(source, "synthetic.cpp").unwrap(),
            ["live".to_string()].into_iter().collect()
        );
    }

    #[test]
    fn declaration_builtin_extractor_binds_dynamic_signature_assignments() {
        let source = r#"
m_sigs[OP_LIVE] = alloc(psig, m, "live", 0, 0, nullptr, range);
auto* helper = alloc(psig, m, "not-a-registry-owner", 0, 0, nullptr, range);
m_sigs[OP_EMPTY] = nullptr;
void plugin::get_op_names() {
    op_names.push_back(builtin_name(m_sigs[i]->m_name.str(), i));
}
"#;
        assert_eq!(
            extract_declaration_builtin_symbols(source, "synthetic.cpp").unwrap(),
            ["live".to_string()].into_iter().collect()
        );
    }

    #[test]
    fn basic_decl_plugin_source_and_all_live_names_are_in_scope() {
        assert!(SELECTED_SOURCE_PATHS.contains(&"src/ast/ast.cpp"));
        assert!(DECLARATION_PLUGIN_PATHS.contains(&"src/ast/ast.cpp"));
        let source = r#"
sort_names.push_back(builtin_name("bool", BOOL_SORT));
sort_names.push_back(builtin_name("Proof", PROOF_SORT));
sort_names.push_back(builtin_name("Bool", BOOL_SORT));
op_names.push_back(builtin_name("true", OP_TRUE));
op_names.push_back(builtin_name("false", OP_FALSE));
op_names.push_back(builtin_name("=", OP_EQ));
op_names.push_back(builtin_name("distinct", OP_DISTINCT));
op_names.push_back(builtin_name("ite", OP_ITE));
op_names.push_back(builtin_name("if", OP_ITE));
op_names.push_back(builtin_name("and", OP_AND));
op_names.push_back(builtin_name("or", OP_OR));
op_names.push_back(builtin_name("xor", OP_XOR));
op_names.push_back(builtin_name("not", OP_NOT));
op_names.push_back(builtin_name("=>", OP_IMPLIES));
op_names.push_back(builtin_name("implies", OP_IMPLIES));
op_names.push_back(builtin_name("iff", OP_EQ));
op_names.push_back(builtin_name("if_then_else", OP_ITE));
op_names.push_back(builtin_name("&&", OP_AND));
op_names.push_back(builtin_name("||", OP_OR));
op_names.push_back(builtin_name("equals", OP_EQ));
op_names.push_back(builtin_name("equiv", OP_EQ));
"#;
        let expected = [
            "&&",
            "=",
            "=>",
            "Bool",
            "Proof",
            "and",
            "bool",
            "distinct",
            "equals",
            "equiv",
            "false",
            "if",
            "if_then_else",
            "iff",
            "implies",
            "ite",
            "not",
            "or",
            "true",
            "xor",
            "||",
        ]
        .into_iter()
        .map(str::to_string)
        .collect::<BTreeSet<_>>();
        assert_eq!(
            extract_declaration_builtin_symbols(source, "src/ast/ast.cpp").unwrap(),
            expected
        );
    }

    #[test]
    fn selected_sources_are_sorted_and_unique() {
        assert!(SELECTED_SOURCE_PATHS
            .windows(2)
            .all(|window| window[0] < window[1]));
    }

    #[test]
    fn registration_classifier_counts_are_closed_and_one_of() {
        assert_eq!(
            EXPECTED_REGISTRATION_CLASSIFICATION_COUNTS
                .iter()
                .map(|(_, count)| count)
                .sum::<usize>(),
            EXPECTED_REGISTRATION_SCAN_LINES
        );
        assert!(EXPECTED_REGISTRATION_CLASSIFICATION_COUNTS
            .windows(2)
            .all(|window| window[0].0 < window[1].0));
        assert_eq!(
            registration_disposition(
                "src/shell/main.cpp",
                "else if (strcmp(opt_name, \"-in\") == 0)"
            )
            .unwrap(),
            "observable.cli-option-dispatch"
        );
        assert_eq!(
            registration_disposition(
                "src/tactic/example.h",
                "ADD_TACTIC(\"example\", \"example tactic\", \"mk_example()\")"
            )
            .unwrap(),
            "observable.tactic-registration"
        );
    }

    #[test]
    fn registration_classifier_rejects_unknown_path_and_lexical_classes() {
        assert!(
            registration_disposition("src/new_component/example.cpp", "void install_cmd();")
                .is_err()
        );
        assert!(registration_disposition("src/tactic/example.cpp", "ordinary source row").is_err());
        assert!(registration_disposition("src/tactic/example.unknown", "tactic").is_err());
    }
}
