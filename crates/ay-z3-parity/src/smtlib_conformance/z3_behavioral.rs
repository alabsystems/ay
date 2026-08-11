// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, executable Z3 5.0.0 CLI transcript differential.
//!
//! This validator intentionally records mismatches.  The catalog is closed in
//! code and a receipt cannot pass by dropping a case, changing its comparator,
//! accepting an interrupted child, or substituting a different oracle.  AY and
//! Z3 run sequentially under the same single-job `_oom_guard.py` plan.

mod declaration_builtins;
mod parser_tokens;

use super::*;
use ay_frontend::SUPPORTED_TACTIC_NAMES;
use std::io::{BufRead as _, BufReader};
use std::process::{Child, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Arc};
use std::thread;
use std::time::Instant;

pub(super) const VALIDATOR_ID: &str = "builtin.z3-behavioral-transcripts-5.0.0.v1";

const DIMENSION_ID: &str = "overlay.z3-5.0.0";
const REQUIREMENT_ID: &str = "overlay.z3-5.0.0.behavioral-transcripts";
const DEFAULT_TIMEOUT_SECS: u64 = 10;
const FILE_PLACEHOLDER: &str = "{INPUT_FILE}";
const STREAM_PHASE_TIMEOUT: Duration = Duration::from_secs(2);
const STREAM_LIMIT: usize = 1024 * 1024;
const ARTIFACT_FILE_LIMIT: usize = 256;
const ARTIFACT_BYTE_LIMIT: u64 = 16 * 1024 * 1024;
const TACTIC_COUNT: usize = 118;
#[cfg(test)]
const Z3_5_HELP_FIXTURE_SHA256: &str =
    "26765e7d789867158b226672f183d9a28a1ce65d07a4ed46465b275a33f48e5b";
#[cfg(test)]
const Z3_5_HELP_SIMPLIFIER_FIXTURE_SHA256: &str =
    "b274b48cbd8722b061f8d69e0af7ff0e8734d06287c3e8a712369d66911c9c92";
#[cfg(test)]
const Z3_5_HELP_TACTIC_FIXTURE_SHA256: &str =
    "10b8bedc54c73b8943fae20aaee07b1117940cd38b86edba2183110facb29ca6";
const BASE_CASE_COUNT: usize = 338;
const EXPECTED_SOURCE_OWNER_COUNT: usize = z3_source_inventory::EXPECTED_OBSERVABLE_ITEMS;
const EXPECTED_CASE_COUNT: usize = BASE_CASE_COUNT + EXPECTED_SOURCE_OWNER_COUNT;
const EXPECTED_UNRESOLVED_COMMAND_OWNERS: usize = 57;
#[cfg(test)]
const EXPECTED_AUDITED_COMMAND_GAP_UNIVERSE_OWNERS: usize = 63;
const EXPECTED_UNRESOLVED_SOURCE_OWNERS: usize = 301;
const EXPECTED_AUDITED_GAP_UNIVERSE_OWNERS: usize = 496;
const EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNERS: usize = 0;
const EXPECTED_OWNERSHIP_SHA256: &str =
    "03c1110cf963723ebb37c64c292bb0435f1fc86487818a286a5799bb03121fac";
const EXPECTED_AUDITED_GAP_UNIVERSE_OWNERSHIP_SHA256: &str =
    "a11767c6a15546d1739add25a4e10ce5487269e58db88f8969e0a20c8c2c31d4";
#[cfg(test)]
const EXPECTED_AUDITED_COMMAND_GAP_UNIVERSE_OWNERSHIP_SHA256: &str =
    "80fa62d97c35766652f1841ae4dfe541aade80cdf2052ff754a7ace81c7f0260";
const EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNERSHIP_SHA256: &str =
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
const EXPECTED_UNRESOLVED_COMMAND_OWNER_KEYS: [(&str, &str); EXPECTED_UNRESOLVED_COMMAND_OWNERS] = [
    ("smt-command", "apply"),
    ("smt-command", "assert-soft"),
    ("smt-command", "assume"),
    ("smt-command", "check-sat-using"),
    ("smt-command", "dbg-bool-flat-rewriter"),
    ("smt-command", "dbg-bool-rewriter"),
    ("smt-command", "dbg-elim-and"),
    ("smt-command", "dbg-elim-unused-vars"),
    ("smt-command", "dbg-get-qbody"),
    ("smt-command", "dbg-instantiate"),
    ("smt-command", "dbg-instantiate-nested"),
    ("smt-command", "dbg-lt"),
    ("smt-command", "dbg-pp-var"),
    ("smt-command", "dbg-set"),
    ("smt-command", "dbg-set-next-id"),
    ("smt-command", "dbg-sexpr"),
    ("smt-command", "dbg-shift-vars"),
    ("smt-command", "dbg-size"),
    ("smt-command", "dbg-some-value"),
    ("smt-command", "dbg-subst"),
    ("smt-command", "dbg-th-rewriter"),
    ("smt-command", "dbg-translator"),
    ("smt-command", "dbg-used-vars"),
    ("smt-command", "declare-map"),
    ("smt-command", "declare-rel"),
    ("smt-command", "declare-tactic"),
    ("smt-command", "del"),
    ("smt-command", "display"),
    ("smt-command", "display-dimacs"),
    ("smt-command", "euf-project"),
    ("smt-command", "eufi"),
    ("smt-command", "eval"),
    ("smt-command", "get-consequences"),
    ("smt-command", "get-interpolant"),
    ("smt-command", "get-model"),
    ("smt-command", "get-objectives"),
    ("smt-command", "get-proof-graph"),
    ("smt-command", "get-user-tactics"),
    ("smt-command", "include"),
    ("smt-command", "infer"),
    ("smt-command", "labels"),
    ("smt-command", "maximize"),
    ("smt-command", "mbi"),
    ("smt-command", "mbp"),
    ("smt-command", "mbp-qel"),
    ("smt-command", "minimize"),
    ("smt-command", "model-add"),
    ("smt-command", "model-del"),
    ("smt-command", "prefer"),
    ("smt-command", "qe-lite"),
    ("smt-command", "qel"),
    ("smt-command", "query"),
    ("smt-command", "reset-preferences"),
    ("smt-command", "rule"),
    ("smt-command", "set-initial-value"),
    ("smt-command", "set-simplifier"),
    ("smt-command", "simplify"),
];
const RESOLVED_EXTENSION_COMMANDS: [&str; 6] = [
    "assert-not",
    "dbg-params",
    "declare-var",
    "help",
    "help-simplifier",
    "help-tactic",
];
const RESOLVED_INFO_KEYS: [&str; 11] = [
    ":?",
    ":all-statistics",
    ":assertion-stack-levels",
    ":authors",
    ":error-behavior",
    ":name",
    ":parameters",
    ":reason-unknown",
    ":rlimit",
    ":status",
    ":version",
];
const RESOLVED_OPTION_KEYS: [&str; 16] = [
    ":error-behavior",
    ":global-declarations",
    ":global-decls",
    ":int-real-coercions",
    ":interactive-mode",
    ":numeral-as-real",
    ":print-success",
    ":print-warning",
    ":produce-assertions",
    ":produce-assignments",
    ":produce-models",
    ":produce-proofs",
    ":produce-unsat-assumptions",
    ":produce-unsat-cores",
    ":random-seed",
    ":verbosity",
];
const RESOLVED_LOGIC_RECOGNIZER_LITERALS: [&str; 24] = [
    "A", "ALL", "BV", "DT", "FP", "FS", "HORN", "HO_ALL", "IDL", "LIA", "LIRA", "LRA", "NIA",
    "NIRA", "NRA", "QF_A", "QF_BVRE", "QF_FD", "QF_S", "QF_SLIA", "QF_SNIA", "RDL", "SMTFD", "UF",
];
const UNRESOLVED_SOURCE_CATEGORIES: [&str; 5] = [
    "declaration-builtin",
    "logic-strategy-alias",
    "smt-info-key",
    "smt-option-key",
    "smt-parser-token",
];
const EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNER_KEYS: [(&str, &str);
    EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNERS] = [];

const PROBE_NAMES: [&str; 42] = [
    "ackr-bound-probe",
    "arith-avg-bw",
    "arith-avg-deg",
    "arith-max-bw",
    "arith-max-deg",
    "depth",
    "has-patterns",
    "has-quantifiers",
    "is-ilp",
    "is-lia",
    "is-lira",
    "is-lra",
    "is-nia",
    "is-nira",
    "is-nra",
    "is-pb",
    "is-propositional",
    "is-qfaufbv",
    "is-qfauflia",
    "is-qfbv",
    "is-qfbv-eq",
    "is-qffp",
    "is-qffpbv",
    "is-qffplra",
    "is-qflia",
    "is-qflira",
    "is-qflra",
    "is-qfnia",
    "is-qfnra",
    "is-qfufnra",
    "is-quasi-pb",
    "is-unbounded",
    "memory",
    "num-arith-consts",
    "num-bool-consts",
    "num-bv-consts",
    "num-consts",
    "num-exprs",
    "produce-model",
    "produce-proofs",
    "produce-unsat-cores",
    "size",
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Comparator {
    /// Compare exit status and both byte streams without transformation.
    ExactBytes,
    /// Preserve all syntax, keys, ordering, and diagnostics, replacing only
    /// numeric statistic values whose wall/allocation values are unstable.
    Statistics,
    /// Preserve verbose component trace structure while eliding only numeric
    /// telemetry (time, memory, counters, and identifiers).
    ComponentTrace,
}

impl Comparator {
    const fn id(self) -> &'static str {
        match self {
            Self::ExactBytes => "exact-exit-stdout-stderr-bytes/v1",
            Self::Statistics => "stats-shape-with-only-numeric-values-elided/v1",
            Self::ComponentTrace => "component-trace-with-numeric-telemetry-elided/v1",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RunStyle {
    Batch,
    File,
    Streaming,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ArtifactPolicy {
    None,
    IsolatedDirectory,
}

impl ArtifactPolicy {
    const fn id(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::IsolatedDirectory => "isolated-directory-exact-manifest/v1",
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct SourceOwner {
    category: String,
    name: String,
}

impl SourceOwner {
    fn canonical_line(&self) -> String {
        format!("{}\t{}\n", self.category, self.name)
    }

    fn display(&self) -> String {
        format!("{}\t{}", self.category, self.name)
    }
}

fn source_proven_no_effect_reason(_owner: &SourceOwner) -> Option<&'static str> {
    // No Z3 5.0.0 CLI owner currently receives no-effect credit. A future
    // claim must first retain every relevant source blob and add executable
    // occurrence and call-site predicates to the source snapshot validator.
    None
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EffectRequirement {
    /// Executing the command/component is itself a semantic observation.
    Inherent,
    /// The authenticated Z3 candidate must observably differ from a baseline.
    OracleDiffersFromBaseline,
    /// The exact pinned source proves that this advertised CLI parameter has
    /// no reachable advertised effect. Candidate and baseline must execute
    /// cleanly and agree exactly, and AY must agree with that no-effect result.
    SourceProvenNoEffect,
    /// No safe distinguishing witness is currently known. This row is always
    /// non-PASS even if AY happens to reproduce the candidate transcript.
    Unresolved,
}

impl EffectRequirement {
    const fn id(self) -> &'static str {
        match self {
            Self::Inherent => "inherent-semantic-execution/v1",
            Self::OracleDiffersFromBaseline => "oracle-differs-from-baseline/v1",
            Self::SourceProvenNoEffect => "source-proven-no-cli-effect/v1",
            Self::Unresolved => "explicit-unresolved-no-safe-witness/v1",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct BaselineSpec {
    args: Vec<String>,
    input: Vec<u8>,
    style: RunStyle,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CaseSpec {
    id: String,
    oracle_args: Vec<String>,
    subject_args: Vec<String>,
    input: Vec<u8>,
    comparator: Comparator,
    style: RunStyle,
    file_extension: String,
    artifact_policy: ArtifactPolicy,
    source_owner: Option<SourceOwner>,
    effect_requirement: EffectRequirement,
    oracle_baseline: Option<BaselineSpec>,
}

impl CaseSpec {
    fn source_effect_reason(&self) -> &'static str {
        if self.effect_requirement != EffectRequirement::SourceProvenNoEffect {
            return "none";
        }
        self.source_owner
            .as_ref()
            .and_then(source_proven_no_effect_reason)
            .unwrap_or("missing-source-proven-no-effect-reason")
    }

    fn descriptor(&self) -> String {
        format!(
            "id={};style={:?};file-extension={:?};artifact-policy={};oracle-args={:?};subject-args={:?};stdin-sha256={};comparator={};source-owner={:?};effect={};source-effect-reason={};baseline={:?}",
            self.id,
            self.style,
            self.file_extension,
            self.artifact_policy.id(),
            self.oracle_args,
            self.subject_args,
            sha256_bytes(&self.input),
            self.comparator.id(),
            self.source_owner,
            self.effect_requirement.id(),
            self.source_effect_reason(),
            self.oracle_baseline,
        )
    }

    fn input_sha256(&self) -> String {
        sha256_bytes(self.descriptor().as_bytes())
    }

    fn expected(&self) -> String {
        format!(
            "source-owner={};effect={};artifact-policy={};source-effect-reason={};pinned Z3 5.0.0 and manifest-bound AY agree under {}; oracle-args={:?}; subject-args={:?}; stdin-sha256={}; both guarded, complete, untruncated, UTF-8",
            self.source_owner
                .as_ref()
                .map_or_else(|| "none".to_string(), SourceOwner::display),
            self.effect_requirement.id(),
            self.artifact_policy.id(),
            self.source_effect_reason(),
            self.comparator.id(),
            self.oracle_args,
            self.subject_args,
            sha256_bytes(&self.input)
        )
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Execution {
    ay_sha256: String,
    z3_sha256: String,
    resource_envelope: String,
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ArtifactObservation {
    path: String,
    size: u64,
    sha256: String,
}

#[derive(Clone, Debug)]
struct Captured {
    exit_code: Option<i32>,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    stdin_complete: bool,
    timed_out: bool,
    memout: bool,
    stdout_truncated: bool,
    stderr_truncated: bool,
    artifacts: Vec<ArtifactObservation>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct StreamDriverReport {
    exit_code: Option<i32>,
    stdout: String,
    stderr: String,
    phase_complete: bool,
    target_timed_out: bool,
    stdout_truncated: bool,
    stderr_truncated: bool,
    read_error: bool,
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut snapshot_path: Option<PathBuf> = None;
    let mut ay_override: Option<PathBuf> = None;
    let mut z3_override: Option<PathBuf> = None;
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
            "--ay" => {
                index += 1;
                ay_override = Some(PathBuf::from(args.get(index).ok_or("--ay needs a path")?));
            }
            "--z3" => {
                index += 1;
                z3_override = Some(PathBuf::from(args.get(index).ok_or("--z3 needs a path")?));
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
                if timeout_secs == 0 || timeout_secs > 3600 {
                    return Err("--timeout must be between 1 and 3600 seconds".to_string());
                }
            }
            flag if flag.starts_with("--") => {
                return Err(format!("unknown z3-behavioral flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("z3-behavioral takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }

    let manifest = manifest.ok_or("z3-behavioral needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("z3-behavioral requires --receipt <path>")?;
    let snapshot_path = snapshot_path
        .ok_or("z3-behavioral requires --source-snapshot <path> from z3-source-snapshot")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let envelope = loaded
        .contract
        .resource_envelope
        .as_deref()
        .ok_or("z3-behavioral requires contract.resource_envelope")?;
    let parsed = parse_resource_envelope(envelope)?;
    if parsed.jobs != 1 {
        return Err("z3-behavioral requires a one-job resource envelope".to_string());
    }
    if parsed.timeout != Duration::from_secs(timeout_secs) {
        return Err(format!(
            "--timeout does not match contract.resource_envelope: expected {:?}",
            parsed.timeout
        ));
    }
    let dimension = overlay_dimension(&loaded.contract)?;
    let subject = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("z3-behavioral requires subject.ay_executable")?;
    let ay = ay_override.unwrap_or_else(|| artifact_path(&loaded.base, &subject.path));
    let z3 = z3_override.unwrap_or_else(|| {
        PathBuf::from(&loaded.contract.profile.z3_overlay.reference_executable.path)
    });
    let loaded_source =
        z3_source_inventory::load_snapshot_for_run(&loaded.contract, &loaded.base, &snapshot_path)?;
    let output_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let execution = execute(
        &loaded.contract,
        &ay,
        &z3,
        &loaded_source.snapshot,
        Duration::from_secs(timeout_secs),
        Some(envelope),
    )?;
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
        dimension_id: dimension.id.clone(),
        requirement_ids: vec![REQUIREMENT_ID.to_string()],
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: VALIDATOR_ID.to_string(),
            kind: ValidatorKind::Z3Differential,
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
        "z3-behavioral={} receipt={} sha256={}",
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
    if receipt.validator.kind != ValidatorKind::Z3Differential
        || context.dimension.id != DIMENSION_ID
        || receipt.requirement_ids != [REQUIREMENT_ID.to_string()]
        || !receipt.exhaustive
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
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
    {
        return Err(format!(
            "{VALIDATOR_ID} has invalid kind, dimension, coverage, exhaustive flag, or bindings"
        ));
    }
    let [source_input] = receipt.reference_inputs.as_slice() else {
        return Err(format!(
            "{VALIDATOR_ID} requires exactly one authenticated Z3 source snapshot"
        ));
    };
    let source_snapshot = z3_source_inventory::load_bound_snapshot(
        source_input,
        context.manifest_dir,
        &context.contract.profile,
    )?;
    validate_receipt_rows(receipt)?;
    if context.mode.replays_registered_validators() {
        let envelope = receipt
            .resource_envelope
            .as_deref()
            .ok_or("z3-behavioral receipt has no resource envelope")?;
        let parsed = parse_resource_envelope(envelope)?;
        if parsed.jobs != 1 {
            return Err("z3-behavioral receipts require a one-job envelope".to_string());
        }
        let subject = context
            .contract
            .subject
            .ay_executable
            .as_ref()
            .ok_or("z3-behavioral replay requires subject.ay_executable")?;
        let live = execute(
            context.contract,
            &artifact_path(context.manifest_dir, &subject.path),
            Path::new(
                &context
                    .contract
                    .profile
                    .z3_overlay
                    .reference_executable
                    .path,
            ),
            &source_snapshot,
            parsed.timeout,
            Some(envelope),
        )?;
        if receipt.result != live.result
            || receipt.cases != live.cases
            || receipt.case_results != live.case_results
        {
            return Err(format!(
                "{VALIDATOR_ID} receipt does not match a fresh authenticated differential replay"
            ));
        }
    }
    Ok(())
}

fn validate_receipt_rows(receipt: &ValidatorReceipt) -> Result<(), String> {
    if receipt.case_results.len() != EXPECTED_CASE_COUNT {
        return Err(format!(
            "{VALIDATOR_ID} requires exactly {EXPECTED_CASE_COUNT} detailed cases, got {}",
            receipt.case_results.len()
        ));
    }
    if !receipt
        .case_results
        .windows(2)
        .all(|pair| pair[0].id < pair[1].id)
    {
        return Err(format!(
            "{VALIDATOR_ID} detailed cases are not exact and sorted"
        ));
    }
    let mut owners = Vec::new();
    let mut unresolved_owners = Vec::new();
    let mut logic_recognizer_owners = Vec::new();
    let mut resolved_extension_command_owners = Vec::new();
    let mut resolved_declaration_builtin_owners = Vec::new();
    let mut resolved_info_key_owners = Vec::new();
    let mut resolved_option_key_owners = Vec::new();
    let mut resolved_parser_token_owners = Vec::new();
    let mut source_proven_no_effect_owners = Vec::new();
    for row in &receipt.case_results {
        if row.process.is_none()
            || row.stdout.is_none()
            || row.stderr.is_none()
            || row.input_sha256.len() != 64
            || !row
                .input_sha256
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit())
        {
            return Err(format!(
                "{VALIDATOR_ID} case identity, transcript, or process binding drift at {}",
                row.id
            ));
        }
        let (owner, effect_and_rest) = row
            .expected
            .strip_prefix("source-owner=")
            .and_then(|rest| rest.split_once(";effect="))
            .ok_or_else(|| {
                format!(
                    "{VALIDATOR_ID} case has no ownership declaration: {}",
                    row.id
                )
            })?;
        let (effect, artifact_and_rest) = effect_and_rest
            .split_once(";artifact-policy=")
            .ok_or_else(|| {
                format!(
                    "{VALIDATOR_ID} case has no effect or artifact declaration: {}",
                    row.id
                )
            })?;
        let (artifact_policy, reason_and_rest) = artifact_and_rest
            .split_once(";source-effect-reason=")
            .ok_or_else(|| {
                format!(
                    "{VALIDATOR_ID} case has no artifact or source-effect declaration: {}",
                    row.id
                )
            })?;
        let (source_effect_reason, _) =
            reason_and_rest
                .split_once(";pinned Z3 5.0.0")
                .ok_or_else(|| {
                    format!(
                        "{VALIDATOR_ID} case has no bounded source-effect reason: {}",
                        row.id
                    )
                })?;
        if ![
            EffectRequirement::Inherent.id(),
            EffectRequirement::OracleDiffersFromBaseline.id(),
            EffectRequirement::SourceProvenNoEffect.id(),
            EffectRequirement::Unresolved.id(),
        ]
        .contains(&effect)
        {
            return Err(format!(
                "{VALIDATOR_ID} case has a foreign effect declaration: {}",
                row.id
            ));
        }
        if ![
            ArtifactPolicy::None.id(),
            ArtifactPolicy::IsolatedDirectory.id(),
        ]
        .contains(&artifact_policy)
        {
            return Err(format!(
                "{VALIDATOR_ID} case has a foreign artifact policy: {}",
                row.id
            ));
        }
        if owner != "none" {
            let (category, name) = owner
                .split_once('\t')
                .ok_or_else(|| format!("{VALIDATOR_ID} malformed source owner at {}", row.id))?;
            let owner = SourceOwner {
                category: category.to_string(),
                name: name.to_string(),
            };
            if row.id != owned_case_id(&owner) {
                return Err(format!(
                    "{VALIDATOR_ID} source owner and case identity drift at {}",
                    row.id
                ));
            }
            if effect == EffectRequirement::Unresolved.id() {
                unresolved_owners.push(owner.clone());
            }
            if owner.category == "logic-recognizer-literal" {
                if effect != EffectRequirement::OracleDiffersFromBaseline.id() {
                    return Err(format!(
                        "{VALIDATOR_ID} logic-recognizer owner lacks a distinguishing witness at {}",
                        row.id
                    ));
                }
                logic_recognizer_owners.push(owner.clone());
            }
            if owner.category == "smt-command"
                && RESOLVED_EXTENSION_COMMANDS.contains(&owner.name.as_str())
            {
                if effect != EffectRequirement::OracleDiffersFromBaseline.id() {
                    return Err(format!(
                        "{VALIDATOR_ID} resolved extension command lacks a distinguishing witness at {}",
                        row.id
                    ));
                }
                resolved_extension_command_owners.push(owner.clone());
            }
            if owner.category == "declaration-builtin"
                && declaration_builtins::semantic_predicate(&owner.name).is_some()
            {
                if effect != EffectRequirement::OracleDiffersFromBaseline.id() {
                    return Err(format!(
                        "{VALIDATOR_ID} resolved declaration builtin lacks a semantic witness at {}",
                        row.id
                    ));
                }
                resolved_declaration_builtin_owners.push(owner.clone());
            }
            if owner.category == "smt-info-key" && RESOLVED_INFO_KEYS.contains(&owner.name.as_str())
            {
                if effect != EffectRequirement::OracleDiffersFromBaseline.id() {
                    return Err(format!(
                        "{VALIDATOR_ID} resolved info key lacks a distinguishing witness at {}",
                        row.id
                    ));
                }
                resolved_info_key_owners.push(owner.clone());
            }
            if owner.category == "smt-option-key"
                && RESOLVED_OPTION_KEYS.contains(&owner.name.as_str())
            {
                if effect != EffectRequirement::OracleDiffersFromBaseline.id() {
                    return Err(format!(
                        "{VALIDATOR_ID} resolved option key lacks a distinguishing witness at {}",
                        row.id
                    ));
                }
                resolved_option_key_owners.push(owner.clone());
            }
            if owner.category == "smt-parser-token"
                && parser_tokens::semantic_witness(&owner.name).is_some()
            {
                if effect != EffectRequirement::OracleDiffersFromBaseline.id() {
                    return Err(format!(
                        "{VALIDATOR_ID} resolved parser token lacks a semantic witness at {}",
                        row.id
                    ));
                }
                resolved_parser_token_owners.push(owner.clone());
            }
            let expected_source_effect_reason =
                if effect == EffectRequirement::SourceProvenNoEffect.id() {
                    source_proven_no_effect_reason(&owner).ok_or_else(|| {
                        format!(
                            "{VALIDATOR_ID} case has no exact source-proven no-effect anchor: {}",
                            row.id
                        )
                    })?
                } else {
                    "none"
                };
            if source_effect_reason != expected_source_effect_reason {
                return Err(format!(
                    "{VALIDATOR_ID} source-effect reason drift at {}",
                    row.id
                ));
            }
            if effect == EffectRequirement::SourceProvenNoEffect.id() {
                source_proven_no_effect_owners.push(owner.clone());
            }
            owners.push(owner);
        } else if source_effect_reason != "none" {
            return Err(format!(
                "{VALIDATOR_ID} unowned case has a source-effect reason at {}",
                row.id
            ));
        }
        if effect == EffectRequirement::Unresolved.id() && row.outcome == ValidatorCaseOutcome::Pass
        {
            return Err(format!(
                "{VALIDATOR_ID} unresolved behavioral owner fabricated PASS at {}",
                row.id
            ));
        }
    }
    owners.sort();
    if owners.len() != EXPECTED_SOURCE_OWNER_COUNT
        || owners.windows(2).any(|pair| pair[0] == pair[1])
        || sha256_bytes(
            owners
                .iter()
                .map(SourceOwner::canonical_line)
                .collect::<Vec<_>>()
                .concat()
                .as_bytes(),
        ) != EXPECTED_OWNERSHIP_SHA256
    {
        return Err(format!(
            "{VALIDATOR_ID} does not bind every authenticated source item to exactly one behavioral owner"
        ));
    }
    unresolved_owners.sort();
    if unresolved_owners.len() != EXPECTED_UNRESOLVED_SOURCE_OWNERS {
        return Err(format!(
            "{VALIDATOR_ID} explicit unresolved source-owner inventory drift"
        ));
    }
    logic_recognizer_owners.sort();
    let expected_logic_recognizer_owners = RESOLVED_LOGIC_RECOGNIZER_LITERALS
        .iter()
        .map(|name| SourceOwner {
            category: "logic-recognizer-literal".to_string(),
            name: (*name).to_string(),
        })
        .collect::<Vec<_>>();
    if logic_recognizer_owners != expected_logic_recognizer_owners {
        return Err(format!(
            "{VALIDATOR_ID} resolved logic-recognizer owner inventory drift"
        ));
    }
    resolved_extension_command_owners.sort();
    let expected_resolved_extension_command_owners = RESOLVED_EXTENSION_COMMANDS
        .iter()
        .map(|name| SourceOwner {
            category: "smt-command".to_string(),
            name: (*name).to_string(),
        })
        .collect::<Vec<_>>();
    if resolved_extension_command_owners != expected_resolved_extension_command_owners {
        return Err(format!(
            "{VALIDATOR_ID} resolved extension-command owner inventory drift"
        ));
    }
    resolved_declaration_builtin_owners.sort();
    let expected_resolved_declaration_builtin_owners = declaration_builtins::semantic_owner_names()
        .map(|name| SourceOwner {
            category: "declaration-builtin".to_string(),
            name: name.to_string(),
        })
        .collect::<Vec<_>>();
    if resolved_declaration_builtin_owners != expected_resolved_declaration_builtin_owners {
        return Err(format!(
            "{VALIDATOR_ID} resolved declaration-builtin owner inventory drift"
        ));
    }
    resolved_info_key_owners.sort();
    let expected_resolved_info_key_owners = RESOLVED_INFO_KEYS
        .iter()
        .map(|name| SourceOwner {
            category: "smt-info-key".to_string(),
            name: (*name).to_string(),
        })
        .collect::<Vec<_>>();
    if resolved_info_key_owners != expected_resolved_info_key_owners {
        return Err(format!(
            "{VALIDATOR_ID} resolved info-key owner inventory drift"
        ));
    }
    resolved_option_key_owners.sort();
    let expected_resolved_option_key_owners = RESOLVED_OPTION_KEYS
        .iter()
        .map(|name| SourceOwner {
            category: "smt-option-key".to_string(),
            name: (*name).to_string(),
        })
        .collect::<Vec<_>>();
    if resolved_option_key_owners != expected_resolved_option_key_owners {
        return Err(format!(
            "{VALIDATOR_ID} resolved option-key owner inventory drift"
        ));
    }
    resolved_parser_token_owners.sort();
    let expected_resolved_parser_token_owners = parser_tokens::semantic_owner_names()
        .map(|name| SourceOwner {
            category: "smt-parser-token".to_string(),
            name: name.to_string(),
        })
        .collect::<Vec<_>>();
    if resolved_parser_token_owners != expected_resolved_parser_token_owners {
        return Err(format!(
            "{VALIDATOR_ID} resolved parser-token owner inventory drift"
        ));
    }
    let mut audited_gap_universe_owners = unresolved_owners;
    audited_gap_universe_owners.extend(logic_recognizer_owners);
    audited_gap_universe_owners.extend(resolved_extension_command_owners);
    audited_gap_universe_owners.extend(resolved_declaration_builtin_owners);
    audited_gap_universe_owners.extend(resolved_info_key_owners);
    audited_gap_universe_owners.extend(resolved_option_key_owners);
    audited_gap_universe_owners.extend(resolved_parser_token_owners);
    audited_gap_universe_owners.sort();
    if audited_gap_universe_owners.len() != EXPECTED_AUDITED_GAP_UNIVERSE_OWNERS
        || sha256_bytes(
            audited_gap_universe_owners
                .iter()
                .map(SourceOwner::canonical_line)
                .collect::<Vec<_>>()
                .concat()
                .as_bytes(),
        ) != EXPECTED_AUDITED_GAP_UNIVERSE_OWNERSHIP_SHA256
    {
        return Err(format!(
            "{VALIDATOR_ID} authenticated audited-gap universe drift"
        ));
    }
    source_proven_no_effect_owners.sort();
    if source_proven_no_effect_owners.len() != EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNERS
        || sha256_bytes(
            source_proven_no_effect_owners
                .iter()
                .map(SourceOwner::canonical_line)
                .collect::<Vec<_>>()
                .concat()
                .as_bytes(),
        ) != EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNERSHIP_SHA256
    {
        return Err(format!(
            "{VALIDATOR_ID} source-proven no-effect owner inventory drift"
        ));
    }
    Ok(())
}

fn execute(
    contract: &Contract,
    ay_source: &Path,
    z3_source: &Path,
    source_snapshot: &z3_source_inventory::Z3SourceSnapshot,
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<Execution, String> {
    if timeout.is_zero() || timeout > Duration::from_hours(1) {
        return Err("z3-behavioral timeout must be between 1ns and 3600 seconds".to_string());
    }
    let subject = contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("z3-behavioral requires subject.ay_executable")?;
    let z3_profile = &contract.profile.z3_overlay.reference_executable;
    let staged_ay = stage_authenticated_executable(ay_source, &subject.sha256, "AY executable")?;
    let staged_z3 =
        stage_authenticated_executable(z3_source, &z3_profile.sha256, "Z3 5.0.0 executable")?;
    let repo_root = locate_repo_root()?;
    let resources = PlannedResources::plan(
        &repo_root,
        1,
        "ay-z3-parity smtlib-conformance z3-behavioral",
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
                "live z3-behavioral replay resource envelope drift: expected {expected:?}, got {resource_envelope:?}"
            ));
        }
    }

    let observable_items =
        discover_observable_items(&resources, &staged_z3.path, source_snapshot, timeout)?;
    let catalog = case_catalog(&observable_items)?;

    let input_directory = tempfile::Builder::new()
        .prefix("ay-z3-behavioral-input-")
        .tempdir()
        .map_err(|error| format!("creating behavioral input directory: {error}"))?;
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let mut rows = Vec::with_capacity(catalog.len());
    for (ordinal, spec) in catalog.iter().enumerate() {
        let shared_input_path = input_directory
            .path()
            .join(format!("case-{ordinal:04}.{}", spec.file_extension));
        let isolated = spec.artifact_policy == ArtifactPolicy::IsolatedDirectory;
        let relative_input = PathBuf::from(format!("input.{}", spec.file_extension));
        let prepare = |role: &str, style: RunStyle, input: &[u8]| {
            if !isolated {
                if style == RunStyle::File {
                    fs::write(&shared_input_path, input).map_err(|error| {
                        format!("writing {}: {error}", shared_input_path.display())
                    })?;
                }
                return Ok((shared_input_path.clone(), None));
            }
            let directory = input_directory
                .path()
                .join(format!("case-{ordinal:04}"))
                .join(role);
            fs::create_dir_all(&directory).map_err(|error| {
                format!(
                    "creating isolated artifact directory {}: {error}",
                    directory.display()
                )
            })?;
            if style == RunStyle::File {
                let path = directory.join(&relative_input);
                fs::write(&path, input)
                    .map_err(|error| format!("writing {}: {error}", path.display()))?;
            }
            Ok::<_, String>((relative_input.clone(), Some(directory)))
        };
        let (oracle_input_path, oracle_directory) = prepare("oracle", spec.style, &spec.input)?;
        let (subject_input_path, subject_directory) = prepare("subject", spec.style, &spec.input)?;
        let oracle_args = resolved_args(&spec.oracle_args, &oracle_input_path);
        let subject_args = resolved_args(&spec.subject_args, &subject_input_path);
        let oracle = run_target(
            &resources,
            &current_exe,
            &staged_z3.path,
            &oracle_args,
            &spec.input,
            spec.style,
            oracle_directory.as_deref(),
            (isolated && spec.style == RunStyle::File).then_some(relative_input.as_path()),
            timeout,
            &format!("Z3 5.0.0 behavioral case {}", spec.id),
        )?;
        let ay = run_target(
            &resources,
            &current_exe,
            &staged_ay.path,
            &subject_args,
            &spec.input,
            spec.style,
            subject_directory.as_deref(),
            (isolated && spec.style == RunStyle::File).then_some(relative_input.as_path()),
            timeout,
            &format!("AY behavioral case {}", spec.id),
        )?;
        let oracle_baseline = if let Some(baseline) = &spec.oracle_baseline {
            let (baseline_input_path, baseline_directory) =
                prepare("baseline", baseline.style, &baseline.input)?;
            let baseline_args = resolved_args(&baseline.args, &baseline_input_path);
            Some(run_target(
                &resources,
                &current_exe,
                &staged_z3.path,
                &baseline_args,
                &baseline.input,
                baseline.style,
                baseline_directory.as_deref(),
                (isolated && baseline.style == RunStyle::File).then_some(relative_input.as_path()),
                timeout,
                &format!("Z3 5.0.0 effect baseline for {}", spec.id),
            )?)
        } else {
            None
        };
        rows.push(row_from_pair(spec, oracle, ay, oracle_baseline));
    }
    let ay_post = sha256_file(&staged_ay.path, "staged AY after behavioral probes")?;
    let z3_post = sha256_file(&staged_z3.path, "staged Z3 after behavioral probes")?;
    if ay_post != subject.sha256 || z3_post != z3_profile.sha256 {
        return Err("authenticated executable bytes changed during behavioral probes".to_string());
    }
    let expected_ids = catalog
        .iter()
        .map(|case| case.id.clone())
        .collect::<Vec<_>>();
    let actual_ids = rows.iter().map(|row| row.id.clone()).collect::<Vec<_>>();
    if actual_ids != expected_ids {
        return Err("internal z3-behavioral case inventory drift".to_string());
    }
    let cases = case_counts_from_rows(&rows)?;
    Ok(Execution {
        ay_sha256: subject.sha256.clone(),
        z3_sha256: z3_profile.sha256.clone(),
        resource_envelope,
        result: overall_validator_result(&rows),
        cases,
        case_results: rows,
    })
}

fn resolved_args(args: &[String], input_path: &Path) -> Vec<String> {
    let replacement = input_path.to_string_lossy();
    args.iter()
        .map(|arg| arg.replace(FILE_PLACEHOLDER, &replacement))
        .collect()
}

fn discover_observable_items(
    resources: &PlannedResources,
    z3: &Path,
    snapshot: &z3_source_inventory::Z3SourceSnapshot,
    timeout: Duration,
) -> Result<Vec<z3_source_inventory::ObservableItem>, String> {
    let capture = |id: &str, args: &[&str], input: &[u8]| -> Result<String, String> {
        let output = resources
            .run_external_transcript(
                z3,
                args.iter().copied(),
                input,
                timeout,
                &format!("Z3 5.0.0 behavioral ownership discovery: {id}"),
            )
            .map_err(|error| error.to_string())?;
        let exit_code = output.status.and_then(|status| status.code());
        let stderr = String::from_utf8(output.stderr)
            .map_err(|_| format!("Z3 ownership discovery {id} emitted non-UTF-8 stderr"))?;
        let stdout = String::from_utf8(output.stdout)
            .map_err(|_| format!("Z3 ownership discovery {id} emitted non-UTF-8 stdout"))?;
        if exit_code != Some(0)
            || !output.stdin_complete
            || output.timed_out
            || output.memout
            || output.stdout_truncated
            || output.stderr_truncated
            || !stderr.is_empty()
        {
            return Err(format!(
                "Z3 ownership discovery {id} was not a clean complete process: exit={exit_code:?}, stderr={stderr:?}"
            ));
        }
        Ok(stdout)
    };

    let cli_help = capture("cli-help", &["-h"], b"")?;
    let command_help = capture("command-help", &["-in"], b"(help)\n(exit)\n")?;
    let tactics = capture("tactics", &["-tactics", "-in"], b"")?;
    let probes = capture("probes", &["-probes", "-in"], b"")?;
    let simplifiers = capture("simplifiers", &["-simplifiers", "-in"], b"")?;
    let parameters = capture("parameters", &["-p"], b"")?;
    let parameter_descriptions = capture("parameter-descriptions", &["-pd"], b"")?;
    z3_source_inventory::extract_observable_items_from_transcripts(
        snapshot,
        z3_source_inventory::ObservableTranscripts {
            cli_help: &cli_help,
            command_help: &command_help,
            tactics: &tactics,
            probes: &probes,
            simplifiers: &simplifiers,
            parameters: &parameters,
            parameter_descriptions: &parameter_descriptions,
        },
    )
}

fn run_target(
    resources: &PlannedResources,
    driver: &Path,
    target: &Path,
    args: &[String],
    input: &[u8],
    style: RunStyle,
    working_directory: Option<&Path>,
    input_file: Option<&Path>,
    timeout: Duration,
    label: &str,
) -> Result<Captured, String> {
    if style != RunStyle::Streaming {
        let output = if let Some(directory) = working_directory {
            let mut wrapped_args = vec![
                std::ffi::OsString::from("-C"),
                directory.as_os_str().to_owned(),
                target.as_os_str().to_owned(),
            ];
            wrapped_args.extend(
                args.iter()
                    .map(|argument| std::ffi::OsString::from(argument.as_str())),
            );
            resources.run_external_transcript("/usr/bin/env", &wrapped_args, input, timeout, label)
        } else {
            resources.run_external_transcript(target, args, input, timeout, label)
        }
        .map_err(|error| error.to_string())?;
        let mut captured = Captured::from(output);
        if let Some(directory) = working_directory {
            captured.artifacts = capture_artifact_manifest(directory, input_file)?;
        }
        return Ok(captured);
    }
    if working_directory.is_some() || input_file.is_some() {
        return Err("streaming cases cannot request artifact isolation".to_string());
    }
    let mut driver_args = vec![
        "smtlib-conformance".to_string(),
        "run".to_string(),
        "z3-behavioral-stream-driver".to_string(),
        "--target".to_string(),
        target.to_string_lossy().into_owned(),
    ];
    for arg in args {
        driver_args.push("--target-arg".to_string());
        driver_args.push(arg.clone());
    }
    let outer = resources
        .run_external_transcript(driver, &driver_args, b"", timeout, label)
        .map_err(|error| error.to_string())?;
    if outer.memout || outer.timed_out || outer.stdout_truncated || outer.stderr_truncated {
        return Ok(Captured::from(outer));
    }
    let report: StreamDriverReport = serde_json::from_slice(&outer.stdout)
        .map_err(|error| format!("{label}: decoding stream-driver report: {error}"))?;
    let driver_stderr = String::from_utf8(outer.stderr)
        .map_err(|_| format!("{label}: stream driver emitted non-UTF-8 stderr"))?;
    if outer.status.and_then(|status| status.code()) != Some(0) || !driver_stderr.is_empty() {
        return Err(format!(
            "{label}: stream driver failed: status={:?}, stderr={driver_stderr:?}",
            outer.status.and_then(|status| status.code())
        ));
    }
    Ok(Captured {
        exit_code: report.exit_code,
        stdout: report.stdout.into_bytes(),
        stderr: report.stderr.into_bytes(),
        stdin_complete: report.phase_complete && !report.read_error,
        timed_out: report.target_timed_out,
        memout: false,
        stdout_truncated: report.stdout_truncated,
        stderr_truncated: report.stderr_truncated,
        artifacts: Vec::new(),
    })
}

impl From<GuardedTranscriptOutput> for Captured {
    fn from(output: GuardedTranscriptOutput) -> Self {
        Self {
            exit_code: output.status.and_then(|status| status.code()),
            stdout: output.stdout,
            stderr: output.stderr,
            stdin_complete: output.stdin_complete,
            timed_out: output.timed_out,
            memout: output.memout,
            stdout_truncated: output.stdout_truncated,
            stderr_truncated: output.stderr_truncated,
            artifacts: Vec::new(),
        }
    }
}

fn capture_artifact_manifest(
    root: &Path,
    excluded_input: Option<&Path>,
) -> Result<Vec<ArtifactObservation>, String> {
    fn visit(
        root: &Path,
        directory: &Path,
        excluded_input: Option<&Path>,
        total_bytes: &mut u64,
        artifacts: &mut Vec<ArtifactObservation>,
    ) -> Result<(), String> {
        let mut entries = fs::read_dir(directory)
            .map_err(|error| {
                format!(
                    "reading artifact directory {}: {error}",
                    directory.display()
                )
            })?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| {
                format!("reading artifact entry in {}: {error}", directory.display())
            })?;
        entries.sort_by_key(fs::DirEntry::file_name);
        for entry in entries {
            let path = entry.path();
            let relative = path
                .strip_prefix(root)
                .map_err(|_| "artifact escaped its isolated directory".to_string())?;
            if excluded_input.is_some_and(|input| relative == input) {
                continue;
            }
            let metadata = fs::symlink_metadata(&path).map_err(|error| {
                format!("reading artifact metadata {}: {error}", path.display())
            })?;
            if metadata.file_type().is_symlink() {
                return Err(format!(
                    "artifact process created unsupported symlink {}",
                    relative.display()
                ));
            }
            if metadata.is_dir() {
                visit(root, &path, excluded_input, total_bytes, artifacts)?;
                continue;
            }
            if !metadata.is_file() {
                return Err(format!(
                    "artifact process created unsupported filesystem object {}",
                    relative.display()
                ));
            }
            if artifacts.len() == ARTIFACT_FILE_LIMIT {
                return Err(format!(
                    "artifact process exceeded {ARTIFACT_FILE_LIMIT} retained files"
                ));
            }
            *total_bytes = total_bytes
                .checked_add(metadata.len())
                .ok_or("artifact byte count overflow")?;
            if *total_bytes > ARTIFACT_BYTE_LIMIT {
                return Err(format!(
                    "artifact process exceeded {ARTIFACT_BYTE_LIMIT} retained bytes"
                ));
            }
            let relative = relative
                .to_str()
                .ok_or_else(|| format!("artifact path is not UTF-8: {}", relative.display()))?
                .replace(std::path::MAIN_SEPARATOR, "/");
            artifacts.push(ArtifactObservation {
                path: relative,
                size: metadata.len(),
                sha256: sha256_file(&path, "behavioral artifact")?,
            });
        }
        Ok(())
    }

    let mut artifacts = Vec::new();
    let mut total_bytes = 0u64;
    visit(root, root, excluded_input, &mut total_bytes, &mut artifacts)?;
    artifacts.sort();
    Ok(artifacts)
}

fn artifact_manifest_text(artifacts: &[ArtifactObservation]) -> String {
    let mut manifest = String::new();
    for artifact in artifacts {
        manifest.push_str(&artifact.path);
        manifest.push('\t');
        manifest.push_str(&artifact.size.to_string());
        manifest.push('\t');
        manifest.push_str(&artifact.sha256);
        manifest.push('\n');
    }
    manifest
}

fn row_from_pair(
    spec: &CaseSpec,
    oracle: Captured,
    subject: Captured,
    oracle_baseline: Option<Captured>,
) -> ValidatorCase {
    let oracle_stdout = String::from_utf8(oracle.stdout.clone());
    let oracle_stderr = String::from_utf8(oracle.stderr.clone());
    let subject_stdout = String::from_utf8(subject.stdout.clone());
    let subject_stderr = String::from_utf8(subject.stderr.clone());
    let baseline_stdout_result = oracle_baseline
        .as_ref()
        .map(|baseline| String::from_utf8(baseline.stdout.clone()))
        .transpose();
    let baseline_stderr_result = oracle_baseline
        .as_ref()
        .map(|baseline| String::from_utf8(baseline.stderr.clone()))
        .transpose();
    let utf8 = oracle_stdout.is_ok()
        && oracle_stderr.is_ok()
        && subject_stdout.is_ok()
        && subject_stderr.is_ok()
        && baseline_stdout_result.is_ok()
        && baseline_stderr_result.is_ok();
    let oracle_stdout = oracle_stdout
        .unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned());
    let oracle_stderr = oracle_stderr
        .unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned());
    let subject_stdout = subject_stdout
        .unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned());
    let subject_stderr = subject_stderr
        .unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned());
    let baseline_stdout = baseline_stdout_result
        .unwrap_or_else(|error| Some(String::from_utf8_lossy(error.as_bytes()).into_owned()))
        .unwrap_or_default();
    let baseline_stderr = baseline_stderr_result
        .unwrap_or_else(|error| Some(String::from_utf8_lossy(error.as_bytes()).into_owned()))
        .unwrap_or_default();
    let mut processes = vec![&oracle, &subject];
    if let Some(baseline) = &oracle_baseline {
        processes.push(baseline);
    }
    let complete = processes.iter().all(|process| {
        process.stdin_complete
            && !process.timed_out
            && !process.memout
            && !process.stdout_truncated
            && !process.stderr_truncated
            && process.exit_code.is_some()
    });
    let (stdout_match, stderr_match) = compare_streams(
        spec.comparator,
        &oracle_stdout,
        &oracle_stderr,
        &subject_stdout,
        &subject_stderr,
    );
    let recorded_oracle_stdout = record_stream(spec.comparator, &oracle_stdout);
    let recorded_oracle_stderr = record_stream(spec.comparator, &oracle_stderr);
    let recorded_subject_stdout = record_stream(spec.comparator, &subject_stdout);
    let recorded_subject_stderr = record_stream(spec.comparator, &subject_stderr);
    let recorded_baseline_stdout = record_stream(spec.comparator, &baseline_stdout);
    let recorded_baseline_stderr = record_stream(spec.comparator, &baseline_stderr);
    let oracle_artifacts = artifact_manifest_text(&oracle.artifacts);
    let subject_artifacts = artifact_manifest_text(&subject.artifacts);
    let baseline_artifacts = oracle_baseline
        .as_ref()
        .map_or_else(String::new, |baseline| {
            artifact_manifest_text(&baseline.artifacts)
        });
    let status_match = oracle.exit_code == subject.exit_code;
    let artifact_match = oracle.artifacts == subject.artifacts;
    let owner_category = spec
        .source_owner
        .as_ref()
        .map(|owner| owner.category.as_str());
    let requires_clean_oracle = matches!(
        owner_category,
        Some(
            "smt-command"
                | "tactic"
                | "filename-extension"
                | "input-mode"
                | "declaration-builtin"
                | "logic-recognizer-literal"
                | "smt-info-key"
                | "smt-parser-token"
        )
    );
    let requires_clean_baseline = matches!(
        owner_category,
        Some("smt-command" | "tactic" | "declaration-builtin" | "smt-parser-token")
    );
    let oracle_clean = if owner_category == Some("smt-option-key") {
        clean_z3_execution_with_redirected_output(&oracle, &oracle_stdout, &oracle_stderr)
    } else {
        !requires_clean_oracle || clean_z3_execution(&oracle, &oracle_stdout, &oracle_stderr)
    };
    let baseline_clean = !requires_clean_baseline
        || oracle_baseline.as_ref().is_some_and(|baseline| {
            clean_z3_execution(baseline, &baseline_stdout, &baseline_stderr)
        });
    let effect_witness = match spec.effect_requirement {
        EffectRequirement::Inherent => true,
        EffectRequirement::Unresolved => false,
        EffectRequirement::OracleDiffersFromBaseline => {
            oracle_baseline.as_ref().is_some_and(|baseline| {
                let (stdout_same, stderr_same) = compare_streams(
                    spec.comparator,
                    &oracle_stdout,
                    &oracle_stderr,
                    &baseline_stdout,
                    &baseline_stderr,
                );
                process_complete(baseline)
                    && (oracle.exit_code != baseline.exit_code
                        || !stdout_same
                        || !stderr_same
                        || oracle.artifacts != baseline.artifacts)
            })
        }
        EffectRequirement::SourceProvenNoEffect => {
            oracle_baseline.as_ref().is_some_and(|baseline| {
                let (stdout_same, stderr_same) = compare_streams(
                    spec.comparator,
                    &oracle_stdout,
                    &oracle_stderr,
                    &baseline_stdout,
                    &baseline_stderr,
                );
                process_complete(baseline)
                    && oracle.exit_code == baseline.exit_code
                    && stdout_same
                    && stderr_same
                    && oracle.artifacts == baseline.artifacts
            })
        }
    };
    let outcome = if processes.iter().any(|process| process.memout) {
        ValidatorCaseOutcome::Memout
    } else if processes.iter().any(|process| process.timed_out) {
        ValidatorCaseOutcome::Timeout
    } else if !complete || !utf8 {
        ValidatorCaseOutcome::Fail
    } else if status_match
        && stdout_match
        && stderr_match
        && artifact_match
        && oracle_clean
        && baseline_clean
        && effect_witness
    {
        ValidatorCaseOutcome::Pass
    } else {
        ValidatorCaseOutcome::Fail
    };
    let observed = format!(
        "source-owner={};effect-requirement={};effect-witness={effect_witness};comparator={};artifact-policy={};oracle-exit={:?};subject-exit={:?};baseline-exit={:?};status-match={status_match};stdout-match={stdout_match};stderr-match={stderr_match};artifact-match={artifact_match};oracle-clean={oracle_clean};baseline-clean={baseline_clean};utf8={utf8};oracle-complete={};subject-complete={};baseline-complete={};oracle-stdout-sha256={};subject-stdout-sha256={};baseline-stdout-sha256={};oracle-stderr-sha256={};subject-stderr-sha256={};baseline-stderr-sha256={};oracle-artifact-manifest-sha256={};subject-artifact-manifest-sha256={};baseline-artifact-manifest-sha256={}",
        spec.source_owner
            .as_ref()
            .map_or_else(|| "none".to_string(), SourceOwner::display),
        spec.effect_requirement.id(),
        spec.comparator.id(),
        spec.artifact_policy.id(),
        oracle.exit_code,
        subject.exit_code,
        oracle_baseline.as_ref().and_then(|baseline| baseline.exit_code),
        process_complete(&oracle),
        process_complete(&subject),
        oracle_baseline.as_ref().map_or(true, process_complete),
        sha256_bytes(recorded_oracle_stdout.as_bytes()),
        sha256_bytes(recorded_subject_stdout.as_bytes()),
        sha256_bytes(recorded_baseline_stdout.as_bytes()),
        sha256_bytes(recorded_oracle_stderr.as_bytes()),
        sha256_bytes(recorded_subject_stderr.as_bytes()),
        sha256_bytes(recorded_baseline_stderr.as_bytes()),
        sha256_bytes(oracle_artifacts.as_bytes()),
        sha256_bytes(subject_artifacts.as_bytes()),
        sha256_bytes(baseline_artifacts.as_bytes()),
    );
    ValidatorCase {
        id: spec.id.clone(),
        input_sha256: spec.input_sha256(),
        expected: spec.expected(),
        observed,
        stdout: Some(format!(
            "--- pinned-z3-5.0.0 stdout ---\n{recorded_oracle_stdout}--- manifest-ay stdout ---\n{recorded_subject_stdout}--- pinned-z3-5.0.0 effect-baseline stdout ---\n{recorded_baseline_stdout}--- pinned-z3-5.0.0 artifacts ---\n{oracle_artifacts}--- manifest-ay artifacts ---\n{subject_artifacts}--- pinned-z3-5.0.0 effect-baseline artifacts ---\n{baseline_artifacts}"
        )),
        stderr: Some(format!(
            "--- pinned-z3-5.0.0 stderr ---\n{recorded_oracle_stderr}--- manifest-ay stderr ---\n{recorded_subject_stderr}--- pinned-z3-5.0.0 effect-baseline stderr ---\n{recorded_baseline_stderr}"
        )),
        exit_code: subject.exit_code,
        process: Some(ProcessObservation {
            stdin_complete: processes.iter().all(|process| process.stdin_complete),
            timed_out: processes.iter().any(|process| process.timed_out),
            memout: processes.iter().any(|process| process.memout),
            stdout_truncated: processes.iter().any(|process| process.stdout_truncated),
            stderr_truncated: processes.iter().any(|process| process.stderr_truncated),
        }),
        outcome,
    }
}

fn clean_z3_execution(process: &Captured, stdout: &str, stderr: &str) -> bool {
    process_complete(process)
        && process.exit_code == Some(0)
        && stderr.is_empty()
        && !stdout.lines().any(z3_error_output_line)
}

fn clean_z3_execution_with_redirected_output(
    process: &Captured,
    stdout: &str,
    stderr: &str,
) -> bool {
    process_complete(process)
        && process.exit_code == Some(0)
        && !stdout
            .lines()
            .chain(stderr.lines())
            .any(z3_error_output_line)
}

fn z3_error_output_line(line: &str) -> bool {
    let line = line.trim_start();
    line.starts_with("(error")
        || line.starts_with("unsupported")
        || line.starts_with("Error:")
        || line.starts_with("[z3 exception]")
        || line.contains("did not verify")
}

fn process_complete(process: &Captured) -> bool {
    process.stdin_complete
        && !process.timed_out
        && !process.memout
        && !process.stdout_truncated
        && !process.stderr_truncated
        && process.exit_code.is_some()
}

fn compare_streams(
    comparator: Comparator,
    oracle_stdout: &str,
    oracle_stderr: &str,
    subject_stdout: &str,
    subject_stderr: &str,
) -> (bool, bool) {
    match comparator {
        Comparator::ExactBytes => (
            oracle_stdout.as_bytes() == subject_stdout.as_bytes(),
            oracle_stderr.as_bytes() == subject_stderr.as_bytes(),
        ),
        Comparator::Statistics => (
            canonicalize_statistics(oracle_stdout) == canonicalize_statistics(subject_stdout),
            canonicalize_statistics(oracle_stderr) == canonicalize_statistics(subject_stderr),
        ),
        Comparator::ComponentTrace => (
            canonicalize_component_trace(oracle_stdout)
                == canonicalize_component_trace(subject_stdout),
            canonicalize_component_trace(oracle_stderr)
                == canonicalize_component_trace(subject_stderr),
        ),
    }
}

fn record_stream(comparator: Comparator, value: &str) -> String {
    match comparator {
        Comparator::ExactBytes => value.to_string(),
        Comparator::Statistics => canonicalize_statistics(value),
        Comparator::ComponentTrace => canonicalize_component_trace(value),
    }
}

fn canonicalize_statistics(value: &str) -> String {
    let mut output = String::with_capacity(value.len());
    for line in value.split_inclusive('\n') {
        let trimmed = line.trim_start();
        let key_start = if trimmed.starts_with("(:") { 1 } else { 0 };
        if !trimmed[key_start..].starts_with(':') {
            output.push_str(line);
            continue;
        }
        let indentation = &line[..line.len() - trimmed.len()];
        let without_newline = trimmed.strip_suffix('\n').unwrap_or(trimmed);
        let (body, newline) = if trimmed.ends_with('\n') {
            (without_newline, "\n")
        } else {
            (without_newline, "")
        };
        let Some(relative_split) = body[key_start..].find(char::is_whitespace) else {
            output.push_str(line);
            continue;
        };
        let split = key_start + relative_split;
        let key = &body[..split];
        let value_and_close = body[split..].trim();
        let close = if value_and_close.ends_with(')') {
            ")"
        } else {
            ""
        };
        let numeric = value_and_close.trim_end_matches(')').trim();
        if numeric.parse::<f64>().is_ok() {
            output.push_str(indentation);
            output.push_str(key);
            output.push(' ');
            output.push_str("<numeric>");
            output.push_str(close);
            output.push_str(newline);
        } else {
            output.push_str(line);
        }
    }
    output
}

fn canonicalize_component_trace(value: &str) -> String {
    let mut output = String::with_capacity(value.len());
    let mut characters = value.chars().peekable();
    while let Some(character) = characters.next() {
        let numeric_start = character.is_ascii_digit()
            || (character == '-' && characters.peek().is_some_and(|next| next.is_ascii_digit()));
        if !numeric_start {
            output.push(character);
            continue;
        }
        output.push_str("<numeric>");
        while characters.peek().is_some_and(|next| {
            next.is_ascii_digit() || matches!(*next, '.' | '/' | '%' | 'e' | 'E' | '+' | '-')
        }) {
            characters.next();
        }
    }
    output
}

fn overlay_dimension(contract: &Contract) -> Result<&Dimension, String> {
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == DIMENSION_ID)
        .ok_or("contract has no overlay.z3-5.0.0 dimension".to_string())
}

fn batch_case(id: impl Into<String>, input: &str) -> CaseSpec {
    CaseSpec {
        id: id.into(),
        oracle_args: vec!["-in".to_string()],
        subject_args: vec!["--z3-mode".to_string(), "-in".to_string()],
        input: input.as_bytes().to_vec(),
        comparator: Comparator::ExactBytes,
        style: RunStyle::Batch,
        file_extension: "smt2".to_string(),
        artifact_policy: ArtifactPolicy::None,
        source_owner: None,
        effect_requirement: EffectRequirement::Inherent,
        oracle_baseline: None,
    }
}

fn fixedpoint_file_case(id: impl Into<String>, input: &str) -> CaseSpec {
    CaseSpec {
        id: id.into(),
        oracle_args: vec![FILE_PLACEHOLDER.to_string()],
        subject_args: vec!["--z3-mode".to_string(), FILE_PLACEHOLDER.to_string()],
        input: input.as_bytes().to_vec(),
        comparator: Comparator::ExactBytes,
        style: RunStyle::File,
        file_extension: "smt2".to_string(),
        artifact_policy: ArtifactPolicy::None,
        source_owner: None,
        effect_requirement: EffectRequirement::Inherent,
        oracle_baseline: None,
    }
}

fn cli_case(id: impl Into<String>, args: &[&str], input: &str) -> CaseSpec {
    let oracle_args = args.iter().map(|arg| (*arg).to_string()).collect();
    let mut subject_args = vec!["--z3-mode".to_string()];
    subject_args.extend(args.iter().map(|arg| (*arg).to_string()));
    CaseSpec {
        id: id.into(),
        oracle_args,
        subject_args,
        input: input.as_bytes().to_vec(),
        comparator: Comparator::ExactBytes,
        style: RunStyle::Batch,
        file_extension: "smt2".to_string(),
        artifact_policy: ArtifactPolicy::None,
        source_owner: None,
        effect_requirement: EffectRequirement::Inherent,
        oracle_baseline: None,
    }
}

fn owned_case_id(owner: &SourceOwner) -> String {
    format!(
        "source-behavior.{}.{}.{}",
        case_token(&owner.category),
        case_token(&owner.name),
        &sha256_bytes(owner.canonical_line().as_bytes())[..12]
    )
}

fn attach_owner(mut case: CaseSpec, item: &z3_source_inventory::ObservableItem) -> CaseSpec {
    let owner = SourceOwner {
        category: item.category.clone(),
        name: item.name.clone(),
    };
    case.id = owned_case_id(&owner);
    case.source_owner = Some(owner);
    case
}

fn require_oracle_difference(mut case: CaseSpec, baseline: BaselineSpec) -> CaseSpec {
    case.effect_requirement = EffectRequirement::OracleDiffersFromBaseline;
    case.oracle_baseline = Some(baseline);
    case
}

fn unresolved_case(mut case: CaseSpec) -> CaseSpec {
    case.effect_requirement = EffectRequirement::Unresolved;
    case.oracle_baseline = None;
    case
}

fn source_owned_case(
    item: &z3_source_inventory::ObservableItem,
    items: &[z3_source_inventory::ObservableItem],
) -> Result<CaseSpec, String> {
    let case = match item.category.as_str() {
        "smt-command" => source_command_case(&item.name),
        "tactic" => source_tactic_case(&item.name),
        "probe" => batch_case(
            "source-probe",
            &format!(
                "(set-logic ALL)\n(declare-const x Int)\n(assert (> x 0))\n(apply (fail-if {}))\n(exit)\n",
                item.name
            ),
        ),
        "simplifier" => source_simplifier_case(&item.name),
        "global-parameter" | "module-parameter" => source_parameter_case(item),
        "parameter-module" => source_parameter_module_case(item, items)?,
        "cli-option" => source_cli_option_case(&item.name),
        "cli-help-option" => source_cli_help_case(item),
        "filename-extension" => source_filename_extension_case(&item.name),
        "input-mode" => source_input_mode_case(&item.name),
        "declaration-builtin" => source_declaration_builtin_case(&item.name),
        "logic-recognizer-literal" => source_logic_recognizer_case(&item.name),
        "smt-info-key" => source_info_key_case(&item.name).unwrap_or_else(|| {
            unresolved_case(batch_case("source-info-key-unresolved", "(exit)\n"))
        }),
        "smt-option-key" => source_option_key_case(&item.name).unwrap_or_else(|| {
            unresolved_case(batch_case("source-option-key-unresolved", "(exit)\n"))
        }),
        "smt-parser-token" => source_parser_token_case(&item.name),
        "logic-strategy-alias" => unresolved_case(batch_case(
            "source-observable-unresolved",
            "(exit)\n",
        )),
        category => return Err(format!("unowned Z3 observable category {category:?}")),
    };
    Ok(attach_owner(case, item))
}

fn source_parser_token_case(name: &str) -> CaseSpec {
    let Some(witness) = parser_tokens::semantic_witness(name) else {
        return unresolved_case(batch_case("source-parser-token-unresolved", "(exit)\n"));
    };
    require_oracle_difference(
        batch_case("source-parser-token", witness.candidate),
        BaselineSpec {
            args: vec!["-in".to_string()],
            input: witness.baseline.as_bytes().to_vec(),
            style: RunStyle::Batch,
        },
    )
}

fn source_declaration_builtin_case(name: &str) -> CaseSpec {
    let Some(predicate) = declaration_builtins::semantic_predicate(name) else {
        return unresolved_case(batch_case(
            "source-declaration-builtin-unresolved",
            "(exit)\n",
        ));
    };
    let logic_prefix = if declaration_builtins::semantic_requires_no_logic(name) {
        ""
    } else {
        "(set-logic ALL)\n"
    };
    let prelude = declaration_builtins::semantic_prelude(name);
    let candidate =
        format!("{prelude}{logic_prefix}(assert (not {predicate}))\n(check-sat)\n(exit)\n");
    require_oracle_difference(
        batch_case("source-declaration-builtin", &candidate),
        BaselineSpec {
            args: vec!["-in".to_string()],
            input: format!("{prelude}{logic_prefix}(check-sat)\n(exit)\n").into_bytes(),
            style: RunStyle::Batch,
        },
    )
}

fn source_logic_recognizer_case(name: &str) -> CaseSpec {
    let candidate = format!("(set-logic {name})\n(exit)\n");
    require_oracle_difference(
        batch_case("source-logic-recognizer", &candidate),
        BaselineSpec {
            args: vec!["-in".to_string()],
            input: b"(set-logic ZZ_NO_SUCH_LOGIC)\n(exit)\n".to_vec(),
            style: RunStyle::Batch,
        },
    )
}

fn source_info_key_case(name: &str) -> Option<CaseSpec> {
    let candidate = match name {
        ":?" => "(get-info :?)\n(exit)\n",
        ":all-statistics" => "(get-info :all-statistics)\n(exit)\n",
        ":error-behavior" => "(get-info :error-behavior)\n(exit)\n",
        ":name" => "(get-info :name)\n(exit)\n",
        ":authors" => "(get-info :authors)\n(exit)\n",
        ":version" => "(get-info :version)\n(exit)\n",
        ":status" => "(set-info :status sat)\n(get-info :status)\n(exit)\n",
        ":reason-unknown" => "(get-info :reason-unknown)\n(exit)\n",
        ":rlimit" => "(get-info :rlimit)\n(exit)\n",
        ":assertion-stack-levels" => "(push 2)\n(get-info :assertion-stack-levels)\n(exit)\n",
        ":parameters" => "(get-info :parameters)\n(exit)\n",
        _ => return None,
    };
    let mut case = batch_case("source-info-key", candidate);
    if name == ":all-statistics" {
        case.comparator = Comparator::Statistics;
    }
    Some(require_oracle_difference(
        case,
        BaselineSpec {
            args: vec!["-in".to_string()],
            // Z3 5.0.0 exits zero for an unknown query while deliberately
            // emitting its positioned diagnostic. That makes this a complete,
            // observable negative control rather than an interrupted invocation.
            input: b"(get-info :ay-no-such-info)\n(exit)\n".to_vec(),
            style: RunStyle::Batch,
        },
    ))
}

fn source_option_key_case(name: &str) -> Option<CaseSpec> {
    if !RESOLVED_OPTION_KEYS.contains(&name) {
        // Known partial option semantics remain explicit gaps even if a narrow
        // round-trip happens to match the oracle.
        return None;
    }
    let candidate = match name {
        ":print-success" => {
            "(set-option :print-success true)\n(get-option :print-success)\n(exit)\n"
        }
        ":interactive-mode" => {
            "(set-option :interactive-mode true)\n(get-option :interactive-mode)\n(exit)\n"
        }
        ":produce-proofs" => {
            "(set-option :produce-proofs true)\n(get-option :produce-proofs)\n(exit)\n"
        }
        ":produce-unsat-cores" => {
            "(set-option :produce-unsat-cores true)\n(get-option :produce-unsat-cores)\n(exit)\n"
        }
        ":produce-unsat-assumptions" => {
            "(set-option :produce-unsat-assumptions true)\n\
             (get-option :produce-unsat-assumptions)\n\
             (exit)\n"
        }
        ":produce-models" => {
            "(set-option :produce-models false)\n(get-option :produce-models)\n(exit)\n"
        }
        ":produce-assignments" => {
            "(set-option :produce-assignments true)\n\
             (get-option :produce-assignments)\n\
             (exit)\n"
        }
        ":produce-assertions" => {
            "(set-option :produce-assertions true)\n\
             (get-option :produce-assertions)\n\
             (exit)\n"
        }
        ":regular-output-channel" => {
            "(set-option :regular-output-channel \"stderr\")\n\
             (get-option :regular-output-channel)\n\
             (exit)\n"
        }
        ":diagnostic-output-channel" => {
            "(set-option :diagnostic-output-channel \"stdout\")\n\
             (get-option :diagnostic-output-channel)\n\
             (exit)\n"
        }
        ":random-seed" => "(set-option :random-seed 17)\n(get-option :random-seed)\n(exit)\n",
        ":verbosity" => "(set-option :verbosity 1)\n(get-option :verbosity)\n(exit)\n",
        ":global-decls" => "(set-option :global-decls true)\n(get-option :global-decls)\n(exit)\n",
        ":global-declarations" => {
            "(set-option :global-declarations true)\n\
             (get-option :global-declarations)\n\
             (exit)\n"
        }
        ":print-warning" => {
            "(set-option :print-warning false)\n\
             (assert (! true :ay-parity-unknown-attribute true))\n\
             (check-sat)\n\
             (exit)\n"
        }
        ":numeral-as-real" => {
            "(set-option :int-real-coercions false)\n\
             (set-option :numeral-as-real true)\n\
             (assert (= 0 0.0))\n\
             (check-sat)\n\
             (exit)\n"
        }
        ":error-behavior" => {
            "(set-option :error-behavior immediate-exit)\n\
             (get-option :error-behavior)\n\
             (exit)\n"
        }
        ":int-real-coercions" => {
            "(set-option :int-real-coercions false)\n\
             (get-option :int-real-coercions)\n\
             (exit)\n"
        }
        _ => return None,
    };
    let baseline = match name {
        ":print-warning" => {
            "(assert (! true :ay-parity-unknown-attribute true))\n\
             (check-sat)\n\
             (exit)\n"
        }
        ":numeral-as-real" => {
            "(set-option :int-real-coercions false)\n\
             (assert (= 0 0.0))\n\
             (check-sat)\n\
             (exit)\n"
        }
        ":error-behavior" => "(get-option :error-behavior)\n(exit)\n",
        ":int-real-coercions" => "(get-option :int-real-coercions)\n(exit)\n",
        _ => "(get-option :ay-no-such-option)\n(exit)\n",
    };
    Some(require_oracle_difference(
        batch_case("source-option-key", candidate),
        BaselineSpec {
            args: vec!["-in".to_string()],
            // As above, Z3's unsupported query is an exit-zero diagnostic and
            // therefore a complete negative control with a real oracle effect.
            input: baseline.as_bytes().to_vec(),
            style: RunStyle::Batch,
        },
    ))
}

#[derive(Clone, Copy)]
struct SourceCommandWitness {
    candidate: &'static str,
    baseline: &'static str,
}

fn standard_source_command_witness(name: &str) -> Option<SourceCommandWitness> {
    let (candidate, baseline) = match name {
        "apply" => (
            "(declare-const x Int)\n(assert (= (+ x 0) 1))\n(apply simplify)\n(exit)\n",
            "(declare-const x Int)\n(assert (= (+ x 0) 1))\n(apply skip)\n(exit)\n",
        ),
        "assert" => (
            "(assert false)\n(check-sat)\n(exit)\n",
            "(check-sat)\n(exit)\n",
        ),
        "assert-not" => (
            "(set-option :print-success true)\n(assert-not true)\n(check-sat)\n(exit)\n",
            "(set-option :print-success true)\n(check-sat)\n(exit)\n",
        ),
        "assert-soft" => (
            "(declare-const a Bool)\n(assert-soft a :weight 1)\n(check-sat)\n(eval a)\n(exit)\n",
            "(declare-const a Bool)\n(check-sat)\n(eval a)\n(exit)\n",
        ),
        "check-sat" => ("(check-sat)\n(exit)\n", "(exit)\n"),
        "check-sat-assuming" => (
            "(declare-const a Bool)\n(check-sat-assuming (a (not a)))\n(exit)\n",
            "(declare-const a Bool)\n(check-sat)\n(exit)\n",
        ),
        "check-sat-using" => (
            "(assert true)\n(check-sat-using (then simplify smt))\n(exit)\n",
            "(assert true)\n(exit)\n",
        ),
        "declare-const" => (
            "(set-option :produce-models true)\n(declare-const a Bool)\n(assert a)\n(check-sat)\n(get-model)\n(exit)\n",
            "(set-option :produce-models true)\n(check-sat)\n(get-model)\n(exit)\n",
        ),
        "declare-datatype" => (
            "(set-option :produce-models true)\n(declare-datatype D ((a) (b)))\n(declare-const d D)\n(assert (= d b))\n(check-sat)\n(get-model)\n(exit)\n",
            "(set-option :produce-models true)\n(check-sat)\n(get-model)\n(exit)\n",
        ),
        "declare-datatypes" => (
            "(set-option :produce-models true)\n(declare-datatypes ((D 0) (E 0)) (((d)) ((e))))\n(declare-const x D)\n(assert (= x d))\n(check-sat)\n(get-model)\n(exit)\n",
            "(set-option :produce-models true)\n(check-sat)\n(get-model)\n(exit)\n",
        ),
        "declare-fun" => (
            "(set-option :produce-models true)\n(declare-fun f () Bool)\n(assert f)\n(check-sat)\n(get-model)\n(exit)\n",
            "(set-option :produce-models true)\n(check-sat)\n(get-model)\n(exit)\n",
        ),
        "declare-sort" => (
            "(set-option :produce-models true)\n(declare-sort U 0)\n(declare-const u U)\n(check-sat)\n(get-model)\n(exit)\n",
            "(set-option :produce-models true)\n(check-sat)\n(get-model)\n(exit)\n",
        ),
        "declare-type-var" => (
            "(set-option :produce-models true)\n(declare-type-var T)\n(declare-const x T)\n(check-sat)\n(get-model)\n(exit)\n",
            "(set-option :produce-models true)\n(check-sat)\n(get-model)\n(exit)\n",
        ),
        "define-const" => (
            "(set-option :print-success true)\n(define-const x Int 2)\n(simplify (+ x 1))\n(exit)\n",
            "(set-option :print-success true)\n(exit)\n",
        ),
        "define-fun" => (
            "(set-option :print-success true)\n(define-fun f ((x Int)) Int (+ x 1))\n(simplify (f 1))\n(exit)\n",
            "(set-option :print-success true)\n(exit)\n",
        ),
        "define-fun-rec" => (
            "(set-option :print-success true)\n(define-fun-rec f ((x Int)) Int (ite (= x 0) 0 (f (- x 1))))\n(simplify (f 0))\n(exit)\n",
            "(set-option :print-success true)\n(exit)\n",
        ),
        "define-funs-rec" => (
            "(set-option :print-success true)\n(define-funs-rec ((f ((x Int)) Int) (g ((x Int)) Int)) ((ite (= x 0) 0 (g (- x 1))) (ite (= x 0) 0 (f (- x 1)))))\n(simplify (f 0))\n(exit)\n",
            "(set-option :print-success true)\n(exit)\n",
        ),
        "define-sort" => (
            "(set-option :produce-models true)\n(define-sort I () Int)\n(declare-const x I)\n(assert (= x 3))\n(check-sat)\n(get-model)\n(exit)\n",
            "(set-option :produce-models true)\n(check-sat)\n(get-model)\n(exit)\n",
        ),
        "dbg-elim-unused-vars" => (
            "(dbg-elim-unused-vars (forall ((x Int) (y Bool)) (= x 0)))\n(exit)\n",
            "(exit)\n",
        ),
        "dbg-instantiate" => (
            "(dbg-instantiate (forall ((x Int) (y Bool)) (or y (= x 3))) (7 false))\n(exit)\n",
            "(exit)\n",
        ),
        "dbg-params" => ("(dbg-params)\n(exit)\n", "(exit)\n"),
        "dbg-pp-var" => (
            "(dbg-set saved true)\n(dbg-pp-var saved)\n(exit)\n",
            "(dbg-set saved true)\n(exit)\n",
        ),
        "dbg-set" => (
            "(dbg-set saved true)\n(dbg-pp-var saved)\n(exit)\n",
            "(dbg-set saved false)\n(dbg-pp-var saved)\n(exit)\n",
        ),
        "dbg-sexpr" => (
            "(dbg-sexpr (a :b 1 \"x\"))\n(exit)\n",
            "(exit)\n",
        ),
        "dbg-size" => ("(dbg-size (and true false))\n(exit)\n", "(exit)\n"),
        "dbg-translator" => (
            "(dbg-translator (and true false))\n(exit)\n",
            "(exit)\n",
        ),
        "dbg-used-vars" => (
            "(dbg-used-vars (forall ((x Int) (y Bool)) (= x 3)))\n(exit)\n",
            "(exit)\n",
        ),
        "echo" => ("(echo \"source-echo\")\n(exit)\n", "(exit)\n"),
        "eval" => (
            "(set-option :produce-models true)\n(declare-const x Int)\n(assert (= x 7))\n(check-sat)\n(eval (+ x 1))\n(exit)\n",
            "(set-option :produce-models true)\n(declare-const x Int)\n(assert (= x 7))\n(check-sat)\n(exit)\n",
        ),
        "display" => ("(display (and true false))\n(exit)\n", "(exit)\n"),
        "exit" => (
            "(exit)\n(echo \"must-not-run\")\n",
            "(echo \"must-run\")\n(exit)\n",
        ),
        "get-assertions" => (
            "(set-option :interactive-mode true)\n(assert false)\n(get-assertions)\n(exit)\n",
            "(set-option :interactive-mode true)\n(assert false)\n(exit)\n",
        ),
        "get-assignment" => (
            "(set-option :produce-assignments true)\n(assert (! true :named n))\n(check-sat)\n(get-assignment)\n(exit)\n",
            "(set-option :produce-assignments true)\n(assert (! true :named n))\n(check-sat)\n(exit)\n",
        ),
        "get-consequences" => (
            "(declare-const a Bool)\n(assert a)\n(get-consequences () (a))\n(exit)\n",
            "(declare-const a Bool)\n(assert a)\n(check-sat)\n(exit)\n",
        ),
        "get-interpolant" => ("(get-interpolant false true)\n(exit)\n", "(exit)\n"),
        "get-info" => ("(get-info :name)\n(exit)\n", "(exit)\n"),
        "get-model" => (
            "(set-option :produce-models true)\n(declare-const x Int)\n(assert (= x 7))\n(check-sat)\n(get-model)\n(exit)\n",
            "(set-option :produce-models true)\n(declare-const x Int)\n(assert (= x 7))\n(check-sat)\n(exit)\n",
        ),
        "get-objectives" => (
            "(declare-const x Int)\n(assert (and (<= 0 x) (<= x 2)))\n(maximize x)\n(check-sat)\n(get-objectives)\n(exit)\n",
            "(declare-const x Int)\n(assert (and (<= 0 x) (<= x 2)))\n(maximize x)\n(check-sat)\n(exit)\n",
        ),
        "help" => ("(help)\n(exit)\n", "(exit)\n"),
        "help-simplifier" => ("(help-simplifier)\n(exit)\n", "(exit)\n"),
        "help-tactic" => ("(help-tactic)\n(exit)\n", "(exit)\n"),
        "labels" => (
            "(check-sat)\n(labels)\n(exit)\n",
            "(check-sat)\n(exit)\n",
        ),
        "get-option" => ("(get-option :print-success)\n(exit)\n", "(exit)\n"),
        "get-proof" => (
            "(set-option :produce-proofs true)\n(assert false)\n(check-sat)\n(get-proof)\n(exit)\n",
            "(set-option :produce-proofs true)\n(assert false)\n(check-sat)\n(exit)\n",
        ),
        "get-unsat-assumptions" => (
            "(set-option :produce-unsat-assumptions true)\n(declare-const a Bool)\n(check-sat-assuming (a (not a)))\n(get-unsat-assumptions)\n(exit)\n",
            "(set-option :produce-unsat-assumptions true)\n(declare-const a Bool)\n(check-sat-assuming (a (not a)))\n(exit)\n",
        ),
        "get-unsat-core" => (
            "(set-option :produce-unsat-cores true)\n(assert (! false :named n))\n(check-sat)\n(get-unsat-core)\n(exit)\n",
            "(set-option :produce-unsat-cores true)\n(assert (! false :named n))\n(check-sat)\n(exit)\n",
        ),
        "get-value" => (
            "(set-option :produce-models true)\n(declare-const x Int)\n(assert (= x 7))\n(check-sat)\n(get-value (x (+ x 1)))\n(exit)\n",
            "(set-option :produce-models true)\n(declare-const x Int)\n(assert (= x 7))\n(check-sat)\n(exit)\n",
        ),
        "maximize" => (
            "(declare-const x Int)\n(assert (and (<= 0 x) (<= x 2)))\n(maximize x)\n(check-sat)\n(eval x)\n(exit)\n",
            "(declare-const x Int)\n(assert (and (<= 0 x) (<= x 2)))\n(minimize x)\n(check-sat)\n(eval x)\n(exit)\n",
        ),
        "minimize" => (
            "(declare-const x Int)\n(assert (and (<= 0 x) (<= x 2)))\n(minimize x)\n(check-sat)\n(eval x)\n(exit)\n",
            "(declare-const x Int)\n(assert (and (<= 0 x) (<= x 2)))\n(maximize x)\n(check-sat)\n(eval x)\n(exit)\n",
        ),
        "pop" => (
            "(push 1)\n(assert false)\n(pop 1)\n(check-sat)\n(exit)\n",
            "(push 1)\n(assert false)\n(check-sat)\n(exit)\n",
        ),
        "push" => (
            "(push 1)\n(get-info :assertion-stack-levels)\n(exit)\n",
            "(get-info :assertion-stack-levels)\n(exit)\n",
        ),
        "reset" => (
            "(assert false)\n(reset)\n(check-sat)\n(exit)\n",
            "(assert false)\n(check-sat)\n(exit)\n",
        ),
        "reset-assertions" => (
            "(assert false)\n(reset-assertions)\n(check-sat)\n(exit)\n",
            "(assert false)\n(check-sat)\n(exit)\n",
        ),
        "simplify" => ("(simplify (+ 0 1))\n(exit)\n", "(exit)\n"),
        "set-info" => (
            "(set-info :status sat)\n(get-info :status)\n(exit)\n",
            "(get-info :status)\n(exit)\n",
        ),
        "set-logic" => (
            "(set-logic QF_BV)\n(check-sat)\n(get-info :all-statistics)\n(exit)\n",
            "(check-sat)\n(get-info :all-statistics)\n(exit)\n",
        ),
        "set-option" => (
            "(set-option :global-declarations true)\n(get-option :global-declarations)\n(exit)\n",
            "(get-option :global-declarations)\n(exit)\n",
        ),
        _ => return None,
    };
    Some(SourceCommandWitness {
        candidate,
        baseline,
    })
}

fn source_fixedpoint_command_case(name: &str) -> Option<CaseSpec> {
    let (candidate, baseline) = match name {
        "declare-rel" => (
            "(declare-rel p ())\n(query p)\n(exit)\n",
            "(check-sat)\n(exit)\n",
        ),
        "declare-var" => (
            "(declare-rel p (Int))\n(declare-var x Int)\n(rule (=> (= x 0) (p x)))\n(query p)\n(exit)\n",
            "(declare-rel p (Int))\n(query p)\n(exit)\n",
        ),
        "rule" => (
            "(declare-rel p ())\n(rule p)\n(query p)\n(exit)\n",
            "(declare-rel p ())\n(query p)\n(exit)\n",
        ),
        "query" => (
            "(declare-rel p ())\n(query p)\n(exit)\n",
            "(declare-rel p ())\n(exit)\n",
        ),
        _ => return None,
    };
    Some(require_oracle_difference(
        fixedpoint_file_case("source-fixedpoint-command", candidate),
        BaselineSpec {
            args: vec![FILE_PLACEHOLDER.to_string()],
            input: baseline.as_bytes().to_vec(),
            style: RunStyle::File,
        },
    ))
}

fn source_command_case(name: &str) -> CaseSpec {
    if EXPECTED_UNRESOLVED_COMMAND_OWNER_KEYS
        .iter()
        .any(|(category, owner)| *category == "smt-command" && *owner == name)
    {
        // A stale happy-path witness must never override a known unsupported
        // branch. The explicit unresolved inventory is authoritative.
        return unresolved_case(batch_case("source-command-unresolved", "(exit)\n"));
    }
    if let Some(case) = source_fixedpoint_command_case(name) {
        return case;
    }
    let Some(witness) = standard_source_command_witness(name) else {
        // The owner remains explicit in the closed catalog, but no diagnostic,
        // malformed call, or identity baseline may manufacture parity credit.
        // A clean, command-specific Z3 witness is required to leave this state.
        return unresolved_case(batch_case("source-command-unresolved", "(exit)\n"));
    };
    let mut case = require_oracle_difference(
        batch_case("source-command", witness.candidate),
        BaselineSpec {
            args: vec!["-in".to_string()],
            input: witness.baseline.as_bytes().to_vec(),
            style: RunStyle::Batch,
        },
    );
    if name == "set-logic" {
        case.comparator = Comparator::Statistics;
    }
    case
}

fn source_tactic_case(name: &str) -> CaseSpec {
    const GOAL: &str =
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (= (bvadd x #x01) #x02))\n";
    let candidate = format!("{GOAL}(apply {name})\n(exit)\n");
    let baseline = format!("{GOAL}(apply skip)\n(exit)\n");
    require_oracle_difference(
        batch_case("source-tactic", &candidate),
        BaselineSpec {
            args: vec!["-in".to_string()],
            input: baseline.into_bytes(),
            style: RunStyle::Batch,
        },
    )
}

fn source_simplifier_case(name: &str) -> CaseSpec {
    const BODY: &str =
        "(declare-const x (_ BitVec 2))\n(assert (= (bvadd x #b01) #b10))\n(check-sat)\n(exit)\n";
    let candidate = format!("(set-simplifier {name})\n{BODY}");
    let mut case = require_oracle_difference(
        batch_case("source-simplifier", &candidate),
        BaselineSpec {
            args: vec!["-v:10".to_string(), "-in".to_string()],
            input: BODY.as_bytes().to_vec(),
            style: RunStyle::Batch,
        },
    );
    case.oracle_args = vec!["-v:10".to_string(), "-in".to_string()];
    case.subject_args = vec![
        "--z3-mode".to_string(),
        "-v:10".to_string(),
        "-in".to_string(),
    ];
    case.comparator = Comparator::ComponentTrace;
    case
}

fn parameter_default(detail: &str) -> Option<&str> {
    let start = detail.find("(default: ")? + "(default: ".len();
    let rest = &detail[start..];
    Some(&rest[..rest.find(')')?])
}

fn parameter_may_create_artifact(name: &str) -> bool {
    matches!(
        name,
        "dot_proof_file"
            | "trace"
            | "trace_file_name"
            | "sat.drat.file"
            | "sat.inprocess.out"
            | "solver.cancel_backup_file"
            | "solver.axioms2files"
            | "solver.proof.log"
            | "solver.proof.save"
            | "solver.smtlib2_log"
            | "opt.dump_benchmarks"
            | "opt.solution_prefix"
            | "nlsat.dump_mathematica"
            | "nlsat.known_sat_assignment_file_name"
            | "fp.generate_proof_trace"
            | "fp.print_aig"
            | "fp.spacer.dump_benchmarks"
            | "fp.spacer.trace_file"
            | "smt.arith.dump_bound_lemmas"
            | "smt.arith.dump_lemmas"
            | "smt.arith.nl.log"
    )
}

fn parameter_named_alternate(name: &str) -> Option<&'static str> {
    match name {
        "encoding" => Some("ascii"),
        "tactic.default_tactic" => Some("smt"),
        "sat.branching.heuristic" => Some("chb"),
        "sat.cardinality.encoding" => Some("ordered"),
        "sat.gc" => Some("dyn_psm"),
        "sat.local_search_mode" => Some("qwsat"),
        "sat.lookahead.cube.cutoff" => Some("freevars"),
        "sat.lookahead.reward" => Some("ternary"),
        "sat.pb.lemma_format" => Some("pb"),
        "sat.pb.resolve" => Some("rounding"),
        "sat.pb.solver" => Some("circuit"),
        "sat.phase" => Some("always_false"),
        "sat.restart" => Some("luby"),
        "opt.maxsat_engine" => Some("wmax"),
        "opt.optsmt_engine" => Some("symba"),
        "opt.priority" => Some("pareto"),
        "nnf.mode" => Some("full"),
        "fp.datalog.check_relation" => Some("ay_z3_behavioral_relation"),
        "fp.datalog.default_relation" => Some("external_relation"),
        "fp.datalog.default_table" | "fp.datalog.default_table_checker" => Some("hashtable"),
        "fp.engine" => Some("spacer"),
        "fp.spacer.logic" | "smt.logic" => Some("QF_LIA"),
        "fp.tab.selection" => Some("first"),
        "fp.xform.instantiate_arrays.slice_technique" => Some("small"),
        "smt.mbqi.id" => Some("ay-z3-behavioral"),
        "smt.qi.cost" => Some("weight"),
        "smt.string_solver" => Some("z3str3"),
        _ => None,
    }
}

fn parameter_alternate(item: &z3_source_inventory::ObservableItem) -> Option<String> {
    if parameter_may_create_artifact(&item.name) {
        return None;
    }
    if let Some(alternate) = parameter_named_alternate(&item.name) {
        return Some(alternate.to_string());
    }
    let default = parameter_default(&item.detail)?;
    if item.detail.contains(" (bool)") {
        return match default {
            "true" => Some("false".to_string()),
            "false" => Some("true".to_string()),
            _ => None,
        };
    }
    if item.detail.contains(" (unsigned int)") || item.detail.contains(" (int)") {
        return Some(if default == "0" { "1" } else { "0" }.to_string());
    }
    if item.detail.contains(" (double)") || item.detail.contains(" (rational)") {
        return Some(
            if default == "0" || default == "0.0" {
                "1"
            } else {
                "0"
            }
            .to_string(),
        );
    }
    None
}

fn parameter_effect_case(
    candidate_args: &[&str],
    baseline_args: &[&str],
    input: String,
    artifact_policy: ArtifactPolicy,
) -> CaseSpec {
    let mut oracle_args = candidate_args
        .iter()
        .map(|argument| (*argument).to_string())
        .collect::<Vec<_>>();
    oracle_args.push("-in".to_string());
    let mut subject_args = vec!["--z3-mode".to_string()];
    subject_args.extend(oracle_args.iter().cloned());
    let mut baseline = baseline_args
        .iter()
        .map(|argument| (*argument).to_string())
        .collect::<Vec<_>>();
    baseline.push("-in".to_string());
    require_oracle_difference(
        CaseSpec {
            id: "source-parameter".to_string(),
            oracle_args,
            subject_args,
            input: input.as_bytes().to_vec(),
            comparator: Comparator::ExactBytes,
            style: RunStyle::Batch,
            file_extension: "smt2".to_string(),
            artifact_policy,
            source_owner: None,
            effect_requirement: EffectRequirement::Inherent,
            oracle_baseline: None,
        },
        BaselineSpec {
            args: baseline,
            input: input.into_bytes(),
            style: RunStyle::Batch,
        },
    )
}

fn pigeonhole_sat_input(pigeons: usize, holes: usize) -> String {
    let mut input = String::new();
    for pigeon in 0..pigeons {
        for hole in 0..holes {
            input.push_str(&format!("(declare-const p{pigeon}_{hole} Bool)\n"));
        }
        input.push_str("(assert (or");
        for hole in 0..holes {
            input.push_str(&format!(" p{pigeon}_{hole}"));
        }
        input.push_str("))\n");
        for first in 0..holes {
            for second in (first + 1)..holes {
                input.push_str(&format!(
                    "(assert (or (not p{pigeon}_{first}) (not p{pigeon}_{second})))\n"
                ));
            }
        }
    }
    for hole in 0..holes {
        for first in 0..pigeons {
            for second in (first + 1)..pigeons {
                input.push_str(&format!(
                    "(assert (or (not p{first}_{hole}) (not p{second}_{hole})))\n"
                ));
            }
        }
    }
    input.push_str("(apply sat)\n(exit)\n");
    input
}

fn source_parameter_witness_case(name: &str) -> Option<CaseSpec> {
    const PROOF_GRAPH: &str = "(set-option :produce-proofs true)\n(declare-const a Bool)\n(assert a)\n(assert (not a))\n(check-sat)\n(get-proof-graph)\n(exit)\n";
    const LIA_CONFLICT: &str = "(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n(assert (<= (+ x y) 0))\n(assert (>= x 1))\n(assert (>= y 1))\n(check-sat)\n(exit)\n";
    const DIRECT_SAT_CONFLICT: &str =
        "(declare-const a Bool)\n(assert a)\n(assert (not a))\n(apply sat)\n(exit)\n";
    const OPTIMIZATION: &str = "(declare-const x Int)\n(assert (<= 0 x))\n(assert (<= x 3))\n(maximize x)\n(check-sat)\n(get-model)\n(exit)\n";
    const NLSAT_CONFLICT: &str = "(set-logic QF_NRA)\n(declare-const x Real)\n(assert (> (* x x) 2.0))\n(assert (< (* x x) 1.0))\n(check-sat)\n(exit)\n";
    const FIXEDPOINT: &str = "(set-logic HORN)\n(declare-rel p ())\n(rule p)\n(query p)\n(exit)\n";
    const FIXEDPOINT_PROOF: &str = "(set-logic HORN)\n(declare-rel p ())\n(declare-rel q ())\n(rule p)\n(rule (=> p q))\n(query q)\n(exit)\n";
    const FIXEDPOINT_EMPTY_AIG: &str = "(set-logic HORN)\n(declare-rel p ())\n(query p)\n(exit)\n";
    const PROOF_SAVE: &str =
        "(declare-const a Bool)\n(assume a)\n(infer (not a))\n(get-proof)\n(exit)\n";
    const NLA_LOG: &str = "(declare-const x Real)\n(assert (= (* x x) 2.0))\n(apply smt)\n(exit)\n";

    let isolated = ArtifactPolicy::IsolatedDirectory;
    let plain = ArtifactPolicy::None;
    let case = match name {
        "dot_proof_file" => parameter_effect_case(
            &["dot_proof_file=artifact"],
            &[],
            PROOF_GRAPH.to_string(),
            isolated,
        ),
        "trace" => parameter_effect_case(
            &["trace=true", "trace_file_name=artifact"],
            &["trace_file_name=artifact"],
            LIA_CONFLICT.to_string(),
            isolated,
        ),
        "trace_file_name" => parameter_effect_case(
            &["trace_file_name=artifact", "trace=true"],
            &["trace=true"],
            LIA_CONFLICT.to_string(),
            isolated,
        ),
        "sat.drat.file" => parameter_effect_case(
            &["sat.drat.file=artifact", "sat.drat.check_unsat=true"],
            &["sat.drat.check_unsat=true"],
            DIRECT_SAT_CONFLICT.to_string(),
            isolated,
        ),
        "sat.inprocess.out" => parameter_effect_case(
            &[
                "sat.inprocess.out=artifact",
                "sat.inprocess.max=1",
                "sat.restart.max=1",
            ],
            &["sat.inprocess.max=1", "sat.restart.max=1"],
            pigeonhole_sat_input(7, 6),
            isolated,
        ),
        "solver.cancel_backup_file" => parameter_effect_case(
            &["solver.cancel_backup_file=artifact", "timeout=1"],
            &["timeout=1"],
            pigeonhole_sat_input(10, 9),
            isolated,
        ),
        "solver.axioms2files" => parameter_effect_case(
            &["solver.axioms2files=true"],
            &[],
            LIA_CONFLICT.to_string(),
            isolated,
        ),
        "solver.proof.log" => parameter_effect_case(
            &["solver.proof.log=artifact"],
            &[],
            LIA_CONFLICT.to_string(),
            isolated,
        ),
        "solver.proof.save" => parameter_effect_case(
            &["solver.proof.save=true"],
            &[],
            PROOF_SAVE.to_string(),
            plain,
        ),
        "solver.smtlib2_log" => parameter_effect_case(
            &["solver.smtlib2_log=artifact"],
            &[],
            LIA_CONFLICT.to_string(),
            isolated,
        ),
        "opt.dump_benchmarks" => parameter_effect_case(
            &["opt.dump_benchmarks=true"],
            &[],
            OPTIMIZATION.to_string(),
            isolated,
        ),
        "opt.solution_prefix" => parameter_effect_case(
            &["opt.solution_prefix=artifact"],
            &[],
            OPTIMIZATION.to_string(),
            isolated,
        ),
        "nlsat.dump_mathematica" => parameter_effect_case(
            &["nlsat.dump_mathematica=true"],
            &[],
            NLSAT_CONFLICT.to_string(),
            plain,
        ),
        "nlsat.known_sat_assignment_file_name" => parameter_effect_case(
            &["nlsat.known_sat_assignment_file_name=known-assignment"],
            &[],
            NLSAT_CONFLICT.to_string(),
            isolated,
        ),
        "fp.generate_proof_trace" => parameter_effect_case(
            &[
                "fp.generate_proof_trace=true",
                "fp.engine=bmc",
                "fp.print_certificate=true",
            ],
            &[
                "fp.generate_proof_trace=false",
                "fp.engine=bmc",
                "fp.print_certificate=true",
            ],
            FIXEDPOINT_PROOF.to_string(),
            plain,
        ),
        "fp.print_aig" => parameter_effect_case(
            &["fp.print_aig=artifact", "fp.engine=datalog"],
            &["fp.engine=datalog"],
            FIXEDPOINT_EMPTY_AIG.to_string(),
            isolated,
        ),
        "fp.spacer.dump_benchmarks" => parameter_effect_case(
            &[
                "fp.spacer.dump_benchmarks=true",
                "fp.spacer.dump_threshold=0",
                "fp.engine=spacer",
            ],
            &["fp.spacer.dump_threshold=0", "fp.engine=spacer"],
            FIXEDPOINT.to_string(),
            isolated,
        ),
        "fp.spacer.trace_file" => parameter_effect_case(
            &["fp.spacer.trace_file=artifact", "fp.engine=spacer"],
            &["fp.engine=spacer"],
            FIXEDPOINT.to_string(),
            isolated,
        ),
        "smt.arith.dump_bound_lemmas" => parameter_effect_case(
            &["smt.arith.dump_bound_lemmas=true"],
            &[],
            LIA_CONFLICT.to_string(),
            plain,
        ),
        "smt.arith.dump_lemmas" => parameter_effect_case(
            &["smt.arith.dump_lemmas=true"],
            &[],
            LIA_CONFLICT.to_string(),
            plain,
        ),
        "smt.arith.nl.log" => parameter_effect_case(
            &["smt.arith.nl.log=true"],
            &[],
            NLA_LOG.to_string(),
            isolated,
        ),
        _ => return None,
    };
    Some(case)
}

fn source_parameter_case(item: &z3_source_inventory::ObservableItem) -> CaseSpec {
    const INPUT: &str = "(set-option :produce-models true)\n(declare-const a Bool)\n(declare-const b Bool)\n(assert (or a b))\n(check-sat)\n(get-model)\n(exit)\n";
    if let Some(case) = source_parameter_witness_case(&item.name) {
        return case;
    }
    let Some(alternate) = parameter_alternate(item) else {
        // Symbol/string domains need a parameter-specific valid alternative,
        // and these artifact-producing booleans need a sandboxed witness.
        // Do not execute a guessed value merely to manufacture a row.
        return unresolved_case(cli_case("source-parameter", &["-in"], "(exit)\n"));
    };
    let argument = format!("{}={alternate}", item.name);
    let mut case = cli_case("source-parameter", &[&argument, "-in"], INPUT);
    case = require_oracle_difference(
        case,
        BaselineSpec {
            args: vec!["-in".to_string()],
            input: INPUT.as_bytes().to_vec(),
            style: RunStyle::Batch,
        },
    );
    case
}

fn source_parameter_module_case(
    module: &z3_source_inventory::ObservableItem,
    items: &[z3_source_inventory::ObservableItem],
) -> Result<CaseSpec, String> {
    let prefix = format!("{}.", module.name);
    let representative = items
        .iter()
        .filter(|item| item.category == "module-parameter" && item.name.starts_with(&prefix))
        .find(|item| parameter_alternate(item).is_some())
        .or_else(|| {
            items
                .iter()
                .find(|item| item.category == "module-parameter" && item.name.starts_with(&prefix))
        })
        .ok_or_else(|| format!("Z3 parameter module {} has no parameter owner", module.name))?;
    Ok(source_parameter_case(representative))
}

fn cli_introspection_only(name: &str) -> bool {
    matches!(
        name,
        "h" | "help"
            | "?"
            | "p"
            | "pd"
            | "pm"
            | "pmmd"
            | "pp"
            | "tactics"
            | "tacticsmd"
            | "simplifiers"
            | "probes"
            | "version"
    )
}

fn source_cli_option_case(name: &str) -> CaseSpec {
    const INPUT: &str = "(check-sat)\n(exit)\n";
    let flag = match name {
        "?" => "-?".to_string(),
        "T" => "-T:0".to_string(),
        "dbg" => "-dbg:ay-z3-behavioral".to_string(),
        "file" => format!("-file:{FILE_PLACEHOLDER}"),
        "memory" => "-memory:64".to_string(),
        "pm" => "-pm:smt".to_string(),
        "pmmd" => "-pmmd:smt".to_string(),
        "pp" => "-pp:timeout".to_string(),
        "t" => "-t:0".to_string(),
        "tacticsmd" => "-tacticsmd:simplify".to_string(),
        "tr" => "-tr:ay-z3-behavioral".to_string(),
        "v" => "-v:0".to_string(),
        other => format!("-{other}"),
    };
    let mut case = cli_case("source-cli-option", &[&flag, "-in"], INPUT);
    if name == "file" {
        case.style = RunStyle::File;
        case.oracle_args = vec![flag.clone()];
        case.subject_args = vec!["--z3-mode".to_string(), flag];
    }
    if cli_introspection_only(name) {
        // These flags' specified behavior is the exact catalog/help/version
        // transcript and exit status produced by the invocation itself.
        return case;
    }
    require_oracle_difference(
        case,
        BaselineSpec {
            args: vec!["-in".to_string()],
            input: INPUT.as_bytes().to_vec(),
            style: RunStyle::Batch,
        },
    )
}

fn source_cli_help_case(item: &z3_source_inventory::ObservableItem) -> CaseSpec {
    let token = item
        .detail
        .split_whitespace()
        .next()
        .unwrap_or("-h")
        .trim_end_matches(',');
    let name = token
        .trim_start_matches('-')
        .split(':')
        .next()
        .unwrap_or("h")
        .trim_end_matches('[');
    if token == "--" {
        let mut case = cli_case("source-cli-help", &["--", FILE_PLACEHOLDER], "(exit)\n");
        case.style = RunStyle::File;
        case.oracle_args = vec!["--".to_string(), FILE_PLACEHOLDER.to_string()];
        case.subject_args = vec![
            "--z3-mode".to_string(),
            "--".to_string(),
            FILE_PLACEHOLDER.to_string(),
        ];
        return case;
    }
    source_cli_option_case(name)
}

fn input_for_extension(extension: &str) -> &'static str {
    match extension {
        "cnf" | "dimacs" => "p cnf 1 1\n1 0\n",
        "wcnf" => "p wcnf 1 1 2\n1 1 0\n",
        "opb" => "* #variable= 1 #constraint= 1\n+1 x1 >= 1 ;\n",
        "lp" => "Minimize\n obj: x\nSubject To\n c1: x >= 0\nEnd\n",
        "datalog" | "dl" => "(declare-rel p ())\n(rule p)\n(query p)\n",
        "fof" | "p" | "tff" | "thf" | "tptp" => "fof(a,axiom,$true).\n",
        // A non-redundant theory clause is accepted by Z3's DRAT reader and
        // produces a stable record/statistics transcript. Ordinary clauses are
        // rejected by this exact frontend before they can seed its checker.
        "drat" => "a arith 1 0\n",
        // This is a complete Z3 API-replay log: version header plus a user-log
        // message. It exercises replay dispatch without calling an ABI entry.
        "log" => "V \"5.0.0.0\"\nM \"ay-z3-log-dispatch\"\n",
        _ => "(check-sat)\n(exit)\n",
    }
}

fn source_filename_extension_case(extension: &str) -> CaseSpec {
    let input = input_for_extension(extension);
    let case = CaseSpec {
        id: "source-filename-extension".to_string(),
        oracle_args: vec![FILE_PLACEHOLDER.to_string()],
        subject_args: vec!["--z3-mode".to_string(), FILE_PLACEHOLDER.to_string()],
        input: input.as_bytes().to_vec(),
        comparator: Comparator::ExactBytes,
        style: RunStyle::File,
        file_extension: extension.to_string(),
        artifact_policy: ArtifactPolicy::None,
        source_owner: None,
        effect_requirement: EffectRequirement::Inherent,
        oracle_baseline: None,
    };
    if matches!(extension, "smt" | "smt2") {
        // SMT extensions select the same parser as an explicit `-smt2` run.
        return case;
    }
    let mut case = require_oracle_difference(
        case,
        BaselineSpec {
            args: vec!["-smt2".to_string(), FILE_PLACEHOLDER.to_string()],
            input: input.as_bytes().to_vec(),
            style: RunStyle::File,
        },
    );
    if extension == "drat" {
        // Z3 5.0.0 stores a `.drat` argument separately from `g_input_file`
        // but still applies the generic "input file was not specified" guard.
        // `-in` satisfies that guard; the DRAT reader still consumes the file.
        case.oracle_args.push("-in".to_string());
        case.subject_args.push("-in".to_string());
    } else if extension == "log" {
        // Replay emits wall/allocation telemetry. Preserve its exact shape and
        // message while eliding only numeric values.
        case.comparator = Comparator::ComponentTrace;
    }
    case
}

fn source_input_mode_case(mode: &str) -> CaseSpec {
    let (extension, flag) = match mode {
        "IN_DATALOG" => ("datalog", Some("-dl")),
        "IN_DIMACS" => ("cnf", Some("-dimacs")),
        "IN_DRAT" => ("drat", None),
        "IN_LP" => ("lp", Some("-lp")),
        "IN_OPB" => ("opb", Some("-pbo")),
        "IN_SMTLIB_2" => ("smt2", Some("-smt2")),
        "IN_TPTP" => ("tptp", Some("-tptp")),
        "IN_WCNF" => ("wcnf", Some("-wcnf")),
        "IN_Z3_LOG" => ("log", Some("-log")),
        _ => ("smt2", None),
    };
    let mut case = source_filename_extension_case(extension);
    if let Some(flag) = flag {
        case.oracle_args = vec![flag.to_string(), FILE_PLACEHOLDER.to_string()];
        case.subject_args = vec![
            "--z3-mode".to_string(),
            flag.to_string(),
            FILE_PLACEHOLDER.to_string(),
        ];
    }
    case
}

fn ownership_sha256(cases: &[CaseSpec]) -> String {
    let mut lines = cases
        .iter()
        .filter_map(|case| case.source_owner.as_ref().map(SourceOwner::canonical_line))
        .collect::<Vec<_>>();
    lines.sort();
    sha256_bytes(lines.concat().as_bytes())
}

#[cfg(test)]
fn unresolved_ownership_sha256(cases: &[CaseSpec]) -> String {
    let mut lines = cases
        .iter()
        .filter(|case| case.effect_requirement == EffectRequirement::Unresolved)
        .filter_map(|case| case.source_owner.as_ref().map(SourceOwner::canonical_line))
        .collect::<Vec<_>>();
    lines.sort();
    sha256_bytes(lines.concat().as_bytes())
}

fn audited_gap_universe_ownership_sha256(cases: &[CaseSpec]) -> String {
    let mut lines = cases
        .iter()
        .filter(|case| {
            case.effect_requirement == EffectRequirement::Unresolved
                || case
                    .source_owner
                    .as_ref()
                    .is_some_and(|owner| owner.category == "logic-recognizer-literal")
                || case.source_owner.as_ref().is_some_and(|owner| {
                    owner.category == "smt-command"
                        && RESOLVED_EXTENSION_COMMANDS.contains(&owner.name.as_str())
                })
                || case.source_owner.as_ref().is_some_and(|owner| {
                    owner.category == "declaration-builtin"
                        && declaration_builtins::semantic_predicate(&owner.name).is_some()
                })
                || case.source_owner.as_ref().is_some_and(|owner| {
                    owner.category == "smt-info-key"
                        && RESOLVED_INFO_KEYS.contains(&owner.name.as_str())
                })
                || case.source_owner.as_ref().is_some_and(|owner| {
                    owner.category == "smt-option-key"
                        && RESOLVED_OPTION_KEYS.contains(&owner.name.as_str())
                })
                || case.source_owner.as_ref().is_some_and(|owner| {
                    owner.category == "smt-parser-token"
                        && parser_tokens::semantic_witness(&owner.name).is_some()
                })
        })
        .filter_map(|case| case.source_owner.as_ref().map(SourceOwner::canonical_line))
        .collect::<Vec<_>>();
    lines.sort();
    sha256_bytes(lines.concat().as_bytes())
}

fn source_proven_no_effect_ownership_sha256(cases: &[CaseSpec]) -> String {
    let mut lines = cases
        .iter()
        .filter(|case| case.effect_requirement == EffectRequirement::SourceProvenNoEffect)
        .filter_map(|case| case.source_owner.as_ref().map(SourceOwner::canonical_line))
        .collect::<Vec<_>>();
    lines.sort();
    sha256_bytes(lines.concat().as_bytes())
}

fn case_catalog(
    observable_items: &[z3_source_inventory::ObservableItem],
) -> Result<Vec<CaseSpec>, String> {
    if SUPPORTED_TACTIC_NAMES.len() != TACTIC_COUNT {
        return Err(format!(
            "AY tactic registry drift: expected {TACTIC_COUNT}, got {}",
            SUPPORTED_TACTIC_NAMES.len()
        ));
    }
    let mut cases = standard_command_cases();
    cases.extend(standard_command_arity_cases());
    cases.extend(extension_command_cases());
    cases.extend(extension_command_arity_cases());
    cases.extend(state_and_diagnostic_cases());
    cases.extend(cli_cases());
    cases.extend(combinator_cases());
    for tactic in SUPPORTED_TACTIC_NAMES {
        cases.push(batch_case(
            format!("tactic.primitive.{}", case_token(tactic)),
            &format!("(set-logic ALL)\n(assert (= 1 1))\n(apply {tactic})\n(exit)\n"),
        ));
    }
    for probe in PROBE_NAMES {
        cases.push(batch_case(
            format!("tactic.probe.{}", case_token(probe)),
            &format!(
                "(set-logic ALL)\n(declare-const x Int)\n(assert (> x 0))\n(apply (fail-if {probe}))\n(exit)\n"
            ),
        ));
    }
    cases.push(CaseSpec {
        id: "streaming.echo-check-sat-echo".to_string(),
        oracle_args: vec!["-in".to_string()],
        subject_args: vec!["--z3-mode".to_string(), "-in".to_string()],
        input: b"three phase writes with response required before next write".to_vec(),
        comparator: Comparator::ExactBytes,
        style: RunStyle::Streaming,
        file_extension: "smt2".to_string(),
        artifact_policy: ArtifactPolicy::None,
        source_owner: None,
        effect_requirement: EffectRequirement::Inherent,
        oracle_baseline: None,
    });
    if cases.len() != BASE_CASE_COUNT {
        return Err(format!(
            "z3-behavioral base catalog drift: expected {BASE_CASE_COUNT}, got {}",
            cases.len()
        ));
    }
    if observable_items.len() != EXPECTED_SOURCE_OWNER_COUNT
        || z3_source_inventory::observable_manifest_sha256(observable_items)
            != z3_source_inventory::EXPECTED_OBSERVABLE_SHA256
    {
        return Err("z3-behavioral received a foreign observable source manifest".to_string());
    }
    for item in observable_items {
        cases.push(source_owned_case(item, observable_items)?);
    }
    cases.sort_by(|left, right| left.id.cmp(&right.id));
    let ids = cases
        .iter()
        .map(|case| case.id.as_str())
        .collect::<BTreeSet<_>>();
    if ids.len() != cases.len() {
        return Err("duplicate z3-behavioral case id".to_string());
    }
    if cases.len() != EXPECTED_CASE_COUNT {
        return Err(format!(
            "z3-behavioral catalog drift: expected {EXPECTED_CASE_COUNT}, got {}",
            cases.len()
        ));
    }
    let source_owners = cases
        .iter()
        .filter_map(|case| case.source_owner.as_ref())
        .collect::<Vec<_>>();
    let actual_ownership_sha256 = ownership_sha256(&cases);
    if source_owners.len() != EXPECTED_SOURCE_OWNER_COUNT
        || source_owners.iter().collect::<BTreeSet<_>>().len() != source_owners.len()
        || actual_ownership_sha256 != EXPECTED_OWNERSHIP_SHA256
    {
        return Err(format!(
            "z3-behavioral source-item ownership is not exact and unique: expected count={EXPECTED_SOURCE_OWNER_COUNT} sha256={EXPECTED_OWNERSHIP_SHA256}, got count={} sha256={actual_ownership_sha256}",
            source_owners.len()
        ));
    }
    let unresolved_source_owners = cases
        .iter()
        .filter(|case| {
            case.source_owner.is_some() && case.effect_requirement == EffectRequirement::Unresolved
        })
        .count();
    let unresolved_owner_keys = cases
        .iter()
        .filter(|case| case.effect_requirement == EffectRequirement::Unresolved)
        .filter_map(|case| case.source_owner.as_ref())
        .map(|owner| (owner.category.as_str(), owner.name.as_str()))
        .collect::<BTreeSet<_>>();
    let mut expected_unresolved_owner_keys = EXPECTED_UNRESOLVED_COMMAND_OWNER_KEYS
        .into_iter()
        .collect::<BTreeSet<_>>();
    expected_unresolved_owner_keys.extend(
        observable_items
            .iter()
            .filter(|item| {
                UNRESOLVED_SOURCE_CATEGORIES.contains(&item.category.as_str())
                    && !(item.category == "declaration-builtin"
                        && declaration_builtins::semantic_predicate(&item.name).is_some())
                    && !(item.category == "smt-info-key"
                        && RESOLVED_INFO_KEYS.contains(&item.name.as_str()))
                    && !(item.category == "smt-option-key"
                        && RESOLVED_OPTION_KEYS.contains(&item.name.as_str()))
                    && !(item.category == "smt-parser-token"
                        && parser_tokens::semantic_witness(&item.name).is_some())
            })
            .map(|item| (item.category.as_str(), item.name.as_str())),
    );
    if unresolved_source_owners != EXPECTED_UNRESOLVED_SOURCE_OWNERS
        || unresolved_owner_keys != expected_unresolved_owner_keys
    {
        return Err("z3-behavioral explicit unresolved source-owner inventory drift".to_string());
    }
    let logic_recognizer_cases = cases
        .iter()
        .filter(|case| {
            case.source_owner
                .as_ref()
                .is_some_and(|owner| owner.category == "logic-recognizer-literal")
        })
        .collect::<Vec<_>>();
    let logic_recognizer_names = logic_recognizer_cases
        .iter()
        .filter_map(|case| case.source_owner.as_ref().map(|owner| owner.name.as_str()))
        .collect::<BTreeSet<_>>();
    if logic_recognizer_names
        != RESOLVED_LOGIC_RECOGNIZER_LITERALS
            .into_iter()
            .collect::<BTreeSet<_>>()
        || logic_recognizer_cases.iter().any(|case| {
            case.effect_requirement != EffectRequirement::OracleDiffersFromBaseline
                || case.oracle_baseline.is_none()
        })
    {
        return Err("z3-behavioral resolved logic-recognizer inventory drift".to_string());
    }
    let resolved_extension_command_cases = cases
        .iter()
        .filter(|case| {
            case.source_owner.as_ref().is_some_and(|owner| {
                owner.category == "smt-command"
                    && RESOLVED_EXTENSION_COMMANDS.contains(&owner.name.as_str())
            })
        })
        .collect::<Vec<_>>();
    let resolved_extension_command_names = resolved_extension_command_cases
        .iter()
        .filter_map(|case| case.source_owner.as_ref().map(|owner| owner.name.as_str()))
        .collect::<BTreeSet<_>>();
    if resolved_extension_command_names
        != RESOLVED_EXTENSION_COMMANDS
            .into_iter()
            .collect::<BTreeSet<_>>()
        || resolved_extension_command_cases.iter().any(|case| {
            case.effect_requirement != EffectRequirement::OracleDiffersFromBaseline
                || case.oracle_baseline.is_none()
        })
    {
        return Err("z3-behavioral resolved extension-command inventory drift".to_string());
    }
    let resolved_declaration_builtin_cases = cases
        .iter()
        .filter(|case| {
            case.source_owner.as_ref().is_some_and(|owner| {
                owner.category == "declaration-builtin"
                    && declaration_builtins::semantic_predicate(&owner.name).is_some()
            })
        })
        .collect::<Vec<_>>();
    let resolved_declaration_builtin_names = resolved_declaration_builtin_cases
        .iter()
        .filter_map(|case| case.source_owner.as_ref().map(|owner| owner.name.as_str()))
        .collect::<BTreeSet<_>>();
    if resolved_declaration_builtin_names
        != declaration_builtins::semantic_owner_names().collect::<BTreeSet<_>>()
        || resolved_declaration_builtin_cases.iter().any(|case| {
            case.effect_requirement != EffectRequirement::OracleDiffersFromBaseline
                || case.oracle_baseline.is_none()
        })
    {
        return Err("z3-behavioral resolved declaration-builtin inventory drift".to_string());
    }
    let resolved_info_key_cases = cases
        .iter()
        .filter(|case| {
            case.source_owner.as_ref().is_some_and(|owner| {
                owner.category == "smt-info-key"
                    && RESOLVED_INFO_KEYS.contains(&owner.name.as_str())
            })
        })
        .collect::<Vec<_>>();
    let resolved_info_key_names = resolved_info_key_cases
        .iter()
        .filter_map(|case| case.source_owner.as_ref().map(|owner| owner.name.as_str()))
        .collect::<BTreeSet<_>>();
    if resolved_info_key_names != RESOLVED_INFO_KEYS.into_iter().collect::<BTreeSet<_>>()
        || resolved_info_key_cases.iter().any(|case| {
            case.effect_requirement != EffectRequirement::OracleDiffersFromBaseline
                || case.oracle_baseline.is_none()
        })
    {
        return Err("z3-behavioral resolved info-key inventory drift".to_string());
    }
    let resolved_option_key_cases = cases
        .iter()
        .filter(|case| {
            case.source_owner.as_ref().is_some_and(|owner| {
                owner.category == "smt-option-key"
                    && RESOLVED_OPTION_KEYS.contains(&owner.name.as_str())
            })
        })
        .collect::<Vec<_>>();
    let resolved_option_key_names = resolved_option_key_cases
        .iter()
        .filter_map(|case| case.source_owner.as_ref().map(|owner| owner.name.as_str()))
        .collect::<BTreeSet<_>>();
    if resolved_option_key_names != RESOLVED_OPTION_KEYS.into_iter().collect::<BTreeSet<_>>()
        || resolved_option_key_cases.iter().any(|case| {
            case.effect_requirement != EffectRequirement::OracleDiffersFromBaseline
                || case.oracle_baseline.is_none()
        })
    {
        return Err("z3-behavioral resolved option-key inventory drift".to_string());
    }
    let resolved_parser_token_cases = cases
        .iter()
        .filter(|case| {
            case.source_owner.as_ref().is_some_and(|owner| {
                owner.category == "smt-parser-token"
                    && parser_tokens::semantic_witness(&owner.name).is_some()
            })
        })
        .collect::<Vec<_>>();
    let resolved_parser_token_names = resolved_parser_token_cases
        .iter()
        .filter_map(|case| case.source_owner.as_ref().map(|owner| owner.name.as_str()))
        .collect::<BTreeSet<_>>();
    if resolved_parser_token_names != parser_tokens::semantic_owner_names().collect::<BTreeSet<_>>()
        || resolved_parser_token_cases.iter().any(|case| {
            case.effect_requirement != EffectRequirement::OracleDiffersFromBaseline
                || case.oracle_baseline.is_none()
        })
    {
        return Err("z3-behavioral resolved parser-token inventory drift".to_string());
    }
    let actual_audited_gap_universe_sha256 = audited_gap_universe_ownership_sha256(&cases);
    if unresolved_source_owners
        + logic_recognizer_cases.len()
        + resolved_extension_command_cases.len()
        + resolved_declaration_builtin_cases.len()
        + resolved_info_key_cases.len()
        + resolved_option_key_cases.len()
        + resolved_parser_token_cases.len()
        != EXPECTED_AUDITED_GAP_UNIVERSE_OWNERS
        || actual_audited_gap_universe_sha256 != EXPECTED_AUDITED_GAP_UNIVERSE_OWNERSHIP_SHA256
    {
        return Err(format!(
            "z3-behavioral authenticated audited-gap universe drift: expected count={EXPECTED_AUDITED_GAP_UNIVERSE_OWNERS} sha256={EXPECTED_AUDITED_GAP_UNIVERSE_OWNERSHIP_SHA256}, got count={} sha256={actual_audited_gap_universe_sha256}",
            unresolved_source_owners
                + logic_recognizer_cases.len()
                + resolved_extension_command_cases.len()
                + resolved_declaration_builtin_cases.len()
                + resolved_info_key_cases.len()
                + resolved_option_key_cases.len()
                + resolved_parser_token_cases.len()
        ));
    }
    let source_proven_no_effect_owner_keys = cases
        .iter()
        .filter(|case| case.effect_requirement == EffectRequirement::SourceProvenNoEffect)
        .filter_map(|case| case.source_owner.as_ref())
        .map(|owner| (owner.category.as_str(), owner.name.as_str()))
        .collect::<BTreeSet<_>>();
    let expected_source_proven_no_effect_owner_keys = EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNER_KEYS
        .into_iter()
        .collect::<BTreeSet<_>>();
    if source_proven_no_effect_owner_keys.len() != EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNERS
        || source_proven_no_effect_owner_keys != expected_source_proven_no_effect_owner_keys
        || source_proven_no_effect_ownership_sha256(&cases)
            != EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNERSHIP_SHA256
    {
        return Err("z3-behavioral source-proven no-effect owner inventory drift".to_string());
    }
    if cases.iter().any(|case| {
        let requires_baseline = matches!(
            case.effect_requirement,
            EffectRequirement::OracleDiffersFromBaseline | EffectRequirement::SourceProvenNoEffect
        );
        requires_baseline != case.oracle_baseline.is_some()
    }) {
        return Err("z3-behavioral effect-baseline ownership drift".to_string());
    }
    let standard = cases
        .iter()
        .filter_map(|case| case.id.strip_prefix("command.standard."))
        .collect::<BTreeSet<_>>();
    if standard != SMTLIB_COMMANDS.into_iter().collect() {
        return Err("z3-behavioral standard-command inventory drift".to_string());
    }
    let arities = cases
        .iter()
        .filter_map(|case| case.id.strip_prefix("arity.standard."))
        .collect::<BTreeSet<_>>();
    if arities != SMTLIB_COMMANDS.into_iter().collect() {
        return Err("z3-behavioral standard-command arity inventory drift".to_string());
    }
    Ok(cases)
}

fn standard_command_cases() -> Vec<CaseSpec> {
    [
        ("assert", "(assert true)\n(check-sat)\n(exit)\n"),
        ("check-sat", "(check-sat)\n(exit)\n"),
        (
            "check-sat-assuming",
            "(declare-const a Bool)\n(check-sat-assuming (a (not a)))\n(exit)\n",
        ),
        (
            "declare-const",
            "(declare-const a Bool)\n(assert a)\n(check-sat)\n(exit)\n",
        ),
        (
            "declare-datatype",
            "(declare-datatype D ((a) (b)))\n(declare-const d D)\n(check-sat)\n(exit)\n",
        ),
        (
            "declare-datatypes",
            "(declare-datatypes ((D 0) (E 0)) (((d)) ((e))))\n(check-sat)\n(exit)\n",
        ),
        (
            "declare-fun",
            "(declare-fun f (Bool) Bool)\n(assert (= (f true) (f true)))\n(check-sat)\n(exit)\n",
        ),
        (
            "declare-sort",
            "(declare-sort U 0)\n(declare-const u U)\n(check-sat)\n(exit)\n",
        ),
        (
            "declare-sort-parameter",
            "(declare-sort-parameter T)\n(declare-const x T)\n(check-sat)\n(exit)\n",
        ),
        (
            "define-const",
            "(define-const x Int 2)\n(assert (= x 2))\n(check-sat)\n(exit)\n",
        ),
        (
            "define-fun",
            "(define-fun f ((x Int)) Int (+ x 1))\n(assert (= (f 1) 2))\n(check-sat)\n(exit)\n",
        ),
        (
            "define-fun-rec",
            "(define-fun-rec f ((x Int)) Int (ite (= x 0) 0 (f (- x 1))))\n(assert (= (f 0) 0))\n(check-sat)\n(exit)\n",
        ),
        (
            "define-funs-rec",
            "(define-funs-rec ((f ((x Int)) Int) (g ((x Int)) Int)) ((ite (= x 0) 0 (g (- x 1))) (ite (= x 0) 0 (f (- x 1)))))\n(assert (= (f 0) 0))\n(check-sat)\n(exit)\n",
        ),
        (
            "define-sort",
            "(define-sort I () Int)\n(declare-const x I)\n(assert (= x 0))\n(check-sat)\n(exit)\n",
        ),
        ("echo", "(echo \"hello\")\n(exit)\n"),
        ("exit", "(exit)\n(echo \"must-not-run\")\n"),
        (
            "get-assertions",
            "(set-option :interactive-mode true)\n(assert (and true false))\n(get-assertions)\n(exit)\n",
        ),
        (
            "get-assignment",
            "(set-option :produce-assignments true)\n(assert (! true :named n))\n(check-sat)\n(get-assignment)\n(exit)\n",
        ),
        ("get-info", "(get-info :name)\n(exit)\n"),
        (
            "get-model",
            "(set-option :produce-models true)\n(declare-const x Int)\n(assert (= x 7))\n(check-sat)\n(get-model)\n(exit)\n",
        ),
        ("get-option", "(get-option :print-success)\n(exit)\n"),
        (
            "get-proof",
            "(set-option :produce-proofs true)\n(assert false)\n(check-sat)\n(get-proof)\n(exit)\n",
        ),
        (
            "get-unsat-assumptions",
            "(set-option :produce-unsat-assumptions true)\n(declare-const a Bool)\n(check-sat-assuming (a (not a)))\n(get-unsat-assumptions)\n(exit)\n",
        ),
        (
            "get-unsat-core",
            "(set-option :produce-unsat-cores true)\n(assert (! false :named n))\n(check-sat)\n(get-unsat-core)\n(exit)\n",
        ),
        (
            "get-value",
            "(set-option :produce-models true)\n(declare-const x Int)\n(assert (= x 7))\n(check-sat)\n(get-value (x (+ x 1)))\n(exit)\n",
        ),
        ("pop", "(push 1)\n(assert false)\n(pop 1)\n(check-sat)\n(exit)\n"),
        ("push", "(push 1)\n(assert false)\n(check-sat)\n(exit)\n"),
        ("reset", "(declare-const x Bool)\n(reset)\n(check-sat)\n(exit)\n"),
        (
            "reset-assertions",
            "(push 1)\n(assert false)\n(reset-assertions)\n(get-info :assertion-stack-levels)\n(check-sat)\n(exit)\n",
        ),
        ("set-info", "(set-info :status sat)\n(check-sat)\n(exit)\n"),
        ("set-logic", "(set-logic ALL)\n(check-sat)\n(exit)\n"),
        (
            "set-option",
            "(set-option :print-success true)\n(set-option :print-success false)\n(check-sat)\n(exit)\n",
        ),
    ]
    .into_iter()
    .map(|(name, input)| batch_case(format!("command.standard.{name}"), input))
    .collect()
}

fn standard_command_arity_cases() -> Vec<CaseSpec> {
    [
        ("assert", "(assert)"),
        ("check-sat", "(check-sat 0)"),
        ("check-sat-assuming", "(check-sat-assuming () ())"),
        ("declare-const", "(declare-const x)"),
        ("declare-datatype", "(declare-datatype D)"),
        ("declare-datatypes", "(declare-datatypes () () extra)"),
        ("declare-fun", "(declare-fun f () Bool extra)"),
        ("declare-sort", "(declare-sort U 0 extra)"),
        ("declare-sort-parameter", "(declare-sort-parameter T extra)"),
        ("define-const", "(define-const x Int)"),
        ("define-fun", "(define-fun f () Bool)"),
        ("define-fun-rec", "(define-fun-rec f () Bool)"),
        ("define-funs-rec", "(define-funs-rec () () extra)"),
        ("define-sort", "(define-sort S () Bool extra)"),
        ("echo", "(echo)"),
        ("exit", "(exit extra)"),
        ("get-assertions", "(get-assertions extra)"),
        ("get-assignment", "(get-assignment extra)"),
        ("get-info", "(get-info)"),
        ("get-model", "(get-model bad-index)"),
        ("get-option", "(get-option)"),
        ("get-proof", "(get-proof extra)"),
        ("get-unsat-assumptions", "(get-unsat-assumptions extra)"),
        ("get-unsat-core", "(get-unsat-core extra extra)"),
        ("get-value", "(get-value)"),
        ("pop", "(pop 1 1)"),
        ("push", "(push 1 1)"),
        ("reset", "(reset extra)"),
        ("reset-assertions", "(reset-assertions extra)"),
        ("set-info", "(set-info :status sat extra)"),
        ("set-logic", "(set-logic ALL extra)"),
        ("set-option", "(set-option :print-success true extra)"),
    ]
    .into_iter()
    .map(|(name, malformed)| {
        batch_case(
            format!("arity.standard.{name}"),
            &format!("{malformed}\n(echo \"recovered\")\n(exit)\n"),
        )
    })
    .collect()
}

fn extension_command_cases() -> Vec<CaseSpec> {
    [
        (
            "apply",
            "(declare-const x Int)\n(assert (= (+ x 0) 1))\n(apply simplify)\n(exit)\n",
        ),
        (
            "assert-soft",
            "(declare-const a Bool)\n(assert-soft a :weight 2 :id g)\n(check-sat)\n(get-objectives)\n(exit)\n",
        ),
        (
            "check-sat-using",
            "(assert true)\n(check-sat-using (then simplify smt))\n(exit)\n",
        ),
        (
            "check-synth",
            "(synth-fun f ((x Int)) Int)\n(constraint (= (f 0) 0))\n(check-synth)\n(exit)\n",
        ),
        (
            "compute-interpolant",
            "(declare-const a Bool)\n(compute-interpolant a (not a))\n(exit)\n",
        ),
        (
            "constraint",
            "(synth-fun f ((x Int)) Int)\n(constraint (= (f 0) 0))\n(check-synth)\n(exit)\n",
        ),
        (
            "declare-rel",
            "(declare-rel p (Int))\n(declare-var x Int)\n(rule (p 0))\n(query p)\n(exit)\n",
        ),
        (
            "declare-var",
            "(declare-rel p (Int))\n(declare-var x Int)\n(rule (=> (= x 0) (p x)))\n(query p)\n(exit)\n",
        ),
        (
            "eval",
            "(set-option :produce-models true)\n(declare-const x Int)\n(assert (= x 7))\n(check-sat)\n(eval (+ x 1))\n(exit)\n",
        ),
        (
            "get-abduct",
            "(declare-const a Bool)\n(assert a)\n(get-abduct abd a)\n(exit)\n",
        ),
        (
            "get-consequences",
            "(declare-const a Bool)\n(assert a)\n(get-consequences () (a))\n(exit)\n",
        ),
        (
            "get-interpolant",
            "(declare-const a Bool)\n(get-interpolant a (not a))\n(exit)\n",
        ),
        (
            "get-objectives",
            "(declare-const x Int)\n(assert (and (<= 0 x) (<= x 2)))\n(maximize x)\n(check-sat)\n(get-objectives)\n(exit)\n",
        ),
        (
            "inv-constraint",
            "(synth-inv inv ((x Int)))\n(define-fun pre ((x Int)) Bool (= x 0))\n(define-fun trans ((x Int) (xp Int)) Bool (= xp (+ x 1)))\n(define-fun post ((x Int)) Bool (>= x 0))\n(inv-constraint inv pre trans post)\n(check-synth)\n(exit)\n",
        ),
        (
            "maximize",
            "(declare-const x Int)\n(assert (and (<= 0 x) (<= x 2)))\n(maximize x)\n(check-sat)\n(get-objectives)\n(exit)\n",
        ),
        (
            "minimize",
            "(declare-const x Int)\n(assert (and (<= 0 x) (<= x 2)))\n(minimize x)\n(check-sat)\n(get-objectives)\n(exit)\n",
        ),
        (
            "query",
            "(declare-rel p ())\n(rule p)\n(query p)\n(exit)\n",
        ),
        (
            "rule",
            "(declare-rel p ())\n(rule p)\n(query p)\n(exit)\n",
        ),
        ("simplify", "(simplify (+ 0 1))\n(exit)\n"),
        (
            "synth-fun",
            "(synth-fun f ((x Int)) Int)\n(constraint (= (f 0) 0))\n(check-synth)\n(exit)\n",
        ),
        (
            "synth-inv",
            "(synth-inv inv ((x Int)))\n(define-fun pre ((x Int)) Bool (= x 0))\n(define-fun trans ((x Int) (xp Int)) Bool (= xp (+ x 1)))\n(define-fun post ((x Int)) Bool (>= x 0))\n(inv-constraint inv pre trans post)\n(check-synth)\n(exit)\n",
        ),
    ]
    .into_iter()
    .map(|(name, input)| {
        let id = format!("command.z3-extension.{name}");
        if matches!(name, "declare-rel" | "declare-var" | "query" | "rule") {
            fixedpoint_file_case(id, input)
        } else {
            batch_case(id, input)
        }
    })
    .collect()
}

fn extension_command_arity_cases() -> Vec<CaseSpec> {
    [
        ("apply", "(apply)"),
        ("assert-soft", "(assert-soft)"),
        ("check-sat-using", "(check-sat-using)"),
        ("check-synth", "(check-synth extra)"),
        ("compute-interpolant", "(compute-interpolant true)"),
        ("constraint", "(constraint)"),
        ("declare-rel", "(declare-rel p)"),
        ("declare-var", "(declare-var x)"),
        ("eval", "(eval)"),
        ("get-abduct", "(get-abduct a)"),
        ("get-consequences", "(get-consequences ())"),
        ("get-interpolant", "(get-interpolant true)"),
        ("get-objectives", "(get-objectives extra)"),
        ("inv-constraint", "(inv-constraint inv pre trans)"),
        ("maximize", "(maximize)"),
        ("minimize", "(minimize)"),
        ("query", "(query)"),
        ("rule", "(rule)"),
        ("simplify", "(simplify)"),
        ("synth-fun", "(synth-fun f () Int extra extra)"),
        ("synth-inv", "(synth-inv inv)"),
    ]
    .into_iter()
    .map(|(name, malformed)| {
        batch_case(
            format!("arity.z3-extension.{name}"),
            &format!("{malformed}\n(echo \"recovered\")\n(exit)\n"),
        )
    })
    .collect()
}

fn state_and_diagnostic_cases() -> Vec<CaseSpec> {
    [
        (
            "artifact.assignment-invalidated",
            "(set-option :produce-assignments true)\n(assert (! true :named n))\n(check-sat)\n(push)\n(get-assignment)\n(exit)\n",
        ),
        (
            "artifact.model-invalidated-by-assert",
            "(set-option :produce-models true)\n(check-sat)\n(assert true)\n(get-model)\n(exit)\n",
        ),
        (
            "artifact.objectives-invalidated-by-push",
            "(declare-const x Int)\n(maximize x)\n(check-sat)\n(push)\n(get-objectives)\n(exit)\n",
        ),
        (
            "artifact.proof-before-check",
            "(set-option :produce-proofs true)\n(get-proof)\n(exit)\n",
        ),
        (
            "artifact.unsat-assumptions-invalidated",
            "(set-option :produce-unsat-assumptions true)\n(declare-const a Bool)\n(check-sat-assuming (a (not a)))\n(assert true)\n(get-unsat-assumptions)\n(exit)\n",
        ),
        (
            "arity.check-sat-trailing-terms",
            "(declare-const a Bool)\n(check-sat a (not a))\n(exit)\n",
        ),
        (
            "arity.get-model-indices",
            "(set-option :produce-models true)\n(check-sat)\n(get-model 0 4294967295)\n(exit)\n",
        ),
        (
            "arity.pop-default-one",
            "(push)\n(assert false)\n(pop)\n(check-sat)\n(exit)\n",
        ),
        (
            "arity.push-default-one",
            "(push)\n(assert false)\n(check-sat)\n(exit)\n",
        ),
        (
            "diagnostic.invalid-command-recovery",
            "(no-such-command)\n(echo \"recovered\")\n(exit)\n",
        ),
        (
            "diagnostic.invalid-option-recovery",
            "(set-option :no-such-option true)\n(echo \"recovered\")\n(exit)\n",
        ),
        (
            "diagnostic.malformed-term-recovery",
            "(assert 1)\n(echo \"recovered\")\n(exit)\n",
        ),
        (
            "diagnostic.pop-underflow-recovery",
            "(pop 1)\n(echo \"recovered\")\n(exit)\n",
        ),
        (
            "output.print-success-epochs",
            "(set-option :print-success true)\n(push)\n(pop)\n(reset-assertions)\n(exit)\n",
        ),
        (
            "reset-assertions.z3-retains-stack-level",
            "(push 2)\n(reset-assertions)\n(get-info :assertion-stack-levels)\n(pop 2)\n(exit)\n",
        ),
        (
            "state.global-declarations-reset-assertions",
            "(set-option :global-declarations true)\n(push)\n(declare-const x Bool)\n(reset-assertions)\n(assert x)\n(check-sat)\n(exit)\n",
        ),
        (
            "state.scoped-declarations-reset-assertions",
            "(set-option :global-declarations false)\n(push)\n(declare-const x Bool)\n(reset-assertions)\n(assert x)\n(echo \"recovered\")\n(exit)\n",
        ),
    ]
    .into_iter()
    .map(|(id, input)| batch_case(id, input))
    .collect()
}

fn cli_cases() -> Vec<CaseSpec> {
    let mut cases = vec![
        cli_case("cli.help.dash-h", &["-h"], ""),
        cli_case("cli.help.long", &["--help"], ""),
        cli_case("cli.help.question", &["-?"], ""),
        cli_case("cli.input.bare-dash", &["-"], "(check-sat)\n(exit)\n"),
        cli_case("cli.input.dimacs", &["-in", "-dimacs"], "p cnf 1 1\n1 0\n"),
        cli_case("cli.input.smt2", &["-in", "-smt2"], "(check-sat)\n(exit)\n"),
        cli_case(
            "cli.model.dash-model",
            &["-in", "-model"],
            "(declare-const x Bool)\n(assert x)\n(check-sat)\n(exit)\n",
        ),
        cli_case(
            "cli.model.dump-models",
            &["-in", "dump-models=true"],
            "(declare-const x Bool)\n(assert x)\n(check-sat)\n(exit)\n",
        ),
        cli_case(
            "cli.model.dump_models",
            &["-in", "dump_models=true"],
            "(declare-const x Bool)\n(assert x)\n(check-sat)\n(exit)\n",
        ),
        cli_case("cli.params.all", &["-in", "-p"], "(exit)\n"),
        cli_case("cli.params.descriptions", &["-in", "-pd"], "(exit)\n"),
        cli_case("cli.params.module-list", &["-in", "-pm"], "(exit)\n"),
        cli_case("cli.params.module-smt", &["-in", "-pm:smt"], "(exit)\n"),
        cli_case("cli.params.one", &["-in", "-pp:timeout"], "(exit)\n"),
        cli_case(
            "cli.resource.memory-dash",
            &["-in", "-memory:64"],
            "(check-sat)\n(exit)\n",
        ),
        cli_case(
            "cli.resource.memory-param",
            &["-in", "memory_max_size=64"],
            "(check-sat)\n(exit)\n",
        ),
        cli_case(
            "cli.resource.timeout-millis",
            &["-in", "-t:0"],
            "(check-sat)\n(exit)\n",
        ),
        cli_case(
            "cli.resource.timeout-param",
            &["-in", "timeout=0"],
            "(check-sat)\n(exit)\n",
        ),
        cli_case(
            "cli.resource.timeout-seconds",
            &["-in", "-T:0"],
            "(check-sat)\n(exit)\n",
        ),
        cli_case(
            "cli.stats.dash-st",
            &["-in", "-st"],
            "(check-sat)\n(exit)\n",
        ),
        cli_case(
            "cli.stats.param",
            &["-in", "stats=true"],
            "(check-sat)\n(exit)\n",
        ),
        cli_case(
            "cli.conflict.input-datalog-with-stdin",
            &["-in", "-dl"],
            "(exit)\n",
        ),
        cli_case(
            "cli.conflict.input-log-with-stdin",
            &["-in", "-log"],
            "(exit)\n",
        ),
        cli_case(
            "cli.conflict.input-lp-with-stdin",
            &["-in", "-lp"],
            "(exit)\n",
        ),
        cli_case(
            "cli.conflict.input-opb-with-stdin",
            &["-in", "-opb"],
            "(exit)\n",
        ),
        cli_case(
            "cli.conflict.input-wcnf-with-stdin",
            &["-in", "-wcnf"],
            "(exit)\n",
        ),
        cli_case(
            "cli.conflict.probes-with-stdin",
            &["-in", "-probes"],
            "(exit)\n",
        ),
        cli_case(
            "cli.conflict.simplifiers-with-stdin",
            &["-in", "-simplifiers"],
            "(exit)\n",
        ),
        cli_case(
            "cli.invalid.simplifier-selection-with-stdin",
            &["-in", "-simplifiers:simplify"],
            "(exit)\n",
        ),
        cli_case(
            "cli.conflict.tactics-with-stdin",
            &["-in", "-tactics"],
            "(exit)\n",
        ),
        cli_case(
            "cli.invalid.tactic-selection-with-stdin",
            &["-in", "-tactics:simplify"],
            "(exit)\n",
        ),
        cli_case(
            "cli.conflict.params-markdown-with-stdin",
            &["-in", "-pmmd:smt"],
            "(exit)\n",
        ),
        cli_case("cli.version.dash-version", &["-version"], ""),
        cli_case("cli.version.long", &["--version"], ""),
        cli_case("cli.version.short-capital", &["-V"], ""),
        cli_case("cli.version.short-v", &["-v"], ""),
        cli_case(
            "cli.verbosity.zero",
            &["-in", "-v:0"],
            "(check-sat)\n(exit)\n",
        ),
        cli_case(
            "cli.warning-disable",
            &["-in", "-nw"],
            "(check-sat)\n(exit)\n",
        ),
    ];
    for case in &mut cases {
        if case.id.starts_with("cli.stats.") {
            case.comparator = Comparator::Statistics;
        }
    }
    cases.push(CaseSpec {
        id: "cli.input.file-alias".to_string(),
        oracle_args: vec![format!("-file:{FILE_PLACEHOLDER}")],
        subject_args: vec!["--z3-mode".to_string(), format!("-file:{FILE_PLACEHOLDER}")],
        input: b"(check-sat)\n(exit)\n".to_vec(),
        comparator: Comparator::ExactBytes,
        style: RunStyle::File,
        file_extension: "smt2".to_string(),
        artifact_policy: ArtifactPolicy::None,
        source_owner: None,
        effect_requirement: EffectRequirement::Inherent,
        oracle_baseline: None,
    });
    cases.push(CaseSpec {
        id: "cli.input.positional-smt2".to_string(),
        oracle_args: vec![FILE_PLACEHOLDER.to_string()],
        subject_args: vec!["--z3-mode".to_string(), FILE_PLACEHOLDER.to_string()],
        input: b"(check-sat)\n(exit)\n".to_vec(),
        comparator: Comparator::ExactBytes,
        style: RunStyle::File,
        file_extension: "smt2".to_string(),
        artifact_policy: ArtifactPolicy::None,
        source_owner: None,
        effect_requirement: EffectRequirement::Inherent,
        oracle_baseline: None,
    });
    cases
}

fn combinator_cases() -> Vec<CaseSpec> {
    [
        ("and-then", "(and-then skip simplify)"),
        ("annotation", "(! simplify :som true)"),
        ("cond", "(cond (> size 0) simplify fail)"),
        ("fail-if", "(fail-if (= size 0))"),
        ("if", "(if (> size 0) simplify fail)"),
        ("or-else", "(or-else fail simplify)"),
        ("par-or", "(par-or fail simplify)"),
        ("par-then", "(par-then skip simplify)"),
        ("repeat", "(repeat simplify 2)"),
        ("then", "(then skip simplify)"),
        ("try-for", "(try-for simplify 1000)"),
        ("using-params", "(using-params simplify :som true)"),
        ("when", "(when (> size 0) simplify)"),
        ("with", "(with simplify :som true)"),
    ]
    .into_iter()
    .map(|(name, tactic)| {
        batch_case(
            format!("tactic.combinator.{name}"),
            &format!("(declare-const x Int)\n(assert (= (+ x 0) 1))\n(apply {tactic})\n(exit)\n"),
        )
    })
    .collect()
}

fn case_token(value: &str) -> String {
    value
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '-' {
                character
            } else {
                '_'
            }
        })
        .collect()
}

/// Hidden, validator-owned helper used to prove live `-in` flushing.  The
/// helper is itself the hash-bound parity executable and is run under the same
/// RSS watchdog as the target it spawns; the target inherits its process group.
pub(super) fn run_stream_driver(args: &[String]) -> Result<i32, String> {
    let mut target: Option<PathBuf> = None;
    let mut target_args = Vec::new();
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--target" => {
                index += 1;
                target = Some(PathBuf::from(
                    args.get(index).ok_or("--target needs a path")?,
                ));
            }
            "--target-arg" => {
                index += 1;
                target_args.push(args.get(index).ok_or("--target-arg needs a value")?.clone());
            }
            other => return Err(format!("unknown stream-driver flag {other:?}")),
        }
        index += 1;
    }
    let target = target.ok_or("stream driver requires --target")?;
    let mut child = Command::new(&target)
        .args(&target_args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("spawning stream target {}: {error}", target.display()))?;
    let mut stdin = child.stdin.take().ok_or("stream target has no stdin")?;
    let stdout = child.stdout.take().ok_or("stream target has no stdout")?;
    let stderr = child.stderr.take().ok_or("stream target has no stderr")?;
    let stdout_truncated = Arc::new(AtomicBool::new(false));
    let stdout_read_error = Arc::new(AtomicBool::new(false));
    let (sender, receiver) = mpsc::channel::<Vec<u8>>();
    let stdout_truncated_worker = Arc::clone(&stdout_truncated);
    let stdout_read_error_worker = Arc::clone(&stdout_read_error);
    let stdout_worker = thread::spawn(move || {
        let mut reader = BufReader::new(stdout);
        let mut retained = 0usize;
        loop {
            let mut line = Vec::new();
            match reader.read_until(b'\n', &mut line) {
                Ok(0) => break,
                Ok(_) => {
                    if retained.saturating_add(line.len()) > STREAM_LIMIT {
                        stdout_truncated_worker.store(true, Ordering::Release);
                        continue;
                    }
                    retained += line.len();
                    if sender.send(line).is_err() {
                        break;
                    }
                }
                Err(_) => {
                    stdout_read_error_worker.store(true, Ordering::Release);
                    break;
                }
            }
        }
    });
    let stderr_worker = thread::spawn(move || drain_bounded(stderr));
    let phases: [(&[u8], &[u8]); 3] = [
        (b"(echo \"phase-one\")\n", b"phase-one\n"),
        (b"(check-sat)\n", b"sat\n"),
        (b"(echo \"phase-two\")\n", b"phase-two\n"),
    ];
    let mut combined_stdout = Vec::new();
    let mut phase_complete = true;
    for (request, expected) in phases {
        if stdin
            .write_all(request)
            .and_then(|()| stdin.flush())
            .is_err()
        {
            phase_complete = false;
            break;
        }
        match receiver.recv_timeout(STREAM_PHASE_TIMEOUT) {
            Ok(line) => {
                phase_complete &= line == expected;
                combined_stdout.extend_from_slice(&line);
            }
            Err(_) => {
                phase_complete = false;
                break;
            }
        }
    }
    if phase_complete {
        phase_complete &= stdin
            .write_all(b"(exit)\n")
            .and_then(|()| stdin.flush())
            .is_ok();
    }
    drop(stdin);
    let (status, target_timed_out) = wait_stream_target(&mut child, STREAM_PHASE_TIMEOUT)?;
    stdout_worker
        .join()
        .map_err(|_| "stream stdout reader panicked".to_string())?;
    while let Ok(line) = receiver.try_recv() {
        if combined_stdout.len().saturating_add(line.len()) <= STREAM_LIMIT {
            combined_stdout.extend_from_slice(&line);
        } else {
            stdout_truncated.store(true, Ordering::Release);
        }
    }
    let (stderr, stderr_truncated, stderr_read_error) = stderr_worker
        .join()
        .map_err(|_| "stream stderr reader panicked".to_string())?;
    let report = StreamDriverReport {
        exit_code: status.and_then(|status| status.code()),
        stdout: String::from_utf8_lossy(&combined_stdout).into_owned(),
        stderr: String::from_utf8_lossy(&stderr).into_owned(),
        phase_complete,
        target_timed_out,
        stdout_truncated: stdout_truncated.load(Ordering::Acquire),
        stderr_truncated,
        read_error: stdout_read_error.load(Ordering::Acquire) || stderr_read_error,
    };
    println!(
        "{}",
        serde_json::to_string(&report)
            .map_err(|error| format!("serializing stream-driver report: {error}"))?
    );
    Ok(0)
}

fn wait_stream_target(
    child: &mut Child,
    timeout: Duration,
) -> Result<(Option<std::process::ExitStatus>, bool), String> {
    let deadline = Instant::now() + timeout;
    loop {
        match child
            .try_wait()
            .map_err(|error| format!("waiting for stream target: {error}"))?
        {
            Some(status) => return Ok((Some(status), false)),
            None if Instant::now() < deadline => thread::sleep(Duration::from_millis(10)),
            None => {
                child
                    .kill()
                    .map_err(|error| format!("killing stalled stream target: {error}"))?;
                let status = child
                    .wait()
                    .map_err(|error| format!("reaping stalled stream target: {error}"))?;
                return Ok((Some(status), true));
            }
        }
    }
}

fn drain_bounded(mut reader: impl std::io::Read) -> (Vec<u8>, bool, bool) {
    let mut retained = Vec::new();
    let mut truncated = false;
    let mut read_error = false;
    let mut chunk = [0u8; 8192];
    loop {
        match reader.read(&mut chunk) {
            Ok(0) => break,
            Ok(read) => {
                let remaining = STREAM_LIMIT.saturating_sub(retained.len());
                retained.extend_from_slice(&chunk[..read.min(remaining)]);
                truncated |= read > remaining;
            }
            Err(_) => {
                read_error = true;
                break;
            }
        }
    }
    (retained, truncated, read_error)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base_catalog_and_source_ownership_cardinalities_are_closed() {
        let base_count = standard_command_cases().len()
            + standard_command_arity_cases().len()
            + extension_command_cases().len()
            + extension_command_arity_cases().len()
            + state_and_diagnostic_cases().len()
            + cli_cases().len()
            + combinator_cases().len()
            + TACTIC_COUNT
            + PROBE_NAMES.len()
            + 1;
        assert_eq!(base_count, BASE_CASE_COUNT);
        assert_eq!(EXPECTED_SOURCE_OWNER_COUNT, 1_508);
        assert_eq!(EXPECTED_CASE_COUNT, 1_846);
        assert_eq!(EXPECTED_UNRESOLVED_COMMAND_OWNERS, 57);
        assert_eq!(EXPECTED_AUDITED_COMMAND_GAP_UNIVERSE_OWNERS, 63);
        assert_eq!(EXPECTED_UNRESOLVED_SOURCE_OWNERS, 301);
        assert_eq!(EXPECTED_AUDITED_GAP_UNIVERSE_OWNERS, 496);
        assert_eq!(RESOLVED_EXTENSION_COMMANDS.len(), 6);
        assert_eq!(RESOLVED_INFO_KEYS.len(), 11);
        assert_eq!(RESOLVED_OPTION_KEYS.len(), 16);
        assert_eq!(parser_tokens::semantic_owner_names().count(), 12);
        assert_eq!(declaration_builtins::semantic_owner_names().count(), 126);
        assert_eq!(RESOLVED_LOGIC_RECOGNIZER_LITERALS.len(), 24);
        assert_eq!(EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNERS, 0);
        assert_eq!(standard_command_cases().len(), SMTLIB_COMMANDS.len());
        assert_eq!(SUPPORTED_TACTIC_NAMES.len(), TACTIC_COUNT);
        assert_eq!(PROBE_NAMES.len(), 42);
    }

    #[test]
    fn unresolved_items_cannot_become_behavioral_passes_by_construction() {
        let item = z3_source_inventory::ObservableItem {
            category: "module-parameter".to_string(),
            name: "ay.no_safe_witness".to_string(),
            detail: "no_safe_witness (symbol)".to_string(),
        };
        let case = attach_owner(source_parameter_case(&item), &item);
        assert_eq!(case.effect_requirement, EffectRequirement::Unresolved);
        assert!(case.oracle_baseline.is_none());
        assert_eq!(case.oracle_args, ["-in"]);
        assert_eq!(case.input, b"(exit)\n");
        assert_eq!(case.source_owner.as_ref().unwrap().name, item.name);
    }

    #[test]
    fn known_partial_commands_override_stale_happy_path_witnesses() {
        for &(category, name) in &EXPECTED_UNRESOLVED_COMMAND_OWNER_KEYS {
            assert_eq!(category, "smt-command");
            let case = source_command_case(name);
            assert_eq!(
                case.effect_requirement,
                EffectRequirement::Unresolved,
                "{name}"
            );
            assert!(case.oracle_baseline.is_none(), "{name}");
        }
    }

    #[test]
    fn supported_z3_extension_commands_have_distinguishing_source_witnesses() {
        for name in [
            "assert-not",
            "dbg-params",
            "help",
            "help-simplifier",
            "help-tactic",
        ] {
            let witness = standard_source_command_witness(name)
                .unwrap_or_else(|| panic!("missing source witness for {name}"));
            assert_ne!(witness.candidate, witness.baseline, "{name}");
            assert!(witness.candidate.contains(&format!("({name}")), "{name}");

            let case = source_command_case(name);
            assert_eq!(
                case.effect_requirement,
                EffectRequirement::OracleDiffersFromBaseline,
                "{name}"
            );
            let baseline = case
                .oracle_baseline
                .as_ref()
                .unwrap_or_else(|| panic!("missing oracle baseline for {name}"));
            assert_eq!(case.input, witness.candidate.as_bytes(), "{name}");
            assert_eq!(baseline.input, witness.baseline.as_bytes(), "{name}");
            assert_eq!(baseline.args, ["-in"], "{name}");
            assert_eq!(baseline.style, RunStyle::Batch, "{name}");
        }
    }

    #[test]
    fn pinned_z3_5_help_fixtures_have_exact_hashes() {
        assert_eq!(
            sha256_bytes(include_bytes!(
                "../../../ay-frontend/src/command/z3_5_help.txt"
            )),
            Z3_5_HELP_FIXTURE_SHA256
        );
        assert_eq!(
            sha256_bytes(include_bytes!(
                "../../../ay-frontend/src/command/z3_5_help_simplifier.txt"
            )),
            Z3_5_HELP_SIMPLIFIER_FIXTURE_SHA256
        );
        assert_eq!(
            sha256_bytes(include_bytes!(
                "../../../ay-frontend/src/command/z3_5_help_tactic.txt"
            )),
            Z3_5_HELP_TACTIC_FIXTURE_SHA256
        );
    }

    #[test]
    fn fixedpoint_commands_have_file_backed_distinguishing_source_witnesses() {
        for name in ["declare-rel", "declare-var", "query", "rule"] {
            let case = source_fixedpoint_command_case(name)
                .unwrap_or_else(|| panic!("missing fixedpoint source witness for {name}"));
            assert_eq!(case.style, RunStyle::File, "{name}");
            assert_eq!(case.oracle_args, [FILE_PLACEHOLDER], "{name}");
            assert_eq!(case.subject_args, ["--z3-mode", FILE_PLACEHOLDER], "{name}");
            assert_eq!(
                case.effect_requirement,
                EffectRequirement::OracleDiffersFromBaseline,
                "{name}"
            );
            assert!(
                String::from_utf8_lossy(&case.input).contains(&format!("({name}")),
                "{name}"
            );
            let baseline = case
                .oracle_baseline
                .as_ref()
                .unwrap_or_else(|| panic!("missing fixedpoint baseline for {name}"));
            assert_eq!(baseline.args, [FILE_PLACEHOLDER], "{name}");
            assert_eq!(baseline.style, RunStyle::File, "{name}");
            assert_ne!(case.input, baseline.input, "{name}");
        }
        assert!(source_fixedpoint_command_case("assert").is_none());
    }

    #[test]
    fn fixedpoint_extension_cases_use_z3_5_file_syntax() {
        let cases = extension_command_cases();
        for name in ["declare-rel", "declare-var", "query", "rule"] {
            let id = format!("command.z3-extension.{name}");
            let case = cases
                .iter()
                .find(|case| case.id == id)
                .unwrap_or_else(|| panic!("missing extension case for {name}"));
            assert_eq!(case.style, RunStyle::File, "{name}");
            assert_eq!(case.oracle_args, [FILE_PLACEHOLDER], "{name}");
            assert_eq!(case.subject_args, ["--z3-mode", FILE_PLACEHOLDER], "{name}");
            assert!(
                !String::from_utf8_lossy(&case.input).contains("(query ("),
                "Z3 5.0.0 query expects a registered predicate name: {name}"
            );
        }
    }

    #[test]
    fn every_z3_logic_recognizer_literal_has_a_distinguishing_witness() {
        for name in RESOLVED_LOGIC_RECOGNIZER_LITERALS {
            let case = source_logic_recognizer_case(name);
            assert_eq!(
                case.input,
                format!("(set-logic {name})\n(exit)\n").as_bytes()
            );
            assert_eq!(
                case.effect_requirement,
                EffectRequirement::OracleDiffersFromBaseline
            );
            let baseline = case.oracle_baseline.as_ref().unwrap();
            assert_eq!(baseline.args, ["-in"]);
            assert_eq!(baseline.input, b"(set-logic ZZ_NO_SUCH_LOGIC)\n(exit)\n");
        }
    }

    #[test]
    fn every_closed_declaration_builtin_has_a_semantic_source_witness() {
        for name in declaration_builtins::semantic_owner_names() {
            let predicate = declaration_builtins::semantic_predicate(name).unwrap();
            let case = source_declaration_builtin_case(name);
            let logic_prefix = if declaration_builtins::semantic_requires_no_logic(name) {
                ""
            } else {
                "(set-logic ALL)\n"
            };
            let prelude = declaration_builtins::semantic_prelude(name);
            assert_eq!(
                case.input,
                format!("{prelude}{logic_prefix}(assert (not {predicate}))\n(check-sat)\n(exit)\n")
                    .as_bytes()
            );
            assert_eq!(
                case.effect_requirement,
                EffectRequirement::OracleDiffersFromBaseline
            );
            let baseline = case.oracle_baseline.as_ref().unwrap();
            assert_eq!(baseline.args, ["-in"]);
            assert_eq!(
                baseline.input,
                format!("{prelude}{logic_prefix}(check-sat)\n(exit)\n").as_bytes()
            );
        }
    }

    #[test]
    fn every_closed_structural_parser_token_has_a_semantic_source_witness() {
        for name in parser_tokens::semantic_owner_names() {
            let witness = parser_tokens::semantic_witness(name).unwrap();
            let case = source_parser_token_case(name);
            assert_eq!(case.input, witness.candidate.as_bytes(), "{name}");
            assert_eq!(
                case.effect_requirement,
                EffectRequirement::OracleDiffersFromBaseline,
                "{name}"
            );
            let baseline = case.oracle_baseline.as_ref().unwrap();
            assert_eq!(baseline.args, ["-in"], "{name}");
            assert_eq!(baseline.input, witness.baseline.as_bytes(), "{name}");
        }
        for partial_or_absent in [
            "!", ":lblneg", ":lblpos", ":named", ":pattern", ":subterm", "as", "choice", "lambda",
            "root-obj",
        ] {
            assert_eq!(
                source_parser_token_case(partial_or_absent).effect_requirement,
                EffectRequirement::Unresolved,
                "{partial_or_absent}"
            );
        }
    }

    #[test]
    fn exact_z3_info_key_cohort_has_distinguishing_witnesses() {
        for name in RESOLVED_INFO_KEYS {
            let case = source_info_key_case(name)
                .unwrap_or_else(|| panic!("missing info-key source witness for {name}"));
            assert_eq!(
                case.effect_requirement,
                EffectRequirement::OracleDiffersFromBaseline,
                "{name}"
            );
            assert!(
                String::from_utf8_lossy(&case.input).contains(name),
                "{name}"
            );
            let baseline = case
                .oracle_baseline
                .as_ref()
                .unwrap_or_else(|| panic!("missing oracle baseline for {name}"));
            assert_eq!(baseline.args, ["-in"], "{name}");
            assert_eq!(baseline.style, RunStyle::Batch, "{name}");
            assert_eq!(
                baseline.input, b"(get-info :ay-no-such-info)\n(exit)\n",
                "{name}"
            );
            assert_ne!(case.input, baseline.input, "{name}");
        }
    }

    #[test]
    fn exact_z3_option_key_cohort_has_effectful_round_trip_witnesses() {
        for name in RESOLVED_OPTION_KEYS {
            let case = source_option_key_case(name)
                .unwrap_or_else(|| panic!("missing option-key source witness for {name}"));
            assert_eq!(
                case.effect_requirement,
                EffectRequirement::OracleDiffersFromBaseline,
                "{name}"
            );
            let candidate = String::from_utf8_lossy(&case.input);
            assert!(
                candidate.contains(&format!("(set-option {name} ")),
                "{name}"
            );
            if !matches!(name, ":print-warning" | ":numeral-as-real") {
                assert!(
                    candidate.contains(&format!("(get-option {name})")),
                    "{name}"
                );
            }
            let baseline = case
                .oracle_baseline
                .as_ref()
                .unwrap_or_else(|| panic!("missing oracle baseline for {name}"));
            assert_eq!(baseline.args, ["-in"], "{name}");
            assert_eq!(baseline.style, RunStyle::Batch, "{name}");
            let expected_baseline = match name {
                ":print-warning" => {
                    b"(assert (! true :ay-parity-unknown-attribute true))\n(check-sat)\n(exit)\n"
                        .as_slice()
                }
                ":numeral-as-real" => b"(set-option :int-real-coercions false)\n(assert (= 0 0.0))\n(check-sat)\n(exit)\n".as_slice(),
                ":error-behavior" => b"(get-option :error-behavior)\n(exit)\n".as_slice(),
                ":int-real-coercions" => {
                    b"(get-option :int-real-coercions)\n(exit)\n".as_slice()
                }
                _ => b"(get-option :ay-no-such-option)\n(exit)\n".as_slice(),
            };
            assert_eq!(baseline.input, expected_baseline, "{name}");
            assert_ne!(case.input, baseline.input, "{name}");
        }
        for partial in [
            ":diagnostic-output-channel",
            ":expand-definitions",
            ":regular-output-channel",
            ":reproducible-resource-limit",
        ] {
            assert!(source_option_key_case(partial).is_none(), "{partial}");
        }
    }

    #[test]
    fn formerly_claimed_no_effect_parameters_require_observable_oracle_effects() {
        for (name, detail) in [
            (
                "nlsat.known_sat_assignment_file_name",
                "known_sat_assignment_file_name (string) (default: )",
            ),
            (
                "opt.dump_benchmarks",
                "dump_benchmarks (bool) (default: false)",
            ),
            ("solver.smtlib2_log", "smtlib2_log (symbol)"),
        ] {
            let item = z3_source_inventory::ObservableItem {
                category: "module-parameter".to_string(),
                name: name.to_string(),
                detail: detail.to_string(),
            };
            let case = attach_owner(source_parameter_case(&item), &item);
            assert_eq!(
                case.effect_requirement,
                EffectRequirement::OracleDiffersFromBaseline
            );
            assert!(case.oracle_baseline.is_some());
            assert_eq!(case.source_effect_reason(), "none");
        }
    }

    #[test]
    fn safe_typed_and_named_parameter_alternates_require_real_effects() {
        for (name, detail, expected_argument) in [
            ("proof", "proof (bool) (default: false)", "proof=true"),
            (
                "timeout",
                "timeout (unsigned int) (default: 4294967295)",
                "timeout=0",
            ),
            (
                "sat.phase",
                "phase (symbol) (default: caching)",
                "sat.phase=always_false",
            ),
        ] {
            let item = z3_source_inventory::ObservableItem {
                category: if name.contains('.') {
                    "module-parameter".to_string()
                } else {
                    "global-parameter".to_string()
                },
                name: name.to_string(),
                detail: detail.to_string(),
            };
            let case = source_parameter_case(&item);
            assert_eq!(
                case.effect_requirement,
                EffectRequirement::OracleDiffersFromBaseline
            );
            assert_eq!(case.oracle_args[0], expected_argument);
            assert!(case.oracle_baseline.is_some());
        }
    }

    #[test]
    fn artifact_parameters_use_sandboxed_effect_witnesses() {
        for (name, detail) in [
            ("trace", "trace (bool) (default: false)"),
            (
                "solver.axioms2files",
                "axioms2files (bool) (default: false)",
            ),
            ("sat.drat.file", "drat.file (symbol)"),
        ] {
            let item = z3_source_inventory::ObservableItem {
                category: if name.contains('.') {
                    "module-parameter".to_string()
                } else {
                    "global-parameter".to_string()
                },
                name: name.to_string(),
                detail: detail.to_string(),
            };
            let case = source_parameter_case(&item);
            assert_eq!(
                case.effect_requirement,
                EffectRequirement::OracleDiffersFromBaseline
            );
            assert_eq!(case.artifact_policy, ArtifactPolicy::IsolatedDirectory);
            assert!(case.oracle_baseline.is_some());
        }
    }

    #[test]
    fn exact_audited_command_gap_universe_digest_is_recomputed_from_canonical_rows() {
        let mut owners = EXPECTED_UNRESOLVED_COMMAND_OWNER_KEYS
            .iter()
            .map(|(category, name)| SourceOwner {
                category: (*category).to_string(),
                name: (*name).to_string(),
            })
            .collect::<Vec<_>>();
        owners.extend(RESOLVED_EXTENSION_COMMANDS.iter().map(|name| SourceOwner {
            category: "smt-command".to_string(),
            name: (*name).to_string(),
        }));
        owners.sort();
        let digest = sha256_bytes(
            owners
                .iter()
                .map(SourceOwner::canonical_line)
                .collect::<Vec<_>>()
                .concat()
                .as_bytes(),
        );
        assert_eq!(owners.len(), EXPECTED_AUDITED_COMMAND_GAP_UNIVERSE_OWNERS);
        assert_eq!(
            digest,
            EXPECTED_AUDITED_COMMAND_GAP_UNIVERSE_OWNERSHIP_SHA256
        );
    }

    #[test]
    fn exact_source_proven_no_effect_digest_is_recomputed_from_canonical_rows() {
        let mut owners = EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNER_KEYS
            .iter()
            .map(|(category, name)| SourceOwner {
                category: (*category).to_string(),
                name: (*name).to_string(),
            })
            .collect::<Vec<_>>();
        owners.sort();
        let digest = sha256_bytes(
            owners
                .iter()
                .map(SourceOwner::canonical_line)
                .collect::<Vec<_>>()
                .concat()
                .as_bytes(),
        );
        assert_eq!(owners.len(), EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNERS);
        assert_eq!(digest, EXPECTED_SOURCE_PROVEN_NO_EFFECT_OWNERSHIP_SHA256);
    }

    #[test]
    fn source_owner_digest_helpers_recompute_canonical_rows() {
        let mut first = batch_case("first", "(exit)\n");
        first.source_owner = Some(SourceOwner {
            category: "tactic".to_string(),
            name: "simplify".to_string(),
        });
        let mut second = unresolved_case(batch_case("second", "(exit)\n"));
        second.source_owner = Some(SourceOwner {
            category: "module-parameter".to_string(),
            name: "solver.smtlib2_log".to_string(),
        });
        let expected_all =
            sha256_bytes(b"module-parameter\tsolver.smtlib2_log\ntactic\tsimplify\n");
        let expected_unresolved = sha256_bytes(b"module-parameter\tsolver.smtlib2_log\n");
        assert_eq!(
            ownership_sha256(&[first.clone(), second.clone()]),
            expected_all
        );
        assert_eq!(
            unresolved_ownership_sha256(&[first, second]),
            expected_unresolved
        );
    }

    #[test]
    fn audited_gap_universe_digest_includes_resolved_logic_owners() {
        let mut unresolved = unresolved_case(batch_case("unresolved", "(exit)\n"));
        unresolved.source_owner = Some(SourceOwner {
            category: "declaration-builtin".to_string(),
            name: "owner".to_string(),
        });
        let mut resolved_logic = source_logic_recognizer_case("ALL");
        resolved_logic.source_owner = Some(SourceOwner {
            category: "logic-recognizer-literal".to_string(),
            name: "ALL".to_string(),
        });
        let expected = sha256_bytes(b"declaration-builtin\towner\nlogic-recognizer-literal\tALL\n");
        assert_eq!(
            audited_gap_universe_ownership_sha256(&[unresolved, resolved_logic]),
            expected
        );
    }

    #[test]
    fn statistics_comparator_elides_only_numeric_values() {
        let left = "sat\n(:memory 1.25\n :other 7)\n";
        let right = "sat\n(:memory 9.00\n :other 42)\n";
        assert_eq!(
            canonicalize_statistics(left),
            canonicalize_statistics(right)
        );
        assert_ne!(
            canonicalize_statistics(left),
            canonicalize_statistics("sat\n(:different 1.25\n :other 7)\n")
        );
        assert_ne!(
            canonicalize_statistics(left),
            canonicalize_statistics("sat\n(error \"diagnostic\")\n(:memory 1.25\n :other 7)\n")
        );
    }

    #[test]
    fn component_trace_comparator_keeps_structure_and_elides_telemetry() {
        let left = "(bit-blast :num-exprs 4 :time 0.01 :memory 17.30)\nsat\n";
        let right = "(bit-blast :num-exprs 99 :time 2.75 :memory 18.41)\nsat\n";
        assert_eq!(
            canonicalize_component_trace(left),
            canonicalize_component_trace(right)
        );
        assert_ne!(
            canonicalize_component_trace(left),
            canonicalize_component_trace(
                "(solve-eqs :num-exprs 4 :time 0.01 :memory 17.30)\nsat\n"
            )
        );
    }
}
