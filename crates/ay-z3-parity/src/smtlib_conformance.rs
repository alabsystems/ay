// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed SMT-LIB conformance accounting for the AY/Z3 replacement claim.
//!
//! This module deliberately separates three things that are easy to conflate:
//!
//! * the normative SMT-LIB 2.7 language and registry,
//! * Z3 5.1.0's extensions and observable behavior, and
//! * evidence that this exact AY build implements either surface.
//!
//! A passing corpus is evidence for rows in a contract; it is never allowed to
//! define the contract. `check --require-complete` therefore succeeds only
//! when every required dimension has a closed source inventory and every row
//! is backed by exhaustive, hash-bound validator receipts with no skipped,
//! unknown, unavailable, timed-out, crashed, or failed cases.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{Read as _, Write as _};
use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use ay_bench::{
    effective_execution_envelope, GuardedTranscriptOutput, PlannedResources,
    ENFORCEMENT_RSS_WATCHDOG_V1,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

mod gate_integrity;
mod language_semantics;
mod lexical_grammar;
mod logic_registry;
mod official_corpus;
mod reference_inventory;
mod sat_models;
mod standard_commands;
mod theory_registry;
mod unknown_policy;
mod unsat_proofs;
mod z3_behavioral;
mod z3_source_inventory;

const MANIFEST_SCHEMA: &str = "ay-smtlib-conformance-contract/v1";
const VALIDATOR_RECEIPT_SCHEMA: &str = "ay-smtlib-validator-receipt/v2";
const CHECK_RECEIPT_SCHEMA: &str = "ay-smtlib-conformance-check-receipt/v1";
const PROFILE_ID: &str = "smtlib-2.7+z3-5.1.0";
const MAX_MANIFEST_BYTES: u64 = 16 * 1024 * 1024;
const MAX_VALIDATOR_RECEIPT_BYTES: u64 = 4 * 1024 * 1024;
const MAX_DIMENSIONS: usize = 64;
const MAX_REQUIREMENTS: usize = 100_000;
const MAX_EVIDENCE_PER_ROW: usize = 64;
const MAX_REFERENCE_INPUTS: usize = 64;
const MAX_AUXILIARY_TOOLS: usize = 16;
const UNASSIGNED_CAMPAIGN: &str = "unassigned";

const SMTLIB_COMMANDS: [&str; 32] = [
    "assert",
    "check-sat",
    "check-sat-assuming",
    "declare-const",
    "declare-datatype",
    "declare-datatypes",
    "declare-fun",
    "declare-sort",
    "declare-sort-parameter",
    "define-const",
    "define-fun",
    "define-fun-rec",
    "define-funs-rec",
    "define-sort",
    "echo",
    "exit",
    "get-assertions",
    "get-assignment",
    "get-info",
    "get-model",
    "get-option",
    "get-proof",
    "get-unsat-assumptions",
    "get-unsat-core",
    "get-value",
    "pop",
    "push",
    "reset",
    "reset-assertions",
    "set-info",
    "set-logic",
    "set-option",
];

const SMTLIB_THEORIES: [(&str, &str); 9] = [
    ("ArraysEx", "Theories/ArraysEx.smt2"),
    ("Core", "Theories/Core.smt2"),
    ("FixedSizeBitVectors", "Theories/FixedSizeBitVectors.smt2"),
    ("FloatingPoint", "Theories/FloatingPoint.smt2"),
    ("HO-Core", "Theories/HO-Core.smt2"),
    ("Ints", "Theories/Ints.smt2"),
    ("Reals", "Theories/Reals.smt2"),
    ("Reals_Ints", "Theories/Reals_Ints.smt2"),
    ("Strings", "Theories/UnicodeStrings.smt2"),
];

const SMTLIB_LOGICS: [&str; 25] = [
    "AUFLIA",
    "AUFLIRA",
    "AUFNIRA",
    "LIA",
    "LRA",
    "QF_ABV",
    "QF_AUFBV",
    "QF_AUFLIA",
    "QF_AX",
    "QF_BV",
    "QF_EIA",
    "QF_IDL",
    "QF_LIA",
    "QF_LRA",
    "QF_NIA",
    "QF_NRA",
    "QF_RDL",
    "QF_UF",
    "QF_UFBV",
    "QF_UFIDL",
    "QF_UFLIA",
    "QF_UFLRA",
    "QF_UFNRA",
    "UFLRA",
    "UFNIA",
];

#[derive(Clone, Copy)]
struct DimensionSpec {
    id: &'static str,
    title: &'static str,
    definition: &'static str,
    validator_kind: ValidatorKind,
}

const DIMENSIONS: [DimensionSpec; 12] = [
    DimensionSpec {
        id: "language.lexical-and-grammar",
        title: "Lexical, S-expression, term, and response grammar",
        definition: "Every normative lexical class and grammar production has positive and negative witnesses, deterministic recovery behavior, and source-position checks.",
        validator_kind: ValidatorKind::TranscriptConformance,
    },
    DimensionSpec {
        id: "language.commands",
        title: "Standard command grammar",
        definition: "Every one of the 32 SMT-LIB 2.7 command alternatives is inventoried and tested for accepted and rejected forms.",
        validator_kind: ValidatorKind::TranscriptConformance,
    },
    DimensionSpec {
        id: "registry.theories",
        title: "Official theory signatures",
        definition: "Every sort and function signature in the nine non-draft official SMT-LIB 2.7 theory declarations is inventoried by full indexed and polymorphic signature.",
        validator_kind: ValidatorKind::TranscriptConformance,
    },
    DimensionSpec {
        id: "registry.logics",
        title: "Official logic definitions",
        definition: "Every official SMT-LIB 2.7 logic declaration, including its prose restrictions, has positive and negative conformance evidence.",
        validator_kind: ValidatorKind::TranscriptConformance,
    },
    DimensionSpec {
        id: "semantics.typing-and-scope",
        title: "Typing and scope",
        definition: "Sort checking, arity, overload resolution, binders, declarations, shadowing, redeclaration, and scope lifetime are covered exhaustively.",
        validator_kind: ValidatorKind::TypeScopeConformance,
    },
    DimensionSpec {
        id: "semantics.command-state-machine",
        title: "Command state machine",
        definition: "Command preconditions, state transitions, stack effects, output channels, poisoning, and artifact invalidation form a closed transition inventory.",
        validator_kind: ValidatorKind::StateMachineConformance,
    },
    DimensionSpec {
        id: "results.sat-models",
        title: "SAT model validity",
        definition: "Every public sat result is query-epoch-bound and every authored assertion and assumption is independently validated with no delegated or unconfirmed cases.",
        validator_kind: ValidatorKind::IndependentModelChecker,
    },
    DimensionSpec {
        id: "results.unsat-proofs",
        title: "UNSAT proof validity",
        definition: "Every public unsat result has a strict, hole-free proof over the exact authored problem and assumptions and is replayed by an independent pinned checker.",
        validator_kind: ValidatorKind::IndependentProofChecker,
    },
    DimensionSpec {
        id: "results.unknown-policy",
        title: "Unknown and artifact policy",
        definition: "Every closed unknown reason is inducible and invalidates authoritative model, proof, core, optimum, and stale query artifacts.",
        validator_kind: ValidatorKind::UnknownPolicy,
    },
    DimensionSpec {
        id: "overlay.z3-5.1.0",
        title: "Exact Z3 5.1.0 overlay",
        definition: "All Z3 5.1.0 commands, aliases, extensions, diagnostics, options, tactics, probes, and transcript quirks are source-inventoried and differentially validated.",
        validator_kind: ValidatorKind::Z3Differential,
    },
    DimensionSpec {
        id: "coverage.corpus",
        title: "Closed conformance corpus",
        definition: "An immutable per-file and per-query corpus manifest has zero missing or unexpected cases, zero wrong or invalid results, and zero Z3-decided AY-missing cases under one enforced envelope.",
        validator_kind: ValidatorKind::OfficialCorpus,
    },
    DimensionSpec {
        id: "gate.integrity",
        title: "Gate integrity and negative controls",
        definition: "The gate rejects removed, duplicated, invented, stale, foreign, truncated, skipped, unavailable, timed-out, hash-drifted, and checker-spoofed evidence.",
        validator_kind: ValidatorKind::GateNegativeControl,
    },
];

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Contract {
    schema: String,
    profile: Profile,
    campaign_id: String,
    resource_envelope: Option<String>,
    subject: Subject,
    dimensions: Vec<Dimension>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Profile {
    id: String,
    standard: StandardTarget,
    z3_overlay: Z3Target,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct StandardTarget {
    name: String,
    version: String,
    release: String,
    language_sources: SourcePin,
    normative_pdf: SourcePin,
    registry: SourcePin,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct SourcePin {
    repository: String,
    revision: String,
    selection: String,
    item_count: usize,
    digest_kind: String,
    sha256: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Z3Target {
    product: String,
    version: String,
    source_repository: String,
    source_tag: String,
    source_commit: String,
    tracked_source_file_count: usize,
    tracked_source_tree_digest_kind: String,
    tracked_source_tree_sha256: String,
    reference_executable: ReferenceExecutable,
    reference_shared_library: ReferenceSharedLibrary,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ReferenceExecutable {
    path: String,
    architecture: String,
    version_output: String,
    sha256: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ReferenceSharedLibrary {
    path: String,
    full_version: String,
    sha256: String,
}

#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Subject {
    ay_executable: Option<Artifact>,
    ay_shared_library: Option<Artifact>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Artifact {
    path: String,
    sha256: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Dimension {
    id: String,
    title: String,
    definition: String,
    inventory: Inventory,
    requirements: Vec<Requirement>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Inventory {
    granularity: InventoryGranularity,
    item_count: usize,
    sha256: String,
    evidence: Vec<EvidenceRef>,
    gap: Option<String>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum InventoryGranularity {
    Unresolved,
    ItemLevel,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Requirement {
    id: String,
    source: SourceLocator,
    classification: Classification,
    claim: String,
    expectation: Expectation,
    evidence: Vec<EvidenceRef>,
    gap: Option<String>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct SourceLocator {
    cohort: SourceCohort,
    locator: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum SourceCohort {
    SmtlibLanguage,
    SmtlibRegistry,
    Z3Source,
    AySource,
    OfficialCorpus,
    Contract,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum Classification {
    Standard,
    ExactOverlay,
    AdjudicatedDeviation,
    Gate,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Expectation {
    parse: Option<String>,
    typing: Option<String>,
    state: Option<String>,
    result: Option<String>,
    semantic: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct EvidenceRef {
    path: String,
    sha256: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ValidatorReceipt {
    schema: String,
    campaign_id: String,
    profile_id: String,
    profile_sha256: String,
    dimension_id: String,
    requirement_ids: Vec<String>,
    inventory_sha256: String,
    validator: ValidatorIdentity,
    subject: ReceiptSubject,
    z3_binary_sha256: Option<String>,
    z3_shared_library_sha256: Option<String>,
    reference_inputs: Vec<ReferenceInput>,
    auxiliary_tools: Vec<AuxiliaryTool>,
    source_provenance: Option<SourceProvenance>,
    resource_envelope: Option<String>,
    exhaustive: bool,
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

/// An immutable, content-addressed source input used by a registered
/// extractor or semantic validator.
///
/// `selection_sha256` is the source-profile digest (for example the sorted
/// path/git-blob/size manifest); `snapshot` is the actual replayable bundle
/// retained beside the receipt.  Keeping both prevents a receipt from naming
/// an authentic revision while feeding the validator different bytes.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ReferenceInput {
    id: String,
    cohort: SourceCohort,
    repository: String,
    revision: String,
    selection: String,
    item_count: usize,
    digest_kind: String,
    selection_sha256: String,
    snapshot: Artifact,
}

/// An independently authenticated checker or other auxiliary executable.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct AuxiliaryTool {
    id: String,
    role: String,
    artifact: Artifact,
    version_output: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ValidatorIdentity {
    id: String,
    kind: ValidatorKind,
    path: String,
    sha256: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum ValidatorKind {
    ReferenceExtractor,
    TranscriptConformance,
    TypeScopeConformance,
    StateMachineConformance,
    IndependentModelChecker,
    IndependentProofChecker,
    UnknownPolicy,
    Z3Differential,
    OfficialCorpus,
    GateNegativeControl,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ReceiptSubject {
    ay_executable_sha256: Option<String>,
    ay_shared_library_sha256: Option<String>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct SourceProvenance {
    source_commit: String,
    origin_main_commit: String,
    source_clean: bool,
    ay_shared_library_build_stamp: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum ValidatorResult {
    Pass,
    Fail,
    Skipped,
    Unavailable,
    Timeout,
    Memout,
    Crash,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ValidatorCase {
    id: String,
    input_sha256: String,
    expected: String,
    observed: String,
    stdout: Option<String>,
    stderr: Option<String>,
    exit_code: Option<i32>,
    process: Option<ProcessObservation>,
    outcome: ValidatorCaseOutcome,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct ProcessObservation {
    stdin_complete: bool,
    timed_out: bool,
    memout: bool,
    stdout_truncated: bool,
    stderr_truncated: bool,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum ValidatorCaseOutcome {
    Pass,
    Fail,
    Skipped,
    Unknown,
    Timeout,
    Memout,
    Crash,
    Unavailable,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct CaseCounts {
    total: usize,
    passed: usize,
    failed: usize,
    skipped: usize,
    unknown: usize,
    timed_out: usize,
    memout: usize,
    crashed: usize,
    unavailable: usize,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct CheckReceipt {
    schema: String,
    created_unix_ms: u128,
    manifest_sha256: String,
    profile_id: String,
    mode: CheckMode,
    report: AuditReport,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum CheckMode {
    Integrity,
    RequireComplete,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct AuditReport {
    complete: bool,
    summary: AuditSummary,
    dimensions: Vec<DimensionReport>,
    blockers: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct AuditSummary {
    dimension_count: usize,
    requirement_count: usize,
    reference_complete_dimensions: usize,
    reference_incomplete_dimensions: usize,
    validated_requirements: usize,
    gap_requirements: usize,
    skipped_or_failed_evidence: usize,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct DimensionReport {
    id: String,
    reference_complete: bool,
    requirement_count: usize,
    validated_requirements: usize,
    gap_requirements: usize,
}

#[derive(Default)]
struct ReceiptCache {
    values: BTreeMap<String, (String, ValidatorReceipt)>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ValidationMode {
    Structural,
    Audit,
    Completion,
}

impl ValidationMode {
    fn replays_registered_validators(self) -> bool {
        self != Self::Structural
    }

    fn verifies_pinned_runtime(self) -> bool {
        self == Self::Completion
    }
}

fn canonical_profile() -> Profile {
    Profile {
        id: PROFILE_ID.to_string(),
        standard: StandardTarget {
            name: "SMT-LIB".to_string(),
            version: "2.7".to_string(),
            release: "2026-03-27".to_string(),
            language_sources: SourcePin {
                repository: "https://github.com/SMT-LIB/SMT-LIB-2.git".to_string(),
                revision: "69f45ad60439cb4833ec031561517b6897d7d385".to_string(),
                selection: "17 Reference/*.{tex,bib} files; excludes stale root PDF and histories"
                    .to_string(),
                item_count: 17,
                digest_kind: "sorted-path-git-blob-size-manifest/v1".to_string(),
                sha256: "09a6782d30308648e49a9cb241866bbd18ecf7d043174d45e3b88d118b5dad20"
                    .to_string(),
            },
            normative_pdf: SourcePin {
                repository: "https://github.com/SMT-LIB/SMT-LIB.github.io.git".to_string(),
                revision: "b7f16149e83606f1569d2a8943b07caa3dc0ccd2".to_string(),
                selection:
                    "papers/smt-lib-reference-v2.7-r2026-03-27.pdf (published normative PDF)"
                        .to_string(),
                item_count: 1,
                digest_kind: "raw-file/v1".to_string(),
                sha256: "1099577ac197bb22ed35be4711b00e8ef8a4031aa3a0771baacc091b5a713b2c"
                    .to_string(),
            },
            registry: SourcePin {
                repository: "https://github.com/SMT-LIB/SMT-LIB.github.io.git".to_string(),
                revision: "47f7ee09ea05de990277781bbb2091245ea4a3f1".to_string(),
                selection: "all 25 Logics/*.smt2 plus nine named non-draft Theories/*.smt2 files"
                    .to_string(),
                item_count: 34,
                digest_kind: "sorted-path-git-blob-size-manifest/v1".to_string(),
                sha256: "506519771cabc1ff0de8b1d6d482659c3fab4432a8c0304a1f50367cd516da04"
                    .to_string(),
            },
        },
        z3_overlay: Z3Target {
            product: "Z3".to_string(),
            version: "5.1.0".to_string(),
            source_repository: "https://github.com/Z3Prover/z3.git".to_string(),
            source_tag: "z3-5.1.0".to_string(),
            source_commit: "0b6cdcdbc65da25ef0f73ac9da210574d0f66cf8".to_string(),
            tracked_source_file_count: 2_756,
            tracked_source_tree_digest_kind: "sorted-path-git-blob-size-manifest/v1".to_string(),
            tracked_source_tree_sha256:
                "df491d15649b581936f8422fbd704b0694831c160c01d1d339164c8a1441939b".to_string(),
            reference_executable: ReferenceExecutable {
                // NOTE: this public path is writable by anything on the machine,
                // and on 2026-07-20 it WAS overwritten -- a hand-built Z3 5.0.0
                // was copied over it, making the reference oracle's identity
                // depend on whoever wrote last. The SHA-256 below is the only
                // thing that catches that, so it is load-bearing rather than
                // decorative: `stage_authenticated_executable` re-hashes this
                // file and fails closed on any mismatch.
                //
                // A brew upgrade restoring the Cellar symlink would point this at
                // 4.16.0 -- a DIFFERENT solver behind an unchanged filename --
                // and the hash check is what turns that into a failure instead of
                // a silently wrong differential.
                path: "/opt/homebrew/bin/z3".to_string(),
                architecture: "aarch64".to_string(),
                version_output: "Z3 version 5.1.0 - 64 bit".to_string(),
                sha256: "8b61a8bc0b7a4e14dfb119910502ef808b055df636b25c8b67b96ae630fbc29c"
                    .to_string(),
            },
            reference_shared_library: ReferenceSharedLibrary {
                path: "/opt/homebrew/opt/z3/lib/libz3.dylib".to_string(),
                full_version: "5.1.0.0".to_string(),
                sha256: "45344d6a38b6f75304433c2458d6fa16bc4907d426c96e2bedf0a90603460422"
                    .to_string(),
            },
        },
    }
}

fn canonical_profile_sha256() -> Result<String, String> {
    let bytes = serde_json::to_vec(&canonical_profile())
        .map_err(|error| format!("serializing canonical profile: {error}"))?;
    Ok(sha256_bytes(&bytes))
}

fn expectation(
    parse: Option<&str>,
    typing: Option<&str>,
    state: Option<&str>,
    result: Option<&str>,
    semantic: &str,
) -> Expectation {
    Expectation {
        parse: parse.map(str::to_string),
        typing: typing.map(str::to_string),
        state: state.map(str::to_string),
        result: result.map(str::to_string),
        semantic: semantic.to_string(),
    }
}

fn requirement(
    id: impl Into<String>,
    cohort: SourceCohort,
    locator: impl Into<String>,
    classification: Classification,
    claim: impl Into<String>,
    expectation: Expectation,
    gap: impl Into<String>,
) -> Requirement {
    Requirement {
        id: id.into(),
        source: SourceLocator {
            cohort,
            locator: locator.into(),
        },
        classification,
        claim: claim.into(),
        expectation,
        evidence: Vec::new(),
        gap: Some(gap.into()),
    }
}

fn requirements_for(spec: DimensionSpec) -> Vec<Requirement> {
    let mut requirements = match spec.id {
        "language.lexical-and-grammar" => lexical_grammar::PRODUCTION_NAMES
            .into_iter()
            .map(|name| {
                requirement(
                    format!("{}.{}", spec.id, name),
                    SourceCohort::SmtlibLanguage,
                    format!("Reference/syntax-macros.tex:{name}"),
                    Classification::Standard,
                    format!("Implement the normative SMT-LIB 2.7 `{name}` production"),
                    expectation(
                        Some("accept a source-grounded well-formed witness and reject a malformed boundary witness"),
                        None,
                        Some("input rejection is positioned and continued-execution recovery reaches the next command"),
                        Some("response productions are recognized by a closed parser over live AY output"),
                        "the authenticated production has positive and negative evidence with exact transcript accounting",
                    ),
                    "no exhaustive source-grounded lexical/grammar validator receipt is attached",
                )
            })
            .collect(),
        "language.commands" => SMTLIB_COMMANDS
            .into_iter()
            .map(|name| {
                requirement(
                    format!("{}.{}", spec.id, name),
                    SourceCohort::SmtlibLanguage,
                    format!("Reference/syntax-macros.tex:cCommands:{name}"),
                    Classification::Standard,
                    format!("Implement the SMT-LIB 2.7 `{name}` command production"),
                    expectation(
                        Some("accept every well-formed standard production; accepted non-standard forms must be owned by the exact Z3 5.1.0 overlay, and all other malformed arity or delimiter forms are rejected"),
                        None,
                        Some("apply the command's normative preconditions, effects, and output behavior"),
                        None,
                        "the command transcript agrees with the pinned standard",
                    ),
                    "no exhaustive positive, negative, and stateful validator receipt is attached",
                )
            })
            .collect(),
        "registry.theories" => SMTLIB_THEORIES
            .into_iter()
            .map(|(name, path)| {
                requirement(
                    format!("{}.{}", spec.id, name),
                    SourceCohort::SmtlibRegistry,
                    path,
                    Classification::Standard,
                    format!("Implement every sort and function signature declared by theory `{name}`"),
                    expectation(
                        Some("accept every declared plain, indexed, qualified, and polymorphic form"),
                        Some("enforce index kinds, arity, operand sorts, result sorts, and overload constraints"),
                        None,
                        Some("produce semantics satisfying the pinned theory declaration"),
                        "positive and negative signature witnesses cover every declaration",
                    ),
                    "the declaration has no exhaustive signature and semantic validator receipt",
                )
            })
            .collect(),
        "registry.logics" => SMTLIB_LOGICS
            .into_iter()
            .map(|name| {
                requirement(
                    format!("{}.{}", spec.id, name),
                    SourceCohort::SmtlibRegistry,
                    format!("Logics/{name}.smt2"),
                    Classification::Standard,
                    format!("Implement the official `{name}` logic declaration and its prose restrictions"),
                    expectation(
                        Some("set-logic accepts the exact official logic symbol"),
                        Some("reject features excluded by the logic language"),
                        Some("route the logic without an unclassified fallback"),
                        Some("decided results obey all included theory semantics"),
                        "positive and negative witnesses cover the full declaration, not only its name",
                    ),
                    "the logic has no exhaustive language-restriction and semantic validator receipt",
                )
            })
            .collect(),
        "semantics.typing-and-scope" => language_semantics::type_scope_requirements(spec),
        "semantics.command-state-machine" => {
            language_semantics::command_state_requirements(spec)
        }
        "results.sat-models" => vec![requirement(
            format!("{}.independent-validation", spec.id),
            SourceCohort::Contract,
            "full-support-definition:sat-model-obligation",
            Classification::Gate,
            "Independently validate every authored assertion and check-sat-assuming literal against the exact published model and query epoch",
            expectation(
                None,
                Some("the model assigns well-sorted interpretations to every required symbol"),
                Some("model authority is invalidated by every semantic mutation or later query"),
                Some("sat is published only after complete independent validation"),
                "CannotConfirm, delegated-only, partial, stale, or printer-inconsistent models force unknown",
            ),
            "no universal independent SMT-LIB model-validation receipt is attached",
        )],
        "results.unsat-proofs" => vec![requirement(
            format!("{}.independent-replay", spec.id),
            SourceCohort::Contract,
            "full-support-definition:unsat-proof-obligation",
            Classification::Gate,
            "Strictly validate and independently replay every proof over the exact authored assertions and assumptions",
            expectation(
                None,
                None,
                Some("proof authority is bound to and invalidated with the exact query epoch"),
                Some("unsat is published only for a hole-free proof ending in the empty clause"),
                "trust, holes, unchecked theory lemmas, foreign assumptions, stale proofs, or unavailable checkers force unknown",
            ),
            "no universal strict proof and independent replay receipt is attached",
        )],
        "results.unknown-policy" => vec![requirement(
            format!("{}.closed-reasons", spec.id),
            SourceCohort::Contract,
            "full-support-definition:unknown-policy",
            Classification::Gate,
            "Inventory and induce every unknown reason and prove that authoritative result artifacts are revoked",
            expectation(
                None,
                None,
                Some("unknown revokes model, proof, core, optimum, and stale query authority"),
                Some("every incomplete or uncertified path returns a closed reason"),
                "no gate phase may itself be skipped, unavailable, timed out, or unknown",
            ),
            "the unknown-reason registry and artifact-revocation matrix are not exhaustively validated",
        )],
        "overlay.z3-5.1.0" => vec![
            requirement(
                format!("{}.c-abi", spec.id),
                SourceCohort::Z3Source,
                "exact-11-header-z3-5.1.0-include-graph;clang-c11-declaration-manifest;authenticated-libz3-5.1.0-export-table;live-stock-c-api-probes;per-symbol-semantic-contracts",
                Classification::ExactOverlay,
                "Require the exact 805-declaration Z3 5.1.0 C header/signature surface, resolution of all 807 exports, all 99 scoped observations, and authenticated executed-call plus exhaustive semantic-contract evidence for every declaration",
                expectation(
                    None,
                    Some("all 805 header declarations and signatures match, all 807 required export names resolve, all 99 scoped observations match, and all 805 declarations pass executed-call and exhaustive semantic-contract differentials"),
                    None,
                    Some("every header declaration, signature, required export, guarded scoped probe, per-symbol callability row, and per-symbol semantic-contract row passes"),
                    "the authenticated AY and Z3 shared-library bytes, clean current-main build stamp, exact headers/signatures/exports, scoped observations, executed calls, and semantic contracts are replayed; header and symbol resolution alone never prove an implementation ABI or behavior",
                ),
                "there is no authenticated current-main `builtin.z3-abi-5.0.v1` receipt",
            ),
            requirement(
                format!("{}.target-identity", spec.id),
                SourceCohort::Z3Source,
                "scripts/VERSION.txt;src/util/z3_version.h.in;live CLI/library identity",
                Classification::ExactOverlay,
                "Authenticate the pinned Z3 executable bytes and require AY's Z3-mode CLI identity transcript to report exactly Z3 5.1.0",
                expectation(
                    None,
                    None,
                    None,
                    Some("every oracle and differential receipt reports exactly Z3 5.1.0"),
                    "the transcript is evidence only for the authenticated executable; source and shared-library closure remain separate profile and inventory obligations",
                ),
                "the exact Z3 5.1.0 executable and AY identity transcript have not been validated for one closed campaign",
            ),
            requirement(
                format!("{}.source-inventory", spec.id),
                SourceCohort::Z3Source,
                "source-tree:commands,logics,theories,options,tactics,probes,extensions",
                Classification::ExactOverlay,
                "Extract every Z3 5.1.0 extension and alias that is observable through the CLI",
                expectation(
                    Some("all accepted Z3-only syntax and commands are owned by one overlay row"),
                    Some("all Z3-only signature and coercion behavior is explicit"),
                    Some("all option and command effects are explicit"),
                    None,
                    "nothing discovered in the pinned source or live registries is unclassified",
                ),
                "the Z3 5.1.0 observable source inventory is not closed",
            ),
            requirement(
                format!("{}.behavioral-transcripts", spec.id),
                SourceCohort::Z3Source,
                "live-oracle:exact-cli-transcript-matrix",
                Classification::ExactOverlay,
                "Differentially validate exit status, stdout, stderr, diagnostics, streaming, and stateful transcript behavior against the pinned Z3 5.1.0 binary",
                expectation(
                    Some("accepted and rejected transcript forms match their declared comparator"),
                    None,
                    Some("incremental command sequences and artifact lifetimes match"),
                    Some("verdict and diagnostic classes have no unadjudicated differences"),
                    "comparators are closed and no arbitrary normalization hides a difference",
                ),
                "there is no exhaustive exact-transcript receipt for the pinned oracle",
            ),
        ],
        "coverage.corpus" => vec![requirement(
            format!("{}.closed-query-manifest", spec.id),
            SourceCohort::OfficialCorpus,
            "immutable-corpus-manifest:all-files-and-queries",
            Classification::Gate,
            "Run every immutable corpus case query-by-query with required model or proof checks under one enforced resource envelope",
            expectation(
                Some("every manifest input is authenticated and no unexpected input is present"),
                None,
                Some("incremental queries retain their exact assertion and assumption epochs"),
                Some("zero wrong, invalid, missing, skipped, unknown-on-Z3-decided, timeout, memout, or crash cases"),
                "corpus selection and the enforced resource envelope are persisted in the receipt",
            ),
            "no closed all-files, all-queries corpus receipt is attached",
        )],
        "gate.integrity" => vec![requirement(
            format!("{}.negative-controls", spec.id),
            SourceCohort::Contract,
            "full-support-definition:mandatory-negative-controls",
            Classification::Gate,
            "Prove the gate rejects contract shrinkage, duplicate or unknown rows, stale or foreign evidence, checker spoofing, hash drift, corrupted artifacts, and interrupted phases",
            expectation(
                Some("malformed and schema-drifted contracts are rejected"),
                None,
                Some("evidence is one campaign bound to one source, build, profile, and resource envelope"),
                Some("aggregate pass fields never override failed detailed rows"),
                "every required negative control must fail for the intended reason",
            ),
            "the full gate-integrity mutation suite has no passing receipt",
        )],
        _ => Vec::new(),
    };
    requirements.sort_by(|left, right| left.id.cmp(&right.id));
    requirements
}

fn starter_contract(subject: Subject) -> Result<Contract, String> {
    let mut dimensions = Vec::with_capacity(DIMENSIONS.len());
    for spec in DIMENSIONS {
        let requirements = requirements_for(spec);
        let sha256 = inventory_sha256(&requirements)?;
        dimensions.push(Dimension {
            id: spec.id.to_string(),
            title: spec.title.to_string(),
            definition: spec.definition.to_string(),
            inventory: Inventory {
                granularity: starter_inventory_granularity(spec),
                item_count: requirements.len(),
                sha256,
                evidence: Vec::new(),
                gap: Some(
                    "no exhaustive source-inventory extractor receipt is attached".to_string(),
                ),
            },
            requirements,
        });
    }
    Ok(Contract {
        schema: MANIFEST_SCHEMA.to_string(),
        profile: canonical_profile(),
        campaign_id: UNASSIGNED_CAMPAIGN.to_string(),
        resource_envelope: None,
        subject,
        dimensions,
    })
}

fn starter_inventory_granularity(spec: DimensionSpec) -> InventoryGranularity {
    match spec.id {
        "coverage.corpus"
        | "gate.integrity"
        | "language.lexical-and-grammar"
        | "language.commands"
        | "overlay.z3-5.1.0"
        | "registry.logics"
        | "registry.theories"
        | "semantics.command-state-machine"
        | "semantics.typing-and-scope"
        | "results.sat-models"
        | "results.unsat-proofs"
        | "results.unknown-policy" => InventoryGranularity::ItemLevel,
        _ => InventoryGranularity::Unresolved,
    }
}

fn inventory_sha256(requirements: &[Requirement]) -> Result<String, String> {
    let mut hasher = Sha256::new();
    for requirement in requirements {
        let value = serde_json::json!({
            "id": requirement.id,
            "source": requirement.source,
            "classification": requirement.classification,
            "claim": requirement.claim,
            "expectation": requirement.expectation,
        });
        let encoded = serde_json::to_vec(&value)
            .map_err(|error| format!("serializing requirement inventory: {error}"))?;
        hasher.update(encoded);
        hasher.update(b"\n");
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn validate_contract(
    contract: &Contract,
    manifest_dir: &Path,
    mode: ValidationMode,
) -> Result<AuditReport, String> {
    if contract.schema != MANIFEST_SCHEMA {
        return Err(format!(
            "manifest schema mismatch: expected {MANIFEST_SCHEMA}, got {:?}",
            contract.schema
        ));
    }
    if contract.profile != canonical_profile() {
        return Err(format!(
            "profile drift: the manifest must use the built-in {PROFILE_ID} profile byte-for-byte"
        ));
    }
    validate_text(&contract.campaign_id, "campaign_id")?;
    if let Some(envelope) = contract.resource_envelope.as_deref() {
        validate_resource_envelope(envelope)?;
    }
    if contract.dimensions.len() > MAX_DIMENSIONS {
        return Err(format!(
            "manifest has {} dimensions; fixed limit is {MAX_DIMENSIONS}",
            contract.dimensions.len()
        ));
    }
    if contract.dimensions.len() != DIMENSIONS.len() {
        return Err(format!(
            "closed dimension mismatch: expected {}, got {}",
            DIMENSIONS.len(),
            contract.dimensions.len()
        ));
    }

    validate_optional_artifact(
        contract.subject.ay_executable.as_ref(),
        manifest_dir,
        "AY executable",
    )?;
    validate_optional_artifact(
        contract.subject.ay_shared_library.as_ref(),
        manifest_dir,
        "AY shared library",
    )?;
    let mut seen_dimension_ids = BTreeSet::new();
    let mut seen_requirement_ids = BTreeSet::new();
    let mut receipt_cache = ReceiptCache::default();
    let mut reports = Vec::with_capacity(DIMENSIONS.len());
    let mut requirement_count = 0usize;
    let mut validated_requirements = 0usize;
    let mut gap_requirements = 0usize;
    let mut reference_complete_dimensions = 0usize;
    let mut skipped_or_failed_evidence = 0usize;
    let mut blockers = Vec::new();

    for (dimension, spec) in contract.dimensions.iter().zip(DIMENSIONS) {
        if !seen_dimension_ids.insert(dimension.id.clone()) {
            return Err(format!("duplicate dimension id {:?}", dimension.id));
        }
        if dimension.id != spec.id
            || dimension.title != spec.title
            || dimension.definition != spec.definition
        {
            return Err(format!(
                "closed dimension definition drift at {:?}; expected id {:?}",
                dimension.id, spec.id
            ));
        }
        if dimension.requirements.is_empty() {
            return Err(format!("dimension {} has no requirements", dimension.id));
        }
        requirement_count = requirement_count
            .checked_add(dimension.requirements.len())
            .ok_or("requirement count overflow")?;
        if requirement_count > MAX_REQUIREMENTS {
            return Err(format!(
                "manifest has more than the fixed {MAX_REQUIREMENTS} requirements"
            ));
        }
        if dimension.inventory.item_count != dimension.requirements.len() {
            return Err(format!(
                "{} inventory item_count={} but requirements={}",
                dimension.id,
                dimension.inventory.item_count,
                dimension.requirements.len()
            ));
        }
        let expected_inventory_sha = inventory_sha256(&dimension.requirements)?;
        if dimension.inventory.sha256 != expected_inventory_sha {
            return Err(format!(
                "{} inventory digest mismatch: expected {}, got {}",
                dimension.id, expected_inventory_sha, dimension.inventory.sha256
            ));
        }
        validate_evidence_refs(
            &dimension.inventory.evidence,
            &format!("{} inventory", dimension.id),
        )?;

        let mut previous_id: Option<&str> = None;
        for requirement in &dimension.requirements {
            if previous_id.is_some_and(|previous| previous >= requirement.id.as_str()) {
                return Err(format!(
                    "{} requirements must be sorted by unique id; {:?} follows {:?}",
                    dimension.id, requirement.id, previous_id
                ));
            }
            previous_id = Some(&requirement.id);
            validate_requirement(requirement, spec)?;
            if !seen_requirement_ids.insert(requirement.id.clone()) {
                return Err(format!(
                    "duplicate global requirement id {:?}",
                    requirement.id
                ));
            }
        }
        require_canonical_rows(dimension, spec)?;

        let requirement_ids = dimension
            .requirements
            .iter()
            .map(|row| row.id.clone())
            .collect::<BTreeSet<_>>();
        let inventory_results = validate_evidence_set(
            &dimension.inventory.evidence,
            EvidenceContext {
                contract,
                manifest_dir,
                dimension,
                expected_kind: ValidatorKind::ReferenceExtractor,
                required_requirement_id: None,
                exact_requirement_ids: Some(&requirement_ids),
                mode,
            },
            &mut receipt_cache,
        )?;
        skipped_or_failed_evidence = skipped_or_failed_evidence
            .checked_add(inventory_results.non_passing)
            .ok_or("evidence count overflow")?;
        let reference_complete = dimension.inventory.granularity == InventoryGranularity::ItemLevel
            && !inventory_results.empty
            && inventory_results.non_passing == 0;
        validate_gap_field(
            dimension.inventory.gap.as_deref(),
            reference_complete,
            &format!("{} inventory", dimension.id),
        )?;
        if reference_complete {
            reference_complete_dimensions += 1;
        } else {
            blockers.push(format!("{}: reference inventory incomplete", dimension.id));
        }

        let mut dimension_validated = 0usize;
        for requirement in &dimension.requirements {
            validate_evidence_refs(
                &requirement.evidence,
                &format!("requirement {}", requirement.id),
            )?;
            let results = validate_evidence_set(
                &requirement.evidence,
                EvidenceContext {
                    contract,
                    manifest_dir,
                    dimension,
                    expected_kind: spec.validator_kind,
                    required_requirement_id: Some(&requirement.id),
                    exact_requirement_ids: None,
                    mode,
                },
                &mut receipt_cache,
            )?;
            skipped_or_failed_evidence = skipped_or_failed_evidence
                .checked_add(results.non_passing)
                .ok_or("evidence count overflow")?;
            let validated = !results.empty && results.non_passing == 0;
            validate_gap_field(
                requirement.gap.as_deref(),
                validated,
                &format!("requirement {}", requirement.id),
            )?;
            if validated {
                dimension_validated += 1;
                validated_requirements += 1;
            } else {
                gap_requirements += 1;
                blockers.push(format!("{}: semantic evidence gap", requirement.id));
            }
        }
        reports.push(DimensionReport {
            id: dimension.id.clone(),
            reference_complete,
            requirement_count: dimension.requirements.len(),
            validated_requirements: dimension_validated,
            gap_requirements: dimension.requirements.len() - dimension_validated,
        });
    }

    if contract.campaign_id == UNASSIGNED_CAMPAIGN {
        blockers.push("campaign_id is still `unassigned`".to_string());
    }
    if contract.subject.ay_executable.is_none() {
        blockers.push("subject.ay_executable is not bound".to_string());
    }
    if contract.subject.ay_shared_library.is_none() {
        blockers.push("subject.ay_shared_library is not bound".to_string());
    }
    if contract.resource_envelope.is_none() {
        blockers.push("resource_envelope is not bound".to_string());
    }

    let reference_incomplete_dimensions = DIMENSIONS.len() - reference_complete_dimensions;
    let complete = blockers.is_empty()
        && reference_incomplete_dimensions == 0
        && gap_requirements == 0
        && skipped_or_failed_evidence == 0
        && validated_requirements == requirement_count;
    if complete && mode.verifies_pinned_runtime() {
        verify_reference_artifact(
            &contract.profile.z3_overlay.reference_executable.path,
            &contract.profile.z3_overlay.reference_executable.sha256,
            "Z3 5.1.0 executable",
        )?;
        verify_reference_artifact(
            &contract.profile.z3_overlay.reference_shared_library.path,
            &contract.profile.z3_overlay.reference_shared_library.sha256,
            "Z3 5.1.0 shared library",
        )?;
    }
    Ok(AuditReport {
        complete,
        summary: AuditSummary {
            dimension_count: DIMENSIONS.len(),
            requirement_count,
            reference_complete_dimensions,
            reference_incomplete_dimensions,
            validated_requirements,
            gap_requirements,
            skipped_or_failed_evidence,
        },
        dimensions: reports,
        blockers,
    })
}

fn validate_requirement(requirement: &Requirement, spec: DimensionSpec) -> Result<(), String> {
    validate_id(&requirement.id, "requirement id")?;
    if !requirement.id.starts_with(&format!("{}.", spec.id)) {
        return Err(format!(
            "requirement {:?} does not belong to dimension {}",
            requirement.id, spec.id
        ));
    }
    validate_text(&requirement.source.locator, "source locator")?;
    validate_text(&requirement.claim, "requirement claim")?;
    validate_text(&requirement.expectation.semantic, "semantic expectation")?;
    for (label, value) in [
        (
            "parse expectation",
            requirement.expectation.parse.as_deref(),
        ),
        (
            "typing expectation",
            requirement.expectation.typing.as_deref(),
        ),
        (
            "state expectation",
            requirement.expectation.state.as_deref(),
        ),
        (
            "result expectation",
            requirement.expectation.result.as_deref(),
        ),
    ] {
        if let Some(value) = value {
            validate_text(value, label)?;
        }
    }
    let expected_classification = match spec.id {
        "overlay.z3-5.1.0" => Classification::ExactOverlay,
        "results.sat-models"
        | "results.unsat-proofs"
        | "results.unknown-policy"
        | "coverage.corpus"
        | "gate.integrity" => Classification::Gate,
        _ => Classification::Standard,
    };
    if requirement.classification != expected_classification
        && requirement.classification != Classification::AdjudicatedDeviation
    {
        return Err(format!(
            "{} has classification {:?}; expected {:?} or an adjudicated deviation",
            requirement.id, requirement.classification, expected_classification
        ));
    }
    if requirement.classification == Classification::AdjudicatedDeviation
        && requirement.source.cohort != SourceCohort::Z3Source
    {
        return Err(format!(
            "{}: an adjudicated deviation must cite the pinned Z3 source",
            requirement.id
        ));
    }
    Ok(())
}

fn require_canonical_rows(dimension: &Dimension, spec: DimensionSpec) -> Result<(), String> {
    let actual = dimension
        .requirements
        .iter()
        .map(|row| (row.id.as_str(), row))
        .collect::<BTreeMap<_, _>>();
    let required_rows = requirements_for(spec);
    if actual.len() != required_rows.len() {
        let required_ids = required_rows
            .iter()
            .map(|row| row.id.as_str())
            .collect::<BTreeSet<_>>();
        let actual_ids = actual.keys().copied().collect::<BTreeSet<_>>();
        let missing = required_ids
            .difference(&actual_ids)
            .copied()
            .collect::<Vec<_>>();
        let unexpected = actual
            .keys()
            .copied()
            .filter(|id| !required_ids.contains(id))
            .collect::<Vec<_>>();
        return Err(format!(
            "{} has invented or missing rows in its closed inventory: expected {}, got {}; missing={missing:?}; unexpected={unexpected:?}",
            dimension.id,
            required_rows.len(),
            actual.len()
        ));
    }
    for required in required_rows {
        let row = actual.get(required.id.as_str()).ok_or_else(|| {
            format!(
                "{} is missing canonical requirement {}",
                dimension.id, required.id
            )
        })?;
        if row.source != required.source
            || row.classification != required.classification
            || row.claim != required.claim
            || row.expectation != required.expectation
        {
            return Err(format!(
                "{} canonical requirement {} changed its source or obligation",
                dimension.id, required.id
            ));
        }
    }
    Ok(())
}

fn validate_gap_field(gap: Option<&str>, complete: bool, label: &str) -> Result<(), String> {
    match (complete, gap) {
        (true, None) => Ok(()),
        (false, Some(reason)) => validate_text(reason, &format!("{label} gap")),
        (true, Some(_)) => Err(format!(
            "{label} has passing exhaustive evidence but still carries a gap"
        )),
        (false, None) => Err(format!(
            "{label} is not validated and must carry an explicit gap"
        )),
    }
}

#[derive(Clone, Copy)]
struct EvidenceContext<'a> {
    contract: &'a Contract,
    manifest_dir: &'a Path,
    dimension: &'a Dimension,
    expected_kind: ValidatorKind,
    required_requirement_id: Option<&'a str>,
    exact_requirement_ids: Option<&'a BTreeSet<String>>,
    mode: ValidationMode,
}

#[derive(Default)]
struct EvidenceResults {
    empty: bool,
    non_passing: usize,
}

fn validate_evidence_set(
    evidence: &[EvidenceRef],
    context: EvidenceContext<'_>,
    cache: &mut ReceiptCache,
) -> Result<EvidenceResults, String> {
    let mut results = EvidenceResults {
        empty: evidence.is_empty(),
        non_passing: 0,
    };
    for reference in evidence {
        let receipt = load_validator_receipt(reference, context.manifest_dir, cache)?;
        let passing = validate_validator_receipt(receipt, context)?;
        if !passing {
            results.non_passing += 1;
        }
    }
    Ok(results)
}

fn validate_validator_receipt(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<bool, String> {
    if receipt.schema != VALIDATOR_RECEIPT_SCHEMA {
        return Err(format!(
            "{} validator receipt schema mismatch: {:?}",
            context.dimension.id, receipt.schema
        ));
    }
    if receipt.campaign_id != context.contract.campaign_id {
        return Err(format!(
            "{} evidence belongs to campaign {:?}, not {:?}",
            context.dimension.id, receipt.campaign_id, context.contract.campaign_id
        ));
    }
    if receipt.profile_id != PROFILE_ID {
        return Err(format!(
            "{} evidence targets profile {:?}, not {PROFILE_ID}",
            context.dimension.id, receipt.profile_id
        ));
    }
    let expected_profile_sha = canonical_profile_sha256()?;
    if receipt.profile_sha256 != expected_profile_sha {
        return Err(format!(
            "{} evidence profile digest mismatch: expected {}, got {}",
            context.dimension.id, expected_profile_sha, receipt.profile_sha256
        ));
    }
    if receipt.dimension_id != context.dimension.id {
        return Err(format!(
            "evidence dimension mismatch: expected {}, got {}",
            context.dimension.id, receipt.dimension_id
        ));
    }
    if receipt.inventory_sha256 != context.dimension.inventory.sha256 {
        return Err(format!(
            "{} evidence inventory digest mismatch",
            context.dimension.id
        ));
    }
    if receipt.validator.kind != context.expected_kind {
        return Err(format!(
            "{} evidence uses validator kind {:?}; expected {:?}",
            context.dimension.id, receipt.validator.kind, context.expected_kind
        ));
    }
    validate_id(&receipt.validator.id, "validator id")?;
    validate_sha256(&receipt.validator.sha256, "validator sha256")?;
    let validator_path = resolve_validator_artifact(receipt, context.manifest_dir)?;
    let actual_validator_sha = sha256_file(&validator_path, "validator implementation")?;
    if actual_validator_sha != receipt.validator.sha256 {
        return Err(format!(
            "validator implementation hash mismatch for {}: expected {}, got {}",
            validator_path.display(),
            receipt.validator.sha256,
            actual_validator_sha
        ));
    }

    let receipt_ids = sorted_unique_ids(&receipt.requirement_ids, "receipt requirement_ids")?;
    let known_ids = context
        .dimension
        .requirements
        .iter()
        .map(|row| row.id.clone())
        .collect::<BTreeSet<_>>();
    if !receipt_ids.is_subset(&known_ids) {
        let unknown = receipt_ids.difference(&known_ids).collect::<Vec<_>>();
        return Err(format!(
            "{} evidence names unknown requirements: {:?}",
            context.dimension.id, unknown
        ));
    }
    if let Some(required) = context.required_requirement_id {
        if !receipt_ids.contains(required) {
            return Err(format!(
                "{} evidence does not cover required row {required}",
                context.dimension.id
            ));
        }
    }
    if let Some(expected) = context.exact_requirement_ids {
        if &receipt_ids != expected {
            return Err(format!(
                "{} inventory extractor coverage is not exact: expected {}, got {} rows",
                context.dimension.id,
                expected.len(),
                receipt_ids.len()
            ));
        }
    }

    validate_receipt_subject(receipt, context.contract)?;
    validate_reference_inputs(receipt, context.manifest_dir)?;
    validate_auxiliary_tools(receipt, context.manifest_dir)?;
    if validator_uses_z3(receipt.validator.kind) {
        let expected = &context
            .contract
            .profile
            .z3_overlay
            .reference_executable
            .sha256;
        if receipt.z3_binary_sha256.as_deref() != Some(expected) {
            return Err(format!(
                "{} evidence is not bound to the pinned Z3 5.1.0 executable",
                context.dimension.id
            ));
        }
    } else if let Some(value) = receipt.z3_binary_sha256.as_deref() {
        validate_sha256(value, "optional z3_binary_sha256")?;
    }
    if receipt.validator.id == "builtin.z3-abi-5.0.v1" {
        let expected = &context
            .contract
            .profile
            .z3_overlay
            .reference_shared_library
            .sha256;
        if receipt.z3_shared_library_sha256.as_deref() != Some(expected) {
            return Err(
                "builtin.z3-abi-5.0.v1 is not bound to the pinned Z3 5.1.0 shared library"
                    .to_string(),
            );
        }
    } else if let Some(value) = receipt.z3_shared_library_sha256.as_deref() {
        validate_sha256(value, "optional z3_shared_library_sha256")?;
    }
    if receipt.validator.kind != ValidatorKind::ReferenceExtractor {
        let contract_envelope = context
            .contract
            .resource_envelope
            .as_deref()
            .ok_or_else(|| {
                format!(
                    "{} semantic evidence requires a contract-wide resource_envelope",
                    context.dimension.id
                )
            })?;
        validate_resource_envelope(contract_envelope)?;
        if receipt.resource_envelope.as_deref() != Some(contract_envelope) {
            return Err(format!(
                "{} evidence resource envelope differs from the contract campaign",
                context.dimension.id
            ));
        }
    } else if receipt.resource_envelope.is_some() {
        return Err(
            "reference-extractor evidence must not claim a solver resource run".to_string(),
        );
    }
    validate_case_results(&receipt.case_results, &receipt.cases)?;
    validate_registered_validator(receipt, context)?;
    let passing = receipt.result == ValidatorResult::Pass
        && receipt.exhaustive
        && receipt.cases.total > 0
        && receipt.cases.passed == receipt.cases.total
        && receipt.cases.failed == 0
        && receipt.cases.skipped == 0
        && receipt.cases.unknown == 0
        && receipt.cases.timed_out == 0
        && receipt.cases.memout == 0
        && receipt.cases.crashed == 0
        && receipt.cases.unavailable == 0;
    if receipt.result == ValidatorResult::Pass && !passing {
        return Err(format!(
            "{} receipt asserts pass but detailed rows are incomplete or non-passing",
            context.dimension.id
        ));
    }
    Ok(passing)
}

fn validate_receipt_subject(receipt: &ValidatorReceipt, contract: &Contract) -> Result<(), String> {
    if receipt.validator.kind == ValidatorKind::ReferenceExtractor {
        if receipt.subject.ay_executable_sha256.is_some()
            || receipt.subject.ay_shared_library_sha256.is_some()
        {
            return Err(
                "reference-extractor evidence must not claim semantic AY artifact binding"
                    .to_string(),
            );
        }
        return Ok(());
    }
    if receipt.validator.id == z3_source_inventory::VALIDATOR_ID {
        if receipt.subject.ay_executable_sha256.is_some()
            || receipt.subject.ay_shared_library_sha256.is_some()
        {
            return Err(
                "Z3 source-inventory evidence must not claim AY behavior binding".to_string(),
            );
        }
        return Ok(());
    }
    if receipt.validator.id == "builtin.z3-abi-5.0.v1" {
        match (
            contract.subject.ay_executable.as_ref(),
            receipt.subject.ay_executable_sha256.as_deref(),
        ) {
            (Some(expected), Some(actual)) if actual == expected.sha256 => {}
            (None, None) => {}
            _ => {
                return Err(
                    "Z3 ABI receipt AY executable hash does not match the contract".to_string(),
                );
            }
        }
        let library = contract
            .subject
            .ay_shared_library
            .as_ref()
            .ok_or("Z3 ABI evidence requires subject.ay_shared_library")?;
        if receipt.subject.ay_shared_library_sha256.as_deref() != Some(&library.sha256) {
            return Err(
                "Z3 ABI receipt AY shared-library hash does not match the contract".to_string(),
            );
        }
        return Ok(());
    }
    let executable = contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("semantic evidence requires subject.ay_executable")?;
    if receipt.subject.ay_executable_sha256.as_deref() != Some(&executable.sha256) {
        return Err("validator receipt AY executable hash does not match the contract".to_string());
    }
    match (
        contract.subject.ay_shared_library.as_ref(),
        receipt.subject.ay_shared_library_sha256.as_deref(),
    ) {
        (Some(expected), Some(actual)) if actual == expected.sha256 => {}
        (None, None) => {}
        _ => {
            return Err(
                "validator receipt AY shared-library hash does not match the contract".to_string(),
            );
        }
    }
    Ok(())
}

fn validate_reference_inputs(receipt: &ValidatorReceipt, base: &Path) -> Result<(), String> {
    validate_reference_input_rows(&receipt.reference_inputs, base)
}

fn validate_reference_input_rows(inputs: &[ReferenceInput], base: &Path) -> Result<(), String> {
    if inputs.len() > MAX_REFERENCE_INPUTS {
        return Err(format!(
            "validator receipt has {} reference inputs; fixed limit is {MAX_REFERENCE_INPUTS}",
            inputs.len()
        ));
    }
    let mut previous: Option<&str> = None;
    let mut paths = BTreeSet::new();
    for input in inputs {
        validate_id(&input.id, "reference input id")?;
        if previous.is_some_and(|prior| prior >= input.id.as_str()) {
            return Err("reference inputs must be sorted and duplicate-free".to_string());
        }
        previous = Some(&input.id);
        validate_text(&input.repository, "reference input repository")?;
        validate_text(&input.revision, "reference input revision")?;
        validate_text(&input.selection, "reference input selection")?;
        if input.item_count == 0 {
            return Err(format!(
                "reference input {} has an empty selected-source inventory",
                input.id
            ));
        }
        validate_text(&input.digest_kind, "reference input digest_kind")?;
        validate_sha256(&input.selection_sha256, "reference input selection_sha256")?;
        validate_relative_path(&input.snapshot.path, "reference input snapshot path")?;
        validate_sha256(&input.snapshot.sha256, "reference input snapshot sha256")?;
        if !paths.insert(input.snapshot.path.as_str()) {
            return Err("reference inputs must use distinct snapshot artifacts".to_string());
        }
        let path = resolve_relative_evidence_path(base, &input.snapshot.path)?;
        let actual = sha256_file(&path, "reference input snapshot")?;
        if actual != input.snapshot.sha256 {
            return Err(format!(
                "reference input {} snapshot hash mismatch: expected {}, got {actual}",
                input.id, input.snapshot.sha256
            ));
        }
    }
    Ok(())
}

fn validate_auxiliary_tools(receipt: &ValidatorReceipt, base: &Path) -> Result<(), String> {
    validate_auxiliary_tool_rows(&receipt.auxiliary_tools, base)
}

fn validate_auxiliary_tool_rows(tools: &[AuxiliaryTool], base: &Path) -> Result<(), String> {
    if tools.len() > MAX_AUXILIARY_TOOLS {
        return Err(format!(
            "validator receipt has {} auxiliary tools; fixed limit is {MAX_AUXILIARY_TOOLS}",
            tools.len()
        ));
    }
    let mut previous: Option<&str> = None;
    let mut paths = BTreeSet::new();
    for tool in tools {
        validate_id(&tool.id, "auxiliary tool id")?;
        if previous.is_some_and(|prior| prior >= tool.id.as_str()) {
            return Err("auxiliary tools must be sorted and duplicate-free".to_string());
        }
        previous = Some(&tool.id);
        validate_text(&tool.role, "auxiliary tool role")?;
        validate_text(&tool.version_output, "auxiliary tool version_output")?;
        validate_relative_path(&tool.artifact.path, "auxiliary tool path")?;
        validate_sha256(&tool.artifact.sha256, "auxiliary tool sha256")?;
        if !paths.insert(tool.artifact.path.as_str()) {
            return Err("auxiliary tools must use distinct executable artifacts".to_string());
        }
        let path = resolve_relative_evidence_path(base, &tool.artifact.path)?;
        let actual = sha256_file(&path, "auxiliary tool")?;
        if actual != tool.artifact.sha256 {
            return Err(format!(
                "auxiliary tool {} hash mismatch: expected {}, got {actual}",
                tool.id, tool.artifact.sha256
            ));
        }
    }
    Ok(())
}

fn resolve_validator_artifact(
    receipt: &ValidatorReceipt,
    manifest_dir: &Path,
) -> Result<PathBuf, String> {
    if matches!(
        receipt.validator.id.as_str(),
        "builtin.target-identity.v1"
            | "builtin.z3-abi-5.0.v1"
            | gate_integrity::VALIDATOR_ID
            | language_semantics::TYPE_SCOPE_VALIDATOR_ID
            | language_semantics::STATE_MACHINE_VALIDATOR_ID
            | lexical_grammar::VALIDATOR_ID
            | logic_registry::VALIDATOR_ID
            | official_corpus::INVENTORY_VALIDATOR_ID
            | official_corpus::VALIDATOR_ID
            | reference_inventory::VALIDATOR_ID
            | sat_models::VALIDATOR_ID
            | standard_commands::VALIDATOR_ID
            | theory_registry::VALIDATOR_ID
            | unknown_policy::VALIDATOR_ID
            | unsat_proofs::VALIDATOR_ID
            | z3_behavioral::VALIDATOR_ID
            | z3_source_inventory::REFERENCE_VALIDATOR_ID
            | z3_source_inventory::VALIDATOR_ID
    ) {
        validate_text(&receipt.validator.path, "built-in validator recorded path")?;
        if !Path::new(&receipt.validator.path).is_absolute() {
            return Err("built-in validator path must be absolute".to_string());
        }
        return fs::canonicalize(
            std::env::current_exe()
                .map_err(|error| format!("locating current parity validator: {error}"))?,
        )
        .map_err(|error| format!("canonicalizing current parity validator: {error}"));
    }
    resolve_relative_evidence_path(manifest_dir, &receipt.validator.path)
}

fn validate_registered_validator(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    match receipt.validator.id.as_str() {
        "builtin.target-identity.v1" => {
            if receipt.validator.kind != ValidatorKind::Z3Differential
                || context.dimension.id != "overlay.z3-5.1.0"
                || receipt.requirement_ids != ["overlay.z3-5.1.0.target-identity".to_string()]
                || !receipt.exhaustive
                || receipt.z3_shared_library_sha256.is_some()
                || !receipt.reference_inputs.is_empty()
                || !receipt.auxiliary_tools.is_empty()
                || receipt.source_provenance.is_some()
            {
                return Err(
                    "builtin.target-identity.v1 has invalid kind, dimension, coverage, exhaustive flag, or ABI-only binding".to_string(),
                );
            }
            let expected_input = sha256_bytes(b"(get-info :name)\n(get-info :version)\n(exit)\n");
            let expected_stdout = "(:name \"Z3\")\n(:version \"5.1.0\")\n";
            let expected_ids = ["ay.identity", "z3.identity"];
            if receipt.case_results.len() != expected_ids.len() {
                return Err(
                    "builtin.target-identity.v1 must contain exactly two detailed cases"
                        .to_string(),
                );
            }
            for (row, expected_id) in receipt.case_results.iter().zip(expected_ids) {
                if row.id != expected_id || row.input_sha256 != expected_input {
                    return Err(
                        "builtin.target-identity.v1 case identity or input hash drift".to_string(),
                    );
                }
                if row.process.is_none() {
                    return Err(format!(
                        "{} is missing its guarded process observation",
                        row.id
                    ));
                }
                if row.outcome == ValidatorCaseOutcome::Pass
                    && (row.exit_code != Some(0)
                        || row.stdout.as_deref() != Some(expected_stdout)
                        || row.stderr.as_deref() != Some(""))
                {
                    return Err(format!(
                        "{} claims pass without the exact exit/stdout/stderr transcript",
                        row.id
                    ));
                }
            }
            if context.mode.replays_registered_validators() {
                replay_target_identity_receipt(receipt, context)?;
            }
            Ok(())
        }
        "builtin.z3-abi-5.0.v1" => {
            validate_z3_abi_receipt_shape(receipt, context)?;
            if context.mode.replays_registered_validators() {
                replay_z3_abi_receipt(receipt, context)?;
            }
            Ok(())
        }
        gate_integrity::VALIDATOR_ID => gate_integrity::validate_and_replay(receipt, context),
        language_semantics::TYPE_SCOPE_VALIDATOR_ID => {
            language_semantics::validate_type_scope(receipt, context)
        }
        language_semantics::STATE_MACHINE_VALIDATOR_ID => {
            language_semantics::validate_command_state(receipt, context)
        }
        lexical_grammar::VALIDATOR_ID => lexical_grammar::validate_and_replay(receipt, context),
        logic_registry::VALIDATOR_ID => logic_registry::validate_and_replay(receipt, context),
        official_corpus::INVENTORY_VALIDATOR_ID => {
            official_corpus::validate_inventory_and_replay(receipt, context)
        }
        official_corpus::VALIDATOR_ID => official_corpus::validate_and_replay(receipt, context),
        reference_inventory::VALIDATOR_ID => {
            reference_inventory::validate_and_replay(receipt, context)
        }
        sat_models::VALIDATOR_ID => sat_models::validate_and_replay(receipt, context),
        standard_commands::VALIDATOR_ID => standard_commands::validate_and_replay(receipt, context),
        theory_registry::VALIDATOR_ID => theory_registry::validate_and_replay(receipt, context),
        unknown_policy::VALIDATOR_ID => unknown_policy::validate_and_replay(receipt, context),
        unsat_proofs::VALIDATOR_ID => unsat_proofs::validate_and_replay(receipt, context),
        z3_behavioral::VALIDATOR_ID => z3_behavioral::validate_and_replay(receipt, context),
        z3_source_inventory::REFERENCE_VALIDATOR_ID => {
            z3_source_inventory::validate_reference_and_replay(receipt, context)
        }
        z3_source_inventory::VALIDATOR_ID => {
            z3_source_inventory::validate_and_replay(receipt, context)
        }
        other => Err(format!(
            "unregistered validator {other:?}; only validators implemented and dispatched by this parity binary may close a conformance row"
        )),
    }
}

fn validate_z3_abi_receipt_shape(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    if receipt.validator.kind != ValidatorKind::Z3Differential
        || context.dimension.id != "overlay.z3-5.1.0"
        || receipt.requirement_ids != ["overlay.z3-5.1.0.c-abi".to_string()]
        || !receipt.exhaustive
        || !receipt.reference_inputs.is_empty()
        || !receipt.auxiliary_tools.is_empty()
    {
        return Err(
            "builtin.z3-abi-5.0.v1 has invalid kind, dimension, coverage, or exhaustive flag"
                .to_string(),
        );
    }
    let provenance = receipt
        .source_provenance
        .as_ref()
        .ok_or("builtin.z3-abi-5.0.v1 requires typed source provenance")?;
    validate_full_commit(&provenance.source_commit, "ABI receipt source commit")?;
    validate_full_commit(
        &provenance.origin_main_commit,
        "ABI receipt origin/main commit",
    )?;
    if !provenance.source_clean
        || provenance.source_commit != provenance.origin_main_commit
        || build_stamp_commit(&provenance.ay_shared_library_build_stamp)
            != Some(provenance.source_commit.as_str())
    {
        return Err("ABI receipt does not bind a clean AY build at exact current main".to_string());
    }
    let ay_sha256 = receipt
        .subject
        .ay_shared_library_sha256
        .as_deref()
        .ok_or("ABI receipt has no AY shared-library hash")?;
    let z3_sha256 = receipt
        .z3_shared_library_sha256
        .as_deref()
        .ok_or("ABI receipt has no Z3 shared-library hash")?;
    let envelope = receipt
        .resource_envelope
        .as_deref()
        .ok_or("ABI receipt has no resource envelope")?;
    let binding = AbiCaseBinding {
        profile_sha256: &receipt.profile_sha256,
        inventory_sha256: &receipt.inventory_sha256,
        validator_sha256: &receipt.validator.sha256,
        ay_sha256,
        z3_sha256,
        source: provenance,
        resource_envelope: envelope,
    };

    let mut fixed = BTreeMap::from([
        (
            "abi.child.ay".to_string(),
            abi_child_expectation("abi.child.ay").to_string(),
        ),
        (
            "abi.child.z3".to_string(),
            abi_child_expectation("abi.child.z3").to_string(),
        ),
        (
            "abi.identity.ay-library".to_string(),
            format!("sha256={ay_sha256}"),
        ),
        (
            "abi.identity.z3-library".to_string(),
            format!("sha256={z3_sha256}"),
        ),
        (
            "abi.identity.z3-version".to_string(),
            crate::z3_abi_500::Z3_500_FULL_VERSION.to_string(),
        ),
        (
            "abi.manifest.z3-5.1.0".to_string(),
            format!(
                "count={};sha256={}",
                crate::z3_abi_500::REQUIRED_SYMBOL_COUNT,
                crate::z3_abi_500::REQUIRED_SYMBOL_MANIFEST_SHA256
            ),
        ),
        (
            "abi.provenance.ay-build".to_string(),
            format!("build-commit={}", provenance.source_commit),
        ),
        (
            "abi.provenance.current-main".to_string(),
            "ay-build-clean=true;HEAD=origin/main".to_string(),
        ),
    ]);
    for (probe, expected) in crate::z3_abi_500::expected_probe_values() {
        fixed.insert(format!("abi.probe.{probe}"), expected);
    }
    for (surface, expected) in crate::z3_abi_500::expected_c_surface_values() {
        fixed.insert(format!("abi.c-surface.{surface}"), expected);
    }
    fixed.insert(
        "abi.c-surface.shape".to_string(),
        "805 sorted unique public declarations; all declared names exported; exactly two library-only exports; byte-exact complete pinned header graph".to_string(),
    );
    for probe in crate::z3_abi_500::stock_c_probes() {
        for subject in ["ay", "z3"] {
            fixed.insert(
                format!("abi.stock-c.{}.{subject}", probe.id),
                abi_stock_c_expectation().to_string(),
            );
        }
    }
    for declaration in crate::z3_abi_500::public_c_declarations() {
        let (symbol, _) = declaration
            .split_once('|')
            .expect("authenticated declaration manifest row");
        fixed.insert(
            format!("abi.callability.{symbol}"),
            abi_callability_expectation().to_string(),
        );
    }
    fixed.insert(
        "abi.callability.full-c-api".to_string(),
        abi_callability_coverage_expectation().to_string(),
    );
    for declaration in crate::z3_abi_500::public_c_declarations() {
        let (symbol, _) = declaration
            .split_once('|')
            .expect("authenticated declaration manifest row");
        fixed.insert(
            format!("abi.semantic-contract.{symbol}"),
            abi_semantic_contract_expectation().to_string(),
        );
    }
    fixed.insert(
        "abi.semantic-contract.full-c-api".to_string(),
        abi_semantic_contract_coverage_expectation().to_string(),
    );

    let mut seen_fixed = BTreeSet::new();
    let mut symbols = Vec::new();
    for row in &receipt.case_results {
        if row.input_sha256 != binding.input_sha256(&row.id) {
            return Err(format!("{} input binding is stale or forged", row.id));
        }
        if row.stdout.is_some() || row.stderr.is_some() {
            return Err(format!(
                "{} must not persist child streams containing host-specific paths",
                row.id
            ));
        }
        let is_child = matches!(row.id.as_str(), "abi.child.ay" | "abi.child.z3")
            || row.id.starts_with("abi.stock-c.");
        if is_child != row.process.is_some() {
            return Err(format!(
                "{} has the wrong guarded-process observation shape",
                row.id
            ));
        }
        if !is_child && (row.exit_code.is_some() || row.process.is_some()) {
            return Err(format!(
                "{} may not claim a direct child-process observation",
                row.id
            ));
        }
        if is_child
            && row.outcome == ValidatorCaseOutcome::Pass
            && (row.exit_code != Some(0)
                || row.process.as_ref().is_none_or(|process| {
                    !process.stdin_complete
                        || process.timed_out
                        || process.memout
                        || process.stdout_truncated
                        || process.stderr_truncated
                }))
        {
            return Err(format!(
                "{} claims pass without a clean guarded child exit",
                row.id
            ));
        }

        if let Some(symbol) = row.id.strip_prefix("abi.symbol.") {
            validate_id(symbol, "ABI required symbol")?;
            if !symbol.starts_with("Z3_") {
                return Err(format!("ABI symbol case is not a Z3 symbol: {symbol:?}"));
            }
            if row.expected != "required Z3 5.1.0 symbol is dlsym-resolvable in AY" {
                return Err(format!("{} has a forged symbol expectation", row.id));
            }
            if row.outcome == ValidatorCaseOutcome::Pass && row.observed != "present" {
                return Err(format!("{} claims pass without dlsym presence", row.id));
            }
            symbols.push(symbol.to_string());
            continue;
        }
        let expected = fixed
            .get(&row.id)
            .ok_or_else(|| format!("unexpected ABI validator case {}", row.id))?;
        if &row.expected != expected || !seen_fixed.insert(row.id.clone()) {
            return Err(format!("{} has a forged or duplicate expectation", row.id));
        }
        if row.outcome == ValidatorCaseOutcome::Pass {
            let expected_observed = match row.id.as_str() {
                "abi.child.ay" => ABI_CHILD_JSON_WITH_AY_DIAGNOSTICS.to_string(),
                "abi.child.z3" => ABI_CHILD_JSON.to_string(),
                "abi.identity.ay-library" => format!("sha256={ay_sha256}"),
                "abi.identity.z3-library" => format!("sha256={z3_sha256}"),
                "abi.identity.z3-version" => crate::z3_abi_500::Z3_500_FULL_VERSION.to_string(),
                "abi.manifest.z3-5.1.0" => format!(
                    "count={};sha256={};dlsym={}",
                    crate::z3_abi_500::REQUIRED_SYMBOL_COUNT,
                    crate::z3_abi_500::REQUIRED_SYMBOL_MANIFEST_SHA256,
                    crate::z3_abi_500::REQUIRED_SYMBOL_COUNT
                ),
                "abi.provenance.ay-build" => provenance.ay_shared_library_build_stamp.clone(),
                "abi.provenance.current-main" => format!(
                    "ay-build-clean=true;HEAD={};origin/main={}",
                    provenance.source_commit, provenance.origin_main_commit
                ),
                "abi.c-surface.shape" => "exact".to_string(),
                "abi.callability.full-c-api" => format!(
                    "{0}/{0} authenticated executed-call markers; 0 missing",
                    crate::z3_abi_500::PUBLIC_C_DECLARATION_COUNT
                ),
                "abi.semantic-contract.full-c-api" => format!(
                    "{0}/{0} authenticated exhaustive semantic contracts; 0 missing",
                    crate::z3_abi_500::PUBLIC_C_DECLARATION_COUNT
                ),
                id if id.starts_with("abi.stock-c.") => ABI_STOCK_C_EXACT_TRANSCRIPT.to_string(),
                id if id.starts_with("abi.callability.") => "passed".to_string(),
                id if id.starts_with("abi.semantic-contract.") => "passed".to_string(),
                id if id.starts_with("abi.c-surface.") => {
                    let surface = id.trim_start_matches("abi.c-surface.");
                    crate::z3_abi_500::observed_c_surface_values()
                        .remove(surface)
                        .ok_or_else(|| format!("unhandled ABI C-surface pass case {id}"))?
                }
                id if id.starts_with("abi.probe.") => {
                    format!("z3={expected};ay={expected}")
                }
                _ => return Err(format!("unhandled ABI pass case {}", row.id)),
            };
            if row.observed != expected_observed {
                return Err(format!(
                    "{} claims pass without the canonical observation",
                    row.id
                ));
            }
        }
    }
    if seen_fixed.len() != fixed.len() {
        let missing = fixed
            .keys()
            .filter(|id| !seen_fixed.contains(*id))
            .cloned()
            .collect::<Vec<_>>();
        return Err(format!(
            "ABI validator receipt is missing cases: {missing:?}"
        ));
    }
    if !crate::z3_abi_500::required_symbol_set_is_exact(&symbols) {
        return Err(format!(
            "ABI validator must contain the exact {}-export-name manifest with sha256 {}",
            crate::z3_abi_500::REQUIRED_SYMBOL_COUNT,
            crate::z3_abi_500::REQUIRED_SYMBOL_MANIFEST_SHA256
        ));
    }
    if receipt.case_results.len() != crate::z3_abi_500::REQUIRED_SYMBOL_COUNT + fixed.len() {
        return Err("ABI validator detailed case inventory is not exact".to_string());
    }
    Ok(())
}

fn validator_uses_z3(kind: ValidatorKind) -> bool {
    matches!(
        kind,
        ValidatorKind::Z3Differential | ValidatorKind::OfficialCorpus
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ParsedResourceEnvelope {
    jobs: usize,
    memlimit_mb: usize,
    nbcore: usize,
    headroom_mb: usize,
    timeout: Duration,
}

fn parse_resource_envelope(value: &str) -> Result<ParsedResourceEnvelope, String> {
    validate_text(value, "resource_envelope")?;
    let fields = value
        .strip_prefix("oom-guard-v2:")
        .ok_or("resource_envelope must use the closed oom-guard-v2 schema")?
        .split(';')
        .collect::<Vec<_>>();
    let expected_keys = [
        "jobs",
        "memlimit_mb",
        "nbcore",
        "headroom_mb",
        "timeout_ns",
        "enforcement",
        "aggregate",
    ];
    if fields.len() != expected_keys.len() {
        return Err("resource_envelope has missing or extra fields".to_string());
    }
    let mut values = BTreeMap::new();
    for (field, expected_key) in fields.into_iter().zip(expected_keys) {
        let (key, value) = field
            .split_once('=')
            .ok_or("resource_envelope field has no `=`")?;
        if key != expected_key || value.is_empty() || values.insert(key, value).is_some() {
            return Err(
                "resource_envelope fields are not in the closed canonical order".to_string(),
            );
        }
    }
    let parse_positive_usize = |key: &str| -> Result<usize, String> {
        let parsed = values[key]
            .parse::<usize>()
            .map_err(|_| format!("resource_envelope {key} is not an integer"))?;
        if parsed == 0 {
            return Err(format!("resource_envelope {key} must be positive"));
        }
        Ok(parsed)
    };
    let jobs = parse_positive_usize("jobs")?;
    let memlimit_mb = parse_positive_usize("memlimit_mb")?;
    let nbcore = parse_positive_usize("nbcore")?;
    let headroom_mb = values["headroom_mb"]
        .parse::<usize>()
        .map_err(|_| "resource_envelope headroom_mb is not an integer".to_string())?;
    let timeout_ns = values["timeout_ns"]
        .parse::<u64>()
        .map_err(|_| "resource_envelope timeout_ns is not an integer".to_string())?;
    if timeout_ns == 0 {
        return Err("resource_envelope timeout_ns must be positive".to_string());
    }
    if values["enforcement"] != ENFORCEMENT_RSS_WATCHDOG_V1 {
        return Err(format!(
            "resource_envelope enforcement must be {ENFORCEMENT_RSS_WATCHDOG_V1}"
        ));
    }
    if values["aggregate"] != "ay-host-exclusive-flock-v1" {
        return Err("resource_envelope aggregate must be ay-host-exclusive-flock-v1".to_string());
    }
    Ok(ParsedResourceEnvelope {
        jobs,
        memlimit_mb,
        nbcore,
        headroom_mb,
        timeout: Duration::from_nanos(timeout_ns),
    })
}

fn validate_resource_envelope(value: &str) -> Result<(), String> {
    parse_resource_envelope(value).map(|_| ())
}

fn validate_case_counts(counts: &CaseCounts) -> Result<(), String> {
    let classified = [
        counts.passed,
        counts.failed,
        counts.skipped,
        counts.unknown,
        counts.timed_out,
        counts.memout,
        counts.crashed,
        counts.unavailable,
    ]
    .into_iter()
    .try_fold(0usize, |sum, value| sum.checked_add(value))
    .ok_or("validator case-count overflow")?;
    if classified != counts.total {
        return Err(format!(
            "validator case accounting is not closed: total={}, classified={classified}",
            counts.total
        ));
    }
    Ok(())
}

fn validate_case_results(rows: &[ValidatorCase], counts: &CaseCounts) -> Result<(), String> {
    validate_case_counts(counts)?;
    if rows.len() != counts.total {
        return Err(format!(
            "validator detailed-row count {} does not match total {}",
            rows.len(),
            counts.total
        ));
    }
    let mut derived = CaseCounts {
        total: rows.len(),
        passed: 0,
        failed: 0,
        skipped: 0,
        unknown: 0,
        timed_out: 0,
        memout: 0,
        crashed: 0,
        unavailable: 0,
    };
    let mut previous: Option<&str> = None;
    for row in rows {
        validate_id(&row.id, "validator case id")?;
        if previous.is_some_and(|prior| prior >= row.id.as_str()) {
            return Err("validator case_results must be sorted and duplicate-free".to_string());
        }
        previous = Some(&row.id);
        validate_sha256(&row.input_sha256, "validator case input_sha256")?;
        validate_text(&row.expected, "validator case expected")?;
        validate_text(&row.observed, "validator case observed")?;
        if let Some(stdout) = row.stdout.as_deref() {
            if stdout.len() > 1024 * 1024 {
                return Err("validator case stdout exceeds the fixed 1 MiB limit".to_string());
            }
        }
        if let Some(stderr) = row.stderr.as_deref() {
            if stderr.len() > 1024 * 1024 {
                return Err("validator case stderr exceeds the fixed 1 MiB limit".to_string());
            }
        }
        if let Some(process) = row.process.as_ref() {
            if row.outcome == ValidatorCaseOutcome::Pass
                && (!process.stdin_complete
                    || process.timed_out
                    || process.memout
                    || process.stdout_truncated
                    || process.stderr_truncated
                    || row.exit_code.is_none())
            {
                return Err(format!(
                    "{} claims pass with incomplete input, no concrete exit status, or truncated/limited execution",
                    row.id
                ));
            }
            if process.timed_out && row.outcome != ValidatorCaseOutcome::Timeout {
                return Err(format!(
                    "{} timeout flag disagrees with its outcome",
                    row.id
                ));
            }
            if process.memout && row.outcome != ValidatorCaseOutcome::Memout {
                return Err(format!("{} memout flag disagrees with its outcome", row.id));
            }
        }
        match row.outcome {
            ValidatorCaseOutcome::Pass => derived.passed += 1,
            ValidatorCaseOutcome::Fail => derived.failed += 1,
            ValidatorCaseOutcome::Skipped => derived.skipped += 1,
            ValidatorCaseOutcome::Unknown => derived.unknown += 1,
            ValidatorCaseOutcome::Timeout => derived.timed_out += 1,
            ValidatorCaseOutcome::Memout => derived.memout += 1,
            ValidatorCaseOutcome::Crash => derived.crashed += 1,
            ValidatorCaseOutcome::Unavailable => derived.unavailable += 1,
        }
    }
    if &derived != counts {
        return Err("validator aggregate counts do not match recomputed detailed rows".to_string());
    }
    Ok(())
}

fn load_validator_receipt<'a>(
    reference: &EvidenceRef,
    manifest_dir: &Path,
    cache: &'a mut ReceiptCache,
) -> Result<&'a ValidatorReceipt, String> {
    validate_sha256(&reference.sha256, "evidence receipt sha256")?;
    let path = resolve_relative_evidence_path(manifest_dir, &reference.path)?;
    let cache_key = path
        .to_str()
        .ok_or_else(|| format!("evidence path is not UTF-8: {}", path.display()))?
        .to_string();
    if !cache.values.contains_key(&cache_key) {
        let bytes = read_bounded_bytes(
            &path,
            MAX_VALIDATOR_RECEIPT_BYTES,
            "validator receipt",
            true,
        )?;
        let actual_sha = sha256_bytes(&bytes);
        if actual_sha != reference.sha256 {
            return Err(format!(
                "validator receipt hash mismatch for {}: expected {}, got {}",
                path.display(),
                reference.sha256,
                actual_sha
            ));
        }
        let receipt: ValidatorReceipt = serde_json::from_slice(&bytes).map_err(|error| {
            format!("invalid validator receipt JSON {}: {error}", path.display())
        })?;
        cache
            .values
            .insert(cache_key.clone(), (actual_sha, receipt));
    }
    let (cached_sha, receipt) = cache
        .values
        .get(&cache_key)
        .ok_or_else(|| "internal receipt cache error".to_string())?;
    if cached_sha != &reference.sha256 {
        return Err(format!(
            "validator receipt {} is referenced with conflicting hashes",
            path.display()
        ));
    }
    Ok(receipt)
}

fn validate_evidence_refs(evidence: &[EvidenceRef], label: &str) -> Result<(), String> {
    if evidence.len() > MAX_EVIDENCE_PER_ROW {
        return Err(format!(
            "{label} has {} evidence references; fixed limit is {MAX_EVIDENCE_PER_ROW}",
            evidence.len()
        ));
    }
    let mut seen = BTreeSet::new();
    for reference in evidence {
        validate_relative_path(&reference.path, "evidence receipt path")?;
        validate_sha256(&reference.sha256, "evidence receipt sha256")?;
        if !seen.insert(reference.path.as_str()) {
            return Err(format!(
                "{label} contains duplicate evidence path {:?}",
                reference.path
            ));
        }
    }
    Ok(())
}

fn sorted_unique_ids(values: &[String], label: &str) -> Result<BTreeSet<String>, String> {
    if values.is_empty() {
        return Err(format!("{label} is empty"));
    }
    let mut result = BTreeSet::new();
    let mut previous: Option<&str> = None;
    for value in values {
        validate_id(value, label)?;
        if previous.is_some_and(|prior| prior >= value.as_str()) {
            return Err(format!("{label} must be sorted and duplicate-free"));
        }
        previous = Some(value);
        result.insert(value.clone());
    }
    Ok(result)
}

fn validate_id(value: &str, label: &str) -> Result<(), String> {
    validate_text(value, label)?;
    if value.len() > 256
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-' | b'_'))
    {
        return Err(format!(
            "{label} must contain only ASCII letters, digits, `.`, `-`, or `_`: {value:?}"
        ));
    }
    Ok(())
}

fn validate_text(value: &str, label: &str) -> Result<(), String> {
    if value.trim().is_empty() {
        return Err(format!("{label} must not be empty"));
    }
    if value.len() > 16 * 1024 {
        return Err(format!("{label} exceeds the fixed 16 KiB limit"));
    }
    if value.chars().any(char::is_control) {
        return Err(format!("{label} contains control characters"));
    }
    Ok(())
}

fn validate_sha256(value: &str, label: &str) -> Result<(), String> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(format!(
            "{label} must be exactly 64 lowercase hexadecimal characters"
        ));
    }
    Ok(())
}

fn validate_relative_path(value: &str, label: &str) -> Result<(), String> {
    validate_text(value, label)?;
    let path = Path::new(value);
    if path.is_absolute() {
        return Err(format!("{label} must be relative to the manifest"));
    }
    let mut count = 0usize;
    for component in path.components() {
        match component {
            Component::Normal(segment) => {
                let segment = segment
                    .to_str()
                    .ok_or_else(|| format!("{label} is not valid UTF-8"))?;
                if segment.chars().any(char::is_control) {
                    return Err(format!("{label} contains control characters"));
                }
                count += 1;
            }
            _ => return Err(format!("{label} must be a normalized relative path")),
        }
    }
    if count == 0 {
        return Err(format!("{label} must not be empty"));
    }
    Ok(())
}

fn resolve_relative_evidence_path(base: &Path, value: &str) -> Result<PathBuf, String> {
    validate_relative_path(value, "evidence path")?;
    let base = fs::canonicalize(base).map_err(|error| {
        format!(
            "canonicalizing manifest directory {}: {error}",
            base.display()
        )
    })?;
    let joined = base.join(value);
    let metadata = fs::symlink_metadata(&joined)
        .map_err(|error| format!("inspecting evidence {}: {error}", joined.display()))?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
        return Err(format!(
            "evidence must be a non-symlink regular file: {}",
            joined.display()
        ));
    }
    let canonical = fs::canonicalize(&joined)
        .map_err(|error| format!("canonicalizing evidence {}: {error}", joined.display()))?;
    if !canonical.starts_with(&base) {
        return Err(format!(
            "evidence escapes the manifest directory: {}",
            canonical.display()
        ));
    }
    Ok(canonical)
}

fn validate_optional_artifact(
    artifact: Option<&Artifact>,
    base: &Path,
    label: &str,
) -> Result<(), String> {
    let Some(artifact) = artifact else {
        return Ok(());
    };
    validate_text(&artifact.path, &format!("{label} path"))?;
    validate_sha256(&artifact.sha256, &format!("{label} sha256"))?;
    verify_artifact(artifact, base, label)
}

fn verify_artifact(artifact: &Artifact, base: &Path, label: &str) -> Result<(), String> {
    let path = artifact_path(base, &artifact.path);
    let actual = sha256_file(&path, label)?;
    if actual != artifact.sha256 {
        return Err(format!(
            "{label} hash mismatch for {}: expected {}, got {actual}",
            path.display(),
            artifact.sha256
        ));
    }
    Ok(())
}

fn verify_reference_artifact(path: &str, expected_sha256: &str, label: &str) -> Result<(), String> {
    validate_sha256(expected_sha256, &format!("{label} sha256"))?;
    let path = Path::new(path);
    if !path.is_absolute() {
        return Err(format!("{label} path must be absolute"));
    }
    let actual = sha256_file(path, label)?;
    if actual != expected_sha256 {
        return Err(format!(
            "{label} hash mismatch for {}: expected {expected_sha256}, got {actual}",
            path.display()
        ));
    }
    Ok(())
}

fn artifact_path(base: &Path, value: &str) -> PathBuf {
    let path = Path::new(value);
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        base.join(path)
    }
}

fn sha256_file(path: &Path, label: &str) -> Result<String, String> {
    let metadata = fs::metadata(path)
        .map_err(|error| format!("inspecting {label} {}: {error}", path.display()))?;
    if !metadata.is_file() {
        return Err(format!("{label} is not a regular file: {}", path.display()));
    }
    let mut file = fs::File::open(path)
        .map_err(|error| format!("opening {label} {}: {error}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut buffer = vec![0u8; 64 * 1024];
    loop {
        let read = file
            .read(&mut buffer)
            .map_err(|error| format!("reading {label} {}: {error}", path.display()))?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

pub(crate) fn sha256_bytes(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}

fn read_bounded_bytes(
    path: &Path,
    limit: u64,
    label: &str,
    reject_symlink: bool,
) -> Result<Vec<u8>, String> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("inspecting {label} {}: {error}", path.display()))?;
    if (reject_symlink && metadata.file_type().is_symlink()) || !metadata.file_type().is_file() {
        return Err(format!(
            "{label} is not a permitted regular file: {}",
            path.display()
        ));
    }
    if metadata.len() > limit {
        return Err(format!(
            "{label} {} exceeds the fixed {limit}-byte limit",
            path.display()
        ));
    }
    let file = fs::File::open(path)
        .map_err(|error| format!("opening {label} {}: {error}", path.display()))?;
    let mut bytes = Vec::with_capacity(usize::try_from(metadata.len()).unwrap_or(0));
    file.take(limit.saturating_add(1))
        .read_to_end(&mut bytes)
        .map_err(|error| format!("reading {label} {}: {error}", path.display()))?;
    if bytes.len() as u64 > limit {
        return Err(format!(
            "{label} {} grew beyond the fixed {limit}-byte limit",
            path.display()
        ));
    }
    Ok(bytes)
}

fn usage() -> &'static str {
    "\
ay-z3-parity smtlib-conformance <command> [options]

COMMANDS:
  profile [--out <path>]
      Print the immutable SMT-LIB 2.7 + Z3 5.1.0 source and oracle profile, or
      publish it to a new file.

  init <manifest> [--campaign <id>] [--ay-executable <path>]
                  [--ay-shared-library <path>]
      Publish a new strict contract. It contains the closed 12-dimension
      definition, all 32 standard commands, nine official theories, all 25
      official logics, and explicit gaps for every missing inventory or
      validator. Paths stored for AY artifacts are interpreted relative to the
      manifest unless absolute. The output is create-new and crash-safe.

  attach <manifest> <validator-receipt> --out <new-manifest>
      Authenticate and replay one registered receipt, attach it to exactly the
      inventory or semantic rows it covers, clear only those proven gaps, and
      publish a new manifest without overwriting either input. The first
      semantic receipt binds the campaign-wide resource envelope; every later
      semantic receipt must match it. All three files must share one evidence
      directory so manifest-relative artifact identities remain stable.

  source-snapshot <language|registry> <git-checkout> --out <path>
      Retain the exact pinned UTF-8 source blobs in a content-addressed JSON
      bundle. Snapshot construction verifies checkout HEAD, selected paths,
      Git blob object IDs, byte sizes, and the profile's selection SHA-256.

  z3-source-snapshot <git-checkout> --out <path>
      Authenticate tag z3-5.1.0 and its exact commit, then retain the complete
      sorted 2,756-row path/Git-blob/size manifest plus only the 43 UTF-8 source
      blobs needed to replay shell, SMT2 command, and registry extraction.

  official-corpus-manifest <corpus-root> --archive-root <path>
                           --record-metadata <path> --out <path>
      Build an immutable external manifest for the complete SMT-LIB 2024
      non-incremental corpus from Zenodo record 11061097. Exactly all 84
      pinned archive rows and exact archive bytes, a deterministic archive
      member-to-materialization bijection, every .smt2 file hash, and every
      decision-query byte range, command hash, and query-prefix hash are
      required. Source and corpus artifacts remain external. The committed
      smoke corpus is deliberately rejected.

  run reference-inventory <manifest> --dimension <id> --receipt <path>
                          [--source-snapshot <path>]
      Run `builtin.reference-inventory.v1`. Source-backed lexical/grammar,
      command, logic, and theory inventories require their authenticated
      language or registry snapshot; contract-defined result-policy inventories
      are replayed from canonical rows. Coarse unresolved dimensions are
      rejected until expanded.

  run lexical-grammar <manifest> --receipt <path> --source-snapshot <path>
                      [--ay <path>] [--timeout <seconds>]
      Run `builtin.lexical-grammar.v1`. It authenticates all 45 normative
      lexical, term, and response productions and owns one source row, one
      positive witness, and one negative witness for each. Input negatives
      require exact positioned continued-execution recovery; response witnesses
      use closed recognizers over live AY output. All children are staged,
      hash-bound, sequential, and OOM-guarded.

  run logic-registry <manifest> --receipt <path> --source-snapshot <path>
                     [--ay <path>] [--timeout <seconds>]
      Run `builtin.logic-registry.v1`. It authenticates all 25 pinned logic
      declarations, owns every theories/language/extension/note field in an
      exact catalog, then runs positive and negative included-theory witnesses
      plus one rejection transcript for every cataloged excluded feature.
      Checks replay the exact catalog and live AY transcripts.

  run theory-registry <manifest> --receipt <path> --source-snapshot <path>
                      [--ay <path>] [--timeout <seconds>]
      Run `builtin.theory-registry.v1`. It authenticates all nine pinned
      non-draft theory declarations, owns every source field and all 123
      machine-readable plus 64 prose-described full signatures, then runs one
      positive typing, negative typing/index, and semantic transcript for each
      signature. Every child is staged and OOM-guarded; any skip, unknown,
      unsupported feature, timeout, or catalog drift leaves the receipt FAIL.

  run type-scope <manifest> --receipt <path> --source-snapshot <path>
                 [--ay <path>] [--timeout <seconds>]
      Run `builtin.type-scope.v1`. It authenticates a closed 32-row inventory
      of the SMT-LIB 2.7 sorting judgments, rank/arity rules, binders,
      declaration collisions, datatype/sort parameters, shadowing, and scope
      lifetimes. Every row has a positive and negative live AY transcript.

  run command-state-machine <manifest> --receipt <path>
                            --source-snapshot <path>
                            [--ay <path>] [--timeout <seconds>]
      Run `builtin.command-state-machine.v1`. It authenticates and exercises
      every one of the 32 commands in all four normative modes, plus closed
      state-effect rows for stack/reset behavior, query artifacts, options,
      channels, atomic recovery, poisoning, assumptions, and exit. Children
      are staged, hash-bound, sequential, and OOM-guarded.

  run standard-commands <manifest> --receipt <path> --source-snapshot <path>
                        [--ay <path>] [--timeout <seconds>]
      Run `builtin.standard-commands.v1` against a hash-authenticated private
      copy of the manifest-bound AY executable. It binds the exact 32 command
      productions from the pinned language snapshot to a closed, sorted
      positive/missing/trailing/malformed catalog, including explicitly owned
      Z3 5.1.0 arity extensions. Every child runs sequentially under one
      `_oom_guard.py` plan; checks re-derive pass/fail from raw transcripts and
      repeat the complete live run.

  run target-identity <manifest> --receipt <path> [--ay <path>] [--z3 <path>]
                      [--timeout <seconds>]
      Run the first built-in executable validator: exact CLI identity against
      the pinned Z3 5.1.0 binary and the manifest-bound AY executable. Z3 and AY
      run sequentially under one `_oom_guard.py` plan. The validator retains
      bounded stdout/stderr and publishes a hash-bound evidence receipt even
      when AY fails; any stale or forged version transcript remains a hard
      failure.

  run z3-abi-5.0 <manifest> --receipt <path> [--ay <path>]
                   [--timeout <seconds>]
      Run `builtin.z3-abi-5.0.v1` against authenticated private copies of the
      manifest-bound AY shared library and the profile-pinned Z3 5.1.0 shared
      library. The receipt requires live HEAD at origin/main and a clean AY
      build stamp for that exact full commit; unrelated caller-worktree edits
      do not taint detached clean-build evidence. It authenticates the exact
      11-header/805-declaration signature surface, requires all 807 exports and
      all 99 scoped observations, and emits one executed-call row plus one
      exhaustive semantic-contract row for every declaration. Current embedded
      probes authenticate 217/805 calls and 0/805 exhaustive contracts, so the
      full-ABI requirement remains red; all 588 missing calls have exact reason
      rows. Header and symbol resolution alone never prove implementation ABI
      behavior.

  run z3-behavioral <manifest> --receipt <path> --source-snapshot <path>
                    [--ay <path>] [--z3 <path>] [--timeout <seconds>]
      Run `builtin.z3-behavioral-transcripts-5.1.0.v1` against authenticated
      private copies of the manifest-bound AY executable and profile-pinned Z3
      5.1.0. It re-derives the exact 1,518-item observable manifest from the
      authenticated source snapshot and gives every command, tactic, probe,
      simplifier, parameter, parameter module, CLI option/help form, input mode,
      filename extension, declaration builtin, logic-recognizer literal,
      logic-strategy alias, information key, option key, and parser token
      exactly one behavioral owner. The 37 simplifiers and every safely tunable
      parameter require a distinguishing Z3 effect baseline; entries without a
      safe witness remain explicit failed rows.
      Catalog listing alone never counts as a semantic effect. Supplementary
      command/state/artifact, diagnostic, combinator, model/value-formatting,
      and phased live-stdin cases remain closed too. Structured comparators
      elide numeric telemetry only, retaining syntax, keys, ordering, channels,
      component names, and diagnostics.

  run z3-source-inventory <manifest> --receipt <path>
                          --source-snapshot <path> [--timeout <seconds>]
      Run `builtin.z3-source-inventory.v1` against the exact profile-pinned Z3
      executable under `_oom_guard.py`. The closed catalog binds all 2,756
      source-tree entries, 94 accepted SMT2 commands (86 live-registry plus
      eight parser-native-only names), 118 tactics, 42 probes, 37 simplifiers,
      678 parameters, 21 parameter modules, 33 source CLI options, 27 live help
      forms, nine input modes, 16 filename extensions, 323 declaration
      builtins, 24 logic-recognizer literals, 33 logic-strategy aliases, 11
      information keys, 20 option keys, and 22 parser tokens. This receipt
      establishes only the Z3 source/observable inventory; it makes no AY
      support claim.

  run z3-reference-inventory <manifest> --receipt <path>
                             --source-snapshot <path>
      Run `builtin.z3-reference-inventory.v1`, the specialized external-source
      ReferenceExtractor for `overlay.z3-5.1.0`. It binds the exact four overlay
      rows to the authenticated 2,756-file Z3 5.1.0 tree and retained source
      owners without claiming any AY behavior.

  run official-corpus-inventory <manifest> --receipt <path>
                                --corpus-manifest <path>
      Run `builtin.official-corpus-inventory.v1`, the specialized
      ReferenceExtractor for `coverage.corpus`. It binds the external immutable
      manifest to the exact corpus requirement and freshly rejects missing,
      unexpected, changed, symlinked, or query-drifted materialization rows.

  run official-corpus <manifest> --receipt <path> --results <path>
                      --corpus-manifest <path> [--ay <path>] [--z3 <path>]
                      [--timeout <seconds>]
      Run every immutable corpus file and decision query against authenticated
      AY and exact Z3 5.1.0 under the campaign's one-job `_oom_guard.py`
      envelope. AY additionally receives the planned `--memory` budget plus
      `--self-check --strict-proofs`. Exact ordered verdict parity, clean
      execution, and a second full archive/member/materialization closure scan
      are mandatory. This receipt does not independently certify models or
      proofs; the separately registered `results.sat-models` and
      `results.unsat-proofs` gates own those universal obligations.
      Per-file/per-query results remain in the content-addressed external
      results artifact; completion checks rerun the entire corpus. No
      multi-gigabyte corpus content is committed.

  run gate-integrity <manifest> --receipt <path>
      Run `builtin.gate-integrity.v1`: nineteen deterministic live mutations
      covering contract shrinkage/duplication/invention, profile and artifact
      drift, stale/foreign/unregistered evidence, truncated or duplicate case
      rows, aggregate spoofing, interrupted outcomes, and missing campaign
      bindings. Checks replay the mutation suite instead of trusting its JSON.

  run sat-models <manifest> --receipt <path> [--ay <path>]
                 [--timeout <seconds>]
      Run `builtin.sat-models.v1` against a hash-authenticated private copy of
      the manifest-bound AY executable with `--self-check`. The closed catalog
      covers plain, assumption, incremental, and optimization query epochs,
      representative model sorts, stale-artifact invalidation, and a
      CannotConfirm negative control that must fail closed to `unknown`.

  run unknown-policy <manifest> --receipt <path> [--ay <path>]
                     [--timeout <seconds>]
      Run `builtin.unknown-policy.v1` against a hash-authenticated private copy
      of the manifest-bound AY executable. The executable establishes live
      model, proof, core, unsat-assumption, and optimum artifacts, then checks
      canonical revocation for every closed Unknown reason. A paired retained-
      artifact negative control proves that stale authority is detected.

  run unsat-proofs <manifest> --receipt <path> [--ay <path>]
                   [--carcara <path>] [--timeout <seconds>]
      Run `builtin.unsat-proofs.v1`. Every exact authored fixture invokes a
      staged AY with `--strict-proofs --self-check --proof` and the planned
      `--memory` budget, retains the exact Alethe bytes, and replays them over
      the exact problem with strict Carcara 1.1.0 at commit 9a352ee. The
      checker is authenticated by version and SHA-256, retained as an
      AuxiliaryTool, staged for every run, and RSS-watchdog constrained. A
      deterministic corrupted-proof control and a foreign-problem control
      must both be rejected.

  check <manifest> [--audit-only | --require-complete] [--receipt <path>] [--json]
      Validate the strict schema, immutable profile, closed dimensions,
      requirement inventory digests, unique ownership, artifact hashes, and
      every referenced validator receipt. COMPLETION IS THE DEFAULT: ANY gap,
      incomplete reference inventory, failed or non-exhaustive evidence, skip,
      unknown, unavailable tool, timeout, memout, crash, missing artifact, or
      unassigned campaign exits non-zero. --require-complete is an explicit
      spelling of the default. --audit-only returns 0 for an honest incomplete
      contract and is deliberately required for that weaker automation mode.
      A check receipt is optional, create-new, and contains recomputed counts.

  receipt-check <manifest> <receipt>
                [--audit-only | --require-complete] [--json]
      Recompute the contract report and reject a stale, foreign, tampered, or
      aggregate-only check receipt. Completion is the default and an audit
      receipt is rejected unless --audit-only is explicit.

VALIDATOR RECEIPTS:
  Evidence paths are normalized, manifest-relative, non-symlink regular files
  using schema `ay-smtlib-validator-receipt/v2`. Each receipt binds one
  campaign, this exact profile, the dimension inventory digest, sorted covered
  requirement IDs, the validator implementation hash, AY artifact hashes, the
  exact Z3 5.1.0 binary and shared-library hashes when applicable,
  content-addressed replayable source snapshots and auxiliary checker binaries
  when used, source provenance, and an enforced resource envelope. A pass requires
  exhaustive=true, total>0, passed=total, and zero
  failed/skipped/unknown/timeout/memout/crash/unavailable cases.
  Validator IDs are a closed code registry, not an extension point. Registered
  implementations are `builtin.reference-inventory.v1`,
  `builtin.type-scope.v1`, `builtin.command-state-machine.v1`,
  `builtin.lexical-grammar.v1`, `builtin.logic-registry.v1`,
  `builtin.standard-commands.v1`,
  `builtin.theory-registry.v1`,
  `builtin.target-identity.v1`, `builtin.z3-abi-5.0.v1`,
  `builtin.z3-behavioral-transcripts-5.1.0.v1`,
  `builtin.z3-reference-inventory.v1`,
  `builtin.z3-source-inventory.v1`,
  `builtin.official-corpus-inventory.v1`,
  `builtin.official-corpus-z3-5.1.0.v1`,
  `builtin.gate-integrity.v1`, `builtin.sat-models.v1`,
  `builtin.unknown-policy.v1`, and
  `builtin.unsat-proofs.v1`. Checks replay
  them against private authenticated copies or live in-process mutations
  instead of trusting their JSON.
"
}

pub(crate) fn run(args: &[String]) -> i32 {
    if args
        .iter()
        .any(|arg| matches!(arg.as_str(), "-h" | "--help"))
    {
        print!("{}", usage());
        return 0;
    }
    let Some((command, rest)) = args.split_first() else {
        eprintln!("error: missing smtlib-conformance command\n\n{}", usage());
        return 2;
    };
    let result = match command.as_str() {
        "profile" => profile_command(rest),
        "init" => init_command(rest),
        "attach" => attach_command(rest),
        "source-snapshot" => reference_inventory::snapshot(rest),
        "official-corpus-manifest" => official_corpus::create_manifest(rest),
        "z3-source-snapshot" => z3_source_inventory::snapshot(rest),
        "run" => run_validator_command(rest),
        "check" => check_command(rest),
        "receipt-check" => receipt_check_command(rest),
        other => Err(format!("unknown smtlib-conformance command {other:?}")),
    };
    match result {
        Ok(code) => code,
        Err(error) => {
            eprintln!("error: {error}");
            1
        }
    }
}

fn profile_command(args: &[String]) -> Result<i32, String> {
    let output = match args {
        [] => None,
        [flag, path] if flag == "--out" => Some(PathBuf::from(path)),
        _ => {
            return Err(
                "usage: ay-z3-parity smtlib-conformance profile [--out <path>]".to_string(),
            );
        }
    };
    let bytes = pretty_json(&canonical_profile())?;
    if let Some(path) = output {
        atomic_write_new(&path, &bytes)?;
        println!("wrote {}", path.display());
    } else {
        print_utf8(&bytes)?;
    }
    Ok(0)
}

fn init_command(args: &[String]) -> Result<i32, String> {
    let mut output: Option<PathBuf> = None;
    let mut campaign = UNASSIGNED_CAMPAIGN.to_string();
    let mut ay_executable: Option<String> = None;
    let mut ay_shared_library: Option<String> = None;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--campaign" => {
                index += 1;
                campaign = args.get(index).ok_or("--campaign needs an id")?.clone();
            }
            "--ay-executable" => {
                index += 1;
                ay_executable = Some(
                    args.get(index)
                        .ok_or("--ay-executable needs a path")?
                        .clone(),
                );
            }
            "--ay-shared-library" => {
                index += 1;
                ay_shared_library = Some(
                    args.get(index)
                        .ok_or("--ay-shared-library needs a path")?
                        .clone(),
                );
            }
            flag if flag.starts_with("--") => return Err(format!("unknown init flag {flag:?}")),
            value => {
                if output.replace(PathBuf::from(value)).is_some() {
                    return Err("init takes exactly one manifest output path".to_string());
                }
            }
        }
        index += 1;
    }
    let output = output.ok_or("init needs a manifest output path")?;
    validate_id(&campaign, "campaign id")?;
    let base = output
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let subject = Subject {
        ay_executable: ay_executable
            .as_deref()
            .map(|path| artifact_from_path(path, base, "AY executable"))
            .transpose()?,
        ay_shared_library: ay_shared_library
            .as_deref()
            .map(|path| artifact_from_path(path, base, "AY shared library"))
            .transpose()?,
    };
    let mut contract = starter_contract(subject)?;
    contract.campaign_id = campaign;
    let bytes = pretty_json(&contract)?;
    atomic_write_new(&output, &bytes)?;
    println!(
        "wrote {} ({} dimensions, {} requirements, complete=false)",
        output.display(),
        contract.dimensions.len(),
        contract
            .dimensions
            .iter()
            .map(|dimension| dimension.requirements.len())
            .sum::<usize>()
    );
    Ok(0)
}

fn attach_command(args: &[String]) -> Result<i32, String> {
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
                return Err(format!("unknown attach flag {flag:?}"));
            }
            value => positionals.push(PathBuf::from(value)),
        }
        index += 1;
    }
    if positionals.len() != 2 {
        return Err(
            "usage: smtlib-conformance attach <manifest> <validator-receipt> --out <new-manifest>"
                .to_string(),
        );
    }
    let output = output.ok_or("attach requires --out <new-manifest>")?;
    let loaded = load_contract(&positionals[0])?;
    validate_contract(&loaded.contract, &loaded.base, ValidationMode::Audit)?;
    require_manifest_output_directory(&loaded.base, &output)?;

    let receipt_relative = future_relative_output(&loaded.base, &positionals[1])?;
    let receipt_path = resolve_relative_evidence_path(&loaded.base, &receipt_relative)?;
    let reference = EvidenceRef {
        path: receipt_relative,
        sha256: sha256_file(&receipt_path, "validator receipt")?,
    };
    let mut cache = ReceiptCache::default();
    let receipt = load_validator_receipt(&reference, &loaded.base, &mut cache)?.clone();

    let mut candidate = loaded.contract;
    let attached = attach_receipt_reference(&mut candidate, reference, &receipt)?;
    let report = validate_contract(&candidate, &loaded.base, ValidationMode::Audit)?;
    let bytes = pretty_json(&candidate)?;
    atomic_write_new(&output, &bytes)?;
    println!(
        "attached={} manifest={} complete={} validated={}/{} inventories={}/{}",
        attached,
        output.display(),
        report.complete,
        report.summary.validated_requirements,
        report.summary.requirement_count,
        report.summary.reference_complete_dimensions,
        report.summary.dimension_count,
    );
    Ok(0)
}

fn require_manifest_output_directory(base: &Path, output: &Path) -> Result<(), String> {
    let parent = output
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let canonical_parent = fs::canonicalize(parent).map_err(|error| {
        format!(
            "canonicalizing new manifest directory {}: {error}",
            parent.display()
        )
    })?;
    if canonical_parent != base {
        return Err(format!(
            "new manifest must stay in {} so existing relative evidence and artifact paths retain their identity",
            base.display()
        ));
    }
    Ok(())
}

fn attach_receipt_reference(
    contract: &mut Contract,
    reference: EvidenceRef,
    receipt: &ValidatorReceipt,
) -> Result<String, String> {
    if receipt.schema != VALIDATOR_RECEIPT_SCHEMA {
        return Err(format!(
            "validator receipt schema mismatch: expected {VALIDATOR_RECEIPT_SCHEMA}, got {:?}",
            receipt.schema
        ));
    }
    if receipt.campaign_id != contract.campaign_id {
        return Err(format!(
            "validator receipt belongs to campaign {:?}, not {:?}",
            receipt.campaign_id, contract.campaign_id
        ));
    }
    let dimension_index = contract
        .dimensions
        .iter()
        .position(|dimension| dimension.id == receipt.dimension_id)
        .ok_or_else(|| {
            format!(
                "validator receipt names unknown dimension {:?}",
                receipt.dimension_id
            )
        })?;

    if receipt.validator.kind == ValidatorKind::ReferenceExtractor {
        let dimension = &mut contract.dimensions[dimension_index];
        if dimension
            .inventory
            .evidence
            .iter()
            .any(|existing| existing.path == reference.path)
        {
            return Err(format!(
                "{} inventory already references {:?}",
                dimension.id, reference.path
            ));
        }
        dimension.inventory.evidence.push(reference);
        dimension
            .inventory
            .evidence
            .sort_by(|left, right| left.path.cmp(&right.path));
        dimension.inventory.gap = None;
        return Ok(format!("{} inventory", dimension.id));
    }

    let receipt_envelope = receipt
        .resource_envelope
        .as_deref()
        .ok_or("semantic validator receipt has no resource_envelope")?;
    validate_resource_envelope(receipt_envelope)?;
    match contract.resource_envelope.as_deref() {
        Some(expected) if expected != receipt_envelope => {
            return Err(format!(
                "semantic receipt envelope differs from the campaign: expected {expected:?}, got {receipt_envelope:?}"
            ));
        }
        Some(_) => {}
        None => contract.resource_envelope = Some(receipt_envelope.to_string()),
    }

    let dimension = &mut contract.dimensions[dimension_index];
    let ids = sorted_unique_ids(&receipt.requirement_ids, "receipt requirement_ids")?;
    let mut attached = Vec::with_capacity(ids.len());
    for id in ids {
        let requirement = dimension
            .requirements
            .iter_mut()
            .find(|requirement| requirement.id == id)
            .ok_or_else(|| {
                format!(
                    "validator receipt names unknown requirement {id:?} in {}",
                    dimension.id
                )
            })?;
        if requirement
            .evidence
            .iter()
            .any(|existing| existing.path == reference.path)
        {
            return Err(format!(
                "requirement {id} already references {:?}",
                reference.path
            ));
        }
        requirement.evidence.push(reference.clone());
        requirement
            .evidence
            .sort_by(|left, right| left.path.cmp(&right.path));
        requirement.gap = None;
        attached.push(id);
    }
    Ok(attached.join(","))
}

fn run_validator_command(args: &[String]) -> Result<i32, String> {
    let Some((validator, rest)) = args.split_first() else {
        return Err(
            "run needs a validator name (`reference-inventory`, `lexical-grammar`, `logic-registry`, `standard-commands`, `theory-registry`, `type-scope`, `command-state-machine`, `target-identity`, `z3-abi-5.0`, `z3-behavioral`, `z3-reference-inventory`, `z3-source-inventory`, `official-corpus-inventory`, `official-corpus`, `gate-integrity`, `sat-models`, `unknown-policy`, or `unsat-proofs`)"
                .to_string(),
        );
    };
    match validator.as_str() {
        "reference-inventory" => reference_inventory::run(rest),
        "lexical-grammar" => lexical_grammar::run(rest),
        "logic-registry" => logic_registry::run(rest),
        "standard-commands" => standard_commands::run(rest),
        "theory-registry" => theory_registry::run(rest),
        "type-scope" => language_semantics::run_type_scope(rest),
        "command-state-machine" => language_semantics::run_command_state(rest),
        "target-identity" => run_target_identity(rest),
        "z3-abi-5.0" => run_z3_abi(rest),
        "z3-behavioral" => z3_behavioral::run(rest),
        "z3-reference-inventory" => z3_source_inventory::run_reference(rest),
        "z3-source-inventory" => z3_source_inventory::run(rest),
        "official-corpus-inventory" => official_corpus::run_inventory(rest),
        "official-corpus" => official_corpus::run(rest),
        "z3-behavioral-stream-driver" => z3_behavioral::run_stream_driver(rest),
        "gate-integrity" => gate_integrity::run(rest),
        "sat-models" => sat_models::run(rest),
        "unknown-policy" => unknown_policy::run(rest),
        "unsat-proofs" => unsat_proofs::run(rest),
        other => Err(format!("unknown built-in validator {other:?}")),
    }
}

struct StagedExecutable {
    _directory: tempfile::TempDir,
    path: PathBuf,
}

struct StagedLibrary {
    _directory: tempfile::TempDir,
    path: PathBuf,
}

fn stage_authenticated_executable(
    source: &Path,
    expected_sha256: &str,
    label: &str,
) -> Result<StagedExecutable, String> {
    validate_sha256(expected_sha256, &format!("{label} expected sha256"))?;
    let metadata = fs::metadata(source)
        .map_err(|error| format!("inspecting {label} {}: {error}", source.display()))?;
    if !metadata.is_file() {
        return Err(format!(
            "{label} is not a regular file: {}",
            source.display()
        ));
    }
    let directory = tempfile::Builder::new()
        .prefix("ay-smtlib-authenticated-")
        .tempdir()
        .map_err(|error| format!("creating private staging directory for {label}: {error}"))?;
    let staged = directory.path().join("program");
    fs::copy(source, &staged).map_err(|error| {
        format!(
            "staging authenticated {label} {} at {}: {error}",
            source.display(),
            staged.display()
        )
    })?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        fs::set_permissions(&staged, fs::Permissions::from_mode(0o500)).map_err(|error| {
            format!(
                "securing staged {label} executable {}: {error}",
                staged.display()
            )
        })?;
    }
    let actual_sha256 = sha256_file(&staged, &format!("staged {label}"))?;
    if actual_sha256 != expected_sha256 {
        return Err(format!(
            "selected {label} bytes do not match the authenticated artifact: expected {expected_sha256}, got {actual_sha256}"
        ));
    }
    fs::File::open(&staged)
        .and_then(|file| file.sync_all())
        .map_err(|error| format!("syncing staged {label} {}: {error}", staged.display()))?;
    Ok(StagedExecutable {
        _directory: directory,
        path: staged,
    })
}

fn stage_authenticated_library(
    source: &Path,
    expected_sha256: &str,
    label: &str,
) -> Result<StagedLibrary, String> {
    validate_sha256(expected_sha256, &format!("{label} expected sha256"))?;
    let metadata = fs::metadata(source)
        .map_err(|error| format!("inspecting {label} {}: {error}", source.display()))?;
    if !metadata.is_file() {
        return Err(format!(
            "{label} is not a regular file: {}",
            source.display()
        ));
    }
    let file_name = source
        .file_name()
        .ok_or_else(|| format!("{label} path has no file name: {}", source.display()))?;
    let directory = tempfile::Builder::new()
        .prefix("ay-smtlib-authenticated-library-")
        .tempdir()
        .map_err(|error| format!("creating private staging directory for {label}: {error}"))?;
    let staged = directory.path().join(file_name);
    fs::copy(source, &staged).map_err(|error| {
        format!(
            "staging authenticated {label} {} at {}: {error}",
            source.display(),
            staged.display()
        )
    })?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        fs::set_permissions(&staged, fs::Permissions::from_mode(0o400)).map_err(|error| {
            format!(
                "securing staged {label} shared library {}: {error}",
                staged.display()
            )
        })?;
    }
    let actual_sha256 = sha256_file(&staged, &format!("staged {label}"))?;
    if actual_sha256 != expected_sha256 {
        return Err(format!(
            "selected {label} bytes do not match the authenticated artifact: expected {expected_sha256}, got {actual_sha256}"
        ));
    }
    fs::File::open(&staged)
        .and_then(|file| file.sync_all())
        .map_err(|error| format!("syncing staged {label} {}: {error}", staged.display()))?;
    Ok(StagedLibrary {
        _directory: directory,
        path: staged,
    })
}

#[derive(Debug, Eq, PartialEq)]
struct IdentityExecution {
    ay_sha256: String,
    z3_sha256: String,
    resource_envelope: String,
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

fn validate_target_identity_replay(
    receipt: &ValidatorReceipt,
    live: &IdentityExecution,
) -> Result<(), String> {
    if receipt.result != live.result
        || receipt.cases != live.cases
        || receipt.case_results != live.case_results
    {
        return Err(
            "builtin.target-identity.v1 receipt does not match a fresh authenticated live replay"
                .to_string(),
        );
    }
    Ok(())
}

fn execute_target_identity(
    contract: &Contract,
    ay_source: &Path,
    z3_source: &Path,
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<IdentityExecution, String> {
    if timeout.is_zero() || timeout > Duration::from_hours(1) {
        return Err("target-identity timeout must be between 1ns and 3600 seconds".to_string());
    }
    let subject_ay = contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("target-identity requires subject.ay_executable")?;
    let expected_z3_sha = &contract.profile.z3_overlay.reference_executable.sha256;
    let staged_ay = stage_authenticated_executable(ay_source, &subject_ay.sha256, "AY executable")?;
    let staged_z3 =
        stage_authenticated_executable(z3_source, expected_z3_sha, "Z3 5.1.0 executable")?;

    let repo_root = locate_repo_root()?;
    let resources = PlannedResources::plan(
        &repo_root,
        1,
        "ay-z3-parity smtlib-conformance target-identity",
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
                "live target-identity replay resource envelope drift: expected {expected:?}, got {resource_envelope:?}"
            ));
        }
    }

    let input = b"(get-info :name)\n(get-info :version)\n(exit)\n";
    let expected_stdout = "(:name \"Z3\")\n(:version \"5.1.0\")\n";

    // Keep oracle and subject sequential: two simultaneous children would
    // exceed the single planner-admitted slot.
    let z3_output = resources
        .run_external_transcript(
            &staged_z3.path,
            ["-in"],
            input,
            timeout,
            "SMT-LIB target identity: Z3 5.1.0",
        )
        .map_err(|error| error.to_string())?;
    let ay_output = resources
        .run_external_transcript(
            &staged_ay.path,
            ["--z3-mode", "--quiet", "-in"],
            input,
            timeout,
            "SMT-LIB target identity: AY",
        )
        .map_err(|error| error.to_string())?;
    let post_ay_sha = sha256_file(&staged_ay.path, "staged AY after identity run")?;
    let post_z3_sha = sha256_file(&staged_z3.path, "staged Z3 after identity run")?;
    if post_ay_sha != subject_ay.sha256 || post_z3_sha != *expected_z3_sha {
        return Err(
            "authenticated AY or Z3 staging bytes changed during transcript execution".to_string(),
        );
    }

    let mut case_results = vec![
        transcript_case(
            "ay.identity",
            input,
            expected_stdout,
            ay_output,
            "AY --z3-mode must report the exact pinned Z3 identity",
        ),
        transcript_case(
            "z3.identity",
            input,
            expected_stdout,
            z3_output,
            "the authenticated oracle must report its pinned identity",
        ),
    ];
    case_results.sort_by(|left, right| left.id.cmp(&right.id));
    let cases = case_counts_from_rows(&case_results)?;
    let result = overall_validator_result(&case_results);
    Ok(IdentityExecution {
        ay_sha256: subject_ay.sha256.clone(),
        z3_sha256: expected_z3_sha.clone(),
        resource_envelope,
        result,
        cases,
        case_results,
    })
}

fn replay_target_identity_receipt(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    let envelope = receipt
        .resource_envelope
        .as_deref()
        .ok_or("target-identity receipt has no resource envelope")?;
    let parsed = parse_resource_envelope(envelope)?;
    if parsed.jobs != 1 {
        return Err("target-identity receipts require a one-job resource envelope".to_string());
    }
    let subject = context
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("target-identity replay requires subject.ay_executable")?;
    let ay = artifact_path(context.manifest_dir, &subject.path);
    let z3 = PathBuf::from(
        &context
            .contract
            .profile
            .z3_overlay
            .reference_executable
            .path,
    );
    let live = execute_target_identity(context.contract, &ay, &z3, parsed.timeout, Some(envelope))?;
    validate_target_identity_replay(receipt, &live)
}

fn run_target_identity(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut ay_override: Option<PathBuf> = None;
    let mut z3_override: Option<PathBuf> = None;
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
            "--z3" => {
                index += 1;
                z3_override = Some(PathBuf::from(args.get(index).ok_or("--z3 needs a path")?));
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
                return Err(format!("unknown target-identity flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("target-identity takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }
    let manifest = manifest.ok_or("target-identity needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("target-identity requires --receipt <path>")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let subject_ay = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("target-identity requires subject.ay_executable")?;
    let ay = ay_override.unwrap_or_else(|| artifact_path(&loaded.base, &subject_ay.path));
    let z3 = z3_override.unwrap_or_else(|| {
        PathBuf::from(&loaded.contract.profile.z3_overlay.reference_executable.path)
    });
    let target_receipt_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let current_exe =
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?;
    let current_exe = fs::canonicalize(&current_exe).map_err(|error| {
        format!(
            "canonicalizing parity executable {}: {error}",
            current_exe.display()
        )
    })?;
    let validator_path = current_exe
        .to_str()
        .ok_or("parity executable path is not UTF-8")?
        .to_string();
    let validator_sha = sha256_file(&current_exe, "parity validator")?;
    let timeout = Duration::from_secs(timeout_secs);
    let execution = execute_target_identity(&loaded.contract, &ay, &z3, timeout, None)?;
    let requirement_id = "overlay.z3-5.1.0.target-identity".to_string();
    let overlay = loaded
        .contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == "overlay.z3-5.1.0")
        .ok_or("closed overlay dimension is missing")?;
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: overlay.id.clone(),
        requirement_ids: vec![requirement_id],
        inventory_sha256: overlay.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: "builtin.target-identity.v1".to_string(),
            kind: ValidatorKind::Z3Differential,
            path: validator_path,
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
        reference_inputs: Vec::new(),
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
        "target-identity={} receipt={} sha256={}",
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        target_receipt_relative,
        receipt_sha
    );
    println!(
        "attach to overlay.z3-5.1.0.target-identity: \
         {{\"path\":\"{target_receipt_relative}\",\"sha256\":\"{receipt_sha}\"}}"
    );
    println!(
        "set contract.resource_envelope to {:?} before attaching semantic evidence",
        receipt
            .resource_envelope
            .as_deref()
            .unwrap_or("<missing-envelope>")
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
struct AbiExecution {
    ay_sha256: String,
    z3_sha256: String,
    source_provenance: SourceProvenance,
    resource_envelope: String,
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

#[derive(Debug)]
struct AbiProbeCapture {
    observation: Option<crate::z3_abi_500::LibraryObservation>,
    category: &'static str,
    outcome: ValidatorCaseOutcome,
    exit_code: Option<i32>,
    process: ProcessObservation,
}

#[derive(Debug)]
struct AbiStockCProbeCapture {
    id: String,
    category: &'static str,
    outcome: ValidatorCaseOutcome,
    exit_code: Option<i32>,
    process: ProcessObservation,
}

#[derive(Clone, Copy)]
enum AbiProbeStderrPolicy {
    Empty,
    AyFiniteSetModelDiagnostics,
}

const ABI_CHILD_JSON: &str = "authenticated-json";
const ABI_CHILD_JSON_WITH_AY_DIAGNOSTICS: &str =
    "authenticated-json;model-unconfirmed=#as-array-ext:4";
const ABI_STOCK_C_EXACT_TRANSCRIPT: &str = "authenticated-exact-transcript";
const AY_ABI_DIAGNOSTIC_COUNT: usize = 4;

fn abi_child_expectation(id: &str) -> &'static str {
    match id {
        "abi.child.ay" => {
            "guarded authenticated probe child returns canonical JSON with exit 0 and exactly four closed #as-array-ext MODEL-UNCONFIRMED diagnostics"
        }
        "abi.child.z3" => {
            "guarded authenticated probe child returns canonical JSON with exit 0 and empty stderr"
        }
        _ => "guarded authenticated probe child has an unknown subject",
    }
}

fn abi_stock_c_expectation() -> &'static str {
    "byte-authenticated stock z3.h consumer compiles, binds the authenticated library, and exits 0 with its exact executed-call inventory and empty stderr"
}

fn abi_callability_coverage_expectation() -> &'static str {
    "all 805 public Z3 5.1.0 C declarations have an authenticated executed-call marker"
}

fn abi_callability_expectation() -> &'static str {
    "at least one authenticated Z3 5.1.0/AY call executed without crash or marker omission"
}

fn abi_semantic_contract_coverage_expectation() -> &'static str {
    "all 805 public Z3 5.1.0 C declarations have an authenticated exhaustive semantic-contract differential"
}

fn abi_semantic_contract_expectation() -> &'static str {
    "authenticated exhaustive Z3 5.1.0/AY input, state, output, and error-contract differential passed"
}

fn is_expected_ay_abi_stderr(stderr: &[u8]) -> bool {
    const PREFIX: &str = "c !! MODEL-UNCONFIRMED [UNCONFIRMED/published] \
        (not a refutation — see [AY SOUNDNESS GATE] for caught invalid models) \
        model validation incomplete: SmtGroundAssertion: Assertion ";
    const REQUIRED_DETAIL: &str =
        "function-backed array equality could not be independently validated (#as-array-ext)";

    let Ok(text) = std::str::from_utf8(stderr) else {
        return false;
    };
    text.ends_with('\n')
        && text.lines().count() == AY_ABI_DIAGNOSTIC_COUNT
        && text.lines().all(|line| {
            line.len() <= 4096
                && line.starts_with(PREFIX)
                && line.ends_with(REQUIRED_DETAIL)
                && !line.chars().any(char::is_control)
        })
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct GitMainState {
    commit: String,
    origin_main_commit: String,
}

struct AbiCaseBinding<'a> {
    profile_sha256: &'a str,
    inventory_sha256: &'a str,
    validator_sha256: &'a str,
    ay_sha256: &'a str,
    z3_sha256: &'a str,
    source: &'a SourceProvenance,
    resource_envelope: &'a str,
}

impl AbiCaseBinding<'_> {
    fn input_sha256(&self, case_id: &str) -> String {
        sha256_bytes(
            format!(
                "builtin.z3-abi-5.0.v1\nprofile={}\ninventory={}\nvalidator={}\nay={}\nz3={}\nsource_commit={}\norigin_main={}\nsource_clean={}\nbuild_stamp={}\nresource={}\ncase={case_id}\n",
                self.profile_sha256,
                self.inventory_sha256,
                self.validator_sha256,
                self.ay_sha256,
                self.z3_sha256,
                self.source.source_commit,
                self.source.origin_main_commit,
                self.source.source_clean,
                self.source.ay_shared_library_build_stamp,
                self.resource_envelope,
            )
            .as_bytes(),
        )
    }
}

fn run_abi_probe_child(
    resources: &PlannedResources,
    validator: &Path,
    library: &Path,
    required_symbols: &[u8],
    timeout: Duration,
    label: &str,
    stderr_policy: AbiProbeStderrPolicy,
) -> Result<AbiProbeCapture, String> {
    let output = resources
        .run_external_transcript_scrubbed(
            validator,
            [std::ffi::OsStr::new("z3-abi-probe"), library.as_os_str()],
            required_symbols,
            timeout,
            label,
        )
        .map_err(|error| error.to_string())?;
    let exit_code = output.status.as_ref().and_then(|status| status.code());
    let process = ProcessObservation {
        stdin_complete: output.stdin_complete,
        timed_out: output.timed_out,
        memout: output.memout,
        stdout_truncated: output.stdout_truncated,
        stderr_truncated: output.stderr_truncated,
    };
    if output.memout {
        return Ok(AbiProbeCapture {
            observation: None,
            category: "memout",
            outcome: ValidatorCaseOutcome::Memout,
            exit_code,
            process,
        });
    }
    if output.timed_out {
        return Ok(AbiProbeCapture {
            observation: None,
            category: "timeout",
            outcome: ValidatorCaseOutcome::Timeout,
            exit_code,
            process,
        });
    }
    if !output.stdin_complete || output.stdout_truncated || output.stderr_truncated {
        return Ok(AbiProbeCapture {
            observation: None,
            category: "incomplete-or-truncated",
            outcome: ValidatorCaseOutcome::Fail,
            exit_code,
            process,
        });
    }
    if !output.status.is_some_and(|status| status.success()) {
        return Ok(AbiProbeCapture {
            observation: None,
            category: "crash-or-nonzero",
            outcome: ValidatorCaseOutcome::Crash,
            exit_code,
            process,
        });
    }
    let category = match stderr_policy {
        AbiProbeStderrPolicy::Empty if output.stderr.is_empty() => ABI_CHILD_JSON,
        AbiProbeStderrPolicy::AyFiniteSetModelDiagnostics
            if is_expected_ay_abi_stderr(&output.stderr) =>
        {
            ABI_CHILD_JSON_WITH_AY_DIAGNOSTICS
        }
        AbiProbeStderrPolicy::AyFiniteSetModelDiagnostics if output.stderr.is_empty() => {
            return Ok(AbiProbeCapture {
                observation: None,
                category: "missing-expected-stderr",
                outcome: ValidatorCaseOutcome::Fail,
                exit_code,
                process,
            });
        }
        _ => {
            return Ok(AbiProbeCapture {
                observation: None,
                category: "unexpected-stderr",
                outcome: ValidatorCaseOutcome::Fail,
                exit_code,
                process,
            });
        }
    };
    let observation =
        serde_json::from_slice::<crate::z3_abi_500::LibraryObservation>(&output.stdout);
    match observation {
        Ok(observation) => Ok(AbiProbeCapture {
            observation: Some(observation),
            category,
            outcome: ValidatorCaseOutcome::Pass,
            exit_code,
            process,
        }),
        Err(_) => Ok(AbiProbeCapture {
            observation: None,
            category: "invalid-json",
            outcome: ValidatorCaseOutcome::Fail,
            exit_code,
            process,
        }),
    }
}

fn scrub_stock_c_compile_environment(command: &mut Command) {
    for variable in [
        "CPATH",
        "C_INCLUDE_PATH",
        "CPLUS_INCLUDE_PATH",
        "DYLD_FRAMEWORK_PATH",
        "DYLD_FALLBACK_FRAMEWORK_PATH",
        "DYLD_FALLBACK_LIBRARY_PATH",
        "DYLD_IMAGE_SUFFIX",
        "DYLD_INSERT_LIBRARIES",
        "DYLD_LIBRARY_PATH",
        "DYLD_ROOT_PATH",
        "DYLD_VERSIONED_FRAMEWORK_PATH",
        "DYLD_VERSIONED_LIBRARY_PATH",
        "GCC_EXEC_PREFIX",
        "LD_AUDIT",
        "LD_DEBUG",
        "LD_LIBRARY_PATH",
        "LD_PRELOAD",
        "LD_PROFILE",
        "LIBRARY_PATH",
        "LIBPATH",
        "SHLIB_PATH",
    ] {
        command.env_remove(variable);
    }
}

fn write_stock_c_probe_inputs(directory: &Path) -> Result<(), String> {
    for (name, bytes) in crate::z3_abi_500::public_header_files() {
        fs::write(directory.join(name), bytes)
            .map_err(|error| format!("writing authenticated stock C header {name}: {error}"))?;
    }
    for probe in crate::z3_abi_500::stock_c_probes() {
        fs::write(directory.join(format!("{}.c", probe.id)), probe.source).map_err(|error| {
            format!(
                "writing authenticated stock C probe source {}: {error}",
                probe.id
            )
        })?;
    }
    Ok(())
}

#[cfg(target_os = "macos")]
fn rebind_stock_c_library(binary: &Path, library: &Path) -> Result<(), String> {
    let library = fs::canonicalize(library).map_err(|error| {
        format!(
            "canonicalizing authenticated stock C library {}: {error}",
            library.display()
        )
    })?;
    let file_name = library.file_name().ok_or_else(|| {
        format!(
            "authenticated stock C library has no file name: {}",
            library.display()
        )
    })?;
    let output = Command::new("/usr/bin/otool")
        .arg("-L")
        .arg(binary)
        .output()
        .map_err(|error| format!("inspecting stock C consumer load commands: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "inspecting stock C consumer load commands failed with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let stdout = std::str::from_utf8(&output.stdout)
        .map_err(|error| format!("stock C consumer load commands are not UTF-8: {error}"))?;
    let dependency = stdout
        .lines()
        .skip(1)
        .filter_map(|line| line.split_whitespace().next())
        .find(|dependency| Path::new(dependency).file_name() == Some(file_name))
        .ok_or_else(|| {
            format!(
                "stock C consumer has no load command for {}",
                library.display()
            )
        })?;
    let output = Command::new("/usr/bin/install_name_tool")
        .arg("-change")
        .arg(dependency)
        .arg(&library)
        .arg(binary)
        .output()
        .map_err(|error| format!("rebinding authenticated stock C library: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "rebinding authenticated stock C library failed with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let output = Command::new("/usr/bin/otool")
        .arg("-L")
        .arg(binary)
        .output()
        .map_err(|error| format!("verifying rebound stock C load command: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "verifying rebound stock C load command failed with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let stdout = std::str::from_utf8(&output.stdout)
        .map_err(|error| format!("rebound stock C load commands are not UTF-8: {error}"))?;
    let rebound_dependency = stdout
        .lines()
        .skip(1)
        .filter_map(|line| line.split_whitespace().next())
        .find(|dependency| Path::new(dependency).file_name() == Some(file_name));
    if rebound_dependency != Some(library.to_string_lossy().as_ref()) {
        return Err(format!(
            "stock C consumer load command did not bind exactly to {}: {:?}",
            library.display(),
            rebound_dependency
        ));
    }
    Ok(())
}

#[cfg(not(target_os = "macos"))]
fn rebind_stock_c_library(_binary: &Path, _library: &Path) -> Result<(), String> {
    Ok(())
}

fn compile_stock_c_probe(
    directory: &Path,
    probe: &crate::z3_abi_500::StockCProbe,
    subject: &str,
    library: &Path,
) -> Result<PathBuf, String> {
    let source = directory.join(format!("{}.c", probe.id));
    let binary = directory.join(format!("{}-{subject}", probe.id));
    let library_directory = library.parent().ok_or_else(|| {
        format!(
            "authenticated {subject} library has no parent: {}",
            library.display()
        )
    })?;
    #[cfg(target_os = "macos")]
    let compiler = "/usr/bin/clang";
    #[cfg(not(target_os = "macos"))]
    let compiler = "/usr/bin/cc";
    let mut command = Command::new(compiler);
    scrub_stock_c_compile_environment(&mut command);
    command
        .arg("-std=c11")
        .arg("-Wall")
        .arg("-Wextra")
        .arg("-Werror")
        .arg("-I")
        .arg(directory)
        .arg(&source)
        .arg(library)
        .arg("-o")
        .arg(&binary);
    #[cfg(target_os = "macos")]
    command
        .arg(format!("-Wl,-rpath,{}", library_directory.display()))
        .arg("-Wl,-headerpad_max_install_names");
    #[cfg(target_os = "linux")]
    command
        .arg(format!(
            "-Wl,--disable-new-dtags,-rpath,{}",
            library_directory.display()
        ))
        .arg("-ldl");
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    command.arg(format!("-Wl,-rpath,{}", library_directory.display()));
    let output = command.output().map_err(|error| {
        format!(
            "compiling stock C probe {} for {subject}: {error}",
            probe.id
        )
    })?;
    if !output.status.success() {
        return Err(format!(
            "compiling stock C probe {} for {subject} failed with {}: {}",
            probe.id,
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    rebind_stock_c_library(&binary, library)?;
    Ok(binary)
}

fn run_stock_c_probe_child(
    resources: &PlannedResources,
    binary: &Path,
    library: &Path,
    id: String,
    expected_stdout: &[u8],
    timeout: Duration,
) -> Result<AbiStockCProbeCapture, String> {
    let library = fs::canonicalize(library).map_err(|error| {
        format!(
            "canonicalizing authenticated stock C runtime library {}: {error}",
            library.display()
        )
    })?;
    let output = resources
        .run_external_transcript_scrubbed(binary, [&library], b"", timeout, &id)
        .map_err(|error| error.to_string())?;
    let exit_code = output.status.as_ref().and_then(|status| status.code());
    let process = ProcessObservation {
        stdin_complete: output.stdin_complete,
        timed_out: output.timed_out,
        memout: output.memout,
        stdout_truncated: output.stdout_truncated,
        stderr_truncated: output.stderr_truncated,
    };
    let (category, outcome) = if output.memout {
        ("memout", ValidatorCaseOutcome::Memout)
    } else if output.timed_out {
        ("timeout", ValidatorCaseOutcome::Timeout)
    } else if !output.stdin_complete || output.stdout_truncated || output.stderr_truncated {
        ("incomplete-or-truncated", ValidatorCaseOutcome::Fail)
    } else if !output.status.is_some_and(|status| status.success()) {
        ("crash-or-nonzero", ValidatorCaseOutcome::Crash)
    } else if !output.stderr.is_empty() {
        ("unexpected-stderr", ValidatorCaseOutcome::Fail)
    } else if output.stdout != expected_stdout {
        ("unexpected-stdout", ValidatorCaseOutcome::Fail)
    } else {
        (ABI_STOCK_C_EXACT_TRANSCRIPT, ValidatorCaseOutcome::Pass)
    };
    Ok(AbiStockCProbeCapture {
        id,
        category,
        outcome,
        exit_code,
        process,
    })
}

fn run_stock_c_probes(
    resources: &PlannedResources,
    ay_library: &Path,
    z3_library: &Path,
    timeout: Duration,
) -> Result<Vec<AbiStockCProbeCapture>, String> {
    let directory = tempfile::Builder::new()
        .prefix("ay-z3-stock-c-")
        .tempdir()
        .map_err(|error| format!("creating private stock C probe directory: {error}"))?;
    write_stock_c_probe_inputs(directory.path())?;
    let mut captures = Vec::new();
    for probe in crate::z3_abi_500::stock_c_probes() {
        for (subject, library) in [("ay", ay_library), ("z3", z3_library)] {
            let binary = compile_stock_c_probe(directory.path(), &probe, subject, library)?;
            captures.push(run_stock_c_probe_child(
                resources,
                &binary,
                library,
                format!("abi.stock-c.{}.{subject}", probe.id),
                &crate::z3_abi_500::stock_c_probe_expected_stdout(&probe),
                timeout,
            )?);
        }
    }
    Ok(captures)
}

fn required_symbol_manifest_bytes(symbols: &[String]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for symbol in symbols {
        bytes.extend_from_slice(symbol.as_bytes());
        bytes.push(b'\n');
    }
    bytes
}

fn validate_probe_observation_shape(
    observation: &crate::z3_abi_500::LibraryObservation,
    label: &str,
) -> Result<(), String> {
    let sorted_unique = |values: &[String], field: &str| -> Result<(), String> {
        let mut previous: Option<&str> = None;
        for value in values {
            if value.len() <= 3
                || !value.starts_with("Z3_")
                || !value[3..]
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
                || previous.is_some_and(|prior| prior >= value.as_str())
            {
                return Err(format!(
                    "{label} {field} is not a sorted duplicate-free Z3 symbol list"
                ));
            }
            previous = Some(value);
        }
        Ok(())
    };
    sorted_unique(&observation.exported_z3_symbols, "export inventory")?;
    sorted_unique(&observation.required_resolvable_symbols, "dlsym inventory")?;
    let expected_probe_ids = crate::z3_abi_500::expected_probe_values()
        .into_keys()
        .collect::<BTreeSet<_>>();
    let observed_probe_ids = observation.probes.keys().cloned().collect::<BTreeSet<_>>();
    if observed_probe_ids != expected_probe_ids {
        return Err(format!("{label} finite-set probe inventory is not exact"));
    }
    Ok(())
}

fn command_stdout(repo: &Path, args: &[&str], label: &str) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .map_err(|error| format!("running git for {label}: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "git {label} failed with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let value = std::str::from_utf8(&output.stdout)
        .map_err(|error| format!("git {label} output is not UTF-8: {error}"))?
        .trim()
        .to_string();
    Ok(value)
}

fn current_git_main_state(repo: &Path) -> Result<GitMainState, String> {
    let commit = command_stdout(repo, &["rev-parse", "HEAD"], "HEAD")?;
    validate_full_commit(&commit, "git HEAD")?;
    let origin_main_commit = command_stdout(
        repo,
        &["rev-parse", "--verify", "refs/remotes/origin/main"],
        "origin/main",
    )?;
    validate_full_commit(&origin_main_commit, "git origin/main")?;
    Ok(GitMainState {
        commit,
        origin_main_commit,
    })
}

fn validate_current_main_state(state: &GitMainState) -> Result<(), String> {
    if state.commit != state.origin_main_commit {
        return Err(format!(
            "Z3 ABI evidence HEAD {} is not current local origin/main {}",
            state.commit, state.origin_main_commit
        ));
    }
    Ok(())
}

fn validate_full_commit(value: &str, label: &str) -> Result<(), String> {
    if value.len() != 40 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(format!("{label} is not a full 40-hex commit: {value:?}"));
    }
    Ok(())
}

fn build_stamp_commit(stamp: &str) -> Option<&str> {
    let before_time = stamp.split_once('@')?.0;
    before_time.rsplit_once('.').map(|(_, commit)| commit)
}

fn source_provenance(
    state: &GitMainState,
    ay_build_stamp: &str,
) -> Result<SourceProvenance, String> {
    validate_current_main_state(state)?;
    validate_text(ay_build_stamp, "AY shared-library build stamp")?;
    let build_commit = build_stamp_commit(ay_build_stamp)
        .ok_or("AY shared-library build stamp has no source commit")?;
    if build_commit.ends_with("-dirty") {
        return Err("AY shared-library build stamp is dirty".to_string());
    }
    validate_full_commit(build_commit, "AY shared-library build commit")?;
    if build_commit != state.commit {
        return Err(format!(
            "AY shared-library build commit {build_commit} does not match current main {}",
            state.commit
        ));
    }
    Ok(SourceProvenance {
        source_commit: state.commit.clone(),
        origin_main_commit: state.origin_main_commit.clone(),
        // This records the cleanliness of the artifact build, proven by the
        // exact stamped commit and absence of `-dirty`. The calling worktree
        // may contain unrelated user changes.
        source_clean: true,
        ay_shared_library_build_stamp: ay_build_stamp.to_string(),
    })
}

fn abi_value_case(
    binding: &AbiCaseBinding<'_>,
    id: &str,
    expected: String,
    observed: String,
    pass: bool,
) -> ValidatorCase {
    ValidatorCase {
        id: id.to_string(),
        input_sha256: binding.input_sha256(id),
        expected,
        observed,
        stdout: None,
        stderr: None,
        exit_code: None,
        process: None,
        outcome: if pass {
            ValidatorCaseOutcome::Pass
        } else {
            ValidatorCaseOutcome::Fail
        },
    }
}

fn abi_child_case(
    binding: &AbiCaseBinding<'_>,
    id: &str,
    capture: &AbiProbeCapture,
) -> ValidatorCase {
    ValidatorCase {
        id: id.to_string(),
        input_sha256: binding.input_sha256(id),
        expected: abi_child_expectation(id).to_string(),
        observed: capture.category.to_string(),
        stdout: None,
        stderr: None,
        exit_code: capture.exit_code,
        process: Some(capture.process.clone()),
        outcome: capture.outcome,
    }
}

fn abi_stock_c_case(
    binding: &AbiCaseBinding<'_>,
    capture: &AbiStockCProbeCapture,
) -> ValidatorCase {
    ValidatorCase {
        id: capture.id.clone(),
        input_sha256: binding.input_sha256(&capture.id),
        expected: abi_stock_c_expectation().to_string(),
        observed: capture.category.to_string(),
        stdout: None,
        stderr: None,
        exit_code: capture.exit_code,
        process: Some(capture.process.clone()),
        outcome: capture.outcome,
    }
}

fn execute_z3_abi(
    contract: &Contract,
    inventory_sha256: &str,
    validator_source: &Path,
    validator_sha256: &str,
    ay_source: &Path,
    z3_source: &Path,
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<AbiExecution, String> {
    if timeout.is_zero() || timeout > Duration::from_hours(1) {
        return Err("z3-abi-5.0 timeout must be between 1ns and 3600 seconds".to_string());
    }
    let ay_artifact = contract
        .subject
        .ay_shared_library
        .as_ref()
        .ok_or("z3-abi-5.0 requires subject.ay_shared_library")?;
    let z3_artifact = &contract.profile.z3_overlay.reference_shared_library;
    let staged_validator =
        stage_authenticated_executable(validator_source, validator_sha256, "ABI validator")?;
    let staged_ay =
        stage_authenticated_library(ay_source, &ay_artifact.sha256, "AY shared library")?;
    let staged_z3 =
        stage_authenticated_library(z3_source, &z3_artifact.sha256, "Z3 5.1.0 shared library")?;

    let repo_root = locate_repo_root()?;
    let git_before = current_git_main_state(&repo_root)?;
    validate_current_main_state(&git_before)?;
    let resources =
        PlannedResources::plan(&repo_root, 1, "ay-z3-parity smtlib-conformance z3-abi-5.0")
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
                "live z3-abi-5.0 replay resource envelope drift: expected {expected:?}, got {resource_envelope:?}"
            ));
        }
    }

    let z3_capture = run_abi_probe_child(
        &resources,
        &staged_validator.path,
        &staged_z3.path,
        b"",
        timeout,
        "Z3 5.1.0 ABI reference probe",
        AbiProbeStderrPolicy::Empty,
    )?;
    let z3_observation = z3_capture.observation.as_ref().ok_or_else(|| {
        format!(
            "authenticated Z3 5.1.0 ABI probe did not complete: {}",
            z3_capture.category
        )
    })?;
    validate_probe_observation_shape(z3_observation, "Z3 5.1.0")?;
    if !crate::z3_abi_500::required_symbol_set_is_exact(&z3_observation.exported_z3_symbols) {
        return Err(format!(
            "authenticated Z3 5.1.0 export manifest is not the committed {}-export-name manifest {}",
            crate::z3_abi_500::REQUIRED_SYMBOL_COUNT,
            crate::z3_abi_500::REQUIRED_SYMBOL_MANIFEST_SHA256
        ));
    }
    if z3_observation.required_resolvable_symbols != z3_observation.exported_z3_symbols {
        return Err("an authenticated Z3 5.1.0 export is not dlsym-resolvable".to_string());
    }
    if z3_observation.full_version.as_deref() != Some(crate::z3_abi_500::Z3_500_FULL_VERSION) {
        return Err(format!(
            "authenticated Z3 shared library reports {:?}, expected {:?}",
            z3_observation.full_version,
            crate::z3_abi_500::Z3_500_FULL_VERSION
        ));
    }
    let expected_probes = crate::z3_abi_500::expected_probe_values();
    if z3_observation.probes != expected_probes {
        let mismatches = expected_probes
            .iter()
            .filter(|(id, expected)| z3_observation.probes.get(*id) != Some(*expected))
            .map(|(id, expected)| {
                format!(
                    "{id}: expected {expected:?}, got {:?}",
                    z3_observation.probes.get(id)
                )
            })
            .collect::<Vec<_>>();
        return Err(format!(
            "authenticated Z3 5.1.0 did not establish the canonical finite-set probes: {}",
            mismatches.join("; ")
        ));
    }

    let manifest = required_symbol_manifest_bytes(&z3_observation.exported_z3_symbols);
    let ay_capture = run_abi_probe_child(
        &resources,
        &staged_validator.path,
        &staged_ay.path,
        &manifest,
        timeout,
        "AY Z3 5.1.0 ABI probe",
        AbiProbeStderrPolicy::AyFiniteSetModelDiagnostics,
    )?;
    if let Some(observation) = ay_capture.observation.as_ref() {
        validate_probe_observation_shape(observation, "AY")?;
    }

    let stock_c_captures =
        run_stock_c_probes(&resources, &staged_ay.path, &staged_z3.path, timeout)?;

    let post_validator_sha = sha256_file(
        &staged_validator.path,
        "staged ABI validator after all probes",
    )?;
    let post_ay_sha = sha256_file(&staged_ay.path, "staged AY after all ABI probes")?;
    let post_z3_sha = sha256_file(&staged_z3.path, "staged Z3 after all ABI probes")?;
    if post_validator_sha != validator_sha256
        || post_ay_sha != ay_artifact.sha256
        || post_z3_sha != z3_artifact.sha256
    {
        return Err(
            "authenticated validator, AY, or Z3 bytes changed during ABI probes".to_string(),
        );
    }

    let git_after = current_git_main_state(&repo_root)?;
    if git_after != git_before {
        return Err("current-main source provenance changed during ABI probes".to_string());
    }
    let ay_build_stamp = ay_capture
        .observation
        .as_ref()
        .and_then(|observation| observation.ay_build_stamp.as_deref())
        .ok_or("AY ABI probe did not return an `ay_version` build stamp")?;
    let provenance = source_provenance(&git_after, ay_build_stamp)?;
    let profile_sha256 = canonical_profile_sha256()?;
    let binding = AbiCaseBinding {
        profile_sha256: &profile_sha256,
        inventory_sha256,
        validator_sha256,
        ay_sha256: &ay_artifact.sha256,
        z3_sha256: &z3_artifact.sha256,
        source: &provenance,
        resource_envelope: &resource_envelope,
    };

    let mut rows = vec![
        abi_child_case(&binding, "abi.child.ay", &ay_capture),
        abi_child_case(&binding, "abi.child.z3", &z3_capture),
        abi_value_case(
            &binding,
            "abi.identity.ay-library",
            format!("sha256={}", ay_artifact.sha256),
            format!("sha256={post_ay_sha}"),
            post_ay_sha == ay_artifact.sha256,
        ),
        abi_value_case(
            &binding,
            "abi.identity.z3-library",
            format!("sha256={}", z3_artifact.sha256),
            format!("sha256={post_z3_sha}"),
            post_z3_sha == z3_artifact.sha256,
        ),
        abi_value_case(
            &binding,
            "abi.identity.z3-version",
            crate::z3_abi_500::Z3_500_FULL_VERSION.to_string(),
            z3_observation
                .full_version
                .clone()
                .unwrap_or_else(|| "unavailable".to_string()),
            z3_observation.full_version.as_deref() == Some(crate::z3_abi_500::Z3_500_FULL_VERSION),
        ),
        abi_value_case(
            &binding,
            "abi.manifest.z3-5.1.0",
            format!(
                "count={};sha256={}",
                crate::z3_abi_500::REQUIRED_SYMBOL_COUNT,
                crate::z3_abi_500::REQUIRED_SYMBOL_MANIFEST_SHA256
            ),
            format!(
                "count={};sha256={};dlsym={}",
                z3_observation.exported_z3_symbols.len(),
                crate::z3_abi_500::symbol_manifest_sha256(&z3_observation.exported_z3_symbols),
                z3_observation.required_resolvable_symbols.len()
            ),
            crate::z3_abi_500::required_symbol_set_is_exact(&z3_observation.exported_z3_symbols)
                && z3_observation.required_resolvable_symbols == z3_observation.exported_z3_symbols,
        ),
        abi_value_case(
            &binding,
            "abi.provenance.ay-build",
            format!("build-commit={}", provenance.source_commit),
            provenance.ay_shared_library_build_stamp.clone(),
            build_stamp_commit(&provenance.ay_shared_library_build_stamp)
                == Some(provenance.source_commit.as_str()),
        ),
        abi_value_case(
            &binding,
            "abi.provenance.current-main",
            "ay-build-clean=true;HEAD=origin/main".to_string(),
            format!(
                "ay-build-clean={};HEAD={};origin/main={}",
                provenance.source_clean, provenance.source_commit, provenance.origin_main_commit
            ),
            provenance.source_clean && provenance.source_commit == provenance.origin_main_commit,
        ),
    ];

    let observed_c_surface = crate::z3_abi_500::observed_c_surface_values();
    for (surface, expected) in crate::z3_abi_500::expected_c_surface_values() {
        let observed = observed_c_surface
            .get(&surface)
            .cloned()
            .unwrap_or_else(|| "missing".to_string());
        rows.push(abi_value_case(
            &binding,
            &format!("abi.c-surface.{surface}"),
            expected.clone(),
            observed.clone(),
            observed == expected,
        ));
    }
    rows.push(abi_value_case(
        &binding,
        "abi.c-surface.shape",
        "805 sorted unique public declarations; all declared names exported; exactly two library-only exports; byte-exact complete pinned header graph".to_string(),
        if crate::z3_abi_500::c_surface_is_exact() {
            "exact".to_string()
        } else {
            "drift".to_string()
        },
        crate::z3_abi_500::c_surface_is_exact(),
    ));
    for capture in &stock_c_captures {
        rows.push(abi_stock_c_case(&binding, capture));
    }
    let mut successful_callability = BTreeSet::new();
    for probe in crate::z3_abi_500::stock_c_probes() {
        let pair_passed = ["ay", "z3"].iter().all(|subject| {
            let id = format!("abi.stock-c.{}.{subject}", probe.id);
            stock_c_captures
                .iter()
                .any(|capture| capture.id == id && capture.outcome == ValidatorCaseOutcome::Pass)
        });
        if pair_passed {
            successful_callability
                .extend(crate::z3_abi_500::stock_c_probe_callability_symbols(&probe));
        }
    }
    let declared_symbols = crate::z3_abi_500::public_c_declarations()
        .iter()
        .map(|declaration| {
            declaration
                .split_once('|')
                .expect("authenticated declaration manifest row")
                .0
                .to_string()
        })
        .collect::<BTreeSet<_>>();
    if !successful_callability.is_subset(&declared_symbols) {
        return Err(
            "authenticated callability inventory contains a non-public declaration".to_string(),
        );
    }
    for declaration in crate::z3_abi_500::public_c_declarations() {
        let (symbol, _) = declaration
            .split_once('|')
            .expect("authenticated declaration manifest row");
        let passed = successful_callability.contains(symbol);
        rows.push(abi_value_case(
            &binding,
            &format!("abi.callability.{symbol}"),
            abi_callability_expectation().to_string(),
            if passed {
                "passed".to_string()
            } else {
                "missing-or-failed".to_string()
            },
            passed,
        ));
    }
    let callability_count = successful_callability
        .intersection(&declared_symbols)
        .count();
    let missing_callability_count =
        crate::z3_abi_500::PUBLIC_C_DECLARATION_COUNT.saturating_sub(callability_count);
    rows.push(abi_value_case(
        &binding,
        "abi.callability.full-c-api",
        abi_callability_coverage_expectation().to_string(),
        format!(
            "{callability_count}/{} authenticated executed-call markers; {missing_callability_count} missing",
            crate::z3_abi_500::PUBLIC_C_DECLARATION_COUNT
        ),
        callability_count == crate::z3_abi_500::PUBLIC_C_DECLARATION_COUNT,
    ));
    let semantic_contracts = crate::z3_abi_500::semantic_contract_runtime_symbols();
    if !semantic_contracts.is_subset(&declared_symbols) {
        return Err(
            "authenticated semantic-contract inventory contains a non-public declaration"
                .to_string(),
        );
    }
    for declaration in crate::z3_abi_500::public_c_declarations() {
        let (symbol, _) = declaration
            .split_once('|')
            .expect("authenticated declaration manifest row");
        let passed = semantic_contracts.contains(symbol);
        rows.push(abi_value_case(
            &binding,
            &format!("abi.semantic-contract.{symbol}"),
            abi_semantic_contract_expectation().to_string(),
            if passed {
                "passed".to_string()
            } else {
                "missing".to_string()
            },
            passed,
        ));
    }
    let semantic_contract_count = semantic_contracts.intersection(&declared_symbols).count();
    let missing_semantic_contract_count =
        crate::z3_abi_500::PUBLIC_C_DECLARATION_COUNT.saturating_sub(semantic_contract_count);
    rows.push(abi_value_case(
        &binding,
        "abi.semantic-contract.full-c-api",
        abi_semantic_contract_coverage_expectation().to_string(),
        format!(
            "{semantic_contract_count}/{} authenticated exhaustive semantic contracts; {missing_semantic_contract_count} missing",
            crate::z3_abi_500::PUBLIC_C_DECLARATION_COUNT
        ),
        semantic_contract_count == crate::z3_abi_500::PUBLIC_C_DECLARATION_COUNT,
    ));

    let ay_resolvable = ay_capture
        .observation
        .as_ref()
        .map(|observation| {
            observation
                .required_resolvable_symbols
                .iter()
                .map(String::as_str)
                .collect::<BTreeSet<_>>()
        })
        .unwrap_or_default();
    for symbol in &z3_observation.exported_z3_symbols {
        let present = ay_resolvable.contains(symbol.as_str());
        rows.push(abi_value_case(
            &binding,
            &format!("abi.symbol.{symbol}"),
            "required Z3 5.1.0 symbol is dlsym-resolvable in AY".to_string(),
            if present {
                "present".to_string()
            } else {
                "missing".to_string()
            },
            present,
        ));
    }
    for (probe_id, expected) in expected_probes {
        let z3_value = z3_observation
            .probes
            .get(&probe_id)
            .cloned()
            .unwrap_or_else(|| "missing".to_string());
        let ay_value = ay_capture
            .observation
            .as_ref()
            .and_then(|observation| observation.probes.get(&probe_id))
            .cloned()
            .unwrap_or_else(|| ay_capture.category.to_string());
        rows.push(abi_value_case(
            &binding,
            &format!("abi.probe.{probe_id}"),
            expected.clone(),
            format!("z3={z3_value};ay={ay_value}"),
            z3_value == expected && ay_value == expected,
        ));
    }
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    let cases = case_counts_from_rows(&rows)?;
    let result = overall_validator_result(&rows);
    Ok(AbiExecution {
        ay_sha256: ay_artifact.sha256.clone(),
        z3_sha256: z3_artifact.sha256.clone(),
        source_provenance: provenance,
        resource_envelope,
        result,
        cases,
        case_results: rows,
    })
}

fn validate_z3_abi_execution(
    receipt: &ValidatorReceipt,
    live: &AbiExecution,
) -> Result<(), String> {
    if receipt.subject.ay_shared_library_sha256.as_deref() != Some(&live.ay_sha256)
        || receipt.z3_shared_library_sha256.as_deref() != Some(&live.z3_sha256)
        || receipt.source_provenance.as_ref() != Some(&live.source_provenance)
        || receipt.resource_envelope.as_deref() != Some(&live.resource_envelope)
        || receipt.result != live.result
        || receipt.cases != live.cases
        || receipt.case_results != live.case_results
    {
        return Err(
            "builtin.z3-abi-5.0.v1 receipt does not match a fresh authenticated live replay"
                .to_string(),
        );
    }
    Ok(())
}

fn replay_z3_abi_receipt(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    let envelope = receipt
        .resource_envelope
        .as_deref()
        .ok_or("z3-abi-5.0 receipt has no resource envelope")?;
    let parsed = parse_resource_envelope(envelope)?;
    if parsed.jobs != 1 {
        return Err("z3-abi-5.0 receipts require a one-job resource envelope".to_string());
    }
    let ay = context
        .contract
        .subject
        .ay_shared_library
        .as_ref()
        .ok_or("z3-abi-5.0 replay requires subject.ay_shared_library")?;
    let ay_path = artifact_path(context.manifest_dir, &ay.path);
    let z3_path = PathBuf::from(
        &context
            .contract
            .profile
            .z3_overlay
            .reference_shared_library
            .path,
    );
    let validator = fs::canonicalize(
        std::env::current_exe()
            .map_err(|error| format!("locating current ABI validator: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing current ABI validator: {error}"))?;
    let live = execute_z3_abi(
        context.contract,
        &context.dimension.inventory.sha256,
        &validator,
        &receipt.validator.sha256,
        &ay_path,
        &z3_path,
        parsed.timeout,
        Some(envelope),
    )?;
    validate_z3_abi_execution(receipt, &live)
}

fn run_z3_abi(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut ay_override: Option<PathBuf> = None;
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
                return Err(format!("unknown z3-abi-5.0 flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("z3-abi-5.0 takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }
    let manifest = manifest.ok_or("z3-abi-5.0 needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("z3-abi-5.0 requires --receipt <path>")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let subject_ay = loaded
        .contract
        .subject
        .ay_shared_library
        .as_ref()
        .ok_or("z3-abi-5.0 requires subject.ay_shared_library")?;
    let ay = ay_override.unwrap_or_else(|| artifact_path(&loaded.base, &subject_ay.path));
    // There is intentionally no Z3 override: this registered validator always
    // selects the immutable profile path and then authenticates its bytes.
    let z3 = PathBuf::from(
        &loaded
            .contract
            .profile
            .z3_overlay
            .reference_shared_library
            .path,
    );
    let target_receipt_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let current_exe =
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?;
    let current_exe = fs::canonicalize(&current_exe).map_err(|error| {
        format!(
            "canonicalizing parity executable {}: {error}",
            current_exe.display()
        )
    })?;
    let validator_path = current_exe
        .to_str()
        .ok_or("parity executable path is not UTF-8")?
        .to_string();
    let validator_sha = sha256_file(&current_exe, "parity validator")?;
    let overlay = loaded
        .contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == "overlay.z3-5.1.0")
        .ok_or("closed overlay dimension is missing")?;
    let execution = execute_z3_abi(
        &loaded.contract,
        &overlay.inventory.sha256,
        &current_exe,
        &validator_sha,
        &ay,
        &z3,
        Duration::from_secs(timeout_secs),
        None,
    )?;
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: overlay.id.clone(),
        requirement_ids: vec!["overlay.z3-5.1.0.c-abi".to_string()],
        inventory_sha256: overlay.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: "builtin.z3-abi-5.0.v1".to_string(),
            kind: ValidatorKind::Z3Differential,
            path: validator_path,
            sha256: validator_sha,
        },
        subject: ReceiptSubject {
            ay_executable_sha256: loaded
                .contract
                .subject
                .ay_executable
                .as_ref()
                .map(|artifact| artifact.sha256.clone()),
            ay_shared_library_sha256: Some(execution.ay_sha256),
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
        z3_shared_library_sha256: Some(execution.z3_sha256),
        reference_inputs: Vec::new(),
        auxiliary_tools: Vec::new(),
        source_provenance: Some(execution.source_provenance),
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
        "z3-abi-5.0={} receipt={} sha256={}",
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        target_receipt_relative,
        receipt_sha
    );
    println!(
        "attach to overlay.z3-5.1.0.c-abi: \
         {{\"path\":\"{target_receipt_relative}\",\"sha256\":\"{receipt_sha}\"}}"
    );
    println!(
        "set contract.resource_envelope to {:?} before attaching semantic evidence",
        receipt
            .resource_envelope
            .as_deref()
            .unwrap_or("<missing-envelope>")
    );
    if !report.complete {
        println!(
            "note: the rest of the contract remains incomplete ({} existing blockers)",
            report.blockers.len()
        );
    }
    Ok(i32::from(receipt.result != ValidatorResult::Pass))
}

fn transcript_case(
    id: &str,
    input: &[u8],
    expected_stdout: &str,
    output: GuardedTranscriptOutput,
    expectation: &str,
) -> ValidatorCase {
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
    } else if !output.status.is_some_and(|status| status.success()) {
        ValidatorCaseOutcome::Crash
    } else if !stderr.is_empty() || stdout != expected_stdout {
        ValidatorCaseOutcome::Fail
    } else {
        ValidatorCaseOutcome::Pass
    };
    let observed = format!(
        "status={:?}; timeout={}; memout={}; stdin_complete={}; stdout_truncated={}; stderr_truncated={}; stdout_match={}; stderr_empty={}",
        exit_code,
        output.timed_out,
        output.memout,
        output.stdin_complete,
        output.stdout_truncated,
        output.stderr_truncated,
        stdout == expected_stdout,
        stderr.is_empty()
    );
    ValidatorCase {
        id: id.to_string(),
        input_sha256: sha256_bytes(input),
        expected: format!("{expectation}; stdout={expected_stdout:?}; stderr=\"\"; exit=0"),
        observed,
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

fn case_counts_from_rows(rows: &[ValidatorCase]) -> Result<CaseCounts, String> {
    let mut counts = CaseCounts {
        total: rows.len(),
        passed: 0,
        failed: 0,
        skipped: 0,
        unknown: 0,
        timed_out: 0,
        memout: 0,
        crashed: 0,
        unavailable: 0,
    };
    for row in rows {
        match row.outcome {
            ValidatorCaseOutcome::Pass => counts.passed += 1,
            ValidatorCaseOutcome::Fail => counts.failed += 1,
            ValidatorCaseOutcome::Skipped => counts.skipped += 1,
            ValidatorCaseOutcome::Unknown => counts.unknown += 1,
            ValidatorCaseOutcome::Timeout => counts.timed_out += 1,
            ValidatorCaseOutcome::Memout => counts.memout += 1,
            ValidatorCaseOutcome::Crash => counts.crashed += 1,
            ValidatorCaseOutcome::Unavailable => counts.unavailable += 1,
        }
    }
    validate_case_results(rows, &counts)?;
    Ok(counts)
}

fn overall_validator_result(rows: &[ValidatorCase]) -> ValidatorResult {
    if rows
        .iter()
        .all(|row| row.outcome == ValidatorCaseOutcome::Pass)
    {
        return ValidatorResult::Pass;
    }
    if rows
        .iter()
        .any(|row| row.outcome == ValidatorCaseOutcome::Memout)
    {
        ValidatorResult::Memout
    } else if rows
        .iter()
        .any(|row| row.outcome == ValidatorCaseOutcome::Timeout)
    {
        ValidatorResult::Timeout
    } else if rows
        .iter()
        .any(|row| row.outcome == ValidatorCaseOutcome::Crash)
    {
        ValidatorResult::Crash
    } else if rows
        .iter()
        .any(|row| row.outcome == ValidatorCaseOutcome::Unavailable)
    {
        ValidatorResult::Unavailable
    } else if rows
        .iter()
        .any(|row| row.outcome == ValidatorCaseOutcome::Skipped)
    {
        ValidatorResult::Skipped
    } else {
        ValidatorResult::Fail
    }
}

fn locate_repo_root() -> Result<PathBuf, String> {
    let mut current =
        std::env::current_dir().map_err(|error| format!("reading current directory: {error}"))?;
    loop {
        if current.join("Cargo.toml").is_file()
            && current.join("scripts").join("_oom_guard.py").is_file()
        {
            return fs::canonicalize(&current)
                .map_err(|error| format!("canonicalizing repo root: {error}"));
        }
        if !current.pop() {
            return Err(
                "could not locate repo root containing Cargo.toml and scripts/_oom_guard.py"
                    .to_string(),
            );
        }
    }
}

fn future_relative_output(base: &Path, path: &Path) -> Result<String, String> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let file_name = path
        .file_name()
        .ok_or_else(|| format!("receipt path has no file name: {}", path.display()))?;
    let canonical_base = fs::canonicalize(base)
        .map_err(|error| format!("canonicalizing manifest directory: {error}"))?;
    let canonical_parent = fs::canonicalize(parent).map_err(|error| {
        format!(
            "canonicalizing receipt directory {}: {error}",
            parent.display()
        )
    })?;
    let resolved = canonical_parent.join(file_name);
    let relative = resolved.strip_prefix(&canonical_base).map_err(|_| {
        format!(
            "receipt {} must be inside manifest directory {}",
            resolved.display(),
            canonical_base.display()
        )
    })?;
    let value = relative
        .to_str()
        .ok_or("receipt relative path is not UTF-8")?
        .to_string();
    validate_relative_path(&value, "receipt relative path")?;
    Ok(value)
}

fn check_command(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut audit_only = false;
    let mut explicit_require_complete = false;
    let mut receipt: Option<PathBuf> = None;
    let mut json = false;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--require-complete" => explicit_require_complete = true,
            "--audit-only" => audit_only = true,
            "--json" => json = true,
            "--receipt" => {
                index += 1;
                receipt = Some(PathBuf::from(
                    args.get(index).ok_or("--receipt needs a path")?,
                ));
            }
            flag if flag.starts_with("--") => return Err(format!("unknown check flag {flag:?}")),
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("check takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }
    if audit_only && explicit_require_complete {
        return Err("--audit-only conflicts with --require-complete".to_string());
    }
    let require_complete = !audit_only;
    let manifest = manifest.ok_or("check needs a manifest path")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(
        &loaded.contract,
        &loaded.base,
        if require_complete {
            ValidationMode::Completion
        } else {
            ValidationMode::Audit
        },
    )?;
    if json {
        print_utf8(&pretty_json(&report)?)?;
    } else {
        print_report(&report);
    }
    if let Some(path) = receipt {
        let check_receipt = CheckReceipt {
            schema: CHECK_RECEIPT_SCHEMA.to_string(),
            created_unix_ms: unix_time_ms()?,
            manifest_sha256: loaded.sha256,
            profile_id: PROFILE_ID.to_string(),
            mode: if require_complete {
                CheckMode::RequireComplete
            } else {
                CheckMode::Integrity
            },
            report: report.clone(),
        };
        atomic_write_new(&path, &pretty_json(&check_receipt)?)?;
        if !json {
            println!("receipt={}", path.display());
        }
    }
    Ok(i32::from(require_complete && !report.complete))
}

fn receipt_check_command(args: &[String]) -> Result<i32, String> {
    let mut paths = Vec::new();
    let mut json = false;
    let mut audit_only = false;
    let mut explicit_require_complete = false;
    for arg in args {
        match arg.as_str() {
            "--json" => json = true,
            "--audit-only" => audit_only = true,
            "--require-complete" => explicit_require_complete = true,
            flag if flag.starts_with("--") => {
                return Err(format!("unknown receipt-check flag {flag:?}"));
            }
            value => paths.push(PathBuf::from(value)),
        }
    }
    if audit_only && explicit_require_complete {
        return Err("--audit-only conflicts with --require-complete".to_string());
    }
    if paths.len() != 2 {
        return Err("receipt-check needs exactly <manifest> <receipt>".to_string());
    }
    let loaded = load_contract(&paths[0])?;
    let receipt_bytes = read_bounded_bytes(
        &paths[1],
        MAX_VALIDATOR_RECEIPT_BYTES,
        "check receipt",
        true,
    )?;
    let receipt: CheckReceipt = serde_json::from_slice(&receipt_bytes)
        .map_err(|error| format!("invalid check receipt JSON {}: {error}", paths[1].display()))?;
    if receipt.schema != CHECK_RECEIPT_SCHEMA {
        return Err(format!(
            "check receipt schema mismatch: expected {CHECK_RECEIPT_SCHEMA}, got {:?}",
            receipt.schema
        ));
    }
    if receipt.profile_id != PROFILE_ID {
        return Err(format!(
            "check receipt profile mismatch: expected {PROFILE_ID}, got {:?}",
            receipt.profile_id
        ));
    }
    if receipt.manifest_sha256 != loaded.sha256 {
        return Err("check receipt belongs to different manifest bytes".to_string());
    }
    let now = unix_time_ms()?;
    if receipt.created_unix_ms > now.saturating_add(60_000) {
        return Err("check receipt timestamp is implausibly in the future".to_string());
    }
    let require_complete = !audit_only;
    let expected_mode = if require_complete {
        CheckMode::RequireComplete
    } else {
        CheckMode::Integrity
    };
    if receipt.mode != expected_mode {
        return Err(format!(
            "check receipt mode is {:?}; this invocation requires {:?}",
            receipt.mode, expected_mode
        ));
    }
    let report = validate_contract(
        &loaded.contract,
        &loaded.base,
        if require_complete {
            ValidationMode::Completion
        } else {
            ValidationMode::Audit
        },
    )?;
    if receipt.report != report {
        return Err("check receipt accounting does not match recomputed detailed rows".to_string());
    }
    if json {
        print_utf8(&pretty_json(&receipt)?)?;
    } else {
        print_report(&report);
        println!("receipt=valid");
    }
    Ok(i32::from(require_complete && !report.complete))
}

struct LoadedContract {
    contract: Contract,
    base: PathBuf,
    sha256: String,
}

fn load_contract(path: &Path) -> Result<LoadedContract, String> {
    let bytes = read_bounded_bytes(path, MAX_MANIFEST_BYTES, "conformance manifest", true)?;
    let contract: Contract = serde_json::from_slice(&bytes)
        .map_err(|error| format!("invalid conformance manifest {}: {error}", path.display()))?;
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let base = fs::canonicalize(parent).map_err(|error| {
        format!(
            "canonicalizing manifest directory {}: {error}",
            parent.display()
        )
    })?;
    Ok(LoadedContract {
        contract,
        base,
        sha256: sha256_bytes(&bytes),
    })
}

fn artifact_from_path(value: &str, base: &Path, label: &str) -> Result<Artifact, String> {
    validate_text(value, &format!("{label} path"))?;
    let path = artifact_path(base, value);
    let sha256 = sha256_file(&path, label)?;
    Ok(Artifact {
        path: value.to_string(),
        sha256,
    })
}

fn pretty_json<T: Serialize>(value: &T) -> Result<Vec<u8>, String> {
    let mut bytes =
        serde_json::to_vec_pretty(value).map_err(|error| format!("serializing JSON: {error}"))?;
    bytes.push(b'\n');
    Ok(bytes)
}

fn print_utf8(bytes: &[u8]) -> Result<(), String> {
    let text = std::str::from_utf8(bytes)
        .map_err(|error| format!("generated JSON is not UTF-8: {error}"))?;
    print!("{text}");
    Ok(())
}

fn print_report(report: &AuditReport) {
    println!("== SMT-LIB 2.7 + exact Z3 5.1.0 conformance contract ==");
    println!(
        "dimensions: {} (reference-complete {}, incomplete {})",
        report.summary.dimension_count,
        report.summary.reference_complete_dimensions,
        report.summary.reference_incomplete_dimensions
    );
    println!(
        "requirements: {} (validated {}, gaps {})",
        report.summary.requirement_count,
        report.summary.validated_requirements,
        report.summary.gap_requirements
    );
    println!(
        "non-passing evidence: {}",
        report.summary.skipped_or_failed_evidence
    );
    for dimension in &report.dimensions {
        println!(
            "  {:<34} inventory={} validated={}/{} gaps={}",
            dimension.id,
            if dimension.reference_complete {
                "complete"
            } else {
                "GAP"
            },
            dimension.validated_requirements,
            dimension.requirement_count,
            dimension.gap_requirements
        );
    }
    if report.blockers.is_empty() {
        println!("RESULT: PASS — the closed conformance contract is complete");
    } else {
        println!("RESULT: INCOMPLETE — {} blocker(s)", report.blockers.len());
        for blocker in report.blockers.iter().take(24) {
            println!("  GAP: {blocker}");
        }
        if report.blockers.len() > 24 {
            println!("  ... {} more", report.blockers.len() - 24);
        }
    }
}

fn unix_time_ms() -> Result<u128, String> {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_millis())
        .map_err(|error| format!("system clock is before Unix epoch: {error}"))
}

fn atomic_write_new(path: &Path, contents: &[u8]) -> Result<(), String> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let file_name = path
        .file_name()
        .ok_or_else(|| format!("output path has no file name: {}", path.display()))?;
    let canonical_parent = fs::canonicalize(parent).map_err(|error| {
        format!(
            "canonicalizing output directory {}: {error}",
            parent.display()
        )
    })?;
    let resolved = canonical_parent.join(file_name);
    if fs::symlink_metadata(&resolved).is_ok() {
        return Err(format!(
            "refusing to overwrite existing output {}",
            resolved.display()
        ));
    }
    let mut temporary = tempfile::NamedTempFile::new_in(&canonical_parent)
        .map_err(|error| format!("creating temporary output: {error}"))?;
    temporary
        .write_all(contents)
        .map_err(|error| format!("writing temporary output: {error}"))?;
    temporary
        .as_file()
        .sync_all()
        .map_err(|error| format!("syncing temporary output: {error}"))?;
    temporary
        .persist_noclobber(&resolved)
        .map_err(|error| format!("publishing {}: {}", resolved.display(), error.error))?;
    #[cfg(unix)]
    fs::File::open(&canonical_parent)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| {
            format!(
                "syncing output directory {}: {error}",
                canonical_parent.display()
            )
        })?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write(path: &Path, bytes: &[u8]) {
        fs::write(path, bytes).expect("write fixture");
    }

    fn dimension_mut<'a>(contract: &'a mut Contract, id: &str) -> &'a mut Dimension {
        contract
            .dimensions
            .iter_mut()
            .find(|dimension| dimension.id == id)
            .expect("dimension")
    }

    #[test]
    fn profile_pins_corrected_smtlib_27_and_exact_z3_500() {
        let profile = canonical_profile();
        assert_eq!(profile.standard.version, "2.7");
        assert_eq!(profile.standard.release, "2026-03-27");
        assert_eq!(
            profile.standard.language_sources.sha256,
            "09a6782d30308648e49a9cb241866bbd18ecf7d043174d45e3b88d118b5dad20"
        );
        assert_eq!(
            profile.standard.normative_pdf.sha256,
            "1099577ac197bb22ed35be4711b00e8ef8a4031aa3a0771baacc091b5a713b2c"
        );
        assert_eq!(
            profile.standard.registry.revision,
            "47f7ee09ea05de990277781bbb2091245ea4a3f1"
        );
        assert_eq!(profile.standard.registry.item_count, 34);
        assert_eq!(
            profile.standard.registry.sha256,
            "506519771cabc1ff0de8b1d6d482659c3fab4432a8c0304a1f50367cd516da04"
        );
        assert_eq!(profile.z3_overlay.version, "5.1.0");
        assert_eq!(
            profile.z3_overlay.source_commit,
            "0b6cdcdbc65da25ef0f73ac9da210574d0f66cf8"
        );
        assert_eq!(profile.z3_overlay.tracked_source_file_count, 2_756);
        assert_eq!(
            profile.z3_overlay.tracked_source_tree_digest_kind,
            "sorted-path-git-blob-size-manifest/v1"
        );
        assert_eq!(
            profile.z3_overlay.tracked_source_tree_sha256,
            "df491d15649b581936f8422fbd704b0694831c160c01d1d339164c8a1441939b"
        );
        assert_eq!(
            profile.z3_overlay.reference_executable.version_output,
            "Z3 version 5.1.0 - 64 bit"
        );
        assert_eq!(
            profile.z3_overlay.reference_executable.sha256,
            "8b61a8bc0b7a4e14dfb119910502ef808b055df636b25c8b67b96ae630fbc29c"
        );
        assert_eq!(
            profile.z3_overlay.reference_shared_library.full_version,
            "5.1.0.0"
        );
        assert_eq!(
            profile.z3_overlay.reference_shared_library.sha256,
            "45344d6a38b6f75304433c2458d6fa16bc4907d426c96e2bedf0a90603460422"
        );
    }

    #[test]
    fn starter_is_closed_over_dimensions_and_reviewed_registries() {
        assert_eq!(
            SMTLIB_COMMANDS,
            [
                "assert",
                "check-sat",
                "check-sat-assuming",
                "declare-const",
                "declare-datatype",
                "declare-datatypes",
                "declare-fun",
                "declare-sort",
                "declare-sort-parameter",
                "define-const",
                "define-fun",
                "define-fun-rec",
                "define-funs-rec",
                "define-sort",
                "echo",
                "exit",
                "get-assertions",
                "get-assignment",
                "get-info",
                "get-model",
                "get-option",
                "get-proof",
                "get-unsat-assumptions",
                "get-unsat-core",
                "get-value",
                "pop",
                "push",
                "reset",
                "reset-assertions",
                "set-info",
                "set-logic",
                "set-option",
            ]
        );
        assert_eq!(
            SMTLIB_THEORIES,
            [
                ("ArraysEx", "Theories/ArraysEx.smt2"),
                ("Core", "Theories/Core.smt2"),
                ("FixedSizeBitVectors", "Theories/FixedSizeBitVectors.smt2"),
                ("FloatingPoint", "Theories/FloatingPoint.smt2"),
                ("HO-Core", "Theories/HO-Core.smt2"),
                ("Ints", "Theories/Ints.smt2"),
                ("Reals", "Theories/Reals.smt2"),
                ("Reals_Ints", "Theories/Reals_Ints.smt2"),
                ("Strings", "Theories/UnicodeStrings.smt2"),
            ]
        );
        assert_eq!(
            SMTLIB_LOGICS,
            [
                "AUFLIA",
                "AUFLIRA",
                "AUFNIRA",
                "LIA",
                "LRA",
                "QF_ABV",
                "QF_AUFBV",
                "QF_AUFLIA",
                "QF_AX",
                "QF_BV",
                "QF_EIA",
                "QF_IDL",
                "QF_LIA",
                "QF_LRA",
                "QF_NIA",
                "QF_NRA",
                "QF_RDL",
                "QF_UF",
                "QF_UFBV",
                "QF_UFIDL",
                "QF_UFLIA",
                "QF_UFLRA",
                "QF_UFNRA",
                "UFLRA",
                "UFNIA",
            ]
        );
        let contract = starter_contract(Subject::default()).expect("starter");
        assert_eq!(contract.dimensions.len(), 12);
        assert_eq!(
            contract
                .dimensions
                .iter()
                .map(|dimension| dimension.requirements.len())
                .sum::<usize>(),
            199
        );
        let commands = contract
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "language.commands")
            .expect("commands");
        assert_eq!(commands.requirements.len(), 32);
        assert!(commands
            .requirements
            .iter()
            .any(|row| row.id.ends_with(".define-funs-rec")));
        let theories = contract
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "registry.theories")
            .expect("theories");
        assert_eq!(theories.requirements.len(), 9);
        assert_eq!(
            theories.inventory.granularity,
            InventoryGranularity::ItemLevel
        );
        let logics = contract
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "registry.logics")
            .expect("logics");
        assert_eq!(logics.requirements.len(), 25);
        assert!(logics
            .requirements
            .iter()
            .any(|row| row.id.ends_with(".QF_EIA")));
        let typing = contract
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "semantics.typing-and-scope")
            .expect("typing and scope");
        assert_eq!(typing.requirements.len(), 32);
        assert_eq!(
            typing.inventory.granularity,
            InventoryGranularity::ItemLevel
        );
        let state = contract
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "semantics.command-state-machine")
            .expect("command state machine");
        assert_eq!(state.requirements.len(), 47);
        assert_eq!(state.inventory.granularity, InventoryGranularity::ItemLevel);
    }

    #[test]
    fn honest_starter_is_valid_but_cannot_be_complete() {
        let directory = tempfile::tempdir().expect("tempdir");
        let contract = starter_contract(Subject::default()).expect("starter");
        let report = validate_contract(&contract, directory.path(), ValidationMode::Structural)
            .expect("valid starter contract");
        assert!(!report.complete);
        assert_eq!(report.summary.reference_complete_dimensions, 0);
        assert_eq!(report.summary.validated_requirements, 0);
        assert_eq!(report.summary.gap_requirements, 199);
        assert!(report
            .blockers
            .iter()
            .any(|blocker| blocker.contains("campaign_id")));
    }

    #[test]
    fn missing_closed_dimension_is_rejected() {
        let directory = tempfile::tempdir().expect("tempdir");
        let mut contract = starter_contract(Subject::default()).expect("starter");
        contract.dimensions.pop();
        let error = validate_contract(&contract, directory.path(), ValidationMode::Structural)
            .expect_err("missing dimension must fail");
        assert!(error.contains("closed dimension mismatch"));
    }

    #[test]
    fn missing_canonical_command_is_rejected_even_with_rehashed_inventory() {
        let directory = tempfile::tempdir().expect("tempdir");
        let mut contract = starter_contract(Subject::default()).expect("starter");
        let dimension = dimension_mut(&mut contract, "language.commands");
        dimension
            .requirements
            .retain(|row| !row.id.ends_with(".define-funs-rec"));
        dimension.inventory.item_count = dimension.requirements.len();
        dimension.inventory.sha256 =
            inventory_sha256(&dimension.requirements).expect("inventory digest");
        let error = validate_contract(&contract, directory.path(), ValidationMode::Structural)
            .expect_err("shrunk command set must fail");
        assert!(error.contains("invented or missing rows"));
        assert!(error.contains("define-funs-rec"));
    }

    #[test]
    fn invented_closed_inventory_row_is_rejected_even_with_rehashed_inventory() {
        let directory = tempfile::tempdir().expect("tempdir");
        let mut contract = starter_contract(Subject::default()).expect("starter");
        let dimension = dimension_mut(&mut contract, "language.commands");
        let mut invented = dimension.requirements[0].clone();
        invented.id = "language.commands.zz-invented".to_string();
        dimension.requirements.push(invented);
        dimension
            .requirements
            .sort_by(|left, right| left.id.cmp(&right.id));
        dimension.inventory.item_count = dimension.requirements.len();
        dimension.inventory.sha256 =
            inventory_sha256(&dimension.requirements).expect("inventory digest");
        let error = validate_contract(&contract, directory.path(), ValidationMode::Structural)
            .expect_err("invented official row must fail");
        assert!(error.contains("invented or missing rows"));
        assert!(error.contains("zz-invented"));
    }

    #[test]
    fn inventory_digest_tampering_is_rejected() {
        let directory = tempfile::tempdir().expect("tempdir");
        let mut contract = starter_contract(Subject::default()).expect("starter");
        dimension_mut(&mut contract, "registry.logics")
            .inventory
            .sha256 = "0".repeat(64);
        let error = validate_contract(&contract, directory.path(), ValidationMode::Structural)
            .expect_err("tampered digest must fail");
        assert!(error.contains("inventory digest mismatch"));
    }

    #[test]
    fn canonical_obligation_content_cannot_be_weakened() {
        let directory = tempfile::tempdir().expect("tempdir");
        let mut contract = starter_contract(Subject::default()).expect("starter");
        let dimension = dimension_mut(&mut contract, "results.sat-models");
        dimension.requirements[0].claim = "run one smoke test".to_string();
        dimension.inventory.sha256 =
            inventory_sha256(&dimension.requirements).expect("inventory digest");
        let error = validate_contract(&contract, directory.path(), ValidationMode::Structural)
            .expect_err("weakened canonical row must fail");
        assert!(error.contains("changed its source or obligation"));
    }

    #[test]
    fn resource_envelope_is_closed_and_typed() {
        assert!(validate_resource_envelope("anything nonempty").is_err());
        assert!(validate_resource_envelope(
            "oom-guard-v2:jobs=1;memlimit_mb=1024;nbcore=1;headroom_mb=512;timeout_ns=1000000000;enforcement=ay-resource-v1:rss-watchdog-zero-grace;aggregate=ay-host-exclusive-flock-v1"
        )
        .is_ok());
    }

    fn attach_fixture_receipt(
        contract: &Contract,
        dimension_id: &str,
        requirement_ids: Vec<String>,
        kind: ValidatorKind,
        envelope: Option<String>,
    ) -> ValidatorReceipt {
        let dimension = contract
            .dimensions
            .iter()
            .find(|dimension| dimension.id == dimension_id)
            .expect("fixture dimension");
        ValidatorReceipt {
            schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
            campaign_id: contract.campaign_id.clone(),
            profile_id: PROFILE_ID.to_string(),
            profile_sha256: canonical_profile_sha256().expect("profile sha"),
            dimension_id: dimension_id.to_string(),
            requirement_ids,
            inventory_sha256: dimension.inventory.sha256.clone(),
            validator: ValidatorIdentity {
                id: "fixture.validator".to_string(),
                kind,
                path: "/fixture/validator".to_string(),
                sha256: "1".repeat(64),
            },
            subject: ReceiptSubject {
                ay_executable_sha256: None,
                ay_shared_library_sha256: None,
            },
            z3_binary_sha256: None,
            z3_shared_library_sha256: None,
            reference_inputs: Vec::new(),
            auxiliary_tools: Vec::new(),
            source_provenance: None,
            resource_envelope: envelope,
            exhaustive: true,
            result: ValidatorResult::Pass,
            cases: CaseCounts {
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
            case_results: vec![passing_fixture_case("fixture.pass")],
        }
    }

    fn passing_fixture_case(id: &str) -> ValidatorCase {
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

    #[test]
    fn attach_routes_inventory_and_semantic_receipts_without_manual_json_edits() {
        let mut contract = starter_contract(Subject::default()).expect("starter");
        contract.campaign_id = "attach-test".to_string();
        let command_ids = contract
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "language.commands")
            .expect("commands")
            .requirements
            .iter()
            .map(|row| row.id.clone())
            .collect::<Vec<_>>();
        let inventory = attach_fixture_receipt(
            &contract,
            "language.commands",
            command_ids,
            ValidatorKind::ReferenceExtractor,
            None,
        );
        let inventory_ref = EvidenceRef {
            path: "evidence/commands.json".to_string(),
            sha256: "2".repeat(64),
        };
        let label = attach_receipt_reference(&mut contract, inventory_ref.clone(), &inventory)
            .expect("attach inventory");
        assert_eq!(label, "language.commands inventory");
        let commands = contract
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "language.commands")
            .expect("commands");
        assert_eq!(commands.inventory.evidence, [inventory_ref]);
        assert!(commands.inventory.gap.is_none());

        let envelope = "oom-guard-v2:jobs=1;memlimit_mb=1024;nbcore=1;headroom_mb=512;timeout_ns=1000000000;enforcement=ay-resource-v1:rss-watchdog-zero-grace;aggregate=ay-host-exclusive-flock-v1".to_string();
        let requirement_id = "gate.integrity.negative-controls".to_string();
        let semantic = attach_fixture_receipt(
            &contract,
            "gate.integrity",
            vec![requirement_id.clone()],
            ValidatorKind::GateNegativeControl,
            Some(envelope.clone()),
        );
        let semantic_ref = EvidenceRef {
            path: "evidence/gate.json".to_string(),
            sha256: "3".repeat(64),
        };
        assert_eq!(
            attach_receipt_reference(&mut contract, semantic_ref.clone(), &semantic)
                .expect("attach semantic"),
            requirement_id
        );
        assert_eq!(
            contract.resource_envelope.as_deref(),
            Some(envelope.as_str())
        );
        let gate = contract
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "gate.integrity")
            .expect("gate");
        assert_eq!(gate.requirements[0].evidence, [semantic_ref]);
        assert!(gate.requirements[0].gap.is_none());
    }

    #[test]
    fn ay_abi_stderr_policy_is_closed_to_the_four_known_array_diagnostics() {
        let line = "c !! MODEL-UNCONFIRMED [UNCONFIRMED/published] \
            (not a refutation — see [AY SOUNDNESS GATE] for caught invalid models) \
            model validation incomplete: SmtGroundAssertion: Assertion 1: (= a b) \
            function-backed array equality could not be independently validated (#as-array-ext)\n";
        assert!(is_expected_ay_abi_stderr(line.repeat(4).as_bytes()));
        assert!(!is_expected_ay_abi_stderr(line.repeat(3).as_bytes()));
        assert!(!is_expected_ay_abi_stderr(
            format!("{}c unexpected\n", line.repeat(4)).as_bytes()
        ));
        assert!(!is_expected_ay_abi_stderr(
            line.repeat(4)
                .replace("#as-array-ext", "#different")
                .as_bytes()
        ));
    }

    fn synthetic_abi_receipt(contract: &Contract) -> ValidatorReceipt {
        let overlay = contract
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "overlay.z3-5.1.0")
            .expect("overlay");
        let ay_sha256 = "a".repeat(64);
        let validator_sha256 = "b".repeat(64);
        let source_commit = "c".repeat(40);
        let z3_sha256 = contract
            .profile
            .z3_overlay
            .reference_shared_library
            .sha256
            .clone();
        let resource_envelope = "oom-guard-v2:jobs=1;memlimit_mb=1024;nbcore=1;headroom_mb=512;timeout_ns=1000000000;enforcement=ay-resource-v1:rss-watchdog-zero-grace;aggregate=ay-host-exclusive-flock-v1".to_string();
        let provenance = SourceProvenance {
            source_commit: source_commit.clone(),
            origin_main_commit: source_commit.clone(),
            source_clean: true,
            ay_shared_library_build_stamp: format!(
                "0.5.0+build.1.{source_commit}@2026-07-29T00:00:00Z"
            ),
        };
        let profile_sha256 = canonical_profile_sha256().expect("profile sha");
        let binding = AbiCaseBinding {
            profile_sha256: &profile_sha256,
            inventory_sha256: &overlay.inventory.sha256,
            validator_sha256: &validator_sha256,
            ay_sha256: &ay_sha256,
            z3_sha256: &z3_sha256,
            source: &provenance,
            resource_envelope: &resource_envelope,
        };
        let failed_row = |id: String, expected: String, child: bool| ValidatorCase {
            input_sha256: binding.input_sha256(&id),
            id,
            expected,
            observed: "synthetic failure".to_string(),
            stdout: None,
            stderr: None,
            exit_code: child.then_some(1),
            process: child.then_some(ProcessObservation {
                stdin_complete: true,
                timed_out: false,
                memout: false,
                stdout_truncated: false,
                stderr_truncated: false,
            }),
            outcome: ValidatorCaseOutcome::Fail,
        };
        let mut rows = vec![
            failed_row(
                "abi.child.ay".to_string(),
                abi_child_expectation("abi.child.ay").to_string(),
                true,
            ),
            failed_row(
                "abi.child.z3".to_string(),
                abi_child_expectation("abi.child.z3").to_string(),
                true,
            ),
            failed_row(
                "abi.identity.ay-library".to_string(),
                format!("sha256={ay_sha256}"),
                false,
            ),
            failed_row(
                "abi.identity.z3-library".to_string(),
                format!("sha256={z3_sha256}"),
                false,
            ),
            failed_row(
                "abi.identity.z3-version".to_string(),
                crate::z3_abi_500::Z3_500_FULL_VERSION.to_string(),
                false,
            ),
            failed_row(
                "abi.manifest.z3-5.1.0".to_string(),
                format!(
                    "count={};sha256={}",
                    crate::z3_abi_500::REQUIRED_SYMBOL_COUNT,
                    crate::z3_abi_500::REQUIRED_SYMBOL_MANIFEST_SHA256
                ),
                false,
            ),
            failed_row(
                "abi.provenance.ay-build".to_string(),
                format!("build-commit={source_commit}"),
                false,
            ),
            failed_row(
                "abi.provenance.current-main".to_string(),
                "ay-build-clean=true;HEAD=origin/main".to_string(),
                false,
            ),
        ];
        for symbol in crate::z3_abi_500::required_symbols() {
            rows.push(failed_row(
                format!("abi.symbol.{symbol}"),
                "required Z3 5.1.0 symbol is dlsym-resolvable in AY".to_string(),
                false,
            ));
        }
        for (probe, expected) in crate::z3_abi_500::expected_probe_values() {
            rows.push(failed_row(format!("abi.probe.{probe}"), expected, false));
        }
        for (surface, expected) in crate::z3_abi_500::expected_c_surface_values() {
            rows.push(failed_row(
                format!("abi.c-surface.{surface}"),
                expected,
                false,
            ));
        }
        rows.push(failed_row(
            "abi.c-surface.shape".to_string(),
            "805 sorted unique public declarations; all declared names exported; exactly two library-only exports; byte-exact complete pinned header graph".to_string(),
            false,
        ));
        for probe in crate::z3_abi_500::stock_c_probes() {
            for subject in ["ay", "z3"] {
                rows.push(failed_row(
                    format!("abi.stock-c.{}.{subject}", probe.id),
                    abi_stock_c_expectation().to_string(),
                    true,
                ));
            }
        }
        for declaration in crate::z3_abi_500::public_c_declarations() {
            let (symbol, _) = declaration
                .split_once('|')
                .expect("authenticated declaration manifest row");
            rows.push(failed_row(
                format!("abi.callability.{symbol}"),
                abi_callability_expectation().to_string(),
                false,
            ));
        }
        rows.push(failed_row(
            "abi.callability.full-c-api".to_string(),
            abi_callability_coverage_expectation().to_string(),
            false,
        ));
        for declaration in crate::z3_abi_500::public_c_declarations() {
            let (symbol, _) = declaration
                .split_once('|')
                .expect("authenticated declaration manifest row");
            rows.push(failed_row(
                format!("abi.semantic-contract.{symbol}"),
                abi_semantic_contract_expectation().to_string(),
                false,
            ));
        }
        rows.push(failed_row(
            "abi.semantic-contract.full-c-api".to_string(),
            abi_semantic_contract_coverage_expectation().to_string(),
            false,
        ));
        rows.sort_by(|left, right| left.id.cmp(&right.id));
        let cases = case_counts_from_rows(&rows).expect("closed ABI case accounting");
        ValidatorReceipt {
            schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
            campaign_id: "abi-test".to_string(),
            profile_id: PROFILE_ID.to_string(),
            profile_sha256,
            dimension_id: overlay.id.clone(),
            requirement_ids: vec!["overlay.z3-5.1.0.c-abi".to_string()],
            inventory_sha256: overlay.inventory.sha256.clone(),
            validator: ValidatorIdentity {
                id: "builtin.z3-abi-5.0.v1".to_string(),
                kind: ValidatorKind::Z3Differential,
                path: "/validator".to_string(),
                sha256: validator_sha256,
            },
            subject: ReceiptSubject {
                ay_executable_sha256: None,
                ay_shared_library_sha256: Some(ay_sha256),
            },
            z3_binary_sha256: Some(
                contract
                    .profile
                    .z3_overlay
                    .reference_executable
                    .sha256
                    .clone(),
            ),
            z3_shared_library_sha256: Some(z3_sha256),
            reference_inputs: Vec::new(),
            auxiliary_tools: Vec::new(),
            source_provenance: Some(provenance),
            resource_envelope: Some(resource_envelope),
            exhaustive: true,
            result: ValidatorResult::Fail,
            cases,
            case_results: rows,
        }
    }

    #[test]
    fn registered_abi_receipt_requires_exact_manifest_provenance_and_case_hashes() {
        let contract = starter_contract(Subject {
            ay_executable: None,
            ay_shared_library: Some(Artifact {
                path: "libay".to_string(),
                sha256: "a".repeat(64),
            }),
        })
        .expect("starter");
        let overlay = contract
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "overlay.z3-5.1.0")
            .expect("overlay");
        let context = EvidenceContext {
            contract: &contract,
            manifest_dir: Path::new("."),
            dimension: overlay,
            expected_kind: ValidatorKind::Z3Differential,
            required_requirement_id: Some("overlay.z3-5.1.0.c-abi"),
            exact_requirement_ids: None,
            mode: ValidationMode::Structural,
        };
        let receipt = synthetic_abi_receipt(&contract);
        validate_z3_abi_receipt_shape(&receipt, context).expect("exact ABI receipt shape");

        let mut missing_symbol = receipt.clone();
        missing_symbol
            .case_results
            .retain(|row| row.id != "abi.symbol.Z3_update_term");
        assert!(validate_z3_abi_receipt_shape(&missing_symbol, context)
            .expect_err("missing symbol must fail")
            .contains("exact 807-export-name manifest"));

        let mut stale_case = receipt.clone();
        stale_case
            .case_results
            .iter_mut()
            .find(|row| row.id == "abi.probe.decl-kind.finite-set-empty")
            .expect("probe")
            .input_sha256 = "0".repeat(64);
        assert!(validate_z3_abi_receipt_shape(&stale_case, context)
            .expect_err("stale case binding must fail")
            .contains("stale or forged"));

        let mut dirty_build = receipt;
        dirty_build
            .source_provenance
            .as_mut()
            .expect("provenance")
            .source_clean = false;
        assert!(validate_z3_abi_receipt_shape(&dirty_build, context)
            .expect_err("dirty build must fail")
            .contains("clean AY build"));
    }

    #[test]
    fn strict_schema_rejects_unknown_fields() {
        let contract = starter_contract(Subject::default()).expect("starter");
        let mut value = serde_json::to_value(contract).expect("json");
        value
            .as_object_mut()
            .expect("object")
            .insert("overall_pass".to_string(), serde_json::json!(true));
        let error = serde_json::from_value::<Contract>(value).expect_err("unknown field must fail");
        assert!(error.to_string().contains("unknown field"));
    }

    #[test]
    fn check_and_receipt_check_require_completion_unless_audit_is_explicit() {
        let directory = tempfile::tempdir().expect("tempdir");
        let manifest = directory.path().join("contract.json");
        let receipt = directory.path().join("audit.json");
        let bytes = pretty_json(&starter_contract(Subject::default()).expect("starter"))
            .expect("contract json");
        write(&manifest, &bytes);

        let default_exit =
            check_command(&[manifest.to_string_lossy().into_owned()]).expect("default check");
        assert_eq!(default_exit, 1);
        let audit_exit = check_command(&[
            manifest.to_string_lossy().into_owned(),
            "--audit-only".to_string(),
            "--receipt".to_string(),
            receipt.to_string_lossy().into_owned(),
        ])
        .expect("explicit audit");
        assert_eq!(audit_exit, 0);

        let downgrade = receipt_check_command(&[
            manifest.to_string_lossy().into_owned(),
            receipt.to_string_lossy().into_owned(),
        ])
        .expect_err("audit receipt cannot satisfy the default completion policy");
        assert!(downgrade.contains("requires RequireComplete"));
        let explicit_audit = receipt_check_command(&[
            manifest.to_string_lossy().into_owned(),
            receipt.to_string_lossy().into_owned(),
            "--audit-only".to_string(),
        ])
        .expect("explicit audit receipt check");
        assert_eq!(explicit_audit, 0);
    }

    #[test]
    fn unregistered_validator_cannot_close_a_requirement() {
        let directory = tempfile::tempdir().expect("tempdir");
        write(&directory.path().join("ay"), b"ay executable");
        write(&directory.path().join("libay"), b"ay library");
        write(
            &directory.path().join("validator"),
            b"validator implementation",
        );
        let ay_sha = sha256_file(&directory.path().join("ay"), "ay").expect("hash");
        let lib_sha = sha256_file(&directory.path().join("libay"), "libay").expect("hash");
        let validator_sha =
            sha256_file(&directory.path().join("validator"), "validator").expect("hash");
        let subject = Subject {
            ay_executable: Some(Artifact {
                path: "ay".to_string(),
                sha256: ay_sha.clone(),
            }),
            ay_shared_library: Some(Artifact {
                path: "libay".to_string(),
                sha256: lib_sha.clone(),
            }),
        };
        let mut contract = starter_contract(subject).expect("starter");
        contract.campaign_id = "unit-campaign".to_string();
        let envelope = "oom-guard-v2:jobs=1;memlimit_mb=1024;nbcore=1;headroom_mb=512;timeout_ns=1000000000;enforcement=ay-resource-v1:rss-watchdog-zero-grace;aggregate=ay-host-exclusive-flock-v1".to_string();
        contract.resource_envelope = Some(envelope.clone());
        let campaign_id = contract.campaign_id.clone();
        let gate = dimension_mut(&mut contract, "gate.integrity");
        let requirement_id = gate.requirements[0].id.clone();
        let receipt = ValidatorReceipt {
            schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
            campaign_id,
            profile_id: PROFILE_ID.to_string(),
            profile_sha256: canonical_profile_sha256().expect("profile sha"),
            dimension_id: gate.id.clone(),
            requirement_ids: vec![requirement_id],
            inventory_sha256: gate.inventory.sha256.clone(),
            validator: ValidatorIdentity {
                id: "unit.gate-validator".to_string(),
                kind: ValidatorKind::GateNegativeControl,
                path: "validator".to_string(),
                sha256: validator_sha,
            },
            subject: ReceiptSubject {
                ay_executable_sha256: Some(ay_sha),
                ay_shared_library_sha256: Some(lib_sha),
            },
            z3_binary_sha256: None,
            z3_shared_library_sha256: None,
            reference_inputs: Vec::new(),
            auxiliary_tools: Vec::new(),
            source_provenance: None,
            resource_envelope: Some(envelope),
            exhaustive: true,
            result: ValidatorResult::Pass,
            cases: CaseCounts {
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
            case_results: vec![ValidatorCase {
                id: "gate.rejects-tamper".to_string(),
                input_sha256: "1".repeat(64),
                expected: "the deliberately tampered contract is rejected".to_string(),
                observed: "the contract was rejected".to_string(),
                stdout: None,
                stderr: None,
                exit_code: Some(1),
                process: None,
                outcome: ValidatorCaseOutcome::Pass,
            }],
        };
        let bytes = pretty_json(&receipt).expect("receipt json");
        write(&directory.path().join("gate.json"), &bytes);
        gate.requirements[0].evidence.push(EvidenceRef {
            path: "gate.json".to_string(),
            sha256: sha256_bytes(&bytes),
        });
        gate.requirements[0].gap = None;
        let error = validate_contract(&contract, directory.path(), ValidationMode::Structural)
            .expect_err("unregistered evidence must fail");
        assert!(error.contains("unregistered validator"));
    }

    #[test]
    fn registered_identity_failure_remains_a_gap() {
        let directory = tempfile::tempdir().expect("tempdir");
        write(&directory.path().join("ay"), b"ay executable");
        write(&directory.path().join("libay"), b"ay library");
        let ay_sha = sha256_file(&directory.path().join("ay"), "ay").expect("hash");
        let lib_sha = sha256_file(&directory.path().join("libay"), "libay").expect("hash");
        let current_exe = fs::canonicalize(std::env::current_exe().expect("current exe"))
            .expect("canonical current exe");
        let validator_sha = sha256_file(&current_exe, "validator").expect("hash");
        let envelope = "oom-guard-v2:jobs=1;memlimit_mb=1024;nbcore=1;headroom_mb=512;timeout_ns=1000000000;enforcement=ay-resource-v1:rss-watchdog-zero-grace;aggregate=ay-host-exclusive-flock-v1".to_string();
        let mut contract = starter_contract(Subject {
            ay_executable: Some(Artifact {
                path: "ay".to_string(),
                sha256: ay_sha.clone(),
            }),
            ay_shared_library: Some(Artifact {
                path: "libay".to_string(),
                sha256: lib_sha.clone(),
            }),
        })
        .expect("starter");
        contract.campaign_id = "identity-failure".to_string();
        contract.resource_envelope = Some(envelope.clone());
        let overlay = dimension_mut(&mut contract, "overlay.z3-5.1.0");
        let input_sha = sha256_bytes(b"(get-info :name)\n(get-info :version)\n(exit)\n");
        let clean_process = ProcessObservation {
            stdin_complete: true,
            timed_out: false,
            memout: false,
            stdout_truncated: false,
            stderr_truncated: false,
        };
        let receipt = ValidatorReceipt {
            schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
            campaign_id: "identity-failure".to_string(),
            profile_id: PROFILE_ID.to_string(),
            profile_sha256: canonical_profile_sha256().expect("profile sha"),
            dimension_id: overlay.id.clone(),
            requirement_ids: vec!["overlay.z3-5.1.0.target-identity".to_string()],
            inventory_sha256: overlay.inventory.sha256.clone(),
            validator: ValidatorIdentity {
                id: "builtin.target-identity.v1".to_string(),
                kind: ValidatorKind::Z3Differential,
                path: current_exe.to_string_lossy().into_owned(),
                sha256: validator_sha,
            },
            subject: ReceiptSubject {
                ay_executable_sha256: Some(ay_sha),
                ay_shared_library_sha256: Some(lib_sha),
            },
            z3_binary_sha256: Some(canonical_profile().z3_overlay.reference_executable.sha256),
            z3_shared_library_sha256: None,
            reference_inputs: Vec::new(),
            auxiliary_tools: Vec::new(),
            source_provenance: None,
            resource_envelope: Some(envelope),
            exhaustive: true,
            result: ValidatorResult::Fail,
            cases: CaseCounts {
                total: 2,
                passed: 1,
                failed: 1,
                skipped: 0,
                unknown: 0,
                timed_out: 0,
                memout: 0,
                crashed: 0,
                unavailable: 0,
            },
            case_results: vec![
                ValidatorCase {
                    id: "ay.identity".to_string(),
                    input_sha256: input_sha.clone(),
                    expected: "exact Z3 5.1.0 identity".to_string(),
                    observed: "AY reported 4.15.4".to_string(),
                    stdout: Some("(:name \"Z3\")\n(:version \"4.15.4\")\n".to_string()),
                    stderr: Some(String::new()),
                    exit_code: Some(0),
                    process: Some(clean_process.clone()),
                    outcome: ValidatorCaseOutcome::Fail,
                },
                ValidatorCase {
                    id: "z3.identity".to_string(),
                    input_sha256: input_sha,
                    expected: "exact Z3 5.1.0 identity".to_string(),
                    observed: "Z3 reported 5.1.0".to_string(),
                    stdout: Some("(:name \"Z3\")\n(:version \"5.1.0\")\n".to_string()),
                    stderr: Some(String::new()),
                    exit_code: Some(0),
                    process: Some(clean_process),
                    outcome: ValidatorCaseOutcome::Pass,
                },
            ],
        };
        let live = IdentityExecution {
            ay_sha256: receipt
                .subject
                .ay_executable_sha256
                .clone()
                .expect("AY hash"),
            z3_sha256: receipt.z3_binary_sha256.clone().expect("Z3 hash"),
            resource_envelope: receipt
                .resource_envelope
                .clone()
                .expect("resource envelope"),
            result: receipt.result,
            cases: receipt.cases.clone(),
            case_results: receipt.case_results.clone(),
        };
        let mut forged_pass = receipt.clone();
        let forged_ay = forged_pass
            .case_results
            .iter_mut()
            .find(|row| row.id == "ay.identity")
            .expect("AY row");
        forged_ay.stdout = Some("(:name \"Z3\")\n(:version \"5.1.0\")\n".to_string());
        forged_ay.observed = "hand-authored passing transcript".to_string();
        forged_ay.outcome = ValidatorCaseOutcome::Pass;
        forged_pass.cases =
            case_counts_from_rows(&forged_pass.case_results).expect("forged counts");
        forged_pass.result = ValidatorResult::Pass;
        let replay_error = validate_target_identity_replay(&forged_pass, &live)
            .expect_err("public receipt fields cannot replace a live replay");
        assert!(replay_error.contains("fresh authenticated live replay"));

        let bytes = pretty_json(&receipt).expect("receipt json");
        write(&directory.path().join("identity.json"), &bytes);
        let target = overlay
            .requirements
            .iter_mut()
            .find(|row| row.id == "overlay.z3-5.1.0.target-identity")
            .expect("target identity row");
        target.evidence.push(EvidenceRef {
            path: "identity.json".to_string(),
            sha256: sha256_bytes(&bytes),
        });
        let report = validate_contract(&contract, directory.path(), ValidationMode::Structural)
            .expect("failed evidence is valid");
        assert!(!report.complete);
        assert_eq!(report.summary.skipped_or_failed_evidence, 1);
        assert!(report
            .blockers
            .iter()
            .any(|blocker| blocker == "overlay.z3-5.1.0.target-identity: semantic evidence gap"));
    }

    #[test]
    fn aggregate_pass_cannot_hide_a_skipped_case() {
        let counts = CaseCounts {
            total: 1,
            passed: 0,
            failed: 0,
            skipped: 1,
            unknown: 0,
            timed_out: 0,
            memout: 0,
            crashed: 0,
            unavailable: 0,
        };
        let rows = vec![ValidatorCase {
            id: "skipped.case".to_string(),
            input_sha256: "2".repeat(64),
            expected: "pass".to_string(),
            observed: "skipped".to_string(),
            stdout: None,
            stderr: None,
            exit_code: None,
            process: None,
            outcome: ValidatorCaseOutcome::Skipped,
        }];
        validate_case_results(&rows, &counts).expect("detailed skipped accounting");
        let falsified = CaseCounts {
            total: 1,
            passed: 1,
            failed: 0,
            skipped: 0,
            unknown: 0,
            timed_out: 0,
            memout: 0,
            crashed: 0,
            unavailable: 0,
        };
        assert!(validate_case_results(&rows, &falsified).is_err());
    }

    #[test]
    fn registered_validator_may_own_an_expected_nonzero_child_status() {
        let counts = CaseCounts {
            total: 1,
            passed: 1,
            failed: 0,
            skipped: 0,
            unknown: 0,
            timed_out: 0,
            memout: 0,
            crashed: 0,
            unavailable: 0,
        };
        let rows = vec![ValidatorCase {
            id: "negative.expected-rejection".to_string(),
            input_sha256: "2".repeat(64),
            expected: "registered validator requires rejection".to_string(),
            observed: "registered validator authenticated exit 1".to_string(),
            stdout: Some("(error \"rejected\")\nrecovered\n".to_string()),
            stderr: Some(String::new()),
            exit_code: Some(1),
            process: Some(ProcessObservation {
                stdin_complete: true,
                timed_out: false,
                memout: false,
                stdout_truncated: false,
                stderr_truncated: false,
            }),
            outcome: ValidatorCaseOutcome::Pass,
        }];
        validate_case_results(&rows, &counts)
            .expect("registered validator owns the exact expected exit class");
    }

    #[test]
    fn atomic_publication_never_overwrites() {
        let directory = tempfile::tempdir().expect("tempdir");
        let path = directory.path().join("receipt.json");
        atomic_write_new(&path, b"first").expect("first publication");
        let error = atomic_write_new(&path, b"second").expect_err("overwrite must fail");
        assert!(error.contains("refusing to overwrite"));
        assert_eq!(fs::read(&path).expect("read"), b"first");
    }
}
