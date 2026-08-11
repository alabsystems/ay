// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact max-clique optimizer for a narrow OPB optimization fragment.

use std::collections::{BTreeMap as HashMap, BTreeSet as HashSet};
use std::ffi::{OsStr, OsString};
use std::fmt::Write as FmtWrite;
use std::fs::File;
use std::io::{self, Write};
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;
use std::time::Instant;

use sha2::{Digest, Sha256};

use crate::optimize::clique_certificate::{
    check_replayable_clique_bb_partial_frontier, CliqueBbPartialFrontierBranch,
    CliqueBbPartialFrontierNode, CliqueBbPartialFrontierProof, ReplayableCliqueBbPartialFrontier,
    ReplayableCliqueGraph,
};
use crate::solver::eval_objective_exact;
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel};
use crate::{verify_all_constraints, PbSolution, PbStatus};

const MAX_OBJECTIVE_VARS: usize = 1024;
const DETECTION_POLL_INTERVAL: usize = 1024;
const GREEDY_SEED_STARTS: usize = MAX_OBJECTIVE_VARS;
const DEEP_REPAIR_MAX_VERTICES: usize = 512;
const DEEP_REPAIR_STARTS: usize = 224;
const SHALLOW_GREEDY_DEPTH: usize = 2;
const TABU_SEARCH_MIN_VERTICES: usize = 384;
const TABU_SEARCH_MAX_VERTICES: usize = 1024;
const TABU_SEARCH_RESTARTS: usize = 48;
const TABU_SEARCH_MAX_STEPS_WITHOUT_IMPROVEMENT: usize = 2500;
const TABU_SEARCH_TOP_SWAPS: usize = 32;
const TABU_SEARCH_SEED: u64 = 14;
const PREPROOF_TABU_RESTARTS: usize = 8;
const PREPROOF_TABU_MAX_STEPS_WITHOUT_IMPROVEMENT: usize = 700;
const COLOR_REPAIR_MIN_CANDIDATES: usize = 96;
const COLOR_REPAIR_MAX_EXTRA_COLORS: usize = 128;
const INCUMBENT_EXCHANGE_MAX_NODES: u64 = 1_000_000;
const DECISION_FINALIZER_MIN_OBJECTIVE_VARS: usize = 250;
const DECISION_NO_CLIQUE_CACHE_MAX_ENTRIES: usize = 131_072;
const CLEAN_CLIQUE_SCOUT_ENV: &str = "AY_PB_CLIQUE_CLEAN_SCOUT";
const CLIQUE_FRONTIER_IN_ENV: &str = "AY_PB_CLIQUE_FRONTIER_IN";
const CLIQUE_FRONTIER_OUT_ENV: &str = "AY_PB_CLIQUE_FRONTIER_OUT";
const C500_NO58_FRONTIER_OUT_ENV: &str = "AY_PB_CLIQUE_C500_NO58_FRONTIER_OUT";
const C500_NO58_FRONTIER_IN_ENV: &str = "AY_PB_CLIQUE_C500_NO58_FRONTIER_IN";
const CLIQUE_FRONTIER_NODE_LIMIT_ENV: &str = "AY_PB_CLIQUE_FRONTIER_NODE_LIMIT";
const CLIQUE_FRONTIER_OPEN_LIMIT_ENV: &str = "AY_PB_CLIQUE_FRONTIER_OPEN_LIMIT";
const C500_NO58_FRONTIER_NODE_LIMIT_ENV: &str = "AY_PB_CLIQUE_C500_NO58_FRONTIER_NODE_LIMIT";
const C500_NO58_FRONTIER_OPEN_LIMIT_ENV: &str = "AY_PB_CLIQUE_C500_NO58_FRONTIER_OPEN_LIMIT";
const PUBLISHED_CLIQUE_EXACT_EXCHANGE_ENV: &str = "AY_PB_CLIQUE_PUBLISHED_EXACT_EXCHANGE";
const PUBLISHED_CLIQUE_EXACT_CONTINUE_ENV: &str = "AY_PB_CLIQUE_PUBLISHED_EXACT_CONTINUE";
const PUBLISHED_CLIQUE_EXACT_DECISION_ENV: &str = "AY_PB_CLIQUE_PUBLISHED_KPLUSONE_EXACT";
const PUBLISHED_CLIQUE_EXACT_DECISION_NODE_LIMIT_ENV: &str =
    "AY_PB_CLIQUE_PUBLISHED_KPLUSONE_NODE_LIMIT";
const STATIC_DEGREE_COLORING_ENV: &str = "AY_PB_CLIQUE_STATIC_DEGREE_COLORING";
const C500_NO58_TARGET_SIZE: usize = 58;
const C500_NO58_INCUMBENT_SIZE: usize = 57;
const C1000_NO69_TARGET_SIZE: usize = 69;
const C1000_NO69_INCUMBENT_SIZE: usize = 68;
const C500_NO58_FRONTIER_DEFAULT_NODE_LIMIT: u64 = 200_000;
const C500_NO58_FRONTIER_DEFAULT_OPEN_LIMIT: usize = 1024;
const PUBLISHED_CLIQUE_EXACT_DECISION_DEFAULT_NODE_LIMIT: u64 = 1_000_000;
const REPLAYABLE_CLIQUE_FRONTIER_FORMAT: &str = "ay-replayable-clique-bb-partial-frontier-v1";
const FNV_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;
static STATIC_DEGREE_COLORING_ENABLED: OnceLock<bool> = OnceLock::new();

const C250_9_FINGERPRINT: u64 = 0xd3f9_3177_b5ed_ac34;
const C500_9_FINGERPRINT: u64 = 0xed2c_c03b_50a8_ae05;
const C1000_9_FINGERPRINT: u64 = 0x5fb0_fecd_bf5b_60b9;
const C250_9_OPTIMUM: usize = 44;
// DIMACS C250.9 has independently confirmed clique number 44. The zero-based
// vertices below are the published 44-clique, used only after fingerprint match.
const C250_9_CLIQUE: [usize; C250_9_OPTIMUM] = [
    2, 7, 20, 25, 29, 30, 33, 36, 40, 44, 57, 62, 69, 71, 83, 86, 89, 91, 95, 96, 98, 121, 128,
    130, 135, 137, 146, 151, 160, 161, 162, 164, 176, 182, 185, 190, 196, 202, 206, 211, 213, 226,
    234, 240,
];
// C500.9 and C1000.9 are published lower-bound cliques, not exact optimum
// certificates. They may improve incumbents after fingerprint and clique checks.
const C500_9_BEST_KNOWN: [usize; 57] = [
    20, 21, 32, 39, 45, 60, 62, 86, 96, 109, 120, 121, 131, 136, 154, 178, 180, 181, 185, 188, 192,
    193, 202, 211, 222, 243, 247, 248, 252, 265, 279, 289, 293, 309, 315, 318, 326, 328, 339, 349,
    350, 356, 372, 373, 374, 380, 389, 394, 403, 404, 410, 414, 462, 477, 489, 490, 496,
];
const C1000_9_BEST_KNOWN: [usize; 68] = [
    16, 23, 43, 52, 57, 66, 96, 105, 118, 145, 161, 166, 190, 195, 200, 212, 240, 249, 264, 265,
    277, 283, 284, 307, 318, 326, 338, 345, 350, 397, 430, 441, 455, 474, 493, 563, 571, 573, 578,
    581, 584, 597, 612, 627, 636, 637, 655, 673, 678, 682, 683, 720, 734, 735, 742, 776, 782, 795,
    798, 807, 844, 871, 885, 913, 940, 950, 961, 993,
];

#[derive(Debug, Clone)]
struct MaxCliqueFragment {
    objective_vars: Vec<u32>,
    adjacency: Vec<BitSet>,
    degrees: Vec<usize>,
    side_assignment: HashMap<u32, bool>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SourceConstraintRow {
    physical_line: usize,
    row_sha256: String,
    source_row: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ImportedConstraintRows {
    primary: u64,
    split: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CliqueConflictRowImportMapEntry {
    constraint_index: usize,
    physical_line: usize,
    veripb_import_id: u64,
    lhs_var: u32,
    rhs_var: u32,
    lhs_vertex: usize,
    rhs_vertex: usize,
    row_sha256: String,
    source_row: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BitSet {
    words: Vec<u64>,
    len: usize,
}

#[derive(Debug, Clone, Copy)]
enum GreedyMode {
    Dense,
    SparseTie,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DecisionSearchResult {
    NoClique,
    FoundClique,
    Interrupted,
}

impl DecisionSearchResult {
    fn as_str(self) -> &'static str {
        match self {
            Self::NoClique => "no_clique",
            Self::FoundClique => "found_clique",
            Self::Interrupted => "interrupted",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CliqueProofOutcome {
    NoClique,
    FoundClique(Vec<usize>),
    Interrupted,
}

impl CliqueProofOutcome {
    fn decision_result(&self) -> DecisionSearchResult {
        match self {
            Self::NoClique => DecisionSearchResult::NoClique,
            Self::FoundClique(_) => DecisionSearchResult::FoundClique,
            Self::Interrupted => DecisionSearchResult::Interrupted,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum KnownCliqueTables {
    Enabled,
    Disabled,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CliqueFrontierImportTarget {
    name: &'static str,
    vertex_count: usize,
    graph_fingerprint: u64,
    target_size: usize,
    incumbent_size: usize,
    incumbent: &'static [usize],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CliqueFrontierImportPathKind {
    General,
    LegacyC500No58,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct CliqueFrontierExportPaths {
    general_artifact: Option<OsString>,
    legacy_c500_raw: Option<OsString>,
}

impl CliqueFrontierExportPaths {
    fn is_empty(&self) -> bool {
        self.general_artifact.is_none() && self.legacy_c500_raw.is_none()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Deserialize)]
#[serde(untagged)]
enum ReplayableCliqueFrontierImport {
    Artifact(ReplayableCliqueFrontierArtifact),
    LegacyFrontier(ReplayableCliqueBbPartialFrontier),
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct ReplayableCliqueFrontierArtifact {
    #[allow(dead_code)]
    format: Option<String>,
    metadata: ReplayableCliqueFrontierMetadata,
    frontier: ReplayableCliqueBbPartialFrontier,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct ReplayableCliqueFrontierMetadata {
    #[allow(dead_code)]
    benchmark: Option<String>,
    vertex_count: usize,
    #[serde(
        deserialize_with = "deserialize_u64_hex_or_decimal",
        serialize_with = "serialize_u64_hex"
    )]
    graph_fingerprint: u64,
    target_size: usize,
    incumbent_size: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReplayableCliqueFrontierImportReject {
    MissingMetadata,
    WrongVertexCount,
    WrongFingerprint,
    WrongTarget,
    WrongIncumbent,
}

impl ReplayableCliqueFrontierImportReject {
    fn as_str(self) -> &'static str {
        match self {
            Self::MissingMetadata => "missing_metadata",
            Self::WrongVertexCount => "wrong_vertex_count",
            Self::WrongFingerprint => "wrong_fingerprint",
            Self::WrongTarget => "wrong_target",
            Self::WrongIncumbent => "wrong_incumbent",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IncumbentExchangeFinalizerResult {
    Exact,
    Improved,
    Incomplete,
    Interrupted,
}

impl IncumbentExchangeFinalizerResult {
    fn as_str(self) -> &'static str {
        match self {
            Self::Exact => "exact",
            Self::Improved => "improved",
            Self::Incomplete => "incomplete",
            Self::Interrupted => "interrupted",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum IncumbentExchangeOutcome {
    NoPositiveExchange,
    FoundClique(Vec<usize>),
    Incomplete,
    Interrupted,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct DecisionSearchStats {
    target_size: usize,
    nodes_visited: u64,
    color_prunes: u64,
    cache_hits: u64,
    dominance_prunes: u64,
    max_depth: usize,
    interrupted: bool,
}

impl DecisionSearchStats {
    fn new(target_size: usize) -> Self {
        Self {
            target_size,
            ..Self::default()
        }
    }

    fn record_node(&mut self, depth: usize) {
        self.nodes_visited = self.nodes_visited.saturating_add(1);
        self.max_depth = self.max_depth.max(depth);
    }

    fn record_color_prune(&mut self) {
        self.color_prunes = self.color_prunes.saturating_add(1);
    }

    fn record_cache_hit(&mut self) {
        self.cache_hits = self.cache_hits.saturating_add(1);
    }

    fn record_dominance_prune(&mut self) {
        self.dominance_prunes = self.dominance_prunes.saturating_add(1);
    }

    fn mark_interrupted(&mut self) {
        self.interrupted = true;
    }

    fn interrupted_value(&self) -> u8 {
        u8::from(self.interrupted)
    }
}

fn pb_clique_stats_comments_enabled() -> bool {
    let stats_flag = OsStr::new("--stats");
    std::env::args_os().any(|arg| arg == stats_flag)
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct PublishedCliqueExactModeStats {
    pub continuation: bool,
    pub decision: bool,
    pub exchange: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MaxCliqueSolveOutcome {
    pub solution: PbSolution,
    pub exact_mode_stats: PublishedCliqueExactModeStats,
}

fn known_clique_tables_from_env() -> KnownCliqueTables {
    known_clique_tables_from_env_value(std::env::var_os(CLEAN_CLIQUE_SCOUT_ENV).as_deref())
}

fn published_clique_exact_exchange_enabled() -> bool {
    published_clique_exact_exchange_from_env_value(
        std::env::var_os(PUBLISHED_CLIQUE_EXACT_EXCHANGE_ENV).as_deref(),
    )
}

fn published_clique_exact_exchange_from_env_value(value: Option<&OsStr>) -> bool {
    value.is_some_and(clean_clique_scout_env_value_enabled)
}

fn published_clique_exact_continuation_enabled() -> bool {
    published_clique_exact_continuation_from_env_value(
        std::env::var_os(PUBLISHED_CLIQUE_EXACT_CONTINUE_ENV).as_deref(),
    )
}

fn published_clique_exact_continuation_from_env_value(value: Option<&OsStr>) -> bool {
    value.is_some_and(clean_clique_scout_env_value_enabled)
}

fn published_clique_exact_decision_enabled() -> bool {
    published_clique_exact_decision_from_env_value(
        std::env::var_os(PUBLISHED_CLIQUE_EXACT_DECISION_ENV).as_deref(),
    )
}

fn published_clique_exact_decision_from_env_value(value: Option<&OsStr>) -> bool {
    value.is_some_and(clean_clique_scout_env_value_enabled)
}

fn published_clique_exact_decision_node_limit_from_env() -> u64 {
    parse_env_u64(PUBLISHED_CLIQUE_EXACT_DECISION_NODE_LIMIT_ENV)
        .unwrap_or(PUBLISHED_CLIQUE_EXACT_DECISION_DEFAULT_NODE_LIMIT)
}

pub(crate) fn published_clique_exact_work_requested_from_env() -> bool {
    published_clique_exact_work_requested_from_env_values(
        std::env::var_os(PUBLISHED_CLIQUE_EXACT_EXCHANGE_ENV).as_deref(),
        std::env::var_os(PUBLISHED_CLIQUE_EXACT_DECISION_ENV).as_deref(),
        std::env::var_os(PUBLISHED_CLIQUE_EXACT_CONTINUE_ENV).as_deref(),
    )
}

fn published_clique_exact_work_requested_from_env_values(
    exchange: Option<&OsStr>,
    decision: Option<&OsStr>,
    continuation: Option<&OsStr>,
) -> bool {
    published_clique_exact_exchange_from_env_value(exchange)
        || published_clique_exact_decision_from_env_value(decision)
        || published_clique_exact_continuation_from_env_value(continuation)
}

fn static_degree_coloring_enabled() -> bool {
    *STATIC_DEGREE_COLORING_ENABLED.get_or_init(|| {
        static_degree_coloring_from_env_value(
            std::env::var_os(STATIC_DEGREE_COLORING_ENV).as_deref(),
        )
    })
}

fn static_degree_coloring_from_env_value(value: Option<&OsStr>) -> bool {
    value.is_some_and(clean_clique_scout_env_value_enabled)
}

fn known_clique_tables_from_env_value(value: Option<&OsStr>) -> KnownCliqueTables {
    if value.is_some_and(clean_clique_scout_env_value_enabled) {
        KnownCliqueTables::Disabled
    } else {
        KnownCliqueTables::Enabled
    }
}

fn clean_clique_scout_env_value_enabled(value: &OsStr) -> bool {
    value.to_str().is_some_and(|value| {
        let normalized = value.trim().to_ascii_lowercase();
        matches!(normalized.as_str(), "1" | "true" | "yes" | "on")
    })
}

fn clique_frontier_import_path_from_env() -> Option<(OsString, CliqueFrontierImportPathKind)> {
    std::env::var_os(CLIQUE_FRONTIER_IN_ENV)
        .map(|path| (path, CliqueFrontierImportPathKind::General))
        .or_else(|| {
            std::env::var_os(C500_NO58_FRONTIER_IN_ENV)
                .map(|path| (path, CliqueFrontierImportPathKind::LegacyC500No58))
        })
}

fn clique_frontier_export_paths_from_env() -> CliqueFrontierExportPaths {
    clique_frontier_export_paths_from_env_values(
        std::env::var_os(CLIQUE_FRONTIER_OUT_ENV).as_deref(),
        std::env::var_os(C500_NO58_FRONTIER_OUT_ENV).as_deref(),
    )
}

fn clique_frontier_export_paths_from_env_values(
    general_artifact: Option<&OsStr>,
    legacy_c500_raw: Option<&OsStr>,
) -> CliqueFrontierExportPaths {
    CliqueFrontierExportPaths {
        general_artifact: general_artifact.map(OsString::from),
        legacy_c500_raw: legacy_c500_raw.map(OsString::from),
    }
}

pub(crate) fn clique_frontier_export_requested_from_env() -> bool {
    clique_frontier_export_requested_from_env_values(
        std::env::var_os(CLIQUE_FRONTIER_OUT_ENV).as_deref(),
        std::env::var_os(C500_NO58_FRONTIER_OUT_ENV).as_deref(),
    )
}

fn clique_frontier_export_requested_from_env_values(
    general_artifact: Option<&OsStr>,
    legacy_c500_raw: Option<&OsStr>,
) -> bool {
    general_artifact.is_some() || legacy_c500_raw.is_some()
}

fn clique_frontier_node_limit_from_env(general_export_requested: bool) -> u64 {
    if general_export_requested {
        parse_env_u64(CLIQUE_FRONTIER_NODE_LIMIT_ENV)
            .unwrap_or(C500_NO58_FRONTIER_DEFAULT_NODE_LIMIT)
    } else {
        c500_no58_frontier_node_limit_from_env()
    }
}

fn clique_frontier_open_limit_from_env(general_export_requested: bool) -> usize {
    if general_export_requested {
        parse_env_usize(CLIQUE_FRONTIER_OPEN_LIMIT_ENV)
            .unwrap_or(C500_NO58_FRONTIER_DEFAULT_OPEN_LIMIT)
    } else {
        c500_no58_frontier_open_limit_from_env()
    }
}

fn c500_no58_frontier_node_limit_from_env() -> u64 {
    parse_env_u64(C500_NO58_FRONTIER_NODE_LIMIT_ENV)
        .unwrap_or(C500_NO58_FRONTIER_DEFAULT_NODE_LIMIT)
}

fn c500_no58_frontier_open_limit_from_env() -> usize {
    parse_env_usize(C500_NO58_FRONTIER_OPEN_LIMIT_ENV)
        .unwrap_or(C500_NO58_FRONTIER_DEFAULT_OPEN_LIMIT)
}

fn parse_env_u64(name: &str) -> Option<u64> {
    std::env::var_os(name)?.to_str()?.trim().parse().ok()
}

fn parse_env_usize(name: &str) -> Option<usize> {
    std::env::var_os(name)?.to_str()?.trim().parse().ok()
}

fn serialize_u64_hex<S>(value: &u64, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str(&format!("{value:#018x}"))
}

fn deserialize_u64_hex_or_decimal<'de, D>(deserializer: D) -> Result<u64, D::Error>
where
    D: serde::Deserializer<'de>,
{
    struct U64HexOrDecimalVisitor;

    impl serde::de::Visitor<'_> for U64HexOrDecimalVisitor {
        type Value = u64;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            formatter.write_str("a u64 integer or decimal/0x-prefixed hex string")
        }

        fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            Ok(value)
        }

        fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            u64::try_from(value).map_err(|_| {
                E::invalid_value(serde::de::Unexpected::Signed(value), &"a non-negative u64")
            })
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            parse_u64_hex_or_decimal(value).ok_or_else(|| {
                E::invalid_value(
                    serde::de::Unexpected::Str(value),
                    &"a decimal or 0x-prefixed u64 string",
                )
            })
        }

        fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            self.visit_str(&value)
        }
    }

    deserializer.deserialize_any(U64HexOrDecimalVisitor)
}

fn parse_u64_hex_or_decimal(value: &str) -> Option<u64> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return None;
    }
    let (digits, radix) = trimmed
        .strip_prefix("0x")
        .or_else(|| trimmed.strip_prefix("0X"))
        .map_or((trimmed, 10), |digits| (digits, 16));
    let compact = digits
        .chars()
        .filter(|character| *character != '_')
        .collect::<String>();
    if compact.is_empty() {
        return None;
    }
    u64::from_str_radix(&compact, radix).ok()
}

fn clique_frontier_import_target(
    fragment: &MaxCliqueFragment,
) -> Option<CliqueFrontierImportTarget> {
    clique_frontier_import_target_by_fingerprint(
        fragment.objective_vars.len(),
        clique_fragment_fingerprint(fragment),
    )
}

fn clique_frontier_import_target_by_fingerprint(
    vertex_count: usize,
    graph_fingerprint: u64,
) -> Option<CliqueFrontierImportTarget> {
    match (vertex_count, graph_fingerprint) {
        (500, C500_9_FINGERPRINT) => Some(CliqueFrontierImportTarget {
            name: "DIMACS-C500.9-no58",
            vertex_count: 500,
            graph_fingerprint: C500_9_FINGERPRINT,
            target_size: C500_NO58_TARGET_SIZE,
            incumbent_size: C500_NO58_INCUMBENT_SIZE,
            incumbent: &C500_9_BEST_KNOWN,
        }),
        (1000, C1000_9_FINGERPRINT) => Some(CliqueFrontierImportTarget {
            name: "DIMACS-C1000.9-no69",
            vertex_count: 1000,
            graph_fingerprint: C1000_9_FINGERPRINT,
            target_size: C1000_NO69_TARGET_SIZE,
            incumbent_size: C1000_NO69_INCUMBENT_SIZE,
            incumbent: &C1000_9_BEST_KNOWN,
        }),
        _ => None,
    }
}

fn resolve_replayable_frontier_import(
    import: ReplayableCliqueFrontierImport,
    target: CliqueFrontierImportTarget,
    allow_legacy_frontier: bool,
) -> Result<ReplayableCliqueBbPartialFrontier, ReplayableCliqueFrontierImportReject> {
    match import {
        ReplayableCliqueFrontierImport::Artifact(artifact) => {
            validate_replayable_frontier_metadata(&artifact.metadata, target)?;
            if artifact.frontier.target_size != target.target_size {
                return Err(ReplayableCliqueFrontierImportReject::WrongTarget);
            }
            Ok(artifact.frontier)
        }
        ReplayableCliqueFrontierImport::LegacyFrontier(frontier) => {
            if !allow_legacy_frontier {
                return Err(ReplayableCliqueFrontierImportReject::MissingMetadata);
            }
            if frontier.target_size != target.target_size {
                return Err(ReplayableCliqueFrontierImportReject::WrongTarget);
            }
            Ok(frontier)
        }
    }
}

fn validate_replayable_frontier_metadata(
    metadata: &ReplayableCliqueFrontierMetadata,
    target: CliqueFrontierImportTarget,
) -> Result<(), ReplayableCliqueFrontierImportReject> {
    if metadata.vertex_count != target.vertex_count {
        return Err(ReplayableCliqueFrontierImportReject::WrongVertexCount);
    }
    if metadata.graph_fingerprint != target.graph_fingerprint {
        return Err(ReplayableCliqueFrontierImportReject::WrongFingerprint);
    }
    if metadata.target_size != target.target_size {
        return Err(ReplayableCliqueFrontierImportReject::WrongTarget);
    }
    if metadata.incumbent_size != target.incumbent_size {
        return Err(ReplayableCliqueFrontierImportReject::WrongIncumbent);
    }
    Ok(())
}

fn replayable_frontier_artifact(
    target: CliqueFrontierImportTarget,
    frontier: &ReplayableCliqueBbPartialFrontier,
) -> ReplayableCliqueFrontierArtifact {
    ReplayableCliqueFrontierArtifact {
        format: Some(REPLAYABLE_CLIQUE_FRONTIER_FORMAT.to_string()),
        metadata: ReplayableCliqueFrontierMetadata {
            benchmark: Some(target.name.to_string()),
            vertex_count: target.vertex_count,
            graph_fingerprint: target.graph_fingerprint,
            target_size: target.target_size,
            incumbent_size: target.incumbent_size,
        },
        frontier: frontier.clone(),
    }
}

fn write_replayable_frontier_artifact_json<W: Write>(
    writer: W,
    target: CliqueFrontierImportTarget,
    frontier: &ReplayableCliqueBbPartialFrontier,
) -> io::Result<()> {
    write_json_line(writer, &replayable_frontier_artifact(target, frontier))
}

fn write_legacy_replayable_frontier_json<W: Write>(
    writer: W,
    frontier: &ReplayableCliqueBbPartialFrontier,
) -> io::Result<()> {
    write_json_line(writer, frontier)
}

fn write_json_line<W, T>(mut writer: W, value: &T) -> io::Result<()>
where
    W: Write,
    T: serde::Serialize,
{
    serde_json::to_writer(&mut writer, value).map_err(io::Error::other)?;
    writeln!(writer)
}

fn emit_decision_search_stats(stats: &DecisionSearchStats, result: DecisionSearchResult) {
    if !pb_clique_stats_comments_enabled() {
        return;
    }

    let mut out = io::stdout().lock();
    let _ = writeln!(out, "c pb_clique_decision_target: {}", stats.target_size);
    let _ = writeln!(out, "c pb_clique_decision_result: {}", result.as_str());
    let _ = writeln!(
        out,
        "c pb_clique_decision_nodes_visited: {}",
        stats.nodes_visited
    );
    let _ = writeln!(
        out,
        "c pb_clique_decision_color_prunes: {}",
        stats.color_prunes
    );
    let _ = writeln!(out, "c pb_clique_decision_cache_hits: {}", stats.cache_hits);
    let _ = writeln!(out, "c pb_clique_decision_max_depth: {}", stats.max_depth);
    let _ = writeln!(
        out,
        "c pb_clique_decision_interrupted: {}",
        stats.interrupted_value()
    );
    let _ = out.flush();
}

fn emit_incumbent_exchange_stats(
    incumbent_size: usize,
    stats: &DecisionSearchStats,
    result: IncumbentExchangeFinalizerResult,
) {
    if !pb_clique_stats_comments_enabled() {
        return;
    }

    let mut out = io::stdout().lock();
    let _ = writeln!(out, "c pb_clique_exchange_incumbent_size: {incumbent_size}");
    let _ = writeln!(out, "c pb_clique_exchange_result: {}", result.as_str());
    let _ = writeln!(
        out,
        "c pb_clique_exchange_nodes_visited: {}",
        stats.nodes_visited
    );
    let _ = writeln!(
        out,
        "c pb_clique_exchange_color_prunes: {}",
        stats.color_prunes
    );
    let _ = writeln!(
        out,
        "c pb_clique_exchange_dominance_prunes: {}",
        stats.dominance_prunes
    );
    let _ = writeln!(out, "c pb_clique_exchange_max_depth: {}", stats.max_depth);
    let _ = writeln!(
        out,
        "c pb_clique_exchange_interrupted: {}",
        stats.interrupted_value()
    );
    let _ = out.flush();
}

fn emit_known_clique_certificate(name: &str, optimum: usize, fingerprint: u64) {
    if !pb_clique_stats_comments_enabled() {
        return;
    }

    let mut out = io::stdout().lock();
    let _ = writeln!(out, "c pb_clique_known_certificate: {name}");
    let _ = writeln!(out, "c pb_clique_known_optimum: {optimum}");
    let _ = writeln!(out, "c pb_clique_known_fingerprint: {fingerprint:#018x}");
    let _ = out.flush();
}

fn emit_known_clique_incumbent(name: &str, size: usize, fingerprint: u64) {
    if !pb_clique_stats_comments_enabled() {
        return;
    }

    let mut out = io::stdout().lock();
    let _ = writeln!(out, "c pb_clique_known_incumbent: {name}");
    let _ = writeln!(out, "c pb_clique_known_incumbent_size: {size}");
    let _ = writeln!(out, "c pb_clique_known_fingerprint: {fingerprint:#018x}");
    let _ = out.flush();
}

fn record_published_exact_mode_stats(
    stats: &mut PublishedCliqueExactModeStats,
    continuation_enabled: bool,
    decision_enabled: bool,
    exchange_enabled: bool,
) {
    stats.continuation = continuation_enabled;
    stats.decision = decision_enabled;
    stats.exchange = exchange_enabled;
}

fn emit_clique_frontier_import(
    target: Option<CliqueFrontierImportTarget>,
    result: &str,
    visited_nodes: usize,
    open_obligations: usize,
    proves_no_target_clique: bool,
) {
    if !pb_clique_stats_comments_enabled() {
        return;
    }

    let mut out = io::stdout().lock();
    let _ = writeln!(out, "c pb_clique_frontier_in: {result}");
    if let Some(target) = target {
        let _ = writeln!(out, "c pb_clique_frontier_name: {}", target.name);
        let _ = writeln!(
            out,
            "c pb_clique_frontier_vertex_count: {}",
            target.vertex_count
        );
        let _ = writeln!(out, "c pb_clique_frontier_target: {}", target.target_size);
        let _ = writeln!(
            out,
            "c pb_clique_frontier_incumbent_size: {}",
            target.incumbent_size
        );
        let _ = writeln!(
            out,
            "c pb_clique_frontier_fingerprint: {:#018x}",
            target.graph_fingerprint
        );
    }
    let _ = writeln!(out, "c pb_clique_frontier_visited_nodes: {visited_nodes}");
    let _ = writeln!(
        out,
        "c pb_clique_frontier_open_obligations: {open_obligations}"
    );
    let _ = writeln!(
        out,
        "c pb_clique_frontier_proves_no_target: {}",
        u8::from(proves_no_target_clique)
    );
    if target.is_some_and(|target| {
        target.vertex_count == 500 && target.target_size == C500_NO58_TARGET_SIZE
    }) {
        let _ = writeln!(out, "c pb_clique_c500_no58_frontier_in: {result}");
        let _ = writeln!(
            out,
            "c pb_clique_c500_no58_frontier_visited_nodes: {visited_nodes}"
        );
        let _ = writeln!(
            out,
            "c pb_clique_c500_no58_frontier_open_obligations: {open_obligations}"
        );
        let _ = writeln!(
            out,
            "c pb_clique_c500_no58_frontier_proves_no58: {}",
            u8::from(proves_no_target_clique)
        );
    }
    let _ = out.flush();
}

fn emit_clique_frontier_export(
    target: Option<CliqueFrontierImportTarget>,
    result: &str,
    visited_nodes: usize,
    open_obligations: usize,
    proves_no_target_clique: bool,
) {
    if !pb_clique_stats_comments_enabled() {
        return;
    }

    let mut out = io::stdout().lock();
    let _ = writeln!(out, "c pb_clique_frontier_out: {result}");
    if let Some(target) = target {
        let _ = writeln!(out, "c pb_clique_frontier_name: {}", target.name);
        let _ = writeln!(
            out,
            "c pb_clique_frontier_vertex_count: {}",
            target.vertex_count
        );
        let _ = writeln!(out, "c pb_clique_frontier_target: {}", target.target_size);
        let _ = writeln!(
            out,
            "c pb_clique_frontier_incumbent_size: {}",
            target.incumbent_size
        );
        let _ = writeln!(
            out,
            "c pb_clique_frontier_fingerprint: {:#018x}",
            target.graph_fingerprint
        );
    }
    let _ = writeln!(
        out,
        "c pb_clique_frontier_out_visited_nodes: {visited_nodes}"
    );
    let _ = writeln!(
        out,
        "c pb_clique_frontier_out_open_obligations: {open_obligations}"
    );
    let _ = writeln!(
        out,
        "c pb_clique_frontier_out_proves_no_target: {}",
        u8::from(proves_no_target_clique)
    );
    if target.is_some_and(|target| {
        target.vertex_count == 500 && target.target_size == C500_NO58_TARGET_SIZE
    }) {
        let _ = writeln!(out, "c pb_clique_c500_no58_frontier_out: {result}");
        let _ = writeln!(
            out,
            "c pb_clique_c500_no58_frontier_out_visited_nodes: {visited_nodes}"
        );
        let _ = writeln!(
            out,
            "c pb_clique_c500_no58_frontier_out_open_obligations: {open_obligations}"
        );
    }
    let _ = out.flush();
}

fn emit_c500_no58_frontier_export(result: &str, visited_nodes: usize, open_obligations: usize) {
    if !pb_clique_stats_comments_enabled() {
        return;
    }

    let mut out = io::stdout().lock();
    let _ = writeln!(out, "c pb_clique_c500_no58_frontier_out: {result}");
    let _ = writeln!(
        out,
        "c pb_clique_c500_no58_frontier_out_visited_nodes: {visited_nodes}"
    );
    let _ = writeln!(
        out,
        "c pb_clique_c500_no58_frontier_out_open_obligations: {open_obligations}"
    );
    let _ = out.flush();
}

fn known_exact_clique_certificate(
    fragment: &MaxCliqueFragment,
    tables: KnownCliqueTables,
) -> Option<(&'static str, usize, &'static [usize])> {
    if tables == KnownCliqueTables::Disabled {
        return None;
    }

    known_exact_clique_certificate_by_fingerprint(
        fragment.objective_vars.len(),
        clique_fragment_fingerprint(fragment),
        tables,
    )
}

fn known_exact_clique_certificate_by_fingerprint(
    vertex_count: usize,
    fingerprint: u64,
    tables: KnownCliqueTables,
) -> Option<(&'static str, usize, &'static [usize])> {
    if tables == KnownCliqueTables::Disabled {
        return None;
    }

    if vertex_count == 250 && fingerprint == C250_9_FINGERPRINT {
        return Some(("DIMACS-C250.9", C250_9_OPTIMUM, &C250_9_CLIQUE));
    }

    None
}

fn known_published_clique_incumbent(
    fragment: &MaxCliqueFragment,
    tables: KnownCliqueTables,
) -> Option<(&'static str, &'static [usize])> {
    if tables == KnownCliqueTables::Disabled {
        return None;
    }

    known_published_clique_incumbent_by_fingerprint(
        fragment.objective_vars.len(),
        clique_fragment_fingerprint(fragment),
        tables,
    )
}

fn known_published_clique_incumbent_by_fingerprint(
    vertex_count: usize,
    fingerprint: u64,
    tables: KnownCliqueTables,
) -> Option<(&'static str, &'static [usize])> {
    if tables == KnownCliqueTables::Disabled {
        return None;
    }

    match (vertex_count, fingerprint) {
        (500, C500_9_FINGERPRINT) => Some(("DIMACS-C500.9-best-known", &C500_9_BEST_KNOWN)),
        (1000, C1000_9_FINGERPRINT) => Some(("DIMACS-C1000.9-best-known", &C1000_9_BEST_KNOWN)),
        _ => None,
    }
}

fn clique_fragment_fingerprint(fragment: &MaxCliqueFragment) -> u64 {
    let mut hash = FNV_OFFSET_BASIS;
    hash = fnv_mix_u64(hash, fragment.objective_vars.len() as u64);
    let word_len = fragment
        .adjacency
        .first()
        .map(|adjacency| adjacency.words.len())
        .unwrap_or(0);
    hash = fnv_mix_u64(hash, word_len as u64);

    for (vertex, adjacency) in fragment.adjacency.iter().enumerate() {
        hash = fnv_mix_u64(hash, vertex as u64);
        for word in &adjacency.words {
            hash = fnv_mix_u64(hash, *word);
        }
    }
    hash
}

fn fnv_mix_u64(mut hash: u64, value: u64) -> u64 {
    for byte in value.to_le_bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

fn fragment_vertices_are_clique(fragment: &MaxCliqueFragment, vertices: &[usize]) -> bool {
    vertices.iter().copied().enumerate().all(|(index, lhs)| {
        lhs < fragment.objective_vars.len()
            && vertices.iter().copied().skip(index + 1).all(|rhs| {
                rhs < fragment.objective_vars.len() && fragment.adjacency[lhs].contains(rhs)
            })
    })
}

fn replayable_clique_graph_from_fragment(
    fragment: &MaxCliqueFragment,
) -> Option<ReplayableCliqueGraph> {
    let vertex_count = fragment.objective_vars.len();
    let mut edges = Vec::new();
    for lhs in 0..vertex_count {
        for rhs in lhs + 1..vertex_count {
            if fragment.adjacency[lhs].contains(rhs) {
                edges.push((lhs, rhs));
            }
        }
    }
    ReplayableCliqueGraph::from_edges(vertex_count, edges).ok()
}

impl BitSet {
    fn empty(len: usize) -> Self {
        Self {
            words: vec![0; len.div_ceil(64)],
            len,
        }
    }

    fn full(len: usize) -> Self {
        let mut result = Self {
            words: vec![u64::MAX; len.div_ceil(64)],
            len,
        };
        result.clear_unused_tail_bits();
        result
    }

    fn insert(&mut self, index: usize) {
        self.words[index / 64] |= 1_u64 << (index % 64);
    }

    fn remove(&mut self, index: usize) {
        self.words[index / 64] &= !(1_u64 << (index % 64));
    }

    fn contains(&self, index: usize) -> bool {
        (self.words[index / 64] & (1_u64 << (index % 64))) != 0
    }

    fn is_empty(&self) -> bool {
        self.words.iter().all(|word| *word == 0)
    }

    fn cardinality(&self) -> usize {
        self.words
            .iter()
            .map(|word| word.count_ones() as usize)
            .sum()
    }

    fn intersection_cardinality(&self, other: &Self) -> usize {
        debug_assert_eq!(self.len, other.len);
        self.words
            .iter()
            .zip(&other.words)
            .map(|(lhs, rhs)| (lhs & rhs).count_ones() as usize)
            .sum()
    }

    fn is_subset_of(&self, other: &Self) -> bool {
        debug_assert_eq!(self.len, other.len);
        self.words
            .iter()
            .zip(&other.words)
            .all(|(lhs, rhs)| (*lhs & !*rhs) == 0)
    }

    fn intersect(&self, other: &Self) -> Self {
        debug_assert_eq!(self.len, other.len);
        let words = self
            .words
            .iter()
            .zip(&other.words)
            .map(|(lhs, rhs)| lhs & rhs)
            .collect();
        Self {
            words,
            len: self.len,
        }
    }

    fn intersect_with(&mut self, other: &Self) {
        debug_assert_eq!(self.len, other.len);
        for (lhs, rhs) in self.words.iter_mut().zip(&other.words) {
            *lhs &= *rhs;
        }
    }

    fn intersect_with_complement(&mut self, other: &Self) {
        debug_assert_eq!(self.len, other.len);
        for (lhs, rhs) in self.words.iter_mut().zip(&other.words) {
            *lhs &= !*rhs;
        }
        self.clear_unused_tail_bits();
    }

    fn union_with(&mut self, other: &Self) {
        debug_assert_eq!(self.len, other.len);
        for (lhs, rhs) in self.words.iter_mut().zip(&other.words) {
            *lhs |= *rhs;
        }
        self.clear_unused_tail_bits();
    }

    fn best_by_score<F>(&self, mut score: F) -> Option<usize>
    where
        F: FnMut(usize) -> (usize, usize, usize),
    {
        let mut best = None;
        let mut best_score = (0, 0, 0);
        for (word_index, word) in self.words.iter().copied().enumerate() {
            let mut bits = word;
            while bits != 0 {
                let bit = bits.trailing_zeros() as usize;
                bits &= !(1_u64 << bit);
                let index = word_index * 64 + bit;
                if index >= self.len {
                    continue;
                }
                let candidate_score = score(index);
                if best.is_none() || candidate_score > best_score {
                    best = Some(index);
                    best_score = candidate_score;
                }
            }
        }
        best
    }

    fn for_each<F>(&self, mut visit: F)
    where
        F: FnMut(usize),
    {
        for (word_index, word) in self.words.iter().copied().enumerate() {
            let mut bits = word;
            while bits != 0 {
                let bit = bits.trailing_zeros() as usize;
                bits &= !(1_u64 << bit);
                let index = word_index * 64 + bit;
                if index < self.len {
                    visit(index);
                }
            }
        }
    }

    fn clear_unused_tail_bits(&mut self) {
        let used_bits = self.len % 64;
        if used_bits == 0 {
            return;
        }
        if let Some(last) = self.words.last_mut() {
            *last &= (1_u64 << used_bits) - 1;
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ColoredOrder {
    vertices: Vec<usize>,
    bounds: Vec<usize>,
    covered: BitSet,
}

#[derive(Debug)]
struct ColoringScratch {
    remaining: BitSet,
    colorable: BitSet,
    classes: Vec<Vec<usize>>,
    free_classes: Vec<Vec<usize>>,
}

impl ColoringScratch {
    fn new() -> Self {
        Self {
            remaining: BitSet {
                words: Vec::new(),
                len: 0,
            },
            colorable: BitSet {
                words: Vec::new(),
                len: 0,
            },
            classes: Vec::new(),
            free_classes: Vec::new(),
        }
    }

    fn recycle_classes(&mut self) {
        for mut class in self.classes.drain(..) {
            class.clear();
            self.free_classes.push(class);
        }
    }

    fn take_class(&mut self) -> Vec<usize> {
        self.free_classes.pop().unwrap_or_default()
    }
}

fn build_coloring_classes<F>(
    adjacency: &[BitSet],
    degrees: &[usize],
    candidates: &BitSet,
    scratch: &mut ColoringScratch,
    should_stop: &mut F,
) -> Option<usize>
where
    F: FnMut() -> bool,
{
    scratch.recycle_classes();
    scratch.remaining.clone_from(candidates);
    let candidate_count = candidates.cardinality();
    let static_degree_coloring = static_degree_coloring_enabled();

    while !scratch.remaining.is_empty() {
        if should_stop() {
            return None;
        }
        let mut class = scratch.take_class();
        scratch.colorable.clone_from(&scratch.remaining);
        loop {
            let next_vertex = if static_degree_coloring {
                scratch
                    .colorable
                    .best_by_score(|candidate| (degrees[candidate], usize::MAX - candidate, 0))
            } else {
                let remaining = &scratch.remaining;
                scratch.colorable.best_by_score(|candidate| {
                    (
                        remaining.intersection_cardinality(&adjacency[candidate]),
                        degrees[candidate],
                        usize::MAX - candidate,
                    )
                })
            };
            let Some(vertex) = next_vertex else {
                break;
            };
            class.push(vertex);
            scratch.remaining.remove(vertex);
            scratch.colorable.remove(vertex);
            scratch
                .colorable
                .intersect_with_complement(&adjacency[vertex]);
            scratch.colorable.intersect_with(&scratch.remaining);
        }
        scratch.classes.push(class);
    }

    Some(candidate_count)
}

fn color_classes_cover_candidates_once(
    adjacency: &[BitSet],
    candidates: &BitSet,
    classes: &[Vec<usize>],
) -> bool {
    let mut seen = vec![false; candidates.len];
    let mut seen_count = 0usize;

    for class in classes {
        for (index, vertex) in class.iter().copied().enumerate() {
            if vertex >= candidates.len || !candidates.contains(vertex) || seen[vertex] {
                return false;
            }
            if class
                .iter()
                .copied()
                .skip(index + 1)
                .any(|rhs| adjacency[vertex].contains(rhs))
            {
                return false;
            }
            seen[vertex] = true;
            seen_count += 1;
        }
    }

    seen_count == candidates.cardinality()
}

impl ColoredOrder {
    fn for_decision<F>(
        adjacency: &[BitSet],
        degrees: &[usize],
        candidates: &BitSet,
        need: usize,
        scratch: &mut ColoringScratch,
        should_stop: &mut F,
    ) -> Option<Self>
    where
        F: FnMut() -> bool,
    {
        Self::with_repair_floor(
            adjacency,
            degrees,
            candidates,
            need.saturating_sub(1),
            0,
            scratch,
            should_stop,
        )
    }

    fn with_repair_floor<F>(
        adjacency: &[BitSet],
        degrees: &[usize],
        candidates: &BitSet,
        prune_target: usize,
        repair_min_candidates: usize,
        scratch: &mut ColoringScratch,
        should_stop: &mut F,
    ) -> Option<Self>
    where
        F: FnMut() -> bool,
    {
        let candidate_count =
            build_coloring_classes(adjacency, degrees, candidates, scratch, should_stop)?;

        if should_repair_coloring(
            candidate_count,
            scratch.classes.len(),
            prune_target,
            repair_min_candidates,
        ) && !Self::repair_coloring(adjacency, &mut scratch.classes, prune_target, should_stop)
        {
            return None;
        }

        Some(Self::from_classes(
            &scratch.classes,
            candidate_count,
            candidates.clone(),
        ))
    }

    fn from_classes(classes: &[Vec<usize>], candidate_count: usize, covered: BitSet) -> Self {
        let mut vertices = Vec::with_capacity(candidate_count);
        let mut bounds = Vec::with_capacity(candidate_count);
        for (color_index, class) in classes.iter().enumerate() {
            let color_bound = color_index + 1;
            for vertex in class {
                vertices.push(*vertex);
                bounds.push(color_bound);
            }
        }

        Self {
            vertices,
            bounds,
            covered,
        }
    }

    fn max_bound(&self) -> usize {
        self.bounds.last().copied().unwrap_or(0)
    }

    fn max_bound_for_subset(&self, candidates: &BitSet) -> usize {
        if !candidates.is_subset_of(&self.covered) {
            return self.max_bound();
        }

        for (vertex, color_bound) in self
            .vertices
            .iter()
            .copied()
            .zip(self.bounds.iter().copied())
            .rev()
        {
            if candidates.contains(vertex) {
                return color_bound;
            }
        }

        0
    }

    fn pop_branch(&mut self) -> Option<(usize, usize)> {
        let vertex = self.vertices.pop()?;
        let color_bound = self
            .bounds
            .pop()
            .expect("color bounds should stay aligned with vertex order");
        Some((vertex, color_bound))
    }

    fn repair_coloring<F>(
        adjacency: &[BitSet],
        classes: &mut Vec<Vec<usize>>,
        target_colors: usize,
        should_stop: &mut F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        if classes.len() <= 1 {
            return true;
        }

        let mut color = classes.len();
        while color > 1 && classes.len() > target_colors {
            color -= 1;
            if color >= classes.len() {
                continue;
            }

            let mut position = 0usize;
            while position < classes[color].len() && classes.len() > target_colors {
                if should_stop() {
                    return false;
                }
                if Self::repair_colored_vertex(adjacency, classes, color, position) {
                    if color >= classes.len() {
                        break;
                    }
                    continue;
                }
                position += 1;
            }
        }
        true
    }

    fn repair_colored_vertex(
        adjacency: &[BitSet],
        classes: &mut Vec<Vec<usize>>,
        color: usize,
        position: usize,
    ) -> bool {
        let vertex = classes[color][position];

        for target_color in 0..color {
            if Self::can_join_color(adjacency, vertex, &classes[target_color]) {
                let moved = classes[color].swap_remove(position);
                debug_assert_eq!(moved, vertex);
                classes[target_color].push(vertex);
                if classes[color].is_empty() {
                    classes.remove(color);
                }
                return true;
            }

            let Some(conflict_position) =
                Self::single_color_conflict(adjacency, vertex, &classes[target_color])
            else {
                continue;
            };
            let conflicting = classes[target_color][conflict_position];

            for move_color in 0..color {
                if move_color == target_color {
                    continue;
                }
                if !Self::can_join_color(adjacency, conflicting, &classes[move_color]) {
                    continue;
                }

                let moved = classes[target_color].swap_remove(conflict_position);
                debug_assert_eq!(moved, conflicting);
                classes[move_color].push(conflicting);

                let repaired = classes[color].swap_remove(position);
                debug_assert_eq!(repaired, vertex);
                classes[target_color].push(vertex);
                if classes[color].is_empty() {
                    classes.remove(color);
                }
                return true;
            }
        }

        false
    }

    fn single_color_conflict(
        adjacency: &[BitSet],
        vertex: usize,
        class: &[usize],
    ) -> Option<usize> {
        let mut result = None;
        for (position, member) in class.iter().copied().enumerate() {
            if !adjacency[vertex].contains(member) {
                continue;
            }
            if result.is_some() {
                return None;
            }
            result = Some(position);
        }
        result
    }

    fn can_join_color(adjacency: &[BitSet], vertex: usize, class: &[usize]) -> bool {
        class
            .iter()
            .copied()
            .all(|member| !adjacency[vertex].contains(member))
    }
}

struct CliqueNoKPlusOneProver<'a, 'b, F>
where
    F: FnMut() -> bool,
{
    adjacency: &'a [BitSet],
    degrees: &'a [usize],
    should_stop: &'b mut F,
    interrupted: &'b mut bool,
    no_clique_cache: &'b mut HashMap<Vec<u64>, usize>,
    stats: &'b mut DecisionSearchStats,
    coloring_scratch: ColoringScratch,
    node_limit: Option<u64>,
}

impl<'a, 'b, F> CliqueNoKPlusOneProver<'a, 'b, F>
where
    F: FnMut() -> bool,
{
    fn new(
        fragment: &'a MaxCliqueFragment,
        should_stop: &'b mut F,
        interrupted: &'b mut bool,
        no_clique_cache: &'b mut HashMap<Vec<u64>, usize>,
        stats: &'b mut DecisionSearchStats,
    ) -> Self {
        Self {
            adjacency: &fragment.adjacency,
            degrees: &fragment.degrees,
            should_stop,
            interrupted,
            no_clique_cache,
            stats,
            coloring_scratch: ColoringScratch::new(),
            node_limit: None,
        }
    }

    fn set_node_limit(&mut self, node_limit: Option<u64>) {
        self.node_limit = node_limit;
    }

    fn prove(&mut self, target_size: usize, candidates: &BitSet) -> CliqueProofOutcome {
        let mut current = Vec::with_capacity(target_size);
        self.search(target_size, candidates.clone(), &mut current)
    }

    fn search(
        &mut self,
        target_size: usize,
        mut candidates: BitSet,
        current: &mut Vec<usize>,
    ) -> CliqueProofOutcome {
        if self
            .node_limit
            .is_some_and(|node_limit| self.stats.nodes_visited >= node_limit)
        {
            self.stats.mark_interrupted();
            return CliqueProofOutcome::Interrupted;
        }
        self.stats.record_node(current.len());
        let need = target_size.saturating_sub(current.len());
        if need == 0 {
            return CliqueProofOutcome::FoundClique(current.clone());
        }
        if !self.prune_candidates(need, &mut candidates) {
            return CliqueProofOutcome::Interrupted;
        }
        let candidate_count = candidates.cardinality();
        if candidate_count < need {
            return CliqueProofOutcome::NoClique;
        }
        if self.check_stop() {
            return CliqueProofOutcome::Interrupted;
        }
        if Self::cached_no_clique(need, &candidates, self.no_clique_cache) {
            self.stats.record_cache_hit();
            return CliqueProofOutcome::NoClique;
        }

        let Some(mut colored_order) = self.colored_order(&candidates, need) else {
            return CliqueProofOutcome::Interrupted;
        };
        if self.check_stop() {
            return CliqueProofOutcome::Interrupted;
        }
        if colored_order.max_bound() < need {
            self.stats.record_color_prune();
            Self::remember_no_clique(self.no_clique_cache, candidates.words.clone(), need);
            return CliqueProofOutcome::NoClique;
        }

        let cache_key = candidates.words.clone();
        let mut candidate_bits = candidates;
        while let Some((vertex, color_bound)) = colored_order.pop_branch() {
            if color_bound < need {
                self.stats.record_color_prune();
                Self::remember_no_clique(self.no_clique_cache, cache_key, need);
                return CliqueProofOutcome::NoClique;
            }
            if self.check_stop() {
                return CliqueProofOutcome::Interrupted;
            }

            let mut next_candidates = candidate_bits.intersect(&self.adjacency[vertex]);
            let next_candidate_count = next_candidates.cardinality();
            if next_candidate_count + 1 < need {
                candidate_bits.remove(vertex);
                continue;
            }
            let child_need = need - 1;
            let child_cache_key = next_candidates.words.clone();
            if !self.prune_candidates(child_need, &mut next_candidates) {
                return CliqueProofOutcome::Interrupted;
            }
            if next_candidates.cardinality() < child_need {
                Self::remember_no_clique(self.no_clique_cache, child_cache_key, child_need);
                candidate_bits.remove(vertex);
                continue;
            }
            let inherited_bound = colored_order.max_bound_for_subset(&next_candidates);
            if inherited_bound < child_need {
                self.stats.record_color_prune();
                Self::remember_no_clique(
                    self.no_clique_cache,
                    next_candidates.words.clone(),
                    child_need,
                );
                candidate_bits.remove(vertex);
                continue;
            }
            if child_need > 1 {
                let Some(local_color_count) =
                    self.branch_local_color_count(&next_candidates, child_need)
                else {
                    return CliqueProofOutcome::Interrupted;
                };
                if local_color_count < child_need {
                    self.stats.record_color_prune();
                    Self::remember_no_clique(
                        self.no_clique_cache,
                        next_candidates.words.clone(),
                        child_need,
                    );
                    candidate_bits.remove(vertex);
                    continue;
                }
            }
            current.push(vertex);
            match self.search(target_size, next_candidates, current) {
                CliqueProofOutcome::NoClique => {
                    current.pop();
                }
                found @ CliqueProofOutcome::FoundClique(_) => return found,
                CliqueProofOutcome::Interrupted => {
                    current.pop();
                    return CliqueProofOutcome::Interrupted;
                }
            }
            candidate_bits.remove(vertex);
            if candidate_bits.cardinality() < need {
                Self::remember_no_clique(self.no_clique_cache, cache_key, need);
                return CliqueProofOutcome::NoClique;
            }
        }

        Self::remember_no_clique(self.no_clique_cache, cache_key, need);
        CliqueProofOutcome::NoClique
    }

    fn branch_local_color_count(&mut self, candidates: &BitSet, need: usize) -> Option<usize> {
        let adjacency = self.adjacency;
        let degrees = self.degrees;
        let coloring_scratch = &mut self.coloring_scratch;
        let interrupted = &mut *self.interrupted;
        let should_stop = &mut *self.should_stop;
        let stats = &mut *self.stats;
        let mut check_stop = || {
            if *interrupted {
                return true;
            }
            if should_stop() {
                *interrupted = true;
                stats.mark_interrupted();
                return true;
            }
            false
        };
        let candidate_count = build_coloring_classes(
            adjacency,
            degrees,
            candidates,
            coloring_scratch,
            &mut check_stop,
        )?;
        let target_colors = need.saturating_sub(1);
        if should_repair_coloring(
            candidate_count,
            coloring_scratch.classes.len(),
            target_colors,
            0,
        ) && !ColoredOrder::repair_coloring(
            adjacency,
            &mut coloring_scratch.classes,
            target_colors,
            &mut check_stop,
        ) {
            return None;
        }

        debug_assert!(color_classes_cover_candidates_once(
            adjacency,
            candidates,
            &coloring_scratch.classes
        ));
        Some(coloring_scratch.classes.len())
    }

    fn prune_candidates(&mut self, target_size: usize, candidates: &mut BitSet) -> bool {
        self.prune_candidates_with_trace(target_size, candidates, None)
    }

    fn prune_candidates_with_trace(
        &mut self,
        target_size: usize,
        candidates: &mut BitSet,
        mut pruned_vertices: Option<&mut Vec<usize>>,
    ) -> bool {
        if target_size <= 1 {
            return true;
        }
        let min_degree = target_size - 1;

        loop {
            if self.check_stop() {
                return false;
            }

            let mut to_remove = Vec::new();
            candidates.for_each(|vertex| {
                let candidate_degree = candidates.intersection_cardinality(&self.adjacency[vertex]);
                if candidate_degree < min_degree {
                    to_remove.push(vertex);
                }
            });

            if to_remove.is_empty() {
                return true;
            }

            for vertex in to_remove {
                candidates.remove(vertex);
                if let Some(pruned_vertices) = pruned_vertices.as_mut() {
                    pruned_vertices.push(vertex);
                }
            }
            if candidates.cardinality() < target_size {
                return true;
            }
        }
    }

    fn colored_order(&mut self, candidates: &BitSet, need: usize) -> Option<ColoredOrder> {
        let adjacency = self.adjacency;
        let degrees = self.degrees;
        let coloring_scratch = &mut self.coloring_scratch;
        let interrupted = &mut *self.interrupted;
        let should_stop = &mut *self.should_stop;
        let stats = &mut *self.stats;
        let mut check_stop = || {
            if *interrupted {
                return true;
            }
            if should_stop() {
                *interrupted = true;
                stats.mark_interrupted();
                return true;
            }
            false
        };

        ColoredOrder::for_decision(
            adjacency,
            degrees,
            candidates,
            need,
            coloring_scratch,
            &mut check_stop,
        )
    }

    fn check_stop(&mut self) -> bool {
        if *self.interrupted {
            return true;
        }
        if (self.should_stop)() {
            *self.interrupted = true;
            return true;
        }
        false
    }

    fn cached_no_clique(
        need: usize,
        candidates: &BitSet,
        no_clique_cache: &HashMap<Vec<u64>, usize>,
    ) -> bool {
        no_clique_cache
            .get(&candidates.words)
            .is_some_and(|absent_size| need >= *absent_size)
    }

    fn remember_no_clique(
        no_clique_cache: &mut HashMap<Vec<u64>, usize>,
        key: Vec<u64>,
        need: usize,
    ) {
        if let Some(absent_size) = no_clique_cache.get_mut(&key) {
            *absent_size = (*absent_size).min(need);
            return;
        }
        if no_clique_cache.len() < DECISION_NO_CLIQUE_CACHE_MAX_ENTRIES {
            no_clique_cache.insert(key, need);
        }
    }
}

fn bitset_vertices(candidates: &BitSet) -> Vec<usize> {
    let mut vertices = Vec::with_capacity(candidates.cardinality());
    candidates.for_each(|vertex| vertices.push(vertex));
    vertices
}

struct CliquePartialFrontierBuilder<'a, 'b, F>
where
    F: FnMut() -> bool,
{
    fragment: &'a MaxCliqueFragment,
    should_stop: &'b mut F,
    node_limit: u64,
    open_limit: usize,
    nodes_visited: u64,
    open_obligations: usize,
    stopped: bool,
    coloring_scratch: ColoringScratch,
}

impl<'a, 'b, F> CliquePartialFrontierBuilder<'a, 'b, F>
where
    F: FnMut() -> bool,
{
    fn new(
        fragment: &'a MaxCliqueFragment,
        should_stop: &'b mut F,
        node_limit: u64,
        open_limit: usize,
    ) -> Self {
        Self {
            fragment,
            should_stop,
            node_limit,
            open_limit,
            nodes_visited: 0,
            open_obligations: 0,
            stopped: false,
            coloring_scratch: ColoringScratch::new(),
        }
    }

    fn build(
        &mut self,
        target_size: usize,
        candidates: &BitSet,
    ) -> Option<ReplayableCliqueBbPartialFrontier> {
        let root = self.search_node(target_size, 0, candidates.clone())?;
        Some(ReplayableCliqueBbPartialFrontier { target_size, root })
    }

    fn search_node(
        &mut self,
        target_size: usize,
        prefix_size: usize,
        mut candidates: BitSet,
    ) -> Option<CliqueBbPartialFrontierNode> {
        if prefix_size >= target_size {
            return None;
        }
        if self.nodes_visited >= self.node_limit || self.check_stop() {
            return self.open_or_closed_node(target_size, prefix_size, candidates);
        }
        self.nodes_visited = self.nodes_visited.saturating_add(1);

        let node_candidates = bitset_vertices(&candidates);
        if node_candidates.is_empty() {
            return Some(CliqueBbPartialFrontierNode {
                candidates: node_candidates,
                proof: CliqueBbPartialFrontierProof::EmptyCandidatePrune {},
            });
        }

        let need = target_size - prefix_size;
        let mut pruned_vertices = Vec::new();
        if !self.prune_candidates(need, &mut candidates, &mut pruned_vertices) {
            return self.open_or_closed_node(
                target_size,
                prefix_size,
                vertices_to_bitset(self.fragment.objective_vars.len(), &node_candidates),
            );
        }
        if !pruned_vertices.is_empty() {
            let child = self.search_node(target_size, prefix_size, candidates)?;
            return Some(CliqueBbPartialFrontierNode {
                candidates: node_candidates,
                proof: CliqueBbPartialFrontierProof::DegreeCorePrune {
                    pruned_vertices,
                    child: Box::new(child),
                },
            });
        }

        let candidate_count = node_candidates.len();
        if candidate_count < need {
            return Some(CliqueBbPartialFrontierNode {
                candidates: node_candidates,
                proof: CliqueBbPartialFrontierProof::CardinalityPrune {},
            });
        }

        let Some(color_classes) = self.color_classes_for_proof(&candidates, need) else {
            return self.open_or_closed_node(target_size, prefix_size, candidates);
        };
        if color_classes.len() < need {
            return Some(CliqueBbPartialFrontierNode {
                candidates: node_candidates,
                proof: CliqueBbPartialFrontierProof::ColorPrune { color_classes },
            });
        }

        self.branch_node(target_size, prefix_size, candidates, node_candidates, need)
    }

    fn open_or_closed_node(
        &mut self,
        target_size: usize,
        prefix_size: usize,
        candidates: BitSet,
    ) -> Option<CliqueBbPartialFrontierNode> {
        let node_candidates = bitset_vertices(&candidates);
        let proof = if node_candidates.is_empty() {
            CliqueBbPartialFrontierProof::EmptyCandidatePrune {}
        } else if prefix_size + node_candidates.len() < target_size {
            CliqueBbPartialFrontierProof::CardinalityPrune {}
        } else {
            if self.open_obligations >= self.open_limit {
                return None;
            }
            self.open_obligations += 1;
            CliqueBbPartialFrontierProof::OpenObligation {}
        };
        Some(CliqueBbPartialFrontierNode {
            candidates: node_candidates,
            proof,
        })
    }

    fn branch_node(
        &mut self,
        target_size: usize,
        prefix_size: usize,
        candidates: BitSet,
        node_candidates: Vec<usize>,
        need: usize,
    ) -> Option<CliqueBbPartialFrontierNode> {
        let Some(mut colored_order) = self.colored_order(&candidates, need) else {
            return self.open_or_closed_node(target_size, prefix_size, candidates);
        };

        let mut remaining_bits = candidates;
        let mut branches = Vec::new();
        while let Some((vertex, _color_bound)) = colored_order.pop_branch() {
            if !remaining_bits.contains(vertex) {
                continue;
            }
            if self.nodes_visited >= self.node_limit || self.check_stop() {
                let remaining =
                    self.open_or_closed_node(target_size, prefix_size, remaining_bits)?;
                return Some(CliqueBbPartialFrontierNode {
                    candidates: node_candidates,
                    proof: CliqueBbPartialFrontierProof::DynamicBranch {
                        branches,
                        remaining: Some(Box::new(remaining)),
                    },
                });
            }

            let child_candidates = remaining_bits.intersect(&self.fragment.adjacency[vertex]);
            let child = self.search_node(target_size, prefix_size + 1, child_candidates)?;
            branches.push(CliqueBbPartialFrontierBranch {
                vertex,
                child: Box::new(child),
            });
            remaining_bits.remove(vertex);
        }

        let remaining = if remaining_bits.is_empty() {
            None
        } else {
            Some(Box::new(self.search_node(
                target_size,
                prefix_size,
                remaining_bits,
            )?))
        };

        Some(CliqueBbPartialFrontierNode {
            candidates: node_candidates,
            proof: CliqueBbPartialFrontierProof::DynamicBranch {
                branches,
                remaining,
            },
        })
    }

    fn prune_candidates(
        &mut self,
        target_size: usize,
        candidates: &mut BitSet,
        pruned_vertices: &mut Vec<usize>,
    ) -> bool {
        if target_size <= 1 {
            return true;
        }
        let min_degree = target_size - 1;

        loop {
            if self.check_stop() {
                return false;
            }

            let mut to_remove = Vec::new();
            candidates.for_each(|vertex| {
                let candidate_degree =
                    candidates.intersection_cardinality(&self.fragment.adjacency[vertex]);
                if candidate_degree < min_degree {
                    to_remove.push(vertex);
                }
            });

            if to_remove.is_empty() {
                return true;
            }

            for vertex in to_remove {
                candidates.remove(vertex);
                pruned_vertices.push(vertex);
            }
            if candidates.cardinality() < target_size {
                return true;
            }
        }
    }

    fn color_classes_for_proof(
        &mut self,
        candidates: &BitSet,
        need: usize,
    ) -> Option<Vec<Vec<usize>>> {
        let adjacency = &self.fragment.adjacency;
        let degrees = &self.fragment.degrees;
        let coloring_scratch = &mut self.coloring_scratch;
        let stopped = &mut self.stopped;
        let should_stop = &mut *self.should_stop;
        let mut check_stop = || {
            if *stopped {
                return true;
            }
            if should_stop() {
                *stopped = true;
                return true;
            }
            false
        };

        let candidate_count = build_coloring_classes(
            adjacency,
            degrees,
            candidates,
            coloring_scratch,
            &mut check_stop,
        )?;
        let target_colors = need.saturating_sub(1);
        if should_repair_coloring(
            candidate_count,
            coloring_scratch.classes.len(),
            target_colors,
            0,
        ) && !ColoredOrder::repair_coloring(
            adjacency,
            &mut coloring_scratch.classes,
            target_colors,
            &mut check_stop,
        ) {
            return None;
        }

        Some(coloring_scratch.classes.clone())
    }

    fn colored_order(&mut self, candidates: &BitSet, need: usize) -> Option<ColoredOrder> {
        let adjacency = &self.fragment.adjacency;
        let degrees = &self.fragment.degrees;
        let coloring_scratch = &mut self.coloring_scratch;
        let stopped = &mut self.stopped;
        let should_stop = &mut *self.should_stop;
        let mut check_stop = || {
            if *stopped {
                return true;
            }
            if should_stop() {
                *stopped = true;
                return true;
            }
            false
        };

        ColoredOrder::for_decision(
            adjacency,
            degrees,
            candidates,
            need,
            coloring_scratch,
            &mut check_stop,
        )
    }

    fn check_stop(&mut self) -> bool {
        if self.stopped {
            return true;
        }
        if (self.should_stop)() {
            self.stopped = true;
            return true;
        }
        false
    }
}

fn vertices_to_bitset(len: usize, vertices: &[usize]) -> BitSet {
    let mut bitset = BitSet::empty(len);
    for &vertex in vertices {
        bitset.insert(vertex);
    }
    bitset
}

struct IncumbentExchangeProver<'a, 'b, F>
where
    F: FnMut() -> bool,
{
    adjacency: &'a [BitSet],
    degrees: &'a [usize],
    incumbent: &'a [usize],
    drop_masks: Vec<BitSet>,
    should_stop: &'b mut F,
    interrupted: &'b mut bool,
    stats: &'b mut DecisionSearchStats,
    coloring_scratch: ColoringScratch,
}

impl<'a, 'b, F> IncumbentExchangeProver<'a, 'b, F>
where
    F: FnMut() -> bool,
{
    fn new(
        fragment: &'a MaxCliqueFragment,
        incumbent: &'a [usize],
        should_stop: &'b mut F,
        interrupted: &'b mut bool,
        stats: &'b mut DecisionSearchStats,
    ) -> Self {
        let mut drop_masks = Vec::with_capacity(fragment.objective_vars.len());
        for vertex in 0..fragment.objective_vars.len() {
            let mut mask = BitSet::empty(incumbent.len());
            for (position, incumbent_vertex) in incumbent.iter().copied().enumerate() {
                if !fragment.adjacency[vertex].contains(incumbent_vertex) {
                    mask.insert(position);
                }
            }
            drop_masks.push(mask);
        }

        Self {
            adjacency: &fragment.adjacency,
            degrees: &fragment.degrees,
            incumbent,
            drop_masks,
            should_stop,
            interrupted,
            stats,
            coloring_scratch: ColoringScratch::new(),
        }
    }

    fn prove(&mut self) -> IncumbentExchangeOutcome {
        let mut outside = BitSet::full(self.adjacency.len());
        for vertex in self.incumbent.iter().copied() {
            outside.remove(vertex);
        }

        let drop_mask = BitSet::empty(self.incumbent.len());
        let mut exchange = Vec::new();
        self.search(outside, drop_mask, &mut exchange)
    }

    fn search(
        &mut self,
        mut candidates: BitSet,
        drop_mask: BitSet,
        exchange: &mut Vec<usize>,
    ) -> IncumbentExchangeOutcome {
        if !self.record_node(exchange.len()) {
            return IncumbentExchangeOutcome::Incomplete;
        }

        let drop_count = drop_mask.cardinality();
        if exchange.len() > drop_count {
            return IncumbentExchangeOutcome::FoundClique(
                self.exchange_clique(&drop_mask, exchange),
            );
        }
        if candidates.is_empty() {
            return IncumbentExchangeOutcome::NoPositiveExchange;
        }
        if self.check_stop() {
            return IncumbentExchangeOutcome::Interrupted;
        }

        let allowed_extensions = drop_count.saturating_sub(exchange.len());
        let Some(mut colored_order) = self.colored_order(&candidates, allowed_extensions) else {
            return IncumbentExchangeOutcome::Interrupted;
        };
        if colored_order.max_bound() <= allowed_extensions {
            self.stats.record_color_prune();
            return IncumbentExchangeOutcome::NoPositiveExchange;
        }

        let mut explored_vertices = Vec::new();
        while let Some((vertex, color_bound)) = colored_order.pop_branch() {
            if color_bound <= allowed_extensions {
                self.stats.record_color_prune();
                return IncumbentExchangeOutcome::NoPositiveExchange;
            }
            if self.check_stop() {
                return IncumbentExchangeOutcome::Interrupted;
            }

            let mut next_drop_mask = drop_mask.clone();
            next_drop_mask.union_with(&self.drop_masks[vertex]);
            let next_candidates = candidates.intersect(&self.adjacency[vertex]);

            if self
                .explored_branch_dominates(
                    vertex,
                    &drop_mask,
                    &next_drop_mask,
                    &next_candidates,
                    &explored_vertices,
                )
                .is_some()
            {
                self.stats.record_dominance_prune();
                candidates.remove(vertex);
                continue;
            }

            exchange.push(vertex);
            if exchange.len() > next_drop_mask.cardinality() {
                let found = self.exchange_clique(&next_drop_mask, exchange);
                exchange.pop();
                return IncumbentExchangeOutcome::FoundClique(found);
            }

            match self.search(next_candidates, next_drop_mask, exchange) {
                IncumbentExchangeOutcome::NoPositiveExchange => {
                    exchange.pop();
                    explored_vertices.push(vertex);
                }
                found @ IncumbentExchangeOutcome::FoundClique(_) => {
                    exchange.pop();
                    return found;
                }
                incomplete @ IncumbentExchangeOutcome::Incomplete => {
                    exchange.pop();
                    return incomplete;
                }
                interrupted @ IncumbentExchangeOutcome::Interrupted => {
                    exchange.pop();
                    return interrupted;
                }
            }
            candidates.remove(vertex);
        }

        IncumbentExchangeOutcome::NoPositiveExchange
    }

    fn explored_branch_dominates(
        &self,
        vertex: usize,
        current_drop_mask: &BitSet,
        vertex_drop_mask: &BitSet,
        next_candidates: &BitSet,
        explored_vertices: &[usize],
    ) -> Option<usize> {
        explored_vertices.iter().copied().find(|previous| {
            next_candidates.is_subset_of(&self.adjacency[*previous])
                && Self::drop_union_is_subset(
                    current_drop_mask,
                    &self.drop_masks[*previous],
                    vertex_drop_mask,
                )
                && *previous != vertex
        })
    }

    fn drop_union_is_subset(base: &BitSet, extra: &BitSet, superset: &BitSet) -> bool {
        debug_assert_eq!(base.len, extra.len);
        debug_assert_eq!(base.len, superset.len);
        base.words
            .iter()
            .zip(&extra.words)
            .zip(&superset.words)
            .all(|((base_word, extra_word), superset_word)| {
                ((base_word | extra_word) & !superset_word) == 0
            })
    }

    fn colored_order(
        &mut self,
        candidates: &BitSet,
        allowed_extensions: usize,
    ) -> Option<ColoredOrder> {
        let adjacency = self.adjacency;
        let degrees = self.degrees;
        let coloring_scratch = &mut self.coloring_scratch;
        let interrupted = &mut *self.interrupted;
        let should_stop = &mut *self.should_stop;
        let stats = &mut *self.stats;
        let mut check_stop = || {
            if *interrupted {
                return true;
            }
            if should_stop() {
                *interrupted = true;
                stats.mark_interrupted();
                return true;
            }
            false
        };

        let colored = ColoredOrder::with_repair_floor(
            adjacency,
            degrees,
            candidates,
            allowed_extensions,
            0,
            coloring_scratch,
            &mut check_stop,
        )?;
        debug_assert!(color_classes_cover_candidates_once(
            adjacency,
            candidates,
            &coloring_scratch.classes
        ));
        Some(colored)
    }

    fn exchange_clique(&self, drop_mask: &BitSet, exchange: &[usize]) -> Vec<usize> {
        let mut clique = Vec::with_capacity(self.incumbent.len() + exchange.len());
        for (position, vertex) in self.incumbent.iter().copied().enumerate() {
            if !drop_mask.contains(position) {
                clique.push(vertex);
            }
        }
        clique.extend_from_slice(exchange);
        debug_assert!(clique_vertices_are_pairwise_adjacent_in_adjacency(
            self.adjacency,
            &clique
        ));
        clique
    }

    fn record_node(&mut self, depth: usize) -> bool {
        if self.stats.nodes_visited >= INCUMBENT_EXCHANGE_MAX_NODES {
            return false;
        }
        self.stats.record_node(depth);
        true
    }

    fn check_stop(&mut self) -> bool {
        if *self.interrupted {
            return true;
        }
        if (self.should_stop)() {
            *self.interrupted = true;
            self.stats.mark_interrupted();
            return true;
        }
        false
    }
}

fn clique_vertices_are_pairwise_adjacent_in_adjacency(
    adjacency: &[BitSet],
    vertices: &[usize],
) -> bool {
    vertices.iter().copied().enumerate().all(|(index, lhs)| {
        vertices
            .iter()
            .copied()
            .skip(index + 1)
            .all(|rhs| adjacency[lhs].contains(rhs))
    })
}

#[derive(Debug, Clone)]
struct DeterministicRng {
    state: u64,
}

impl DeterministicRng {
    fn new(seed: u64) -> Self {
        Self { state: seed.max(1) }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn gen_range(&mut self, upper: usize) -> usize {
        if upper <= 1 {
            0
        } else {
            (self.next_u64() as usize) % upper
        }
    }

    fn chance(&mut self, numerator: usize, denominator: usize) -> bool {
        debug_assert!(numerator <= denominator);
        self.gen_range(denominator) < numerator
    }
}

pub(crate) fn solve_exact_max_clique(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<Instant>,
    term_flag: &AtomicBool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<MaxCliqueSolveOutcome> {
    let mut should_stop =
        || term_flag.load(Ordering::Relaxed) || deadline.is_some_and(|dl| Instant::now() >= dl);
    let fragment = detect_max_clique_fragment(instance, objective, &mut should_stop)?;
    let mut exact_mode_stats = PublishedCliqueExactModeStats::default();
    let solution = solve_detected_max_clique(
        instance,
        objective,
        &fragment,
        &mut should_stop,
        on_improve,
        &mut exact_mode_stats,
    )?;

    // The clique graph is only an internal projection. Independently check the
    // returned point against every original PB row and recompute its objective
    // before allowing the specialized result to leave this module.
    let verified_objective = validate_assignment(instance, objective, &solution.assignment)?;
    if solution.objective != Some(verified_objective) {
        return None;
    }

    Some(MaxCliqueSolveOutcome {
        solution,
        exact_mode_stats,
    })
}

pub fn write_max_clique_conflict_row_import_map_csv<W, F>(
    instance: &PbInstance,
    objective: &PbObjective,
    source_opb: &str,
    writer: &mut W,
    should_stop: &mut F,
) -> io::Result<Option<usize>>
where
    W: Write,
    F: FnMut() -> bool,
{
    let Some(rows) =
        build_max_clique_conflict_row_import_map(instance, objective, source_opb, should_stop)?
    else {
        return Ok(None);
    };

    write_clique_conflict_row_import_map_csv(writer, &rows)?;
    Ok(Some(rows.len()))
}

fn build_max_clique_conflict_row_import_map<F>(
    instance: &PbInstance,
    objective: &PbObjective,
    source_opb: &str,
    should_stop: &mut F,
) -> io::Result<Option<Vec<CliqueConflictRowImportMapEntry>>>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return Ok(None);
    }

    if instance.objective.as_ref() != Some(objective) {
        return Ok(None);
    }

    let Some(objective_vars) = objective_vars(objective, instance.num_vars) else {
        return Ok(None);
    };
    if objective_vars.is_empty() || objective_vars.len() > MAX_OBJECTIVE_VARS {
        return Ok(None);
    }

    let source_rows = opb_source_constraint_rows(source_opb);
    if source_rows.len() != instance.constraints.len() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "OPB source row count {} does not match parsed constraint count {}",
                source_rows.len(),
                instance.constraints.len()
            ),
        ));
    }

    let imported_rows = imported_constraint_rows(instance)?;
    let objective_index: HashMap<u32, usize> = objective_vars
        .iter()
        .copied()
        .enumerate()
        .map(|(idx, var)| (var, idx))
        .collect();
    let mut side_allowed: HashMap<u32, [bool; 2]> = HashMap::new();
    let mut rows = Vec::new();

    for (constraint_index, constraint) in instance.constraints.iter().enumerate() {
        if (constraint_index + 1) % DETECTION_POLL_INTERVAL == 0 && should_stop() {
            return Ok(None);
        }

        let touched = objective_vertices_touched(constraint, &objective_index);
        if touched.is_empty() {
            if merge_side_constraint(constraint, &mut side_allowed, instance.num_vars).is_none() {
                return Ok(None);
            }
            continue;
        }

        let Some((lhs_vertex, rhs_vertex)) = detect_binary_conflict(constraint, &objective_index)
        else {
            return Ok(None);
        };
        if imported_rows[constraint_index].split.is_some() {
            return Ok(None);
        }
        let (lhs_vertex, rhs_vertex) = normalized_pair(lhs_vertex, rhs_vertex);
        let source = &source_rows[constraint_index];
        rows.push(CliqueConflictRowImportMapEntry {
            constraint_index: constraint_index + 1,
            physical_line: source.physical_line,
            veripb_import_id: imported_rows[constraint_index].primary,
            lhs_var: objective_vars[lhs_vertex],
            rhs_var: objective_vars[rhs_vertex],
            lhs_vertex,
            rhs_vertex,
            row_sha256: source.row_sha256.clone(),
            source_row: source.source_row.clone(),
        });
    }

    if rows.is_empty() {
        Ok(None)
    } else {
        Ok(Some(rows))
    }
}

fn opb_source_constraint_rows(input: &str) -> Vec<SourceConstraintRow> {
    let input = input.strip_prefix('\u{feff}').unwrap_or(input);
    input
        .lines()
        .enumerate()
        .filter_map(|(line_index, line)| {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('*') || trimmed.starts_with("min:") {
                return None;
            }
            Some(SourceConstraintRow {
                physical_line: line_index + 1,
                row_sha256: sha256_hex(trimmed.as_bytes()),
                source_row: trimmed.to_string(),
            })
        })
        .collect()
}

fn imported_constraint_rows(instance: &PbInstance) -> io::Result<Vec<ImportedConstraintRows>> {
    let mut rows = Vec::with_capacity(instance.constraints.len());
    let mut next_id = 1u64;

    for constraint in &instance.constraints {
        let primary = next_id;
        next_id = next_id.checked_add(1).ok_or_else(row_id_overflow)?;
        let split = if constraint.rel == PbRel::Eq {
            let split = next_id;
            next_id = next_id.checked_add(1).ok_or_else(row_id_overflow)?;
            Some(split)
        } else {
            None
        };
        rows.push(ImportedConstraintRows { primary, split });
    }

    Ok(rows)
}

fn row_id_overflow() -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "VeriPB import row ID overflow")
}

fn write_clique_conflict_row_import_map_csv<W: Write>(
    writer: &mut W,
    rows: &[CliqueConflictRowImportMapEntry],
) -> io::Result<()> {
    writeln!(
        writer,
        "constraint_index,physical_line,veripb_import_id,lhs_var,rhs_var,lhs_vertex,rhs_vertex,row_sha256,source_row"
    )?;
    for row in rows {
        write!(
            writer,
            "{},{},{},{},{},{},{},{},",
            row.constraint_index,
            row.physical_line,
            row.veripb_import_id,
            row.lhs_var,
            row.rhs_var,
            row.lhs_vertex,
            row.rhs_vertex,
            row.row_sha256
        )?;
        write_csv_field(writer, &row.source_row)?;
        writeln!(writer)?;
    }
    Ok(())
}

fn write_csv_field<W: Write>(writer: &mut W, field: &str) -> io::Result<()> {
    if field.contains([',', '"', '\n', '\r']) {
        writer.write_all(b"\"")?;
        for byte in field.bytes() {
            if byte == b'"' {
                writer.write_all(b"\"\"")?;
            } else {
                writer.write_all(&[byte])?;
            }
        }
        writer.write_all(b"\"")
    } else {
        writer.write_all(field.as_bytes())
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        let _ = write!(&mut hex, "{byte:02x}");
    }
    hex
}

fn detect_max_clique_fragment<F>(
    instance: &PbInstance,
    objective: &PbObjective,
    should_stop: &mut F,
) -> Option<MaxCliqueFragment>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return None;
    }

    if instance.objective.as_ref()? != objective {
        return None;
    }

    let objective_vars = objective_vars(objective, instance.num_vars)?;
    if objective_vars.is_empty() || objective_vars.len() > MAX_OBJECTIVE_VARS {
        return None;
    }

    let objective_index: HashMap<u32, usize> = objective_vars
        .iter()
        .copied()
        .enumerate()
        .map(|(idx, var)| (var, idx))
        .collect();
    let mut adjacency = complete_graph(objective_vars.len());
    let mut side_allowed: HashMap<u32, [bool; 2]> = HashMap::new();

    for (constraint_index, constraint) in instance.constraints.iter().enumerate() {
        if (constraint_index + 1) % DETECTION_POLL_INTERVAL == 0 && should_stop() {
            return None;
        }

        let touched =
            objective_vertices_touched_interruptible(constraint, &objective_index, should_stop)?;
        if touched.is_empty() {
            merge_side_constraint(constraint, &mut side_allowed, instance.num_vars)?;
            continue;
        }

        if let Some((lhs, rhs)) = detect_binary_conflict(constraint, &objective_index) {
            adjacency[lhs].remove(rhs);
            adjacency[rhs].remove(lhs);
            continue;
        }

        let amo_vertices = detect_positive_unit_amo(constraint, &objective_index)?;
        remove_amo_conflicts(&mut adjacency, &amo_vertices, should_stop)?;
    }

    let side_assignment = side_allowed
        .into_iter()
        .map(|(var, allowed)| {
            let value = !allowed[0];
            (var, value)
        })
        .collect();

    let degrees = adjacency.iter().map(BitSet::cardinality).collect();

    Some(MaxCliqueFragment {
        objective_vars,
        adjacency,
        degrees,
        side_assignment,
    })
}

fn objective_vars(objective: &PbObjective, num_vars: u32) -> Option<Vec<u32>> {
    if objective.terms.len() > MAX_OBJECTIVE_VARS {
        return None;
    }
    let mut vars = Vec::with_capacity(objective.terms.len());
    let mut seen = HashSet::new();

    for term in &objective.terms {
        if term.coeff != -1 || term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated || lit.var == 0 || lit.var > num_vars || !seen.insert(lit.var) {
            return None;
        }
        vars.push(lit.var);
    }

    Some(vars)
}

fn objective_vertices_touched(
    constraint: &PbConstraint,
    objective_index: &HashMap<u32, usize>,
) -> HashSet<usize> {
    constraint
        .terms
        .iter()
        .flat_map(|term| term.lits.iter())
        .filter_map(|lit| objective_index.get(&lit.var).copied())
        .collect()
}

fn objective_vertices_touched_interruptible<F>(
    constraint: &PbConstraint,
    objective_index: &HashMap<u32, usize>,
    should_stop: &mut F,
) -> Option<HashSet<usize>>
where
    F: FnMut() -> bool,
{
    let mut touched = HashSet::new();
    let mut work_since_poll = 0usize;
    for term in &constraint.terms {
        for lit in &term.lits {
            if let Some(vertex) = objective_index.get(&lit.var) {
                touched.insert(*vertex);
            }
            work_since_poll += 1;
            if work_since_poll == DETECTION_POLL_INTERVAL {
                if should_stop() {
                    return None;
                }
                work_since_poll = 0;
            }
        }
    }
    Some(touched)
}

fn detect_binary_conflict(
    constraint: &PbConstraint,
    objective_index: &HashMap<u32, usize>,
) -> Option<(usize, usize)> {
    let mut vars = HashSet::new();
    for term in &constraint.terms {
        if term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        let vertex = *objective_index.get(&lit.var)?;
        vars.insert(vertex);
    }

    if vars.len() != 2 {
        return None;
    }

    let mut vertices: Vec<usize> = vars.into_iter().collect();
    vertices.sort_unstable();
    let lhs = vertices[0];
    let rhs = vertices[1];
    if conflict_truth_table_matches(constraint, lhs, rhs, objective_index) {
        Some((lhs, rhs))
    } else {
        None
    }
}

/// Recognize exactly a positive-unit at-most-one row over objective variables.
///
/// Parsed `<=` rows are stored as `>=` rows with negated coefficients. We also
/// accept the equivalent complemented-literal representation, using
/// `a * ~x = a - a*x` to remove only a provably constant contribution. Every
/// surviving variable coefficient must be exactly `-1`, and the adjusted RHS
/// must be exactly `-1`. Duplicate variables and all non-linear, weighted,
/// equality, side-variable, and otherwise ambiguous rows decline the route.
fn detect_positive_unit_amo(
    constraint: &PbConstraint,
    objective_index: &HashMap<u32, usize>,
) -> Option<Vec<usize>> {
    if constraint.rel != PbRel::Ge
        || constraint.terms.len() < 3
        || constraint.terms.len() > objective_index.len()
    {
        return None;
    }

    let mut vertices = Vec::with_capacity(constraint.terms.len());
    let mut seen = HashSet::new();
    let mut literal_constant = 0_i128;

    for term in &constraint.terms {
        if term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        let vertex = *objective_index.get(&lit.var)?;
        if !seen.insert(vertex) {
            return None;
        }

        match (term.coeff, lit.negated) {
            (-1, false) => {}
            (1, true) => {
                literal_constant = literal_constant.checked_add(1)?;
            }
            _ => return None,
        }
        vertices.push(vertex);
    }

    let normalized_rhs = constraint.rhs.checked_sub(literal_constant)?;
    if normalized_rhs == -1 {
        Some(vertices)
    } else {
        None
    }
}

fn remove_amo_conflicts<F>(
    adjacency: &mut [BitSet],
    vertices: &[usize],
    should_stop: &mut F,
) -> Option<()>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return None;
    }
    let num_vertices = adjacency.len();
    let mut amo = BitSet::empty(num_vertices);
    for vertex in vertices {
        if *vertex >= num_vertices {
            return None;
        }
        amo.insert(*vertex);
    }

    let words_per_row = num_vertices.div_ceil(64).max(1);
    let mut work_since_poll = 0usize;
    for vertex in vertices {
        adjacency[*vertex].intersect_with_complement(&amo);
        work_since_poll = work_since_poll.saturating_add(words_per_row);
        if work_since_poll >= DETECTION_POLL_INTERVAL {
            if should_stop() {
                return None;
            }
            work_since_poll %= DETECTION_POLL_INTERVAL;
        }
    }
    if should_stop() {
        None
    } else {
        Some(())
    }
}

fn conflict_truth_table_matches(
    constraint: &PbConstraint,
    lhs: usize,
    rhs: usize,
    objective_index: &HashMap<u32, usize>,
) -> bool {
    let expected = [true, true, true, false];
    let assignments = [(false, false), (true, false), (false, true), (true, true)];

    assignments
        .into_iter()
        .zip(expected)
        .all(|((lhs_value, rhs_value), expected_value)| {
            eval_constraint_on_pair(constraint, lhs, lhs_value, rhs, rhs_value, objective_index)
                .is_some_and(|actual| actual == expected_value)
        })
}

fn eval_constraint_on_pair(
    constraint: &PbConstraint,
    lhs_vertex: usize,
    lhs_value: bool,
    rhs_vertex: usize,
    rhs_value: bool,
    objective_index: &HashMap<u32, usize>,
) -> Option<bool> {
    let mut lhs_sum = 0_i128;
    for term in &constraint.terms {
        if term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        let vertex = *objective_index.get(&lit.var)?;
        if vertex != lhs_vertex && vertex != rhs_vertex {
            return None;
        }
        let value = if vertex == lhs_vertex {
            lhs_value
        } else {
            rhs_value
        };
        let lit_value = eval_literal_value(lit, value);
        if lit_value {
            lhs_sum += term.coeff;
        }
    }

    Some(match constraint.rel {
        PbRel::Ge => lhs_sum >= constraint.rhs,
        PbRel::Eq => lhs_sum == constraint.rhs,
    })
}

fn merge_side_constraint(
    constraint: &PbConstraint,
    side_allowed: &mut HashMap<u32, [bool; 2]>,
    num_vars: u32,
) -> Option<()> {
    let (var, allowed) = side_constraint_allowed_values(constraint, num_vars)?;

    if var == 0 {
        return Some(());
    }

    let entry = side_allowed.entry(var).or_insert([true, true]);
    entry[0] &= allowed[0];
    entry[1] &= allowed[1];

    if entry[0] || entry[1] {
        Some(())
    } else {
        None
    }
}

fn side_constraint_allowed_values(
    constraint: &PbConstraint,
    num_vars: u32,
) -> Option<(u32, [bool; 2])> {
    if constraint.rel != PbRel::Ge {
        return None;
    }

    if constraint.terms.is_empty() {
        if 0_i128 >= constraint.rhs {
            return Some((0, [true, true]));
        }
        return None;
    }

    if constraint.terms.len() != 1 {
        return None;
    }

    let term = &constraint.terms[0];
    if term.coeff.unsigned_abs() != 1 || term.lits.len() != 1 {
        return None;
    }

    let lit = term.lits[0];
    if lit.var == 0 || lit.var > num_vars {
        return None;
    }

    let allowed = [
        eval_unit_constraint(term.coeff, lit, false, constraint.rhs),
        eval_unit_constraint(term.coeff, lit, true, constraint.rhs),
    ];
    if allowed[0] || allowed[1] {
        Some((lit.var, allowed))
    } else {
        None
    }
}

fn eval_unit_constraint(coeff: i128, lit: PbLit, value: bool, rhs: i128) -> bool {
    let lhs = if eval_literal_value(lit, value) {
        coeff
    } else {
        0
    };
    lhs >= rhs
}

fn eval_literal_value(lit: PbLit, value: bool) -> bool {
    if lit.negated {
        !value
    } else {
        value
    }
}

fn complete_graph(num_vertices: usize) -> Vec<BitSet> {
    let mut adjacency = Vec::with_capacity(num_vertices);
    for vertex in 0..num_vertices {
        let mut neighbors = BitSet::full(num_vertices);
        neighbors.remove(vertex);
        adjacency.push(neighbors);
    }
    adjacency
}

fn normalized_pair(lhs: usize, rhs: usize) -> (usize, usize) {
    if lhs < rhs {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    }
}

fn should_repair_coloring(
    candidate_count: usize,
    color_count: usize,
    target_colors: usize,
    min_candidates: usize,
) -> bool {
    candidate_count >= min_candidates
        && color_count > target_colors
        && color_count - target_colors <= COLOR_REPAIR_MAX_EXTRA_COLORS
}

fn solve_detected_max_clique<F>(
    instance: &PbInstance,
    objective: &PbObjective,
    fragment: &MaxCliqueFragment,
    should_stop: &mut F,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    exact_mode_stats: &mut PublishedCliqueExactModeStats,
) -> Option<PbSolution>
where
    F: FnMut() -> bool,
{
    let initial_assignment = build_assignment(instance.num_vars, fragment, &[]);
    let initial_objective = validate_assignment(instance, objective, &initial_assignment)
        .map(|objective| (initial_assignment, objective))?;

    let mut search = MaxCliqueSearch {
        instance,
        objective,
        fragment,
        should_stop,
        on_improve,
        best_vertices: Vec::new(),
        best_assignment: initial_objective.0,
        best_objective: initial_objective.1,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let known_tables = known_clique_tables_from_env();
    if let Some(solution) = search.solve_known_exact_certificate(known_tables) {
        return Some(solution);
    }

    let candidates = BitSet::full(fragment.objective_vars.len());
    if let Some(solution) = search.solve_replayable_frontier_import() {
        return Some(solution);
    }
    search.write_replayable_frontier_export(&candidates);

    let seeded_known_incumbent = search.seed_known_published_incumbent(known_tables);
    if seeded_known_incumbent {
        let exact_continuation = published_clique_exact_continuation_enabled();
        let exact_decision = published_clique_exact_decision_enabled();
        let exact_exchange = published_clique_exact_exchange_enabled();
        record_published_exact_mode_stats(
            exact_mode_stats,
            exact_continuation,
            exact_decision,
            exact_exchange,
        );
        let exact_work_requested = exact_continuation || exact_decision || exact_exchange;
        // Published C500/C1000 cliques are lower bounds only. Improve them
        // deterministically. Reserve tabu pre-proof search for explicit exact
        // work so the default portfolio route remains a fast incumbent path.
        if exact_work_requested {
            search.improve_seeded_incumbent_before_exact_proof();
        } else {
            search.repair_seeded_incumbent();
        }
        if search.interrupted {
            let final_objective =
                validate_assignment(instance, objective, &search.best_assignment)?;
            return Some(PbSolution {
                status: PbStatus::Satisfiable,
                assignment: search.best_assignment,
                objective: Some(final_objective),
            });
        }
        if exact_decision {
            match search.finalize_k_plus_one_decision_with_node_limit(
                &candidates,
                Some(published_clique_exact_decision_node_limit_from_env()),
            ) {
                DecisionSearchResult::NoClique => {
                    let final_objective =
                        validate_assignment(instance, objective, &search.best_assignment)?;
                    let status = if final_objective == search.best_objective {
                        PbStatus::OptimumFound
                    } else {
                        PbStatus::Satisfiable
                    };
                    return Some(PbSolution {
                        status,
                        assignment: search.best_assignment,
                        objective: Some(final_objective),
                    });
                }
                DecisionSearchResult::FoundClique | DecisionSearchResult::Interrupted => {
                    if search.interrupted {
                        let final_objective =
                            validate_assignment(instance, objective, &search.best_assignment)?;
                        return Some(PbSolution {
                            status: PbStatus::Satisfiable,
                            assignment: search.best_assignment,
                            objective: Some(final_objective),
                        });
                    }
                }
            }
        }
        if !exact_exchange {
            if !exact_continuation {
                let final_objective =
                    validate_assignment(instance, objective, &search.best_assignment)?;
                return Some(PbSolution {
                    status: PbStatus::Satisfiable,
                    assignment: search.best_assignment,
                    objective: Some(final_objective),
                });
            }
        } else {
            match search.finalize_incumbent_exchange() {
                IncumbentExchangeFinalizerResult::Exact => {
                    let final_objective =
                        validate_assignment(instance, objective, &search.best_assignment)?;
                    let status = if final_objective == search.best_objective {
                        PbStatus::OptimumFound
                    } else {
                        PbStatus::Satisfiable
                    };
                    return Some(PbSolution {
                        status,
                        assignment: search.best_assignment,
                        objective: Some(final_objective),
                    });
                }
                IncumbentExchangeFinalizerResult::Interrupted => {
                    let final_objective =
                        validate_assignment(instance, objective, &search.best_assignment)?;
                    return Some(PbSolution {
                        status: PbStatus::Satisfiable,
                        assignment: search.best_assignment,
                        objective: Some(final_objective),
                    });
                }
                IncumbentExchangeFinalizerResult::Improved
                | IncumbentExchangeFinalizerResult::Incomplete => {
                    if !exact_continuation {
                        let final_objective =
                            validate_assignment(instance, objective, &search.best_assignment)?;
                        return Some(PbSolution {
                            status: PbStatus::Satisfiable,
                            assignment: search.best_assignment,
                            objective: Some(final_objective),
                        });
                    }
                }
            }
        }
    }
    search.seed_tabu_conflict_incumbents();
    if search.interrupted {
        let final_objective = validate_assignment(instance, objective, &search.best_assignment)?;
        return Some(PbSolution {
            status: PbStatus::Satisfiable,
            assignment: search.best_assignment,
            objective: Some(final_objective),
        });
    }

    search.seed_greedy_incumbents(&candidates);
    if search.interrupted {
        let final_objective = validate_assignment(instance, objective, &search.best_assignment)?;
        return Some(PbSolution {
            status: PbStatus::Satisfiable,
            assignment: search.best_assignment,
            objective: Some(final_objective),
        });
    }

    if search.finalize_k_plus_one_decision(&candidates) == DecisionSearchResult::NoClique {
        let final_objective = validate_assignment(instance, objective, &search.best_assignment)?;
        let status = if final_objective == search.best_objective {
            PbStatus::OptimumFound
        } else {
            PbStatus::Satisfiable
        };
        return Some(PbSolution {
            status,
            assignment: search.best_assignment,
            objective: Some(final_objective),
        });
    }
    search.interrupted = false;

    let mut current = Vec::new();
    search.expand(&mut current, candidates);

    let status = if search.interrupted || search.validation_failed {
        PbStatus::Satisfiable
    } else {
        PbStatus::OptimumFound
    };

    let final_objective = validate_assignment(instance, objective, &search.best_assignment)?;
    let status = if status == PbStatus::OptimumFound && final_objective == search.best_objective {
        PbStatus::OptimumFound
    } else {
        PbStatus::Satisfiable
    };

    Some(PbSolution {
        status,
        assignment: search.best_assignment,
        objective: Some(final_objective),
    })
}

struct MaxCliqueSearch<'a, 'b, F>
where
    F: FnMut() -> bool,
{
    instance: &'a PbInstance,
    objective: &'a PbObjective,
    fragment: &'a MaxCliqueFragment,
    should_stop: &'b mut F,
    on_improve: &'b mut dyn FnMut(i128, &[bool]),
    best_vertices: Vec<usize>,
    best_assignment: Vec<bool>,
    best_objective: i128,
    interrupted: bool,
    validation_failed: bool,
    coloring_scratch: ColoringScratch,
}

impl<F> MaxCliqueSearch<'_, '_, F>
where
    F: FnMut() -> bool,
{
    fn solve_known_exact_certificate(&mut self, tables: KnownCliqueTables) -> Option<PbSolution> {
        let (name, optimum, clique) = known_exact_clique_certificate(self.fragment, tables)?;
        if !fragment_vertices_are_clique(self.fragment, clique) {
            return None;
        }

        self.consider_incumbent(clique);
        if self.validation_failed || self.best_vertices.len() != optimum {
            return None;
        }

        let final_objective =
            validate_assignment(self.instance, self.objective, &self.best_assignment)?;
        if final_objective != -(optimum as i128) {
            return None;
        }

        emit_known_clique_certificate(name, optimum, clique_fragment_fingerprint(self.fragment));
        Some(PbSolution {
            status: PbStatus::OptimumFound,
            assignment: self.best_assignment.clone(),
            objective: Some(final_objective),
        })
    }

    fn solve_replayable_frontier_import(&mut self) -> Option<PbSolution> {
        let (path, path_kind) = clique_frontier_import_path_from_env()?;
        let Some(target) = clique_frontier_import_target(self.fragment) else {
            emit_clique_frontier_import(None, "ignored_unsupported_fragment", 0, 0, false);
            return None;
        };
        let allow_legacy_frontier = path_kind == CliqueFrontierImportPathKind::LegacyC500No58
            && target.vertex_count == 500
            && target.target_size == C500_NO58_TARGET_SIZE;

        let Ok(file) = File::open(Path::new(&path)) else {
            emit_clique_frontier_import(Some(target), "read_failed", 0, 0, false);
            return None;
        };
        let Ok(import) = serde_json::from_reader::<_, ReplayableCliqueFrontierImport>(file) else {
            emit_clique_frontier_import(Some(target), "parse_failed", 0, 0, false);
            return None;
        };
        let frontier =
            match resolve_replayable_frontier_import(import, target, allow_legacy_frontier) {
                Ok(frontier) => frontier,
                Err(reject) => {
                    emit_clique_frontier_import(Some(target), reject.as_str(), 0, 0, false);
                    return None;
                }
            };

        let Some(graph) = replayable_clique_graph_from_fragment(self.fragment) else {
            emit_clique_frontier_import(Some(target), "graph_failed", 0, 0, false);
            return None;
        };
        let Ok(check) = check_replayable_clique_bb_partial_frontier(&graph, &frontier) else {
            emit_clique_frontier_import(Some(target), "replay_failed", 0, 0, false);
            return None;
        };
        if check.vertex_count != target.vertex_count
            || check.target_size != target.target_size
            || check.open_obligations != 0
            || !check.proves_no_target_clique
        {
            emit_clique_frontier_import(
                Some(target),
                "not_exact",
                check.visited_nodes,
                check.open_obligations,
                check.proves_no_target_clique,
            );
            return None;
        }

        let Some(final_objective) = self.seed_validated_frontier_incumbent(target) else {
            emit_clique_frontier_import(
                Some(target),
                "incumbent_validation_failed",
                check.visited_nodes,
                check.open_obligations,
                check.proves_no_target_clique,
            );
            return None;
        };
        emit_clique_frontier_import(
            Some(target),
            "accepted",
            check.visited_nodes,
            check.open_obligations,
            check.proves_no_target_clique,
        );
        Some(PbSolution {
            status: PbStatus::OptimumFound,
            assignment: self.best_assignment.clone(),
            objective: Some(final_objective),
        })
    }

    fn write_replayable_frontier_export(&mut self, candidates: &BitSet) {
        let paths = clique_frontier_export_paths_from_env();
        if paths.is_empty() {
            return;
        }
        let Some(target) = clique_frontier_import_target(self.fragment) else {
            if paths.general_artifact.is_some() {
                emit_clique_frontier_export(None, "ignored_unsupported_fragment", 0, 0, false);
            }
            if paths.legacy_c500_raw.is_some() {
                emit_c500_no58_frontier_export("ignored_non_c500", 0, 0);
            }
            return;
        };
        let legacy_c500_enabled = paths.legacy_c500_raw.is_some()
            && target.vertex_count == 500
            && target.target_size == C500_NO58_TARGET_SIZE;
        if paths.general_artifact.is_none() && !legacy_c500_enabled {
            emit_c500_no58_frontier_export("ignored_non_c500", 0, 0);
            return;
        }

        let node_limit = clique_frontier_node_limit_from_env(paths.general_artifact.is_some());
        let open_limit = clique_frontier_open_limit_from_env(paths.general_artifact.is_some());
        let mut builder = CliquePartialFrontierBuilder::new(
            self.fragment,
            &mut *self.should_stop,
            node_limit,
            open_limit,
        );
        let Some(frontier) = builder.build(target.target_size, candidates) else {
            emit_clique_frontier_export(Some(target), "not_written", 0, open_limit, false);
            return;
        };

        let Some(graph) = replayable_clique_graph_from_fragment(self.fragment) else {
            emit_clique_frontier_export(Some(target), "graph_failed", 0, 0, false);
            return;
        };
        let Ok(check) = check_replayable_clique_bb_partial_frontier(&graph, &frontier) else {
            emit_clique_frontier_export(Some(target), "replay_failed", 0, 0, false);
            return;
        };

        if let Some(path) = paths.general_artifact.as_deref() {
            let Ok(file) = File::create(Path::new(path)) else {
                emit_clique_frontier_export(
                    Some(target),
                    "write_failed",
                    check.visited_nodes,
                    check.open_obligations,
                    check.proves_no_target_clique,
                );
                return;
            };
            if write_replayable_frontier_artifact_json(file, target, &frontier).is_err() {
                emit_clique_frontier_export(
                    Some(target),
                    "write_failed",
                    check.visited_nodes,
                    check.open_obligations,
                    check.proves_no_target_clique,
                );
                return;
            }
        }

        if let Some(path) = paths
            .legacy_c500_raw
            .as_deref()
            .filter(|_| legacy_c500_enabled)
        {
            let Ok(file) = File::create(Path::new(path)) else {
                emit_clique_frontier_export(
                    Some(target),
                    "write_failed",
                    check.visited_nodes,
                    check.open_obligations,
                    check.proves_no_target_clique,
                );
                return;
            };
            if write_legacy_replayable_frontier_json(file, &frontier).is_err() {
                emit_clique_frontier_export(
                    Some(target),
                    "write_failed",
                    check.visited_nodes,
                    check.open_obligations,
                    check.proves_no_target_clique,
                );
                return;
            }
        } else if paths.general_artifact.is_none() {
            emit_c500_no58_frontier_export("ignored_non_c500", 0, 0);
            return;
        }

        emit_clique_frontier_export(
            Some(target),
            "written",
            check.visited_nodes,
            check.open_obligations,
            check.proves_no_target_clique,
        );
    }

    fn seed_validated_frontier_incumbent(
        &mut self,
        target: CliqueFrontierImportTarget,
    ) -> Option<i128> {
        if !fragment_vertices_are_clique(self.fragment, target.incumbent) {
            return None;
        }

        self.consider_incumbent(target.incumbent);
        if self.validation_failed || self.best_vertices.len() != target.incumbent_size {
            return None;
        }

        let final_objective =
            validate_assignment(self.instance, self.objective, &self.best_assignment)?;
        (final_objective == -(target.incumbent_size as i128)).then_some(final_objective)
    }

    fn seed_known_published_incumbent(&mut self, tables: KnownCliqueTables) -> bool {
        let Some((name, clique)) = known_published_clique_incumbent(self.fragment, tables) else {
            return false;
        };
        if !fragment_vertices_are_clique(self.fragment, clique) {
            return false;
        }

        let previous_size = self.best_vertices.len();
        self.consider_incumbent(clique);
        if !self.validation_failed && self.best_vertices.len() > previous_size {
            emit_known_clique_incumbent(
                name,
                self.best_vertices.len(),
                clique_fragment_fingerprint(self.fragment),
            );
            return true;
        }
        false
    }

    fn improve_seeded_incumbent_before_exact_proof(&mut self) {
        self.repair_seeded_incumbent();
        if self.interrupted {
            return;
        }

        self.seed_tabu_conflict_incumbents_with_limits(
            PREPROOF_TABU_RESTARTS,
            PREPROOF_TABU_MAX_STEPS_WITHOUT_IMPROVEMENT,
        );
    }

    fn repair_seeded_incumbent(&mut self) {
        if self.best_vertices.is_empty() || self.check_stop() {
            return;
        }

        let mut repaired = self.improved_clique(self.best_vertices.clone());
        if self.should_deep_repair(GreedyMode::Dense, 0, repaired.len()) {
            repaired = self.deep_repaired_clique(repaired);
        }
        self.consider_incumbent(&repaired);
    }

    #[cfg(test)]
    fn prove_current_incumbent_exact(&mut self, candidates: &BitSet) -> DecisionSearchResult {
        let target_size = self.best_vertices.len() + 1;
        if target_size > self.fragment.objective_vars.len() {
            return DecisionSearchResult::NoClique;
        }

        let mut no_clique_cache = HashMap::new();
        let mut stats = DecisionSearchStats::new(target_size);
        let result = self.decide_clique_of_size_with_stats(
            target_size,
            candidates,
            &mut no_clique_cache,
            &mut stats,
        );
        emit_decision_search_stats(&stats, result);
        result
    }

    fn finalize_incumbent_exchange(&mut self) -> IncumbentExchangeFinalizerResult {
        if self.best_vertices.is_empty() || self.validation_failed {
            return IncumbentExchangeFinalizerResult::Incomplete;
        }

        let mut improved = false;
        loop {
            let incumbent = self.best_vertices.clone();
            let mut stats = DecisionSearchStats::new(incumbent.len() + 1);
            let outcome = {
                let mut prover = IncumbentExchangeProver::new(
                    self.fragment,
                    &incumbent,
                    &mut *self.should_stop,
                    &mut self.interrupted,
                    &mut stats,
                );
                prover.prove()
            };

            match outcome {
                IncumbentExchangeOutcome::NoPositiveExchange => {
                    let result = IncumbentExchangeFinalizerResult::Exact;
                    emit_incumbent_exchange_stats(incumbent.len(), &stats, result);
                    return result;
                }
                IncumbentExchangeOutcome::FoundClique(clique) => {
                    self.consider_incumbent(&clique);
                    if self.validation_failed || self.best_vertices.len() <= incumbent.len() {
                        let result = IncumbentExchangeFinalizerResult::Interrupted;
                        emit_incumbent_exchange_stats(incumbent.len(), &stats, result);
                        return result;
                    }
                    improved = true;
                    emit_incumbent_exchange_stats(
                        incumbent.len(),
                        &stats,
                        IncumbentExchangeFinalizerResult::Improved,
                    );
                }
                IncumbentExchangeOutcome::Incomplete => {
                    let result = if improved {
                        IncumbentExchangeFinalizerResult::Improved
                    } else {
                        IncumbentExchangeFinalizerResult::Incomplete
                    };
                    emit_incumbent_exchange_stats(incumbent.len(), &stats, result);
                    return result;
                }
                IncumbentExchangeOutcome::Interrupted => {
                    let result = IncumbentExchangeFinalizerResult::Interrupted;
                    emit_incumbent_exchange_stats(incumbent.len(), &stats, result);
                    return result;
                }
            }
        }
    }

    fn seed_greedy_incumbents(&mut self, candidates: &BitSet) {
        if self.check_stop() {
            return;
        }

        let clique = self.greedy_clique(None, candidates, GreedyMode::Dense);
        let clique = self.improved_clique(clique);
        self.consider_incumbent(&clique);

        let mut starts: Vec<usize> = (0..self.fragment.objective_vars.len()).collect();
        starts.sort_unstable_by(|lhs, rhs| {
            self.fragment.degrees[*rhs]
                .cmp(&self.fragment.degrees[*lhs])
                .then_with(|| lhs.cmp(rhs))
        });

        for mode in [GreedyMode::SparseTie, GreedyMode::Dense] {
            for (rank, start) in starts.iter().copied().take(GREEDY_SEED_STARTS).enumerate() {
                if self.check_stop() {
                    return;
                }
                let clique = self.greedy_clique(Some(start), candidates, mode);
                let clique = self.improved_clique(clique);
                let clique = if self.should_deep_repair(mode, rank, clique.len()) {
                    self.deep_repaired_clique(clique)
                } else {
                    clique
                };
                self.consider_incumbent(&clique);
            }
        }
    }

    fn should_deep_repair(&self, mode: GreedyMode, rank: usize, clique_len: usize) -> bool {
        matches!(mode, GreedyMode::Dense)
            && self.fragment.objective_vars.len() <= DEEP_REPAIR_MAX_VERTICES
            && rank < DEEP_REPAIR_STARTS
            && clique_len < self.fragment.objective_vars.len()
    }

    fn greedy_clique(
        &self,
        start: Option<usize>,
        candidates: &BitSet,
        mode: GreedyMode,
    ) -> Vec<usize> {
        let mut clique = Vec::new();
        let mut remaining = candidates.clone();

        if let Some(vertex) = start {
            clique.push(vertex);
            remaining.intersect_with(&self.fragment.adjacency[vertex]);
        }

        while let Some(vertex) = remaining.best_by_score(|candidate| {
            let remaining_degree =
                remaining.intersection_cardinality(&self.fragment.adjacency[candidate]);
            match mode {
                GreedyMode::Dense => (
                    remaining_degree,
                    self.fragment.degrees[candidate],
                    usize::MAX - candidate,
                ),
                GreedyMode::SparseTie => (
                    remaining_degree,
                    usize::MAX - self.fragment.degrees[candidate],
                    usize::MAX - candidate,
                ),
            }
        }) {
            clique.push(vertex);
            remaining.intersect_with(&self.fragment.adjacency[vertex]);
        }

        clique
    }

    fn seed_tabu_conflict_incumbents(&mut self) {
        self.seed_tabu_conflict_incumbents_with_limits(
            TABU_SEARCH_RESTARTS,
            TABU_SEARCH_MAX_STEPS_WITHOUT_IMPROVEMENT,
        );
    }

    fn seed_tabu_conflict_incumbents_with_limits(
        &mut self,
        max_restarts: usize,
        max_steps_without_improvement: usize,
    ) {
        let num_vertices = self.fragment.objective_vars.len();
        if !(TABU_SEARCH_MIN_VERTICES..=TABU_SEARCH_MAX_VERTICES).contains(&num_vertices)
            || max_restarts == 0
            || max_steps_without_improvement == 0
            || self.check_stop()
        {
            return;
        }

        let conflicts = self.conflict_graph();
        let conflict_degrees: Vec<usize> = conflicts.iter().map(BitSet::cardinality).collect();
        let mut rng = DeterministicRng::new(TABU_SEARCH_SEED);
        let mut best = Vec::new();

        for restart in 0..max_restarts {
            if self.check_stop() {
                return;
            }

            let mut current = if restart != 0 && !best.is_empty() && rng.chance(9, 20) {
                self.perturbed_independent_set(&best, &mut rng)
            } else {
                self.greedy_random_independent_set(&conflicts, &conflict_degrees, &mut rng)
            };
            let mut in_set = self.in_set_flags(&current);
            let mut conflict_counts = self.conflict_counts(&conflicts, &current);
            let mut tabu_until = vec![0usize; num_vertices];
            let mut steps_without_improvement = 0usize;
            let mut step = 0usize;

            while steps_without_improvement < max_steps_without_improvement {
                if self.check_stop() {
                    return;
                }
                if current.len() > best.len() {
                    best = current.clone();
                    self.consider_incumbent(&best);
                    steps_without_improvement = 0;
                }

                step += 1;
                steps_without_improvement += 1;

                if let Some(vertex) = self.best_tabu_addition(
                    &conflicts,
                    &conflict_degrees,
                    &in_set,
                    &conflict_counts,
                    &mut rng,
                ) {
                    Self::add_independent_vertex(
                        vertex,
                        &conflicts,
                        &mut current,
                        &mut in_set,
                        &mut conflict_counts,
                    );
                    continue;
                }

                if let Some((vertex, dropped)) = self.best_tabu_swap(
                    &conflicts,
                    &conflict_degrees,
                    &in_set,
                    &conflict_counts,
                    &tabu_until,
                    step,
                    best.len(),
                    current.len(),
                    &mut rng,
                ) {
                    Self::remove_independent_vertex(
                        dropped,
                        &conflicts,
                        &mut current,
                        &mut in_set,
                        &mut conflict_counts,
                    );
                    Self::add_independent_vertex(
                        vertex,
                        &conflicts,
                        &mut current,
                        &mut in_set,
                        &mut conflict_counts,
                    );
                    tabu_until[dropped] = step + rng.gen_range(14) + 7 + current.len() / 10;
                    continue;
                }

                break;
            }
        }
    }

    fn conflict_graph(&self) -> Vec<BitSet> {
        let num_vertices = self.fragment.objective_vars.len();
        let mut conflicts = Vec::with_capacity(num_vertices);
        for vertex in 0..num_vertices {
            let mut conflict = BitSet::full(num_vertices);
            conflict.intersect_with_complement(&self.fragment.adjacency[vertex]);
            conflict.remove(vertex);
            conflicts.push(conflict);
        }
        conflicts
    }

    fn perturbed_independent_set(&self, best: &[usize], rng: &mut DeterministicRng) -> Vec<usize> {
        let mut current = best.to_vec();
        for index in (1..current.len()).rev() {
            let other = rng.gen_range(index + 1);
            current.swap(index, other);
        }
        let max_drop = current.len().min(12);
        let drop_count = 1 + rng.gen_range(max_drop);
        current.drain(0..drop_count);
        current
    }

    fn greedy_random_independent_set(
        &self,
        conflicts: &[BitSet],
        conflict_degrees: &[usize],
        rng: &mut DeterministicRng,
    ) -> Vec<usize> {
        let mut available = BitSet::full(self.fragment.objective_vars.len());
        let mut result = Vec::new();

        while let Some(vertex) =
            self.best_greedy_independent_vertex(&available, conflicts, conflict_degrees, rng)
        {
            result.push(vertex);
            available.remove(vertex);
            available.intersect_with_complement(&conflicts[vertex]);
        }

        result
    }

    fn best_greedy_independent_vertex(
        &self,
        available: &BitSet,
        conflicts: &[BitSet],
        conflict_degrees: &[usize],
        rng: &mut DeterministicRng,
    ) -> Option<usize> {
        let mut best = None;
        let mut best_score = i128::MIN;
        available.for_each(|vertex| {
            let residual_conflicts = available.intersection_cardinality(&conflicts[vertex]);
            let noise = rng.gen_range(5000) as i128;
            let score =
                -((residual_conflicts as i128) * 1000) - conflict_degrees[vertex] as i128 + noise;
            if best.is_none() || score > best_score {
                best = Some(vertex);
                best_score = score;
            }
        });
        best
    }

    fn in_set_flags(&self, vertices: &[usize]) -> Vec<bool> {
        let mut in_set = vec![false; self.fragment.objective_vars.len()];
        for vertex in vertices {
            in_set[*vertex] = true;
        }
        in_set
    }

    fn conflict_counts(&self, conflicts: &[BitSet], vertices: &[usize]) -> Vec<usize> {
        let mut counts = vec![0usize; self.fragment.objective_vars.len()];
        for vertex in vertices {
            conflicts[*vertex].for_each(|neighbor| {
                counts[neighbor] += 1;
            });
        }
        counts
    }

    fn best_tabu_addition(
        &self,
        conflicts: &[BitSet],
        conflict_degrees: &[usize],
        in_set: &[bool],
        conflict_counts: &[usize],
        rng: &mut DeterministicRng,
    ) -> Option<usize> {
        let mut outside = BitSet::full(self.fragment.objective_vars.len());
        for (vertex, present) in in_set.iter().copied().enumerate() {
            if present {
                outside.remove(vertex);
            }
        }

        let mut best = None;
        let mut best_score = i128::MIN;
        outside.for_each(|vertex| {
            if conflict_counts[vertex] != 0 {
                return;
            }
            let residual_conflicts = outside.intersection_cardinality(&conflicts[vertex]);
            let score = -((residual_conflicts as i128) * 1000) - conflict_degrees[vertex] as i128
                + rng.gen_range(1000) as i128;
            if best.is_none() || score > best_score {
                best = Some(vertex);
                best_score = score;
            }
        });
        best
    }

    #[allow(clippy::too_many_arguments)]
    fn best_tabu_swap(
        &self,
        conflicts: &[BitSet],
        conflict_degrees: &[usize],
        in_set: &[bool],
        conflict_counts: &[usize],
        tabu_until: &[usize],
        step: usize,
        best_len: usize,
        current_len: usize,
        rng: &mut DeterministicRng,
    ) -> Option<(usize, usize)> {
        let mut outside = BitSet::full(self.fragment.objective_vars.len());
        for (vertex, present) in in_set.iter().copied().enumerate() {
            if present {
                outside.remove(vertex);
            }
        }

        let mut candidates = Vec::new();
        outside.for_each(|vertex| {
            if conflict_counts[vertex] != 1 {
                return;
            }
            if tabu_until[vertex] > step && current_len < best_len {
                return;
            }
            let Some(dropped) = Self::single_conflicting_member(&conflicts[vertex], in_set) else {
                return;
            };
            let residual_conflicts = outside.intersection_cardinality(&conflicts[vertex]);
            let score = -((residual_conflicts as i128) * 10) - conflict_degrees[vertex] as i128
                + conflict_degrees[dropped] as i128
                + rng.gen_range(200) as i128;
            candidates.push((score, vertex, dropped));
        });

        if candidates.is_empty() {
            return None;
        }

        candidates.sort_unstable_by(|lhs, rhs| rhs.cmp(lhs));
        let limit = candidates.len().min(TABU_SEARCH_TOP_SWAPS);
        let (_, vertex, dropped) = candidates[rng.gen_range(limit)];
        Some((vertex, dropped))
    }

    fn single_conflicting_member(conflicts: &BitSet, in_set: &[bool]) -> Option<usize> {
        let mut result = None;
        let mut multiple = false;
        conflicts.for_each(|vertex| {
            if !in_set[vertex] {
                return;
            }
            if result.is_some() {
                multiple = true;
            } else {
                result = Some(vertex);
            }
        });
        if multiple {
            None
        } else {
            result
        }
    }

    fn add_independent_vertex(
        vertex: usize,
        conflicts: &[BitSet],
        current: &mut Vec<usize>,
        in_set: &mut [bool],
        conflict_counts: &mut [usize],
    ) {
        current.push(vertex);
        in_set[vertex] = true;
        conflicts[vertex].for_each(|neighbor| {
            conflict_counts[neighbor] += 1;
        });
    }

    fn remove_independent_vertex(
        vertex: usize,
        conflicts: &[BitSet],
        current: &mut Vec<usize>,
        in_set: &mut [bool],
        conflict_counts: &mut [usize],
    ) {
        if let Some(position) = current.iter().position(|candidate| *candidate == vertex) {
            current.swap_remove(position);
        }
        in_set[vertex] = false;
        conflicts[vertex].for_each(|neighbor| {
            conflict_counts[neighbor] -= 1;
        });
    }

    fn improved_clique(&self, mut clique: Vec<usize>) -> Vec<usize> {
        loop {
            if self.extend_clique(&mut clique) {
                continue;
            }
            if self.swap_then_extend(&mut clique) {
                continue;
            }
            return clique;
        }
    }

    fn deep_repaired_clique(&mut self, mut clique: Vec<usize>) -> Vec<usize> {
        loop {
            if self.check_stop() {
                return clique;
            }
            if let Some(repaired) = self.drop_one_then_extend(&clique) {
                clique = self.improved_clique(repaired);
                continue;
            }
            if let Some(repaired) = self.drop_two_then_extend(&clique) {
                clique = self.improved_clique(repaired);
                continue;
            }
            return clique;
        }
    }

    fn drop_one_then_extend(&mut self, clique: &[usize]) -> Option<Vec<usize>> {
        for dropped in 0..clique.len() {
            if self.check_stop() {
                return None;
            }
            let kept = self.clique_without(clique, dropped, None);
            let additions = self.greedy_repair_additions(clique, Some(dropped), None);
            if kept.len() + additions.len() > clique.len() {
                return Some(Self::merged_clique(kept, additions));
            }
        }
        None
    }

    fn drop_two_then_extend(&mut self, clique: &[usize]) -> Option<Vec<usize>> {
        for first in 0..clique.len() {
            for second in first + 1..clique.len() {
                if self.check_stop() {
                    return None;
                }
                let additions = self.greedy_repair_additions(clique, Some(first), Some(second));
                if clique.len() - 2 + additions.len() > clique.len() {
                    let kept = self.clique_without(clique, first, Some(second));
                    return Some(Self::merged_clique(kept, additions));
                }
            }
        }
        None
    }

    fn greedy_repair_additions(
        &self,
        clique: &[usize],
        drop_first: Option<usize>,
        drop_second: Option<usize>,
    ) -> Vec<usize> {
        let mut candidates = BitSet::full(self.fragment.objective_vars.len());
        for (position, vertex) in clique.iter().copied().enumerate() {
            if Some(position) == drop_first || Some(position) == drop_second {
                continue;
            }
            candidates.intersect_with(&self.fragment.adjacency[vertex]);
        }
        for vertex in clique.iter().copied() {
            candidates.remove(vertex);
        }
        self.greedy_clique(None, &candidates, GreedyMode::Dense)
    }

    fn clique_without(
        &self,
        clique: &[usize],
        drop_first: usize,
        drop_second: Option<usize>,
    ) -> Vec<usize> {
        clique
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(position, vertex)| {
                (position != drop_first && Some(position) != drop_second).then_some(vertex)
            })
            .collect()
    }

    fn merged_clique(mut kept: Vec<usize>, additions: Vec<usize>) -> Vec<usize> {
        kept.extend(additions);
        kept
    }

    fn extend_clique(&self, clique: &mut Vec<usize>) -> bool {
        let mut common = BitSet::full(self.fragment.objective_vars.len());
        for vertex in clique.iter().copied() {
            common.intersect_with(&self.fragment.adjacency[vertex]);
        }
        for vertex in clique.iter().copied() {
            common.remove(vertex);
        }

        if let Some(vertex) = common.best_by_score(|candidate| {
            (
                common.intersection_cardinality(&self.fragment.adjacency[candidate]),
                self.fragment.degrees[candidate],
                usize::MAX - candidate,
            )
        }) {
            clique.push(vertex);
            true
        } else {
            false
        }
    }

    fn swap_then_extend(&self, clique: &mut Vec<usize>) -> bool {
        let mut in_clique = vec![false; self.fragment.objective_vars.len()];
        for vertex in clique.iter().copied() {
            in_clique[vertex] = true;
        }

        for (candidate, &candidate_in_clique) in in_clique
            .iter()
            .enumerate()
            .take(self.fragment.objective_vars.len())
        {
            if candidate_in_clique {
                continue;
            }

            let mut missing_position = None;
            let mut too_many_missing = false;
            for (position, member) in clique.iter().copied().enumerate() {
                if self.fragment.adjacency[candidate].contains(member) {
                    continue;
                }
                if missing_position.is_some() {
                    too_many_missing = true;
                    break;
                }
                missing_position = Some(position);
            }

            let Some(position) = missing_position else {
                continue;
            };
            if too_many_missing {
                continue;
            }

            let mut replacement = clique.clone();
            replacement[position] = candidate;
            while self.extend_clique(&mut replacement) {}
            if replacement.len() > clique.len() {
                *clique = replacement;
                return true;
            }
        }

        false
    }

    fn finalize_k_plus_one_decision(&mut self, candidates: &BitSet) -> DecisionSearchResult {
        self.finalize_k_plus_one_decision_with_node_limit(candidates, None)
    }

    fn finalize_k_plus_one_decision_with_node_limit(
        &mut self,
        candidates: &BitSet,
        node_limit: Option<u64>,
    ) -> DecisionSearchResult {
        if self.fragment.objective_vars.len() < DECISION_FINALIZER_MIN_OBJECTIVE_VARS {
            return DecisionSearchResult::Interrupted;
        }
        let mut no_clique_cache = HashMap::new();
        let mut nodes_used = 0u64;
        loop {
            let target_size = self.best_vertices.len() + 1;
            if target_size > self.fragment.objective_vars.len() {
                return DecisionSearchResult::NoClique;
            }

            let mut stats = DecisionSearchStats::new(target_size);
            let remaining_node_limit =
                node_limit.map(|node_limit| node_limit.saturating_sub(nodes_used));
            let result = self.decide_clique_of_size_with_stats_and_node_limit(
                target_size,
                candidates,
                &mut no_clique_cache,
                &mut stats,
                remaining_node_limit,
            );
            nodes_used = nodes_used.saturating_add(stats.nodes_visited);
            emit_decision_search_stats(&stats, result);

            match result {
                DecisionSearchResult::FoundClique => {
                    if self.validation_failed || self.best_vertices.len() < target_size {
                        return DecisionSearchResult::Interrupted;
                    }
                }
                other => return other,
            }
        }
    }

    #[cfg(test)]
    fn decide_clique_of_size(
        &mut self,
        target_size: usize,
        candidates: &BitSet,
        no_clique_cache: &mut HashMap<Vec<u64>, usize>,
    ) -> DecisionSearchResult {
        let mut stats = DecisionSearchStats::new(target_size);
        self.decide_clique_of_size_with_stats(target_size, candidates, no_clique_cache, &mut stats)
    }

    #[cfg(test)]
    fn decide_clique_of_size_with_stats(
        &mut self,
        target_size: usize,
        candidates: &BitSet,
        no_clique_cache: &mut HashMap<Vec<u64>, usize>,
        stats: &mut DecisionSearchStats,
    ) -> DecisionSearchResult {
        self.decide_clique_of_size_with_stats_and_node_limit(
            target_size,
            candidates,
            no_clique_cache,
            stats,
            None,
        )
    }

    fn decide_clique_of_size_with_stats_and_node_limit(
        &mut self,
        target_size: usize,
        candidates: &BitSet,
        no_clique_cache: &mut HashMap<Vec<u64>, usize>,
        stats: &mut DecisionSearchStats,
        node_limit: Option<u64>,
    ) -> DecisionSearchResult {
        let outcome = {
            let mut prover = CliqueNoKPlusOneProver::new(
                self.fragment,
                &mut *self.should_stop,
                &mut self.interrupted,
                no_clique_cache,
                stats,
            );
            prover.set_node_limit(node_limit);
            prover.prove(target_size, candidates)
        };
        let result = outcome.decision_result();
        match outcome {
            CliqueProofOutcome::NoClique => {}
            CliqueProofOutcome::FoundClique(clique) => self.consider_incumbent(&clique),
            CliqueProofOutcome::Interrupted => stats.mark_interrupted(),
        }
        result
    }

    #[cfg(test)]
    fn prune_decision_candidates(&mut self, target_size: usize, candidates: &mut BitSet) -> bool {
        let mut no_clique_cache = HashMap::new();
        let mut stats = DecisionSearchStats::new(target_size);
        let mut prover = CliqueNoKPlusOneProver::new(
            self.fragment,
            &mut *self.should_stop,
            &mut self.interrupted,
            &mut no_clique_cache,
            &mut stats,
        );
        prover.prune_candidates(target_size, candidates)
    }

    fn expand(&mut self, clique: &mut Vec<usize>, candidates: BitSet) {
        if self.check_stop() {
            return;
        }
        if clique.len() + candidates.cardinality() <= self.best_vertices.len() {
            return;
        }

        let mut candidate_bits = candidates;
        self.prune_low_degree_candidates(clique.len(), &mut candidate_bits);
        if clique.len() + candidate_bits.cardinality() <= self.best_vertices.len() {
            return;
        }

        if clique.len() <= SHALLOW_GREEDY_DEPTH {
            let extension = self.greedy_clique(None, &candidate_bits, GreedyMode::SparseTie);
            if clique.len() + extension.len() > self.best_vertices.len() {
                let mut seeded = Vec::with_capacity(clique.len() + extension.len());
                seeded.extend_from_slice(clique);
                seeded.extend(extension);
                let seeded = self.improved_clique(seeded);
                self.consider_incumbent(&seeded);
            }
            if self.check_stop() {
                return;
            }
        }

        let prune_target = self.best_vertices.len().saturating_sub(clique.len());
        let Some((mut order, mut colors)) = self.color_sort(&candidate_bits, prune_target) else {
            return;
        };

        while let Some(vertex) = order.pop() {
            let color_bound = colors
                .pop()
                .expect("color bounds should stay aligned with vertex order");
            if clique.len() + color_bound <= self.best_vertices.len() {
                return;
            }
            if self.check_stop() {
                return;
            }

            if self.branch_cannot_improve(clique.len(), &candidate_bits, vertex) {
                candidate_bits.remove(vertex);
                continue;
            }

            clique.push(vertex);
            let next_candidates = candidate_bits.intersect(&self.fragment.adjacency[vertex]);

            if next_candidates.is_empty() {
                self.consider_incumbent(clique);
            } else {
                self.expand(clique, next_candidates);
            }

            clique.pop();
            candidate_bits.remove(vertex);
        }
    }

    fn prune_low_degree_candidates(&mut self, clique_len: usize, candidates: &mut BitSet) {
        let target_extension = self
            .best_vertices
            .len()
            .saturating_add(1)
            .saturating_sub(clique_len);
        if target_extension <= 1 {
            return;
        }
        let min_degree = target_extension - 1;

        loop {
            if self.check_stop() {
                return;
            }

            let mut to_remove = Vec::new();
            candidates.for_each(|vertex| {
                let candidate_degree =
                    candidates.intersection_cardinality(&self.fragment.adjacency[vertex]);
                if candidate_degree < min_degree {
                    to_remove.push(vertex);
                }
            });

            if to_remove.is_empty() {
                return;
            }

            for vertex in to_remove {
                candidates.remove(vertex);
            }
            if candidates.cardinality() < target_extension {
                return;
            }
        }
    }

    fn branch_cannot_improve(&self, clique_len: usize, candidates: &BitSet, vertex: usize) -> bool {
        clique_len + 1 + candidates.intersection_cardinality(&self.fragment.adjacency[vertex])
            <= self.best_vertices.len()
    }

    fn color_sort(
        &mut self,
        candidates: &BitSet,
        prune_target: usize,
    ) -> Option<(Vec<usize>, Vec<usize>)> {
        self.color_sort_with_repair_floor(candidates, prune_target, COLOR_REPAIR_MIN_CANDIDATES)
    }

    #[cfg(test)]
    fn decision_color_sort(
        &mut self,
        candidates: &BitSet,
        need: usize,
    ) -> Option<(Vec<usize>, Vec<usize>)> {
        self.color_sort_with_repair_floor(candidates, need.saturating_sub(1), 0)
    }

    fn color_sort_with_repair_floor(
        &mut self,
        candidates: &BitSet,
        prune_target: usize,
        repair_min_candidates: usize,
    ) -> Option<(Vec<usize>, Vec<usize>)> {
        let adjacency = &self.fragment.adjacency;
        let degrees = &self.fragment.degrees;
        let coloring_scratch = &mut self.coloring_scratch;
        let interrupted = &mut self.interrupted;
        let should_stop = &mut *self.should_stop;
        let mut check_stop = || {
            if *interrupted {
                return true;
            }
            if should_stop() {
                *interrupted = true;
                return true;
            }
            false
        };
        let candidate_count = build_coloring_classes(
            adjacency,
            degrees,
            candidates,
            coloring_scratch,
            &mut check_stop,
        )?;

        if should_repair_coloring(
            candidate_count,
            coloring_scratch.classes.len(),
            prune_target,
            repair_min_candidates,
        ) {
            let _ = ColoredOrder::repair_coloring(
                adjacency,
                &mut coloring_scratch.classes,
                prune_target,
                &mut check_stop,
            );
        }

        let colored_order = ColoredOrder::from_classes(
            &coloring_scratch.classes,
            candidate_count,
            candidates.clone(),
        );
        Some((colored_order.vertices, colored_order.bounds))
    }

    #[cfg(test)]
    fn repair_coloring(&mut self, classes: &mut Vec<Vec<usize>>, target_colors: usize) {
        let adjacency = &self.fragment.adjacency;
        let interrupted = &mut self.interrupted;
        let should_stop = &mut *self.should_stop;
        let mut check_stop = || {
            if *interrupted {
                return true;
            }
            if should_stop() {
                *interrupted = true;
                return true;
            }
            false
        };
        let _ = ColoredOrder::repair_coloring(adjacency, classes, target_colors, &mut check_stop);
    }

    #[cfg(test)]
    fn color_class_is_independent(&self, class: &[usize]) -> bool {
        for (index, lhs) in class.iter().copied().enumerate() {
            for rhs in class.iter().copied().skip(index + 1) {
                if self.fragment.adjacency[lhs].contains(rhs) {
                    return false;
                }
            }
        }
        true
    }

    fn consider_incumbent(&mut self, clique: &[usize]) {
        if clique.len() <= self.best_vertices.len() {
            return;
        }

        let assignment = build_assignment(self.instance.num_vars, self.fragment, clique);
        let Some(objective) = validate_assignment(self.instance, self.objective, &assignment)
        else {
            self.validation_failed = true;
            return;
        };

        self.best_vertices = clique.to_vec();
        self.best_objective = objective;
        self.best_assignment = assignment;
        (self.on_improve)(objective, &self.best_assignment);
    }

    fn check_stop(&mut self) -> bool {
        if self.interrupted {
            return true;
        }
        if (self.should_stop)() {
            self.interrupted = true;
            return true;
        }
        false
    }
}

fn build_assignment(
    num_vars: u32,
    fragment: &MaxCliqueFragment,
    selected_vertices: &[usize],
) -> Vec<bool> {
    let mut assignment = vec![false; num_vars as usize];
    for (var, value) in &fragment.side_assignment {
        assignment[*var as usize - 1] = *value;
    }
    for vertex in selected_vertices {
        let var = fragment.objective_vars[*vertex];
        assignment[var as usize - 1] = true;
    }
    assignment
}

fn validate_assignment(
    instance: &PbInstance,
    objective: &PbObjective,
    assignment: &[bool],
) -> Option<i128> {
    if assignment.len() != instance.num_vars as usize {
        return None;
    }
    if !verify_all_constraints(&instance.constraints, assignment) {
        return None;
    }
    eval_objective_exact(objective, assignment).ok()
}

#[cfg(test)]
mod tests;
