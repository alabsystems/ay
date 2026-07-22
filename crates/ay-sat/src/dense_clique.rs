// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read-only dense clique/coloring/mutex structure scouting.
//!
//! The scout recognizes a narrow DIMACS-visible structure: disjoint positive
//! support clauses of equal width plus deterministic negative binary mutexes:
//! row-internal exclusions, same-vertex cross-row exclusions, and all-or-none
//! cross-row exclusions that recover graph non-edges. It never derives
//! SAT/UNSAT and never mutates a solver; callers use it only for default-off
//! route telemetry until an original-DIMACS proof/model path exists.

use crate::literal::Literal;
use std::collections::{BTreeMap, BTreeSet};

const MAX_SCOUT_VARS: usize = 4_096;

/// Deterministic read-only scout result for dense clique/coloring mutex CNFs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliqueScout {
    /// Number of variables declared by the DIMACS header.
    pub num_vars: usize,
    /// Number of clauses supplied to the scout.
    pub num_clauses: usize,
    /// Positive support clauses considered as color/slot rows.
    pub positive_support_clauses: usize,
    /// Negative binary mutex clauses over distinct variables.
    pub negative_binary_mutexes: usize,
    /// Clauses outside the strict support/mutex surface.
    pub other_clauses: usize,
    /// Exact recovered structure when the strict scout accepts.
    pub structure: Option<DenseCliqueStructure>,
    /// Fail-closed rejection reason when no exact structure is available.
    pub rejection: DenseCliqueRejection,
}

/// Recovered dense clique/coloring mutex structure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliqueStructure {
    /// Number of graph vertices inferred from each support row width.
    pub graph_vertices: usize,
    /// Number of colors/slots inferred from the support row count.
    pub colors: usize,
    /// Number of Boolean variables covered by the support rows.
    pub variables: usize,
    /// Observed negative binary mutex clauses.
    pub mutexes: usize,
    /// Expected mutex clauses for the recovered clique/coloring surface.
    pub expected_mutexes: usize,
    /// Recovered compatibility edges between graph vertices.
    pub graph_edges: usize,
    /// Recovered graph non-edges between graph vertices.
    pub graph_non_edges: usize,
    /// Number of connected components in the graph-complement relation.
    pub graph_non_edge_buckets: usize,
    /// Smallest graph-complement component size.
    pub graph_non_edge_bucket_min: usize,
    /// Largest graph-complement component size.
    pub graph_non_edge_bucket_max: usize,
    /// Whether graph non-edges form disjoint cliques, i.e. a complete multipartite graph.
    pub complete_multipartite: bool,
    /// Pigeons in the recovered PHP obligation.
    pub php_pigeons: usize,
    /// Holes in the recovered PHP obligation.
    pub php_holes: usize,
    /// Whether the recovered bucket obligation proves UNSAT by PHP.
    pub php_unsat_obligation: bool,
    /// Number of positive support clauses in the structure.
    pub positive_support_clauses: usize,
    /// Width of each positive support clause.
    pub support_width: usize,
}

/// Source clause with the original one-based DIMACS row identity preserved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliqueSourceClause {
    /// One-based source clause identifier from the original DIMACS stream.
    pub source_id: usize,
    /// Original DIMACS literals before the terminating zero.
    pub raw_dimacs: Vec<i32>,
    /// Parsed literals for the same row.
    pub literals: Vec<Literal>,
}

/// Deterministic source-clause construction counters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliqueSourceClauseAudit {
    /// Parsed DIMACS clauses scanned.
    pub clauses_seen: usize,
    /// Source rows materialized with one-based contiguous source IDs.
    pub source_rows: usize,
    /// Total literal cells copied into `raw_dimacs`.
    pub raw_dimacs_literals: usize,
    /// Empty original clauses seen while copying source rows.
    pub empty_clause_rows: usize,
    /// First one-based source clause ID, if any.
    pub first_source_id: Option<usize>,
    /// Last one-based source clause ID, if any.
    pub last_source_id: Option<usize>,
}

/// Source rows plus construction audit for future dense-clique route ingress.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliqueSourceClauseRows {
    /// Source rows with one-based original DIMACS IDs.
    pub clauses: Vec<DenseCliqueSourceClause>,
    /// Result-silent source construction counters.
    pub audit: DenseCliqueSourceClauseAudit,
}

/// Positive support row witness preserving the original source row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliqueSupportRowWitness {
    /// One-based source clause identifier.
    pub source_id: usize,
    /// Original DIMACS literals before the terminating zero.
    pub raw_dimacs: Vec<i32>,
    /// Zero-based variable indices in sorted row order.
    pub variables: Vec<usize>,
}

/// Negative binary mutex witness preserving the original source row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliqueMutexWitness {
    /// One-based source clause identifier.
    pub source_id: usize,
    /// Original DIMACS literals before the terminating zero.
    pub raw_dimacs: Vec<i32>,
    /// Lower zero-based variable index in the mutex pair.
    pub lhs_variable: usize,
    /// Higher zero-based variable index in the mutex pair.
    pub rhs_variable: usize,
}

/// Recovered graph-pair witness over support-row vertex positions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliqueGraphPairWitness {
    /// Left graph vertex position.
    pub lhs_vertex: usize,
    /// Right graph vertex position.
    pub rhs_vertex: usize,
    /// Whether the pair is a graph edge, i.e. no cross-row exclusion was present.
    pub graph_edge: bool,
    /// Source row IDs for all cross-row mutexes proving a graph non-edge.
    pub cross_mutex_source_ids: Vec<usize>,
}

/// Witness for the PHP obligation induced by graph-complement buckets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliquePhpObligation {
    /// Pigeons in the recovered PHP obligation.
    pub pigeons: usize,
    /// Holes in the recovered PHP obligation.
    pub holes: usize,
    /// Graph vertex buckets that form PHP holes.
    pub bucket_vertices: Vec<Vec<usize>>,
    /// Whether the obligation is UNSAT by pigeonhole principle.
    pub unsat_obligation: bool,
}

/// Source-only replay ledger for the dense-clique PHP proof obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliquePhpReplayLedger {
    /// Original declared variables before planned extensions.
    pub original_vars: usize,
    /// Original DIMACS clause count before planned derived rows.
    pub original_clauses: usize,
    /// Pigeons in the PHP obligation.
    pub pigeons: usize,
    /// Holes in the PHP obligation.
    pub holes: usize,
    /// Recovered graph-complement buckets in deterministic order.
    pub bucket_vertices: Vec<Vec<usize>>,
    /// First planned extension variable, one-based.
    pub extension_var_start_one_based: usize,
    /// Last planned extension variable, one-based.
    pub extension_var_end_one_based: usize,
    /// First planned extension-definition clause ID.
    pub extension_clause_id_start: usize,
    /// Last planned extension-definition clause ID.
    pub extension_clause_id_end: usize,
    /// First derived bucket ALO clause ID.
    pub bucket_alo_clause_id_start: usize,
    /// Last derived bucket ALO clause ID.
    pub bucket_alo_clause_id_end: usize,
    /// First derived bucket mutex clause ID.
    pub bucket_mutex_clause_id_start: usize,
    /// Last derived bucket mutex clause ID.
    pub bucket_mutex_clause_id_end: usize,
    /// Planned extension definitions, three clauses per row.
    pub extension_rows: Vec<DenseCliquePhpExtensionReplayRow>,
    /// Derived bucket ALO rows, one per pigeon.
    pub bucket_alo_rows: Vec<DenseCliquePhpBucketAloReplayRow>,
    /// Derived bucket mutex rows, one per hole and pigeon pair.
    pub bucket_mutex_rows: Vec<DenseCliquePhpBucketMutexReplayRow>,
}

/// Result-silent dense-clique PHP replay packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliquePhpReplayPacket {
    /// Source-ingress counters for original DIMACS rows.
    pub source_audit: DenseCliqueSourceClauseAudit,
    /// Recovered dense-clique witness.
    pub witness: DenseCliqueWitness,
    /// Source-only PHP replay ledger.
    pub replay_ledger: DenseCliquePhpReplayLedger,
    /// Hard false until a separate legal route gate emits a checked proof.
    pub route_admitted: bool,
    /// Hard false: this packet never authorizes solver results.
    pub result_authority: bool,
    /// Hard false: UNSAT stdout is outside this packet.
    pub unsat_output_authority: bool,
    /// Hard false: proof output is outside this packet.
    pub proof_output_authority: bool,
    /// Hard false: model output is outside this packet.
    pub model_output_authority: bool,
}

/// Default-off controls for checker-visible dense-clique PHP row audits.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DenseCliquePhpCheckerAuditConfig {
    /// Enables pure row materialization. Default false keeps the slice inert.
    pub enabled: bool,
}

/// Checker-visible planned row kind for dense-clique PHP obligations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DenseCliquePhpCheckerVisibleRowKind {
    /// Extension row encoding `original -> bucket_extension`.
    ExtensionForward,
    /// Extension row encoding `bucket_extension -> original_lhs or original_rhs`.
    ExtensionBackward,
    /// Derived bucket at-least-one row for one pigeon.
    BucketAlo,
    /// Derived bucket mutex row for one hole and pigeon pair.
    BucketMutex,
}

/// Original source row dependency retained with a checker-visible audit row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliquePhpCheckerSourceRow {
    /// One-based original DIMACS source clause id.
    pub source_id: usize,
    /// Original DIMACS literals before the terminating zero.
    pub raw_dimacs: Vec<i32>,
}

/// One planned checker-visible row for the dense-clique PHP proof obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliquePhpCheckerVisibleRow {
    /// Planned row kind.
    pub row_kind: DenseCliquePhpCheckerVisibleRowKind,
    /// Planned checker-visible clause id.
    pub checker_visible_id: usize,
    /// Planned DIMACS literals for this row.
    pub clause_lits_dimacs: Vec<i32>,
    /// Original source rows consumed by this obligation row.
    pub source_rows: Vec<DenseCliquePhpCheckerSourceRow>,
    /// Planned non-source clause ids consumed by this obligation row.
    pub dependency_clause_ids: Vec<usize>,
    /// External checker verdict. This materializer never accepts one.
    pub external_checker_verified: bool,
}

/// Aggregate counters for dense-clique PHP checker-row materialization.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DenseCliquePhpCheckerAuditStats {
    /// Whether the materializer was explicitly enabled.
    pub enabled: bool,
    /// Original source rows audited through the replay packet.
    pub source_rows_audited: u64,
    /// Planned extension rows inspected.
    pub extension_rows_seen: u64,
    /// Planned bucket ALO rows inspected.
    pub bucket_alo_rows_seen: u64,
    /// Planned bucket mutex rows inspected.
    pub bucket_mutex_rows_seen: u64,
    /// Checker-visible rows materialized.
    pub checker_rows_materialized: u64,
    /// Extension-definition checker rows materialized.
    pub extension_definition_rows_materialized: u64,
    /// Bucket ALO checker rows materialized.
    pub bucket_alo_rows_materialized: u64,
    /// Bucket mutex checker rows materialized.
    pub bucket_mutex_rows_materialized: u64,
    /// Original source-row dependency edges retained.
    pub source_dependency_edges: u64,
    /// Planned derived-clause dependency edges retained.
    pub dependency_clause_edges: u64,
    /// Rows accepted as externally checked. Always zero here.
    pub external_checker_verified_rows: u64,
}

/// Result-silent checker-visible row audit for the dense-clique PHP route.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliquePhpCheckerAudit {
    /// Materialized checker-visible rows.
    pub rows: Vec<DenseCliquePhpCheckerVisibleRow>,
    /// Counters for the materialization attempt.
    pub stats: DenseCliquePhpCheckerAuditStats,
    /// Hard false until a separate legal route gate emits a checked proof.
    pub route_admitted: bool,
    /// Hard false: this audit never authorizes solver results.
    pub result_authority: bool,
    /// Hard false: UNSAT stdout is outside this audit.
    pub unsat_output_authority: bool,
    /// Hard false: proof output is outside this audit.
    pub proof_output_authority: bool,
    /// Hard false: model output is outside this audit.
    pub model_output_authority: bool,
    /// Hard false: no external checker verdict is accepted here.
    pub external_checker_verified: bool,
}

/// Default-off controls for original-DIMACS DRAT materialization from a compact PHP proof.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DenseCliquePhpOriginalDratMaterializerConfig {
    /// Enables proof-text materialization. Default false keeps the helper inert.
    pub enabled: bool,
}

/// Aggregate counters for original-DIMACS DRAT materialization.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DenseCliquePhpOriginalDratMaterializationStats {
    /// Whether the materializer was explicitly enabled.
    pub enabled: bool,
    /// Original source rows audited through the replay packet.
    pub source_rows_audited: u64,
    /// Compact PHP variables covered by the replay ledger.
    pub compact_variables: u64,
    /// Compact PHP clauses covered by bucket ALO and mutex rows.
    pub compact_clauses: u64,
    /// Extension definition clauses added to the original-DIMACS proof.
    pub extension_clauses_added: u64,
    /// Bucket ALO clauses added to the original-DIMACS proof.
    pub bucket_alo_clauses_added: u64,
    /// Bucket mutex clauses added to the original-DIMACS proof.
    pub bucket_mutex_clauses_added: u64,
    /// Bucket ALO plus bucket mutex clauses added before replaying the compact proof.
    pub planned_bucket_clauses_added: u64,
    /// Support clauses inserted before bucket mutex clauses.
    pub bucket_mutex_support_clauses_added: u64,
    /// Non-comment compact proof lines replayed.
    pub compact_proof_lines_seen: u64,
    /// Compact proof comment lines skipped.
    pub compact_proof_comments_skipped: u64,
    /// Compact proof addition lines remapped.
    pub compact_proof_additions_remapped: u64,
    /// Compact proof deletion lines remapped.
    pub compact_proof_deletions_remapped: u64,
    /// Maximum variable id observed in the compact proof.
    pub compact_proof_max_var: usize,
    /// Maximum variable id emitted in the original-DIMACS proof.
    pub original_proof_max_var: usize,
    /// External checker verdicts accepted by this helper. Always zero.
    pub external_checker_verified: u64,
}

/// Result-silent original-DIMACS DRAT materialization artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliquePhpOriginalDratMaterialization {
    /// Materialized DRAT proof text. Empty when the helper is disabled.
    pub drat: String,
    /// Counters for the materialization attempt.
    pub stats: DenseCliquePhpOriginalDratMaterializationStats,
    /// Hard false until a separate legal route gate emits a checked proof.
    pub route_admitted: bool,
    /// Hard false: this artifact never authorizes solver results.
    pub result_authority: bool,
    /// Hard false: UNSAT stdout is outside this artifact.
    pub unsat_output_authority: bool,
    /// Hard false: proof output is outside this artifact.
    pub proof_output_authority: bool,
    /// Hard false: model output is outside this artifact.
    pub model_output_authority: bool,
    /// Hard false: no external checker verdict is accepted here.
    pub external_checker_verified: bool,
}

/// Default-off controls for original-DIMACS LRAT materialization from a compact PHP proof.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DenseCliquePhpOriginalLratMaterializerConfig {
    /// Enables proof-text materialization. Default false keeps the helper inert.
    pub enabled: bool,
}

/// Aggregate counters for original-DIMACS LRAT materialization.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DenseCliquePhpOriginalLratMaterializationStats {
    /// Whether the materializer was explicitly enabled.
    pub enabled: bool,
    /// Original source rows audited through the replay packet.
    pub source_rows_audited: u64,
    /// Compact PHP variables covered by the replay ledger.
    pub compact_variables: u64,
    /// Compact PHP clauses covered by bucket ALO and mutex rows.
    pub compact_clauses: u64,
    /// Extension definition clauses added to the original-DIMACS proof.
    pub extension_clauses_added: u64,
    /// Bucket ALO clauses added to the original-DIMACS proof.
    pub bucket_alo_clauses_added: u64,
    /// Bucket mutex clauses added to the original-DIMACS proof.
    pub bucket_mutex_clauses_added: u64,
    /// Bucket ALO plus bucket mutex clauses added before replaying the compact proof.
    pub planned_bucket_clauses_added: u64,
    /// Support clauses inserted before bucket mutex clauses.
    pub bucket_mutex_support_clauses_added: u64,
    /// Non-comment compact LRAT lines replayed.
    pub compact_lrat_lines_seen: u64,
    /// Compact LRAT comment lines skipped.
    pub compact_lrat_comments_skipped: u64,
    /// Compact LRAT addition lines remapped.
    pub compact_lrat_additions_remapped: u64,
    /// Compact LRAT deletion lines remapped.
    pub compact_lrat_deletions_remapped: u64,
    /// Compact LRAT deletion lines with no IDs, intentionally not emitted.
    pub compact_lrat_empty_deletions_skipped: u64,
    /// Maximum variable id observed in the compact LRAT proof.
    pub compact_lrat_max_var: usize,
    /// Maximum clause id observed in the compact LRAT proof.
    pub compact_lrat_max_id: u64,
    /// Offset used for compact derived LRAT ids.
    pub compact_lrat_derived_id_offset: u64,
    /// Maximum variable id emitted in the original-DIMACS proof.
    pub original_lrat_max_var: usize,
    /// Maximum clause id emitted in the original-DIMACS proof.
    pub original_lrat_max_id: u64,
    /// External checker verdicts accepted by this helper. Always zero.
    pub external_checker_verified: u64,
}

/// Result-silent original-DIMACS LRAT materialization artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliquePhpOriginalLratMaterialization {
    /// Materialized LRAT proof text. Empty when the helper is disabled.
    pub lrat: String,
    /// Counters for the materialization attempt.
    pub stats: DenseCliquePhpOriginalLratMaterializationStats,
    /// Hard false until a separate legal route gate emits a checked proof.
    pub route_admitted: bool,
    /// Hard false: this artifact never authorizes solver results.
    pub result_authority: bool,
    /// Hard false: UNSAT stdout is outside this artifact.
    pub unsat_output_authority: bool,
    /// Hard false: proof output is outside this artifact.
    pub proof_output_authority: bool,
    /// Hard false: model output is outside this artifact.
    pub model_output_authority: bool,
    /// Hard false: no external checker verdict is accepted here.
    pub external_checker_verified: bool,
}

impl DenseCliquePhpReplayPacket {
    /// True only while every authority bit remains absent.
    #[must_use]
    pub const fn authority_is_absent(&self) -> bool {
        !self.route_admitted
            && !self.result_authority
            && !self.unsat_output_authority
            && !self.proof_output_authority
            && !self.model_output_authority
    }
}

impl DenseCliquePhpCheckerAudit {
    /// True only while every authority bit remains absent.
    #[must_use]
    pub const fn authority_is_absent(&self) -> bool {
        !self.route_admitted
            && !self.result_authority
            && !self.unsat_output_authority
            && !self.proof_output_authority
            && !self.model_output_authority
            && !self.external_checker_verified
    }
}

impl DenseCliquePhpOriginalDratMaterialization {
    /// True only while every authority bit remains absent.
    #[must_use]
    pub const fn authority_is_absent(&self) -> bool {
        !self.route_admitted
            && !self.result_authority
            && !self.unsat_output_authority
            && !self.proof_output_authority
            && !self.model_output_authority
            && !self.external_checker_verified
    }
}

impl DenseCliquePhpOriginalLratMaterialization {
    /// True only while every authority bit remains absent.
    #[must_use]
    pub const fn authority_is_absent(&self) -> bool {
        !self.route_admitted
            && !self.result_authority
            && !self.unsat_output_authority
            && !self.proof_output_authority
            && !self.model_output_authority
            && !self.external_checker_verified
    }
}

impl DenseCliquePhpReplayLedger {
    /// Number of planned extension-definition clauses.
    #[must_use]
    pub fn extension_clause_count(&self) -> usize {
        self.extension_rows.len() * 3
    }
}

/// Build one-based source rows from parsed DIMACS clauses.
///
/// This is source-ingress plumbing only. It preserves row order and raw DIMACS
/// literals for later witness/replay checks, but it does not scout, route, or
/// emit SAT/UNSAT authority.
#[must_use]
pub fn dense_clique_source_clauses_from_clauses(
    clauses: &[Vec<Literal>],
) -> DenseCliqueSourceClauseRows {
    let mut source_clauses = Vec::with_capacity(clauses.len());
    let mut raw_dimacs_literals = 0usize;
    let mut empty_clause_rows = 0usize;

    for (idx, literals) in clauses.iter().enumerate() {
        if literals.is_empty() {
            empty_clause_rows += 1;
        }
        raw_dimacs_literals += literals.len();
        source_clauses.push(DenseCliqueSourceClause {
            source_id: idx + 1,
            raw_dimacs: literals.iter().map(|lit| lit.to_dimacs()).collect(),
            literals: literals.clone(),
        });
    }

    DenseCliqueSourceClauseRows {
        audit: DenseCliqueSourceClauseAudit {
            clauses_seen: clauses.len(),
            source_rows: source_clauses.len(),
            raw_dimacs_literals,
            empty_clause_rows,
            first_source_id: (!source_clauses.is_empty()).then_some(1),
            last_source_id: source_clauses.last().map(|source| source.source_id),
        },
        clauses: source_clauses,
    }
}

/// Build a result-silent PHP replay packet from parsed original DIMACS clauses.
///
/// This is the deterministic ingress for future dense-clique route admission.
/// It recovers source rows, witness data, and replay-ledger obligations, but it
/// never emits a proof or grants result authority.
pub fn build_dense_clique_php_replay_packet_from_clauses(
    num_vars: usize,
    clauses: &[Vec<Literal>],
) -> Result<DenseCliquePhpReplayPacket, DenseCliquePhpReplayPacketReject> {
    let source = dense_clique_source_clauses_from_clauses(clauses);
    let witness = DenseCliqueScout::scan_with_witness(num_vars, &source.clauses)
        .map_err(DenseCliquePhpReplayPacketReject::Witness)?;
    let replay_ledger = build_dense_clique_php_replay_ledger(&witness)
        .map_err(DenseCliquePhpReplayPacketReject::Replay)?;

    Ok(DenseCliquePhpReplayPacket {
        source_audit: source.audit,
        witness,
        replay_ledger,
        route_admitted: false,
        result_authority: false,
        unsat_output_authority: false,
        proof_output_authority: false,
        model_output_authority: false,
    })
}

/// Materialize planned checker-visible dense-clique PHP rows from a replay packet.
///
/// This is a pure/default-off audit. It emits no proof, accepts no checker
/// verdict, grants no route/result authority, and rejects bucket shapes that do
/// not match the pair-bucket extension schedule used by the clique route.
pub fn materialize_dense_clique_php_checker_audit(
    config: DenseCliquePhpCheckerAuditConfig,
    packet: &DenseCliquePhpReplayPacket,
) -> Result<DenseCliquePhpCheckerAudit, DenseCliquePhpCheckerAuditReject> {
    let mut stats = DenseCliquePhpCheckerAuditStats {
        enabled: config.enabled,
        source_rows_audited: packet.source_audit.source_rows as u64,
        extension_rows_seen: packet.replay_ledger.extension_rows.len() as u64,
        bucket_alo_rows_seen: packet.replay_ledger.bucket_alo_rows.len() as u64,
        bucket_mutex_rows_seen: packet.replay_ledger.bucket_mutex_rows.len() as u64,
        ..DenseCliquePhpCheckerAuditStats::default()
    };

    if !config.enabled {
        return Ok(DenseCliquePhpCheckerAudit {
            rows: Vec::new(),
            stats,
            route_admitted: false,
            result_authority: false,
            unsat_output_authority: false,
            proof_output_authority: false,
            model_output_authority: false,
            external_checker_verified: false,
        });
    }
    if !packet.authority_is_absent() {
        return Err(DenseCliquePhpCheckerAuditReject::PacketAuthorityPresent);
    }
    validate_checker_audit_packet(packet)?;

    for (bucket, vertices) in packet.replay_ledger.bucket_vertices.iter().enumerate() {
        if vertices.len() != 2 {
            return Err(DenseCliquePhpCheckerAuditReject::UnsupportedBucketArity {
                bucket,
                arity: vertices.len(),
            });
        }
    }

    let source_rows_by_id = checker_audit_source_rows_by_id(&packet.witness);
    let mut rows = Vec::with_capacity(
        packet.replay_ledger.extension_clause_count()
            + packet.replay_ledger.bucket_alo_rows.len()
            + packet.replay_ledger.bucket_mutex_rows.len(),
    );

    push_extension_checker_rows(packet, &mut rows)?;
    push_bucket_alo_checker_rows(packet, &source_rows_by_id, &mut rows)?;
    push_bucket_mutex_checker_rows(packet, &source_rows_by_id, &mut rows)?;

    stats.checker_rows_materialized = rows.len() as u64;
    stats.extension_definition_rows_materialized =
        packet.replay_ledger.extension_clause_count() as u64;
    stats.bucket_alo_rows_materialized = packet.replay_ledger.bucket_alo_rows.len() as u64;
    stats.bucket_mutex_rows_materialized = packet.replay_ledger.bucket_mutex_rows.len() as u64;
    stats.source_dependency_edges = rows.iter().map(|row| row.source_rows.len() as u64).sum();
    stats.dependency_clause_edges = rows
        .iter()
        .map(|row| row.dependency_clause_ids.len() as u64)
        .sum();
    stats.external_checker_verified_rows = rows
        .iter()
        .filter(|row| row.external_checker_verified)
        .count() as u64;

    Ok(DenseCliquePhpCheckerAudit {
        rows,
        stats,
        route_admitted: false,
        result_authority: false,
        unsat_output_authority: false,
        proof_output_authority: false,
        model_output_authority: false,
        external_checker_verified: false,
    })
}

/// Materialize an original-DIMACS DRAT proof from a compact PHP DRAT proof.
///
/// This is a default-off proof primitive, not a route gate. It replays the
/// already-audited pair-bucket PHP extension schedule in the original DIMACS
/// namespace, remaps compact PHP proof variables after the original variables,
/// accepts no checker verdict, and grants no result/proof authority.
pub fn materialize_dense_clique_php_original_drat_from_compact_proof(
    config: DenseCliquePhpOriginalDratMaterializerConfig,
    packet: &DenseCliquePhpReplayPacket,
    compact_drat: &str,
) -> Result<
    DenseCliquePhpOriginalDratMaterialization,
    DenseCliquePhpOriginalDratMaterializationReject,
> {
    let ledger = &packet.replay_ledger;
    let mut stats = DenseCliquePhpOriginalDratMaterializationStats {
        enabled: config.enabled,
        source_rows_audited: packet.source_audit.source_rows as u64,
        compact_variables: ledger.extension_rows.len() as u64,
        compact_clauses: (ledger.bucket_alo_rows.len() + ledger.bucket_mutex_rows.len()) as u64,
        ..DenseCliquePhpOriginalDratMaterializationStats::default()
    };

    if !config.enabled {
        return Ok(DenseCliquePhpOriginalDratMaterialization {
            drat: String::new(),
            stats,
            route_admitted: false,
            result_authority: false,
            unsat_output_authority: false,
            proof_output_authority: false,
            model_output_authority: false,
            external_checker_verified: false,
        });
    }

    let audit = materialize_dense_clique_php_checker_audit(
        DenseCliquePhpCheckerAuditConfig { enabled: true },
        packet,
    )?;
    debug_assert!(audit.authority_is_absent());

    let mut drat = String::new();
    push_original_drat_extension_clauses(ledger, &mut drat, &mut stats)?;
    push_original_drat_bucket_alo_clauses(ledger, &mut drat, &mut stats)?;
    push_original_drat_bucket_mutex_clauses(ledger, &mut drat, &mut stats)?;
    push_remapped_compact_drat(ledger, compact_drat, &mut drat, &mut stats)?;

    Ok(DenseCliquePhpOriginalDratMaterialization {
        drat,
        stats,
        route_admitted: false,
        result_authority: false,
        unsat_output_authority: false,
        proof_output_authority: false,
        model_output_authority: false,
        external_checker_verified: false,
    })
}

/// Materialize an original-DIMACS LRAT proof from a compact PHP LRAT proof.
///
/// This is a default-off proof primitive, not a route gate. It materializes the
/// pair-bucket replay ledger as checker-visible LRAT rows, remaps compact PHP
/// proof variables and clause IDs into the original DIMACS namespace, accepts no
/// checker verdict, and grants no result/proof authority.
pub fn materialize_dense_clique_php_original_lrat_from_compact_proof(
    config: DenseCliquePhpOriginalLratMaterializerConfig,
    packet: &DenseCliquePhpReplayPacket,
    compact_lrat: &str,
) -> Result<
    DenseCliquePhpOriginalLratMaterialization,
    DenseCliquePhpOriginalLratMaterializationReject,
> {
    let ledger = &packet.replay_ledger;
    let compact_clauses = ledger.bucket_alo_rows.len() + ledger.bucket_mutex_rows.len();
    let mut stats = DenseCliquePhpOriginalLratMaterializationStats {
        enabled: config.enabled,
        source_rows_audited: packet.source_audit.source_rows as u64,
        compact_variables: ledger.extension_rows.len() as u64,
        compact_clauses: compact_clauses as u64,
        ..DenseCliquePhpOriginalLratMaterializationStats::default()
    };

    if !config.enabled {
        return Ok(DenseCliquePhpOriginalLratMaterialization {
            lrat: String::new(),
            stats,
            route_admitted: false,
            result_authority: false,
            unsat_output_authority: false,
            proof_output_authority: false,
            model_output_authority: false,
            external_checker_verified: false,
        });
    }

    let audit = materialize_dense_clique_php_checker_audit(
        DenseCliquePhpCheckerAuditConfig { enabled: true },
        packet,
    )?;
    debug_assert!(audit.authority_is_absent());

    let source_mutex_ids = original_lrat_source_mutex_ids(packet);
    let mut schedule = OriginalLratReplaySchedule::new(ledger);
    let mut lrat = String::new();
    push_original_lrat_extension_clauses(ledger, &mut schedule, &mut lrat, &mut stats)?;
    push_original_lrat_bucket_alo_clauses(ledger, &mut schedule, &mut lrat, &mut stats)?;
    push_original_lrat_bucket_mutex_clauses(
        ledger,
        &source_mutex_ids,
        &mut schedule,
        &mut lrat,
        &mut stats,
    )?;
    stats.compact_lrat_derived_id_offset = schedule.compact_derived_id_offset();
    push_remapped_compact_lrat(ledger, &schedule, compact_lrat, &mut lrat, &mut stats)?;

    Ok(DenseCliquePhpOriginalLratMaterialization {
        lrat,
        stats,
        route_admitted: false,
        result_authority: false,
        unsat_output_authority: false,
        proof_output_authority: false,
        model_output_authority: false,
        external_checker_verified: false,
    })
}

/// Planned extension row for one pigeon/hole bucket pair.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliquePhpExtensionReplayRow {
    /// Pigeon/color index.
    pub pigeon: usize,
    /// Hole/bucket index.
    pub bucket: usize,
    /// Planned extension variable, one-based.
    pub extension_var_one_based: usize,
    /// Original variables folded into this bucket extension, one-based.
    pub original_vars_one_based: Vec<usize>,
    /// Planned extension-definition clause IDs.
    pub extension_clause_ids: [usize; 3],
}

/// Derived bucket ALO row for one pigeon.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliquePhpBucketAloReplayRow {
    /// Pigeon/color index.
    pub pigeon: usize,
    /// Original support clause proving the source ALO row.
    pub source_support_id: usize,
    /// Derived bucket ALO clause ID.
    pub derived_clause_id: usize,
    /// Extension variables participating in the derived bucket ALO.
    pub extension_vars_one_based: Vec<usize>,
}

/// Derived bucket mutex row for one hole and pigeon pair.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliquePhpBucketMutexReplayRow {
    /// Hole/bucket index.
    pub bucket: usize,
    /// Left pigeon/color index.
    pub lhs_pigeon: usize,
    /// Right pigeon/color index.
    pub rhs_pigeon: usize,
    /// Derived bucket mutex clause ID.
    pub derived_clause_id: usize,
    /// Left bucket extension variable, one-based.
    pub lhs_extension_var_one_based: usize,
    /// Right bucket extension variable, one-based.
    pub rhs_extension_var_one_based: usize,
    /// Original mutex source rows proving all vertex-pair exclusions for this bucket.
    pub source_mutex_ids: Vec<usize>,
}

/// Witness-preserving dense clique recovery result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseCliqueWitness {
    /// Aggregate scout result for compatibility with existing callers.
    pub scout: DenseCliqueScout,
    /// Positive support rows with original source row IDs.
    pub support_rows: Vec<DenseCliqueSupportRowWitness>,
    /// Negative binary mutexes with original source row IDs.
    pub mutexes: Vec<DenseCliqueMutexWitness>,
    /// Recovered graph edge/non-edge witnesses.
    pub graph_pairs: Vec<DenseCliqueGraphPairWitness>,
    /// Recovered PHP obligation witness.
    pub php_obligation: DenseCliquePhpObligation,
}

/// Fail-closed rejection reason for witness-preserving scan input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DenseCliqueWitnessReject {
    /// Source clause IDs are duplicated.
    DuplicateSourceId {
        /// Duplicated one-based source clause identifier.
        source_id: usize,
    },
    /// Source clause IDs are not exactly contiguous and one-based.
    NonContiguousSourceId {
        /// Expected one-based source clause identifier.
        expected: usize,
        /// Actual source clause identifier encountered at that position.
        actual: usize,
    },
    /// Raw DIMACS literals do not round-trip from parsed literals.
    RawDimacsMismatch {
        /// One-based source clause identifier for the mismatched row.
        source_id: usize,
        /// DIMACS literals reconstructed from parsed literals.
        expected: Vec<i32>,
        /// Raw DIMACS literals supplied by the caller.
        actual: Vec<i32>,
    },
    /// The aggregate strict scout rejected the structure.
    Scout(DenseCliqueRejection),
    /// The accepted aggregate scout did not return a structure.
    MissingStructure,
    /// A mutex pair appeared more than once in the source rows.
    DuplicateMutexPair {
        /// Lower zero-based variable index in the duplicated mutex pair.
        lhs_variable: usize,
        /// Higher zero-based variable index in the duplicated mutex pair.
        rhs_variable: usize,
        /// First source clause identifier for the mutex pair.
        first_source_id: usize,
        /// Second source clause identifier for the mutex pair.
        second_source_id: usize,
    },
}

/// Fail-closed replay-ledger materialization rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DenseCliquePhpReplayLedgerReject {
    /// The accepted scout did not return a structure.
    MissingStructure,
    /// The witness does not describe an UNSAT PHP obligation.
    NotPhpUnsatObligation,
    /// Support rows do not match the recovered pigeon count.
    SupportRowCountMismatch {
        /// Expected support row count.
        expected: usize,
        /// Actual support row count.
        actual: usize,
    },
    /// Bucket count does not match the recovered hole count.
    BucketCountMismatch {
        /// Expected bucket count.
        expected: usize,
        /// Actual bucket count.
        actual: usize,
    },
    /// A bucket references a vertex outside the recovered support width.
    BucketVertexOutOfRange {
        /// Bucket index.
        bucket: usize,
        /// Vertex index from the bucket.
        vertex: usize,
        /// Support row width.
        width: usize,
    },
    /// A source mutex needed for a derived bucket mutex row is missing.
    MissingMutexSource {
        /// Bucket index.
        bucket: usize,
        /// Left pigeon/color index.
        lhs_pigeon: usize,
        /// Right pigeon/color index.
        rhs_pigeon: usize,
        /// Left graph vertex index.
        lhs_vertex: usize,
        /// Right graph vertex index.
        rhs_vertex: usize,
        /// Left original variable, zero-based.
        lhs_variable: usize,
        /// Right original variable, zero-based.
        rhs_variable: usize,
    },
}

/// Fail-closed replay-packet construction rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DenseCliquePhpReplayPacketReject {
    /// Dense-clique witness recovery rejected the parsed clause surface.
    Witness(DenseCliqueWitnessReject),
    /// PHP replay ledger construction rejected the recovered witness.
    Replay(DenseCliquePhpReplayLedgerReject),
}

/// Fail-closed checker-row audit materialization rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DenseCliquePhpCheckerAuditReject {
    /// The replay packet already carries authority this audit is not allowed to accept.
    PacketAuthorityPresent,
    /// Packet witness/audit/ledger counters disagree.
    PacketLedgerMismatch {
        /// Counter or field that mismatched.
        field: &'static str,
        /// Expected value from the authoritative side of the packet.
        expected: usize,
        /// Actual value observed in the dependent side of the packet.
        actual: usize,
    },
    /// The three-clause extension materializer only supports pair buckets.
    UnsupportedBucketArity {
        /// Bucket index.
        bucket: usize,
        /// Number of vertices in the bucket.
        arity: usize,
    },
    /// A planned row did not match the deterministic checker-visible schedule.
    PlannedRowMismatch {
        /// Planned row kind.
        row_kind: DenseCliquePhpCheckerVisibleRowKind,
        /// Row index within that row kind.
        row_index: usize,
        /// Field that mismatched.
        field: &'static str,
        /// Expected deterministic value.
        expected: usize,
        /// Actual value in the replay ledger.
        actual: usize,
    },
    /// A referenced source row was absent from the packet witness.
    MissingSourceRow {
        /// Missing one-based source clause id.
        source_id: usize,
    },
    /// A bucket mutex row did not retain all source mutex rows for a pair bucket.
    SourceMutexCountMismatch {
        /// Bucket mutex row index.
        row_index: usize,
        /// Expected source mutex source-row count.
        expected: usize,
        /// Actual source mutex source-row count.
        actual: usize,
    },
    /// A planned variable cannot be represented as a DIMACS i32 literal.
    DimacsLiteralOverflow {
        /// One-based variable id.
        variable_one_based: usize,
    },
}

/// Fail-closed original-DIMACS DRAT materialization rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DenseCliquePhpOriginalDratMaterializationReject {
    /// The checker-visible replay audit rejected the packet.
    CheckerAudit(DenseCliquePhpCheckerAuditReject),
    /// A planned extension row did not match the pair-bucket DRAT schedule.
    ExtensionOriginalVarCountMismatch {
        /// Extension row index.
        row_index: usize,
        /// Expected original variables in the bucket.
        expected: usize,
        /// Actual original variables in the replay row.
        actual: usize,
    },
    /// A compact proof line was missing the terminating zero.
    CompactProofMissingTerminator {
        /// One-based proof line number.
        line_number: usize,
    },
    /// A compact proof line contained a deletion marker without a clause body.
    CompactProofMalformedDeletion {
        /// One-based proof line number.
        line_number: usize,
    },
    /// A compact proof literal token was not an integer.
    CompactProofLiteralParse {
        /// One-based proof line number.
        line_number: usize,
        /// Token that failed to parse.
        token: String,
    },
    /// A compact proof line contained zero before its terminator.
    CompactProofZeroBeforeTerminator {
        /// One-based proof line number.
        line_number: usize,
    },
    /// A compact proof literal cannot be represented as a positive variable id.
    CompactProofVariableOverflow {
        /// One-based proof line number.
        line_number: usize,
        /// Literal text that overflowed.
        token: String,
    },
    /// Remapping a compact proof variable overflowed the original namespace.
    OriginalVariableOverflow {
        /// One-based proof line number, or zero for planned rows.
        line_number: usize,
        /// Compact variable id being remapped.
        compact_variable: usize,
    },
    /// A remapped proof variable cannot be represented as a DIMACS i32 literal.
    DimacsLiteralOverflow {
        /// One-based proof line number, or zero for planned rows.
        line_number: usize,
        /// One-based variable id.
        variable_one_based: usize,
    },
}

impl From<DenseCliquePhpCheckerAuditReject> for DenseCliquePhpOriginalDratMaterializationReject {
    fn from(reject: DenseCliquePhpCheckerAuditReject) -> Self {
        Self::CheckerAudit(reject)
    }
}

/// Fail-closed original-DIMACS LRAT materialization rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DenseCliquePhpOriginalLratMaterializationReject {
    /// The checker-visible replay audit rejected the packet.
    CheckerAudit(DenseCliquePhpCheckerAuditReject),
    /// A planned extension row did not match the pair-bucket LRAT schedule.
    ExtensionOriginalVarCountMismatch {
        /// Extension row index.
        row_index: usize,
        /// Expected original variables in the bucket.
        expected: usize,
        /// Actual original variables in the replay row.
        actual: usize,
    },
    /// A required original mutex source row was absent.
    MissingSourceMutex {
        /// Bucket index.
        bucket: usize,
        /// Left pigeon/color index.
        lhs_pigeon: usize,
        /// Right pigeon/color index.
        rhs_pigeon: usize,
        /// Left original variable, one-based.
        lhs_original_var: usize,
        /// Right original variable, one-based.
        rhs_original_var: usize,
    },
    /// A compact LRAT line did not contain an id token.
    CompactLratMissingId {
        /// One-based proof line number.
        line_number: usize,
    },
    /// A compact LRAT id token was not an integer.
    CompactLratIdParse {
        /// One-based proof line number.
        line_number: usize,
        /// Token that failed to parse.
        token: String,
    },
    /// A compact LRAT id token was zero.
    CompactLratIdZero {
        /// One-based proof line number.
        line_number: usize,
    },
    /// A compact LRAT addition tried to redefine an original compact clause id.
    CompactLratOriginalAddId {
        /// One-based proof line number.
        line_number: usize,
        /// Compact clause id.
        compact_id: u64,
    },
    /// A compact LRAT addition was missing a clause terminator.
    CompactLratMissingClauseTerminator {
        /// One-based proof line number.
        line_number: usize,
    },
    /// A compact LRAT addition was missing a hint terminator.
    CompactLratMissingHintTerminator {
        /// One-based proof line number.
        line_number: usize,
    },
    /// A compact LRAT deletion was missing its terminating zero.
    CompactLratMissingDeletionTerminator {
        /// One-based proof line number.
        line_number: usize,
    },
    /// A compact LRAT line contained tokens after the terminating zero.
    CompactLratTrailingTokens {
        /// One-based proof line number.
        line_number: usize,
    },
    /// A compact LRAT literal token was not an integer.
    CompactLratLiteralParse {
        /// One-based proof line number.
        line_number: usize,
        /// Token that failed to parse.
        token: String,
    },
    /// A compact LRAT literal token overflowed a positive variable id.
    CompactLratVariableOverflow {
        /// One-based proof line number.
        line_number: usize,
        /// Token that overflowed.
        token: String,
    },
    /// A compact LRAT hint/delete id token was not an integer.
    CompactLratHintParse {
        /// One-based proof line number.
        line_number: usize,
        /// Token that failed to parse.
        token: String,
    },
    /// A compact LRAT hint/delete id token was zero.
    CompactLratHintZero {
        /// One-based proof line number.
        line_number: usize,
    },
    /// Remapping a compact LRAT variable overflowed the original namespace.
    OriginalVariableOverflow {
        /// One-based proof line number, or zero for planned rows.
        line_number: usize,
        /// Compact variable id being remapped.
        compact_variable: usize,
    },
    /// Remapping a compact LRAT id overflowed the original proof namespace.
    OriginalClauseIdOverflow {
        /// One-based proof line number, or zero for planned rows.
        line_number: usize,
        /// Compact clause id being remapped.
        compact_id: u64,
    },
    /// A remapped proof variable cannot be represented as a DIMACS i32 literal.
    DimacsLiteralOverflow {
        /// One-based proof line number, or zero for planned rows.
        line_number: usize,
        /// One-based variable id.
        variable_one_based: usize,
    },
}

impl From<DenseCliquePhpCheckerAuditReject> for DenseCliquePhpOriginalLratMaterializationReject {
    fn from(reject: DenseCliquePhpCheckerAuditReject) -> Self {
        Self::CheckerAudit(reject)
    }
}

/// Rejection reason for a strict dense clique scout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DenseCliqueRejection {
    /// The strict scout accepted the structure.
    None,
    /// The input is intentionally too large for the exact scout.
    TooManyVariables,
    /// No positive support clauses with width at least two were present.
    NoPositiveSupportClauses,
    /// Positive support clauses did not all have the same width.
    NonUniformSupportWidth,
    /// Positive support clauses overlap in at least one variable.
    OverlappingSupportRows,
    /// Positive support clauses did not cover every declared variable.
    SupportDoesNotCoverAllVariables,
    /// Some clause is neither a positive support row nor a negative binary mutex.
    NonSupportOrMutexClauses,
    /// The negative binary mutex graph is incomplete or has unsupported extras.
    IncompleteMutexGraph,
    /// Cross-row mutexes do not define a deterministic graph edge relation.
    InconsistentGraphMutexes,
    /// The shape has only one support row, so it is not a clique/coloring route.
    SingleSupportRow,
}

impl DenseCliqueRejection {
    /// Stable numeric code for stats counters.
    #[must_use]
    pub const fn code(self) -> u64 {
        match self {
            Self::None => 0,
            Self::TooManyVariables => 1,
            Self::NoPositiveSupportClauses => 2,
            Self::NonUniformSupportWidth => 3,
            Self::OverlappingSupportRows => 4,
            Self::SupportDoesNotCoverAllVariables => 5,
            Self::NonSupportOrMutexClauses => 6,
            Self::IncompleteMutexGraph => 7,
            Self::SingleSupportRow => 8,
            Self::InconsistentGraphMutexes => 9,
        }
    }

    /// Stable short label for diagnostic messages and reports.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::TooManyVariables => "too-many-variables",
            Self::NoPositiveSupportClauses => "no-positive-support-clauses",
            Self::NonUniformSupportWidth => "non-uniform-support-width",
            Self::OverlappingSupportRows => "overlapping-support-rows",
            Self::SupportDoesNotCoverAllVariables => "support-does-not-cover-all-variables",
            Self::NonSupportOrMutexClauses => "non-support-or-mutex-clauses",
            Self::IncompleteMutexGraph => "incomplete-mutex-graph",
            Self::SingleSupportRow => "single-support-row",
            Self::InconsistentGraphMutexes => "inconsistent-graph-mutexes",
        }
    }
}

impl DenseCliqueScout {
    /// Scan a CNF for the strict dense clique/coloring mutex surface.
    #[must_use]
    pub fn scan(num_vars: usize, clauses: &[Vec<Literal>]) -> Self {
        if num_vars > MAX_SCOUT_VARS {
            return Self::rejected(
                num_vars,
                clauses.len(),
                0,
                0,
                clauses.len(),
                DenseCliqueRejection::TooManyVariables,
            );
        }

        let mut support_rows: Vec<Vec<usize>> = Vec::new();
        let mut mutex_pairs: BTreeSet<(usize, usize)> = BTreeSet::new();
        let mut other_clauses = 0usize;

        for clause in clauses {
            if is_positive_support_clause(clause) {
                let mut row: Vec<_> = clause.iter().map(|lit| lit.variable().index()).collect();
                row.sort_unstable();
                support_rows.push(row);
            } else if let Some(pair) = negative_binary_mutex_pair(clause) {
                mutex_pairs.insert(pair);
            } else {
                other_clauses += 1;
            }
        }

        let positive_support_clauses = support_rows.len();
        let negative_binary_mutexes = mutex_pairs.len();

        if support_rows.is_empty() {
            return Self::rejected(
                num_vars,
                clauses.len(),
                positive_support_clauses,
                negative_binary_mutexes,
                other_clauses,
                DenseCliqueRejection::NoPositiveSupportClauses,
            );
        }
        if support_rows.len() == 1 {
            return Self::rejected(
                num_vars,
                clauses.len(),
                positive_support_clauses,
                negative_binary_mutexes,
                other_clauses,
                DenseCliqueRejection::SingleSupportRow,
            );
        }

        let support_width = support_rows[0].len();
        if support_rows.iter().any(|row| row.len() != support_width) {
            return Self::rejected(
                num_vars,
                clauses.len(),
                positive_support_clauses,
                negative_binary_mutexes,
                other_clauses,
                DenseCliqueRejection::NonUniformSupportWidth,
            );
        }

        let mut support_vars = vec![false; num_vars];
        let mut covered_vars = 0usize;
        for row in &support_rows {
            for &var in row {
                if var >= num_vars || support_vars[var] {
                    return Self::rejected(
                        num_vars,
                        clauses.len(),
                        positive_support_clauses,
                        negative_binary_mutexes,
                        other_clauses,
                        DenseCliqueRejection::OverlappingSupportRows,
                    );
                }
                support_vars[var] = true;
                covered_vars += 1;
            }
        }

        if covered_vars != num_vars {
            return Self::rejected(
                num_vars,
                clauses.len(),
                positive_support_clauses,
                negative_binary_mutexes,
                other_clauses,
                DenseCliqueRejection::SupportDoesNotCoverAllVariables,
            );
        }

        if other_clauses != 0 || positive_support_clauses + negative_binary_mutexes != clauses.len()
        {
            return Self::rejected(
                num_vars,
                clauses.len(),
                positive_support_clauses,
                negative_binary_mutexes,
                other_clauses,
                DenseCliqueRejection::NonSupportOrMutexClauses,
            );
        }

        let recovered = match recover_graph_mutexes(&support_rows, &mutex_pairs) {
            Ok(recovered) => recovered,
            Err(rejection) => {
                return Self::rejected(
                    num_vars,
                    clauses.len(),
                    positive_support_clauses,
                    negative_binary_mutexes,
                    other_clauses,
                    rejection,
                );
            }
        };
        let graph_edges = recovered.graph_edges;
        let expected_mutexes = recovered.expected_mutexes;
        if negative_binary_mutexes != expected_mutexes {
            return Self::rejected(
                num_vars,
                clauses.len(),
                positive_support_clauses,
                negative_binary_mutexes,
                other_clauses,
                DenseCliqueRejection::IncompleteMutexGraph,
            );
        }

        Self {
            num_vars,
            num_clauses: clauses.len(),
            positive_support_clauses,
            negative_binary_mutexes,
            other_clauses,
            structure: Some(DenseCliqueStructure {
                graph_vertices: support_width,
                colors: support_rows.len(),
                variables: num_vars,
                mutexes: negative_binary_mutexes,
                expected_mutexes,
                graph_edges,
                graph_non_edges: recovered.graph_non_edges,
                graph_non_edge_buckets: recovered.graph_non_edge_buckets,
                graph_non_edge_bucket_min: recovered.graph_non_edge_bucket_min,
                graph_non_edge_bucket_max: recovered.graph_non_edge_bucket_max,
                complete_multipartite: recovered.complete_multipartite,
                php_pigeons: support_rows.len(),
                php_holes: recovered.graph_non_edge_buckets,
                php_unsat_obligation: recovered.complete_multipartite
                    && support_rows.len() > recovered.graph_non_edge_buckets,
                positive_support_clauses,
                support_width,
            }),
            rejection: DenseCliqueRejection::None,
        }
    }

    /// Scan source clauses while preserving source IDs and raw rows for replay.
    pub fn scan_with_witness(
        num_vars: usize,
        source_clauses: &[DenseCliqueSourceClause],
    ) -> Result<DenseCliqueWitness, DenseCliqueWitnessReject> {
        validate_source_clause_ids(source_clauses)?;
        validate_raw_dimacs_rows(source_clauses)?;

        let clauses: Vec<Vec<Literal>> = source_clauses
            .iter()
            .map(|source_clause| source_clause.literals.clone())
            .collect();
        let scout = Self::scan(num_vars, &clauses);
        if !scout.detected() {
            return Err(DenseCliqueWitnessReject::Scout(scout.rejection));
        }
        let structure = scout
            .structure
            .as_ref()
            .ok_or(DenseCliqueWitnessReject::MissingStructure)?;

        let mut support_rows = Vec::new();
        let mut mutex_map = BTreeMap::new();
        let mut mutexes = Vec::new();
        for source_clause in source_clauses {
            if is_positive_support_clause(&source_clause.literals) {
                let mut variables: Vec<_> = source_clause
                    .literals
                    .iter()
                    .map(|lit| lit.variable().index())
                    .collect();
                variables.sort_unstable();
                support_rows.push(DenseCliqueSupportRowWitness {
                    source_id: source_clause.source_id,
                    raw_dimacs: source_clause.raw_dimacs.clone(),
                    variables,
                });
            } else if let Some((lhs_variable, rhs_variable)) =
                negative_binary_mutex_pair(&source_clause.literals)
            {
                let mutex = DenseCliqueMutexWitness {
                    source_id: source_clause.source_id,
                    raw_dimacs: source_clause.raw_dimacs.clone(),
                    lhs_variable,
                    rhs_variable,
                };
                if let Some(first) = mutex_map.insert((lhs_variable, rhs_variable), mutex.source_id)
                {
                    return Err(DenseCliqueWitnessReject::DuplicateMutexPair {
                        lhs_variable,
                        rhs_variable,
                        first_source_id: first,
                        second_source_id: mutex.source_id,
                    });
                }
                mutexes.push(mutex);
            }
        }

        let graph_pairs = recover_graph_pair_witnesses(&support_rows, &mutex_map);
        let graph_non_edges: Vec<_> = graph_pairs
            .iter()
            .filter(|pair| !pair.graph_edge)
            .map(|pair| (pair.lhs_vertex, pair.rhs_vertex))
            .collect();
        let bucket_vertices =
            recover_graph_non_edge_bucket_vertices(structure.graph_vertices, &graph_non_edges);
        let php_obligation = DenseCliquePhpObligation {
            pigeons: structure.php_pigeons,
            holes: structure.php_holes,
            bucket_vertices,
            unsat_obligation: structure.php_unsat_obligation,
        };

        Ok(DenseCliqueWitness {
            scout,
            support_rows,
            mutexes,
            graph_pairs,
            php_obligation,
        })
    }

    /// Return whether the scout recovered the exact strict structure.
    #[must_use]
    pub const fn detected(&self) -> bool {
        self.structure.is_some()
    }

    /// Return recovered graph vertex count, or zero when not detected.
    #[must_use]
    pub fn graph_vertices(&self) -> usize {
        self.structure
            .as_ref()
            .map_or(0, |structure| structure.graph_vertices)
    }

    /// Return recovered color/slot count, or zero when not detected.
    #[must_use]
    pub fn colors(&self) -> usize {
        self.structure
            .as_ref()
            .map_or(0, |structure| structure.colors)
    }

    /// Return recovered graph edge count, or zero when not detected.
    #[must_use]
    pub fn graph_edges(&self) -> usize {
        self.structure
            .as_ref()
            .map_or(0, |structure| structure.graph_edges)
    }

    /// Return recovered graph non-edge count, or zero when not detected.
    #[must_use]
    pub fn graph_non_edges(&self) -> usize {
        self.structure
            .as_ref()
            .map_or(0, |structure| structure.graph_non_edges)
    }

    /// Return graph-complement bucket count, or zero when not detected.
    #[must_use]
    pub fn graph_non_edge_buckets(&self) -> usize {
        self.structure
            .as_ref()
            .map_or(0, |structure| structure.graph_non_edge_buckets)
    }

    /// Return minimum graph-complement bucket size, or zero when not detected.
    #[must_use]
    pub fn graph_non_edge_bucket_min(&self) -> usize {
        self.structure
            .as_ref()
            .map_or(0, |structure| structure.graph_non_edge_bucket_min)
    }

    /// Return maximum graph-complement bucket size, or zero when not detected.
    #[must_use]
    pub fn graph_non_edge_bucket_max(&self) -> usize {
        self.structure
            .as_ref()
            .map_or(0, |structure| structure.graph_non_edge_bucket_max)
    }

    /// Return whether the recovered graph is complete multipartite.
    #[must_use]
    pub fn complete_multipartite(&self) -> bool {
        self.structure
            .as_ref()
            .is_some_and(|structure| structure.complete_multipartite)
    }

    /// Return recovered PHP hole count, or zero when not detected.
    #[must_use]
    pub fn php_holes(&self) -> usize {
        self.structure
            .as_ref()
            .map_or(0, |structure| structure.php_holes)
    }

    /// Return recovered PHP pigeon count, or zero when not detected.
    #[must_use]
    pub fn php_pigeons(&self) -> usize {
        self.structure
            .as_ref()
            .map_or(0, |structure| structure.php_pigeons)
    }

    /// Return whether the recovered PHP bucket obligation is UNSAT.
    #[must_use]
    pub fn pigeonhole_unsat_obligation(&self) -> bool {
        self.structure
            .as_ref()
            .is_some_and(|structure| structure.php_unsat_obligation)
    }

    /// Return expected complete mutex count, or zero when not detected.
    #[must_use]
    pub fn expected_mutexes(&self) -> usize {
        self.structure
            .as_ref()
            .map_or(0, |structure| structure.expected_mutexes)
    }

    /// Return support row width, or zero when not detected.
    #[must_use]
    pub fn support_width(&self) -> usize {
        self.structure
            .as_ref()
            .map_or(0, |structure| structure.support_width)
    }

    fn rejected(
        num_vars: usize,
        num_clauses: usize,
        positive_support_clauses: usize,
        negative_binary_mutexes: usize,
        other_clauses: usize,
        rejection: DenseCliqueRejection,
    ) -> Self {
        Self {
            num_vars,
            num_clauses,
            positive_support_clauses,
            negative_binary_mutexes,
            other_clauses,
            structure: None,
            rejection,
        }
    }
}

/// Build a deterministic source-only PHP replay ledger from a dense-clique witness.
pub fn build_dense_clique_php_replay_ledger(
    witness: &DenseCliqueWitness,
) -> Result<DenseCliquePhpReplayLedger, DenseCliquePhpReplayLedgerReject> {
    let structure = witness
        .scout
        .structure
        .as_ref()
        .ok_or(DenseCliquePhpReplayLedgerReject::MissingStructure)?;
    if !witness.php_obligation.unsat_obligation {
        return Err(DenseCliquePhpReplayLedgerReject::NotPhpUnsatObligation);
    }

    let pigeons = witness.php_obligation.pigeons;
    let holes = witness.php_obligation.holes;
    if witness.support_rows.len() != pigeons {
        return Err(DenseCliquePhpReplayLedgerReject::SupportRowCountMismatch {
            expected: pigeons,
            actual: witness.support_rows.len(),
        });
    }
    if witness.php_obligation.bucket_vertices.len() != holes {
        return Err(DenseCliquePhpReplayLedgerReject::BucketCountMismatch {
            expected: holes,
            actual: witness.php_obligation.bucket_vertices.len(),
        });
    }

    let width = structure.support_width;
    for (bucket, vertices) in witness.php_obligation.bucket_vertices.iter().enumerate() {
        for &vertex in vertices {
            if vertex >= width {
                return Err(DenseCliquePhpReplayLedgerReject::BucketVertexOutOfRange {
                    bucket,
                    vertex,
                    width,
                });
            }
        }
    }

    let extension_rows_len = pigeons * holes;
    let extension_var_start_one_based = witness.scout.num_vars + 1;
    let extension_var_end_one_based = extension_var_start_one_based + extension_rows_len - 1;
    let extension_clause_id_start = witness.scout.num_clauses + 1;
    let extension_clause_count = extension_rows_len * 3;
    let extension_clause_id_end = extension_clause_id_start + extension_clause_count - 1;
    let bucket_alo_clause_id_start = extension_clause_id_end + 1;
    let bucket_alo_clause_id_end = bucket_alo_clause_id_start + pigeons - 1;
    let bucket_mutex_rows_len = holes * pigeons.saturating_mul(pigeons.saturating_sub(1)) / 2;
    let bucket_mutex_clause_id_start = bucket_alo_clause_id_end + 1;
    let bucket_mutex_clause_id_end = bucket_mutex_clause_id_start + bucket_mutex_rows_len - 1;

    let mut extension_rows = Vec::with_capacity(extension_rows_len);
    let mut next_extension_clause_id = extension_clause_id_start;
    for pigeon in 0..pigeons {
        let support_row = &witness.support_rows[pigeon];
        for (bucket, bucket_vertices) in witness.php_obligation.bucket_vertices.iter().enumerate() {
            let extension_clause_ids = [
                next_extension_clause_id,
                next_extension_clause_id + 1,
                next_extension_clause_id + 2,
            ];
            next_extension_clause_id += 3;
            extension_rows.push(DenseCliquePhpExtensionReplayRow {
                pigeon,
                bucket,
                extension_var_one_based: dense_clique_php_extension_var_one_based(
                    witness.scout.num_vars,
                    holes,
                    pigeon,
                    bucket,
                ),
                original_vars_one_based: bucket_vertices
                    .iter()
                    .map(|&vertex| support_row.variables[vertex] + 1)
                    .collect(),
                extension_clause_ids,
            });
        }
    }

    let mut bucket_alo_rows = Vec::with_capacity(pigeons);
    for pigeon in 0..pigeons {
        let derived_clause_id = bucket_alo_clause_id_start + pigeon;
        bucket_alo_rows.push(DenseCliquePhpBucketAloReplayRow {
            pigeon,
            source_support_id: witness.support_rows[pigeon].source_id,
            derived_clause_id,
            extension_vars_one_based: (0..holes)
                .map(|bucket| {
                    dense_clique_php_extension_var_one_based(
                        witness.scout.num_vars,
                        holes,
                        pigeon,
                        bucket,
                    )
                })
                .collect(),
        });
    }

    let mutex_map: BTreeMap<_, _> = witness
        .mutexes
        .iter()
        .map(|mutex| {
            (
                ordered_pair(mutex.lhs_variable, mutex.rhs_variable),
                mutex.source_id,
            )
        })
        .collect();
    let mut bucket_mutex_rows = Vec::with_capacity(bucket_mutex_rows_len);
    let mut next_bucket_mutex_clause_id = bucket_mutex_clause_id_start;
    for (bucket, bucket_vertices) in witness.php_obligation.bucket_vertices.iter().enumerate() {
        for lhs_pigeon in 0..pigeons {
            for rhs_pigeon in (lhs_pigeon + 1)..pigeons {
                let mut source_mutex_ids = Vec::with_capacity(bucket_vertices.len().pow(2));
                for &lhs_vertex in bucket_vertices {
                    for &rhs_vertex in bucket_vertices {
                        let lhs_variable = witness.support_rows[lhs_pigeon].variables[lhs_vertex];
                        let rhs_variable = witness.support_rows[rhs_pigeon].variables[rhs_vertex];
                        let pair = ordered_pair(lhs_variable, rhs_variable);
                        let source_id = mutex_map.get(&pair).copied().ok_or(
                            DenseCliquePhpReplayLedgerReject::MissingMutexSource {
                                bucket,
                                lhs_pigeon,
                                rhs_pigeon,
                                lhs_vertex,
                                rhs_vertex,
                                lhs_variable,
                                rhs_variable,
                            },
                        )?;
                        source_mutex_ids.push(source_id);
                    }
                }
                source_mutex_ids.sort_unstable();
                bucket_mutex_rows.push(DenseCliquePhpBucketMutexReplayRow {
                    bucket,
                    lhs_pigeon,
                    rhs_pigeon,
                    derived_clause_id: next_bucket_mutex_clause_id,
                    lhs_extension_var_one_based: dense_clique_php_extension_var_one_based(
                        witness.scout.num_vars,
                        holes,
                        lhs_pigeon,
                        bucket,
                    ),
                    rhs_extension_var_one_based: dense_clique_php_extension_var_one_based(
                        witness.scout.num_vars,
                        holes,
                        rhs_pigeon,
                        bucket,
                    ),
                    source_mutex_ids,
                });
                next_bucket_mutex_clause_id += 1;
            }
        }
    }

    Ok(DenseCliquePhpReplayLedger {
        original_vars: witness.scout.num_vars,
        original_clauses: witness.scout.num_clauses,
        pigeons,
        holes,
        bucket_vertices: witness.php_obligation.bucket_vertices.clone(),
        extension_var_start_one_based,
        extension_var_end_one_based,
        extension_clause_id_start,
        extension_clause_id_end,
        bucket_alo_clause_id_start,
        bucket_alo_clause_id_end,
        bucket_mutex_clause_id_start,
        bucket_mutex_clause_id_end,
        extension_rows,
        bucket_alo_rows,
        bucket_mutex_rows,
    })
}

fn validate_checker_audit_packet(
    packet: &DenseCliquePhpReplayPacket,
) -> Result<(), DenseCliquePhpCheckerAuditReject> {
    require_packet_equal(
        "source_audit.clauses_seen",
        packet.source_audit.source_rows,
        packet.source_audit.clauses_seen,
    )?;
    require_packet_equal(
        "ledger.original_vars",
        packet.witness.scout.num_vars,
        packet.replay_ledger.original_vars,
    )?;
    require_packet_equal(
        "ledger.original_clauses",
        packet.source_audit.source_rows,
        packet.replay_ledger.original_clauses,
    )?;
    require_packet_equal(
        "witness.source_rows",
        packet.source_audit.source_rows,
        packet.witness.support_rows.len() + packet.witness.mutexes.len(),
    )?;
    require_packet_equal(
        "ledger.pigeons",
        packet.witness.php_obligation.pigeons,
        packet.replay_ledger.pigeons,
    )?;
    require_packet_equal(
        "ledger.holes",
        packet.witness.php_obligation.holes,
        packet.replay_ledger.holes,
    )?;
    require_packet_equal(
        "ledger.extension_rows",
        packet.replay_ledger.pigeons * packet.replay_ledger.holes,
        packet.replay_ledger.extension_rows.len(),
    )?;
    require_packet_equal(
        "ledger.bucket_alo_rows",
        packet.replay_ledger.pigeons,
        packet.replay_ledger.bucket_alo_rows.len(),
    )?;
    require_packet_equal(
        "ledger.bucket_mutex_rows",
        packet.replay_ledger.holes
            * packet
                .replay_ledger
                .pigeons
                .saturating_mul(packet.replay_ledger.pigeons.saturating_sub(1))
            / 2,
        packet.replay_ledger.bucket_mutex_rows.len(),
    )?;
    Ok(())
}

fn push_extension_checker_rows(
    packet: &DenseCliquePhpReplayPacket,
    rows: &mut Vec<DenseCliquePhpCheckerVisibleRow>,
) -> Result<(), DenseCliquePhpCheckerAuditReject> {
    let ledger = &packet.replay_ledger;
    for (row_index, extension) in ledger.extension_rows.iter().enumerate() {
        let expected_pigeon = row_index / ledger.holes;
        let expected_bucket = row_index % ledger.holes;
        require_planned_row_equal(
            DenseCliquePhpCheckerVisibleRowKind::ExtensionForward,
            row_index,
            "pigeon",
            expected_pigeon,
            extension.pigeon,
        )?;
        require_planned_row_equal(
            DenseCliquePhpCheckerVisibleRowKind::ExtensionForward,
            row_index,
            "bucket",
            expected_bucket,
            extension.bucket,
        )?;
        require_planned_row_equal(
            DenseCliquePhpCheckerVisibleRowKind::ExtensionForward,
            row_index,
            "extension_var_one_based",
            dense_clique_php_extension_var_one_based(
                ledger.original_vars,
                ledger.holes,
                expected_pigeon,
                expected_bucket,
            ),
            extension.extension_var_one_based,
        )?;
        for offset in 0..3 {
            require_planned_row_equal(
                DenseCliquePhpCheckerVisibleRowKind::ExtensionForward,
                row_index,
                "extension_clause_id",
                ledger.extension_clause_id_start + row_index * 3 + offset,
                extension.extension_clause_ids[offset],
            )?;
        }
        require_planned_row_equal(
            DenseCliquePhpCheckerVisibleRowKind::ExtensionForward,
            row_index,
            "original_vars_one_based",
            2,
            extension.original_vars_one_based.len(),
        )?;

        let lhs_original = extension.original_vars_one_based[0];
        let rhs_original = extension.original_vars_one_based[1];
        let extension_var = extension.extension_var_one_based;
        rows.push(DenseCliquePhpCheckerVisibleRow {
            row_kind: DenseCliquePhpCheckerVisibleRowKind::ExtensionForward,
            checker_visible_id: extension.extension_clause_ids[0],
            clause_lits_dimacs: vec![
                checked_negative_dimacs(lhs_original)?,
                checked_positive_dimacs(extension_var)?,
            ],
            source_rows: Vec::new(),
            dependency_clause_ids: Vec::new(),
            external_checker_verified: false,
        });
        rows.push(DenseCliquePhpCheckerVisibleRow {
            row_kind: DenseCliquePhpCheckerVisibleRowKind::ExtensionForward,
            checker_visible_id: extension.extension_clause_ids[1],
            clause_lits_dimacs: vec![
                checked_negative_dimacs(rhs_original)?,
                checked_positive_dimacs(extension_var)?,
            ],
            source_rows: Vec::new(),
            dependency_clause_ids: Vec::new(),
            external_checker_verified: false,
        });
        rows.push(DenseCliquePhpCheckerVisibleRow {
            row_kind: DenseCliquePhpCheckerVisibleRowKind::ExtensionBackward,
            checker_visible_id: extension.extension_clause_ids[2],
            clause_lits_dimacs: vec![
                checked_positive_dimacs(lhs_original)?,
                checked_positive_dimacs(rhs_original)?,
                checked_negative_dimacs(extension_var)?,
            ],
            source_rows: Vec::new(),
            dependency_clause_ids: Vec::new(),
            external_checker_verified: false,
        });
    }
    Ok(())
}

fn push_bucket_alo_checker_rows(
    packet: &DenseCliquePhpReplayPacket,
    source_rows_by_id: &BTreeMap<usize, Vec<i32>>,
    rows: &mut Vec<DenseCliquePhpCheckerVisibleRow>,
) -> Result<(), DenseCliquePhpCheckerAuditReject> {
    let ledger = &packet.replay_ledger;
    for (row_index, alo) in ledger.bucket_alo_rows.iter().enumerate() {
        require_planned_row_equal(
            DenseCliquePhpCheckerVisibleRowKind::BucketAlo,
            row_index,
            "pigeon",
            row_index,
            alo.pigeon,
        )?;
        require_planned_row_equal(
            DenseCliquePhpCheckerVisibleRowKind::BucketAlo,
            row_index,
            "derived_clause_id",
            ledger.bucket_alo_clause_id_start + row_index,
            alo.derived_clause_id,
        )?;
        require_planned_row_equal(
            DenseCliquePhpCheckerVisibleRowKind::BucketAlo,
            row_index,
            "extension_vars_one_based",
            ledger.holes,
            alo.extension_vars_one_based.len(),
        )?;

        let mut dependency_clause_ids = Vec::with_capacity(ledger.holes * 2);
        for bucket in 0..ledger.holes {
            let extension = extension_replay_row(ledger, alo.pigeon, bucket);
            dependency_clause_ids.push(extension.extension_clause_ids[0]);
            dependency_clause_ids.push(extension.extension_clause_ids[1]);
            require_planned_row_equal(
                DenseCliquePhpCheckerVisibleRowKind::BucketAlo,
                row_index,
                "extension_var_one_based",
                extension.extension_var_one_based,
                alo.extension_vars_one_based[bucket],
            )?;
        }

        rows.push(DenseCliquePhpCheckerVisibleRow {
            row_kind: DenseCliquePhpCheckerVisibleRowKind::BucketAlo,
            checker_visible_id: alo.derived_clause_id,
            clause_lits_dimacs: alo
                .extension_vars_one_based
                .iter()
                .map(|&var| checked_positive_dimacs(var))
                .collect::<Result<Vec<_>, _>>()?,
            source_rows: checker_source_rows_for_ids(source_rows_by_id, &[alo.source_support_id])?,
            dependency_clause_ids,
            external_checker_verified: false,
        });
    }
    Ok(())
}

fn push_bucket_mutex_checker_rows(
    packet: &DenseCliquePhpReplayPacket,
    source_rows_by_id: &BTreeMap<usize, Vec<i32>>,
    rows: &mut Vec<DenseCliquePhpCheckerVisibleRow>,
) -> Result<(), DenseCliquePhpCheckerAuditReject> {
    let ledger = &packet.replay_ledger;
    for (row_index, mutex) in ledger.bucket_mutex_rows.iter().enumerate() {
        let pairs_per_bucket = ledger
            .pigeons
            .saturating_mul(ledger.pigeons.saturating_sub(1))
            / 2;
        let expected_bucket = row_index / pairs_per_bucket;
        require_planned_row_equal(
            DenseCliquePhpCheckerVisibleRowKind::BucketMutex,
            row_index,
            "bucket",
            expected_bucket,
            mutex.bucket,
        )?;
        require_planned_row_equal(
            DenseCliquePhpCheckerVisibleRowKind::BucketMutex,
            row_index,
            "derived_clause_id",
            ledger.bucket_mutex_clause_id_start + row_index,
            mutex.derived_clause_id,
        )?;
        require_planned_row_equal(
            DenseCliquePhpCheckerVisibleRowKind::BucketMutex,
            row_index,
            "lhs_extension_var_one_based",
            dense_clique_php_extension_var_one_based(
                ledger.original_vars,
                ledger.holes,
                mutex.lhs_pigeon,
                mutex.bucket,
            ),
            mutex.lhs_extension_var_one_based,
        )?;
        require_planned_row_equal(
            DenseCliquePhpCheckerVisibleRowKind::BucketMutex,
            row_index,
            "rhs_extension_var_one_based",
            dense_clique_php_extension_var_one_based(
                ledger.original_vars,
                ledger.holes,
                mutex.rhs_pigeon,
                mutex.bucket,
            ),
            mutex.rhs_extension_var_one_based,
        )?;
        if mutex.source_mutex_ids.len() != 4 {
            return Err(DenseCliquePhpCheckerAuditReject::SourceMutexCountMismatch {
                row_index,
                expected: 4,
                actual: mutex.source_mutex_ids.len(),
            });
        }

        let lhs_extension = extension_replay_row(ledger, mutex.lhs_pigeon, mutex.bucket);
        let rhs_extension = extension_replay_row(ledger, mutex.rhs_pigeon, mutex.bucket);
        rows.push(DenseCliquePhpCheckerVisibleRow {
            row_kind: DenseCliquePhpCheckerVisibleRowKind::BucketMutex,
            checker_visible_id: mutex.derived_clause_id,
            clause_lits_dimacs: vec![
                checked_negative_dimacs(mutex.lhs_extension_var_one_based)?,
                checked_negative_dimacs(mutex.rhs_extension_var_one_based)?,
            ],
            source_rows: checker_source_rows_for_ids(source_rows_by_id, &mutex.source_mutex_ids)?,
            dependency_clause_ids: vec![
                lhs_extension.extension_clause_ids[2],
                rhs_extension.extension_clause_ids[2],
            ],
            external_checker_verified: false,
        });
    }
    Ok(())
}

fn push_original_drat_extension_clauses(
    ledger: &DenseCliquePhpReplayLedger,
    drat: &mut String,
    stats: &mut DenseCliquePhpOriginalDratMaterializationStats,
) -> Result<(), DenseCliquePhpOriginalDratMaterializationReject> {
    for (row_index, extension) in ledger.extension_rows.iter().enumerate() {
        if extension.original_vars_one_based.len() != 2 {
            return Err(
                DenseCliquePhpOriginalDratMaterializationReject::ExtensionOriginalVarCountMismatch {
                    row_index,
                    expected: 2,
                    actual: extension.original_vars_one_based.len(),
                },
            );
        }
        let lhs_original = extension.original_vars_one_based[0];
        let rhs_original = extension.original_vars_one_based[1];
        let extension_var = extension.extension_var_one_based;
        push_original_drat_clause_line(
            false,
            &[
                checked_negative_dimacs_for_original_drat(lhs_original, 0)?,
                checked_positive_dimacs_for_original_drat(extension_var, 0)?,
            ],
            drat,
            stats,
        );
        push_original_drat_clause_line(
            false,
            &[
                checked_negative_dimacs_for_original_drat(rhs_original, 0)?,
                checked_positive_dimacs_for_original_drat(extension_var, 0)?,
            ],
            drat,
            stats,
        );
        push_original_drat_clause_line(
            false,
            &[
                checked_positive_dimacs_for_original_drat(lhs_original, 0)?,
                checked_positive_dimacs_for_original_drat(rhs_original, 0)?,
                checked_negative_dimacs_for_original_drat(extension_var, 0)?,
            ],
            drat,
            stats,
        );
        stats.extension_clauses_added += 3;
    }
    Ok(())
}

fn push_original_drat_bucket_alo_clauses(
    ledger: &DenseCliquePhpReplayLedger,
    drat: &mut String,
    stats: &mut DenseCliquePhpOriginalDratMaterializationStats,
) -> Result<(), DenseCliquePhpOriginalDratMaterializationReject> {
    for alo in &ledger.bucket_alo_rows {
        let clause = alo
            .extension_vars_one_based
            .iter()
            .map(|&var| checked_positive_dimacs_for_original_drat(var, 0))
            .collect::<Result<Vec<_>, _>>()?;
        push_original_drat_clause_line(false, &clause, drat, stats);
        stats.bucket_alo_clauses_added += 1;
        stats.planned_bucket_clauses_added += 1;
    }
    Ok(())
}

fn push_original_drat_bucket_mutex_clauses(
    ledger: &DenseCliquePhpReplayLedger,
    drat: &mut String,
    stats: &mut DenseCliquePhpOriginalDratMaterializationStats,
) -> Result<(), DenseCliquePhpOriginalDratMaterializationReject> {
    for mutex in &ledger.bucket_mutex_rows {
        let lhs_extension = extension_replay_row(ledger, mutex.lhs_pigeon, mutex.bucket);
        let rhs_extension_var =
            checked_negative_dimacs_for_original_drat(mutex.rhs_extension_var_one_based, 0)?;
        for &lhs_original in &lhs_extension.original_vars_one_based {
            push_original_drat_clause_line(
                false,
                &[
                    rhs_extension_var,
                    checked_negative_dimacs_for_original_drat(lhs_original, 0)?,
                ],
                drat,
                stats,
            );
            stats.bucket_mutex_support_clauses_added += 1;
        }

        push_original_drat_clause_line(
            false,
            &[
                checked_negative_dimacs_for_original_drat(mutex.lhs_extension_var_one_based, 0)?,
                rhs_extension_var,
            ],
            drat,
            stats,
        );
        stats.bucket_mutex_clauses_added += 1;
        stats.planned_bucket_clauses_added += 1;
    }
    Ok(())
}

fn push_remapped_compact_drat(
    ledger: &DenseCliquePhpReplayLedger,
    compact_drat: &str,
    drat: &mut String,
    stats: &mut DenseCliquePhpOriginalDratMaterializationStats,
) -> Result<(), DenseCliquePhpOriginalDratMaterializationReject> {
    for (line_index, line) in compact_drat.lines().enumerate() {
        let line_number = line_index + 1;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if trimmed.starts_with('c') {
            stats.compact_proof_comments_skipped += 1;
            continue;
        }

        let (deletion, literals) = remap_compact_drat_line(ledger, line_number, trimmed, stats)?;
        push_original_drat_clause_line(deletion, &literals, drat, stats);
        stats.compact_proof_lines_seen += 1;
        if deletion {
            stats.compact_proof_deletions_remapped += 1;
        } else {
            stats.compact_proof_additions_remapped += 1;
        }
    }
    Ok(())
}

fn remap_compact_drat_line(
    ledger: &DenseCliquePhpReplayLedger,
    line_number: usize,
    trimmed: &str,
    stats: &mut DenseCliquePhpOriginalDratMaterializationStats,
) -> Result<(bool, Vec<i32>), DenseCliquePhpOriginalDratMaterializationReject> {
    let mut tokens: Vec<_> = trimmed.split_whitespace().collect();
    let deletion = if tokens.first().copied() == Some("d") {
        tokens.remove(0);
        if tokens.is_empty() {
            return Err(
                DenseCliquePhpOriginalDratMaterializationReject::CompactProofMalformedDeletion {
                    line_number,
                },
            );
        }
        true
    } else {
        false
    };

    if tokens.last().copied() != Some("0") {
        return Err(
            DenseCliquePhpOriginalDratMaterializationReject::CompactProofMissingTerminator {
                line_number,
            },
        );
    }

    let mut literals = Vec::with_capacity(tokens.len().saturating_sub(1));
    for token in &tokens[..tokens.len().saturating_sub(1)] {
        let parsed = token.parse::<i64>().map_err(|_| {
            DenseCliquePhpOriginalDratMaterializationReject::CompactProofLiteralParse {
                line_number,
                token: (*token).to_string(),
            }
        })?;
        let abs = parsed.checked_abs().ok_or_else(|| {
            DenseCliquePhpOriginalDratMaterializationReject::CompactProofVariableOverflow {
                line_number,
                token: (*token).to_string(),
            }
        })?;
        if abs == 0 {
            return Err(
                DenseCliquePhpOriginalDratMaterializationReject::CompactProofZeroBeforeTerminator {
                    line_number,
                },
            );
        }
        let compact_variable = usize::try_from(abs).map_err(|_| {
            DenseCliquePhpOriginalDratMaterializationReject::CompactProofVariableOverflow {
                line_number,
                token: (*token).to_string(),
            }
        })?;
        stats.compact_proof_max_var = stats.compact_proof_max_var.max(compact_variable);
        let original_variable = ledger.original_vars.checked_add(compact_variable).ok_or(
            DenseCliquePhpOriginalDratMaterializationReject::OriginalVariableOverflow {
                line_number,
                compact_variable,
            },
        )?;
        let remapped = checked_positive_dimacs_for_original_drat(original_variable, line_number)?;
        literals.push(if parsed < 0 { -remapped } else { remapped });
    }
    Ok((deletion, literals))
}

fn push_original_drat_clause_line(
    deletion: bool,
    literals: &[i32],
    drat: &mut String,
    stats: &mut DenseCliquePhpOriginalDratMaterializationStats,
) {
    if deletion {
        drat.push_str("d ");
    }
    for &literal in literals {
        stats.original_proof_max_var = stats
            .original_proof_max_var
            .max(literal.unsigned_abs() as usize);
        drat.push_str(&literal.to_string());
        drat.push(' ');
    }
    drat.push_str("0\n");
}

fn checked_positive_dimacs_for_original_drat(
    variable_one_based: usize,
    line_number: usize,
) -> Result<i32, DenseCliquePhpOriginalDratMaterializationReject> {
    i32::try_from(variable_one_based).map_err(|_| {
        DenseCliquePhpOriginalDratMaterializationReject::DimacsLiteralOverflow {
            line_number,
            variable_one_based,
        }
    })
}

fn checked_negative_dimacs_for_original_drat(
    variable_one_based: usize,
    line_number: usize,
) -> Result<i32, DenseCliquePhpOriginalDratMaterializationReject> {
    checked_positive_dimacs_for_original_drat(variable_one_based, line_number).map(|lit| -lit)
}

#[derive(Debug, Clone)]
struct OriginalLratReplaySchedule {
    compact_clauses: u64,
    next_id: u64,
    bucket_alo_ids: Vec<u64>,
    bucket_mutex_ids: Vec<u64>,
    extension_forward_ids: Vec<[u64; 2]>,
    extension_backward_ids: Vec<u64>,
}

impl OriginalLratReplaySchedule {
    fn new(ledger: &DenseCliquePhpReplayLedger) -> Self {
        Self {
            compact_clauses: (ledger.bucket_alo_rows.len() + ledger.bucket_mutex_rows.len()) as u64,
            next_id: ledger.extension_clause_id_start as u64,
            bucket_alo_ids: Vec::with_capacity(ledger.bucket_alo_rows.len()),
            bucket_mutex_ids: Vec::with_capacity(ledger.bucket_mutex_rows.len()),
            extension_forward_ids: Vec::with_capacity(ledger.extension_rows.len()),
            extension_backward_ids: Vec::with_capacity(ledger.extension_rows.len()),
        }
    }

    fn take_next_id(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    fn compact_derived_id_offset(&self) -> u64 {
        self.next_id - 1 - self.compact_clauses
    }

    fn map_compact_id(
        &self,
        ledger: &DenseCliquePhpReplayLedger,
        compact_id: u64,
        line_number: usize,
    ) -> Result<u64, DenseCliquePhpOriginalLratMaterializationReject> {
        if compact_id == 0 {
            return Err(
                DenseCliquePhpOriginalLratMaterializationReject::CompactLratHintZero {
                    line_number,
                },
            );
        }
        let alo_count = ledger.bucket_alo_rows.len() as u64;
        if compact_id <= alo_count {
            return self
                .bucket_alo_ids
                .get(compact_id as usize - 1)
                .copied()
                .ok_or(
                    DenseCliquePhpOriginalLratMaterializationReject::OriginalClauseIdOverflow {
                        line_number,
                        compact_id,
                    },
                );
        }
        if compact_id <= self.compact_clauses {
            let compact_mutex_idx = (compact_id - alo_count - 1) as usize;
            let ledger_mutex_idx =
                compact_pair_major_mutex_index_to_ledger_index(ledger, compact_mutex_idx).ok_or(
                    DenseCliquePhpOriginalLratMaterializationReject::OriginalClauseIdOverflow {
                        line_number,
                        compact_id,
                    },
                )?;
            return self.bucket_mutex_ids.get(ledger_mutex_idx).copied().ok_or(
                DenseCliquePhpOriginalLratMaterializationReject::OriginalClauseIdOverflow {
                    line_number,
                    compact_id,
                },
            );
        }
        compact_id
            .checked_add(self.compact_derived_id_offset())
            .ok_or(
                DenseCliquePhpOriginalLratMaterializationReject::OriginalClauseIdOverflow {
                    line_number,
                    compact_id,
                },
            )
    }

    fn extension_forward_ids(
        &self,
        ledger: &DenseCliquePhpReplayLedger,
        pigeon: usize,
        bucket: usize,
    ) -> [u64; 2] {
        self.extension_forward_ids[pigeon * ledger.holes + bucket]
    }

    fn extension_backward_id(
        &self,
        ledger: &DenseCliquePhpReplayLedger,
        pigeon: usize,
        bucket: usize,
    ) -> u64 {
        self.extension_backward_ids[pigeon * ledger.holes + bucket]
    }
}

fn compact_pair_major_mutex_index_to_ledger_index(
    ledger: &DenseCliquePhpReplayLedger,
    compact_mutex_idx: usize,
) -> Option<usize> {
    let pair_count = ledger.pigeons.checked_mul(ledger.pigeons.checked_sub(1)?)? / 2;
    let compact_mutex_count = pair_count.checked_mul(ledger.holes)?;
    if compact_mutex_idx >= compact_mutex_count || ledger.holes == 0 {
        return None;
    }
    let pair_index = compact_mutex_idx / ledger.holes;
    let bucket = compact_mutex_idx % ledger.holes;
    let (lhs_pigeon, rhs_pigeon) = pigeon_pair_for_compact_pair_index(ledger.pigeons, pair_index)?;
    let ledger_index = bucket.checked_mul(pair_count)?.checked_add(pair_index)?;
    if let Some(row) = ledger.bucket_mutex_rows.get(ledger_index) {
        debug_assert_eq!(row.bucket, bucket);
        debug_assert_eq!(row.lhs_pigeon, lhs_pigeon);
        debug_assert_eq!(row.rhs_pigeon, rhs_pigeon);
    }
    Some(ledger_index)
}

fn pigeon_pair_for_compact_pair_index(pigeons: usize, pair_index: usize) -> Option<(usize, usize)> {
    let mut remaining = pair_index;
    for lhs_pigeon in 0..pigeons {
        let rhs_count = pigeons.checked_sub(lhs_pigeon + 1)?;
        if remaining < rhs_count {
            return Some((lhs_pigeon, lhs_pigeon + 1 + remaining));
        }
        remaining -= rhs_count;
    }
    None
}

fn push_original_lrat_extension_clauses(
    ledger: &DenseCliquePhpReplayLedger,
    schedule: &mut OriginalLratReplaySchedule,
    lrat: &mut String,
    stats: &mut DenseCliquePhpOriginalLratMaterializationStats,
) -> Result<(), DenseCliquePhpOriginalLratMaterializationReject> {
    for (row_index, extension) in ledger.extension_rows.iter().enumerate() {
        if extension.original_vars_one_based.len() != 2 {
            return Err(
                DenseCliquePhpOriginalLratMaterializationReject::ExtensionOriginalVarCountMismatch {
                    row_index,
                    expected: 2,
                    actual: extension.original_vars_one_based.len(),
                },
            );
        }
        let lhs_original = extension.original_vars_one_based[0];
        let rhs_original = extension.original_vars_one_based[1];
        let extension_var = extension.extension_var_one_based;
        let forward_lhs_id = schedule.take_next_id();
        let forward_rhs_id = schedule.take_next_id();
        let backward_id = schedule.take_next_id();
        debug_assert_eq!(forward_lhs_id, extension.extension_clause_ids[0] as u64);
        debug_assert_eq!(forward_rhs_id, extension.extension_clause_ids[1] as u64);
        debug_assert_eq!(backward_id, extension.extension_clause_ids[2] as u64);

        push_original_lrat_add_line(
            forward_lhs_id,
            &[
                checked_positive_dimacs_for_original_lrat(extension_var, 0)?,
                checked_negative_dimacs_for_original_lrat(lhs_original, 0)?,
            ],
            &[],
            lrat,
            stats,
        );
        push_original_lrat_add_line(
            forward_rhs_id,
            &[
                checked_positive_dimacs_for_original_lrat(extension_var, 0)?,
                checked_negative_dimacs_for_original_lrat(rhs_original, 0)?,
            ],
            &[],
            lrat,
            stats,
        );
        push_original_lrat_add_line(
            backward_id,
            &[
                checked_negative_dimacs_for_original_lrat(extension_var, 0)?,
                checked_positive_dimacs_for_original_lrat(lhs_original, 0)?,
                checked_positive_dimacs_for_original_lrat(rhs_original, 0)?,
            ],
            &[-(forward_lhs_id as i64), -(forward_rhs_id as i64)],
            lrat,
            stats,
        );
        schedule
            .extension_forward_ids
            .push([forward_lhs_id, forward_rhs_id]);
        schedule.extension_backward_ids.push(backward_id);
        stats.extension_clauses_added += 3;
    }
    Ok(())
}

fn push_original_lrat_bucket_alo_clauses(
    ledger: &DenseCliquePhpReplayLedger,
    schedule: &mut OriginalLratReplaySchedule,
    lrat: &mut String,
    stats: &mut DenseCliquePhpOriginalLratMaterializationStats,
) -> Result<(), DenseCliquePhpOriginalLratMaterializationReject> {
    for alo in &ledger.bucket_alo_rows {
        let id = schedule.take_next_id();
        debug_assert_eq!(id, alo.derived_clause_id as u64);
        let clause = alo
            .extension_vars_one_based
            .iter()
            .map(|&var| checked_positive_dimacs_for_original_lrat(var, 0))
            .collect::<Result<Vec<_>, _>>()?;
        let mut hints = Vec::with_capacity(ledger.holes * 2 + 1);
        for bucket in 0..ledger.holes {
            let [lhs_forward, rhs_forward] =
                schedule.extension_forward_ids(ledger, alo.pigeon, bucket);
            hints.push(lhs_forward as i64);
            hints.push(rhs_forward as i64);
        }
        hints.push(alo.source_support_id as i64);
        push_original_lrat_add_line(id, &clause, &hints, lrat, stats);
        schedule.bucket_alo_ids.push(id);
        stats.bucket_alo_clauses_added += 1;
        stats.planned_bucket_clauses_added += 1;
    }
    Ok(())
}

fn push_original_lrat_bucket_mutex_clauses(
    ledger: &DenseCliquePhpReplayLedger,
    source_mutex_ids: &BTreeMap<(usize, usize), usize>,
    schedule: &mut OriginalLratReplaySchedule,
    lrat: &mut String,
    stats: &mut DenseCliquePhpOriginalLratMaterializationStats,
) -> Result<(), DenseCliquePhpOriginalLratMaterializationReject> {
    for mutex in &ledger.bucket_mutex_rows {
        let lhs_extension = extension_replay_row(ledger, mutex.lhs_pigeon, mutex.bucket);
        let rhs_extension = extension_replay_row(ledger, mutex.rhs_pigeon, mutex.bucket);
        if lhs_extension.original_vars_one_based.len() != 2 {
            return Err(
                DenseCliquePhpOriginalLratMaterializationReject::ExtensionOriginalVarCountMismatch {
                    row_index: mutex.lhs_pigeon * ledger.holes + mutex.bucket,
                    expected: 2,
                    actual: lhs_extension.original_vars_one_based.len(),
                },
            );
        }
        if rhs_extension.original_vars_one_based.len() != 2 {
            return Err(
                DenseCliquePhpOriginalLratMaterializationReject::ExtensionOriginalVarCountMismatch {
                    row_index: mutex.rhs_pigeon * ledger.holes + mutex.bucket,
                    expected: 2,
                    actual: rhs_extension.original_vars_one_based.len(),
                },
            );
        }

        let rhs_backward_id =
            schedule.extension_backward_id(ledger, mutex.rhs_pigeon, mutex.bucket);
        let mut support_ids = Vec::with_capacity(lhs_extension.original_vars_one_based.len());
        for &lhs_original in &lhs_extension.original_vars_one_based {
            let source_a = original_lrat_mutex_source_id(
                source_mutex_ids,
                mutex,
                lhs_original,
                rhs_extension.original_vars_one_based[0],
            )?;
            let source_b = original_lrat_mutex_source_id(
                source_mutex_ids,
                mutex,
                lhs_original,
                rhs_extension.original_vars_one_based[1],
            )?;
            let support_id = schedule.take_next_id();
            push_original_lrat_add_line(
                support_id,
                &[
                    checked_negative_dimacs_for_original_lrat(
                        mutex.rhs_extension_var_one_based,
                        0,
                    )?,
                    checked_negative_dimacs_for_original_lrat(lhs_original, 0)?,
                ],
                &[source_a as i64, rhs_backward_id as i64, source_b as i64],
                lrat,
                stats,
            );
            support_ids.push(support_id);
            stats.bucket_mutex_support_clauses_added += 1;
        }

        let lhs_backward_id =
            schedule.extension_backward_id(ledger, mutex.lhs_pigeon, mutex.bucket);
        let mutex_id = schedule.take_next_id();
        push_original_lrat_add_line(
            mutex_id,
            &[
                checked_negative_dimacs_for_original_lrat(mutex.lhs_extension_var_one_based, 0)?,
                checked_negative_dimacs_for_original_lrat(mutex.rhs_extension_var_one_based, 0)?,
            ],
            &[
                support_ids[1] as i64,
                lhs_backward_id as i64,
                support_ids[0] as i64,
            ],
            lrat,
            stats,
        );
        schedule.bucket_mutex_ids.push(mutex_id);
        stats.bucket_mutex_clauses_added += 1;
        stats.planned_bucket_clauses_added += 1;
    }
    Ok(())
}

fn push_remapped_compact_lrat(
    ledger: &DenseCliquePhpReplayLedger,
    schedule: &OriginalLratReplaySchedule,
    compact_lrat: &str,
    lrat: &mut String,
    stats: &mut DenseCliquePhpOriginalLratMaterializationStats,
) -> Result<(), DenseCliquePhpOriginalLratMaterializationReject> {
    for (line_index, line) in compact_lrat.lines().enumerate() {
        let line_number = line_index + 1;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if trimmed.starts_with('c') {
            stats.compact_lrat_comments_skipped += 1;
            continue;
        }
        let parsed = parse_compact_lrat_line(ledger, schedule, line_number, trimmed, stats)?;
        stats.compact_lrat_lines_seen += 1;
        match parsed {
            RemappedCompactLratLine::Add { id, clause, hints } => {
                push_original_lrat_add_line(id, &clause, &hints, lrat, stats);
                stats.compact_lrat_additions_remapped += 1;
            }
            RemappedCompactLratLine::Delete { id, deleted_ids } => {
                stats.compact_lrat_deletions_remapped += 1;
                if deleted_ids.is_empty() {
                    stats.compact_lrat_empty_deletions_skipped += 1;
                    continue;
                }
                push_original_lrat_delete_line(id, &deleted_ids, lrat, stats);
            }
        }
    }
    Ok(())
}

enum RemappedCompactLratLine {
    Add {
        id: u64,
        clause: Vec<i32>,
        hints: Vec<i64>,
    },
    Delete {
        id: u64,
        deleted_ids: Vec<u64>,
    },
}

fn parse_compact_lrat_line(
    ledger: &DenseCliquePhpReplayLedger,
    schedule: &OriginalLratReplaySchedule,
    line_number: usize,
    trimmed: &str,
    stats: &mut DenseCliquePhpOriginalLratMaterializationStats,
) -> Result<RemappedCompactLratLine, DenseCliquePhpOriginalLratMaterializationReject> {
    let tokens = trimmed.split_whitespace().collect::<Vec<_>>();
    let compact_id = parse_compact_lrat_id(line_number, tokens.first().copied())?;
    stats.compact_lrat_max_id = stats.compact_lrat_max_id.max(compact_id);
    if tokens.get(1).copied() == Some("d") {
        let deleted_ids =
            parse_compact_lrat_delete_ids(ledger, schedule, line_number, &tokens[2..], stats)?;
        return Ok(RemappedCompactLratLine::Delete {
            id: schedule.map_compact_id(ledger, compact_id, line_number)?,
            deleted_ids,
        });
    }
    if compact_id <= schedule.compact_clauses {
        return Err(
            DenseCliquePhpOriginalLratMaterializationReject::CompactLratOriginalAddId {
                line_number,
                compact_id,
            },
        );
    }
    let id = schedule.map_compact_id(ledger, compact_id, line_number)?;
    let (clause, hint_tokens) =
        parse_compact_lrat_clause(ledger, line_number, &tokens[1..], stats)?;
    let hints = parse_compact_lrat_hints(ledger, schedule, line_number, hint_tokens, stats)?;
    Ok(RemappedCompactLratLine::Add { id, clause, hints })
}

fn parse_compact_lrat_id(
    line_number: usize,
    token: Option<&str>,
) -> Result<u64, DenseCliquePhpOriginalLratMaterializationReject> {
    let token = token.ok_or(
        DenseCliquePhpOriginalLratMaterializationReject::CompactLratMissingId { line_number },
    )?;
    let id = token.parse::<u64>().map_err(|_| {
        DenseCliquePhpOriginalLratMaterializationReject::CompactLratIdParse {
            line_number,
            token: token.to_string(),
        }
    })?;
    if id == 0 {
        return Err(
            DenseCliquePhpOriginalLratMaterializationReject::CompactLratIdZero { line_number },
        );
    }
    Ok(id)
}

fn parse_compact_lrat_clause<'a>(
    ledger: &DenseCliquePhpReplayLedger,
    line_number: usize,
    tokens: &'a [&'a str],
    stats: &mut DenseCliquePhpOriginalLratMaterializationStats,
) -> Result<(Vec<i32>, &'a [&'a str]), DenseCliquePhpOriginalLratMaterializationReject> {
    let Some(terminator) = tokens.iter().position(|token| *token == "0") else {
        return Err(
            DenseCliquePhpOriginalLratMaterializationReject::CompactLratMissingClauseTerminator {
                line_number,
            },
        );
    };
    let mut clause = Vec::with_capacity(terminator);
    for token in &tokens[..terminator] {
        let parsed = token.parse::<i64>().map_err(|_| {
            DenseCliquePhpOriginalLratMaterializationReject::CompactLratLiteralParse {
                line_number,
                token: (*token).to_string(),
            }
        })?;
        let abs = parsed.checked_abs().ok_or_else(|| {
            DenseCliquePhpOriginalLratMaterializationReject::CompactLratVariableOverflow {
                line_number,
                token: (*token).to_string(),
            }
        })?;
        if abs == 0 {
            return Err(
                DenseCliquePhpOriginalLratMaterializationReject::CompactLratLiteralParse {
                    line_number,
                    token: (*token).to_string(),
                },
            );
        }
        let compact_variable = usize::try_from(abs).map_err(|_| {
            DenseCliquePhpOriginalLratMaterializationReject::CompactLratVariableOverflow {
                line_number,
                token: (*token).to_string(),
            }
        })?;
        stats.compact_lrat_max_var = stats.compact_lrat_max_var.max(compact_variable);
        let original_variable = ledger.original_vars.checked_add(compact_variable).ok_or(
            DenseCliquePhpOriginalLratMaterializationReject::OriginalVariableOverflow {
                line_number,
                compact_variable,
            },
        )?;
        let remapped = checked_positive_dimacs_for_original_lrat(original_variable, line_number)?;
        clause.push(if parsed < 0 { -remapped } else { remapped });
    }
    Ok((clause, &tokens[terminator + 1..]))
}

fn parse_compact_lrat_hints(
    ledger: &DenseCliquePhpReplayLedger,
    schedule: &OriginalLratReplaySchedule,
    line_number: usize,
    tokens: &[&str],
    stats: &mut DenseCliquePhpOriginalLratMaterializationStats,
) -> Result<Vec<i64>, DenseCliquePhpOriginalLratMaterializationReject> {
    let Some(terminator) = tokens.iter().position(|token| *token == "0") else {
        return Err(
            DenseCliquePhpOriginalLratMaterializationReject::CompactLratMissingHintTerminator {
                line_number,
            },
        );
    };
    if terminator + 1 != tokens.len() {
        return Err(
            DenseCliquePhpOriginalLratMaterializationReject::CompactLratTrailingTokens {
                line_number,
            },
        );
    }
    tokens[..terminator]
        .iter()
        .map(|token| remap_compact_lrat_signed_hint(ledger, schedule, line_number, token, stats))
        .collect()
}

fn parse_compact_lrat_delete_ids(
    ledger: &DenseCliquePhpReplayLedger,
    schedule: &OriginalLratReplaySchedule,
    line_number: usize,
    tokens: &[&str],
    stats: &mut DenseCliquePhpOriginalLratMaterializationStats,
) -> Result<Vec<u64>, DenseCliquePhpOriginalLratMaterializationReject> {
    let Some(terminator) = tokens.iter().position(|token| *token == "0") else {
        return Err(
            DenseCliquePhpOriginalLratMaterializationReject::CompactLratMissingDeletionTerminator {
                line_number,
            },
        );
    };
    if terminator + 1 != tokens.len() {
        return Err(
            DenseCliquePhpOriginalLratMaterializationReject::CompactLratTrailingTokens {
                line_number,
            },
        );
    }
    tokens[..terminator]
        .iter()
        .map(|token| {
            let parsed = token.parse::<u64>().map_err(|_| {
                DenseCliquePhpOriginalLratMaterializationReject::CompactLratHintParse {
                    line_number,
                    token: (*token).to_string(),
                }
            })?;
            if parsed == 0 {
                return Err(
                    DenseCliquePhpOriginalLratMaterializationReject::CompactLratHintZero {
                        line_number,
                    },
                );
            }
            stats.compact_lrat_max_id = stats.compact_lrat_max_id.max(parsed);
            schedule.map_compact_id(ledger, parsed, line_number)
        })
        .collect()
}

fn remap_compact_lrat_signed_hint(
    ledger: &DenseCliquePhpReplayLedger,
    schedule: &OriginalLratReplaySchedule,
    line_number: usize,
    token: &str,
    stats: &mut DenseCliquePhpOriginalLratMaterializationStats,
) -> Result<i64, DenseCliquePhpOriginalLratMaterializationReject> {
    let parsed = token.parse::<i64>().map_err(|_| {
        DenseCliquePhpOriginalLratMaterializationReject::CompactLratHintParse {
            line_number,
            token: token.to_string(),
        }
    })?;
    let abs = parsed.checked_abs().ok_or_else(|| {
        DenseCliquePhpOriginalLratMaterializationReject::CompactLratHintParse {
            line_number,
            token: token.to_string(),
        }
    })?;
    if abs == 0 {
        return Err(
            DenseCliquePhpOriginalLratMaterializationReject::CompactLratHintZero { line_number },
        );
    }
    let compact_id = u64::try_from(abs).map_err(|_| {
        DenseCliquePhpOriginalLratMaterializationReject::CompactLratHintParse {
            line_number,
            token: token.to_string(),
        }
    })?;
    stats.compact_lrat_max_id = stats.compact_lrat_max_id.max(compact_id);
    let mapped = schedule.map_compact_id(ledger, compact_id, line_number)?;
    let mapped = i64::try_from(mapped).map_err(|_| {
        DenseCliquePhpOriginalLratMaterializationReject::OriginalClauseIdOverflow {
            line_number,
            compact_id,
        }
    })?;
    Ok(if parsed < 0 { -mapped } else { mapped })
}

fn push_original_lrat_add_line(
    id: u64,
    literals: &[i32],
    hints: &[i64],
    lrat: &mut String,
    stats: &mut DenseCliquePhpOriginalLratMaterializationStats,
) {
    stats.original_lrat_max_id = stats.original_lrat_max_id.max(id);
    lrat.push_str(&id.to_string());
    lrat.push(' ');
    for &literal in literals {
        stats.original_lrat_max_var = stats
            .original_lrat_max_var
            .max(literal.unsigned_abs() as usize);
        lrat.push_str(&literal.to_string());
        lrat.push(' ');
    }
    lrat.push('0');
    for &hint in hints {
        stats.original_lrat_max_id = stats.original_lrat_max_id.max(hint.unsigned_abs());
        lrat.push(' ');
        lrat.push_str(&hint.to_string());
    }
    lrat.push_str(" 0\n");
}

fn push_original_lrat_delete_line(
    id: u64,
    deleted_ids: &[u64],
    lrat: &mut String,
    stats: &mut DenseCliquePhpOriginalLratMaterializationStats,
) {
    stats.original_lrat_max_id = stats.original_lrat_max_id.max(id);
    lrat.push_str(&id.to_string());
    lrat.push_str(" d");
    for &deleted_id in deleted_ids {
        stats.original_lrat_max_id = stats.original_lrat_max_id.max(deleted_id);
        lrat.push(' ');
        lrat.push_str(&deleted_id.to_string());
    }
    lrat.push_str(" 0\n");
}

fn checked_positive_dimacs_for_original_lrat(
    variable_one_based: usize,
    line_number: usize,
) -> Result<i32, DenseCliquePhpOriginalLratMaterializationReject> {
    i32::try_from(variable_one_based).map_err(|_| {
        DenseCliquePhpOriginalLratMaterializationReject::DimacsLiteralOverflow {
            line_number,
            variable_one_based,
        }
    })
}

fn checked_negative_dimacs_for_original_lrat(
    variable_one_based: usize,
    line_number: usize,
) -> Result<i32, DenseCliquePhpOriginalLratMaterializationReject> {
    checked_positive_dimacs_for_original_lrat(variable_one_based, line_number).map(|lit| -lit)
}

fn original_lrat_source_mutex_ids(
    packet: &DenseCliquePhpReplayPacket,
) -> BTreeMap<(usize, usize), usize> {
    packet
        .witness
        .mutexes
        .iter()
        .map(|mutex| {
            (
                ordered_pair(mutex.lhs_variable + 1, mutex.rhs_variable + 1),
                mutex.source_id,
            )
        })
        .collect()
}

fn original_lrat_mutex_source_id(
    source_mutex_ids: &BTreeMap<(usize, usize), usize>,
    mutex: &DenseCliquePhpBucketMutexReplayRow,
    lhs_original_var: usize,
    rhs_original_var: usize,
) -> Result<usize, DenseCliquePhpOriginalLratMaterializationReject> {
    source_mutex_ids
        .get(&ordered_pair(lhs_original_var, rhs_original_var))
        .copied()
        .ok_or(
            DenseCliquePhpOriginalLratMaterializationReject::MissingSourceMutex {
                bucket: mutex.bucket,
                lhs_pigeon: mutex.lhs_pigeon,
                rhs_pigeon: mutex.rhs_pigeon,
                lhs_original_var,
                rhs_original_var,
            },
        )
}

fn checker_audit_source_rows_by_id(witness: &DenseCliqueWitness) -> BTreeMap<usize, Vec<i32>> {
    let mut source_rows = BTreeMap::new();
    for support in &witness.support_rows {
        source_rows.insert(support.source_id, support.raw_dimacs.clone());
    }
    for mutex in &witness.mutexes {
        source_rows.insert(mutex.source_id, mutex.raw_dimacs.clone());
    }
    source_rows
}

fn checker_source_rows_for_ids(
    source_rows_by_id: &BTreeMap<usize, Vec<i32>>,
    source_ids: &[usize],
) -> Result<Vec<DenseCliquePhpCheckerSourceRow>, DenseCliquePhpCheckerAuditReject> {
    source_ids
        .iter()
        .map(|&source_id| {
            let raw_dimacs = source_rows_by_id
                .get(&source_id)
                .cloned()
                .ok_or(DenseCliquePhpCheckerAuditReject::MissingSourceRow { source_id })?;
            Ok(DenseCliquePhpCheckerSourceRow {
                source_id,
                raw_dimacs,
            })
        })
        .collect()
}

fn extension_replay_row(
    ledger: &DenseCliquePhpReplayLedger,
    pigeon: usize,
    bucket: usize,
) -> &DenseCliquePhpExtensionReplayRow {
    &ledger.extension_rows[pigeon * ledger.holes + bucket]
}

fn require_packet_equal(
    field: &'static str,
    expected: usize,
    actual: usize,
) -> Result<(), DenseCliquePhpCheckerAuditReject> {
    if expected != actual {
        return Err(DenseCliquePhpCheckerAuditReject::PacketLedgerMismatch {
            field,
            expected,
            actual,
        });
    }
    Ok(())
}

fn require_planned_row_equal(
    row_kind: DenseCliquePhpCheckerVisibleRowKind,
    row_index: usize,
    field: &'static str,
    expected: usize,
    actual: usize,
) -> Result<(), DenseCliquePhpCheckerAuditReject> {
    if expected != actual {
        return Err(DenseCliquePhpCheckerAuditReject::PlannedRowMismatch {
            row_kind,
            row_index,
            field,
            expected,
            actual,
        });
    }
    Ok(())
}

fn checked_positive_dimacs(
    variable_one_based: usize,
) -> Result<i32, DenseCliquePhpCheckerAuditReject> {
    i32::try_from(variable_one_based)
        .map_err(|_| DenseCliquePhpCheckerAuditReject::DimacsLiteralOverflow { variable_one_based })
}

fn checked_negative_dimacs(
    variable_one_based: usize,
) -> Result<i32, DenseCliquePhpCheckerAuditReject> {
    checked_positive_dimacs(variable_one_based).map(|lit| -lit)
}

fn dense_clique_php_extension_var_one_based(
    original_vars: usize,
    holes: usize,
    pigeon: usize,
    bucket: usize,
) -> usize {
    original_vars + pigeon * holes + bucket + 1
}

fn validate_source_clause_ids(
    source_clauses: &[DenseCliqueSourceClause],
) -> Result<(), DenseCliqueWitnessReject> {
    let mut seen = BTreeSet::new();
    for source_clause in source_clauses {
        if !seen.insert(source_clause.source_id) {
            return Err(DenseCliqueWitnessReject::DuplicateSourceId {
                source_id: source_clause.source_id,
            });
        }
    }
    for (idx, source_id) in seen.iter().copied().enumerate() {
        let expected = idx + 1;
        if source_id != expected {
            return Err(DenseCliqueWitnessReject::NonContiguousSourceId {
                expected,
                actual: source_id,
            });
        }
    }
    Ok(())
}

fn validate_raw_dimacs_rows(
    source_clauses: &[DenseCliqueSourceClause],
) -> Result<(), DenseCliqueWitnessReject> {
    for source_clause in source_clauses {
        let expected: Vec<_> = source_clause
            .literals
            .iter()
            .map(|lit| lit.to_dimacs())
            .collect();
        if source_clause.raw_dimacs != expected {
            return Err(DenseCliqueWitnessReject::RawDimacsMismatch {
                source_id: source_clause.source_id,
                expected,
                actual: source_clause.raw_dimacs.clone(),
            });
        }
    }
    Ok(())
}

fn is_positive_support_clause(clause: &[Literal]) -> bool {
    if clause.len() < 2 || clause.iter().any(|lit| !lit.is_positive()) {
        return false;
    }
    let mut vars: Vec<_> = clause.iter().map(|lit| lit.variable().index()).collect();
    vars.sort_unstable();
    vars.windows(2).all(|pair| pair[0] != pair[1])
}

fn negative_binary_mutex_pair(clause: &[Literal]) -> Option<(usize, usize)> {
    if clause.len() != 2 || clause.iter().any(|lit| lit.is_positive()) {
        return None;
    }
    let a = clause[0].variable().index();
    let b = clause[1].variable().index();
    if a == b {
        return None;
    }
    Some(if a < b { (a, b) } else { (b, a) })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RecoveredGraphMutexes {
    graph_edges: usize,
    graph_non_edges: usize,
    graph_non_edge_buckets: usize,
    graph_non_edge_bucket_min: usize,
    graph_non_edge_bucket_max: usize,
    complete_multipartite: bool,
    expected_mutexes: usize,
}

fn recover_graph_mutexes(
    support_rows: &[Vec<usize>],
    mutex_pairs: &BTreeSet<(usize, usize)>,
) -> Result<RecoveredGraphMutexes, DenseCliqueRejection> {
    let colors = support_rows.len();
    let width = support_rows[0].len();
    let color_pairs = colors.saturating_mul(colors.saturating_sub(1)) / 2;
    let mut expected_mutexes = 0usize;

    for row in support_rows {
        for lhs_vertex in 0..width {
            for rhs_vertex in (lhs_vertex + 1)..width {
                if !mutex_pairs.contains(&ordered_pair(row[lhs_vertex], row[rhs_vertex])) {
                    return Err(DenseCliqueRejection::IncompleteMutexGraph);
                }
                expected_mutexes += 1;
            }
        }
    }

    for lhs_color in 0..colors {
        for rhs_color in (lhs_color + 1)..colors {
            let lhs_row = &support_rows[lhs_color];
            let rhs_row = &support_rows[rhs_color];
            for vertex in 0..width {
                if !mutex_pairs.contains(&ordered_pair(lhs_row[vertex], rhs_row[vertex])) {
                    return Err(DenseCliqueRejection::IncompleteMutexGraph);
                }
                expected_mutexes += 1;
            }
        }
    }

    let mut edges = 0usize;
    let mut graph_non_edges = Vec::new();
    for lhs_vertex in 0..width {
        for rhs_vertex in (lhs_vertex + 1)..width {
            let mut mutex_count = 0usize;
            for lhs_color in 0..colors {
                for rhs_color in (lhs_color + 1)..colors {
                    let lhs_row = &support_rows[lhs_color];
                    let rhs_row = &support_rows[rhs_color];
                    if mutex_pairs.contains(&ordered_pair(lhs_row[lhs_vertex], rhs_row[rhs_vertex]))
                    {
                        mutex_count += 1;
                    }
                    if mutex_pairs.contains(&ordered_pair(lhs_row[rhs_vertex], rhs_row[lhs_vertex]))
                    {
                        mutex_count += 1;
                    }
                }
            }
            let total_ordered_color_pairs = color_pairs * 2;
            if mutex_count == 0 {
                edges += 1;
            } else if mutex_count == total_ordered_color_pairs {
                expected_mutexes += mutex_count;
                graph_non_edges.push((lhs_vertex, rhs_vertex));
            } else {
                return Err(DenseCliqueRejection::InconsistentGraphMutexes);
            }
        }
    }
    let buckets = recover_graph_non_edge_buckets(width, &graph_non_edges);
    Ok(RecoveredGraphMutexes {
        graph_edges: edges,
        graph_non_edges: graph_non_edges.len(),
        graph_non_edge_buckets: buckets.count,
        graph_non_edge_bucket_min: buckets.min,
        graph_non_edge_bucket_max: buckets.max,
        complete_multipartite: buckets.complete_multipartite,
        expected_mutexes,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct GraphNonEdgeBuckets {
    count: usize,
    min: usize,
    max: usize,
    complete_multipartite: bool,
}

fn recover_graph_non_edge_buckets(
    width: usize,
    graph_non_edges: &[(usize, usize)],
) -> GraphNonEdgeBuckets {
    let mut adjacency = vec![BTreeSet::new(); width];
    for &(lhs, rhs) in graph_non_edges {
        adjacency[lhs].insert(rhs);
        adjacency[rhs].insert(lhs);
    }

    let mut seen = vec![false; width];
    let mut count = 0usize;
    let mut min = usize::MAX;
    let mut max = 0usize;
    let mut complete_multipartite = true;
    for root in 0..width {
        if seen[root] {
            continue;
        }
        count += 1;
        let mut stack = vec![root];
        let mut component = Vec::new();
        seen[root] = true;
        while let Some(vertex) = stack.pop() {
            component.push(vertex);
            for &next in &adjacency[vertex] {
                if !seen[next] {
                    seen[next] = true;
                    stack.push(next);
                }
            }
        }
        min = min.min(component.len());
        max = max.max(component.len());
        for lhs_idx in 0..component.len() {
            for rhs_idx in (lhs_idx + 1)..component.len() {
                let lhs = component[lhs_idx];
                let rhs = component[rhs_idx];
                if !adjacency[lhs].contains(&rhs) {
                    complete_multipartite = false;
                }
            }
        }
    }

    if count == 0 {
        min = 0;
    }

    GraphNonEdgeBuckets {
        count,
        min,
        max,
        complete_multipartite,
    }
}

fn recover_graph_pair_witnesses(
    support_rows: &[DenseCliqueSupportRowWitness],
    mutex_map: &BTreeMap<(usize, usize), usize>,
) -> Vec<DenseCliqueGraphPairWitness> {
    let colors = support_rows.len();
    let width = support_rows[0].variables.len();
    let mut graph_pairs = Vec::new();
    for lhs_vertex in 0..width {
        for rhs_vertex in (lhs_vertex + 1)..width {
            let mut cross_mutex_source_ids = Vec::new();
            for lhs_color in 0..colors {
                for rhs_color in (lhs_color + 1)..colors {
                    let lhs_row = &support_rows[lhs_color].variables;
                    let rhs_row = &support_rows[rhs_color].variables;
                    if let Some(source_id) =
                        mutex_map.get(&ordered_pair(lhs_row[lhs_vertex], rhs_row[rhs_vertex]))
                    {
                        cross_mutex_source_ids.push(*source_id);
                    }
                    if let Some(source_id) =
                        mutex_map.get(&ordered_pair(lhs_row[rhs_vertex], rhs_row[lhs_vertex]))
                    {
                        cross_mutex_source_ids.push(*source_id);
                    }
                }
            }
            cross_mutex_source_ids.sort_unstable();
            graph_pairs.push(DenseCliqueGraphPairWitness {
                lhs_vertex,
                rhs_vertex,
                graph_edge: cross_mutex_source_ids.is_empty(),
                cross_mutex_source_ids,
            });
        }
    }
    graph_pairs
}

fn ordered_pair(a: usize, b: usize) -> (usize, usize) {
    if a < b {
        (a, b)
    } else {
        (b, a)
    }
}

fn recover_graph_non_edge_bucket_vertices(
    width: usize,
    graph_non_edges: &[(usize, usize)],
) -> Vec<Vec<usize>> {
    let mut adjacency = vec![BTreeSet::new(); width];
    for &(lhs, rhs) in graph_non_edges {
        adjacency[lhs].insert(rhs);
        adjacency[rhs].insert(lhs);
    }

    let mut seen = vec![false; width];
    let mut buckets = Vec::new();
    for root in 0..width {
        if seen[root] {
            continue;
        }
        let mut stack = vec![root];
        let mut component = Vec::new();
        seen[root] = true;
        while let Some(vertex) = stack.pop() {
            component.push(vertex);
            for &next in &adjacency[vertex] {
                if !seen[next] {
                    seen[next] = true;
                    stack.push(next);
                }
            }
        }
        component.sort_unstable();
        buckets.push(component);
    }
    buckets
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse_dimacs, Literal, Variable};
    use std::env;
    use std::fs;
    use std::path::Path;

    fn pos(var: usize) -> Literal {
        Literal::positive(Variable(var as u32))
    }

    fn neg(var: usize) -> Literal {
        Literal::negative(Variable(var as u32))
    }

    fn strict_fixture(colors: usize, width: usize) -> Vec<Vec<Literal>> {
        let mut clauses = Vec::new();
        for color in 0..colors {
            clauses.push((0..width).map(|idx| pos(color * width + idx)).collect());
        }
        for lhs in 0..(colors * width) {
            for rhs in (lhs + 1)..(colors * width) {
                clauses.push(vec![neg(lhs), neg(rhs)]);
            }
        }
        clauses
    }

    fn source_clauses(clauses: &[Vec<Literal>]) -> Vec<DenseCliqueSourceClause> {
        dense_clique_source_clauses_from_clauses(clauses).clauses
    }

    fn parse_optional_xz_fixture(relative_path: &str) -> Option<crate::DimacsFormula> {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative_path);
        if !path.exists() {
            eprintln!("dense clique scout fixture missing: {}", path.display());
            return None;
        }
        let content = String::from_utf8(crate::test_xz::decompress_xz_path(&path)?)
            .expect("fixture is UTF-8 DIMACS");
        Some(parse_dimacs(&content).expect("parse DIMACS fixture"))
    }

    fn parse_required_xz_fixture(relative_path: &str) -> crate::DimacsFormula {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative_path);
        let content = String::from_utf8(crate::test_xz::decompress_required_xz_path(&path))
            .expect("required tracked fixture is UTF-8 DIMACS");
        parse_dimacs(&content).expect("parse required tracked DIMACS fixture")
    }

    #[test]
    fn source_clause_ingress_preserves_contiguous_dimacs_rows_without_routing() {
        let clauses = vec![
            vec![pos(0), neg(1), pos(2)],
            Vec::new(),
            vec![neg(3), neg(4)],
        ];

        let source = dense_clique_source_clauses_from_clauses(&clauses);

        assert_eq!(source.audit.clauses_seen, 3);
        assert_eq!(source.audit.source_rows, 3);
        assert_eq!(source.audit.raw_dimacs_literals, 5);
        assert_eq!(source.audit.empty_clause_rows, 1);
        assert_eq!(source.audit.first_source_id, Some(1));
        assert_eq!(source.audit.last_source_id, Some(3));
        assert_eq!(source.clauses[0].source_id, 1);
        assert_eq!(source.clauses[0].raw_dimacs, vec![1, -2, 3]);
        assert_eq!(source.clauses[1].source_id, 2);
        assert!(source.clauses[1].raw_dimacs.is_empty());
        assert_eq!(source.clauses[2].source_id, 3);
        assert_eq!(source.clauses[2].raw_dimacs, vec![-4, -5]);
        assert_eq!(source.clauses[2].literals, clauses[2]);
    }

    #[test]
    fn strict_global_mutex_fixture_recovers_structure_without_solving() {
        let clauses = strict_fixture(3, 4);
        let scout = DenseCliqueScout::scan(12, &clauses);

        assert!(scout.detected());
        assert_eq!(scout.rejection, DenseCliqueRejection::None);
        assert_eq!(scout.graph_vertices(), 4);
        assert_eq!(scout.colors(), 3);
        assert_eq!(scout.graph_edges(), 0);
        assert_eq!(scout.graph_non_edges(), 6);
        assert_eq!(scout.graph_non_edge_buckets(), 1);
        assert_eq!(scout.graph_non_edge_bucket_min(), 4);
        assert_eq!(scout.graph_non_edge_bucket_max(), 4);
        assert!(scout.complete_multipartite());
        assert_eq!(scout.php_pigeons(), 3);
        assert_eq!(scout.php_holes(), 1);
        assert!(scout.pigeonhole_unsat_obligation());
        assert_eq!(scout.negative_binary_mutexes, 66);
        assert_eq!(scout.expected_mutexes(), 66);
        assert_eq!(scout.positive_support_clauses, 3);
        assert_eq!(scout.support_width(), 4);
    }

    #[test]
    fn strict_fixture_scan_with_witness_preserves_source_ids() {
        let clauses = strict_fixture(3, 4);
        let source = source_clauses(&clauses);

        let witness = DenseCliqueScout::scan_with_witness(12, &source).unwrap();

        assert!(witness.scout.detected());
        assert_eq!(witness.support_rows.len(), 3);
        assert_eq!(witness.support_rows[0].source_id, 1);
        assert_eq!(witness.support_rows[1].source_id, 2);
        assert_eq!(witness.support_rows[2].source_id, 3);
        assert_eq!(witness.support_rows[0].raw_dimacs, vec![1, 2, 3, 4]);
        assert_eq!(witness.support_rows[0].variables, vec![0, 1, 2, 3]);
        assert_eq!(witness.mutexes.len(), 66);
        assert_eq!(witness.mutexes[0].source_id, 4);
        assert_eq!(witness.graph_pairs.len(), 6);
        assert!(witness.graph_pairs.iter().all(|pair| !pair.graph_edge));
        assert!(witness
            .graph_pairs
            .iter()
            .all(|pair| pair.cross_mutex_source_ids.len() == 6));
        assert_eq!(witness.php_obligation.pigeons, 3);
        assert_eq!(witness.php_obligation.holes, 1);
        assert_eq!(
            witness.php_obligation.bucket_vertices,
            vec![vec![0, 1, 2, 3]]
        );
        assert!(witness.php_obligation.unsat_obligation);
    }

    #[test]
    fn strict_fixture_builds_php_replay_ledger_source_only() {
        let clauses = strict_fixture(3, 4);
        let source = source_clauses(&clauses);
        let witness = DenseCliqueScout::scan_with_witness(12, &source).unwrap();

        let ledger = build_dense_clique_php_replay_ledger(&witness).unwrap();

        assert_eq!(ledger.original_vars, 12);
        assert_eq!(ledger.original_clauses, 69);
        assert_eq!(ledger.pigeons, 3);
        assert_eq!(ledger.holes, 1);
        assert_eq!(ledger.bucket_vertices, vec![vec![0, 1, 2, 3]]);
        assert_eq!(ledger.extension_var_start_one_based, 13);
        assert_eq!(ledger.extension_var_end_one_based, 15);
        assert_eq!(ledger.extension_clause_id_start, 70);
        assert_eq!(ledger.extension_clause_id_end, 78);
        assert_eq!(ledger.extension_clause_count(), 9);
        assert_eq!(ledger.bucket_alo_clause_id_start, 79);
        assert_eq!(ledger.bucket_alo_clause_id_end, 81);
        assert_eq!(ledger.bucket_mutex_clause_id_start, 82);
        assert_eq!(ledger.bucket_mutex_clause_id_end, 84);
        assert_eq!(ledger.extension_rows.len(), 3);
        assert_eq!(ledger.bucket_alo_rows.len(), 3);
        assert_eq!(ledger.bucket_mutex_rows.len(), 3);
        assert_eq!(ledger.bucket_alo_rows[0].source_support_id, 1);
        assert_eq!(ledger.bucket_alo_rows[0].extension_vars_one_based, vec![13]);
        assert_eq!(ledger.bucket_mutex_rows[0].source_mutex_ids.len(), 16);
    }

    #[test]
    fn scan_with_witness_rejects_duplicate_source_id() {
        let clauses = strict_fixture(2, 3);
        let mut source = source_clauses(&clauses);
        source[1].source_id = source[0].source_id;

        let rejection = DenseCliqueScout::scan_with_witness(6, &source).unwrap_err();

        assert_eq!(
            rejection,
            DenseCliqueWitnessReject::DuplicateSourceId { source_id: 1 }
        );
    }

    #[test]
    fn scan_with_witness_rejects_non_contiguous_source_id() {
        let clauses = strict_fixture(2, 3);
        let mut source = source_clauses(&clauses);
        source[1].source_id = 99;

        let rejection = DenseCliqueScout::scan_with_witness(6, &source).unwrap_err();

        assert_eq!(
            rejection,
            DenseCliqueWitnessReject::NonContiguousSourceId {
                expected: 2,
                actual: 3
            }
        );
    }

    #[test]
    fn scan_with_witness_rejects_raw_dimacs_mismatch() {
        let clauses = strict_fixture(2, 3);
        let mut source = source_clauses(&clauses);
        source[0].raw_dimacs[0] = -source[0].raw_dimacs[0];

        let rejection = DenseCliqueScout::scan_with_witness(6, &source).unwrap_err();

        assert_eq!(
            rejection,
            DenseCliqueWitnessReject::RawDimacsMismatch {
                source_id: 1,
                expected: vec![1, 2, 3],
                actual: vec![-1, 2, 3],
            }
        );
    }

    #[test]
    fn incomplete_mutex_graph_rejects_fail_closed() {
        let mut clauses = strict_fixture(2, 3);
        clauses.pop();

        let scout = DenseCliqueScout::scan(6, &clauses);

        assert!(!scout.detected());
        assert_eq!(scout.rejection, DenseCliqueRejection::IncompleteMutexGraph);
        assert_eq!(scout.negative_binary_mutexes, 14);
    }

    #[test]
    fn mixed_clause_rejects_fail_closed() {
        let mut clauses = strict_fixture(2, 3);
        clauses.push(vec![pos(0), neg(4)]);

        let scout = DenseCliqueScout::scan(6, &clauses);

        assert!(!scout.detected());
        assert_eq!(
            scout.rejection,
            DenseCliqueRejection::NonSupportOrMutexClauses
        );
    }

    #[test]
    fn clique_n2_k10_xz_fixture_recovers_scoreboard_row_structure() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz",
        ) else {
            return;
        };

        let scout = DenseCliqueScout::scan(formula.num_vars, &formula.clauses);

        assert!(scout.detected());
        assert_eq!(scout.num_vars, 180);
        assert_eq!(scout.num_clauses, 3_160);
        assert_eq!(scout.graph_vertices(), 18);
        assert_eq!(scout.colors(), 10);
        assert_eq!(scout.graph_edges(), 144);
        assert_eq!(scout.graph_non_edges(), 9);
        assert_eq!(scout.graph_non_edge_buckets(), 9);
        assert_eq!(scout.graph_non_edge_bucket_min(), 2);
        assert_eq!(scout.graph_non_edge_bucket_max(), 2);
        assert!(scout.complete_multipartite());
        assert_eq!(scout.php_pigeons(), 10);
        assert_eq!(scout.php_holes(), 9);
        assert!(scout.pigeonhole_unsat_obligation());
        assert_eq!(scout.positive_support_clauses, 10);
        assert_eq!(scout.negative_binary_mutexes, 3_150);
        assert_eq!(scout.expected_mutexes(), 3_150);
        assert_eq!(scout.other_clauses, 0);
    }

    #[test]
    fn clique_n2_k10_xz_fixture_scan_with_witness_recovers_php_obligation() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz",
        ) else {
            return;
        };
        let source = source_clauses(&formula.clauses);

        let witness = DenseCliqueScout::scan_with_witness(formula.num_vars, &source).unwrap();

        assert_eq!(witness.support_rows.len(), 10);
        assert_eq!(witness.support_rows[0].source_id, 1);
        assert_eq!(witness.support_rows[9].source_id, 10);
        assert_eq!(witness.mutexes.len(), 3_150);
        assert_eq!(witness.graph_pairs.len(), 153);
        assert_eq!(
            witness
                .graph_pairs
                .iter()
                .filter(|pair| pair.graph_edge)
                .count(),
            144
        );
        assert_eq!(
            witness
                .graph_pairs
                .iter()
                .filter(|pair| !pair.graph_edge)
                .count(),
            9
        );
        assert!(witness
            .graph_pairs
            .iter()
            .filter(|pair| !pair.graph_edge)
            .all(|pair| pair.cross_mutex_source_ids.len() == 90));
        assert_eq!(witness.php_obligation.pigeons, 10);
        assert_eq!(witness.php_obligation.holes, 9);
        assert_eq!(witness.php_obligation.bucket_vertices.len(), 9);
        assert!(witness
            .php_obligation
            .bucket_vertices
            .iter()
            .all(|bucket| bucket.len() == 2));
        assert!(witness.php_obligation.unsat_obligation);
    }

    #[test]
    fn clique_n2_k10_xz_fixture_witness_builds_php_replay_ledger() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz",
        ) else {
            return;
        };
        let source = source_clauses(&formula.clauses);
        let witness = DenseCliqueScout::scan_with_witness(formula.num_vars, &source).unwrap();

        let ledger = build_dense_clique_php_replay_ledger(&witness).unwrap();

        assert_eq!(
            ledger.bucket_vertices,
            vec![
                vec![0, 1],
                vec![2, 3],
                vec![4, 5],
                vec![6, 7],
                vec![8, 9],
                vec![10, 11],
                vec![12, 13],
                vec![14, 15],
                vec![16, 17],
            ]
        );
        assert_eq!(ledger.original_vars, 180);
        assert_eq!(ledger.original_clauses, 3_160);
        assert_eq!(ledger.pigeons, 10);
        assert_eq!(ledger.holes, 9);
        assert_eq!(ledger.extension_var_start_one_based, 181);
        assert_eq!(ledger.extension_var_end_one_based, 270);
        assert_eq!(ledger.extension_clause_id_start, 3_161);
        assert_eq!(ledger.extension_clause_id_end, 3_430);
        assert_eq!(ledger.extension_clause_count(), 270);
        assert_eq!(ledger.bucket_alo_clause_id_start, 3_431);
        assert_eq!(ledger.bucket_alo_clause_id_end, 3_440);
        assert_eq!(ledger.bucket_mutex_clause_id_start, 3_441);
        assert_eq!(ledger.bucket_mutex_clause_id_end, 3_845);
        assert_eq!(ledger.extension_rows.len(), 90);
        assert_eq!(ledger.bucket_alo_rows.len(), 10);
        assert_eq!(ledger.bucket_mutex_rows.len(), 405);
        assert_eq!(
            ledger.bucket_mutex_rows[0].source_mutex_ids,
            vec![1541, 1586, 2351, 2352]
        );
        assert_eq!(
            ledger.bucket_mutex_rows.last().unwrap().source_mutex_ids,
            vec![2305, 2350, 3159, 3160]
        );
    }

    #[test]
    fn strict_fixture_builds_result_silent_php_replay_packet() {
        let clauses = strict_fixture(3, 4);

        let packet = build_dense_clique_php_replay_packet_from_clauses(12, &clauses).unwrap();

        assert!(packet.authority_is_absent());
        assert_eq!(packet.source_audit.clauses_seen, 69);
        assert_eq!(packet.source_audit.source_rows, 69);
        assert_eq!(packet.source_audit.raw_dimacs_literals, 144);
        assert_eq!(packet.source_audit.empty_clause_rows, 0);
        assert_eq!(packet.source_audit.first_source_id, Some(1));
        assert_eq!(packet.source_audit.last_source_id, Some(69));
        assert_eq!(packet.witness.php_obligation.pigeons, 3);
        assert_eq!(packet.witness.php_obligation.holes, 1);
        assert!(packet.witness.php_obligation.unsat_obligation);
        assert_eq!(packet.replay_ledger.original_vars, 12);
        assert_eq!(packet.replay_ledger.original_clauses, 69);
        assert_eq!(packet.replay_ledger.extension_rows.len(), 3);
        assert_eq!(packet.replay_ledger.bucket_alo_rows.len(), 3);
        assert_eq!(packet.replay_ledger.bucket_mutex_rows.len(), 3);
        assert!(!packet.route_admitted);
        assert!(!packet.result_authority);
        assert!(!packet.unsat_output_authority);
        assert!(!packet.proof_output_authority);
        assert!(!packet.model_output_authority);
    }

    #[test]
    fn checker_audit_materializer_is_default_off() {
        let clauses = strict_fixture(3, 2);
        let packet = build_dense_clique_php_replay_packet_from_clauses(6, &clauses).unwrap();

        let audit =
            materialize_dense_clique_php_checker_audit(Default::default(), &packet).unwrap();

        assert!(audit.rows.is_empty());
        assert!(audit.authority_is_absent());
        assert!(!audit.stats.enabled);
        assert_eq!(audit.stats.source_rows_audited, 18);
        assert_eq!(audit.stats.extension_rows_seen, 3);
        assert_eq!(audit.stats.checker_rows_materialized, 0);
        assert_eq!(audit.stats.external_checker_verified_rows, 0);
    }

    #[test]
    fn pair_bucket_fixture_materializes_checker_visible_rows_without_authority() {
        let clauses = strict_fixture(3, 2);
        let packet = build_dense_clique_php_replay_packet_from_clauses(6, &clauses).unwrap();

        let audit = materialize_dense_clique_php_checker_audit(
            DenseCliquePhpCheckerAuditConfig { enabled: true },
            &packet,
        )
        .unwrap();

        assert!(audit.authority_is_absent());
        assert_eq!(audit.rows.len(), 15);
        assert_eq!(audit.stats.source_rows_audited, 18);
        assert_eq!(audit.stats.checker_rows_materialized, 15);
        assert_eq!(audit.stats.extension_definition_rows_materialized, 9);
        assert_eq!(audit.stats.bucket_alo_rows_materialized, 3);
        assert_eq!(audit.stats.bucket_mutex_rows_materialized, 3);
        assert_eq!(audit.stats.source_dependency_edges, 15);
        assert_eq!(audit.stats.dependency_clause_edges, 12);
        assert_eq!(audit.stats.external_checker_verified_rows, 0);

        assert_eq!(
            audit.rows[0],
            DenseCliquePhpCheckerVisibleRow {
                row_kind: DenseCliquePhpCheckerVisibleRowKind::ExtensionForward,
                checker_visible_id: 19,
                clause_lits_dimacs: vec![-1, 7],
                source_rows: Vec::new(),
                dependency_clause_ids: Vec::new(),
                external_checker_verified: false,
            }
        );
        assert_eq!(
            audit.rows[2],
            DenseCliquePhpCheckerVisibleRow {
                row_kind: DenseCliquePhpCheckerVisibleRowKind::ExtensionBackward,
                checker_visible_id: 21,
                clause_lits_dimacs: vec![1, 2, -7],
                source_rows: Vec::new(),
                dependency_clause_ids: Vec::new(),
                external_checker_verified: false,
            }
        );
        assert_eq!(
            audit.rows[9].row_kind,
            DenseCliquePhpCheckerVisibleRowKind::BucketAlo
        );
        assert_eq!(audit.rows[9].checker_visible_id, 28);
        assert_eq!(audit.rows[9].clause_lits_dimacs, vec![7]);
        assert_eq!(audit.rows[9].source_rows[0].source_id, 1);
        assert_eq!(audit.rows[9].source_rows[0].raw_dimacs, vec![1, 2]);
        assert_eq!(audit.rows[9].dependency_clause_ids, vec![19, 20]);
        assert_eq!(
            audit.rows[12].row_kind,
            DenseCliquePhpCheckerVisibleRowKind::BucketMutex
        );
        assert_eq!(audit.rows[12].checker_visible_id, 31);
        assert_eq!(audit.rows[12].clause_lits_dimacs, vec![-7, -8]);
        assert_eq!(
            audit.rows[12]
                .source_rows
                .iter()
                .map(|row| row.source_id)
                .collect::<Vec<_>>(),
            vec![5, 6, 9, 10]
        );
        assert_eq!(audit.rows[12].dependency_clause_ids, vec![21, 24]);
    }

    #[test]
    fn checker_audit_rejects_non_pair_bucket_extension_schedule() {
        let clauses = strict_fixture(3, 4);
        let packet = build_dense_clique_php_replay_packet_from_clauses(12, &clauses).unwrap();

        let reject = materialize_dense_clique_php_checker_audit(
            DenseCliquePhpCheckerAuditConfig { enabled: true },
            &packet,
        )
        .unwrap_err();

        assert_eq!(
            reject,
            DenseCliquePhpCheckerAuditReject::UnsupportedBucketArity {
                bucket: 0,
                arity: 4,
            }
        );
    }

    #[test]
    fn checker_audit_rejects_replay_packet_authority_injection() {
        let clauses = strict_fixture(3, 2);
        let mut packet = build_dense_clique_php_replay_packet_from_clauses(6, &clauses).unwrap();
        packet.proof_output_authority = true;

        let reject = materialize_dense_clique_php_checker_audit(
            DenseCliquePhpCheckerAuditConfig { enabled: true },
            &packet,
        )
        .unwrap_err();

        assert_eq!(
            reject,
            DenseCliquePhpCheckerAuditReject::PacketAuthorityPresent
        );
    }

    #[test]
    fn original_drat_materializer_is_default_off_without_authority() {
        let clauses = strict_fixture(3, 2);
        let packet = build_dense_clique_php_replay_packet_from_clauses(6, &clauses).unwrap();

        let materialization = materialize_dense_clique_php_original_drat_from_compact_proof(
            Default::default(),
            &packet,
            "0\n",
        )
        .unwrap();

        assert!(materialization.drat.is_empty());
        assert!(materialization.authority_is_absent());
        assert!(!materialization.stats.enabled);
        assert_eq!(materialization.stats.source_rows_audited, 18);
        assert_eq!(materialization.stats.compact_variables, 3);
        assert_eq!(materialization.stats.compact_clauses, 6);
        assert_eq!(materialization.stats.extension_clauses_added, 0);
        assert_eq!(materialization.stats.external_checker_verified, 0);
    }

    #[test]
    fn pair_bucket_fixture_materializes_original_drat_from_compact_proof() {
        let clauses = strict_fixture(3, 2);
        let packet = build_dense_clique_php_replay_packet_from_clauses(6, &clauses).unwrap();

        let materialization = materialize_dense_clique_php_original_drat_from_compact_proof(
            DenseCliquePhpOriginalDratMaterializerConfig { enabled: true },
            &packet,
            "c compact proof\n1 -2 0\nd -1 0\n0\n",
        )
        .unwrap();

        assert!(materialization.authority_is_absent());
        assert_eq!(materialization.stats.source_rows_audited, 18);
        assert_eq!(materialization.stats.compact_variables, 3);
        assert_eq!(materialization.stats.compact_clauses, 6);
        assert_eq!(materialization.stats.extension_clauses_added, 9);
        assert_eq!(materialization.stats.bucket_alo_clauses_added, 3);
        assert_eq!(materialization.stats.bucket_mutex_clauses_added, 3);
        assert_eq!(materialization.stats.planned_bucket_clauses_added, 6);
        assert_eq!(materialization.stats.bucket_mutex_support_clauses_added, 6);
        assert_eq!(materialization.stats.compact_proof_lines_seen, 3);
        assert_eq!(materialization.stats.compact_proof_comments_skipped, 1);
        assert_eq!(materialization.stats.compact_proof_additions_remapped, 2);
        assert_eq!(materialization.stats.compact_proof_deletions_remapped, 1);
        assert_eq!(materialization.stats.compact_proof_max_var, 2);
        assert_eq!(materialization.stats.original_proof_max_var, 9);

        let rows = materialization.drat.lines().collect::<Vec<_>>();
        assert_eq!(&rows[0..3], &["-1 7 0", "-2 7 0", "1 2 -7 0"]);
        assert_eq!(&rows[9..12], &["7 0", "8 0", "9 0"]);
        assert_eq!(
            &rows[12..21],
            &[
                "-8 -1 0", "-8 -2 0", "-7 -8 0", "-9 -1 0", "-9 -2 0", "-7 -9 0", "-9 -3 0",
                "-9 -4 0", "-8 -9 0"
            ]
        );
        assert_eq!(&rows[21..24], &["7 -8 0", "d -7 0", "0"]);
    }

    #[test]
    fn original_drat_materializer_rejects_non_pair_bucket_schedule() {
        let clauses = strict_fixture(3, 4);
        let packet = build_dense_clique_php_replay_packet_from_clauses(12, &clauses).unwrap();

        let reject = materialize_dense_clique_php_original_drat_from_compact_proof(
            DenseCliquePhpOriginalDratMaterializerConfig { enabled: true },
            &packet,
            "0\n",
        )
        .unwrap_err();

        assert_eq!(
            reject,
            DenseCliquePhpOriginalDratMaterializationReject::CheckerAudit(
                DenseCliquePhpCheckerAuditReject::UnsupportedBucketArity {
                    bucket: 0,
                    arity: 4,
                }
            )
        );
    }

    #[test]
    fn original_drat_materializer_rejects_malformed_compact_proof() {
        let clauses = strict_fixture(3, 2);
        let packet = build_dense_clique_php_replay_packet_from_clauses(6, &clauses).unwrap();

        let reject = materialize_dense_clique_php_original_drat_from_compact_proof(
            DenseCliquePhpOriginalDratMaterializerConfig { enabled: true },
            &packet,
            "1 -2\n",
        )
        .unwrap_err();

        assert_eq!(
            reject,
            DenseCliquePhpOriginalDratMaterializationReject::CompactProofMissingTerminator {
                line_number: 1
            }
        );
    }

    #[test]
    fn original_lrat_materializer_is_default_off_without_authority() {
        let clauses = strict_fixture(3, 2);
        let packet = build_dense_clique_php_replay_packet_from_clauses(6, &clauses).unwrap();

        let materialization = materialize_dense_clique_php_original_lrat_from_compact_proof(
            Default::default(),
            &packet,
            "7 -2 0 1 4 0\n8 0 2 7 0\n",
        )
        .unwrap();

        assert!(materialization.lrat.is_empty());
        assert!(materialization.authority_is_absent());
        assert!(!materialization.stats.enabled);
        assert_eq!(materialization.stats.source_rows_audited, 18);
        assert_eq!(materialization.stats.compact_variables, 3);
        assert_eq!(materialization.stats.compact_clauses, 6);
        assert_eq!(materialization.stats.extension_clauses_added, 0);
        assert_eq!(materialization.stats.external_checker_verified, 0);
    }

    #[test]
    fn pair_bucket_fixture_materializes_original_lrat_from_compact_proof() {
        let clauses = strict_fixture(3, 2);
        let packet = build_dense_clique_php_replay_packet_from_clauses(6, &clauses).unwrap();

        let materialization = materialize_dense_clique_php_original_lrat_from_compact_proof(
            DenseCliquePhpOriginalLratMaterializerConfig { enabled: true },
            &packet,
            "c compact LRAT\n7 -2 0 1 4 0\n8 0 2 7 0\n",
        )
        .unwrap();

        assert!(materialization.authority_is_absent());
        assert_eq!(materialization.stats.source_rows_audited, 18);
        assert_eq!(materialization.stats.compact_variables, 3);
        assert_eq!(materialization.stats.compact_clauses, 6);
        assert_eq!(materialization.stats.extension_clauses_added, 9);
        assert_eq!(materialization.stats.bucket_alo_clauses_added, 3);
        assert_eq!(materialization.stats.bucket_mutex_clauses_added, 3);
        assert_eq!(materialization.stats.planned_bucket_clauses_added, 6);
        assert_eq!(materialization.stats.bucket_mutex_support_clauses_added, 6);
        assert_eq!(materialization.stats.compact_lrat_lines_seen, 2);
        assert_eq!(materialization.stats.compact_lrat_comments_skipped, 1);
        assert_eq!(materialization.stats.compact_lrat_additions_remapped, 2);
        assert_eq!(materialization.stats.compact_lrat_deletions_remapped, 0);
        assert_eq!(materialization.stats.compact_lrat_max_var, 2);
        assert_eq!(materialization.stats.compact_lrat_max_id, 8);
        assert_eq!(materialization.stats.compact_lrat_derived_id_offset, 33);
        assert_eq!(materialization.stats.original_lrat_max_var, 9);
        assert_eq!(materialization.stats.original_lrat_max_id, 41);

        let rows = materialization.lrat.lines().collect::<Vec<_>>();
        assert_eq!(
            &rows[0..3],
            &["19 7 -1 0 0", "20 7 -2 0 0", "21 -7 1 2 0 -19 -20 0"]
        );
        assert_eq!(
            &rows[9..12],
            &["28 7 0 19 20 1 0", "29 8 0 22 23 2 0", "30 9 0 25 26 3 0",]
        );
        assert_eq!(
            &rows[12..21],
            &[
                "31 -8 -1 0 5 24 6 0",
                "32 -8 -2 0 9 24 10 0",
                "33 -7 -8 0 32 21 31 0",
                "34 -9 -1 0 7 27 8 0",
                "35 -9 -2 0 11 27 12 0",
                "36 -7 -9 0 35 21 34 0",
                "37 -9 -3 0 14 27 15 0",
                "38 -9 -4 0 16 27 17 0",
                "39 -8 -9 0 38 24 37 0",
            ]
        );
        assert_eq!(&rows[21..23], &["40 -8 0 28 33 0", "41 0 29 40 0"]);
    }

    #[test]
    fn original_lrat_materializer_maps_compact_mutex_hints_from_pair_major_order() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz",
        ) else {
            return;
        };
        let packet =
            build_dense_clique_php_replay_packet_from_clauses(formula.num_vars, &formula.clauses)
                .unwrap();

        let compact_mutex_idx = 92 - packet.replay_ledger.bucket_alo_rows.len() - 1;
        let ledger_idx = compact_pair_major_mutex_index_to_ledger_index(
            &packet.replay_ledger,
            compact_mutex_idx,
        )
        .unwrap();
        let row = &packet.replay_ledger.bucket_mutex_rows[ledger_idx];
        assert_eq!(
            (ledger_idx, row.bucket, row.lhs_pigeon, row.rhs_pigeon),
            (9, 0, 1, 2),
            "compact mutex id 92 is pair-major (p1,p2,b0), not ledger bucket-major index 81"
        );
    }

    #[test]
    fn original_lrat_materializer_rejects_non_pair_bucket_schedule() {
        let clauses = strict_fixture(3, 4);
        let packet = build_dense_clique_php_replay_packet_from_clauses(12, &clauses).unwrap();

        let reject = materialize_dense_clique_php_original_lrat_from_compact_proof(
            DenseCliquePhpOriginalLratMaterializerConfig { enabled: true },
            &packet,
            "7 -2 0 1 4 0\n",
        )
        .unwrap_err();

        assert_eq!(
            reject,
            DenseCliquePhpOriginalLratMaterializationReject::CheckerAudit(
                DenseCliquePhpCheckerAuditReject::UnsupportedBucketArity {
                    bucket: 0,
                    arity: 4,
                }
            )
        );
    }

    #[test]
    fn original_lrat_materializer_rejects_malformed_compact_proof() {
        let clauses = strict_fixture(3, 2);
        let packet = build_dense_clique_php_replay_packet_from_clauses(6, &clauses).unwrap();

        let reject = materialize_dense_clique_php_original_lrat_from_compact_proof(
            DenseCliquePhpOriginalLratMaterializerConfig { enabled: true },
            &packet,
            "7 -2 0 1 4\n",
        )
        .unwrap_err();

        assert_eq!(
            reject,
            DenseCliquePhpOriginalLratMaterializationReject::CompactLratMissingHintTerminator {
                line_number: 1
            }
        );
    }

    #[test]
    fn clique_n2_k10_xz_fixture_builds_result_silent_php_replay_packet() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz",
        ) else {
            return;
        };

        let packet =
            build_dense_clique_php_replay_packet_from_clauses(formula.num_vars, &formula.clauses)
                .unwrap();

        assert!(packet.authority_is_absent());
        assert_eq!(packet.source_audit.clauses_seen, 3_160);
        assert_eq!(packet.source_audit.source_rows, 3_160);
        assert_eq!(packet.source_audit.raw_dimacs_literals, 6_480);
        assert_eq!(packet.source_audit.first_source_id, Some(1));
        assert_eq!(packet.source_audit.last_source_id, Some(3_160));
        assert_eq!(packet.witness.support_rows.len(), 10);
        assert_eq!(packet.witness.mutexes.len(), 3_150);
        assert_eq!(packet.witness.php_obligation.pigeons, 10);
        assert_eq!(packet.witness.php_obligation.holes, 9);
        assert!(packet.witness.php_obligation.unsat_obligation);
        assert_eq!(packet.replay_ledger.extension_rows.len(), 90);
        assert_eq!(packet.replay_ledger.bucket_alo_rows.len(), 10);
        assert_eq!(packet.replay_ledger.bucket_mutex_rows.len(), 405);
        assert_eq!(packet.replay_ledger.bucket_mutex_clause_id_end, 3_845);
        assert!(!packet.route_admitted);
        assert!(!packet.result_authority);
        assert!(!packet.proof_output_authority);
    }

    #[test]
    fn clique_n2_k10_xz_fixture_materializes_checker_visible_audit_rows() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz",
        ) else {
            return;
        };
        let packet =
            build_dense_clique_php_replay_packet_from_clauses(formula.num_vars, &formula.clauses)
                .unwrap();

        let audit = materialize_dense_clique_php_checker_audit(
            DenseCliquePhpCheckerAuditConfig { enabled: true },
            &packet,
        )
        .unwrap();

        assert!(audit.authority_is_absent());
        assert_eq!(audit.rows.len(), 685);
        assert_eq!(audit.stats.source_rows_audited, 3_160);
        assert_eq!(audit.stats.extension_rows_seen, 90);
        assert_eq!(audit.stats.bucket_alo_rows_seen, 10);
        assert_eq!(audit.stats.bucket_mutex_rows_seen, 405);
        assert_eq!(audit.stats.extension_definition_rows_materialized, 270);
        assert_eq!(audit.stats.bucket_alo_rows_materialized, 10);
        assert_eq!(audit.stats.bucket_mutex_rows_materialized, 405);
        assert_eq!(audit.stats.source_dependency_edges, 1_630);
        assert_eq!(audit.stats.dependency_clause_edges, 990);
        assert_eq!(audit.stats.external_checker_verified_rows, 0);

        assert_eq!(
            audit.rows[0],
            DenseCliquePhpCheckerVisibleRow {
                row_kind: DenseCliquePhpCheckerVisibleRowKind::ExtensionForward,
                checker_visible_id: 3_161,
                clause_lits_dimacs: vec![-1, 181],
                source_rows: Vec::new(),
                dependency_clause_ids: Vec::new(),
                external_checker_verified: false,
            }
        );
        assert_eq!(
            audit.rows[2],
            DenseCliquePhpCheckerVisibleRow {
                row_kind: DenseCliquePhpCheckerVisibleRowKind::ExtensionBackward,
                checker_visible_id: 3_163,
                clause_lits_dimacs: vec![1, 2, -181],
                source_rows: Vec::new(),
                dependency_clause_ids: Vec::new(),
                external_checker_verified: false,
            }
        );

        let first_alo = &audit.rows[270];
        assert_eq!(
            first_alo.row_kind,
            DenseCliquePhpCheckerVisibleRowKind::BucketAlo
        );
        assert_eq!(first_alo.checker_visible_id, 3_431);
        assert_eq!(
            first_alo.clause_lits_dimacs,
            vec![181, 182, 183, 184, 185, 186, 187, 188, 189]
        );
        assert_eq!(first_alo.source_rows[0].source_id, 1);
        assert_eq!(
            first_alo.source_rows[0].raw_dimacs,
            (1..=18).collect::<Vec<_>>()
        );
        assert_eq!(first_alo.dependency_clause_ids.len(), 18);
        assert_eq!(&first_alo.dependency_clause_ids[0..2], &[3_161, 3_162]);
        assert_eq!(&first_alo.dependency_clause_ids[16..18], &[3_185, 3_186]);

        let first_mutex = &audit.rows[280];
        assert_eq!(
            first_mutex.row_kind,
            DenseCliquePhpCheckerVisibleRowKind::BucketMutex
        );
        assert_eq!(first_mutex.checker_visible_id, 3_441);
        assert_eq!(first_mutex.clause_lits_dimacs, vec![-181, -190]);
        assert_eq!(
            first_mutex
                .source_rows
                .iter()
                .map(|row| row.source_id)
                .collect::<Vec<_>>(),
            vec![1541, 1586, 2351, 2352]
        );
        assert_eq!(first_mutex.dependency_clause_ids, vec![3_163, 3_190]);

        let last = audit.rows.last().unwrap();
        assert_eq!(
            last.row_kind,
            DenseCliquePhpCheckerVisibleRowKind::BucketMutex
        );
        assert_eq!(last.checker_visible_id, 3_845);
        assert_eq!(last.clause_lits_dimacs, vec![-261, -270]);
        assert_eq!(
            last.source_rows
                .iter()
                .map(|row| row.source_id)
                .collect::<Vec<_>>(),
            vec![2305, 2350, 3159, 3160]
        );
        assert_eq!(last.dependency_clause_ids, vec![3_403, 3_430]);
    }

    #[test]
    fn clique_n2_k10_xz_fixture_materializes_original_drat_schedule() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz",
        ) else {
            return;
        };
        let packet =
            build_dense_clique_php_replay_packet_from_clauses(formula.num_vars, &formula.clauses)
                .unwrap();
        let compact_drat_path = env::var("AY_DENSE_CLIQUE_COMPACT_DRAT_PROOF").ok();
        let compact_drat = compact_drat_path
            .as_ref()
            .map(|path| fs::read_to_string(path).expect("read compact dense-clique DRAT proof"))
            .unwrap_or_else(|| "0\n".to_string());

        let materialization = materialize_dense_clique_php_original_drat_from_compact_proof(
            DenseCliquePhpOriginalDratMaterializerConfig { enabled: true },
            &packet,
            &compact_drat,
        )
        .unwrap();

        assert!(materialization.authority_is_absent());
        assert_eq!(materialization.stats.source_rows_audited, 3_160);
        assert_eq!(materialization.stats.compact_variables, 90);
        assert_eq!(materialization.stats.compact_clauses, 415);
        assert_eq!(materialization.stats.extension_clauses_added, 270);
        assert_eq!(materialization.stats.bucket_alo_clauses_added, 10);
        assert_eq!(materialization.stats.bucket_mutex_clauses_added, 405);
        assert_eq!(materialization.stats.planned_bucket_clauses_added, 415);
        assert_eq!(
            materialization.stats.bucket_mutex_support_clauses_added,
            810
        );
        assert_eq!(materialization.stats.external_checker_verified, 0);
        assert!(materialization
            .drat
            .starts_with("-1 181 0\n-2 181 0\n1 2 -181 0\n-3 182 0\n"));

        if compact_drat_path.is_none() {
            assert_eq!(materialization.stats.compact_proof_lines_seen, 1);
            assert_eq!(materialization.stats.compact_proof_additions_remapped, 1);
            assert_eq!(materialization.stats.compact_proof_deletions_remapped, 0);
            assert_eq!(materialization.stats.compact_proof_max_var, 0);
            assert_eq!(materialization.stats.original_proof_max_var, 270);
        }

        if let Ok(out_path) = env::var("AY_DENSE_CLIQUE_ORIGINAL_DRAT_OUT") {
            let out_path = Path::new(&out_path);
            assert!(
                out_path.starts_with("/tmp"),
                "proof sidecar output must stay under /tmp: {}",
                out_path.display()
            );
            if let Some(parent) = out_path.parent() {
                fs::create_dir_all(parent).expect("create dense-clique proof sidecar parent");
            }
            fs::write(out_path, materialization.drat).expect("write dense-clique proof sidecar");
        }
    }

    #[test]
    fn clique_n2_k10_xz_fixture_materializes_original_lrat_schedule() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz",
        ) else {
            return;
        };
        let packet =
            build_dense_clique_php_replay_packet_from_clauses(formula.num_vars, &formula.clauses)
                .unwrap();
        let compact_lrat_path = env::var("AY_DENSE_CLIQUE_COMPACT_LRAT_PROOF").ok();
        let compact_lrat = compact_lrat_path
            .as_ref()
            .map(|path| fs::read_to_string(path).expect("read compact dense-clique LRAT proof"))
            .unwrap_or_else(|| "416 0 0\n".to_string());

        let materialization = materialize_dense_clique_php_original_lrat_from_compact_proof(
            DenseCliquePhpOriginalLratMaterializerConfig { enabled: true },
            &packet,
            &compact_lrat,
        )
        .unwrap();

        assert!(materialization.authority_is_absent());
        assert_eq!(materialization.stats.source_rows_audited, 3_160);
        assert_eq!(materialization.stats.compact_variables, 90);
        assert_eq!(materialization.stats.compact_clauses, 415);
        assert_eq!(materialization.stats.extension_clauses_added, 270);
        assert_eq!(materialization.stats.bucket_alo_clauses_added, 10);
        assert_eq!(materialization.stats.bucket_mutex_clauses_added, 405);
        assert_eq!(materialization.stats.planned_bucket_clauses_added, 415);
        assert_eq!(
            materialization.stats.bucket_mutex_support_clauses_added,
            810
        );
        assert_eq!(materialization.stats.external_checker_verified, 0);
        assert!(materialization
            .lrat
            .starts_with("3161 181 -1 0 0\n3162 181 -2 0 0\n3163 -181 1 2 0 -3161 -3162 0\n"));

        if compact_lrat_path.is_none() {
            assert_eq!(materialization.stats.compact_lrat_lines_seen, 1);
            assert_eq!(materialization.stats.compact_lrat_additions_remapped, 1);
            assert_eq!(materialization.stats.compact_lrat_deletions_remapped, 0);
            assert_eq!(materialization.stats.compact_lrat_max_var, 0);
            assert_eq!(materialization.stats.compact_lrat_max_id, 416);
            assert_eq!(materialization.stats.compact_lrat_derived_id_offset, 4_240);
            assert_eq!(materialization.stats.original_lrat_max_var, 270);
            assert_eq!(materialization.stats.original_lrat_max_id, 4_656);
        }

        if let Ok(out_path) = env::var("AY_DENSE_CLIQUE_ORIGINAL_LRAT_OUT") {
            let out_path = Path::new(&out_path);
            assert!(
                out_path.starts_with("/tmp"),
                "proof sidecar output must stay under /tmp: {}",
                out_path.display()
            );
            if let Some(parent) = out_path.parent() {
                fs::create_dir_all(parent).expect("create dense-clique proof sidecar parent");
            }
            fs::write(out_path, materialization.lrat).expect("write dense-clique proof sidecar");
        }
    }

    #[test]
    fn php_replay_packet_rejects_circuit_and_fmla_controls_without_authority() {
        let circuit = parse_required_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             c5ae0ec49de0959cd14431ce851c14f8-Circuit_multiplier22.cnf.xz",
        );
        let circuit_rejection =
            build_dense_clique_php_replay_packet_from_clauses(circuit.num_vars, &circuit.clauses)
                .unwrap_err();
        assert!(matches!(
            circuit_rejection,
            DenseCliquePhpReplayPacketReject::Witness(DenseCliqueWitnessReject::Scout(_))
        ));

        let Some(fmla) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.xz",
        ) else {
            return;
        };
        let fmla_rejection =
            build_dense_clique_php_replay_packet_from_clauses(fmla.num_vars, &fmla.clauses)
                .unwrap_err();
        assert_eq!(
            fmla_rejection,
            DenseCliquePhpReplayPacketReject::Witness(DenseCliqueWitnessReject::Scout(
                DenseCliqueRejection::TooManyVariables
            ))
        );
    }

    #[test]
    fn circuit_multiplier22_xz_fixture_does_not_enter_route() {
        let formula = parse_required_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             c5ae0ec49de0959cd14431ce851c14f8-Circuit_multiplier22.cnf.xz",
        );

        let scout = DenseCliqueScout::scan(formula.num_vars, &formula.clauses);

        assert!(!scout.detected());
        assert_ne!(scout.rejection, DenseCliqueRejection::None);
    }

    #[test]
    fn circuit_multiplier22_xz_fixture_scan_with_witness_rejects() {
        let formula = parse_required_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             c5ae0ec49de0959cd14431ce851c14f8-Circuit_multiplier22.cnf.xz",
        );
        let source = source_clauses(&formula.clauses);

        let rejection = DenseCliqueScout::scan_with_witness(formula.num_vars, &source).unwrap_err();

        assert!(matches!(
            rejection,
            DenseCliqueWitnessReject::Scout(DenseCliqueRejection::NoPositiveSupportClauses)
                | DenseCliqueWitnessReject::Scout(DenseCliqueRejection::NonSupportOrMutexClauses)
                | DenseCliqueWitnessReject::Scout(DenseCliqueRejection::NonUniformSupportWidth)
                | DenseCliqueWitnessReject::Scout(DenseCliqueRejection::OverlappingSupportRows)
                | DenseCliqueWitnessReject::Scout(
                    DenseCliqueRejection::SupportDoesNotCoverAllVariables
                )
                | DenseCliqueWitnessReject::Scout(DenseCliqueRejection::IncompleteMutexGraph)
                | DenseCliqueWitnessReject::Scout(DenseCliqueRejection::InconsistentGraphMutexes)
        ));
    }

    #[test]
    fn fmla_equiv_chain_xz_fixture_does_not_enter_route() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.xz",
        ) else {
            return;
        };

        let scout = DenseCliqueScout::scan(formula.num_vars, &formula.clauses);

        assert!(!scout.detected());
        assert_eq!(scout.rejection, DenseCliqueRejection::TooManyVariables);
    }

    #[test]
    fn fmla_equiv_chain_xz_fixture_scan_with_witness_rejects_too_large() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.xz",
        ) else {
            return;
        };
        let source = source_clauses(&formula.clauses);

        let rejection = DenseCliqueScout::scan_with_witness(formula.num_vars, &source).unwrap_err();

        assert_eq!(
            rejection,
            DenseCliqueWitnessReject::Scout(DenseCliqueRejection::TooManyVariables)
        );
    }
}
