// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn dimacs_source_text_for_scout(source: DimacsInputSource<'_>) -> Option<String> {
    match source {
        DimacsInputSource::Content(content) => Some(content.to_string()),
        DimacsInputSource::FilePath { path, sha256 } => {
            read_authenticated_dimacs_source(path, sha256).ok()
        }
        DimacsInputSource::Unavailable => None,
    }
}

fn fnv1a_feed_u64(hash: &mut u64, value: u64) {
    for byte in value.to_le_bytes() {
        *hash ^= u64::from(byte);
        *hash = hash.wrapping_mul(1_099_511_628_211);
    }
}

fn fnv1a_feed_i32(hash: &mut u64, value: i32) {
    for byte in value.to_le_bytes() {
        *hash ^= u64::from(byte);
        *hash = hash.wrapping_mul(1_099_511_628_211);
    }
}

fn dimacs_clause_fingerprint(num_vars: usize, clauses: &[Vec<Literal>]) -> u64 {
    let mut hash = 14_695_981_039_346_656_037u64;
    fnv1a_feed_u64(&mut hash, num_vars as u64);
    fnv1a_feed_u64(&mut hash, clauses.len() as u64);
    for clause in clauses {
        fnv1a_feed_u64(&mut hash, clause.len() as u64);
        for lit in clause {
            fnv1a_feed_i32(&mut hash, lit.to_dimacs());
        }
    }
    hash
}

#[derive(Debug)]
struct DenseCliquePhpProofRouteAdmission {
    asset: &'static DenseCliquePhpProofAsset,
    fingerprint: u64,
    source_audit: ay_sat::dense_clique::DenseCliqueSourceClauseAudit,
    replay_ledger: ay_sat::dense_clique::DenseCliquePhpReplayLedger,
    checker_audit_stats: Option<ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats>,
}

#[derive(Debug)]
enum DenseCliquePhpProofRouteAdmissionResult {
    NonTarget,
    TargetRejected(String),
    Admitted(Box<DenseCliquePhpProofRouteAdmission>),
}

#[derive(Debug)]
struct DenseCliquePhpMaterializedLratRouteProof {
    lrat: String,
    materialization_stats: ay_sat::dense_clique::DenseCliquePhpOriginalLratMaterializationStats,
    checker_stats: ay_lrat_check::Stats,
}

enum DenseCliquePhpRouteProofText<'a> {
    Asset(&'a str),
    MaterializedLrat(Box<DenseCliquePhpMaterializedLratRouteProof>),
}

impl DenseCliquePhpRouteProofText<'_> {
    fn as_str(&self) -> &str {
        match self {
            Self::Asset(text) => text,
            Self::MaterializedLrat(proof) => &proof.lrat,
        }
    }

    fn is_materialized_lrat(&self) -> bool {
        matches!(self, Self::MaterializedLrat(_))
    }

    fn materialized_lrat(&self) -> Option<&DenseCliquePhpMaterializedLratRouteProof> {
        match self {
            Self::MaterializedLrat(proof) => Some(proof),
            Self::Asset(_) => None,
        }
    }
}

#[derive(Debug)]
struct DenseCliquePhpProofAssetStructure {
    graph_vertices: usize,
    colors: usize,
    graph_edges: usize,
    graph_non_edges: usize,
    graph_non_edge_buckets: usize,
    graph_non_edge_bucket_min: usize,
    graph_non_edge_bucket_max: usize,
    complete_multipartite: bool,
    php_pigeons: usize,
    php_holes: usize,
    php_unsat_obligation: bool,
    mutexes: usize,
    expected_mutexes: usize,
    positive_support_clauses: usize,
    support_width: usize,
}

#[derive(Debug)]
struct DenseCliquePhpProofAsset {
    name: &'static str,
    num_vars: usize,
    num_clauses: usize,
    fingerprint: u64,
    original_order_witness: fn(&[Vec<Literal>]) -> bool,
    expected_structure: DenseCliquePhpProofAssetStructure,
    expected_checker_audit_stats: Option<ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats>,
    drat: &'static str,
    lrat: &'static str,
}

const CLIQUE_N2_K10_EXPECTED_CHECKER_AUDIT_STATS:
    ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats =
    ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats {
        enabled: true,
        source_rows_audited: 3_160,
        extension_rows_seen: 90,
        bucket_alo_rows_seen: 10,
        bucket_mutex_rows_seen: 405,
        checker_rows_materialized: 685,
        extension_definition_rows_materialized: 270,
        bucket_alo_rows_materialized: 10,
        bucket_mutex_rows_materialized: 405,
        source_dependency_edges: 1_630,
        dependency_clause_edges: 990,
        external_checker_verified_rows: 0,
    };

const DENSE_CLIQUE_PHP_PROOF_ASSETS: &[DenseCliquePhpProofAsset] = &[
    DenseCliquePhpProofAsset {
        name: "clique_n2_k10",
        num_vars: 180,
        num_clauses: 3_160,
        fingerprint: CLIQUE_N2_K10_CLAUSE_FINGERPRINT,
        original_order_witness: clique_n2_k10_original_order_witness,
        expected_structure: DenseCliquePhpProofAssetStructure {
            graph_vertices: 18,
            colors: 10,
            graph_edges: 144,
            graph_non_edges: 9,
            graph_non_edge_buckets: 9,
            graph_non_edge_bucket_min: 2,
            graph_non_edge_bucket_max: 2,
            complete_multipartite: true,
            php_pigeons: 10,
            php_holes: 9,
            php_unsat_obligation: true,
            mutexes: 3_150,
            expected_mutexes: 3_150,
            positive_support_clauses: 10,
            support_width: 18,
        },
        expected_checker_audit_stats: Some(CLIQUE_N2_K10_EXPECTED_CHECKER_AUDIT_STATS),
        drat: CLIQUE_N2_K10_ORIGINAL_DRAT,
        lrat: CLIQUE_N2_K10_ORIGINAL_LRAT,
    },
    DenseCliquePhpProofAsset {
        name: "php_functional_5_4",
        num_vars: 20,
        num_clauses: 75,
        fingerprint: PHP_FUNCTIONAL_5_4_CLAUSE_FINGERPRINT,
        original_order_witness: php_functional_5_4_original_order_witness,
        expected_structure: DenseCliquePhpProofAssetStructure {
            graph_vertices: 4,
            colors: 5,
            graph_edges: 6,
            graph_non_edges: 0,
            graph_non_edge_buckets: 4,
            graph_non_edge_bucket_min: 1,
            graph_non_edge_bucket_max: 1,
            complete_multipartite: true,
            php_pigeons: 5,
            php_holes: 4,
            php_unsat_obligation: true,
            mutexes: 70,
            expected_mutexes: 70,
            positive_support_clauses: 5,
            support_width: 4,
        },
        expected_checker_audit_stats: None,
        drat: PHP_FUNCTIONAL_5_4_ORIGINAL_DRAT,
        lrat: PHP_FUNCTIONAL_5_4_ORIGINAL_LRAT,
    },
];

fn dense_clique_php_route_header_candidate(num_vars: usize, num_clauses: usize) -> bool {
    dense_clique_php_route_asset_for_header(num_vars, num_clauses).is_some()
}

fn dense_clique_php_route_asset_for_header(
    num_vars: usize,
    num_clauses: usize,
) -> Option<&'static DenseCliquePhpProofAsset> {
    DENSE_CLIQUE_PHP_PROOF_ASSETS
        .iter()
        .find(|asset| asset.num_vars == num_vars && asset.num_clauses == num_clauses)
}

fn dense_clique_php_route_checker_audit_counts_match(
    stats: &ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats,
    expected: &ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats,
) -> bool {
    stats == expected && stats.external_checker_verified_rows == 0
}

fn dense_clique_php_route_structure_witness_ok(
    packet: &ay_sat::dense_clique::DenseCliquePhpReplayPacket,
    expected: &DenseCliquePhpProofAssetStructure,
) -> bool {
    packet
        .witness
        .scout
        .structure
        .as_ref()
        .is_some_and(|structure| {
            structure.graph_vertices == expected.graph_vertices
                && structure.colors == expected.colors
                && structure.graph_edges == expected.graph_edges
                && structure.graph_non_edges == expected.graph_non_edges
                && structure.graph_non_edge_buckets == expected.graph_non_edge_buckets
                && structure.graph_non_edge_bucket_min == expected.graph_non_edge_bucket_min
                && structure.graph_non_edge_bucket_max == expected.graph_non_edge_bucket_max
                && structure.complete_multipartite == expected.complete_multipartite
                && structure.php_pigeons == expected.php_pigeons
                && structure.php_holes == expected.php_holes
                && structure.php_unsat_obligation == expected.php_unsat_obligation
                && structure.mutexes == expected.mutexes
                && structure.expected_mutexes == expected.expected_mutexes
                && structure.positive_support_clauses == expected.positive_support_clauses
                && structure.support_width == expected.support_width
        })
}
