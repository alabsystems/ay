// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

const SAT_DENSE_CLIQUE_PHP_COMPACT_LRAT_PROOF_ENV: &str =
    "AY_SAT_DENSE_CLIQUE_PHP_COMPACT_LRAT_PROOF";

fn dense_clique_php_route_admission(
    num_vars: usize,
    clauses: &[Vec<Literal>],
) -> DenseCliquePhpProofRouteAdmissionResult {
    let Some(asset) = dense_clique_php_route_asset_for_header(num_vars, clauses.len()) else {
        return DenseCliquePhpProofRouteAdmissionResult::NonTarget;
    };
    if !(asset.original_order_witness)(clauses) {
        return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(format!(
            "{} original-order witness mismatch",
            asset.name
        ));
    }
    let fingerprint = dimacs_clause_fingerprint(num_vars, clauses);
    if fingerprint != asset.fingerprint {
        return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(format!(
            "{} original clause fingerprint mismatch",
            asset.name
        ));
    }

    let packet = match ay_sat::dense_clique::build_dense_clique_php_replay_packet_from_clauses(
        num_vars, clauses,
    ) {
        Ok(packet) => packet,
        Err(error) => {
            return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(format!(
                "dense clique PHP source replay packet rejected: {error:?}"
            ));
        }
    };
    if !packet.authority_is_absent() {
        return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(
            "dense clique PHP source replay packet unexpectedly carried authority".to_string(),
        );
    }

    if !dense_clique_php_route_structure_witness_ok(&packet, &asset.expected_structure) {
        return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(format!(
            "dense clique PHP {} structure witness mismatch",
            asset.name
        ));
    }

    let checker_audit_stats = if let Some(expected) = asset.expected_checker_audit_stats.as_ref() {
        let checker_audit = match ay_sat::dense_clique::materialize_dense_clique_php_checker_audit(
            ay_sat::dense_clique::DenseCliquePhpCheckerAuditConfig { enabled: true },
            &packet,
        ) {
            Ok(checker_audit) => checker_audit,
            Err(error) => {
                return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(format!(
                    "dense clique PHP checker audit materialization rejected: {error:?}"
                ));
            }
        };
        if !checker_audit.authority_is_absent() {
            return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(
                "dense clique PHP checker audit unexpectedly carried authority".to_string(),
            );
        }
        if !dense_clique_php_route_checker_audit_counts_match(&checker_audit.stats, expected) {
            return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(format!(
                "dense clique PHP {} checker audit materialization counters mismatch",
                asset.name
            ));
        }
        Some(checker_audit.stats)
    } else {
        None
    };

    DenseCliquePhpProofRouteAdmissionResult::Admitted(Box::new(DenseCliquePhpProofRouteAdmission {
        asset,
        fingerprint,
        source_audit: packet.source_audit,
        replay_ledger: packet.replay_ledger,
        checker_audit_stats,
    }))
}

fn dense_clique_php_materialized_lrat_route_proof_from_env(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    admission: &DenseCliquePhpProofRouteAdmission,
) -> Result<Option<DenseCliquePhpMaterializedLratRouteProof>, String> {
    let Some(compact_lrat_path) = std::env::var_os(SAT_DENSE_CLIQUE_PHP_COMPACT_LRAT_PROOF_ENV)
    else {
        return Ok(None);
    };
    let compact_lrat_path = PathBuf::from(compact_lrat_path);
    if compact_lrat_path.as_os_str().is_empty() {
        return Ok(None);
    }
    let compact_lrat = std::fs::read_to_string(&compact_lrat_path).map_err(|error| {
        format!(
            "failed to read compact LRAT proof {}: {error}",
            compact_lrat_path.display()
        )
    })?;

    let packet =
        ay_sat::dense_clique::build_dense_clique_php_replay_packet_from_clauses(num_vars, clauses)
            .map_err(|error| {
                format!("dense clique PHP source replay packet rejected: {error:?}")
            })?;
    if !packet.authority_is_absent() {
        return Err(
            "dense clique PHP source replay packet unexpectedly carried authority".to_string(),
        );
    }

    let materialization =
        ay_sat::dense_clique::materialize_dense_clique_php_original_lrat_from_compact_proof(
            ay_sat::dense_clique::DenseCliquePhpOriginalLratMaterializerConfig { enabled: true },
            &packet,
            &compact_lrat,
        )
        .map_err(|error| format!("original-DIMACS LRAT materialization rejected: {error:?}"))?;
    if !materialization.authority_is_absent() {
        return Err(
            "original-DIMACS LRAT materialization unexpectedly carried authority".to_string(),
        );
    }
    let expected_compact_clauses = admission.replay_ledger.bucket_alo_rows.len()
        + admission.replay_ledger.bucket_mutex_rows.len();
    if materialization.stats.source_rows_audited != admission.source_audit.source_rows as u64
        || materialization.stats.compact_clauses != expected_compact_clauses as u64
        || materialization.stats.extension_clauses_added
            != admission.replay_ledger.extension_clause_count() as u64
        || materialization.stats.external_checker_verified != 0
    {
        return Err(format!(
            "original-DIMACS LRAT materialization counters mismatch: {:?}",
            materialization.stats
        ));
    }

    let checker_stats =
        validate_original_lrat_against_clauses(num_vars, clauses, &materialization.lrat)?;
    Ok(Some(DenseCliquePhpMaterializedLratRouteProof {
        lrat: materialization.lrat,
        materialization_stats: materialization.stats,
        checker_stats,
    }))
}

fn validate_original_lrat_against_clauses(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    lrat: &str,
) -> Result<ay_lrat_check::Stats, String> {
    if num_vars > ay_lrat_check::checker::MAX_DENSE_VARS {
        return Err(format!(
            "formula variable count {num_vars} exceeds LRAT checker's dense maximum {}",
            ay_lrat_check::checker::MAX_DENSE_VARS
        ));
    }
    let steps = ay_lrat_check::lrat_parser::parse_text_lrat(lrat)
        .map_err(|error| format!("LRAT proof parse error: {error}"))?;
    if steps.is_empty() {
        return Err("LRAT proof contains zero steps".to_string());
    }

    let mut checker = ay_lrat_check::checker::LratChecker::new(num_vars);
    for (index, clause) in clauses.iter().enumerate() {
        let mut checker_clause = Vec::with_capacity(clause.len());
        for lit in clause {
            checker_clause.push(ay_lrat_check::dimacs::Literal::from_dimacs(lit.to_dimacs()));
        }
        if !checker.add_original(index as u64 + 1, &checker_clause) {
            return Err(format!(
                "LRAT checker rejected original clause {}: {}",
                index + 1,
                checker.stats_summary()
            ));
        }
    }
    if checker.verify_proof(&steps) {
        Ok(checker.stats().clone())
    } else {
        Err(format!(
            "LRAT checker rejected materialized proof: {}",
            checker.stats_summary()
        ))
    }
}

fn clique_n2_k10_original_order_witness(clauses: &[Vec<Literal>]) -> bool {
    if clauses.len() != 3160 {
        return false;
    }
    for color in 0..10 {
        let clause = &clauses[color];
        if clause.len() != 18 {
            return false;
        }
        for (vertex, lit) in clause.iter().enumerate() {
            if !lit.is_positive() || lit.to_dimacs() != (color * 18 + vertex + 1) as i32 {
                return false;
            }
        }
    }

    let mut offset = 10usize;
    for color in 0..10 {
        let base = color * 18 + 1;
        for lhs in 0..18 {
            for rhs in (lhs + 1)..18 {
                if !clause_is_ordered_negative_binary(&clauses[offset], base + lhs, base + rhs) {
                    return false;
                }
                offset += 1;
            }
        }
    }
    true
}

fn php_functional_5_4_original_order_witness(clauses: &[Vec<Literal>]) -> bool {
    if clauses.len() != 75 {
        return false;
    }

    for pigeon in 0..5 {
        let clause = &clauses[pigeon];
        if clause.len() != 4 {
            return false;
        }
        for (hole, lit) in clause.iter().enumerate() {
            if !lit.is_positive() || lit.to_dimacs() != php_functional_5_4_var(pigeon, hole) as i32
            {
                return false;
            }
        }
    }

    let mut offset = 5usize;
    for pigeon in 0..5 {
        for lhs_hole in 0..4 {
            for rhs_hole in (lhs_hole + 1)..4 {
                if !clause_is_ordered_negative_binary(
                    &clauses[offset],
                    php_functional_5_4_var(pigeon, lhs_hole),
                    php_functional_5_4_var(pigeon, rhs_hole),
                ) {
                    return false;
                }
                offset += 1;
            }
        }
    }

    for hole in 0..4 {
        for lhs_pigeon in 0..5 {
            for rhs_pigeon in (lhs_pigeon + 1)..5 {
                if !clause_is_ordered_negative_binary(
                    &clauses[offset],
                    php_functional_5_4_var(lhs_pigeon, hole),
                    php_functional_5_4_var(rhs_pigeon, hole),
                ) {
                    return false;
                }
                offset += 1;
            }
        }
    }

    offset == clauses.len()
}

const fn php_functional_5_4_var(pigeon: usize, hole: usize) -> usize {
    pigeon * 4 + hole + 1
}
