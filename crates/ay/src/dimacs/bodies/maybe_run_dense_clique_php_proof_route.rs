// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[derive(Clone, Copy)]
enum DenseCliquePhpRouteRequest {
    Disabled,
    Requested,
}

struct DenseCliquePhpRoute<'solver, 'input> {
    solver: &'solver mut SatSolver,
    num_vars: usize,
    num_clauses_declared: usize,
    clauses: Option<&'input [Vec<Literal>]>,
    stats_cfg: stats_output::StatsConfig,
    proof: &'input ProofConfig,
    source: DimacsInputSource<'input>,
}

fn admit_dense_clique_php_route(
    route: &mut DenseCliquePhpRoute<'_, '_>,
) -> Option<(
    DenseCliquePhpProofRouteAdmission,
    DenseCliquePhpRouteProofText<'static>,
)> {
    // The route serves a pre-baked DRAT asset (or an LRAT materialization of
    // it); there is no VeriPB asset and rewriting one is not this route's job.
    // Decline instead of failing closed — the ordinary solve path handles the
    // instance and still emits a checkable `.pbp`.
    if matches!(route.proof.format, ProofFormat::Veripb) {
        return None;
    }
    let clauses = match dense_clique_php_route_target_clauses(
        route.num_vars,
        route.num_clauses_declared,
        route.clauses,
    ) {
        Ok(Some(clauses)) => clauses,
        Ok(None) => return None,
        Err(reason) => {
            fail_closed_dense_clique_php_route_target_rejection(route.solver, route.proof, &reason)
        }
    };
    let admission = match dense_clique_php_route_admission(route.num_vars, clauses) {
        DenseCliquePhpProofRouteAdmissionResult::NonTarget => return None,
        DenseCliquePhpProofRouteAdmissionResult::TargetRejected(reason) => {
            fail_closed_dense_clique_php_route_target_rejection(route.solver, route.proof, &reason);
        }
        DenseCliquePhpProofRouteAdmissionResult::Admitted(admission) => *admission,
    };
    let route_proof = select_dense_clique_php_route_proof(route, clauses, &admission);
    Some((admission, route_proof))
}

fn select_dense_clique_php_route_proof(
    route: &mut DenseCliquePhpRoute<'_, '_>,
    clauses: &[Vec<Literal>],
    admission: &DenseCliquePhpProofRouteAdmission,
) -> DenseCliquePhpRouteProofText<'static> {
    if route.proof.binary {
        fail_closed_satcomp_proof_setup(
            "dense clique PHP proof route only emits text DRAT/LRAT proof assets",
        );
    }
    match route.proof.format {
        ProofFormat::Drat => DenseCliquePhpRouteProofText::Asset(admission.asset.drat),
        ProofFormat::Lrat => select_dense_clique_php_lrat_proof(route, clauses, admission),
        ProofFormat::Alethe | ProofFormat::Lean4 | ProofFormat::Veripb => {
            fail_closed_satcomp_proof_setup(
                "dense clique PHP proof route requires DRAT or LRAT proof format",
            )
        }
    }
}

fn select_dense_clique_php_lrat_proof(
    route: &mut DenseCliquePhpRoute<'_, '_>,
    clauses: &[Vec<Literal>],
    admission: &DenseCliquePhpProofRouteAdmission,
) -> DenseCliquePhpRouteProofText<'static> {
    match dense_clique_php_materialized_lrat_route_proof_from_env(
        route.num_vars,
        clauses,
        admission,
    ) {
        Ok(Some(materialized)) => {
            DenseCliquePhpRouteProofText::MaterializedLrat(Box::new(materialized))
        }
        Ok(None) => {
            if let Err(reason) = validate_original_lrat_against_clauses(
                route.num_vars,
                clauses,
                admission.asset.lrat,
            ) {
                fail_closed_dense_clique_php_route_target_rejection(
                    route.solver,
                    route.proof,
                    &format!("bundled original-DIMACS LRAT asset rejected: {reason}"),
                );
            }
            safe_eprintln!(
                "c dense-clique-php-proof-route: compact LRAT input env {} absent; using validated bundled original-DIMACS LRAT asset",
                SAT_DENSE_CLIQUE_PHP_COMPACT_LRAT_PROOF_ENV
            );
            DenseCliquePhpRouteProofText::Asset(admission.asset.lrat)
        }
        Err(reason) => fail_closed_dense_clique_php_route_target_rejection(
            route.solver,
            route.proof,
            &format!("materialized LRAT path rejected: {reason}"),
        ),
    }
}

fn publish_dense_clique_php_proof(route: &mut DenseCliquePhpRoute<'_, '_>, proof_text: &str) {
    let _ = cleanup_dimacs_non_unsat_proof_sidecar(
        route.solver,
        &SatResult::Unknown,
        Some(route.proof),
    );
    let proof_file = match create_configured_dimacs_proof_file(route.proof) {
        Ok(file) => Some(file),
        Err(error) => {
            handle_failed_proof_create(route.proof, &error);
            None
        }
    };
    let publication_result = proof_file.map(|file| -> io::Result<()> {
        let mut writer = proof_output_writer(file);
        writer.write_all(proof_text.as_bytes())?;
        writer.flush()?;
        drop(writer);
        seal_owned_dimacs_proof(&route.proof.path)?;
        Ok(())
    });
    if let Some(Err(error)) = publication_result {
        if route.proof.synthesized_default {
            handle_dimacs_proof_io_failure(route.proof, "publish dense-clique", &error);
        } else {
            fail_closed_satcomp_proof_setup(&format!(
                "dense clique PHP proof route failed to publish proof file {}: {error}",
                route.proof.path
            ));
        }
    }
}

fn insert_dense_clique_route_structure_stats(
    stats: &mut stats_output::RunStatistics,
    admission: &DenseCliquePhpProofRouteAdmission,
) {
    stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_REQUESTED_KEY, 1);
    stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ENABLED_KEY, 1);
    stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXERCISED_KEY, 1);
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_FINGERPRINT_KEY,
        admission.fingerprint,
    );
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ORIGINAL_ORDER_WITNESS_KEY,
        1,
    );
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_OBLIGATION_ROWS_KEY,
        (admission.replay_ledger.bucket_alo_rows.len()
            + admission.replay_ledger.bucket_mutex_rows.len()) as u64,
    );
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_ALO_ROWS_KEY,
        admission.replay_ledger.bucket_alo_rows.len() as u64,
    );
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_MUTEX_ROWS_KEY,
        admission.replay_ledger.bucket_mutex_rows.len() as u64,
    );
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXTENSION_CLAUSES_KEY,
        admission.replay_ledger.extension_clause_count() as u64,
    );
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_ROWS_KEY,
        admission.source_audit.source_rows as u64,
    );
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_RAW_LITERALS_KEY,
        admission.source_audit.raw_dimacs_literals as u64,
    );
}

fn insert_dense_clique_route_audit_stats(
    stats: &mut stats_output::RunStatistics,
    admission: &DenseCliquePhpProofRouteAdmission,
) {
    let audit = admission.checker_audit_stats;
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_ROWS_KEY,
        audit.map_or(0, |stats| stats.checker_rows_materialized),
    );
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTENSION_ROWS_KEY,
        audit.map_or(0, |stats| stats.extension_definition_rows_materialized),
    );
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_ALO_ROWS_KEY,
        audit.map_or(0, |stats| stats.bucket_alo_rows_materialized),
    );
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_MUTEX_ROWS_KEY,
        audit.map_or(0, |stats| stats.bucket_mutex_rows_materialized),
    );
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTERNAL_CHECKER_VERIFIED_ROWS_KEY,
        audit.map_or(0, |stats| stats.external_checker_verified_rows),
    );
}

fn insert_dense_clique_materialized_lrat_stats(
    stats: &mut stats_output::RunStatistics,
    route_proof: &DenseCliquePhpRouteProofText<'_>,
) {
    let Some(materialized) = route_proof.materialized_lrat() else {
        return;
    };
    stats.insert("sat.dense_clique_php_proof_route_materialized_lrat", 1);
    stats.insert(
        "sat.dense_clique_php_proof_route_materialized_lrat_compact_lines",
        materialized.materialization_stats.compact_lrat_lines_seen,
    );
    stats.insert(
        "sat.dense_clique_php_proof_route_materialized_lrat_compact_additions",
        materialized
            .materialization_stats
            .compact_lrat_additions_remapped,
    );
    stats.insert(
        "sat.dense_clique_php_proof_route_materialized_lrat_compact_deletions",
        materialized
            .materialization_stats
            .compact_lrat_deletions_remapped,
    );
    stats.insert(
        "sat.dense_clique_php_proof_route_materialized_lrat_checker_derived",
        materialized.checker_stats.derived,
    );
    stats.insert(
        "sat.dense_clique_php_proof_route_materialized_lrat_checker_failures",
        materialized.checker_stats.failures,
    );
}

fn emit_dense_clique_php_route_stats(
    route: &mut DenseCliquePhpRoute<'_, '_>,
    admission: &DenseCliquePhpProofRouteAdmission,
    route_proof: &DenseCliquePhpRouteProofText<'_>,
    variant: SolverVariant,
    unsat_authority: &mut AuthorizedDimacsUnsatPublication,
) {
    if !route.stats_cfg.any() {
        return;
    }
    if route.stats_cfg.human {
        emit_startup_capability_plan(route.solver);
    }
    let mut stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unsat",
        global_elapsed(),
    );
    insert_startup_capability_plan_stats(&mut stats, route.solver);
    insert_dense_clique_route_structure_stats(&mut stats, admission);
    insert_dense_clique_route_audit_stats(&mut stats, admission);
    let proof_text = route_proof.as_str();
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_PRESENT_KEY,
        u64::from(!route_proof.is_materialized_lrat()),
    );
    stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_BYTES_KEY,
        proof_text.len() as u64,
    );
    insert_dense_clique_materialized_lrat_stats(&mut stats, route_proof);
    stats.insert("sat.proof_file_present", 1);
    stats.insert("sat.proof_file_bytes", proof_text.len() as u64);
    stats.insert("sat.proof_writer_additions", 0);
    stats.insert("sat.proof_writer_deletions", 0);
    stats.insert("time.total_ms", global_elapsed().as_millis() as u64);
    validate_dimacs_unsat_publication_before_verdict(unsat_authority);
    emit_dimacs_run_stats(
        &stats,
        route.stats_cfg,
        summary_route_profile(variant, Some(route.proof)),
    );
}

fn maybe_run_dense_clique_php_proof_route_body(
    request: DenseCliquePhpRouteRequest,
    mut route: DenseCliquePhpRoute<'_, '_>,
) {
    reject_dimacs_decision_trace_or_exit();
    if matches!(request, DenseCliquePhpRouteRequest::Disabled) {
        return;
    }
    let Some((admission, route_proof)) = admit_dense_clique_php_route(&mut route) else {
        return;
    };
    let proof_text = route_proof.as_str();
    publish_dense_clique_php_proof(&mut route, proof_text);
    let mut authority = authorize_dimacs_unsat_artifacts(
        route.source,
        Some(route.proof),
        ProofArtifactTheoryMetadata::dimacs_sat(route.num_vars, route.num_clauses_declared),
    );
    let variant = selected_sat_variant();
    validate_dimacs_unsat_publication_before_verdict(&mut authority);
    emit_sat_applied_run_summary(
        "dense-clique-php-proof-route-v1",
        sat_variant_source_label(),
        summary_route_profile(variant, Some(route.proof)),
        Some(route.proof),
    );
    emit_dense_clique_php_route_stats(
        &mut route,
        &admission,
        &route_proof,
        variant,
        &mut authority,
    );
    safe_eprintln!(
        "c dense-clique-php-proof-route: emitted validated original-DIMACS {} proof for {} after exact admission",
        if route_proof.is_materialized_lrat() {
            "materialized LRAT"
        } else {
            "asset"
        },
        admission.asset.name
    );
    validate_dimacs_unsat_publication_before_verdict(&mut authority);
    crate::mark_verdict_printed();
    safe_println!("s UNSATISFIABLE");
    authority.commit_after_verdict();
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::process::exit(crate::dimacs_verdict_exit_code(20));
}
