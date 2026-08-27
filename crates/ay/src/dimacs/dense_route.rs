// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn clause_is_ordered_negative_binary(clause: &[Literal], lhs_var: usize, rhs_var: usize) -> bool {
    clause.len() == 2
        && clause[0].to_dimacs() == -(lhs_var as i32)
        && clause[1].to_dimacs() == -(rhs_var as i32)
}

fn dense_clique_php_route_target_clauses(
    num_vars: usize,
    num_clauses_declared: usize,
    clauses: Option<&[Vec<Literal>]>,
) -> Result<Option<&[Vec<Literal>]>, String> {
    if !dense_clique_php_route_header_candidate(num_vars, num_clauses_declared) {
        return Ok(None);
    }
    let clauses = clauses.ok_or_else(|| {
        "dense clique PHP proof-asset clause capture unavailable for target header".to_string()
    })?;
    if num_clauses_declared != clauses.len() {
        return Err(format!(
            "dense clique PHP proof-asset declared clause count {num_clauses_declared} does not match captured clause count {}",
            clauses.len()
        ));
    }
    Ok(Some(clauses))
}

fn maybe_run_dense_clique_php_proof_route(
    request: DenseCliquePhpRouteRequest,
    solver: &mut SatSolver,
    num_vars: usize,
    num_clauses_declared: usize,
    clauses: Option<&[Vec<Literal>]>,
    stats_cfg: stats_output::StatsConfig,
    proof: &ProofConfig,
    source: DimacsInputSource<'_>,
) {
    maybe_run_dense_clique_php_proof_route_body(
        request,
        DenseCliquePhpRoute {
            solver,
            num_vars,
            num_clauses_declared,
            clauses,
            stats_cfg,
            proof,
            source,
        },
    );
}

fn cleanup_dense_clique_php_route_rejection_proof(
    solver: &mut SatSolver,
    proof: &ProofConfig,
) -> Option<DimacsProofWriterTelemetry> {
    cleanup_dimacs_non_unsat_proof_sidecar(solver, &SatResult::Unknown, Some(proof))
}
