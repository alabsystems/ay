// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn run_dimacs_cube_and_conquer_body(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    depth: usize,
    num_threads: usize,
) {
    use ay_sat::CubeAndConquerSolver;

    reject_dimacs_decision_trace_or_exit();
    enforce_required_dimacs_proof_gate(proof_config);
    let formula = match parse_dimacs(content) {
        Ok(formula) => formula,
        Err(error) => {
            cleanup_dimacs_non_unsat_proof_paths(proof_config);
            safe_eprintln!("c Parse error: {error}");
            safe_println!("s UNKNOWN");
            std::process::exit(1);
        }
    };
    safe_eprintln!(
        "c cube-and-conquer: depth {depth}, {num_threads} threads, {} vars, {} clauses",
        formula.num_vars,
        formula.clauses.len()
    );
    let start = std::time::Instant::now();
    let result = CubeAndConquerSolver::new(num_threads, depth).solve(&formula);
    safe_eprintln!(
        "c cube-and-conquer: solved in {:.3}s",
        start.elapsed().as_secs_f64()
    );
    cleanup_dimacs_non_unsat_proof_paths_for_result(&result, proof_config);
    if let (SatResult::Unsat(cert), Some(proof)) = (&result, proof_config) {
        let original = dimacs_original_clauses_from_literals(&formula.clauses);
        write_parallel_proof(None, cert, proof, &original);
    }
    let mut authority = parallel_unsat_authority(content, proof_config, &formula, &result);
    let route = ParallelDimacsRoute::CubeAndConquer {
        depth,
        threads: num_threads,
    };
    emit_parallel_dimacs_statistics(route, &result, stats_cfg, &mut authority);
    if let Some(authority) = &mut authority {
        validate_dimacs_unsat_publication_before_verdict(authority);
    }
    emit_sat_applied_run_summary(
        route.label(),
        route.source(),
        VariantRouteProfile::Standard,
        proof_config,
    );
    publish_parallel_dimacs_result(route, result, authority);
}
