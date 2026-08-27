// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn run_dimacs_solver_with_research_sidecar_stats(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    content: &str,
    proof_config: Option<&ProofConfig>,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    run_dimacs_solver_with_source_and_research_sidecar_stats(
        solver,
        stats_cfg,
        DimacsInputSource::Content(content),
        proof_config,
        guard_cover,
        separator_cover,
    );
}

fn run_dimacs_solver_with_source(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
) {
    run_dimacs_solver_with_source_and_research_sidecar_stats(
        solver,
        stats_cfg,
        source,
        proof_config,
        None,
        None,
    );
}

fn run_dimacs_solver_with_source_and_research_sidecar_stats(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    configure_dimacs_solver(solver, stats_cfg);
    let _fmla_proof_out_env = FmlaCurrentProofOutEnvGuard::set_for_proof(proof_config);
    let result = solver.solve_interruptible(is_timed_out).into_inner();
    finish_dimacs_solve_with_source(
        solver,
        result,
        stats_cfg,
        source,
        proof_config,
        guard_cover,
        separator_cover,
        None,
    );
}

fn run_dimacs_solver_with_extension(
    solver: &mut SatSolver,
    ext: &mut dyn Extension,
    stats_cfg: stats_output::StatsConfig,
    content: &str,
    proof_config: Option<&ProofConfig>,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    configure_dimacs_solver(solver, stats_cfg);
    let _fmla_proof_out_env = FmlaCurrentProofOutEnvGuard::set_for_proof(proof_config);
    let result = solver
        .solve_interruptible_with_extension(ext, is_timed_out)
        .into_inner();
    finish_dimacs_solve(
        solver,
        result,
        stats_cfg,
        content,
        proof_config,
        guard_cover,
        separator_cover,
    );
}

/// Solve one input and write a soundness-grounded Lean4 LRAT proof on UNSAT.
///
/// The solver must have LRAT output enabled so its certificate can be exported
/// with the original clause table and connected to
/// `AySoundness.lratCheck_sound`.
fn run_dimacs_solver_lean4_with_source(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    lean4_path: &str,
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
    original_clauses: &[(u64, Vec<i32>)],
) {
    configure_dimacs_solver(solver, stats_cfg);
    let result = solver.solve_interruptible(is_timed_out).into_inner();

    // On UNSAT, write the Lean4 LRAT kernel-checkable export before
    // finish_dimacs_solve exits.
    let mut proof_writer_telemetry = None;
    if let SatResult::Unsat(ref cert) = result {
        let (lean_cert, telemetry) = take_text_lrat_certificate(solver, cert);
        proof_writer_telemetry = telemetry;
        let file = match create_owned_dimacs_proof_file(lean4_path) {
            Ok(f) => f,
            Err(e) => {
                safe_eprintln!("Error: failed to create Lean4 proof file {lean4_path}: {e}");
                std::process::exit(1);
            }
        };
        let mut writer = proof_output_writer(file);
        if let Err(e) = lean_cert.write_lean4_verified(original_clauses, &mut writer) {
            safe_eprintln!("Error: failed to write Lean4 proof to {lean4_path}: {e}");
            std::process::exit(1);
        }
        if let Err(e) = writer.flush() {
            safe_eprintln!("Error: failed to flush Lean4 proof file {lean4_path}: {e}");
            std::process::exit(1);
        }
        drop(writer);
        if let Err(e) = seal_owned_dimacs_proof(lean4_path) {
            safe_eprintln!("Error: failed to seal Lean4 proof file {lean4_path}: {e}");
            std::process::exit(1);
        }
    }

    finish_dimacs_solve_with_source(
        solver,
        result,
        stats_cfg,
        source,
        proof_config,
        None,
        None,
        proof_writer_telemetry,
    );
}

fn take_text_lrat_certificate(
    solver: &mut SatSolver,
    fallback: &ProofCertificate,
) -> (ProofCertificate, Option<DimacsProofWriterTelemetry>) {
    let telemetry = dimacs_proof_writer_telemetry(solver);
    let Some(proof_output) = solver.take_proof_writer() else {
        return (fallback.clone(), telemetry);
    };
    let bytes = match proof_output.into_vec() {
        Ok(bytes) => bytes,
        Err(error) => {
            safe_eprintln!(
                "c Warning: failed to capture internal LRAT stream for Lean4 proof ({error}); \
                 falling back to deferred certificate"
            );
            return (fallback.clone(), telemetry);
        }
    };
    match ProofCertificate::from_lrat_text(&bytes) {
        Ok(cert) => (cert, telemetry),
        Err(error) => {
            safe_eprintln!(
                "c Warning: failed to parse internal LRAT stream for Lean4 proof ({error}); \
                 falling back to deferred certificate"
            );
            (fallback.clone(), telemetry)
        }
    }
}
