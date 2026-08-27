// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn cleanup_dimacs_non_unsat_proof_sidecar(
    solver: &mut SatSolver,
    result: &SatResult,
    proof_config: Option<&ProofConfig>,
) -> Option<DimacsProofWriterTelemetry> {
    if matches!(result, SatResult::Unsat(_)) {
        return None;
    }

    retain_fmla_learned_lrat_dry_run_artifact_from_env(solver);
    let writer_telemetry = dimacs_proof_writer_telemetry(solver);
    if let Some(mut proof_output) = solver.take_proof_writer() {
        if let Err(error) = proof_output.flush() {
            safe_eprintln!("c Warning: failed to flush discarded non-UNSAT proof output: {error}");
        }
    }

    cleanup_dimacs_non_unsat_proof_paths(proof_config);
    writer_telemetry
}

fn cleanup_dimacs_non_unsat_proof_paths_for_result(
    result: &SatResult,
    proof_config: Option<&ProofConfig>,
) {
    if matches!(result, SatResult::Unsat(_)) {
        return;
    }
    cleanup_dimacs_non_unsat_proof_paths(proof_config);
}

fn cleanup_dimacs_non_unsat_proof_paths(proof_config: Option<&ProofConfig>) {
    let Some(proof) = proof_config else {
        return;
    };
    if let Err(error) = remove_owned_dimacs_proof(&proof.path) {
        safe_eprintln!(
            "c Warning: failed to remove owned non-UNSAT proof output {}: {error}",
            proof.path
        );
    }
    // Proof artifacts are only published after a sealed UNSAT proof exists.
    // Never unlink a pre-existing sidecar on a non-UNSAT route: it is not
    // owned by this solve and may be an unrelated hard-linked file.
}

fn finalize_solver_dimacs_proof_or_exit(solver: &mut SatSolver, proof: &ProofConfig) {
    if published_dimacs_proof(&proof.path).is_ok() {
        return;
    }
    let Some(mut output) = solver.take_proof_writer() else {
        if synthesized_default_dimacs_proof_is_optional(proof) {
            warn_optional_dimacs_proof_failure(proof, "the UNSAT solve produced no proof writer");
            if let Err(error) = remove_owned_dimacs_proof(&proof.path) {
                safe_eprintln!(
                    "c Warning: failed to discard writerless optional DIMACS proof {}: {error}",
                    proof.path
                );
            }
            return;
        }
        fail_dimacs_certification_or_exit(&format!(
            "UNSAT result produced no proof writer for requested output {}",
            proof.path
        ));
    };
    if let Err(error) = output.flush() {
        handle_dimacs_proof_io_failure(proof, "flush", &error);
        return;
    }
    drop(output);
    if let Err(error) = seal_owned_dimacs_proof(&proof.path) {
        handle_dimacs_proof_io_failure(proof, "seal", &error);
    }
}

fn required_dimacs_proof_gate_name() -> Option<&'static str> {
    let strict = super::STRICT_PROOFS_ENABLED.load(Ordering::SeqCst);
    let self_check = super::SELF_CHECK_ENABLED.load(Ordering::SeqCst);
    match (strict, self_check) {
        (true, true) => Some("--strict-proofs/--self-check"),
        (true, false) => Some("--strict-proofs"),
        (false, true) => Some("--self-check"),
        (false, false) => None,
    }
}

fn required_dimacs_proof_gate_error(proof_config: Option<&ProofConfig>) -> Option<String> {
    let gate = required_dimacs_proof_gate_name()?;
    if !super::VERIFY_PROOF_ENABLED.load(Ordering::SeqCst) {
        return Some(format!(
            "{gate} requires authenticated DIMACS proof re-checking; --no-verify-proof and competition proof opt-outs are incompatible with this route"
        ));
    }
    let Some(proof) = proof_config else {
        return Some(format!(
            "{gate} requires a same-run DIMACS refutation; --no-proof, --z3-mode, and competition proof opt-outs are incompatible with this route"
        ));
    };
    if !matches!(proof.format, ProofFormat::Drat | ProofFormat::Lrat) {
        return Some(format!(
            "{gate} requires a DIMACS proof format supported by AY's independent checker (DRAT or LRAT); got {}",
            proof_format_name(proof.format)
        ));
    }
    None
}

fn enforce_required_dimacs_proof_gate(proof_config: Option<&ProofConfig>) {
    if proof_config.is_some_and(|proof| proof.format == ProofFormat::Alethe) {
        safe_eprintln!(
            "Error: Alethe proof output is unavailable for DIMACS input because the SAT certificate does not retain original clause literals; use --proof-format lrat or drat"
        );
        std::process::exit(1);
    }
    if let Some(error) = required_dimacs_proof_gate_error(proof_config) {
        safe_eprintln!("Error: {error}");
        std::process::exit(1);
    }
}

fn invalidate_synthesized_default_dimacs_proof(proof: &ProofConfig) -> io::Result<bool> {
    debug_assert!(proof.synthesized_default);
    mark_synthesized_default_dimacs_proof_stale(proof);
    remove_owned_dimacs_proof(&proof.path)
}

/// Complete every mandatory UNSAT proof gate before publishing a proof
/// artifact or exposing UNSAT through stats/stdout. The proof bytes themselves
/// must already have been emitted and descriptor-sealed by the route.
fn authorize_dimacs_unsat_artifacts(
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
    theory: ProofArtifactTheoryMetadata,
) -> AuthorizedDimacsUnsatPublication {
    authorize_dimacs_unsat_artifacts_body(source, proof_config, theory)
}
