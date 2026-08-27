// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn create_finalize_rescue_solver(
    formula: &ay_sat::DimacsFormula,
    proof_config: Option<&ProofConfig>,
) -> Option<SatSolver> {
    let Some(proof) = proof_config else {
        return Some(SatSolver::new(formula.num_vars));
    };
    let num_original_clauses = formula.clauses.len() as u64;
    let output = match create_configured_dimacs_proof_file(proof)
        .and_then(|file| solver_proof_output_writer(file, proof))
    {
        Ok(writer) => match (proof.format, proof.binary) {
            (ProofFormat::Veripb, _) => ProofOutput::veripb(writer),
            (ProofFormat::Drat, false) => ProofOutput::drat_text(writer),
            (ProofFormat::Drat, true) => ProofOutput::drat_binary(writer),
            (ProofFormat::Lrat, false) => ProofOutput::lrat_text(writer, num_original_clauses),
            (ProofFormat::Lrat, true) => ProofOutput::lrat_binary(writer, num_original_clauses),
            (ProofFormat::Alethe | ProofFormat::Lean4, _) => return None,
        },
        Err(error) if synthesized_default_dimacs_proof_is_optional(proof) => {
            sink_proof_output_after_optional_create_failure(proof, num_original_clauses, &error)
        }
        Err(error) => {
            safe_eprintln!(
                "c FINALIZE_RESCUE: skipped (proof re-create failed for {}: {error})",
                proof.path
            );
            return None;
        }
    };
    Some(SatSolver::with_proof_output(formula.num_vars, output))
}

fn run_finalize_rescue_body(
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
) -> Option<(SatResult, SatSolver)> {
    let owned_content;
    let content = match source {
        DimacsInputSource::Content(content) => content,
        DimacsInputSource::FilePath { path, sha256 } => {
            owned_content = match read_authenticated_dimacs_source(path, sha256) {
                Ok(text) => text,
                Err(error) => {
                    safe_eprintln!(
                        "c FINALIZE_RESCUE: skipped (authenticated re-read failed: {error})"
                    );
                    return None;
                }
            };
            owned_content.as_str()
        }
        DimacsInputSource::Unavailable => {
            safe_eprintln!("c FINALIZE_RESCUE: skipped (original DIMACS unavailable)");
            return None;
        }
    };
    let formula = match parse_dimacs(content) {
        Ok(formula) => formula,
        Err(error) => {
            safe_eprintln!("c FINALIZE_RESCUE: skipped (re-parse failed: {error})");
            return None;
        }
    };
    safe_eprintln!(
        "c FINALIZE_RESCUE: finalize gate rejected the candidate model; retrying once \
         with model-mutating preprocessing disabled (elapsed {}ms)",
        global_elapsed().as_millis()
    );
    let mut solver = create_finalize_rescue_solver(&formula, proof_config)?;
    solver.set_inprocessing_profile(&finalize_rescue_profile());
    solver.set_symmetry_oneshot(true);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve_interruptible(is_timed_out).into_inner();
    let verdict = match &result {
        SatResult::Sat(_) => "sat",
        SatResult::Unsat(_) => "unsat",
        _ => "unknown",
    };
    safe_eprintln!(
        "c FINALIZE_RESCUE: retry verdict={verdict} (elapsed {}ms)",
        global_elapsed().as_millis()
    );
    if !matches!(result, SatResult::Unsat(_)) {
        let _ = cleanup_dimacs_non_unsat_proof_sidecar(&mut solver, &result, proof_config);
    }
    Some((result, solver))
}
