// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn emit_dimacs_run_stats(
    run_stats: &stats_output::RunStatistics,
    stats_cfg: stats_output::StatsConfig,
    route_profile: VariantRouteProfile,
) {
    if stats_cfg.human {
        run_stats.print_to_stderr();
    }
    if stats_cfg.json {
        safe_eprintln!("{}", dimacs_run_stats_json(run_stats, route_profile));
    }
}

fn dimacs_proof_file_telemetry(proof_config: Option<&ProofConfig>) -> (u64, u64) {
    let Some(proof) = proof_config else {
        return (0, 0);
    };
    match std::fs::metadata(&proof.path) {
        Ok(metadata) if metadata.is_file() => (1, metadata.len()),
        _ => (0, 0),
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct DimacsProofWriterTelemetry {
    additions: u64,
    deletions: u64,
}

fn dimacs_proof_writer_telemetry(solver: &SatSolver) -> Option<DimacsProofWriterTelemetry> {
    solver
        .proof_writer()
        .map(|writer| DimacsProofWriterTelemetry {
            additions: writer.added_count(),
            deletions: writer.deleted_count(),
        })
}

fn insert_dimacs_proof_telemetry(
    run_stats: &mut stats_output::RunStatistics,
    solver: &mut SatSolver,
    proof_config: Option<&ProofConfig>,
    writer_telemetry_override: Option<DimacsProofWriterTelemetry>,
) {
    let writer_telemetry = writer_telemetry_override
        .or_else(|| dimacs_proof_writer_telemetry(solver))
        .unwrap_or_default();
    if let Err(error) = solver.flush_proof_writer() {
        safe_eprintln!("c Warning: failed to flush proof output before stats: {error}");
    }
    let (proof_file_present, proof_file_bytes) = dimacs_proof_file_telemetry(proof_config);
    run_stats.insert("sat.proof_file_present", proof_file_present);
    run_stats.insert("sat.proof_file_bytes", proof_file_bytes);
    run_stats.insert("sat.proof_writer_additions", writer_telemetry.additions);
    run_stats.insert("sat.proof_writer_deletions", writer_telemetry.deletions);
}

fn insert_preprocessing_transaction_telemetry(
    run_stats: &mut stats_output::RunStatistics,
    stats: ay_sat::PreprocessTransactionStats,
) {
    run_stats.insert("sat.preprocess_tx_started", stats.started);
    run_stats.insert("sat.preprocess_tx_attempted", stats.started);
    run_stats.insert("sat.preprocess_tx_committed", stats.committed);
    run_stats.insert("sat.preprocess_tx_rolled_back", stats.rolled_back);
    run_stats.insert("sat.preprocess_tx_fail_closed", stats.fail_closed);
    run_stats.insert("sat.preprocess_tx_rejected", stats.fail_closed);
    run_stats.insert(
        "sat.preprocess_tx_proof_obligation_not_required",
        stats.proof_obligation_not_required,
    );
    run_stats.insert(
        "sat.preprocess_tx_proof_obligation_satisfied",
        stats.proof_obligation_satisfied,
    );
    run_stats.insert(
        "sat.preprocess_tx_proof_obligation_rejected",
        stats.proof_obligation_rejected,
    );
    run_stats.insert(
        "sat.preprocess_tx_proof_obligation_pending",
        stats.proof_obligation_pending,
    );
    run_stats.insert(
        "sat.preprocess_tx_reconstruction_witness_not_applicable",
        stats.reconstruction_witness_not_applicable,
    );
    run_stats.insert(
        "sat.preprocess_tx_reconstruction_witness_present",
        stats.reconstruction_witness_present,
    );
    run_stats.insert(
        "sat.preprocess_tx_reconstruction_witness_missing",
        stats.reconstruction_witness_missing,
    );
    run_stats.insert(
        "sat.preprocess_tx_touched_variables_total",
        stats.touched_variables_total,
    );
    run_stats.insert(
        "sat.preprocess_tx_eliminated_variables_total",
        stats.eliminated_variables_total,
    );
    run_stats.insert(
        "sat.preprocess_tx_equivalent_variables_total",
        stats.equivalent_variables_total,
    );
    run_stats.insert(
        "sat.preprocess_tx_planned_substitutions_total",
        stats.planned_substitutions_total,
    );
    run_stats.insert(
        "sat.preprocess_tx_max_mutation_epoch",
        stats.max_mutation_epoch,
    );
    run_stats.insert("sat.preprocess_tx_active", stats.active_transactions);
    run_stats.insert(
        "sat.preprocess_tx_retained_completed",
        stats.retained_completed,
    );
    run_stats.insert(
        "sat.preprocess_tx_fail_closed_model_reconstruction_witness_missing",
        stats.fail_closed_model_reconstruction_witness_missing,
    );
    run_stats.insert(
        "sat.preprocess_tx_fail_closed_decompose_lrat_preflight_rejected",
        stats.fail_closed_decompose_lrat_preflight_rejected,
    );
    run_stats.insert(
        "sat.preprocess_tx_fail_closed_decompose_lrat_clamped_after_dry_run",
        stats.fail_closed_decompose_lrat_clamped_after_dry_run,
    );
    run_stats.insert(
        "sat.preprocess_tx_fail_closed_other",
        stats.fail_closed_other,
    );
    run_stats.insert(
        "sat.preprocess_tx_rolled_back_other",
        stats.rolled_back_other,
    );
}

fn insert_decompose_lrat_preflight_telemetry(
    run_stats: &mut stats_output::RunStatistics,
    stats: &ay_sat::DecomposeLratPreflightStats,
) {
    insert_decompose_lrat_preflight_telemetry_body(run_stats, stats);
}
