// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn insert_multiplier_equiv_shape_stats(
    run_stats: &mut stats_output::RunStatistics,
    formula: &ay_sat::DimacsFormula,
) {
    let diagnostic = formula.multiplier_equivalence_conservation_diagnostic();
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCHEMA_VERSION_KEY,
        u64::from(diagnostic.schema_version),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_TARGET_ISSUE_KEY,
        u64::from(diagnostic.target_issue),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_ADMISSION_ISSUE_KEY,
        u64::from(diagnostic.lean_admission_contract_issue),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_CONSERVATION_ISSUE_KEY,
        u64::from(diagnostic.lean_conservation_contract_issue),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_OFFICIAL_ROW_COUNT_KEY,
        u64::from(diagnostic.official_row_count),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_NUM_VARS_KEY,
        diagnostic.num_vars as u64,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_NUM_CLAUSES_KEY,
        diagnostic.num_clauses as u64,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENABLED_KEY,
        u64::from(diagnostic.diagnostic_candidate),
    );
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_EXERCISED_KEY, 1);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_OFFICIAL_SHAPE_KEY,
        u64::from(diagnostic.official_shape_candidate),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_STRUCTURAL_CANDIDATE_KEY,
        u64::from(diagnostic.structural_candidate),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_DIAGNOSTIC_CANDIDATE_KEY,
        u64::from(diagnostic.diagnostic_candidate),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_FAIL_CLOSED_KEY,
        u64::from(diagnostic.fail_closed),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_GATE_AND_KEY,
        diagnostic.gate_and,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_GATE_XOR_KEY,
        diagnostic.gate_xor,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_GATES_TOTAL_KEY,
        diagnostic.gates_total,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PARTIAL_PRODUCT_ROWS_KEY,
        diagnostic.partial_product_rows,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_COMPRESSOR_LAYER_ROWS_KEY,
        diagnostic.compressor_layer_rows,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_OBLIGATION_ROWS_KEY,
        diagnostic.weighted_conservation_obligation_rows,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BOUND_ROWS_KEY,
        diagnostic.source_clause_bound_rows,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BINDINGS_MISSING_KEY,
        diagnostic.source_clause_bindings_missing,
    );
}

fn insert_multiplier_equiv_authority_stats(
    run_stats: &mut stats_output::RunStatistics,
    formula: &ay_sat::DimacsFormula,
) {
    let diagnostic = formula.multiplier_equivalence_conservation_diagnostic();
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_REFERENCES_KEY,
        diagnostic.source_gate_clause_references,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BOUND_REFERENCES_KEY,
        diagnostic.source_gate_clause_bound_references,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BINDING_MISSING_REFERENCES_KEY,
        diagnostic.source_gate_clause_binding_missing_references,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_DUPLICATE_REFERENCES_KEY,
        diagnostic.source_gate_clause_duplicate_references,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_OUT_OF_RANGE_REFERENCES_KEY,
        diagnostic.source_gate_clause_out_of_range_references,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_LITERAL_MISMATCH_REFERENCES_KEY,
        diagnostic.source_gate_clause_literal_mismatch_references,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_COMMON_PRODUCT_WITNESS_ROWS_KEY,
        diagnostic.common_product_witness_rows,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_MITER_DISEQUALITY_ROWS_KEY,
        diagnostic.miter_disequality_rows,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_BLOCKER_CODE_KEY,
        diagnostic.route_blocker_code,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REJECTION_CODE_KEY,
        diagnostic.scout_rejection_code,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_ADMITTED_KEY,
        u64::from(diagnostic.route_admitted),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_RESULT_AUTHORITY_KEY,
        u64::from(diagnostic.result_authority),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_OUTPUT_AUTHORITY_KEY,
        u64::from(diagnostic.proof_output_authority),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_REPLAY_CHECKED_KEY,
        u64::from(diagnostic.proof_replay_checked),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_EXTERNAL_CHECKER_VERIFIED_KEY,
        u64::from(diagnostic.external_checker_verified),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_ARTIFACT_PRESENT_KEY,
        u64::from(diagnostic.proof_artifact_present),
    );
}

fn insert_multiplier_equiv_conservation_scout_stats_body(
    run_stats: &mut stats_output::RunStatistics,
    source: DimacsInputSource<'_>,
) {
    let requested = ay_core::sat_ab_switches().multiplier_equiv_conservation_scout;
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REQUESTED_KEY,
        u64::from(requested),
    );
    if !requested {
        insert_empty_multiplier_equiv_conservation_scout_stats(run_stats, 0);
        return;
    }
    let Some(content) = dimacs_source_text_for_scout(source) else {
        insert_empty_multiplier_equiv_conservation_scout_stats(run_stats, 99);
        return;
    };
    let Ok(formula) = parse_dimacs(&content) else {
        insert_empty_multiplier_equiv_conservation_scout_stats(run_stats, 98);
        return;
    };
    insert_multiplier_equiv_shape_stats(run_stats, &formula);
    insert_multiplier_equiv_authority_stats(run_stats, &formula);
}
