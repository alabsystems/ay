// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn insert_empty_multiplier_equiv_shape_stats(
    run_stats: &mut stats_output::RunStatistics,
    blocker_code: u64,
) {
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_SCHEMA_VERSION_KEY, 1);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_TARGET_ISSUE_KEY, 9725);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_ADMISSION_ISSUE_KEY,
        9733,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_CONSERVATION_ISSUE_KEY,
        9736,
    );
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_OFFICIAL_ROW_COUNT_KEY, 12);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_NUM_VARS_KEY, 0);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_NUM_CLAUSES_KEY, 0);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENABLED_KEY, 0);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_EXERCISED_KEY, 0);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_OFFICIAL_SHAPE_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_STRUCTURAL_CANDIDATE_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_DIAGNOSTIC_CANDIDATE_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_FAIL_CLOSED_KEY,
        u64::from(blocker_code != 0),
    );
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_GATE_AND_KEY, 0);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_GATE_XOR_KEY, 0);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_GATES_TOTAL_KEY, 0);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PARTIAL_PRODUCT_ROWS_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_COMPRESSOR_LAYER_ROWS_KEY,
        0,
    );
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_OBLIGATION_ROWS_KEY, 0);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BOUND_ROWS_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BINDINGS_MISSING_KEY,
        0,
    );
}

fn insert_empty_multiplier_equiv_authority_stats(
    run_stats: &mut stats_output::RunStatistics,
    blocker_code: u64,
) {
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_REFERENCES_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BOUND_REFERENCES_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BINDING_MISSING_REFERENCES_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_DUPLICATE_REFERENCES_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_OUT_OF_RANGE_REFERENCES_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_LITERAL_MISMATCH_REFERENCES_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_COMMON_PRODUCT_WITNESS_ROWS_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_MITER_DISEQUALITY_ROWS_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_BLOCKER_CODE_KEY,
        blocker_code,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REJECTION_CODE_KEY,
        0,
    );
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_ADMITTED_KEY, 0);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_RESULT_AUTHORITY_KEY, 0);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_OUTPUT_AUTHORITY_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_REPLAY_CHECKED_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_EXTERNAL_CHECKER_VERIFIED_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_ARTIFACT_PRESENT_KEY,
        0,
    );
}

fn insert_empty_multiplier_equiv_conservation_scout_stats_body(
    run_stats: &mut stats_output::RunStatistics,
    blocker_code: u64,
) {
    insert_empty_multiplier_equiv_shape_stats(run_stats, blocker_code);
    insert_empty_multiplier_equiv_authority_stats(run_stats, blocker_code);
}
