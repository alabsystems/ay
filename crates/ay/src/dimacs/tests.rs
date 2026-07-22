//! Unit tests for `super` (dimacs.rs).
//! Extracted verbatim to keep the production module readable.

#[cfg(target_os = "linux")]
use super::{
    anonymous_dimacs_staging_is_unsupported, cleanup_dense_clique_php_route_rejection_proof,
    cleanup_dimacs_non_unsat_proof_sidecar, create_owned_dimacs_proof_file,
    dimacs_proof_status_lock_path, dimacs_proof_status_path,
    inject_anonymous_dimacs_staging_error_once, inject_dimacs_proof_cleanup_failure_once,
    inject_dimacs_proof_cleanup_replacement_once, inject_dimacs_proof_clone_failure_once,
    inject_dimacs_proof_identity_failure_once, inject_dimacs_rename_noreplace_error_once,
    inject_dimacs_status_lock_identity_failure_once, inject_optional_dimacs_writer_failure_once,
    mark_synthesized_default_dimacs_proof_current, mark_synthesized_default_dimacs_proof_stale,
    owned_dimacs_proof_write_failure_flag, proof_output_writer,
    publish_dimacs_descriptor_noreplace, read_published_dimacs_proof, remove_owned_dimacs_proof,
    rename_dimacs_noreplace, retain_published_dimacs_proof, seal_owned_dimacs_proof,
    DimacsPublicationInvalidation, DimacsUnsatPublicationTransaction, RetainedDimacsPublication,
    SolverDimacsProofWriter, DIMACS_PROOF_STAGING_PREFIX,
};
use super::{
    checked_lrat_original_clause_count, clique_n2_k10_original_order_witness,
    configure_dimacs_solver, create_configured_dimacs_proof_file, dense_clique_php_route_admission,
    dense_clique_php_route_checker_audit_counts_match, dense_clique_php_route_target_clauses,
    dimacs_clause_fingerprint, dimacs_run_stats_json, dimacs_timeout_exit_code_for_policy,
    emit_dimacs_sat_model_to_writer, insert_decompose_lrat_preflight_telemetry,
    insert_dense_clique_scout_stats, insert_multiplier_equiv_conservation_scout_stats,
    insert_preprocessing_transaction_telemetry, php_functional_5_4_original_order_witness,
    read_authenticated_dimacs_source, sha256_digest, should_enable_xor_extension,
    variant_input_for_dimacs, variant_input_for_dimacs_route, verification_skip_is_acceptable,
    AuthenticatedLeanSnapshot, DenseCliquePhpProofRouteAdmissionResult, DimacsInputSource,
    CLIQUE_N2_K10_CLAUSE_FINGERPRINT, CLIQUE_N2_K10_EXPECTED_CHECKER_AUDIT_STATS,
    DIMACS_MODEL_LINE_LIMIT, DIMACS_TIMEOUT_EXIT_CODE, PHP_FUNCTIONAL_5_4_CLAUSE_FINGERPRINT,
    SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENABLED_KEY,
    SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENV,
    SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENABLED_KEY,
    SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENV,
    SAT_BCP_LEARNED_18_TAIL_REORDER_CANDIDATES_KEY, SAT_BCP_LEARNED_18_TAIL_REORDER_CHANGED_KEY,
    SAT_BCP_LEARNED_18_TAIL_REORDER_ENABLED_KEY, SAT_BCP_LEARNED_18_TAIL_REORDER_EXERCISED_KEY,
    SAT_BCP_LEARNED_18_TAIL_REORDER_SWAPS_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_AFFECTED_FSW_ROWS_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_CANDIDATES_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELIDED_SUFFIX_SLOTS_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISIONS_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECTS_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTIONS_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_MISMATCH_DEMOTIONS_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_POPULATES_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_REPEAT_REJECTS_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_AFFECTED_FSW_ROWS_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ELIDED_SUFFIX_SLOTS_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_HITS_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_MISMATCHES_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_STALE_REJECTS_KEY,
    SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_CONFLICT_KEY,
    SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ELIGIBLE_KEY,
    SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENV,
    SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_WRITES_KEY,
    SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_APPLIED_KEY,
    SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_CANDIDATES_KEY,
    SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENABLED_KEY, SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENV,
    SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_PREFIX_KEY,
    SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_SUFFIX_KEY,
    SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_PREFIX_KEY,
    SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_SUFFIX_KEY,
    SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_CONFLICT_KEY,
    SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_UNIT_KEY,
    SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_SAVED_SLOTS_KEY, SAT_BCP_LEARNED_1963_IDENTITY_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_IDENTITY_ENV, SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENV,
    SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENV,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_APPLIED_KEY,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_CANDIDATES_KEY,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SKIPPED_OVER_BUDGET_KEY,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_APPLIED_KEY,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_SKIPPED_KEY,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_CANDIDATES_KEY,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_CHANGED_KEY, SAT_BCP_LEARNED_1963_TAIL_REORDER_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAPS_KEY,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENV,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_LIMIT_KEY,
    SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY,
    SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_MOVES_KEY,
    SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_CONFLICT_KEY,
    SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ELIGIBLE_KEY,
    SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENV,
    SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_UNIT_KEY,
    SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_WRITES_KEY,
    SAT_BCP_LEARNED_617_TAIL_REORDER_CANDIDATES_KEY, SAT_BCP_LEARNED_617_TAIL_REORDER_CHANGED_KEY,
    SAT_BCP_LEARNED_617_TAIL_REORDER_ENABLED_KEY, SAT_BCP_LEARNED_617_TAIL_REORDER_EXERCISED_KEY,
    SAT_BCP_LEARNED_617_TAIL_REORDER_SWAPS_KEY,
    SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY,
    SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ENABLED_KEY,
    SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_MOVES_KEY,
    SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE_ENABLED_KEY,
    SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENABLED_KEY,
    SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENV,
    SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENABLED_KEY, SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENV,
    SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_EXERCISED_KEY,
    SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_REQUESTED_KEY, SAT_BOUNDED_BACKBONE_BACKOFF_TRIGGERS_KEY,
    SAT_BOUNDED_BACKBONE_BINARY_SUPPRESSED_KEY, SAT_BOUNDED_BACKBONE_MS_KEY,
    SAT_BOUNDED_BACKBONE_RUNS_KEY, SAT_BOUNDED_BACKBONE_YIELDS_KEY,
    SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENABLED_KEY,
    SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENV, SAT_BVE_LRAT_SCOUT_ROUTE_ENV,
    SAT_DENSE_CLIQUE_MAB_BRANCH_ENABLED_KEY, SAT_DENSE_CLIQUE_MAB_BRANCH_ENV,
    SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISED_KEY, SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISE_COUNT_KEY,
    SAT_DENSE_CLIQUE_MAB_BRANCH_REQUESTED_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_ALO_ROWS_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_MUTEX_ROWS_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTENSION_ROWS_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTERNAL_CHECKER_VERIFIED_ROWS_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_ROWS_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_ALO_ROWS_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_MUTEX_ROWS_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ENABLED_KEY, SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXERCISED_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXTENSION_CLAUSES_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_FINGERPRINT_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_OBLIGATION_ROWS_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ORIGINAL_ORDER_WITNESS_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_BYTES_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_PRESENT_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_REQUESTED_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_RAW_LITERALS_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_ROWS_KEY, SAT_DENSE_CLIQUE_SCOUT_COLORS_KEY,
    SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MULTIPARTITE_KEY, SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MUTEX_KEY,
    SAT_DENSE_CLIQUE_SCOUT_ENABLED_KEY, SAT_DENSE_CLIQUE_SCOUT_ENV,
    SAT_DENSE_CLIQUE_SCOUT_EXERCISED_KEY, SAT_DENSE_CLIQUE_SCOUT_EXPECTED_MUTEXES_KEY,
    SAT_DENSE_CLIQUE_SCOUT_GRAPH_EDGES_KEY, SAT_DENSE_CLIQUE_SCOUT_GRAPH_NON_EDGES_KEY,
    SAT_DENSE_CLIQUE_SCOUT_MUTEXES_KEY, SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKETS_KEY,
    SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MAX_KEY, SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MIN_KEY,
    SAT_DENSE_CLIQUE_SCOUT_OTHER_CLAUSES_KEY, SAT_DENSE_CLIQUE_SCOUT_PHP_HOLES_KEY,
    SAT_DENSE_CLIQUE_SCOUT_PHP_PIGEONS_KEY, SAT_DENSE_CLIQUE_SCOUT_PHP_UNSAT_OBLIGATION_KEY,
    SAT_DENSE_CLIQUE_SCOUT_REJECTION_CODE_KEY, SAT_DENSE_CLIQUE_SCOUT_REQUESTED_KEY,
    SAT_DENSE_CLIQUE_SCOUT_SUPPORT_CLAUSES_KEY, SAT_DENSE_CLIQUE_SCOUT_SUPPORT_WIDTH_KEY,
    SAT_DENSE_CLIQUE_SCOUT_VERTICES_KEY, SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_BINARY_CLAUSES_KEY,
    SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_CLAUSES_KEY,
    SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_VARS_KEY,
    SAT_DENSE_MUTEX_FOCUSED_RESTART_COMPUTED_GATE_KEY,
    SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENABLED_KEY, SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV,
    SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_REQUESTED_KEY,
    SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_UPDATES_KEY,
    SAT_DENSE_MUTEX_FOCUSED_RESTART_PREVIOUS_GATE_KEY,
    SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CANDIDATE_KEY,
    SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CHECKED_KEY,
    SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE_ENV, SAT_FOCUSED_RESTART_GATE_FINAL_KEY,
    SAT_HARD_TAIL_ROW_ID_ENV, SAT_INPROCESSING_LRAT_CLAMPED_BVE_DUE_ROUNDS_KEY,
    SAT_INPROCESSING_LRAT_CLAMPED_FACTOR_DUE_ROUNDS_KEY,
    SAT_INPROCESSING_LRAT_PROBE_RESCUE_ROUNDS_KEY, SAT_INPROCESSING_YIELD_PRODUCTIVITY_RESCUE_ENV,
    SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENABLED_KEY,
    SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENV,
    SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENABLED_KEY, SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENV,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_EXTERNAL_CHECKER_VERIFIED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_ADMISSION_ISSUE_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_CONSERVATION_ISSUE_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_OBLIGATION_ROWS_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_OUTPUT_AUTHORITY_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_REPLAY_CHECKED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_RESULT_AUTHORITY_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_ADMITTED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENABLED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENV,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_EXERCISED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_FAIL_CLOSED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REQUESTED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BINDINGS_MISSING_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BOUND_ROWS_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BINDING_MISSING_REFERENCES_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BOUND_REFERENCES_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_DUPLICATE_REFERENCES_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_LITERAL_MISMATCH_REFERENCES_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_OUT_OF_RANGE_REFERENCES_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_REFERENCES_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_TARGET_ISSUE_KEY, XOR_EXTENSION_MAX_CLAUSES,
};
use crate::{stats_output, ProofConfig, ProofFormat, TIMED_OUT, VERDICT_PRINTED};
use ay_sat::{
    Literal, ProofOutput, SatResult, Solver as SatSolver, SolverVariant, Variable,
    VariantRouteProfile, VariantStartupPolicy,
};
use ay_test_support::env::{lock_env, ScopedEnvVar};
use std::io::{BufWriter, Write as _};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::Ordering;
use std::time::Duration;

fn render_dimacs_sat_model_for_test(model: &[bool]) -> String {
    let mut output = Vec::new();
    emit_dimacs_sat_model_to_writer(model, &mut output)
        .expect("DIMACS SAT model rendering should succeed");
    String::from_utf8(output).expect("DIMACS SAT model rendering should be UTF-8")
}

#[test]
fn proof_mode_rejects_unrepresentable_lrat_header_count() {
    let over = usize::try_from(ay_sat::MAX_LRAT_ORIGINAL_CLAUSES + 1)
        .expect("test requires a 64-bit usize");
    let error = checked_lrat_original_clause_count(over)
        .expect_err("LRAT header must be rejected before writer construction");

    assert!(
        error.to_string().contains("LRAT original-clause"),
        "{error}"
    );
}

#[test]
fn test_dimacs_sat_model_writer_preserves_small_model_format() {
    assert_eq!(
        render_dimacs_sat_model_for_test(&[true, false, true]),
        "v 1 -2 3 0\n"
    );
}

#[test]
fn test_dimacs_sat_model_writer_wraps_without_losing_literals() {
    let model = (0..5000).map(|index| index % 3 != 1).collect::<Vec<_>>();
    let rendered = render_dimacs_sat_model_for_test(&model);
    let mut observed = Vec::with_capacity(model.len());

    for line in rendered.lines() {
        assert!(line.starts_with('v'));
        assert!(line.len() <= DIMACS_MODEL_LINE_LIMIT);
        for token in line.split_whitespace().skip(1) {
            if token == "0" {
                continue;
            }
            observed.push(token.parse::<i32>().expect("valid DIMACS literal"));
        }
    }

    let expected = model
        .iter()
        .enumerate()
        .map(|(index, &value)| {
            let var = i32::try_from(index + 1).expect("test variable fits i32");
            if value {
                var
            } else {
                -var
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(observed, expected);
    assert!(rendered.ends_with(" 0\n"));
}

/// Build a clause list with given clause size distribution.
/// `binary_count` clauses of length 2, `ternary_count` clauses of length 3.
fn make_clauses(binary_count: usize, ternary_count: usize) -> Vec<Vec<Literal>> {
    make_clauses_mixed(binary_count, ternary_count, 0)
}

/// Build a clause list with binary, ternary, and larger clauses.
/// `large_count` clauses of length 5 (breaks the gate-structure pattern).
fn make_clauses_mixed(
    binary_count: usize,
    ternary_count: usize,
    large_count: usize,
) -> Vec<Vec<Literal>> {
    let a = Literal::positive(Variable::new(0));
    let b = Literal::negative(Variable::new(1));
    let c = Literal::positive(Variable::new(2));
    let d = Literal::negative(Variable::new(3));
    let e = Literal::positive(Variable::new(4));
    let mut clauses = Vec::with_capacity(binary_count + ternary_count + large_count);
    for _ in 0..binary_count {
        clauses.push(vec![a, b]);
    }
    for _ in 0..ternary_count {
        clauses.push(vec![a, b, c]);
    }
    for _ in 0..large_count {
        clauses.push(vec![a, b, c, d, e]);
    }
    clauses
}

#[test]
fn test_variant_input_for_dimacs_records_dense_mutex_restart_env_request() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV);

    let default_input =
        variant_input_for_dimacs(SolverVariant::Default, 180, 3_160, true, true, true);
    assert!(
        !default_input.dense_mutex_focused_restart_gate_experiment,
        "dense-mutex focused restart route must be default-off"
    );

    let _guard = ScopedEnvVar::set(SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV, "1");
    let requested_input =
        variant_input_for_dimacs(SolverVariant::Default, 180, 3_160, true, true, true);
    assert!(
        requested_input.dense_mutex_focused_restart_gate_experiment,
        "truthy DIMACS env should record the dense-mutex focused restart route request"
    );
}

#[test]
fn test_variant_input_for_dimacs_records_dense_clique_mab_branch_env_request() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_DENSE_CLIQUE_MAB_BRANCH_ENV);

    let default_input =
        variant_input_for_dimacs(SolverVariant::Default, 180, 3_160, true, true, true);
    assert!(
        !default_input.dense_clique_mab_branch_experiment,
        "dense-clique MAB branch route must be default-off"
    );

    let _guard = ScopedEnvVar::set(SAT_DENSE_CLIQUE_MAB_BRANCH_ENV, "1");
    let requested_input =
        variant_input_for_dimacs(SolverVariant::Default, 180, 3_160, true, true, true);
    assert!(
        requested_input.dense_clique_mab_branch_experiment,
        "truthy DIMACS env should record the dense-clique MAB branch route request"
    );
}

#[test]
fn test_variant_input_for_dimacs_bve_lrat_scout_route_env_default_off() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_BVE_LRAT_SCOUT_ROUTE_ENV);
    let _guard = ScopedEnvVar::set("AY_SAT_PROFILE_ID", "ay-sat-regular-main");

    let input = variant_input_for_dimacs(SolverVariant::Default, 180, 3_160, true, true, true);

    assert_eq!(
        input.route_profile,
        VariantRouteProfile::OfficialSatCompMainLrat
    );
    assert!(
        !input.bve_lrat_scout_route,
        "Main/LRAT BVE scout route env hook must be default-off"
    );
}

#[test]
fn test_variant_input_for_dimacs_bve_lrat_scout_route_env_official_only() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::set(SAT_BVE_LRAT_SCOUT_ROUTE_ENV, "1");
    let _guard = ScopedEnvVar::set("AY_SAT_PROFILE_ID", "ay-sat-regular-main");

    let official = variant_input_for_dimacs(SolverVariant::Default, 180, 3_160, true, true, true);
    assert_eq!(
        official.route_profile,
        VariantRouteProfile::OfficialSatCompMainLrat
    );
    assert!(
        official.bve_lrat_scout_route,
        "truthy DIMACS env should request the official Main/LRAT BVE scout route"
    );

    let non_official = variant_input_for_dimacs_route(
        SolverVariant::Default,
        180,
        3_160,
        true,
        true,
        true,
        false,
        false,
    );
    assert_eq!(non_official.route_profile, VariantRouteProfile::Standard);
    assert!(
        !non_official.bve_lrat_scout_route,
        "route helper must keep the BVE scout flag off without the official wrapper shape"
    );

    let internal_lrat_export =
        variant_input_for_dimacs(SolverVariant::Default, 180, 3_160, true, true, false);
    assert_eq!(
        internal_lrat_export.route_profile,
        VariantRouteProfile::Standard
    );
    assert!(
        !internal_lrat_export.bve_lrat_scout_route,
        "env hook must not enable the route for internal LRAT export without LRAT output"
    );

    let aggressive =
        variant_input_for_dimacs(SolverVariant::Aggressive, 180, 3_160, true, true, true);
    assert_eq!(aggressive.route_profile, VariantRouteProfile::Standard);
    assert!(
        !aggressive.bve_lrat_scout_route,
        "env hook must not enable the route outside default variant"
    );
}

#[test]
fn test_variant_input_for_dimacs_fmla_decompose_lrat_preflight_env_default_off() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE_ENV);
    let _guard = ScopedEnvVar::set("AY_SAT_PROFILE_ID", "ay-sat-regular-main");

    let input = variant_input_for_dimacs(SolverVariant::Default, 180, 3_160, true, true, true);

    assert_eq!(
        input.route_profile,
        VariantRouteProfile::OfficialSatCompMainLrat
    );
    assert!(
        !input.fmla_decompose_lrat_preflight_route,
        "Main/LRAT Fmla decompose preflight route env hook must be default-off"
    );
}

#[test]
fn test_variant_input_for_dimacs_fmla_decompose_lrat_preflight_env_official_only() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::set(SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE_ENV, "1");
    let _guard = ScopedEnvVar::set("AY_SAT_PROFILE_ID", "ay-sat-regular-main");

    let official = variant_input_for_dimacs(SolverVariant::Default, 180, 3_160, true, true, true);
    assert_eq!(
        official.route_profile,
        VariantRouteProfile::OfficialSatCompMainLrat
    );
    assert!(
        official.fmla_decompose_lrat_preflight_route,
        "truthy DIMACS env should request the official Main/LRAT Fmla preflight route"
    );

    let non_official = variant_input_for_dimacs_route(
        SolverVariant::Default,
        180,
        3_160,
        true,
        true,
        true,
        false,
        false,
    );
    assert_eq!(non_official.route_profile, VariantRouteProfile::Standard);
    assert!(
        !non_official.fmla_decompose_lrat_preflight_route,
        "route helper must keep the Fmla preflight flag off without official wrapper shape"
    );

    let internal_lrat_export =
        variant_input_for_dimacs(SolverVariant::Default, 180, 3_160, true, true, false);
    assert_eq!(
        internal_lrat_export.route_profile,
        VariantRouteProfile::Standard
    );
    assert!(
        !internal_lrat_export.fmla_decompose_lrat_preflight_route,
        "env hook must not enable the route for internal LRAT export without LRAT output"
    );

    let aggressive =
        variant_input_for_dimacs(SolverVariant::Aggressive, 180, 3_160, true, true, true);
    assert_eq!(aggressive.route_profile, VariantRouteProfile::Standard);
    assert!(
        !aggressive.fmla_decompose_lrat_preflight_route,
        "env hook must not enable the route outside default variant"
    );
}

#[test]
fn test_configure_dimacs_solver_search_inplace_watch_scan_default_on() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );

    // The in-place SEARCH BCP route is default-on (cold.rs), verified
    // bit-identical to the safe path by `propagation_bcp_unsafe.rs`. Without an
    // env override it stays on; the route runs in `raw-pointer-bcp` builds (which is
    // a default feature).
    assert!(
        solver.bcp_search_inplace_watch_scan_enabled(),
        "SEARCH in-place watch scan is default-on without an env override"
    );
    assert_eq!(
        solver.bcp_search_inplace_watch_scan_route_enabled(),
        cfg!(feature = "raw-pointer-bcp"),
        "route runs only in raw-pointer-bcp builds (a default feature)"
    );
    assert!(!solver.bcp_search_inplace_watch_scan_exercised());
}

#[test]
fn test_configure_dimacs_solver_search_inplace_watch_scan_env_kill_switch() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::set(SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENV, "0");

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );

    // Kill-switch: `=0` forces the solver back onto the safe deferred-copy route
    // off the default-on in-place path, in any build.
    assert!(
        !solver.bcp_search_inplace_watch_scan_enabled(),
        "AY_SAT_BCP_SEARCH_INPLACE_WATCH_SCAN=0 must disable the in-place route"
    );
    assert!(!solver.bcp_search_inplace_watch_scan_route_enabled());
}

#[test]
fn test_configure_dimacs_solver_search_inplace_watch_scan_env_gate_truthy() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::set(SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENV, "1");

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );

    assert!(
        solver.bcp_search_inplace_watch_scan_enabled(),
        "truthy env should request the SEARCH in-place watch scan route"
    );
    assert_eq!(
        solver.bcp_search_inplace_watch_scan_route_enabled(),
        cfg!(feature = "raw-pointer-bcp"),
        "route can only be enabled in raw-pointer-bcp builds"
    );
}

#[test]
fn test_configure_dimacs_solver_scan_pressure_env_gate_default_off() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );

    assert!(
        !solver.bcp_learned_no_replacement_scan_pressure_enabled(),
        "learned no-replacement scan-pressure profiling must stay default-off"
    );
}

#[test]
fn test_configure_dimacs_solver_scan_pressure_env_gate_truthy() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::set(SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENV, "1");

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );

    assert!(
        solver.bcp_learned_no_replacement_scan_pressure_enabled(),
        "truthy DIMACS env should expose #9297 scan-pressure profiling"
    );
}

#[test]
fn test_configure_dimacs_solver_learned_1963_identity_env_gate() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_BCP_LEARNED_1963_IDENTITY_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.bcp_learned_1963_identity_profile_enabled(),
        "learned 19-63 identity profiling must stay default-off"
    );

    let _guard = ScopedEnvVar::set(SAT_BCP_LEARNED_1963_IDENTITY_ENV, "1");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.bcp_learned_1963_identity_profile_enabled(),
        "truthy DIMACS env should enable learned 19-63 identity profiling"
    );
}

#[test]
fn test_configure_dimacs_solver_learned_1963_pressure_reduction_env_gate() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENV);
    let _guard = ScopedEnvVar::unset(SAT_BCP_LEARNED_1963_IDENTITY_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.bcp_learned_1963_pressure_reduction_enabled(),
        "learned 19-63 pressure reduction must stay default-off"
    );
    assert!(
        !solver.bcp_learned_1963_identity_profile_enabled(),
        "pressure reduction default-off must not enable identity profiling"
    );

    let _guard = ScopedEnvVar::set(SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENV, "1");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.bcp_learned_1963_pressure_reduction_enabled(),
        "truthy DIMACS env should enable learned 19-63 pressure reduction"
    );
    assert!(
        solver.bcp_learned_1963_identity_profile_enabled(),
        "pressure reduction needs exact identity rows as its pressure source"
    );
}

#[test]
fn test_configure_dimacs_solver_learned_1963_pressure_retention_env_gate() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENV);
    let _guard = ScopedEnvVar::unset(SAT_BCP_LEARNED_1963_IDENTITY_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.bcp_learned_1963_pressure_retention_enabled(),
        "learned 19-63 pressure retention must stay default-off"
    );
    assert!(
        !solver.bcp_learned_1963_identity_profile_enabled(),
        "pressure retention default-off must not enable identity profiling"
    );

    let _guard = ScopedEnvVar::set(SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENV, "1");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.bcp_learned_1963_pressure_retention_enabled(),
        "truthy DIMACS env should enable learned 19-63 pressure retention"
    );
    assert!(
        solver.bcp_learned_1963_identity_profile_enabled(),
        "pressure retention needs exact identity rows as its pressure source"
    );
}

#[test]
fn test_configure_dimacs_solver_used5_fsw_reset_env_gate() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(),
        "learned 19-63 used5 FSW reset must stay default-off"
    );

    let _guard = ScopedEnvVar::set(SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENV, "1");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(),
        "truthy DIMACS env should enable the used5 FSW reset"
    );
}

#[test]
fn test_configure_dimacs_solver_fsw_conflict_saved_pos_reset_env_gate() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(),
        "learned 19-63 FSW conflict-only reset must stay default-off"
    );

    let _guard = ScopedEnvVar::set(SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENV, "1");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(),
        "truthy DIMACS env should enable the FSW conflict-only reset"
    );
}

#[test]
fn test_configure_dimacs_solver_fsw_gent_skip_env_gate() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.bcp_learned_1963_fsw_gent_skip_enabled(),
        "learned 19-63 FSW Gent-order skip must stay default-off"
    );

    let _guard = ScopedEnvVar::set(SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENV, "1");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.bcp_learned_1963_fsw_gent_skip_enabled(),
        "truthy DIMACS env should enable the FSW Gent-order skip"
    );
}

#[test]
fn test_configure_dimacs_solver_disable_1963_unit_blocker_refresh_env_gate() {
    let _lock = lock_env();
    let _guard =
        ScopedEnvVar::unset(SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.bcp_disable_learned_1963_no_replacement_unit_blocker_refresh_enabled(),
        "learned 19-63 no-replacement unit blocker-refresh guard must stay default-off"
    );

    let _guard = ScopedEnvVar::set(
        SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENV,
        "1",
    );
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.bcp_disable_learned_1963_no_replacement_unit_blocker_refresh_enabled(),
        "truthy DIMACS env should enable the learned 19-63 unit blocker-refresh guard"
    );
}

#[test]
fn test_configure_dimacs_solver_1963_tail_reorder_swap_budget_env_gate() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert_eq!(
        solver.bcp_learned_1963_tail_reorder_swap_budget(),
        None,
        "learned 19-63 budgeted tail reorder must stay default-off"
    );

    let _guard = ScopedEnvVar::set(SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENV, "256");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert_eq!(
        solver.bcp_learned_1963_tail_reorder_swap_budget(),
        Some(256),
        "DIMACS env should configure the learned 19-63 tail reorder swap budget"
    );
}

#[test]
fn test_configure_dimacs_solver_inprocessing_yield_productivity_rescue_env_gate() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_INPROCESSING_YIELD_PRODUCTIVITY_RESCUE_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.inprocessing_yield_productivity_rescue_enabled(),
        "the #9084 yield-productivity rescue must stay default-off"
    );

    let _guard = ScopedEnvVar::set(SAT_INPROCESSING_YIELD_PRODUCTIVITY_RESCUE_ENV, "1");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.inprocessing_yield_productivity_rescue_enabled(),
        "truthy DIMACS env should enable the #9084 yield-productivity rescue"
    );
}

#[test]
fn test_configure_dimacs_solver_lrat_proof_clamp_probe_rescue_env_gate() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.lrat_proof_clamp_probe_rescue_enabled(),
        "LRAT proof-clamp probe rescue must stay default-off"
    );

    let _guard = ScopedEnvVar::set(SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENV, "1");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.lrat_proof_clamp_probe_rescue_enabled(),
        "truthy DIMACS env should enable the LRAT proof-clamp probe rescue"
    );
}

#[test]
fn test_configure_dimacs_solver_yield_rescue_backbone_cooldown_env_gate() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.inprocessing_yield_rescue_backbone_cooldown_enabled(),
        "the #9084 yield-rescue backbone cooldown must stay default-off"
    );

    let _guard = ScopedEnvVar::set(SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENV, "1");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.inprocessing_yield_rescue_backbone_cooldown_enabled(),
        "truthy DIMACS env should enable the #9084 backbone cooldown experiment"
    );
}

#[test]
fn test_configure_dimacs_solver_bounded_backbone_zero_decompose_backoff_env_gate() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.bounded_backbone_zero_decompose_backoff_enabled(),
        "the #9084 bounded-backbone zero-decompose backoff must stay default-off"
    );

    let _guard = ScopedEnvVar::set(SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENV, "1");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.bounded_backbone_zero_decompose_backoff_enabled(),
        "truthy DIMACS env should enable the #9084 bounded-only backoff experiment"
    );
}

#[test]
fn test_configure_dimacs_solver_backbone_post_vivify_binary_admission_env_gate() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENV);

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.backbone_post_vivify_binary_admission_enabled(),
        "post-vivify binary admission must stay default-on without env override"
    );

    let _guard = ScopedEnvVar::set(SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENV, "0");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.backbone_post_vivify_binary_admission_enabled(),
        "env 0 should restore the legacy post-vivify backbone gate"
    );

    let _guard = ScopedEnvVar::set(SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENV, "1");
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.backbone_post_vivify_binary_admission_enabled(),
        "env 1 should keep current post-vivify binary admission behavior"
    );
}

#[test]
fn test_dimacs_stats_json_exports_backbone_post_vivify_binary_admission_gate() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(1),
    );
    run_stats.insert(SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENABLED_KEY, 0);

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");
    assert_eq!(
        parsed[SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENABLED_KEY],
        serde_json::json!(false),
        "stats JSON should expose the post-vivify binary admission gate as a boolean"
    );
}

#[test]
fn test_dimacs_stats_json_exports_hard_tail_row_id() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::set(SAT_HARD_TAIL_ROW_ID_ENV, "Circuit_multiplier22");

    let run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(1),
    );

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::OfficialSatCompMainLrat);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");
    assert_eq!(
        parsed["hard_tail_row_id"],
        serde_json::json!("Circuit_multiplier22"),
        "top-level stats JSON should expose the wrapper-provided hard-tail row"
    );
    assert_eq!(
        parsed["sat_competition"]["hard_tail_row_id"],
        serde_json::json!("Circuit_multiplier22"),
        "SAT-COMP stats envelope should expose the wrapper-provided hard-tail row"
    );
    assert_eq!(
        parsed["sat_competition"]["route_profile"],
        serde_json::json!("official-satcomp-main-lrat"),
        "row-id stamping must not change the route profile"
    );
}

#[test]
fn test_dimacs_stats_json_exports_learned_lrat_snapshot_counters() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(7),
    );
    run_stats.insert("sat.shrink_singleton_fast_path_skips", 11);
    run_stats.insert("sat.lrat_original_learned_snapshot_copies", 7);
    run_stats.insert("sat.lrat_original_learned_snapshot_literals", 37);
    run_stats.insert("sat.lrat_original_learned_snapshot_singleton_skips", 5);
    run_stats.insert("sat.lrat_removed_literal_chain_calls", 3);

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed["sat.shrink_singleton_fast_path_skips"],
        serde_json::json!(11)
    );
    assert_eq!(
        parsed["sat.lrat_original_learned_snapshot_copies"],
        serde_json::json!(7)
    );
    assert_eq!(
        parsed["sat.lrat_original_learned_snapshot_literals"],
        serde_json::json!(37)
    );
    assert_eq!(
        parsed["sat.lrat_original_learned_snapshot_singleton_skips"],
        serde_json::json!(5)
    );
    assert_eq!(
        parsed["sat.lrat_removed_literal_chain_calls"],
        serde_json::json!(3)
    );
}

#[test]
fn test_dimacs_stats_json_exports_yield_rescue_backbone_cooldown_gate() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(1),
    );
    run_stats.insert(
        SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENABLED_KEY,
        1,
    );

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");
    assert_eq!(
        parsed[SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the yield-rescue backbone cooldown gate as a boolean"
    );
}

#[test]
fn test_dimacs_stats_json_exports_lrat_proof_clamp_probe_rescue_stats() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(1),
    );
    run_stats.insert(SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENABLED_KEY, 1);
    run_stats.insert(SAT_INPROCESSING_LRAT_CLAMPED_BVE_DUE_ROUNDS_KEY, 2);
    run_stats.insert(SAT_INPROCESSING_LRAT_CLAMPED_FACTOR_DUE_ROUNDS_KEY, 3);
    run_stats.insert(SAT_INPROCESSING_LRAT_PROBE_RESCUE_ROUNDS_KEY, 4);

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");
    assert_eq!(
        parsed[SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the LRAT proof-clamp probe-rescue gate as a boolean"
    );
    assert_eq!(
        parsed[SAT_INPROCESSING_LRAT_CLAMPED_BVE_DUE_ROUNDS_KEY],
        serde_json::json!(2),
        "stats JSON should expose LRAT proof-clamped BVE eligibility rounds"
    );
    assert_eq!(
        parsed[SAT_INPROCESSING_LRAT_CLAMPED_FACTOR_DUE_ROUNDS_KEY],
        serde_json::json!(3),
        "stats JSON should expose LRAT proof-clamped factor eligibility rounds"
    );
    assert_eq!(
        parsed[SAT_INPROCESSING_LRAT_PROBE_RESCUE_ROUNDS_KEY],
        serde_json::json!(4),
        "stats JSON should expose LRAT proof-clamp probe-rescue rounds"
    );
}

#[test]
fn test_dimacs_stats_json_exports_bounded_backbone_zero_decompose_backoff_stats() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(1),
    );
    run_stats.insert(SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENABLED_KEY, 1);
    run_stats.insert(SAT_BOUNDED_BACKBONE_BACKOFF_TRIGGERS_KEY, 2);
    run_stats.insert(SAT_BOUNDED_BACKBONE_RUNS_KEY, 3);
    run_stats.insert(SAT_BOUNDED_BACKBONE_YIELDS_KEY, 1);
    run_stats.insert(SAT_BOUNDED_BACKBONE_MS_KEY, 900);
    run_stats.insert(SAT_BOUNDED_BACKBONE_BINARY_SUPPRESSED_KEY, 0);

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");
    assert_eq!(
        parsed[SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the bounded-only backoff gate as a boolean"
    );
    assert_eq!(parsed[SAT_BOUNDED_BACKBONE_BACKOFF_TRIGGERS_KEY], 2);
    assert_eq!(parsed[SAT_BOUNDED_BACKBONE_RUNS_KEY], 3);
    assert_eq!(parsed[SAT_BOUNDED_BACKBONE_YIELDS_KEY], 1);
    assert_eq!(parsed[SAT_BOUNDED_BACKBONE_MS_KEY], 900);
    assert_eq!(
        parsed[SAT_BOUNDED_BACKBONE_BINARY_SUPPRESSED_KEY], 0,
        "bounded-only backoff must make binary suppression visible as zero"
    );
}

#[test]
fn test_dimacs_stats_json_exports_dense_mutex_restart_route_stats() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "sat",
        Duration::from_millis(7),
    );
    run_stats.insert(SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_REQUESTED_KEY, 1);
    run_stats.insert(SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENABLED_KEY, 1);
    run_stats.insert(SAT_FOCUSED_RESTART_GATE_FINAL_KEY, 45);
    run_stats.insert(SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_UPDATES_KEY, 1);
    run_stats.insert(SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CHECKED_KEY, 1);
    run_stats.insert(SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_VARS_KEY, 180);
    run_stats.insert(SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_CLAUSES_KEY, 3160);
    run_stats.insert(
        SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_BINARY_CLAUSES_KEY,
        3150,
    );
    run_stats.insert(SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CANDIDATE_KEY, 1);
    run_stats.insert(SAT_DENSE_MUTEX_FOCUSED_RESTART_PREVIOUS_GATE_KEY, 4);
    run_stats.insert(SAT_DENSE_MUTEX_FOCUSED_RESTART_COMPUTED_GATE_KEY, 45);

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_REQUESTED_KEY],
        serde_json::json!(true),
        "stats JSON should expose dense-mutex restart route request as a boolean"
    );
    assert_eq!(
        parsed[SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose dense-mutex restart route enable state as a boolean"
    );
    assert_eq!(
        parsed[SAT_FOCUSED_RESTART_GATE_FINAL_KEY],
        serde_json::json!(45)
    );
    assert_eq!(
        parsed[SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_UPDATES_KEY],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed[SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CHECKED_KEY],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed[SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_VARS_KEY],
        serde_json::json!(180)
    );
    assert_eq!(
        parsed[SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_CLAUSES_KEY],
        serde_json::json!(3160)
    );
    assert_eq!(
        parsed[SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_BINARY_CLAUSES_KEY],
        serde_json::json!(3150)
    );
    assert_eq!(
        parsed[SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CANDIDATE_KEY],
        serde_json::json!(true),
        "stats JSON should expose dense-mutex runtime candidate as a boolean"
    );
    assert_eq!(
        parsed[SAT_DENSE_MUTEX_FOCUSED_RESTART_PREVIOUS_GATE_KEY],
        serde_json::json!(4)
    );
    assert_eq!(
        parsed[SAT_DENSE_MUTEX_FOCUSED_RESTART_COMPUTED_GATE_KEY],
        serde_json::json!(45)
    );
}

#[test]
fn test_dimacs_stats_json_exports_preprocess_transaction_ledger_counters() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(7),
    );
    insert_preprocessing_transaction_telemetry(
        &mut run_stats,
        ay_sat::PreprocessTransactionStats {
            started: 3,
            committed: 1,
            rolled_back: 1,
            fail_closed: 1,
            proof_obligation_satisfied: 1,
            proof_obligation_rejected: 1,
            proof_obligation_pending: 1,
            reconstruction_witness_not_applicable: 1,
            reconstruction_witness_present: 1,
            reconstruction_witness_missing: 1,
            touched_variables_total: 11,
            equivalent_variables_total: 5,
            planned_substitutions_total: 4,
            max_mutation_epoch: 19,
            active_transactions: 0,
            retained_completed: 3,
            fail_closed_decompose_lrat_preflight_rejected: 1,
            rolled_back_other: 1,
            ..Default::default()
        },
    );

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(parsed["sat.preprocess_tx_started"], serde_json::json!(3));
    assert_eq!(parsed["sat.preprocess_tx_attempted"], serde_json::json!(3));
    assert_eq!(parsed["sat.preprocess_tx_committed"], serde_json::json!(1));
    assert_eq!(
        parsed["sat.preprocess_tx_rolled_back"],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed["sat.preprocess_tx_fail_closed"],
        serde_json::json!(1)
    );
    assert_eq!(parsed["sat.preprocess_tx_rejected"], serde_json::json!(1));
    assert_eq!(
        parsed["sat.preprocess_tx_proof_obligation_rejected"],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed["sat.preprocess_tx_reconstruction_witness_missing"],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed["sat.preprocess_tx_planned_substitutions_total"],
        serde_json::json!(4)
    );
    assert_eq!(
        parsed["sat.preprocess_tx_fail_closed_decompose_lrat_preflight_rejected"],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed["sat.preprocess_tx_rolled_back_other"],
        serde_json::json!(1)
    );
}

#[test]
fn test_dimacs_stats_json_exports_decompose_lrat_materializer_counters() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(7),
    );
    insert_decompose_lrat_preflight_telemetry(
        &mut run_stats,
        &ay_sat::DecomposeLratPreflightStats {
            attempts: 1,
            transaction_candidates: 2,
            no_substitution: 3,
            empty_candidates: 4,
            dry_run_emitted: 5,
            dry_run_rejected: 6,
            missing_source_id: 7,
            missing_chain_edge_id: 8,
            missing_equiv_chain: 9,
            malformed_rewrite: 10,
            contradiction: 11,
            missing_level0_unit_id: 12,
            planned_add_rejected: 13,
            missing_substitution_hint: 14,
            missing_transient_equiv_id: 15,
            proof_obligations: 16,
            reconstruction_witnesses: 17,
            main_rewrite_materializer_attempts: 18,
            main_rewrite_materializer_proof_emit_records_seen: 19,
            main_rewrite_materializer_records: 20,
            main_rewrite_materializer_fail_closed: 21,
            main_rewrite_materializer_missing_runtime_records: 22,
            main_rewrite_materializer_first_reject_checker_visible_id: 0,
            main_rewrite_materializer_first_reject_sidecar_row_index: 0,
            fmla_lift_attempts: 23,
            fmla_lift_detected: 24,
            fmla_lift_rejection_code: 25,
            fmla_lift_onehot_groups: 26,
            fmla_lift_guarded_equiv_pairs: 27,
            fmla_lift_guarded_equiv_guards: 28,
            fmla_lift_directional_ternary_witnesses: 29,
            fmla_lift_touched_vars: 30,
            fmla_lift_runtime_records: 31,
            fmla_lift_witness_checker_passed: 32,
            fmla_lift_all_witness_pairs_checked: 33,
            fmla_lift_all_witness_pairs_missing_guard_group: 34,
            fmla_lift_source_id_refs_checked: 35,
            fmla_lift_unique_source_ids_checked: 36,
            fmla_lift_source_ids_checked: 37,
            fmla_lift_source_ids_visible: 38,
            fmla_lift_source_ids_missing: 39,
            fmla_lift_first_missing_source_id: 40,
            fmla_lift_proof_ready: 41,
            fmla_lift_model_ready: 42,
            fmla_lift_destructive_allowed: 43,
            ..Default::default()
        },
    );

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed["sat.decompose_lrat_preflight_attempts"],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_candidate_count"],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_no_substitution"],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_empty_candidates"],
        serde_json::json!(4)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_slices"],
        serde_json::json!(5)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_missing_substitution_hint"],
        serde_json::json!(14)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_missing_transient_equiv_id"],
        serde_json::json!(15)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_proof_obligations"],
        serde_json::json!(16)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_reconstruction_witnesses"],
        serde_json::json!(17)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_main_rewrite_materializer_attempts"],
        serde_json::json!(18)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_main_rewrite_materializer_proof_emit_records_seen"],
        serde_json::json!(19)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_main_rewrite_materializer_records"],
        serde_json::json!(20)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_main_rewrite_materializer_fail_closed"],
        serde_json::json!(21)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_main_rewrite_materializer_missing_runtime_records"],
        serde_json::json!(22)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_fmla_lift_attempts"],
        serde_json::json!(23)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_fmla_lift_detected"],
        serde_json::json!(24)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_fmla_lift_guarded_equiv_pairs"],
        serde_json::json!(27)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_fmla_lift_all_witness_pairs_checked"],
        serde_json::json!(33)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_fmla_lift_unique_source_ids_checked"],
        serde_json::json!(36)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_fmla_lift_source_ids_missing"],
        serde_json::json!(39)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_fmla_lift_first_missing_source_id"],
        serde_json::json!(40)
    );
    assert_eq!(
        parsed["sat.decompose_lrat_preflight_fmla_lift_destructive_allowed"],
        serde_json::json!(43)
    );
}

#[test]
fn test_dimacs_stats_json_exports_dense_clique_mab_branch_route_stats() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "sat",
        Duration::from_millis(7),
    );
    run_stats.insert(SAT_DENSE_CLIQUE_MAB_BRANCH_REQUESTED_KEY, 1);
    run_stats.insert(SAT_DENSE_CLIQUE_MAB_BRANCH_ENABLED_KEY, 1);
    run_stats.insert(SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISED_KEY, 1);
    run_stats.insert(SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISE_COUNT_KEY, 12);

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_MAB_BRANCH_REQUESTED_KEY],
        serde_json::json!(true),
        "stats JSON should expose dense-clique MAB branch request as a boolean"
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_MAB_BRANCH_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose dense-clique MAB branch enable state as a boolean"
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISED_KEY],
        serde_json::json!(true),
        "stats JSON should expose dense-clique MAB branch exercise as a boolean"
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISE_COUNT_KEY],
        serde_json::json!(12)
    );
}

#[test]
fn test_dimacs_stats_json_exports_dense_clique_php_proof_route_stats() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unsat",
        Duration::from_millis(7),
    );
    run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_REQUESTED_KEY, 1);
    run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ENABLED_KEY, 1);
    run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXERCISED_KEY, 1);
    run_stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_FINGERPRINT_KEY,
        CLIQUE_N2_K10_CLAUSE_FINGERPRINT,
    );

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::OfficialSatCompMainLrat);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_REQUESTED_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ENABLED_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXERCISED_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_FINGERPRINT_KEY],
        serde_json::json!(CLIQUE_N2_K10_CLAUSE_FINGERPRINT)
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ORIGINAL_ORDER_WITNESS_KEY,
        1,
    );
    run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_OBLIGATION_ROWS_KEY, 415);
    run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_ALO_ROWS_KEY, 10);
    run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_MUTEX_ROWS_KEY, 405);
    run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXTENSION_CLAUSES_KEY, 270);
    run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_ROWS_KEY, 3160);
    run_stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_RAW_LITERALS_KEY,
        6480,
    );
    run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_ROWS_KEY, 685);
    run_stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTENSION_ROWS_KEY,
        270,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_ALO_ROWS_KEY,
        10,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_MUTEX_ROWS_KEY,
        405,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTERNAL_CHECKER_VERIFIED_ROWS_KEY,
        0,
    );
    run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_PRESENT_KEY, 1);
    run_stats.insert(
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_BYTES_KEY,
        988_231,
    );

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::OfficialSatCompMainLrat);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ORIGINAL_ORDER_WITNESS_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_OBLIGATION_ROWS_KEY],
        serde_json::json!(415)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_ALO_ROWS_KEY],
        serde_json::json!(10)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_MUTEX_ROWS_KEY],
        serde_json::json!(405)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXTENSION_CLAUSES_KEY],
        serde_json::json!(270)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_ROWS_KEY],
        serde_json::json!(3160)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_RAW_LITERALS_KEY],
        serde_json::json!(6480)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_ROWS_KEY],
        serde_json::json!(685)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTENSION_ROWS_KEY],
        serde_json::json!(270)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_ALO_ROWS_KEY],
        serde_json::json!(10)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_MUTEX_ROWS_KEY],
        serde_json::json!(405)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTERNAL_CHECKER_VERIFIED_ROWS_KEY],
        serde_json::json!(0)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_PRESENT_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_BYTES_KEY],
        serde_json::json!(988_231)
    );
}

#[test]
fn test_dense_clique_php_route_admission_uses_source_replay_ledger() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "../../benchmarks/sat/satcomp2024-sample/\
             cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz",
    );
    if !path.exists() {
        eprintln!("dense clique route fixture missing: {}", path.display());
        return;
    }
    let output = Command::new("xz")
        .arg("-dc")
        .arg(&path)
        .output()
        .expect("run xz -dc for dense clique route fixture");
    assert!(
        output.status.success(),
        "xz -dc failed for {}: {}",
        path.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    let content = String::from_utf8(output.stdout).expect("fixture is UTF-8 DIMACS");
    let formula = ay_sat::parse_dimacs(&content).expect("parse clique_n2_k10 fixture");

    let admission = match dense_clique_php_route_admission(formula.num_vars, &formula.clauses) {
        DenseCliquePhpProofRouteAdmissionResult::Admitted(admission) => admission,
        other => {
            panic!("exact route fixture should admit through source replay packet: {other:?}")
        }
    };
    let ledger = &admission.replay_ledger;

    assert_eq!(ledger.extension_var_start_one_based, 181);
    assert_eq!(ledger.extension_var_end_one_based, 270);
    assert_eq!(ledger.extension_clause_id_start, 3_161);
    assert_eq!(ledger.extension_clause_id_end, 3_430);
    assert_eq!(ledger.bucket_alo_rows.len(), 10);
    assert_eq!(ledger.bucket_mutex_rows.len(), 405);
    assert_eq!(ledger.extension_clause_count(), 270);
    assert_eq!(admission.source_audit.clauses_seen, 3160);
    assert_eq!(admission.source_audit.source_rows, 3160);
    assert_eq!(admission.source_audit.raw_dimacs_literals, 6480);
    assert_eq!(admission.source_audit.first_source_id, Some(1));
    assert_eq!(admission.source_audit.last_source_id, Some(3160));
    let checker_audit_stats = admission
        .checker_audit_stats
        .expect("clique_n2_k10 asset should retain checker audit stats");
    assert_eq!(checker_audit_stats.checker_rows_materialized, 685);
    assert_eq!(
        checker_audit_stats.extension_definition_rows_materialized,
        270
    );
    assert_eq!(checker_audit_stats.bucket_alo_rows_materialized, 10);
    assert_eq!(checker_audit_stats.bucket_mutex_rows_materialized, 405);
    assert_eq!(checker_audit_stats.external_checker_verified_rows, 0);

    let mut corrupted_clauses = formula.clauses.clone();
    corrupted_clauses[1540] = vec![Literal::from_dimacs(-1), Literal::from_dimacs(-20)];
    assert!(
        clique_n2_k10_original_order_witness(&corrupted_clauses),
        "control mutation should keep the prefix/order witness so the fingerprint guard is tested"
    );
    assert_ne!(
        dimacs_clause_fingerprint(formula.num_vars, &corrupted_clauses),
        CLIQUE_N2_K10_CLAUSE_FINGERPRINT,
        "control mutation must change the exact route fingerprint"
    );
    match dense_clique_php_route_admission(formula.num_vars, &corrupted_clauses) {
            DenseCliquePhpProofRouteAdmissionResult::TargetRejected(reason) => {
                assert!(
                    reason.contains("fingerprint"),
                    "target rejection should explain the exact-target fingerprint guard: {reason}"
                );
            }
            other => panic!(
                "route admission must reject the target before replay when the exact fingerprint changes: {other:?}"
            ),
        }
}

#[test]
fn test_dense_clique_php_route_admission_accepts_exact_php_functional_asset() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/sat/unsat/php_functional_5_4.cnf");
    if !path.exists() {
        eprintln!("dense clique PHP asset fixture missing: {}", path.display());
        return;
    }
    let content = std::fs::read_to_string(&path).expect("read php_functional_5_4 fixture");
    let formula = ay_sat::parse_dimacs(&content).expect("parse php_functional_5_4 fixture");

    assert!(php_functional_5_4_original_order_witness(&formula.clauses));
    assert_eq!(
        dimacs_clause_fingerprint(formula.num_vars, &formula.clauses),
        PHP_FUNCTIONAL_5_4_CLAUSE_FINGERPRINT
    );
    let admission = match dense_clique_php_route_admission(formula.num_vars, &formula.clauses) {
        DenseCliquePhpProofRouteAdmissionResult::Admitted(admission) => admission,
        other => panic!("php_functional_5_4 proof asset should admit exactly: {other:?}"),
    };

    assert_eq!(admission.asset.name, "php_functional_5_4");
    assert_eq!(admission.fingerprint, PHP_FUNCTIONAL_5_4_CLAUSE_FINGERPRINT);
    assert_eq!(admission.source_audit.source_rows, 75);
    assert_eq!(admission.source_audit.raw_dimacs_literals, 160);
    assert_eq!(admission.replay_ledger.pigeons, 5);
    assert_eq!(admission.replay_ledger.holes, 4);
    assert_eq!(admission.replay_ledger.bucket_alo_rows.len(), 5);
    assert_eq!(admission.replay_ledger.bucket_mutex_rows.len(), 40);
    assert!(
        admission.checker_audit_stats.is_none(),
        "singleton-bucket PHP asset must not claim pair-bucket checker audit authority"
    );

    let mut corrupted_clauses = formula.clauses.clone();
    corrupted_clauses[35] = vec![Literal::from_dimacs(-1), Literal::from_dimacs(-10)];
    assert!(
        !php_functional_5_4_original_order_witness(&corrupted_clauses),
        "control mutation should break the exact order witness"
    );
    match dense_clique_php_route_admission(formula.num_vars, &corrupted_clauses) {
        DenseCliquePhpProofRouteAdmissionResult::TargetRejected(reason) => {
            assert!(
                reason.contains("original-order witness"),
                "target rejection should explain the exact asset witness guard: {reason}"
            );
        }
        other => panic!("corrupted php_functional_5_4 asset must reject: {other:?}"),
    }
}

#[test]
fn test_dense_clique_php_route_admission_keeps_non_targets_silent() {
    assert!(matches!(
        dense_clique_php_route_admission(1, &[]),
        DenseCliquePhpProofRouteAdmissionResult::NonTarget
    ));

    let clauses = vec![vec![Literal::from_dimacs(1)]];
    assert!(matches!(
        dense_clique_php_route_admission(180, &clauses),
        DenseCliquePhpProofRouteAdmissionResult::NonTarget
    ));

    assert!(matches!(
        dense_clique_php_route_target_clauses(1, 0, None),
        Ok(None)
    ));

    let missing_target_clauses =
        dense_clique_php_route_target_clauses(180, 3160, None).unwrap_err();
    assert!(
            missing_target_clauses.contains("clause capture unavailable"),
            "exact target missing-clause capture should be a target rejection: {missing_target_clauses}"
        );

    let short_capture = vec![vec![Literal::from_dimacs(1)]];
    let count_mismatch =
        dense_clique_php_route_target_clauses(180, 3160, Some(&short_capture)).unwrap_err();
    assert!(
        count_mismatch.contains("captured clause count 1"),
        "exact target captured-count mismatch should be a target rejection: {count_mismatch}"
    );
}

#[test]
fn test_dense_clique_php_route_checker_audit_counts_fail_closed() {
    let exact = ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats {
        enabled: true,
        source_rows_audited: 3_160,
        extension_rows_seen: 90,
        bucket_alo_rows_seen: 10,
        bucket_mutex_rows_seen: 405,
        checker_rows_materialized: 685,
        extension_definition_rows_materialized: 270,
        bucket_alo_rows_materialized: 10,
        bucket_mutex_rows_materialized: 405,
        source_dependency_edges: 1_630,
        dependency_clause_edges: 990,
        external_checker_verified_rows: 0,
    };
    let counts_ok = |stats| {
        dense_clique_php_route_checker_audit_counts_match(
            stats,
            &CLIQUE_N2_K10_EXPECTED_CHECKER_AUDIT_STATS,
        )
    };
    assert!(counts_ok(&exact));

    let mut disabled = exact;
    disabled.enabled = false;
    assert!(!counts_ok(&disabled));

    let mut wrong_source_rows = exact;
    wrong_source_rows.source_rows_audited -= 1;
    assert!(!counts_ok(&wrong_source_rows));

    let mut wrong_extension_seen = exact;
    wrong_extension_seen.extension_rows_seen -= 1;
    assert!(!counts_ok(&wrong_extension_seen));

    let mut wrong_alo_seen = exact;
    wrong_alo_seen.bucket_alo_rows_seen -= 1;
    assert!(!counts_ok(&wrong_alo_seen));

    let mut wrong_mutex_seen = exact;
    wrong_mutex_seen.bucket_mutex_rows_seen -= 1;
    assert!(!counts_ok(&wrong_mutex_seen));

    let mut wrong_total = exact;
    wrong_total.checker_rows_materialized -= 1;
    assert!(!counts_ok(&wrong_total));

    let mut wrong_extension_rows = exact;
    wrong_extension_rows.extension_definition_rows_materialized -= 1;
    assert!(!counts_ok(&wrong_extension_rows));

    let mut wrong_alo_rows = exact;
    wrong_alo_rows.bucket_alo_rows_materialized -= 1;
    assert!(!counts_ok(&wrong_alo_rows));

    let mut wrong_mutex_rows = exact;
    wrong_mutex_rows.bucket_mutex_rows_materialized -= 1;
    assert!(!counts_ok(&wrong_mutex_rows));

    let mut wrong_source_edges = exact;
    wrong_source_edges.source_dependency_edges -= 1;
    assert!(!counts_ok(&wrong_source_edges));

    let mut wrong_dependency_edges = exact;
    wrong_dependency_edges.dependency_clause_edges -= 1;
    assert!(!counts_ok(&wrong_dependency_edges));

    let mut checker_claim = exact;
    checker_claim.external_checker_verified_rows = 1;
    assert!(!counts_ok(&checker_claim));
}

#[test]
fn test_dense_clique_scout_stats_are_default_off() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_DENSE_CLIQUE_SCOUT_ENV);
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(7),
    );

    insert_dense_clique_scout_stats(
        &mut run_stats,
        DimacsInputSource::Content("not parsed when default-off"),
    );
    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_REQUESTED_KEY],
        serde_json::json!(false),
        "dense-clique scout must be default-off"
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_ENABLED_KEY],
        serde_json::json!(false)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_EXERCISED_KEY],
        serde_json::json!(false)
    );
}

#[test]
fn test_dense_clique_scout_stats_recover_strict_mutex_surface() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::set(SAT_DENSE_CLIQUE_SCOUT_ENV, "1");
    let content = "\
p cnf 6 17
1 2 3 0
4 5 6 0
-1 -2 0
-1 -3 0
-1 -4 0
-1 -5 0
-1 -6 0
-2 -3 0
-2 -4 0
-2 -5 0
-2 -6 0
-3 -4 0
-3 -5 0
-3 -6 0
-4 -5 0
-4 -6 0
-5 -6 0
";
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(7),
    );

    insert_dense_clique_scout_stats(&mut run_stats, DimacsInputSource::Content(content));
    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_REQUESTED_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_ENABLED_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_EXERCISED_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MUTEX_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_REJECTION_CODE_KEY],
        serde_json::json!(0)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_VERTICES_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_COLORS_KEY],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_GRAPH_EDGES_KEY],
        serde_json::json!(0)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_GRAPH_NON_EDGES_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKETS_KEY],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MIN_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MAX_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MULTIPARTITE_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_PHP_PIGEONS_KEY],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_PHP_HOLES_KEY],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_PHP_UNSAT_OBLIGATION_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_MUTEXES_KEY],
        serde_json::json!(15)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_EXPECTED_MUTEXES_KEY],
        serde_json::json!(15)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_SUPPORT_CLAUSES_KEY],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_SUPPORT_WIDTH_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_OTHER_CLAUSES_KEY],
        serde_json::json!(0)
    );
}

#[test]
fn test_dense_clique_scout_requested_mixed_formula_fails_closed() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::set(SAT_DENSE_CLIQUE_SCOUT_ENV, "1");
    let content = "\
p cnf 4 3
1 2 0
-1 -2 0
3 -4 0
";
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(7),
    );

    insert_dense_clique_scout_stats(&mut run_stats, DimacsInputSource::Content(content));
    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_REQUESTED_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_ENABLED_KEY],
        serde_json::json!(false)
    );
    assert_eq!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_EXERCISED_KEY],
        serde_json::json!(false)
    );
    assert_ne!(
        parsed[SAT_DENSE_CLIQUE_SCOUT_REJECTION_CODE_KEY],
        serde_json::json!(0)
    );
}

#[test]
fn test_multiplier_equiv_conservation_scout_stats_are_default_off() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset(SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENV);
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(7),
    );

    insert_multiplier_equiv_conservation_scout_stats(
        &mut run_stats,
        DimacsInputSource::Content("not parsed when default-off"),
    );
    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REQUESTED_KEY],
        serde_json::json!(false)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENABLED_KEY],
        serde_json::json!(false)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_FAIL_CLOSED_KEY],
        serde_json::json!(false),
        "default-off scout should not create a fail-closed runtime claim"
    );
}

#[test]
fn test_multiplier_equiv_conservation_scout_requested_fails_closed_without_proof() {
    let _lock = lock_env();
    let _guard = ScopedEnvVar::set(SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENV, "1");
    let content = "\
p cnf 3 3
-3 1 0
-3 2 0
3 -1 -2 0
";
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(7),
    );

    insert_multiplier_equiv_conservation_scout_stats(
        &mut run_stats,
        DimacsInputSource::Content(content),
    );
    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REQUESTED_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_TARGET_ISSUE_KEY],
        serde_json::json!(9725)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_ADMISSION_ISSUE_KEY],
        serde_json::json!(9733)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_CONSERVATION_ISSUE_KEY],
        serde_json::json!(9736)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_EXERCISED_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_FAIL_CLOSED_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_ADMITTED_KEY],
        serde_json::json!(false)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_RESULT_AUTHORITY_KEY],
        serde_json::json!(false)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_OUTPUT_AUTHORITY_KEY],
        serde_json::json!(false)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_REPLAY_CHECKED_KEY],
        serde_json::json!(false)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_EXTERNAL_CHECKER_VERIFIED_KEY],
        serde_json::json!(false)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_OBLIGATION_ROWS_KEY],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BOUND_ROWS_KEY],
        serde_json::json!(0)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BINDINGS_MISSING_KEY],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_REFERENCES_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BOUND_REFERENCES_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BINDING_MISSING_REFERENCES_KEY],
        serde_json::json!(0)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_DUPLICATE_REFERENCES_KEY],
        serde_json::json!(0)
    );
    assert_eq!(
        parsed[SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_OUT_OF_RANGE_REFERENCES_KEY],
        serde_json::json!(0)
    );
    assert_eq!(
        parsed
            [SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_LITERAL_MISMATCH_REFERENCES_KEY],
        serde_json::json!(0)
    );
}

#[test]
fn test_dimacs_stats_json_exports_search_inplace_watch_scan_route_as_booleans() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "sat",
        Duration::from_millis(7),
    );
    run_stats.insert(SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_REQUESTED_KEY, 1);
    run_stats.insert(SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENABLED_KEY, 1);
    run_stats.insert(SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_EXERCISED_KEY, 1);

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_REQUESTED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the SEARCH route request as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the SEARCH route enable state as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_EXERCISED_KEY],
        serde_json::json!(true),
        "stats JSON should expose SEARCH route exercise as a boolean"
    );
}

#[test]
fn test_dimacs_stats_json_exports_true_tail_relocation_gate_as_boolean() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "sat",
        Duration::from_millis(7),
    );
    run_stats.insert(SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ENABLED_KEY, 1);
    run_stats.insert(SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY, 2);
    run_stats.insert(SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_MOVES_KEY, 1);
    run_stats.insert(
        SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENABLED_KEY,
        1,
    );
    run_stats.insert(
        SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ELIGIBLE_KEY,
        4,
    );
    run_stats.insert(SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_WRITES_KEY, 3);
    run_stats.insert(SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_UNIT_KEY, 2);
    run_stats.insert(
        SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_CONFLICT_KEY,
        1,
    );
    run_stats.insert(
        SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENABLED_KEY,
        1,
    );
    run_stats.insert(
        SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ELIGIBLE_KEY,
        8,
    );
    run_stats.insert(
        SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_WRITES_KEY,
        7,
    );
    run_stats.insert(
        SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_CONFLICT_KEY,
        6,
    );
    run_stats.insert(SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ENABLED_KEY, 1);
    run_stats.insert(SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY, 3);
    run_stats.insert(SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_MOVES_KEY, 2);
    run_stats.insert(
        SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE_ENABLED_KEY,
        1,
    );
    run_stats.insert(SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENABLED_KEY, 1);
    run_stats.insert(SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_CANDIDATES_KEY, 11);
    run_stats.insert(SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_APPLIED_KEY, 10);
    run_stats.insert(SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_SAVED_SLOTS_KEY, 9);
    run_stats.insert(SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_SUFFIX_KEY, 8);
    run_stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_SUFFIX_KEY,
        7,
    );
    run_stats.insert(SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_PREFIX_KEY, 6);
    run_stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_PREFIX_KEY,
        5,
    );
    run_stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_UNIT_KEY,
        4,
    );
    run_stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_CONFLICT_KEY,
        3,
    );
    run_stats.insert(
        SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENABLED_KEY,
        1,
    );

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the relocation gate as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_MOVES_KEY],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the used5 FSW reset gate as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ELIGIBLE_KEY],
        serde_json::json!(4)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_WRITES_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_UNIT_KEY],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_CONFLICT_KEY],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the FSW conflict-only reset gate as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ELIGIBLE_KEY],
        serde_json::json!(8)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_WRITES_KEY],
        serde_json::json!(7)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_CONFLICT_KEY],
        serde_json::json!(6)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the 6-18 relocation gate as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_MOVES_KEY],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the no-replacement saved-pos gate as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the FSW Gent-order skip gate as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_CANDIDATES_KEY],
        serde_json::json!(11)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_APPLIED_KEY],
        serde_json::json!(10)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_SAVED_SLOTS_KEY],
        serde_json::json!(9)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_SUFFIX_KEY],
        serde_json::json!(8)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_SUFFIX_KEY],
        serde_json::json!(7)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_PREFIX_KEY],
        serde_json::json!(6)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_PREFIX_KEY],
        serde_json::json!(5)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_UNIT_KEY],
        serde_json::json!(4)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_CONFLICT_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the learned 19-63 unit blocker-refresh guard as a boolean"
    );
}

#[test]
fn test_dimacs_stats_json_exports_no_replacement_scan_pressure_buckets() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "unknown",
        Duration::from_millis(7),
    );
    run_stats.insert(SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENABLED_KEY, 1);
    run_stats.insert(
        "sat.bcp_learned_no_replacement_scan_pressure_19_63_scans",
        11,
    );
    run_stats.insert(
        "sat.bcp_learned_no_replacement_scan_pressure_19_63_steps",
        37,
    );
    run_stats.insert(
        "sat.bcp_learned_no_replacement_scan_pressure_19_63_start_false",
        5,
    );
    run_stats.insert(
        "sat.bcp_learned_no_replacement_scan_pressure_19_63_wrapped",
        3,
    );
    run_stats.insert("sat.bcp_learned_no_replacement_scan_pressure_19_63_unit", 7);
    run_stats.insert(
        "sat.bcp_learned_no_replacement_scan_pressure_19_63_conflict",
        4,
    );
    run_stats.insert("sat.bcp_learned_1963_fsw_unit_lbd_3_6", 2);
    run_stats.insert("sat.bcp_learned_1963_fsw_unit_lbd_3_6_steps", 61);
    run_stats.insert("sat.bcp_learned_1963_fsw_conflict_used_0", 3);
    run_stats.insert("sat.bcp_learned_1963_fsw_conflict_used_0_steps", 89);
    run_stats.insert("sat.bcp_learned_1963_fsw_repeat_bucket_max", 4);
    run_stats.insert("sat.bcp_learned_1963_fsw_repeat_bucket_7_count", 4);
    run_stats.insert("sat.bcp_learned_1963_fsw_repeat_bucket_7_steps", 144);
    run_stats.insert(SAT_BCP_LEARNED_1963_IDENTITY_ENABLED_KEY, 1);
    run_stats.insert("sat.bcp_learned_1963_identity_exact_rows", 2);
    run_stats.insert(
        "sat.bcp_learned_1963_identity_topk_pressure_share_ppm",
        750_000,
    );
    run_stats.insert("sat.bcp_learned_1963_identity_topk_fsw_steps", 321);
    run_stats.insert(
        "sat.bcp_learned_1963_identity_topk_fsw_pressure_share_ppm",
        875_000,
    );
    run_stats.insert("sat.bcp_learned_1963_identity_age_1000_9999_steps", 55);
    run_stats.insert("sat.bcp_learned_1963_identity_fsw_age_1000_9999_steps", 44);
    run_stats.insert("sat.bcp_learned_1963_identity_lbd_3_6_steps", 66);
    run_stats.insert("sat.bcp_learned_1963_identity_used_2_4_steps", 77);
    run_stats.insert("sat.bcp_learned_1963_identity_activity_0_steps", 88);
    run_stats.insert("sat.bcp_learned_1963_identity_row_0_clause_id", 42);
    run_stats.insert("sat.bcp_learned_1963_identity_row_0_age", 1234);
    run_stats.insert("sat.bcp_learned_1963_identity_row_0_steps", 99);
    run_stats.insert("sat.bcp_learned_1963_identity_row_0_fsw_steps", 77);
    run_stats.insert("sat.bcp_learned_1963_identity_row_0_fsw_unit_steps", 55);
    run_stats.insert("sat.bcp_learned_1963_identity_row_0_fsw_conflict_steps", 22);
    run_stats.insert("sat.bcp_learned_1963_identity_row_0_repeat_scans", 3);
    run_stats.insert("sat.bcp_learned_1963_identity_row_0_fsw_repeat_steps", 11);
    run_stats.insert("sat.bcp_learned_1963_identity_fsw_row_0_clause_id", 84);
    run_stats.insert("sat.bcp_learned_1963_identity_fsw_row_0_steps", 111);
    run_stats.insert("sat.bcp_learned_1963_identity_fsw_row_0_fsw_steps", 101);
    run_stats.insert(
        "sat.bcp_learned_1963_identity_fsw_row_0_fsw_conflict_steps",
        99,
    );
    run_stats.insert(SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENABLED_KEY, 1);
    run_stats.insert("sat.bcp_learned_1963_pressure_reduction_candidates", 41);
    run_stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_pressure_candidates",
        29,
    );
    run_stats.insert("sat.bcp_learned_1963_pressure_reduction_ranked", 23);
    run_stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_rank_bias_total",
        8192,
    );
    run_stats.insert("sat.bcp_learned_1963_pressure_reduction_selected", 13);
    run_stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_selected_steps",
        2048,
    );
    run_stats.insert("sat.bcp_learned_1963_pressure_reduction_deleted", 11);
    run_stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_deleted_steps",
        1024,
    );
    run_stats.insert("sat.bcp_learned_1963_pressure_reduction_kept", 7);
    run_stats.insert("sat.bcp_learned_1963_pressure_reduction_kept_steps", 512);
    run_stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_skipped_no_pressure",
        5,
    );
    run_stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_lrat_retained_delete_skips",
        2,
    );
    run_stats.insert(SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENABLED_KEY, 1);
    run_stats.insert("sat.bcp_learned_1963_pressure_retention_candidates", 43);
    run_stats.insert(
        "sat.bcp_learned_1963_pressure_retention_pressure_candidates",
        31,
    );
    run_stats.insert("sat.bcp_learned_1963_pressure_retention_ranked", 27);
    run_stats.insert(
        "sat.bcp_learned_1963_pressure_retention_rank_bias_total",
        4096,
    );
    run_stats.insert("sat.bcp_learned_1963_pressure_retention_selected", 3);
    run_stats.insert(
        "sat.bcp_learned_1963_pressure_retention_selected_steps",
        256,
    );
    run_stats.insert("sat.bcp_learned_1963_pressure_retention_deleted", 1);
    run_stats.insert("sat.bcp_learned_1963_pressure_retention_deleted_steps", 128);
    run_stats.insert("sat.bcp_learned_1963_pressure_retention_kept", 24);
    run_stats.insert("sat.bcp_learned_1963_pressure_retention_kept_steps", 3584);
    run_stats.insert(
        "sat.bcp_learned_1963_pressure_retention_skipped_no_pressure",
        12,
    );
    run_stats.insert(
        "sat.bcp_learned_1963_pressure_retention_lrat_retained_delete_skips",
        2,
    );

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose scan-pressure profiling as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_IDENTITY_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose learned 19-63 identity profiling as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose learned 19-63 pressure reduction as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose learned 19-63 pressure retention as a boolean"
    );
    assert_eq!(
        parsed["sat.bcp_learned_no_replacement_scan_pressure_19_63_scans"],
        serde_json::json!(11)
    );
    assert_eq!(
        parsed["sat.bcp_learned_no_replacement_scan_pressure_19_63_steps"],
        serde_json::json!(37)
    );
    assert_eq!(
        parsed["sat.bcp_learned_no_replacement_scan_pressure_19_63_start_false"],
        serde_json::json!(5)
    );
    assert_eq!(
        parsed["sat.bcp_learned_no_replacement_scan_pressure_19_63_wrapped"],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed["sat.bcp_learned_no_replacement_scan_pressure_19_63_unit"],
        serde_json::json!(7)
    );
    assert_eq!(
        parsed["sat.bcp_learned_no_replacement_scan_pressure_19_63_conflict"],
        serde_json::json!(4)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_fsw_unit_lbd_3_6"],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_fsw_unit_lbd_3_6_steps"],
        serde_json::json!(61)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_fsw_conflict_used_0"],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_fsw_conflict_used_0_steps"],
        serde_json::json!(89)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_fsw_repeat_bucket_max"],
        serde_json::json!(4)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_fsw_repeat_bucket_7_count"],
        serde_json::json!(4)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_fsw_repeat_bucket_7_steps"],
        serde_json::json!(144)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_exact_rows"],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_topk_pressure_share_ppm"],
        serde_json::json!(750_000)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_topk_fsw_steps"],
        serde_json::json!(321)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_topk_fsw_pressure_share_ppm"],
        serde_json::json!(875_000)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_age_1000_9999_steps"],
        serde_json::json!(55)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_fsw_age_1000_9999_steps"],
        serde_json::json!(44)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_lbd_3_6_steps"],
        serde_json::json!(66)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_used_2_4_steps"],
        serde_json::json!(77)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_activity_0_steps"],
        serde_json::json!(88)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_row_0_clause_id"],
        serde_json::json!(42)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_row_0_age"],
        serde_json::json!(1234)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_row_0_steps"],
        serde_json::json!(99)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_row_0_fsw_steps"],
        serde_json::json!(77)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_row_0_fsw_unit_steps"],
        serde_json::json!(55)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_row_0_fsw_conflict_steps"],
        serde_json::json!(22)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_row_0_repeat_scans"],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_row_0_fsw_repeat_steps"],
        serde_json::json!(11)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_fsw_row_0_clause_id"],
        serde_json::json!(84)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_fsw_row_0_steps"],
        serde_json::json!(111)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_fsw_row_0_fsw_steps"],
        serde_json::json!(101)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_identity_fsw_row_0_fsw_conflict_steps"],
        serde_json::json!(99)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_pressure_reduction_rank_bias_total"],
        serde_json::json!(8192)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_pressure_reduction_lrat_retained_delete_skips"],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_pressure_retention_rank_bias_total"],
        serde_json::json!(4096)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_pressure_retention_kept_steps"],
        serde_json::json!(3584)
    );
    assert_eq!(
        parsed["sat.bcp_learned_1963_pressure_retention_lrat_retained_delete_skips"],
        serde_json::json!(2)
    );
}

#[test]
fn test_dimacs_stats_json_exports_blocker_cert_shadow_counters() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "sat",
        Duration::from_millis(7),
    );
    run_stats.insert(SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION_ENABLED_KEY, 1);
    run_stats.insert(SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ENABLED_KEY, 1);
    run_stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE_ENABLED_KEY,
        1,
    );
    run_stats.insert(SAT_BCP_LEARNED_1963_BLOCKER_CERT_CANDIDATES_KEY, 11);
    run_stats.insert(SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISIONS_KEY, 2);
    run_stats.insert(SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_HITS_KEY, 3);
    run_stats.insert(SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_MISMATCHES_KEY, 4);
    run_stats.insert(SAT_BCP_LEARNED_1963_BLOCKER_CERT_MISMATCH_DEMOTIONS_KEY, 15);
    run_stats.insert(SAT_BCP_LEARNED_1963_BLOCKER_CERT_POPULATES_KEY, 5);
    run_stats.insert(SAT_BCP_LEARNED_1963_BLOCKER_CERT_STALE_REJECTS_KEY, 6);
    run_stats.insert(SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECTS_KEY, 7);
    run_stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTIONS_KEY,
        8,
    );
    run_stats.insert(SAT_BCP_LEARNED_1963_BLOCKER_CERT_REPEAT_REJECTS_KEY, 9);
    run_stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELIDED_SUFFIX_SLOTS_KEY,
        10,
    );
    run_stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ELIDED_SUFFIX_SLOTS_KEY,
        12,
    );
    run_stats.insert(SAT_BCP_LEARNED_1963_BLOCKER_CERT_AFFECTED_FSW_ROWS_KEY, 13);
    run_stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_AFFECTED_FSW_ROWS_KEY,
        14,
    );

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose blocker-cert elision as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose blocker-cert shadow probing as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose blocker-cert false-reject demotion as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_CANDIDATES_KEY],
        serde_json::json!(11)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISIONS_KEY],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_HITS_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_MISMATCHES_KEY],
        serde_json::json!(4)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_MISMATCH_DEMOTIONS_KEY],
        serde_json::json!(15)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_POPULATES_KEY],
        serde_json::json!(5)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_STALE_REJECTS_KEY],
        serde_json::json!(6)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECTS_KEY],
        serde_json::json!(7)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTIONS_KEY],
        serde_json::json!(8)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_REPEAT_REJECTS_KEY],
        serde_json::json!(9)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELIDED_SUFFIX_SLOTS_KEY],
        serde_json::json!(10)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ELIDED_SUFFIX_SLOTS_KEY],
        serde_json::json!(12)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_AFFECTED_FSW_ROWS_KEY],
        serde_json::json!(13)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_AFFECTED_FSW_ROWS_KEY],
        serde_json::json!(14)
    );
}

#[test]
fn test_dimacs_stats_json_exports_small_tail_reorder_gates_as_boolean() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "sat",
        Duration::from_millis(7),
    );
    run_stats.insert(SAT_BCP_LEARNED_617_TAIL_REORDER_ENABLED_KEY, 1);
    run_stats.insert(SAT_BCP_LEARNED_617_TAIL_REORDER_CANDIDATES_KEY, 4);
    run_stats.insert(SAT_BCP_LEARNED_617_TAIL_REORDER_EXERCISED_KEY, 4);
    run_stats.insert(SAT_BCP_LEARNED_617_TAIL_REORDER_CHANGED_KEY, 3);
    run_stats.insert(SAT_BCP_LEARNED_617_TAIL_REORDER_SWAPS_KEY, 8);
    run_stats.insert(SAT_BCP_LEARNED_18_TAIL_REORDER_ENABLED_KEY, 1);
    run_stats.insert(SAT_BCP_LEARNED_18_TAIL_REORDER_CANDIDATES_KEY, 2);
    run_stats.insert(SAT_BCP_LEARNED_18_TAIL_REORDER_EXERCISED_KEY, 2);
    run_stats.insert(SAT_BCP_LEARNED_18_TAIL_REORDER_CHANGED_KEY, 1);
    run_stats.insert(SAT_BCP_LEARNED_18_TAIL_REORDER_SWAPS_KEY, 5);

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_BCP_LEARNED_617_TAIL_REORDER_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the 6-17 tail reorder gate as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_617_TAIL_REORDER_CANDIDATES_KEY],
        serde_json::json!(4)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_617_TAIL_REORDER_EXERCISED_KEY],
        serde_json::json!(4)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_617_TAIL_REORDER_CHANGED_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_617_TAIL_REORDER_SWAPS_KEY],
        serde_json::json!(8)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_18_TAIL_REORDER_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the length-18 tail reorder gate as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_18_TAIL_REORDER_CANDIDATES_KEY],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_18_TAIL_REORDER_EXERCISED_KEY],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_18_TAIL_REORDER_CHANGED_KEY],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_18_TAIL_REORDER_SWAPS_KEY],
        serde_json::json!(5)
    );
}

#[test]
fn test_dimacs_stats_json_exports_tail_reorder_gate_as_boolean() {
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        "sat",
        Duration::from_millis(7),
    );
    run_stats.insert(SAT_BCP_LEARNED_1963_TAIL_REORDER_ENABLED_KEY, 1);
    run_stats.insert(SAT_BCP_LEARNED_1963_TAIL_REORDER_CANDIDATES_KEY, 3);
    run_stats.insert(SAT_BCP_LEARNED_1963_TAIL_REORDER_CHANGED_KEY, 2);
    run_stats.insert(SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAPS_KEY, 5);
    run_stats.insert(SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENABLED_KEY, 1);
    run_stats.insert(SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_LIMIT_KEY, 256);
    run_stats.insert(SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_CANDIDATES_KEY, 4);
    run_stats.insert(SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_APPLIED_KEY, 3);
    run_stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SKIPPED_OVER_BUDGET_KEY,
        1,
    );
    run_stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_APPLIED_KEY,
        9,
    );
    run_stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_SKIPPED_KEY,
        300,
    );

    let json = dimacs_run_stats_json(&run_stats, VariantRouteProfile::Standard);
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("DIMACS stats JSON should parse");

    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TAIL_REORDER_ENABLED_KEY],
        serde_json::json!(true),
        "stats JSON should expose the tail reorder gate as a boolean"
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TAIL_REORDER_CANDIDATES_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TAIL_REORDER_CHANGED_KEY],
        serde_json::json!(2)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAPS_KEY],
        serde_json::json!(5)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENABLED_KEY],
        serde_json::json!(true)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_LIMIT_KEY],
        serde_json::json!(256)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_CANDIDATES_KEY],
        serde_json::json!(4)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_APPLIED_KEY],
        serde_json::json!(3)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SKIPPED_OVER_BUDGET_KEY],
        serde_json::json!(1)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_APPLIED_KEY],
        serde_json::json!(9)
    );
    assert_eq!(
        parsed[SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_SKIPPED_KEY],
        serde_json::json!(300)
    );
}

#[test]
fn test_dimacs_timeout_exit_flushes_buffered_proof_output_2971() {
    struct TimeoutFlagGuard;
    impl Drop for TimeoutFlagGuard {
        fn drop(&mut self) {
            TIMED_OUT.store(false, Ordering::SeqCst);
            VERDICT_PRINTED.store(false, Ordering::SeqCst);
        }
    }

    let proof_path = std::env::temp_dir().join(format!(
        "ay_dimacs_timeout_flush_{}.drat",
        std::process::id()
    ));
    let _ = std::fs::remove_file(&proof_path);
    struct Cleanup(PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    let _cleanup = Cleanup(proof_path.clone());

    let file = std::fs::File::create(&proof_path).expect("create proof fixture");
    let proof_output = ProofOutput::drat_text(BufWriter::new(file));
    let mut solver = SatSolver::with_proof_output(1, proof_output);
    solver.add_clause(Vec::new());

    TIMED_OUT.store(true, Ordering::SeqCst);
    VERDICT_PRINTED.store(true, Ordering::SeqCst);
    let _guard = TimeoutFlagGuard;

    let code = dimacs_timeout_exit_code_for_policy(Some(&mut solver), false);
    assert_eq!(code, Some(DIMACS_TIMEOUT_EXIT_CODE));
    assert_eq!(
        std::fs::read_to_string(&proof_path).expect("read flushed proof fixture"),
        "0\n",
        "timeout exit preparation must flush buffered DRAT/LRAT output before propagating 124",
    );
}

#[test]
fn test_dimacs_timeout_exit_retains_fmla_learned_lrat_fail_closed_diagnostic() {
    struct TimeoutFlagGuard;
    impl Drop for TimeoutFlagGuard {
        fn drop(&mut self) {
            TIMED_OUT.store(false, Ordering::SeqCst);
            VERDICT_PRINTED.store(false, Ordering::SeqCst);
        }
    }

    let _env_lock = lock_env();
    let artifact_path = std::env::temp_dir().join(format!(
        "ay_dimacs_timeout_fmla_learned_lrat_dry_run_{}.json",
        std::process::id()
    ));
    let _ = std::fs::remove_file(&artifact_path);
    struct Cleanup(PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    let _cleanup = Cleanup(artifact_path.clone());

    let _guard = ScopedEnvVar::set(
        ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_PATH_ENV,
        artifact_path.to_str().expect("artifact path utf8"),
    );
    let proof_output = ProofOutput::lrat_text(Vec::new(), 1);
    let mut solver = SatSolver::with_proof_output(1, proof_output);

    TIMED_OUT.store(true, Ordering::SeqCst);
    VERDICT_PRINTED.store(true, Ordering::SeqCst);
    let _guard = TimeoutFlagGuard;

    let code = dimacs_timeout_exit_code_for_policy(Some(&mut solver), false);
    assert_eq!(code, Some(DIMACS_TIMEOUT_EXIT_CODE));
    let artifact_json: serde_json::Value = serde_json::from_slice(
        &std::fs::read(&artifact_path).expect("read retained Fmla dry-run artifact"),
    )
    .expect("retained Fmla dry-run artifact must be JSON");
    assert_eq!(
        artifact_json["schema"].as_str(),
        Some(ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA)
    );
    assert_eq!(
        artifact_json["materialization_status"].as_str(),
        Some("fail_closed_no_learned_lrat_authority_records")
    );
    assert_eq!(
        artifact_json["authorizes_main_proof_out"].as_bool(),
        Some(false),
        "timeout-retained diagnostic must not authorize Main proof.out"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn test_synthesized_default_dimacs_non_unsat_cleanup_removes_private_staging() {
    let dir = tempfile::tempdir().expect("tempdir");
    let proof_path = dir.path().join("proof.lrat");

    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Lrat,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: true,
        format_was_explicit: false,
    };
    let file = create_configured_dimacs_proof_file(&proof).expect("create owned proof fixture");
    let proof_output = ProofOutput::lrat_text(BufWriter::new(file), 1);
    let mut solver = SatSolver::with_proof_output(1, proof_output);
    solver.add_clause(Vec::new());

    let telemetry =
        cleanup_dimacs_non_unsat_proof_sidecar(&mut solver, &SatResult::Unknown, Some(&proof))
            .expect("cleanup should preserve proof telemetry");

    assert!(
        solver.proof_writer().is_none(),
        "non-UNSAT cleanup must detach the proof writer before process exit"
    );
    assert!(
        !proof_path.exists(),
        "non-UNSAT cleanup must remove the proof sidecar"
    );
    assert!(
        private_dimacs_staging_entries(dir.path()).is_empty(),
        "synthesized-default cleanup must remove private staging"
    );
    assert!(
        std::fs::read_to_string(dimacs_proof_status_path(&proof.path))
            .expect("read non-UNSAT stale marker")
            .contains("status=stale-not-current"),
        "non-UNSAT cleanup must publish an explicit stale marker"
    );
    assert!(!dimacs_proof_status_lock_path(&dimacs_proof_status_path(&proof.path)).exists());
    assert!(
        telemetry.additions > 0,
        "cleanup should snapshot proof telemetry before detaching the writer"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn test_dense_clique_php_route_rejection_cleanup_removes_proof_sidecar() {
    let proof_path = std::env::temp_dir().join(format!(
        "ay_dense_clique_route_rejection_cleanup_{}.lrat",
        std::process::id()
    ));
    let _ = std::fs::remove_file(&proof_path);
    struct Cleanup(PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    let _cleanup = Cleanup(proof_path.clone());

    let file = create_owned_dimacs_proof_file(proof_path.to_str().expect("UTF-8 path"))
        .expect("create owned proof fixture");
    let proof_output = ProofOutput::lrat_text(BufWriter::new(file), 3_160);
    let mut solver = SatSolver::with_proof_output(180, proof_output);
    solver.add_clause(Vec::new());
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Lrat,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: false,
        format_was_explicit: false,
    };

    let telemetry = cleanup_dense_clique_php_route_rejection_proof(&mut solver, &proof)
        .expect("target-rejection cleanup should preserve proof telemetry");

    assert!(
        solver.proof_writer().is_none(),
        "target-rejection cleanup must detach the DIMACS proof writer before fail-closed exit"
    );
    assert!(
        !proof_path.exists(),
        "target-rejection cleanup must remove the partial proof sidecar"
    );
    assert!(
        telemetry.additions > 0,
        "target-rejection cleanup should snapshot proof telemetry before detaching the writer"
    );
}

#[test]
fn test_satcomp_dimacs_timeout_exit_code_is_unknown_success() {
    struct TimeoutFlagGuard;
    impl Drop for TimeoutFlagGuard {
        fn drop(&mut self) {
            TIMED_OUT.store(false, Ordering::SeqCst);
            VERDICT_PRINTED.store(false, Ordering::SeqCst);
        }
    }

    TIMED_OUT.store(true, Ordering::SeqCst);
    VERDICT_PRINTED.store(true, Ordering::SeqCst);
    let _guard = TimeoutFlagGuard;

    let code = dimacs_timeout_exit_code_for_policy(None, true);
    assert_eq!(
        code,
        Some(0),
        "SAT-COMP wrapper UNKNOWN timeout must use the competition UNKNOWN exit code"
    );
}

#[test]
fn test_official_main_default_lrat_route_disables_startup_phase_init() {
    let input = variant_input_for_dimacs_route(
        SolverVariant::Default,
        32,
        96,
        true,
        true,
        true,
        true,
        false,
    );

    assert_eq!(
        input.startup_policy,
        VariantStartupPolicy::DisableWarmupWalk
    );
    assert_eq!(
        input.route_profile,
        VariantRouteProfile::OfficialSatCompMainLrat
    );
    let config = SolverVariant::Default.config(input);
    assert!(
        config.features.walk,
        "official Main LRAT keeps periodic rephase walk"
    );
    assert!(
        config.features.warmup,
        "official Main LRAT keeps warmup in the feature profile"
    );
}

#[test]
fn test_non_official_default_lrat_route_preserves_startup_phase_init() {
    let input = variant_input_for_dimacs_route(
        SolverVariant::Default,
        32,
        96,
        true,
        true,
        true,
        false,
        false,
    );

    assert_eq!(input.startup_policy, VariantStartupPolicy::Preserve);
    assert_eq!(input.route_profile, VariantRouteProfile::Standard);
    let config = SolverVariant::Default.config(input);
    assert!(config.features.walk, "non-official LRAT keeps walk");
    assert!(config.features.warmup, "non-official LRAT keeps warmup");
}

#[test]
fn test_explicit_startup_phase_init_preserves_official_route() {
    let input = variant_input_for_dimacs_route(
        SolverVariant::Default,
        32,
        96,
        true,
        true,
        true,
        true,
        true,
    );

    assert_eq!(input.startup_policy, VariantStartupPolicy::Preserve);
    assert_eq!(
        input.route_profile,
        VariantRouteProfile::OfficialSatCompMainLrat
    );
    let config = SolverVariant::Default.config(input);
    assert!(config.features.walk, "explicit opt-in keeps walk");
    assert!(config.features.warmup, "explicit opt-in keeps warmup");
    assert!(
        config.hot_path.prune_conflict_analysis_experiments,
        "official route identity is independent of startup opt-in"
    );
}

#[test]
fn test_official_route_policy_requires_default_lrat_output() {
    let aggressive = variant_input_for_dimacs_route(
        SolverVariant::Aggressive,
        32,
        96,
        true,
        true,
        true,
        true,
        false,
    );
    assert_eq!(aggressive.startup_policy, VariantStartupPolicy::Preserve);
    assert_eq!(aggressive.route_profile, VariantRouteProfile::Standard);

    let internal_lrat_export = variant_input_for_dimacs_route(
        SolverVariant::Default,
        32,
        96,
        true,
        true,
        false,
        true,
        false,
    );
    assert_eq!(
        internal_lrat_export.startup_policy,
        VariantStartupPolicy::Preserve
    );
    assert_eq!(
        internal_lrat_export.route_profile,
        VariantRouteProfile::Standard
    );
}

#[test]
fn test_should_enable_xor_extension_zero() {
    let clauses = make_clauses(0, 0);
    assert!(!should_enable_xor_extension(&clauses, 0, 0, 0));
}

#[test]
fn test_should_enable_xor_extension_requires_density_not_just_detection() {
    // Use mixed clauses so gate-structure check doesn't fire (has large clauses).
    let clauses = make_clauses_mixed(0, 5, 5);
    // A tiny pure-XOR formula still qualifies (low binary fraction).
    assert!(should_enable_xor_extension(&clauses, 2, 0, 1));
    // A single accidental XOR in a large formula should stay disabled.
    assert!(!should_enable_xor_extension(&clauses, 2, 9_998, 1));
}

#[test]
fn test_should_enable_xor_extension_pure_xor() {
    // Pure ternary XOR formula, no remaining clauses.
    // NOTE: 100% ternary triggers gate-structure check, so pure-ternary
    // formulas are now treated as gate-structured and XOR is disabled.
    // This is correct: pure ternary formulas are typically gate encodings.
    let clauses = make_clauses(0, 10);
    assert!(!should_enable_xor_extension(&clauses, 100, 0, 10));
    // Mix in large clauses to represent real XOR-heavy formulas.
    let clauses = make_clauses_mixed(0, 8, 2); // 80% ternary + 20% large
    assert!(should_enable_xor_extension(&clauses, 100, 0, 10));
    assert!(should_enable_xor_extension(&clauses, 8, 0, 4));
}

#[test]
fn test_should_enable_xor_extension_high_density() {
    // High XOR density (80-90%): enabled when binary fraction is low and
    // formula has clause size diversity (not purely binary+ternary).
    let clauses = make_clauses_mixed(0, 90, 10); // 90% ternary + 10% large
    assert!(should_enable_xor_extension(&clauses, 1732, 307, 100));
    assert!(should_enable_xor_extension(&clauses, 4000, 600, 200));
    assert!(should_enable_xor_extension(&clauses, 7232, 1664, 300));
    assert!(should_enable_xor_extension(&clauses, 4000, 1000, 200));
}

#[test]
fn test_large_formula_disables_xor_extension() {
    // inc6: large formulas (> XOR_EXTENSION_MAX_CLAUSES) must stay on the
    // standard CDCL + inprocessing path even at high XOR density. The XOR
    // extension disables congruence/BVE/sweep/probe/vivify and collapses CDCL
    // search on big instances (intel047/dislog regression). A mixed-size
    // distribution keeps the binary/gate-structure guards from firing first,
    // isolating the absolute-size guard.
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset("AY_XOR_ALLOW_LARGE");

    let n = XOR_EXTENSION_MAX_CLAUSES + 1;
    let bin = n / 10; // 10% binary
    let ter = (n * 6) / 10; // 60% ternary
    let wide = n - bin - ter; // ~30% wide -> passes all fraction guards
    let clauses = make_clauses_mixed(bin, ter, wide);
    assert!(clauses.len() > XOR_EXTENSION_MAX_CLAUSES);
    // High XOR density (consumed ~ half the formula) would normally enable.
    assert!(
        !should_enable_xor_extension(&clauses, clauses.len() / 2, clauses.len() / 2, 5_000),
        "large formulas must skip the XOR extension regardless of density"
    );
    // The escape hatch restores GE for experimentation.
    let _guard = ScopedEnvVar::set("AY_XOR_ALLOW_LARGE", "1");
    assert!(
        should_enable_xor_extension(&clauses, clauses.len() / 2, clauses.len() / 2, 5_000),
        "AY_XOR_ALLOW_LARGE must re-enable the XOR extension on large formulas"
    );
}

#[test]
fn test_small_dense_xor_still_enabled_under_size_cap() {
    // inc6: a small, dense, mixed-size XOR-heavy formula (well under the cap)
    // must still route to the XOR extension -- this is the case GE helps.
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset("AY_XOR_ALLOW_LARGE");

    let clauses = make_clauses_mixed(0, 80, 20); // 100 clauses, 80% ternary
    assert!(clauses.len() <= XOR_EXTENSION_MAX_CLAUSES);
    assert!(
        should_enable_xor_extension(&clauses, 80, 20, 40),
        "small dense XOR formulas should still use the XOR extension"
    );
}

#[test]
fn test_should_enable_xor_extension_crypto_benchmarks() {
    // The residual-dominance asserts below read AY_XOR_ALLOW_RESIDUAL, which the
    // kill-switch test mutates globally under the shared environment lock;
    // hold that lock and clear the var so the two tests cannot race.
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset("AY_XOR_ALLOW_RESIDUAL");

    // Crypto benchmarks: low binary fraction, high XOR density, mixed sizes.
    // Real crypto formulas have clauses of sizes 2-8+, not just binary+ternary.
    let clauses = make_clauses_mixed(5, 75, 20); // 5% binary + 75% ternary + 20% large
                                                 // 30% consumed / 70% residual: XOR still covers a dominant-enough share to
                                                 // pay for forfeiting preprocessing on the residual — stays on the XOR path
                                                 // (residual 70% < 85% guard). (A 1M-clause formula is disabled in
                                                 // production by XOR_EXTENSION_MAX_CLAUSES; this synthetic clauses vec only
                                                 // exercises the fraction/density/residual gates.)
    assert!(should_enable_xor_extension(
        &clauses, 300_000, 700_000, 5_000
    ));
    // 10% consumed / 90% residual and 5% consumed / 95% residual: the XOR path
    // forfeits ALL preprocessing (congruence/sweep/BVE/factor) on the huge CNF
    // residual — measured catastrophic on the 31e843c5 class (wf_ff0f9700).
    // The residual-dominance guard (residual > 85%) now keeps these on the
    // pure-SAT + full-preprocessing path. AY_XOR_ALLOW_RESIDUAL=1 restores the
    // old unconditional enable.
    assert!(!should_enable_xor_extension(&clauses, 10_000, 90_000, 500));
    assert!(!should_enable_xor_extension(&clauses, 500, 9_500, 50));
}

#[test]
fn test_residual_dominance_disables_xor_extension() {
    // wf_ff0f9700: the XOR/GE extension routes the whole formula through the
    // theory backend, which disables ALL preprocessing and freezes XOR vars.
    // When XOR extraction consumes only a small slice and a large CNF residual
    // remains, that residual grinds on bare CDCL. Measured catastrophic on
    // 31e843c5 (848 consumed / 12560 remaining = 94% residual): XOR path
    // s UNKNOWN@120s vs plain + full-preprocess path s UNSATISFIABLE@110s
    // (kissat-agreed, dpr-trim -> cake_lpr verified). The residual-dominance
    // guard disables XOR when residual > 85% of the clause count.
    let _lock = lock_env();
    let _guard = ScopedEnvVar::unset("AY_XOR_ALLOW_RESIDUAL");

    // Mirror 31e843c5's clause-size distribution (32.5% binary, 46% ternary,
    // 21.5% wide) so the binary%, gate%, and sparse-wide guards all pass and
    // the residual guard is the deciding factor. xor_count=207 also keeps the
    // sparse-wide guard's xor-fraction leg from firing.
    let clauses = make_clauses_mixed(325, 460, 215); // 1000 clauses
                                                     // 94% residual -> disabled by the residual-dominance guard.
    assert!(
        !should_enable_xor_extension(&clauses, 848, 12_560, 207),
        "94% CNF residual must disable the XOR extension (31e843c5 class)"
    );
    // Legitimate "XOR ~= whole formula": 15% residual (99718c17) stays on XOR.
    assert!(
        should_enable_xor_extension(&clauses, 4_672, 833, 207),
        "15% residual (legitimate XOR-dominant) must stay on the XOR path"
    );
    // Pure-XOR extraction (0 remaining, 77a0d54f) stays on XOR.
    assert!(
        should_enable_xor_extension(&clauses, 5_505, 0, 207),
        "0% residual (pure XOR) must stay on the XOR path"
    );
    // Boundary: exactly 85% residual is kept (guard fires only when > 85%).
    assert!(
        should_enable_xor_extension(&clauses, 1_500, 8_500, 207),
        "exactly 85% residual is kept on the XOR path"
    );
    // Just above 85% residual is disabled.
    assert!(
        !should_enable_xor_extension(&clauses, 1_499, 8_501, 207),
        "just over 85% residual disables the XOR extension"
    );

    // Kill switch restores the old unconditional enable byte-for-byte.
    let _kill_switch = ScopedEnvVar::set("AY_XOR_ALLOW_RESIDUAL", "1");
    assert!(
        should_enable_xor_extension(&clauses, 848, 12_560, 207),
        "AY_XOR_ALLOW_RESIDUAL=1 must restore the pre-fix XOR enable"
    );
}

#[test]
fn test_should_enable_xor_extension_below_density() {
    // Below 5% density: accidental XOR matches, not worth GE overhead.
    let clauses = make_clauses_mixed(0, 50, 50);
    assert!(!should_enable_xor_extension(&clauses, 100, 9_900, 10));
    assert!(!should_enable_xor_extension(&clauses, 40, 9_960, 5));
}

#[test]
fn test_sparse_xor_wide_circuit_cnf_disables_xor() {
    // Circuit_multiplier22-like shape: sparse XOR recovery over a formula
    // dominated by width-4+ definition clauses should keep pure SAT
    // preprocessing available for factor/BVE/model reconstruction.
    let clauses = make_clauses_mixed(2, 8, 90);
    assert!(
        !should_enable_xor_extension(&clauses, 6, 94, 1),
        "sparse XOR over wide circuit CNF should stay on the pure SAT path"
    );
    assert!(
        should_enable_xor_extension(&clauses, 20, 80, 5),
        "dense XOR recovery should still use the XOR extension"
    );
}

#[test]
fn test_should_disable_xor_high_binary_fraction() {
    // Gate-structured circuit formulas have >50% binary clauses.
    // XOR extraction should be disabled even though XOR density is high.
    // eq.atree.braun.8: 688/919 = 74.9% binary, 78.7% XOR density.
    let clauses = make_clauses(688, 231); // 74.9% binary
    assert!(
        !should_enable_xor_extension(&clauses, 724, 195, 321),
        "XOR should be disabled for gate-structured formulas with high binary fraction"
    );
}

#[test]
fn test_should_enable_xor_low_binary_fraction() {
    // Crypto formulas typically have <30% binary clauses and mixed sizes.
    let clauses = make_clauses_mixed(10, 60, 30); // 10% binary + 60% ternary + 30% large
    assert!(
        should_enable_xor_extension(&clauses, 300, 700, 50),
        "XOR should be enabled for crypto formulas with low binary fraction"
    );
}

#[test]
fn test_binary_fraction_boundary() {
    // Use mixed clauses to avoid gate-structure check firing.
    // 50% binary + 25% ternary + 25% large = not gate-structured (75% bin+tern < 95%).
    let clauses = make_clauses_mixed(50, 25, 25);
    assert!(
        should_enable_xor_extension(&clauses, 80, 20, 10),
        "XOR should be enabled at 50% binary with mixed sizes"
    );

    // 51% binary: should disable via binary-fraction check.
    let clauses = make_clauses_mixed(51, 24, 25);
    assert!(
        !should_enable_xor_extension(&clauses, 80, 20, 10),
        "XOR should be disabled at 51% binary"
    );
}

#[test]
fn test_gate_structure_disables_xor() {
    // Gate-structured formulas: >95% binary+ternary.
    // eq.atree.braun.7: 43% binary + 56% ternary = 99% gate-structured.
    let clauses = make_clauses(43, 56); // 99% binary+ternary, 1% "other" = 0
    assert!(
        !should_enable_xor_extension(&clauses, 400, 200, 100),
        "XOR should be disabled for gate-structured formulas (>95% binary+ternary)"
    );
    // Same ratio but with 6% large clauses — no longer gate-structured.
    let clauses = make_clauses_mixed(43, 51, 6); // 94% binary+ternary
    assert!(
        should_enable_xor_extension(&clauses, 400, 200, 100),
        "XOR should be enabled when binary+ternary is below 95%"
    );
}

#[cfg(target_os = "linux")]
fn private_dimacs_staging_entries(parent: &Path) -> Vec<PathBuf> {
    std::fs::read_dir(parent)
        .expect("read DIMACS proof parent")
        .filter_map(|entry| {
            let entry = entry.expect("read DIMACS proof parent entry");
            entry
                .file_name()
                .to_string_lossy()
                .starts_with(DIMACS_PROOF_STAGING_PREFIX)
                .then(|| entry.path())
        })
        .collect()
}

#[cfg(target_os = "linux")]
fn private_dimacs_staging_debris_bytes(parent: &Path) -> Vec<Vec<u8>> {
    let mut debris = Vec::new();
    for entry in private_dimacs_staging_entries(parent) {
        if entry.is_dir() {
            for nested in std::fs::read_dir(&entry).expect("read DIMACS quarantine directory") {
                let nested = nested.expect("read DIMACS quarantine entry").path();
                if nested.is_file() {
                    debris.push(std::fs::read(nested).expect("read DIMACS quarantine tombstone"));
                }
            }
        } else {
            debris.push(std::fs::read(entry).expect("read named DIMACS staging tombstone"));
        }
    }
    debris
}

#[cfg(target_os = "linux")]
fn retained_test_transaction(
    proof: &ProofConfig,
    published: super::PublishedDimacsProof,
    optional: bool,
) -> DimacsUnsatPublicationTransaction {
    let retained = retain_published_dimacs_proof(&proof.path, published, proof.binary)
        .expect("retain proof authority");
    DimacsUnsatPublicationTransaction::new(retained, None, optional)
}

#[cfg(target_os = "linux")]
fn private_lean_snapshot_entries() -> Vec<PathBuf> {
    let prefix = format!(".ay-lean-verify-{}-", std::process::id());
    let mut entries: Vec<_> = std::fs::read_dir(std::env::temp_dir())
        .expect("read temporary directory")
        .filter_map(|entry| {
            let entry = entry.expect("read temporary directory entry");
            entry
                .file_name()
                .to_string_lossy()
                .starts_with(&prefix)
                .then(|| entry.path())
        })
        .collect();
    entries.sort();
    entries
}

#[cfg(target_os = "linux")]
#[test]
fn authenticated_lean_snapshot_is_anonymous_and_never_cleans_named_replacements() {
    use std::os::unix::fs::MetadataExt as _;

    let proof_dir = tempfile::tempdir().expect("proof tempdir");
    let proof_path = proof_dir.path().join("proof.lean4");
    let proof_path_text = proof_path.to_str().expect("UTF-8 proof path");
    let mut proof = create_owned_dimacs_proof_file(proof_path_text).expect("reserve Lean proof");
    std::io::Write::write_all(
        &mut proof,
        b"theorem ay_snapshot_test : True := by trivial\n",
    )
    .expect("write Lean proof");
    drop(proof);
    let published = seal_owned_dimacs_proof(proof_path_text).expect("seal Lean proof");

    let before = private_lean_snapshot_entries();
    let mut snapshot =
        AuthenticatedLeanSnapshot::create(proof_path_text, published).expect("create snapshot");
    snapshot.validate().expect("validate snapshot");
    assert_eq!(
        snapshot
            .descriptor
            .metadata()
            .expect("snapshot metadata")
            .nlink(),
        0,
        "the authenticated Lean snapshot must remain anonymous"
    );
    assert_eq!(
        private_lean_snapshot_entries(),
        before,
        "snapshot creation must not expose a named .ay-lean-verify entry"
    );

    let replacement_prefix = format!(".ay-lean-verify-{}-replacement-", std::process::id());
    let replacement = tempfile::Builder::new()
        .prefix(&replacement_prefix)
        .tempdir_in(std::env::temp_dir())
        .expect("create replacement directory");
    let replacement_path = replacement.path().join("proof.lean4");
    std::fs::write(&replacement_path, b"unrelated replacement\n").expect("write replacement proof");

    drop(snapshot);
    assert_eq!(
        std::fs::read(&replacement_path).expect("read replacement after snapshot close"),
        b"unrelated replacement\n",
        "closing an anonymous snapshot must not remove a named replacement"
    );
    drop(replacement);
    assert_eq!(
        private_lean_snapshot_entries(),
        before,
        "snapshot close must not leak a named .ay-lean-verify entry"
    );

    assert!(remove_owned_dimacs_proof(proof_path_text).expect("remove owned Lean proof"));
}

#[cfg(not(target_os = "linux"))]
#[test]
fn authenticated_lean_snapshot_fails_closed_without_anonymous_descriptors() {
    let executable = std::env::current_exe().expect("current executable");
    let metadata = std::fs::metadata(executable).expect("current executable metadata");
    let published = super::PublishedDimacsProof {
        identity: super::ProofFileIdentity::from_metadata(&metadata),
        len: 0,
        sha256: [0; 32],
    };

    let error = match AuthenticatedLeanSnapshot::create("must-not-be-opened.lean4", published) {
        Ok(_) => panic!("unsupported platforms must reject Lean snapshot creation"),
        Err(error) => error,
    };
    assert_eq!(error.kind(), std::io::ErrorKind::Unsupported);
}

#[cfg(target_os = "linux")]
#[test]
fn dimacs_proof_output_refuses_stale_regular_file() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    std::fs::write(&path, b"stale proof\n").expect("seed stale proof");

    let error = create_owned_dimacs_proof_file(path.to_str().expect("UTF-8 path"))
        .expect_err("same-run proof creation must not clobber stale output");
    assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);
    assert_eq!(
        std::fs::read(&path).expect("read stale proof"),
        b"stale proof\n"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn linux_rename_noreplace_is_atomic_and_never_clobbers() {
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("source");
    let target = dir.path().join("target");
    std::fs::write(&source, b"source bytes\n").expect("write source");
    std::fs::write(&target, b"target bytes\n").expect("write target");

    let error = rename_dimacs_noreplace(&source, &target)
        .expect_err("no-replace rename must reject an existing target");
    assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);
    assert_eq!(
        std::fs::read(&source).expect("read source"),
        b"source bytes\n"
    );
    assert_eq!(
        std::fs::read(&target).expect("read target"),
        b"target bytes\n"
    );

    std::fs::remove_file(&target).expect("remove target");
    rename_dimacs_noreplace(&source, &target).expect("rename to unoccupied target");
    assert!(!source.exists());
    assert_eq!(
        std::fs::read(&target).expect("read renamed file"),
        b"source bytes\n"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn linux_descriptor_publication_works_unprivileged_and_never_clobbers() {
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("source");
    let target = dir.path().join("target");
    std::fs::write(&source, b"descriptor bytes\n").expect("write source");
    let descriptor = std::fs::File::open(&source).expect("open source descriptor");

    publish_dimacs_descriptor_noreplace(&descriptor, &target)
        .expect("publish through AT_EMPTY_PATH or unprivileged proc-fd fallback");
    assert_eq!(
        std::fs::read(&target).expect("read published target"),
        b"descriptor bytes\n"
    );
    let error = publish_dimacs_descriptor_noreplace(&descriptor, &target)
        .expect_err("descriptor publication must never clobber an existing target");
    assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);
    assert_eq!(
        std::fs::read(&target).expect("read preserved target"),
        b"descriptor bytes\n"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn unsupported_anonymous_staging_falls_back_to_named_sibling_stage() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let path_text = path.to_str().expect("UTF-8 path");
    inject_anonymous_dimacs_staging_error_once(nix::libc::EOPNOTSUPP);

    let mut proof = create_owned_dimacs_proof_file(path_text)
        .expect("unsupported O_TMPFILE must use the named sibling fallback");
    proof.write_all(b"0\n").expect("write fallback proof");
    drop(proof);
    assert!(
        !path.exists(),
        "fallback must remain private before sealing"
    );
    assert_eq!(private_dimacs_staging_entries(dir.path()).len(), 1);

    seal_owned_dimacs_proof(path_text).expect("seal fallback proof");
    assert_eq!(std::fs::read(&path).expect("read fallback proof"), b"0\n");
    assert!(private_dimacs_staging_entries(dir.path()).is_empty());
    assert!(remove_owned_dimacs_proof(path_text).expect("remove fallback proof"));
}

#[cfg(target_os = "linux")]
#[test]
fn anonymous_staging_fallback_accepts_only_capability_errors() {
    for raw_os_error in [nix::libc::EOPNOTSUPP, nix::libc::EINVAL] {
        assert!(anonymous_dimacs_staging_is_unsupported(
            &std::io::Error::from_raw_os_error(raw_os_error)
        ));
    }
    for raw_os_error in [
        nix::libc::EACCES,
        nix::libc::EDQUOT,
        nix::libc::ENOSPC,
        nix::libc::EIO,
        nix::libc::EMFILE,
        nix::libc::EISDIR,
    ] {
        assert!(
            !anonymous_dimacs_staging_is_unsupported(&std::io::Error::from_raw_os_error(
                raw_os_error
            )),
            "operational error {raw_os_error} must remain fail closed"
        );
    }
}

#[cfg(target_os = "linux")]
#[test]
fn pre_o_tmpfile_kernel_signal_remains_fail_closed() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    inject_anonymous_dimacs_staging_error_once(nix::libc::EISDIR);

    let error = create_owned_dimacs_proof_file(path.to_str().expect("UTF-8 path"))
        .expect_err("EISDIR must not enter a renameat2-dependent fallback");
    assert_eq!(error.raw_os_error(), Some(nix::libc::EISDIR));
    assert!(!path.exists());
    assert!(private_dimacs_staging_entries(dir.path()).is_empty());
}

#[cfg(target_os = "linux")]
#[test]
fn anonymous_staging_non_capability_errors_remain_fail_closed() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    inject_anonymous_dimacs_staging_error_once(nix::libc::EACCES);

    let error = create_owned_dimacs_proof_file(path.to_str().expect("UTF-8 path"))
        .expect_err("permission errors must not silently use a different staging route");
    assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied);
    assert!(!path.exists());
    assert!(private_dimacs_staging_entries(dir.path()).is_empty());
}

#[cfg(target_os = "linux")]
#[test]
fn named_fallback_seal_collision_preserves_the_raced_target() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let path_text = path.to_str().expect("UTF-8 path");
    inject_anonymous_dimacs_staging_error_once(nix::libc::EINVAL);
    let mut proof = create_owned_dimacs_proof_file(path_text).expect("reserve fallback proof");
    proof.write_all(b"0\n").expect("write proof");
    drop(proof);
    std::fs::write(&path, b"raced target\n").expect("plant target");

    let error = seal_owned_dimacs_proof(path_text)
        .expect_err("fallback publication must retain no-clobber semantics");
    assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);
    assert_eq!(
        std::fs::read(&path).expect("read target"),
        b"raced target\n"
    );
    assert!(remove_owned_dimacs_proof(path_text).expect("discard fallback staging"));
    assert_eq!(
        std::fs::read(&path).expect("read target"),
        b"raced target\n"
    );
    assert_eq!(
        private_dimacs_staging_debris_bytes(dir.path()),
        vec![b"invalidated-by-ay\n".to_vec()]
    );
}

#[cfg(target_os = "linux")]
#[test]
fn named_fallback_cleanup_preserves_replacement_after_quarantine() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let path_text = path.to_str().expect("UTF-8 path");
    inject_anonymous_dimacs_staging_error_once(nix::libc::EOPNOTSUPP);
    let mut proof = create_owned_dimacs_proof_file(path_text).expect("reserve fallback proof");
    proof.write_all(b"0\n").expect("write proof");
    drop(proof);
    seal_owned_dimacs_proof(path_text).expect("publish fallback proof");
    inject_dimacs_proof_cleanup_replacement_once();

    assert!(remove_owned_dimacs_proof(path_text).expect("remove authenticated fallback proof"));
    assert_eq!(
        std::fs::read(&path).expect("read raced replacement"),
        b"raced replacement\n"
    );
    assert_eq!(
        private_dimacs_staging_debris_bytes(dir.path()),
        vec![b"invalidated-by-ay\n".to_vec()]
    );
}

#[cfg(target_os = "linux")]
#[test]
fn named_fallback_enosys_fails_before_target_exposure() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let path_text = path.to_str().expect("UTF-8 path");
    inject_anonymous_dimacs_staging_error_once(nix::libc::EOPNOTSUPP);
    let mut proof = create_owned_dimacs_proof_file(path_text).expect("reserve fallback proof");
    proof.write_all(b"0\n").expect("write proof");
    proof.flush().expect("flush proof");
    drop(proof);

    inject_dimacs_rename_noreplace_error_once(nix::libc::ENOSYS);
    let error = seal_owned_dimacs_proof(path_text)
        .expect_err("missing renameat2 must fail before publishing the named stage");
    assert_eq!(error.raw_os_error(), Some(nix::libc::ENOSYS));
    assert!(!path.exists(), "ENOSYS must precede target exposure");
    assert_eq!(private_dimacs_staging_entries(dir.path()).len(), 1);
    assert!(remove_owned_dimacs_proof(path_text).expect("invalidate failed named stage"));
    assert!(!path.exists());
    assert_eq!(
        private_dimacs_staging_debris_bytes(dir.path()),
        vec![b"invalidated-by-ay\n".to_vec()]
    );
}

#[cfg(target_os = "linux")]
#[test]
fn named_fallback_never_publishes_or_deletes_a_swapped_stage() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let path_text = path.to_str().expect("UTF-8 path");
    inject_anonymous_dimacs_staging_error_once(nix::libc::EOPNOTSUPP);
    let mut proof = create_owned_dimacs_proof_file(path_text).expect("reserve fallback proof");
    proof.write_all(b"0\n").expect("write proof");
    proof.flush().expect("flush proof");
    drop(proof);
    let staging_path = private_dimacs_staging_entries(dir.path())
        .into_iter()
        .next()
        .expect("fallback sibling stage");
    let displaced_owned_stage = dir.path().join("displaced-owned-proof");
    std::fs::rename(&staging_path, &displaced_owned_stage).expect("displace owned stage");
    std::fs::write(&staging_path, b"unrelated staged replacement\n")
        .expect("plant staged replacement");

    seal_owned_dimacs_proof(path_text)
        .expect_err("swapped named stage must fail the publication transaction");
    assert_eq!(
        std::fs::read(&path).expect("read preserved stage replacement"),
        b"unrelated staged replacement\n"
    );
    assert_eq!(
        std::fs::read(&displaced_owned_stage).expect("read displaced owned stage"),
        b"0\n"
    );
    assert!(
        !remove_owned_dimacs_proof(path_text).expect("preserve published replacement"),
        "the public name was not AY's owned inode"
    );
    assert_eq!(
        std::fs::read(&path).expect("read preserved stage replacement"),
        b"unrelated staged replacement\n"
    );
    assert_eq!(
        std::fs::read(&displaced_owned_stage).expect("read invalidated owned stage"),
        b"invalidated-by-ay\n"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn synthesized_default_preexisting_proof_gets_explicit_stale_status() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("input.cnf.drat");
    std::fs::write(&path, b"proof from an older run\n").expect("seed stale proof");
    let proof = ProofConfig {
        path: path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: true,
        format_was_explicit: false,
    };

    let error = create_configured_dimacs_proof_file(&proof)
        .expect_err("preexisting default proof must not be rebound to this run");

    assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);
    assert_eq!(
        std::fs::read(&path).expect("read old proof"),
        b"proof from an older run\n"
    );
    let status = std::fs::read_to_string(dimacs_proof_status_path(&proof.path))
        .expect("read stale status marker");
    assert!(status.contains("status=stale-not-current"));
    assert!(!status.contains("current-same-run"));
    assert!(!dimacs_proof_status_lock_path(&dimacs_proof_status_path(&proof.path)).exists());
}

#[cfg(target_os = "linux")]
#[test]
fn synthesized_default_never_overwrites_preexisting_status_output() {
    let dir = tempfile::tempdir().expect("tempdir");
    let proof_path = dir.path().join("input.cnf.drat");
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: true,
        format_was_explicit: false,
    };
    let status_path = dimacs_proof_status_path(&proof.path);
    std::fs::write(&status_path, b"unrelated status bytes\n").expect("seed status replacement");

    let error = create_configured_dimacs_proof_file(&proof)
        .expect_err("preexisting status must reject the proof transaction");
    assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);
    assert_eq!(
        std::fs::read(&status_path).expect("read preserved status"),
        b"unrelated status bytes\n"
    );
    assert!(!proof_path.exists());
    assert!(!dimacs_proof_status_lock_path(&status_path).exists());
}

#[cfg(target_os = "linux")]
#[test]
fn status_lock_post_create_identity_failure_cleans_exact_owned_path() {
    let dir = tempfile::tempdir().expect("tempdir");
    let proof_path = dir.path().join("input.cnf.drat");
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: true,
        format_was_explicit: false,
    };
    let status_path = dimacs_proof_status_path(&proof.path);
    let lock_path = dimacs_proof_status_lock_path(&status_path);
    inject_dimacs_status_lock_identity_failure_once();

    let error = create_configured_dimacs_proof_file(&proof)
        .expect_err("injected status-lock identity failure must abort reservation");
    assert!(error
        .to_string()
        .contains("injected DIMACS proof status lock identity"));
    assert!(!proof_path.exists());
    assert!(!status_path.exists());
    assert!(!lock_path.exists(), "owned lock pathname must be removed");
    assert_eq!(
        private_dimacs_staging_debris_bytes(dir.path()),
        vec![Vec::<u8>::new()]
    );
}

#[cfg(target_os = "linux")]
#[test]
fn concurrent_synthesized_default_loser_cannot_replace_winner_status() {
    let dir = tempfile::tempdir().expect("tempdir");
    let proof_path = dir.path().join("input.cnf.drat");
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: true,
        format_was_explicit: false,
    };
    let mut winner =
        create_configured_dimacs_proof_file(&proof).expect("winner reserves transaction");
    let losing_proof = proof.clone();
    let loser = std::thread::spawn(move || create_configured_dimacs_proof_file(&losing_proof));
    let loser_error = loser
        .join()
        .expect("loser thread")
        .expect_err("loser must not share the status transaction");
    assert_eq!(loser_error.kind(), std::io::ErrorKind::AlreadyExists);

    winner.write_all(b"0\n").expect("write winner proof");
    winner.flush().expect("flush winner proof");
    drop(winner);
    let published = seal_owned_dimacs_proof(&proof.path).expect("seal winner proof");
    let mut publication = retained_test_transaction(&proof, published, false);
    mark_synthesized_default_dimacs_proof_current(&proof, published, &mut publication)
        .expect("publish winner status");
    publication.validate().expect("validate winner transaction");
    publication.commit();
    let status_path = dimacs_proof_status_path(&proof.path);
    let winner_status = std::fs::read(&status_path).expect("read winner status");
    assert!(String::from_utf8_lossy(&winner_status).contains("status=current-same-run"));

    mark_synthesized_default_dimacs_proof_stale(&proof);
    assert_eq!(
        std::fs::read(&status_path).expect("read preserved winner status"),
        winner_status,
        "a later losing run must not relabel the winner's marker"
    );
    assert!(remove_owned_dimacs_proof(&proof.path).expect("remove winner proof"));
}

#[cfg(target_os = "linux")]
#[test]
fn late_status_collision_removes_only_the_owned_proof_generation() {
    let dir = tempfile::tempdir().expect("tempdir");
    let proof_path = dir.path().join("input.cnf.drat");
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: true,
        format_was_explicit: false,
    };
    let mut output = create_configured_dimacs_proof_file(&proof).expect("reserve proof");
    output.write_all(b"0\n").expect("write proof");
    drop(output);
    let published = seal_owned_dimacs_proof(&proof.path).expect("seal proof");
    let status_path = dimacs_proof_status_path(&proof.path);
    std::fs::write(&status_path, b"raced unrelated status\n").expect("plant status collision");

    let mut publication = retained_test_transaction(&proof, published, false);
    mark_synthesized_default_dimacs_proof_current(&proof, published, &mut publication)
        .expect_err("status publication must not clobber the raced file");
    publication.invalidate_exact();
    assert!(remove_owned_dimacs_proof(&proof.path).expect("remove only owned proof"));
    assert!(!proof_path.exists());
    assert_eq!(
        std::fs::read(&status_path).expect("read status replacement"),
        b"raced unrelated status\n"
    );
    assert_eq!(
        std::fs::read(dimacs_proof_status_lock_path(&status_path))
            .expect("read invalid status lock tombstone"),
        b""
    );
}

#[cfg(target_os = "linux")]
#[test]
fn current_status_remains_absent_until_required_artifact_is_published() {
    let dir = tempfile::tempdir().expect("tempdir");
    let proof_path = dir.path().join("input.cnf.drat");
    let artifact_path = dir.path().join("proof-artifact.json");
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: Some(artifact_path.to_string_lossy().into_owned()),
        is_temp: false,
        synthesized_default: true,
        format_was_explicit: false,
    };
    let mut output = create_configured_dimacs_proof_file(&proof).expect("reserve proof");
    output.write_all(b"0\n").expect("write proof");
    drop(output);
    seal_owned_dimacs_proof(&proof.path).expect("seal proof");

    let status_path = dimacs_proof_status_path(&proof.path);
    assert!(
        !status_path.exists(),
        "current status must not precede the required artifact transaction"
    );
    assert!(
        dimacs_proof_status_lock_path(&status_path).exists(),
        "status ownership must remain reserved while later artifacts are pending"
    );
    assert!(remove_owned_dimacs_proof(&proof.path).expect("remove proof after artifact failure"));
    let status = std::fs::read_to_string(&status_path).expect("read stale status marker");
    assert!(status.contains("status=stale-not-current"));
    assert!(!dimacs_proof_status_lock_path(&status_path).exists());
}

#[cfg(target_os = "linux")]
#[test]
fn status_failure_cleans_retained_artifact_without_touching_replacement() {
    let dir = tempfile::tempdir().expect("tempdir");
    let problem_path = dir.path().join("input.cnf");
    let problem = b"p cnf 0 1\n0\n";
    std::fs::write(&problem_path, problem).expect("write problem");
    let proof_path = dir.path().join("input.cnf.drat");
    let artifact_path = dir.path().join("proof-artifact.json");
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: Some(artifact_path.to_string_lossy().into_owned()),
        is_temp: false,
        synthesized_default: true,
        format_was_explicit: false,
    };
    let mut output = create_configured_dimacs_proof_file(&proof).expect("reserve proof");
    output.write_all(b"0\n").expect("write proof");
    drop(output);
    let published = seal_owned_dimacs_proof(&proof.path).expect("seal proof");
    let (artifact_descriptor, artifact_public_path) =
        crate::proof_artifact::write_sealed_proof_artifact(
            crate::proof_artifact::ProofArtifactProblem::AuthenticatedFilePath {
                path: problem_path.to_str().expect("UTF-8 problem path"),
                sha256: sha256_digest(problem),
            },
            &proof,
            crate::proof_artifact::ProofArtifactTheoryMetadata::dimacs_sat(0, 1),
            published.sha256,
        )
        .expect("publish retained artifact")
        .expect("configured artifact");
    let retained_artifact = RetainedDimacsPublication::capture(
        artifact_descriptor,
        artifact_public_path,
        "DIMACS proof artifact",
        None,
        DimacsPublicationInvalidation::Empty,
    )
    .expect("retain artifact authority");
    let retained_proof = retain_published_dimacs_proof(&proof.path, published, proof.binary)
        .expect("retain proof authority");
    let mut publication =
        DimacsUnsatPublicationTransaction::new(retained_proof, Some(retained_artifact), false);
    let status_path = dimacs_proof_status_path(&proof.path);
    std::fs::write(&status_path, b"unrelated raced status\n").expect("plant status replacement");

    mark_synthesized_default_dimacs_proof_current(&proof, published, &mut publication)
        .expect_err("raced status must invalidate final publication");
    publication.invalidate_exact();
    assert!(remove_owned_dimacs_proof(&proof.path).expect("remove owned proof"));
    assert_eq!(
        std::fs::read(&artifact_path).expect("read invalidated artifact"),
        b""
    );
    assert!(!proof_path.exists());
    assert_eq!(
        std::fs::read(&status_path).expect("read preserved status replacement"),
        b"unrelated raced status\n"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn status_lock_cleanup_preserves_a_raced_replacement() {
    let dir = tempfile::tempdir().expect("tempdir");
    let proof_path = dir.path().join("input.cnf.drat");
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: true,
        format_was_explicit: false,
    };
    let mut output = create_configured_dimacs_proof_file(&proof).expect("reserve proof");
    output.write_all(b"partial\n").expect("write staged proof");
    drop(output);
    let status_path = dimacs_proof_status_path(&proof.path);
    let lock_path = dimacs_proof_status_lock_path(&status_path);
    let displaced_lock = dir.path().join("displaced-owned-status-lock");
    std::fs::rename(&lock_path, &displaced_lock).expect("displace owned lock");
    std::fs::write(&lock_path, b"unrelated lock replacement\n").expect("plant replacement");

    remove_owned_dimacs_proof(&proof.path)
        .expect_err("replaced status lock must make cleanup report failure");
    assert!(
        !proof_path.exists(),
        "owned proof generation must still be removed"
    );
    assert_eq!(
        std::fs::read(&lock_path).expect("read restored lock replacement"),
        b"unrelated lock replacement\n"
    );
    assert_eq!(
        std::fs::read(&displaced_lock).expect("read displaced owned lock"),
        b""
    );
    std::fs::remove_file(&lock_path).expect("remove unrelated lock replacement");
    assert!(
        !remove_owned_dimacs_proof(&proof.path).expect("retry settled removed proof state"),
        "the proof generation was already removed on the first cleanup attempt"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn retained_proof_replacement_invalidates_exact_inode_for_both_policies() {
    for optional in [false, true] {
        let dir = tempfile::tempdir().expect("tempdir");
        let proof_path = dir.path().join("proof.drat");
        let displaced = dir.path().join("displaced-owned-proof.drat");
        let proof = ProofConfig {
            path: proof_path.to_string_lossy().into_owned(),
            format: ProofFormat::Drat,
            binary: false,
            artifact_path: None,
            is_temp: false,
            synthesized_default: optional,
            format_was_explicit: false,
        };
        let mut output = if optional {
            create_configured_dimacs_proof_file(&proof).expect("reserve optional proof")
        } else {
            create_owned_dimacs_proof_file(&proof.path).expect("reserve required proof")
        };
        output.write_all(b"0\n").expect("write proof");
        drop(output);
        let published = seal_owned_dimacs_proof(&proof.path).expect("seal proof");
        let transaction = retained_test_transaction(&proof, published, optional);
        let mut authority = super::AuthorizedDimacsUnsatPublication {
            publication: Some(transaction),
            temp_proof_path: None,
        };

        std::fs::rename(&proof_path, &displaced).expect("displace owned proof");
        std::fs::write(&proof_path, b"unrelated proof replacement\n")
            .expect("plant proof replacement");
        let (reported_optional, reason) = authority
            .validate_before_verdict()
            .expect_err("replacement must revoke proof authority");
        assert_eq!(reported_optional, optional);
        assert!(reason.contains("lost namespace authority"));
        assert_eq!(
            std::fs::read(&proof_path).expect("read proof replacement"),
            b"unrelated proof replacement\n"
        );
        assert_eq!(
            std::fs::read(&displaced).expect("read exact invalidated proof"),
            b"invalidated-by-ay\n"
        );
        assert!(
            !remove_owned_dimacs_proof(&proof.path).expect("settle proof registry"),
            "the replacement must not be attributed to AY"
        );
    }
}

#[cfg(target_os = "linux")]
#[test]
fn retained_status_replacement_invalidates_proof_and_exact_marker() {
    let dir = tempfile::tempdir().expect("tempdir");
    let proof_path = dir.path().join("proof.drat");
    let status_path = dimacs_proof_status_path(proof_path.to_str().expect("UTF-8 path"));
    let displaced_status = dir.path().join("displaced-owned-status");
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: true,
        format_was_explicit: false,
    };
    let mut output = create_configured_dimacs_proof_file(&proof).expect("reserve proof");
    output.write_all(b"0\n").expect("write proof");
    drop(output);
    let published = seal_owned_dimacs_proof(&proof.path).expect("seal proof");
    let mut transaction = retained_test_transaction(&proof, published, false);
    mark_synthesized_default_dimacs_proof_current(&proof, published, &mut transaction)
        .expect("publish current marker");
    let mut authority = super::AuthorizedDimacsUnsatPublication {
        publication: Some(transaction),
        temp_proof_path: None,
    };

    std::fs::rename(&status_path, &displaced_status).expect("displace owned status");
    std::fs::write(&status_path, b"unrelated status replacement\n")
        .expect("plant status replacement");
    let (optional, _) = authority
        .validate_before_verdict()
        .expect_err("replacement must revoke status authority");
    assert!(!optional);
    assert_eq!(
        std::fs::read(&status_path).expect("read status replacement"),
        b"unrelated status replacement\n"
    );
    assert_eq!(
        std::fs::read(&displaced_status).expect("read invalidated exact status"),
        b""
    );
    assert_eq!(
        std::fs::read(&proof_path).expect("read invalidated proof"),
        b"invalidated-by-ay\n"
    );
    assert!(remove_owned_dimacs_proof(&proof.path).expect("settle proof registry"));
}

#[cfg(target_os = "linux")]
#[test]
fn retained_artifact_replacement_invalidates_proof_and_exact_artifact() {
    let dir = tempfile::tempdir().expect("tempdir");
    let problem_path = dir.path().join("input.cnf");
    let problem = b"p cnf 0 1\n0\n";
    std::fs::write(&problem_path, problem).expect("write problem");
    let proof_path = dir.path().join("proof.drat");
    let artifact_path = dir.path().join("proof-artifact.json");
    let displaced_artifact = dir.path().join("displaced-owned-artifact.json");
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: Some(artifact_path.to_string_lossy().into_owned()),
        is_temp: false,
        synthesized_default: false,
        format_was_explicit: false,
    };
    let mut output = create_configured_dimacs_proof_file(&proof).expect("reserve proof");
    output.write_all(b"0\n").expect("write proof");
    drop(output);
    let published = seal_owned_dimacs_proof(&proof.path).expect("seal proof");
    let (artifact_descriptor, artifact_public_path) =
        crate::proof_artifact::write_sealed_proof_artifact(
            crate::proof_artifact::ProofArtifactProblem::AuthenticatedFilePath {
                path: problem_path.to_str().expect("UTF-8 problem path"),
                sha256: sha256_digest(problem),
            },
            &proof,
            crate::proof_artifact::ProofArtifactTheoryMetadata::dimacs_sat(0, 1),
            published.sha256,
        )
        .expect("publish artifact")
        .expect("configured artifact");
    let retained_artifact = RetainedDimacsPublication::capture(
        artifact_descriptor,
        artifact_public_path,
        "DIMACS proof artifact",
        None,
        DimacsPublicationInvalidation::Empty,
    )
    .expect("retain artifact authority");
    let retained_proof = retain_published_dimacs_proof(&proof.path, published, proof.binary)
        .expect("retain proof authority");
    let transaction =
        DimacsUnsatPublicationTransaction::new(retained_proof, Some(retained_artifact), false);
    let mut authority = super::AuthorizedDimacsUnsatPublication {
        publication: Some(transaction),
        temp_proof_path: None,
    };

    std::fs::rename(&artifact_path, &displaced_artifact).expect("displace owned artifact");
    std::fs::write(&artifact_path, b"unrelated artifact replacement\n")
        .expect("plant artifact replacement");
    authority
        .validate_before_verdict()
        .expect_err("replacement must revoke artifact authority");
    assert_eq!(
        std::fs::read(&artifact_path).expect("read artifact replacement"),
        b"unrelated artifact replacement\n"
    );
    assert_eq!(
        std::fs::read(&displaced_artifact).expect("read invalidated exact artifact"),
        b""
    );
    assert_eq!(
        std::fs::read(&proof_path).expect("read invalidated proof"),
        b"invalidated-by-ay\n"
    );
    assert!(remove_owned_dimacs_proof(&proof.path).expect("settle proof registry"));
}

#[cfg(target_os = "linux")]
#[test]
fn temporary_proof_stays_valid_until_verdict_then_preserves_replacement() {
    let dir = tempfile::tempdir().expect("tempdir");
    let proof_path = dir.path().join("verify-only.drat");
    let displaced = dir.path().join("displaced-verify-only.drat");
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: None,
        is_temp: true,
        synthesized_default: false,
        format_was_explicit: false,
    };
    let mut output = create_configured_dimacs_proof_file(&proof).expect("reserve temp proof");
    output.write_all(b"0\n").expect("write proof");
    drop(output);
    let published = seal_owned_dimacs_proof(&proof.path).expect("seal temp proof");
    let transaction = retained_test_transaction(&proof, published, false);
    let mut authority = super::AuthorizedDimacsUnsatPublication {
        publication: Some(transaction),
        temp_proof_path: Some(proof.path.clone()),
    };

    authority
        .validate_before_verdict()
        .expect("temp proof must remain valid through the verdict gate");
    assert_eq!(
        std::fs::read(&proof_path).expect("read live temp proof"),
        b"0\n"
    );
    std::fs::rename(&proof_path, &displaced).expect("race temp proof after verdict gate");
    std::fs::write(&proof_path, b"unrelated post-verdict replacement\n")
        .expect("plant post-verdict replacement");
    authority.commit_after_verdict();

    assert_eq!(
        std::fs::read(&proof_path).expect("read preserved replacement"),
        b"unrelated post-verdict replacement\n"
    );
    assert_eq!(
        std::fs::read(&displaced).expect("read exact-invalidated temp proof"),
        b"invalidated-by-ay\n"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn proof_tombstones_reject_empty_clause_input_that_accepts_empty_drat() {
    use ay_drat_check::checker::DratChecker;
    use ay_drat_check::cnf_parser::parse_cnf;
    use ay_drat_check::drat_parser::parse_drat;

    let cnf = parse_cnf(&b"p cnf 0 1\n0\n"[..]).expect("parse empty-clause CNF");
    let empty_steps = parse_drat(b"").expect("parse empty DRAT");
    let mut checker = DratChecker::new(cnf.num_vars, true);
    checker
        .verify(&cnf.clauses, &empty_steps)
        .expect("an initial empty clause needs no DRAT steps");

    let dir = tempfile::tempdir().expect("tempdir");
    let text_path = dir.path().join("text.drat");
    let text = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(&text_path)
        .expect("create text proof");
    super::invalidate_dimacs_descriptor(
        &text,
        DimacsPublicationInvalidation::Proof { binary: false },
    )
    .expect("invalidate text proof");
    let text_tombstone = std::fs::read(&text_path).expect("read text tombstone");
    assert_eq!(text_tombstone, b"invalidated-by-ay\n");
    assert!(parse_drat(&text_tombstone).is_err());
    assert!(ay_lrat_check::lrat_parser::parse_text_lrat(
        std::str::from_utf8(&text_tombstone).expect("text tombstone is UTF-8")
    )
    .is_err());

    let binary_path = dir.path().join("binary.drat");
    let binary = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(&binary_path)
        .expect("create binary proof");
    super::invalidate_dimacs_descriptor(
        &binary,
        DimacsPublicationInvalidation::Proof { binary: true },
    )
    .expect("invalidate binary proof");
    let binary_tombstone = std::fs::read(&binary_path).expect("read binary tombstone");
    assert_eq!(binary_tombstone, b"\x80");
    assert!(parse_drat(&binary_tombstone).is_err());
    assert!(ay_lrat_check::lrat_parser::parse_binary_lrat(&binary_tombstone).is_err());
}

#[cfg(not(target_os = "linux"))]
#[test]
fn unsupported_platform_proof_gate_mutates_no_paths() {
    let dir = tempfile::tempdir().expect("tempdir");
    let proof_path = dir.path().join("proof.drat");
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: true,
        format_was_explicit: false,
    };
    let error = create_configured_dimacs_proof_file(&proof)
        .expect_err("unsupported platform must fail before mutation");
    assert_eq!(error.kind(), std::io::ErrorKind::Unsupported);
    assert!(std::fs::read_dir(dir.path())
        .expect("read untouched directory")
        .next()
        .is_none());
}

#[cfg(target_os = "linux")]
#[test]
fn dimacs_proof_identity_failure_cleans_descriptor_owned_staging() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    inject_dimacs_proof_identity_failure_once();

    let error = create_owned_dimacs_proof_file(path.to_str().expect("UTF-8 path"))
        .expect_err("injected identity failure must reject proof setup");

    assert!(error.to_string().contains("injected DIMACS proof identity"));
    assert!(!path.exists(), "failed setup must not publish a proof");
    assert!(
        private_dimacs_staging_entries(dir.path()).is_empty(),
        "identity failure must remove descriptor-owned private staging"
    );
    assert!(
        !remove_owned_dimacs_proof(path.to_str().expect("UTF-8 path"))
            .expect("failed setup must not leave a registry entry")
    );
}

#[cfg(target_os = "linux")]
#[test]
fn dimacs_proof_clone_failure_cleans_descriptor_owned_staging() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    inject_dimacs_proof_clone_failure_once();

    let error = create_owned_dimacs_proof_file(path.to_str().expect("UTF-8 path"))
        .expect_err("injected clone failure must reject proof setup");

    assert!(error.to_string().contains("injected DIMACS proof clone"));
    assert!(!path.exists(), "failed setup must not publish a proof");
    assert!(
        private_dimacs_staging_entries(dir.path()).is_empty(),
        "clone failure must remove descriptor-owned private staging"
    );
    assert!(
        !remove_owned_dimacs_proof(path.to_str().expect("UTF-8 path"))
            .expect("failed setup must not leave a registry entry")
    );
}

#[cfg(target_os = "linux")]
#[test]
fn optional_writer_failure_is_visible_to_seal_and_never_publishes_partial_bytes() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let path_text = path.to_str().expect("UTF-8 path");
    let file = create_owned_dimacs_proof_file(path_text).expect("reserve proof");
    let failed = owned_dimacs_proof_write_failure_flag(path_text).expect("failure flag");
    let mut writer = SolverDimacsProofWriter::Optional {
        writer: proof_output_writer(file),
        path: path_text.to_string(),
        failed,
    };

    inject_optional_dimacs_writer_failure_once();
    std::io::Write::write_all(&mut writer, b"partial proof bytes\n")
        .expect("optional solver writer must preserve verdict progress");
    std::io::Write::flush(&mut writer).expect("failed optional writer flush is absorbed");
    drop(writer);

    let error = seal_owned_dimacs_proof(path_text)
        .expect_err("an earlier optional writer failure must prohibit sealing");
    assert_eq!(error.kind(), std::io::ErrorKind::WriteZero);
    assert!(
        !path.exists(),
        "partial proof bytes must never be published"
    );
    assert!(remove_owned_dimacs_proof(path_text).expect("discard failed staging"));
    assert!(private_dimacs_staging_entries(dir.path()).is_empty());
}

#[cfg(target_os = "linux")]
#[test]
fn dimacs_proof_output_does_not_follow_symlink() {
    use std::os::unix::fs::symlink;

    let dir = tempfile::tempdir().expect("tempdir");
    let victim = dir.path().join("victim");
    let path = dir.path().join("proof.drat");
    std::fs::write(&victim, b"victim bytes\n").expect("seed victim");
    symlink(&victim, &path).expect("create proof symlink");

    create_owned_dimacs_proof_file(path.to_str().expect("UTF-8 path"))
        .expect_err("proof creation must reject a pre-existing symlink");
    assert_eq!(
        std::fs::read(&victim).expect("read victim"),
        b"victim bytes\n"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn dimacs_proof_seal_never_clobbers_raced_target() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let path_text = path.to_str().expect("UTF-8 path");
    let mut proof = create_owned_dimacs_proof_file(path_text).expect("reserve proof");
    std::io::Write::write_all(&mut proof, b"0\n").expect("write proof");
    std::io::Write::flush(&mut proof).expect("flush proof");
    drop(proof);

    assert!(
        !path.exists(),
        "unsealed proof must remain privately staged"
    );
    std::fs::write(&path, b"replacement\n").expect("plant replacement");
    seal_owned_dimacs_proof(path_text).expect_err("replacement must invalidate publication");
    assert!(remove_owned_dimacs_proof(path_text).expect("discard private staging"));
    assert_eq!(
        std::fs::read(&path).expect("read replacement"),
        b"replacement\n"
    );
    assert!(private_dimacs_staging_entries(dir.path()).is_empty());
}

#[cfg(target_os = "linux")]
#[test]
fn dimacs_published_proof_is_bound_to_owned_generation() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let path_text = path.to_str().expect("UTF-8 path");
    let mut proof = create_owned_dimacs_proof_file(path_text).expect("reserve proof");
    std::io::Write::write_all(&mut proof, b"0\n").expect("write proof");
    std::io::Write::flush(&mut proof).expect("flush proof");
    drop(proof);

    assert!(
        !path.exists(),
        "unsealed proof must not be publicly visible"
    );
    let seal = seal_owned_dimacs_proof(path_text).expect("seal proof");
    assert!(
        private_dimacs_staging_entries(dir.path()).is_empty(),
        "successful publication must not leak a private staging directory"
    );
    assert_eq!(
        read_published_dimacs_proof(path_text, seal.sha256).expect("authenticated read"),
        b"0\n"
    );
    assert!(remove_owned_dimacs_proof(path_text).expect("remove owned proof"));
    assert!(!path.exists());
    assert_eq!(
        private_dimacs_staging_debris_bytes(dir.path()),
        vec![b"invalidated-by-ay\n".to_vec()]
    );
}

#[cfg(target_os = "linux")]
#[test]
fn dimacs_cleanup_retains_registry_authority_across_retryable_failure() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let path_text = path.to_str().expect("UTF-8 path");
    let mut proof = create_owned_dimacs_proof_file(path_text).expect("reserve proof");
    std::io::Write::write_all(&mut proof, b"0\n").expect("write proof");
    drop(proof);
    seal_owned_dimacs_proof(path_text).expect("seal proof");
    inject_dimacs_proof_cleanup_failure_once();

    remove_owned_dimacs_proof(path_text)
        .expect_err("injected post-quarantine cleanup failure must surface");
    assert!(!path.exists(), "owned proof must already be quarantined");
    assert_eq!(private_dimacs_staging_entries(dir.path()).len(), 1);
    assert!(
        !remove_owned_dimacs_proof(path_text).expect("registry-held cleanup retry must settle"),
        "the public name was already quarantined on the first attempt"
    );
    assert_eq!(
        private_dimacs_staging_debris_bytes(dir.path()),
        vec![b"invalidated-by-ay\n".to_vec()]
    );
}

#[cfg(target_os = "linux")]
#[test]
fn dimacs_cleanup_preserves_replacement_raced_after_quarantine() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let path_text = path.to_str().expect("UTF-8 path");
    let mut proof = create_owned_dimacs_proof_file(path_text).expect("reserve proof");
    std::io::Write::write_all(&mut proof, b"0\n").expect("write proof");
    drop(proof);
    seal_owned_dimacs_proof(path_text).expect("seal proof");
    inject_dimacs_proof_cleanup_replacement_once();

    assert!(remove_owned_dimacs_proof(path_text).expect("remove quarantined owned proof"));
    assert_eq!(
        std::fs::read(&path).expect("read raced replacement"),
        b"raced replacement\n"
    );
    assert_eq!(
        private_dimacs_staging_debris_bytes(dir.path()),
        vec![b"invalidated-by-ay\n".to_vec()]
    );
}

#[cfg(target_os = "linux")]
#[test]
fn dimacs_cleanup_restores_replacement_found_before_quarantine() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let displaced = dir.path().join("displaced-owned-proof.drat");
    let path_text = path.to_str().expect("UTF-8 path");
    let mut proof = create_owned_dimacs_proof_file(path_text).expect("reserve proof");
    std::io::Write::write_all(&mut proof, b"0\n").expect("write proof");
    drop(proof);
    seal_owned_dimacs_proof(path_text).expect("seal proof");
    std::fs::rename(&path, &displaced).expect("displace owned proof");
    std::fs::write(&path, b"replacement before cleanup\n").expect("plant replacement");

    assert!(!remove_owned_dimacs_proof(path_text).expect("restore unrelated replacement"));
    assert_eq!(
        std::fs::read(&path).expect("read restored replacement"),
        b"replacement before cleanup\n"
    );
    assert_eq!(
        std::fs::read(&displaced).expect("read displaced proof"),
        b"invalidated-by-ay\n"
    );
    assert_eq!(private_dimacs_staging_entries(dir.path()).len(), 1);
}

#[test]
fn authenticated_dimacs_source_rejects_replacement() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("problem.cnf");
    let original = b"p cnf 1 1\n1 0\n";
    std::fs::write(&path, original).expect("write original problem");
    let digest = sha256_digest(original);
    let path_text = path.to_str().expect("UTF-8 path");
    assert_eq!(
        read_authenticated_dimacs_source(path_text, digest).expect("authenticated read"),
        std::str::from_utf8(original).expect("ASCII")
    );

    std::fs::write(&path, b"p cnf 1 1\n-1 0\n").expect("replace problem");
    read_authenticated_dimacs_source(path_text, digest)
        .expect_err("replacement must not be rebound to the proof");
}

#[test]
fn explicit_proof_verification_never_accepts_a_skipped_check() {
    assert!(verification_skip_is_acceptable(false));
    assert!(!verification_skip_is_acceptable(true));
}
