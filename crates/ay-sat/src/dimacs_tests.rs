// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::circuit_equiv_packet::CircuitEquivRouteAdmissionStatus;
use crate::circuit_scout::{
    produce_original_dimacs_sat_model_authority_packet,
    CircuitOriginalDimacsSatModelAuthorityPacket, CircuitSourceFrameFamily, CircuitSourceFrameKind,
    CircuitSourceFrameRow,
};
use ay_test_support::env::{lock_env, ScopedEnvVar};
use std::sync::MutexGuard;
use std::{fs, path::PathBuf};

/// Acquire the one workspace-wide env lock and clear the six authority env
/// vars, capturing their prior values; the returned guards restore them (also
/// on panic) when both drop. The caller layers its own [`ScopedEnvVar::set`]
/// guards on top in a SEPARATE binding so restore stays LIFO (the set layer
/// unwinds before this reset layer).
fn circuit_multiplier22_dimacs_authority_env_guard() -> (MutexGuard<'static, ()>, [ScopedEnvVar; 6])
{
    let guard = lock_env();
    let env = [
        ScopedEnvVar::unset(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV),
        ScopedEnvVar::unset(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_FORMULA_ENV),
        ScopedEnvVar::unset(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_STDOUT_ENV),
        ScopedEnvVar::unset(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT_ENV),
        ScopedEnvVar::unset(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_COMMAND_ENV),
        ScopedEnvVar::unset(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_EXIT_STATUS_ENV),
    ];
    (guard, env)
}

fn retained_model_check_json(
    formula_path: &str,
    model_stdout_path: &str,
    num_vars: usize,
    clauses_checked: usize,
    valid: bool,
) -> Vec<u8> {
    let model_status = if valid { "valid" } else { "invalid" };
    format!(
        r#"{{"schema":"ay.satcomp-model-check/v1","formula":"{formula_path}","stdout":"{model_stdout_path}","model_status":"{model_status}","valid":{valid},"num_vars":{num_vars},"clauses_checked":{clauses_checked},"first_unsatisfied_clause":null,"elapsed_ms":0,"ay_build":{{"stamp":"dimacs-route-authority-test"}}}}"#
    )
    .into_bytes()
}

fn circuit_multiplier22_dimacs_authority_fixture(
    checker_valid: bool,
) -> (
    DimacsFormula,
    Vec<CircuitSourceFrameRow>,
    CircuitOriginalDimacsSatModelAuthorityPacket,
) {
    circuit_multiplier22_dimacs_authority_fixture_with_paths(
        checker_valid,
        "retained/dimacs-circuit-authority.cnf",
        "retained/dimacs-circuit-authority-model.stdout",
    )
}

fn circuit_multiplier22_dimacs_authority_fixture_with_paths(
    checker_valid: bool,
    formula_path: &str,
    model_stdout_path: &str,
) -> (
    DimacsFormula,
    Vec<CircuitSourceFrameRow>,
    CircuitOriginalDimacsSatModelAuthorityPacket,
) {
    let formula = parse_str(
        r"
p cnf 3 3
-3 1 0
-3 2 0
3 -1 -2 0
",
    )
    .expect("synthetic circuit CNF should parse");
    let out = Variable::new(2);
    let a = Variable::new(0);
    let b = Variable::new(1);
    let source_rows = vec![
        CircuitSourceFrameRow {
            source_row_id: 10,
            var: 0,
            literal: Literal::positive(a),
            clause_id: 0,
            source_value: true,
            family: CircuitSourceFrameFamily::W210Frontier,
            kind: CircuitSourceFrameKind::FrontierValue,
        },
        CircuitSourceFrameRow {
            source_row_id: 11,
            var: 1,
            literal: Literal::positive(b),
            clause_id: 1,
            source_value: false,
            family: CircuitSourceFrameFamily::ForcedGateReplayBridge,
            kind: CircuitSourceFrameKind::ForcedGateReplayBridge,
        },
    ];
    let authority_packet = produce_original_dimacs_sat_model_authority_packet(
        formula.num_vars,
        &formula.clauses,
        &source_rows,
        formula_path,
        model_stdout_path,
        vec![
            "ay".to_owned(),
            "check".to_owned(),
            "model".to_owned(),
            formula_path.to_owned(),
            model_stdout_path.to_owned(),
            "--json".to_owned(),
        ],
        if checker_valid { 0 } else { 1 },
        retained_model_check_json(
            formula_path,
            model_stdout_path,
            formula.num_vars,
            formula.clauses.len(),
            checker_valid,
        ),
    )
    .expect("synthetic authority packet should bind retained checker output");

    assert_eq!(out.index(), 2);
    (formula, source_rows, authority_packet)
}

fn retained_artifacts_from_authority_packet(
    packet: CircuitOriginalDimacsSatModelAuthorityPacket,
    checker_verdict_json: Option<Vec<u8>>,
) -> CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifacts {
    CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifacts {
        formula_path: packet.artifacts.formula.path,
        formula_bytes: packet.formula_dimacs,
        model_stdout_path: packet.artifacts.model_stdout.path,
        model_stdout_bytes: packet.model_stdout,
        checker_command: packet.artifacts.checker_command,
        checker_exit_status: packet.checker_evidence.checker_exit_status,
        checker_verdict_json,
    }
}

fn retained_artifact_paths_from_authority_packet(
    formula_path: PathBuf,
    model_stdout_path: PathBuf,
    checker_verdict_json_path: PathBuf,
    packet: &CircuitOriginalDimacsSatModelAuthorityPacket,
) -> CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactPaths {
    CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactPaths {
        formula_path,
        model_stdout_path,
        checker_verdict_json_path,
        checker_command: packet.artifacts.checker_command.clone(),
        checker_exit_status: packet.checker_evidence.checker_exit_status,
    }
}

fn run_matrix_artifacts_from_authority_packet(
    formula_path: PathBuf,
    model_stdout_path: PathBuf,
    checker_verdict_json_path: PathBuf,
    packet: &CircuitOriginalDimacsSatModelAuthorityPacket,
) -> CircuitMultiplier22DimacsSatModelAuthorityRunMatrixArtifacts {
    CircuitMultiplier22DimacsSatModelAuthorityRunMatrixArtifacts {
        model_checker_formula: formula_path,
        model_checker_stdout: model_stdout_path,
        model_checker_artifact: checker_verdict_json_path,
        checker_command: packet.artifacts.checker_command.clone(),
        checker_exit_status: packet.checker_evidence.checker_exit_status,
    }
}

#[test]
fn multiplier_equivalence_conservation_diagnostic_stays_fail_closed() {
    let formula = DimacsFormula {
        num_vars: 2540,
        num_clauses: 8495,
        clauses: Vec::new(),
    };

    let diagnostic = formula.multiplier_equivalence_conservation_diagnostic();

    assert_eq!(diagnostic.target_issue, 9725);
    assert_eq!(diagnostic.lean_admission_contract_issue, 9733);
    assert_eq!(diagnostic.lean_conservation_contract_issue, 9736);
    assert!(diagnostic.official_shape_candidate);
    assert!(!diagnostic.structural_candidate);
    assert!(!diagnostic.diagnostic_candidate);
    assert!(diagnostic.fail_closed);
    assert!(!diagnostic.route_admitted);
    assert!(!diagnostic.result_authority);
    assert!(!diagnostic.proof_output_authority);
    assert!(!diagnostic.proof_replay_checked);
    assert!(!diagnostic.external_checker_verified);
    assert_eq!(diagnostic.weighted_conservation_obligation_rows, 0);
    assert_eq!(diagnostic.source_clause_bound_rows, 0);
    assert_eq!(diagnostic.source_clause_bindings_missing, 0);
    assert_eq!(diagnostic.source_gate_clause_references, 0);
    assert_eq!(diagnostic.source_gate_clause_bound_references, 0);
}

#[test]
fn multiplier_equivalence_conservation_diagnostic_rejects_non_target_shape() {
    let formula = parse_str(
        r"
p cnf 3 3
-3 1 0
-3 2 0
3 -1 -2 0
",
    )
    .expect("synthetic AND gate should parse");

    let diagnostic = formula.multiplier_equivalence_conservation_diagnostic();

    assert!(!diagnostic.official_shape_candidate);
    assert!(diagnostic.fail_closed);
    assert_eq!(diagnostic.route_blocker_code, 10);
    assert_eq!(diagnostic.weighted_conservation_obligation_rows, 1);
    assert_eq!(diagnostic.source_clause_bound_rows, 0);
    assert_eq!(diagnostic.source_clause_bindings_missing, 1);
    assert_eq!(diagnostic.source_gate_clause_references, 3);
    assert_eq!(diagnostic.source_gate_clause_bound_references, 3);
    assert_eq!(diagnostic.source_gate_clause_binding_missing_references, 0);
    assert_eq!(diagnostic.source_gate_clause_duplicate_references, 0);
    assert_eq!(diagnostic.source_gate_clause_out_of_range_references, 0);
    assert_eq!(diagnostic.source_gate_clause_literal_mismatch_references, 0);
    assert!(!diagnostic.route_admitted);
    assert!(!diagnostic.result_authority);
    assert!(!diagnostic.proof_output_authority);
    assert!(!diagnostic.proof_replay_checked);
    assert!(!diagnostic.external_checker_verified);
}

fn retained_authority_file_fixture_with_checker_json<F>(
    checker_json: F,
) -> (
    tempfile::TempDir,
    DimacsFormula,
    Vec<CircuitSourceFrameRow>,
    CircuitOriginalDimacsSatModelAuthorityPacket,
    PathBuf,
    PathBuf,
    PathBuf,
)
where
    F: FnOnce(&CircuitOriginalDimacsSatModelAuthorityPacket) -> Vec<u8>,
{
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(&formula_path, &authority_packet.formula_dimacs).expect("write retained formula");
    fs::write(&model_stdout_path, &authority_packet.model_stdout)
        .expect("write retained model stdout");
    fs::write(&checker_verdict_json_path, checker_json(&authority_packet))
        .expect("write retained checker verdict");
    (
        dir,
        formula,
        source_rows,
        authority_packet,
        formula_path,
        model_stdout_path,
        checker_verdict_json_path,
    )
}

fn checker_json_without_field(
    packet: &CircuitOriginalDimacsSatModelAuthorityPacket,
    field: &str,
) -> Vec<u8> {
    let mut payload: serde_json::Value =
        serde_json::from_slice(&packet.checker_verdict_json).expect("checker json parses");
    payload
        .as_object_mut()
        .expect("checker json is object")
        .remove(field);
    serde_json::to_vec(&payload).expect("checker json serializes")
}

fn checker_json_with_field(
    packet: &CircuitOriginalDimacsSatModelAuthorityPacket,
    field: &str,
    value: serde_json::Value,
) -> Vec<u8> {
    let mut payload: serde_json::Value =
        serde_json::from_slice(&packet.checker_verdict_json).expect("checker json parses");
    payload
        .as_object_mut()
        .expect("checker json is object")
        .insert(field.to_owned(), value);
    serde_json::to_vec(&payload).expect("checker json serializes")
}

#[must_use]
fn set_circuit_multiplier22_dimacs_authority_env(
    formula_path: &Path,
    model_stdout_path: &Path,
    checker_verdict_json_path: &Path,
    checker_command: &[String],
    checker_exit_status: i32,
) -> [ScopedEnvVar; 6] {
    [
        ScopedEnvVar::set(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV, "1"),
        ScopedEnvVar::set(
            CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_FORMULA_ENV,
            formula_path.to_str().expect("formula path utf8"),
        ),
        ScopedEnvVar::set(
            CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_STDOUT_ENV,
            model_stdout_path.to_str().expect("model stdout path utf8"),
        ),
        ScopedEnvVar::set(
            CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT_ENV,
            checker_verdict_json_path
                .to_str()
                .expect("checker verdict path utf8"),
        ),
        ScopedEnvVar::set(
            CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_COMMAND_ENV,
            serde_json::to_string(checker_command).expect("checker command json"),
        ),
        ScopedEnvVar::set(
            CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_EXIT_STATUS_ENV,
            checker_exit_status.to_string(),
        ),
    ]
}

#[test]
fn test_parse_simple() {
    let input = r"
c A simple CNF
p cnf 3 2
1 -2 3 0
-1 2 0
";
    let formula = parse_str(input).unwrap();
    assert_eq!(formula.num_vars, 3);
    assert_eq!(formula.num_clauses, 2);
    assert_eq!(formula.clauses.len(), 2);

    // First clause: x1 OR NOT x2 OR x3
    assert_eq!(formula.clauses[0].len(), 3);
    assert_eq!(formula.clauses[0][0], Literal::positive(Variable(0)));
    assert_eq!(formula.clauses[0][1], Literal::negative(Variable(1)));
    assert_eq!(formula.clauses[0][2], Literal::positive(Variable(2)));

    // Second clause: NOT x1 OR x2
    assert_eq!(formula.clauses[1].len(), 2);
    assert_eq!(formula.clauses[1][0], Literal::negative(Variable(0)));
    assert_eq!(formula.clauses[1][1], Literal::positive(Variable(1)));
}

#[test]
fn test_dimacs_solver_sizes_by_actual_vars_not_declared_header() {
    // Root cause: an over-declared header must NOT drive the solver's dense
    // per-variable allocation. This declares 4e9 variables but uses only 3, so
    // it is a valid 3-variable instance (it was a ~69 GB OOM when `Solver::new`
    // trusted the declared count).
    let formula = parse_str("p cnf 4000000000 1\n1 -2 3 0\n")
        .expect("over-declared header must parse, not error/OOM");
    // The declared count is preserved as metadata (model counting needs it)...
    assert_eq!(formula.num_vars, 4_000_000_000);
    // ...but the constructed solver allocates only for the variables that
    // actually appear, so it does not OOM.
    let solver = formula.into_solver();
    assert_eq!(
        solver.user_num_vars(),
        3,
        "solver is sized by the actual maximum variable, not the declared header"
    );

    // A lying clause count must not OOM either (the speculative reserve is
    // bounded and the real vector stays tiny).
    let f2 = parse_str("p cnf 3 4000000000\n1 -2 3 0\n").expect("huge clause count must not OOM");
    assert_eq!(f2.num_vars, 3);
    assert_eq!(f2.clauses.len(), 1);

    // The only thing refused at parse time is a pathological *actual* variable
    // index: dense numbering makes the per-variable arrays O(max index), so
    // explicitly referencing a variable beyond the backstop is rejected (var 2e9
    // < i32::MAX parses, but exceeds MAX_DIMACS_VARS).
    let err = parse_str("p cnf 2000000000 1\n2000000000 0\n")
        .expect_err("explicitly referencing var 2e9 must be refused");
    assert!(
        matches!(err, DimacsError::HeaderCountTooLarge { .. }),
        "expected HeaderCountTooLarge for a pathological actual index, got {err:?}"
    );
}

#[test]
fn test_into_solver_dimacs_policy_defaults() {
    let formula = DimacsFormula {
        num_vars: 3,
        num_clauses: 1,
        clauses: vec![vec![
            Literal::positive(Variable(0)),
            Literal::negative(Variable(1)),
        ]],
    };

    let solver = formula.into_solver();
    // Default flipped 2026-07-08 (post ef818369): the sparse-band BVE
    // unlock is ON by default; this tiny formula is in-band, so BVE is
    // enabled. AY_AB_BVE_SPARSE=0 is the kill-switch (asserted hermetically
    // when set).
    if crate::variant::ab_bve_sparse_knob_set() {
        assert!(
            solver.is_bve_enabled(),
            "DIMACS default enables BVE for in-band inputs \
             (sparse-band unlock default-ON)"
        );
    } else {
        assert!(
            !solver.is_bve_enabled(),
            "kill-switch (AY_AB_BVE_SPARSE=0) restores BVE-off"
        );
    }
    // Default flipped 2026-07-10 (wf_55735963): the route-aware
    // substitution-collapse AUTO is ON by default on the non-proof Default
    // route (+7 measured UNSAT flips / 0 hard losses, main2025 scoreboard
    // protocol); the expensive fixpoint stays gated behind the one-round
    // equivalence-density probe at preprocess time. AY_AB_SUBST_AUTO=0 is
    // the kill-switch (asserted hermetically when set).
    match std::env::var("AY_AB_SUBST_AUTO").ok().as_deref() {
        None | Some("1") => {
            assert!(
                solver.is_congruence_enabled(),
                "DIMACS default enables congruence eligibility (AUTO \
                 default-ON, probe-gated; wf_55735963)"
            );
            assert!(
                solver.is_decompose_enabled(),
                "DIMACS default enables decompose eligibility (AUTO \
                 default-ON, probe-gated; wf_55735963)"
            );
        }
        Some(_) => {
            assert!(
                !solver.is_congruence_enabled(),
                "kill-switch (AY_AB_SUBST_AUTO=0) restores congruence-off"
            );
            assert!(
                !solver.is_decompose_enabled(),
                "kill-switch (AY_AB_SUBST_AUTO=0) restores decompose-off"
            );
        }
    }
    assert!(
        solver.is_subsume_enabled(),
        "DIMACS solver should enable subsumption (#4872 one-watch forward)"
    );
    assert!(
        solver.is_factor_enabled(),
        "DIMACS solver should keep factorization enabled for structured SAT workloads"
    );
    assert!(
        !solver.stable_only_enabled(),
        "DIMACS solver should use CaDiCaL-style focused/stable alternation"
    );
    // Small formulas (< 5K vars) get full BVE/subsumption effort.
    // Only large formulas (> DIMACS_PROOF_REDUCED_EFFORT_MIN_VARS = 5K)
    // get the reduced effort budgets (BVE=10, subsume=60).
    assert_eq!(
        solver.bve_effort_permille(),
        1000,
        "Small DIMACS formulas (<5K vars) should keep full BVE effort"
    );
    assert_eq!(
        solver.subsume_effort_permille(),
        1000,
        "Small DIMACS formulas (<5K vars) should keep full subsumption effort"
    );
    assert!(
        solver.is_full_preprocessing_enabled(),
        "small DIMACS formulas should keep full preprocessing enabled"
    );
}

#[test]
fn test_into_solver_large_dimacs_keeps_quick_preprocessing() {
    let formula = DimacsFormula {
        num_vars: 10_000,
        num_clauses: 5_000_001,
        clauses: vec![],
    };

    let solver = formula.into_solver();
    assert!(
        !solver.stable_only_enabled(),
        "DIMACS solver should use CaDiCaL-style focused/stable alternation on large formulas"
    );
    assert!(
        !solver.is_full_preprocessing_enabled(),
        "very large DIMACS formulas should stay on quick preprocessing"
    );
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_route_default_off_and_missing_evidence() {
    let (formula, source_rows, _authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture(true);

    let disabled =
        circuit_multiplier22_dimacs_sat_model_authority_route(false, &formula, &source_rows, None);
    assert_eq!(
        disabled,
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Disabled
    );
    assert!(!disabled.is_admitted());

    let missing =
        circuit_multiplier22_dimacs_sat_model_authority_route(true, &formula, &source_rows, None);
    match missing {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedEvidenceMissing
            );
            assert_eq!(counters.row_id, "Circuit_multiplier22");
            assert!(!counters.circuit_original_dimacs_model_present);
            assert_eq!(counters.circuit_original_dimacs_model_vars, 0);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("missing retained evidence should stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_route_blocks_invalid_retained_evidence() {
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture(false);

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route(
        true,
        &formula,
        &source_rows,
        Some(authority_packet),
    );

    assert!(!decision.is_admitted());
    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            let CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::FacadeBlocked {
                authority_status,
                route_admission_status,
            } = blocker
            else {
                panic!("invalid retained evidence should be rejected by facade");
            };
            assert!(!authority_status.is_admitted());
            assert_eq!(route_admission_status, counters.route_admission_status);
            assert!(!route_admission_status.is_admitted());
            assert_eq!(counters.circuit_source_frame_rows, source_rows.len());
            assert!(!counters.circuit_original_dimacs_model_present);
        }
        other => panic!("invalid retained evidence should stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_route_admits_valid_synthetic_evidence() {
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture(true);

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route(
        true,
        &formula,
        &source_rows,
        Some(authority_packet),
    );

    assert!(decision.is_admitted());
    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Admitted {
            assignment,
            counters,
        } => {
            assert_eq!(assignment, vec![true, false, false]);
            assert_eq!(counters.circuit_source_frame_rows, source_rows.len());
            assert!(counters.circuit_original_dimacs_model_present);
            assert_eq!(
                counters.circuit_original_dimacs_model_vars,
                formula.num_vars
            );
            assert_eq!(
                counters.route_admission_status,
                CircuitEquivRouteAdmissionStatus::Admitted
            );
        }
        other => panic!("valid retained evidence should reach facade admission, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_retained_loader_requires_checker_json() {
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture(true);
    let retained = retained_artifacts_from_authority_packet(authority_packet, None);

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_artifacts(
        true,
        &formula,
        &source_rows,
        Some(retained),
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictJsonMissing
            );
            assert_eq!(counters.row_id, "Circuit_multiplier22");
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("missing checker JSON must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_retained_loader_rejects_model_drift() {
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture(true);
    let checker_verdict_json = Some(authority_packet.checker_verdict_json.clone());
    let mut retained =
        retained_artifacts_from_authority_packet(authority_packet, checker_verdict_json);
    retained.model_stdout_bytes = b"s SATISFIABLE\nv 1 2 3 0\n".to_vec();

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_artifacts(
        true,
        &formula,
        &source_rows,
        Some(retained),
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutBytesMismatch
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("retained model stdout drift must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_retained_loader_admits_valid_synthetic_artifacts() {
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture(true);
    let checker_verdict_json = Some(authority_packet.checker_verdict_json.clone());
    let retained = retained_artifacts_from_authority_packet(authority_packet, checker_verdict_json);

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_artifacts(
        true,
        &formula,
        &source_rows,
        Some(retained),
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Admitted {
            assignment,
            counters,
        } => {
            assert_eq!(assignment, vec![true, false, false]);
            assert!(counters.circuit_original_dimacs_model_present);
            assert_eq!(
                counters.circuit_original_dimacs_model_vars,
                formula.num_vars
            );
            assert_eq!(
                counters.route_admission_status,
                CircuitEquivRouteAdmissionStatus::Admitted
            );
        }
        other => panic!("valid retained artifacts should reach facade admission, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_path_loader_requires_each_artifact() {
    for missing in [
        CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::Formula,
        CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::ModelStdout,
        CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::CheckerVerdictJson,
    ] {
        let dir = tempfile::tempdir().expect("tempdir");
        let formula_path = dir.path().join("formula.cnf");
        let model_stdout_path = dir.path().join("model.stdout");
        let checker_verdict_json_path = dir.path().join("checker.json");
        let (formula, source_rows, authority_packet) =
            circuit_multiplier22_dimacs_authority_fixture_with_paths(
                true,
                formula_path.to_str().expect("formula path utf8"),
                model_stdout_path.to_str().expect("model stdout path utf8"),
            );
        if missing != CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::Formula {
            fs::write(&formula_path, &authority_packet.formula_dimacs)
                .expect("write retained formula");
        }
        if missing != CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::ModelStdout {
            fs::write(&model_stdout_path, &authority_packet.model_stdout)
                .expect("write retained model stdout");
        }
        if missing
            != CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::CheckerVerdictJson
        {
            fs::write(
                &checker_verdict_json_path,
                &authority_packet.checker_verdict_json,
            )
            .expect("write retained checker verdict");
        }
        let retained_paths = retained_artifact_paths_from_authority_packet(
            formula_path,
            model_stdout_path,
            checker_verdict_json_path,
            &authority_packet,
        );

        let decision =
            circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_artifact_paths(
                true,
                &formula,
                &source_rows,
                Some(retained_paths),
            );

        match decision {
            CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked {
                blocker,
                counters,
            } => {
                assert_eq!(
                    blocker,
                    CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedArtifactMissing(
                        missing
                    )
                );
                assert!(!counters.circuit_original_dimacs_model_present);
                assert!(!counters.route_admission_status.is_admitted());
            }
            other => panic!("missing retained artifact must stay blocked, got {other:?}"),
        }
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_path_loader_rejects_model_artifact_drift() {
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(&formula_path, &authority_packet.formula_dimacs).expect("write retained formula");
    fs::write(&model_stdout_path, b"s SATISFIABLE\nv 1 2 3 0\n")
        .expect("write drifted retained model stdout");
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let retained_paths = retained_artifact_paths_from_authority_packet(
        formula_path,
        model_stdout_path,
        checker_verdict_json_path,
        &authority_packet,
    );

    let decision =
        circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_artifact_paths(
            true,
            &formula,
            &source_rows,
            Some(retained_paths),
        );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutBytesMismatch
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("drifted model artifact must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_path_loader_admits_valid_synthetic_artifacts() {
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(&formula_path, &authority_packet.formula_dimacs).expect("write retained formula");
    fs::write(&model_stdout_path, &authority_packet.model_stdout)
        .expect("write retained model stdout");
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let retained_paths = retained_artifact_paths_from_authority_packet(
        formula_path,
        model_stdout_path,
        checker_verdict_json_path,
        &authority_packet,
    );

    let decision =
        circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_artifact_paths(
            true,
            &formula,
            &source_rows,
            Some(retained_paths),
        );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Admitted {
            assignment,
            counters,
        } => {
            assert_eq!(assignment, vec![true, false, false]);
            assert!(counters.circuit_original_dimacs_model_present);
            assert_eq!(
                counters.circuit_original_dimacs_model_vars,
                formula.num_vars
            );
            assert_eq!(
                counters.route_admission_status,
                CircuitEquivRouteAdmissionStatus::Admitted
            );
        }
        other => panic!("valid retained artifact paths should admit, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_run_matrix_handoff_uses_retained_path_loader() {
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(&formula_path, &authority_packet.formula_dimacs).expect("write retained formula");
    fs::write(&model_stdout_path, &authority_packet.model_stdout)
        .expect("write retained model stdout");
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let retained = run_matrix_artifacts_from_authority_packet(
        formula_path,
        model_stdout_path,
        checker_verdict_json_path,
        &authority_packet,
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_run_matrix_artifacts(
        true,
        &formula,
        &source_rows,
        Some(retained),
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Admitted {
            assignment,
            counters,
        } => {
            assert_eq!(assignment, vec![true, false, false]);
            assert!(counters.circuit_original_dimacs_model_present);
            assert_eq!(
                counters.route_admission_status,
                CircuitEquivRouteAdmissionStatus::Admitted
            );
        }
        other => {
            panic!("run/matrix artifacts should hand off to retained path admission: {other:?}")
        }
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_run_matrix_handoff_blocks_missing_checker_artifact() {
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(&formula_path, &authority_packet.formula_dimacs).expect("write retained formula");
    fs::write(&model_stdout_path, &authority_packet.model_stdout)
        .expect("write retained model stdout");
    let retained = run_matrix_artifacts_from_authority_packet(
        formula_path,
        model_stdout_path,
        checker_verdict_json_path,
        &authority_packet,
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_run_matrix_artifacts(
        true,
        &formula,
        &source_rows,
        Some(retained),
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedArtifactMissing(
                    CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::CheckerVerdictJson
                )
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("missing run/matrix checker artifact must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_run_matrix_handoff_rejects_formula_path_drift() {
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let drift_formula_path = dir.path().join("drift-formula.cnf");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let retained = run_matrix_artifacts_from_authority_packet(
        drift_formula_path,
        model_stdout_path,
        checker_verdict_json_path,
        &authority_packet,
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_run_matrix_artifacts(
        true,
        &formula,
        &source_rows,
        Some(retained),
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictFormulaPathMismatch
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("formula path drift must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_run_matrix_handoff_rejects_stdout_path_drift() {
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let drift_model_stdout_path = dir.path().join("drift-model.stdout");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let retained = run_matrix_artifacts_from_authority_packet(
        formula_path,
        drift_model_stdout_path,
        checker_verdict_json_path,
        &authority_packet,
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_run_matrix_artifacts(
        true,
        &formula,
        &source_rows,
        Some(retained),
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictModelStdoutPathMismatch
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("model stdout path drift must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_run_matrix_handoff_rejects_checker_command_drift() {
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let drift_model_stdout_path = dir.path().join("drift-model.stdout");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(&formula_path, &authority_packet.formula_dimacs).expect("write retained formula");
    fs::write(&model_stdout_path, &authority_packet.model_stdout)
        .expect("write retained model stdout");
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let mut retained = run_matrix_artifacts_from_authority_packet(
        formula_path,
        model_stdout_path,
        checker_verdict_json_path,
        &authority_packet,
    );
    retained.checker_command[4] = drift_model_stdout_path
        .to_str()
        .expect("drift model stdout path utf8")
        .to_owned();

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_run_matrix_artifacts(
        true,
        &formula,
        &source_rows,
        Some(retained),
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerCommandModelStdoutPathMismatch
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("checker command model stdout drift must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_requires_complete_run_matrix_artifacts() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let _authority_env = [
        ScopedEnvVar::set(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV, "1"),
        ScopedEnvVar::set(
            CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_FORMULA_ENV,
            "formula.cnf",
        ),
    ];
    let (formula, source_rows, _authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture(true);

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
        &formula,
        &source_rows,
        None,
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedArtifactPathEnvMissing(
                    CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::ModelStdout
                )
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("partial run/matrix env handoff must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_accepts_complete_matrix_fields() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(&formula_path, &authority_packet.formula_dimacs).expect("write retained formula");
    fs::write(&model_stdout_path, &authority_packet.model_stdout)
        .expect("write retained model stdout");
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let _g = ScopedEnvVar::set(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV, "1");
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_FORMULA_ENV,
        formula_path.to_str().expect("formula path utf8"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_STDOUT_ENV,
        model_stdout_path.to_str().expect("model stdout path utf8"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT_ENV,
        checker_verdict_json_path
            .to_str()
            .expect("checker verdict path utf8"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_COMMAND_ENV,
        serde_json::to_string(&authority_packet.artifacts.checker_command)
            .expect("checker command json"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_EXIT_STATUS_ENV,
        authority_packet
            .checker_evidence
            .checker_exit_status
            .to_string(),
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
        &formula,
        &source_rows,
        None,
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Admitted {
            assignment,
            counters,
        } => {
            assert_eq!(assignment, vec![true, false, false]);
            assert!(counters.circuit_original_dimacs_model_present);
            assert_eq!(
                counters.route_admission_status,
                CircuitEquivRouteAdmissionStatus::Admitted
            );
        }
        other => panic!("complete run/matrix env fields should admit, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_retained_stdout_admits_complete_checker_artifact(
) {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let (
        _dir,
        formula,
        _source_rows,
        authority_packet,
        formula_path,
        model_stdout_path,
        checker_verdict_json_path,
    ) = retained_authority_file_fixture_with_checker_json(|packet| {
        packet.checker_verdict_json.clone()
    });
    let _authority_env = set_circuit_multiplier22_dimacs_authority_env(
        &formula_path,
        &model_stdout_path,
        &checker_verdict_json_path,
        &authority_packet.artifacts.checker_command,
        authority_packet.checker_evidence.checker_exit_status,
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env_retained_stdout(
        &formula,
        &authority_packet.formula_dimacs,
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Admitted {
            assignment,
            counters,
        } => {
            assert_eq!(assignment, vec![true, false, false]);
            assert!(counters.circuit_original_dimacs_model_present);
            assert_eq!(
                counters.circuit_original_dimacs_model_vars,
                formula.num_vars
            );
            assert_eq!(
                counters.route_admission_status,
                CircuitEquivRouteAdmissionStatus::Admitted
            );
        }
        other => panic!("retained checker artifact should admit retained stdout, got {other:?}"),
    }

    assert_eq!(
        formula.circuit_multiplier22_retained_sat_model_from_env(&authority_packet.formula_dimacs),
        Some(vec![true, false, false])
    );
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_retained_stdout_rejects_formula_drift() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let (
        _dir,
        formula,
        _source_rows,
        authority_packet,
        formula_path,
        model_stdout_path,
        checker_verdict_json_path,
    ) = retained_authority_file_fixture_with_checker_json(|packet| {
        packet.checker_verdict_json.clone()
    });
    let _authority_env = set_circuit_multiplier22_dimacs_authority_env(
        &formula_path,
        &model_stdout_path,
        &checker_verdict_json_path,
        &authority_packet.artifacts.checker_command,
        authority_packet.checker_evidence.checker_exit_status,
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env_retained_stdout(
        &formula,
        b"p cnf 3 1\n1 0\n",
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedFormulaBytesMismatch
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("retained formula byte drift must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_retained_stdout_rejects_model_drift() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let (
        _dir,
        formula,
        _source_rows,
        authority_packet,
        formula_path,
        model_stdout_path,
        checker_verdict_json_path,
    ) = retained_authority_file_fixture_with_checker_json(|packet| {
        packet.checker_verdict_json.clone()
    });
    fs::write(&model_stdout_path, b"s SATISFIABLE\nv -1 -2 3 0\n")
        .expect("write drifted retained model stdout");
    let _authority_env = set_circuit_multiplier22_dimacs_authority_env(
        &formula_path,
        &model_stdout_path,
        &checker_verdict_json_path,
        &authority_packet.artifacts.checker_command,
        authority_packet.checker_evidence.checker_exit_status,
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env_retained_stdout(
        &formula,
        &authority_packet.formula_dimacs,
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutInvalid
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("retained model stdout drift must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_retained_stdout_blocks_status_drift() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let (
        _dir,
        formula,
        _source_rows,
        authority_packet,
        formula_path,
        model_stdout_path,
        checker_verdict_json_path,
    ) = retained_authority_file_fixture_with_checker_json(|packet| {
        packet.checker_verdict_json.clone()
    });
    let _authority_env = set_circuit_multiplier22_dimacs_authority_env(
        &formula_path,
        &model_stdout_path,
        &checker_verdict_json_path,
        &authority_packet.artifacts.checker_command,
        1,
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env_retained_stdout(
        &formula,
        &authority_packet.formula_dimacs,
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerExitStatusNonZero
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("retained checker status drift must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_rejects_incomplete_checker_artifact() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    for (field, expected_blocker) in [
        (
            "schema",
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictSchemaMismatch,
        ),
        (
            "model_status",
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictModelStatusMissing,
        ),
        (
            "valid",
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictValidMissing,
        ),
        (
            "num_vars",
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictNumVarsMissing,
        ),
        (
            "clauses_checked",
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictClausesCheckedMissing,
        ),
        (
            "ay_build",
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictBuildProvenanceMissing,
        ),
    ] {
        let (
            _dir,
            formula,
            source_rows,
            authority_packet,
            formula_path,
            model_stdout_path,
            checker_verdict_json_path,
        ) = retained_authority_file_fixture_with_checker_json(|packet| {
            checker_json_without_field(packet, field)
        });
        let _authority_env = set_circuit_multiplier22_dimacs_authority_env(
            &formula_path,
            &model_stdout_path,
            &checker_verdict_json_path,
            &authority_packet.artifacts.checker_command,
            authority_packet.checker_evidence.checker_exit_status,
        );

        let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
            &formula,
            &source_rows,
            None,
        );

        match decision {
            CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked {
                blocker,
                counters,
            } => {
                assert_eq!(blocker, expected_blocker, "field {field}");
                assert!(!counters.circuit_original_dimacs_model_present);
                assert!(!counters.route_admission_status.is_admitted());
            }
            other => {
                panic!("missing checker artifact field {field} must stay blocked, got {other:?}")
            }
        }
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_rejects_checker_artifact_value_drift() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    for (field, value, expected_blocker) in [
        (
            "model_status",
            serde_json::json!("invalid"),
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictModelStatusNotValid,
        ),
        (
            "valid",
            serde_json::json!(false),
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictInvalid,
        ),
        (
            "num_vars",
            serde_json::json!(4),
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictNumVarsMismatch,
        ),
        (
            "clauses_checked",
            serde_json::json!(4),
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictClausesCheckedMismatch,
        ),
        (
            "ay_build",
            serde_json::json!({"stamp": ""}),
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictBuildProvenanceMissing,
        ),
    ] {
        let (
            _dir,
            formula,
            source_rows,
            authority_packet,
            formula_path,
            model_stdout_path,
            checker_verdict_json_path,
        ) = retained_authority_file_fixture_with_checker_json(|packet| {
            checker_json_with_field(packet, field, value)
        });
        let _authority_env = set_circuit_multiplier22_dimacs_authority_env(
            &formula_path,
            &model_stdout_path,
            &checker_verdict_json_path,
            &authority_packet.artifacts.checker_command,
            authority_packet.checker_evidence.checker_exit_status,
        );

        let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
            &formula,
            &source_rows,
            None,
        );

        match decision {
            CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked {
                blocker,
                counters,
            } => {
                assert_eq!(blocker, expected_blocker, "field {field}");
                assert!(!counters.circuit_original_dimacs_model_present);
                assert!(!counters.route_admission_status.is_admitted());
            }
            other => panic!("checker artifact field {field} drift must stay blocked, got {other:?}"),
        }
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_derives_paths_from_checker_artifact() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(&formula_path, &authority_packet.formula_dimacs).expect("write retained formula");
    fs::write(&model_stdout_path, &authority_packet.model_stdout)
        .expect("write retained model stdout");
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let _g = ScopedEnvVar::set(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV, "1");
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT_ENV,
        checker_verdict_json_path
            .to_str()
            .expect("checker verdict path utf8"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_COMMAND_ENV,
        serde_json::to_string(&authority_packet.artifacts.checker_command)
            .expect("checker command json"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_EXIT_STATUS_ENV,
        authority_packet
            .checker_evidence
            .checker_exit_status
            .to_string(),
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
        &formula,
        &source_rows,
        None,
    );

    assert!(decision.is_admitted());
    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Admitted {
            assignment,
            counters,
        } => {
            assert_eq!(assignment, vec![true, false, false]);
            assert!(counters.circuit_original_dimacs_model_present);
            assert_eq!(
                counters.route_admission_status,
                CircuitEquivRouteAdmissionStatus::Admitted
            );
        }
        other => panic!("checker-artifact env handoff should admit, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_rejects_checker_command_formula_drift() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let drift_formula_path = dir.path().join("drift-formula.cnf");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(&formula_path, &authority_packet.formula_dimacs).expect("write retained formula");
    fs::write(&model_stdout_path, &authority_packet.model_stdout)
        .expect("write retained model stdout");
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let mut checker_command = authority_packet.artifacts.checker_command.clone();
    checker_command[3] = drift_formula_path
        .to_str()
        .expect("drift formula path utf8")
        .to_owned();
    let _g = ScopedEnvVar::set(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV, "1");
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT_ENV,
        checker_verdict_json_path
            .to_str()
            .expect("checker verdict path utf8"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_COMMAND_ENV,
        serde_json::to_string(&checker_command).expect("checker command json"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_EXIT_STATUS_ENV,
        authority_packet
            .checker_evidence
            .checker_exit_status
            .to_string(),
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
        &formula,
        &source_rows,
        None,
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerCommandFormulaPathMismatch
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("checker command formula drift must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_rejects_formula_path_drift() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let drift_formula_path = dir.path().join("drift-formula.cnf");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let _g = ScopedEnvVar::set(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV, "1");
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_FORMULA_ENV,
        drift_formula_path
            .to_str()
            .expect("drift formula path utf8"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT_ENV,
        checker_verdict_json_path
            .to_str()
            .expect("checker verdict path utf8"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_COMMAND_ENV,
        serde_json::to_string(&authority_packet.artifacts.checker_command)
            .expect("checker command json"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_EXIT_STATUS_ENV,
        authority_packet
            .checker_evidence
            .checker_exit_status
            .to_string(),
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
        &formula,
        &source_rows,
        None,
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictFormulaPathMismatch
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("env formula path drift must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_blocks_missing_checker_command() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let _g = ScopedEnvVar::set(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV, "1");
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT_ENV,
        checker_verdict_json_path
            .to_str()
            .expect("checker verdict path utf8"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_EXIT_STATUS_ENV,
        "0",
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
        &formula,
        &source_rows,
        None,
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerCommandEnvMissing
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("missing checker command env must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_blocks_malformed_checker_command() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let _g = ScopedEnvVar::set(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV, "1");
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT_ENV,
        checker_verdict_json_path
            .to_str()
            .expect("checker verdict path utf8"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_COMMAND_ENV,
        r#"["ay",""]"#,
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_EXIT_STATUS_ENV,
        "0",
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
        &formula,
        &source_rows,
        None,
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerCommandEnvInvalid
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("malformed checker command env must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_blocks_missing_checker_status() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let _g = ScopedEnvVar::set(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV, "1");
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT_ENV,
        checker_verdict_json_path
            .to_str()
            .expect("checker verdict path utf8"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_COMMAND_ENV,
        serde_json::to_string(&authority_packet.artifacts.checker_command)
            .expect("checker command json"),
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
        &formula,
        &source_rows,
        None,
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerExitStatusEnvMissing
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("missing checker status env must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_blocks_nonzero_checker_status() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let (
        _dir,
        formula,
        source_rows,
        authority_packet,
        formula_path,
        model_stdout_path,
        checker_verdict_json_path,
    ) = retained_authority_file_fixture_with_checker_json(|packet| {
        packet.checker_verdict_json.clone()
    });
    let _authority_env = set_circuit_multiplier22_dimacs_authority_env(
        &formula_path,
        &model_stdout_path,
        &checker_verdict_json_path,
        &authority_packet.artifacts.checker_command,
        1,
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
        &formula,
        &source_rows,
        None,
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerExitStatusNonZero
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("nonzero checker status must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_circuit_multiplier22_dimacs_authority_env_handoff_blocks_malformed_status() {
    let (_lock, _env) = circuit_multiplier22_dimacs_authority_env_guard();
    let dir = tempfile::tempdir().expect("tempdir");
    let formula_path = dir.path().join("formula.cnf");
    let model_stdout_path = dir.path().join("model.stdout");
    let checker_verdict_json_path = dir.path().join("checker.json");
    let (formula, source_rows, authority_packet) =
        circuit_multiplier22_dimacs_authority_fixture_with_paths(
            true,
            formula_path.to_str().expect("formula path utf8"),
            model_stdout_path.to_str().expect("model stdout path utf8"),
        );
    fs::write(
        &checker_verdict_json_path,
        &authority_packet.checker_verdict_json,
    )
    .expect("write retained checker verdict");
    let _g = ScopedEnvVar::set(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV, "1");
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT_ENV,
        checker_verdict_json_path
            .to_str()
            .expect("checker verdict path utf8"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_COMMAND_ENV,
        serde_json::to_string(&authority_packet.artifacts.checker_command)
            .expect("checker command json"),
    );
    let _g = ScopedEnvVar::set(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_EXIT_STATUS_ENV,
        "not-an-exit-status",
    );

    let decision = circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
        &formula,
        &source_rows,
        None,
    );

    match decision {
        CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { blocker, counters } => {
            assert_eq!(
                blocker,
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerExitStatusEnvInvalid
            );
            assert!(!counters.circuit_original_dimacs_model_present);
            assert!(!counters.route_admission_status.is_admitted());
        }
        other => panic!("malformed checker status env must stay blocked, got {other:?}"),
    }
}

#[test]
fn test_parse_multiline_clause() {
    let input = r"
p cnf 5 1
1 2 3
4 5 0
";
    let formula = parse_str(input).unwrap();
    assert_eq!(formula.clauses.len(), 1);
    assert_eq!(formula.clauses[0].len(), 5);
}

#[test]
fn test_parse_empty_clause() {
    let input = r"
p cnf 3 3
1 2 0
0
-1 0
";
    let formula = parse_str(input).unwrap();
    // Empty clauses (just "0") ARE preserved — they signal UNSAT
    assert_eq!(formula.clauses.len(), 3);
    assert_eq!(formula.clauses[0].len(), 2); // {1, 2}
    assert!(formula.clauses[1].is_empty()); // empty clause
    assert_eq!(formula.clauses[2].len(), 1); // {-1}
}

#[test]
fn test_parse_trivially_unsat_empty_clause() {
    // p cnf 0 1 with one empty clause must yield UNSAT
    let input = "p cnf 0 1\n0\n";
    let formula = parse_str(input).unwrap();
    assert_eq!(formula.clauses.len(), 1);
    assert!(formula.clauses[0].is_empty());
    // Verify the solver returns UNSAT
    let mut solver = formula.into_solver();
    assert!(solver.solve().is_unsat());
}

#[test]
fn test_missing_problem_line() {
    let input = "1 2 0";
    let result = parse_str(input);
    assert!(matches!(result, Err(DimacsError::MissingProblemLine)));
}

#[test]
fn test_variable_out_of_range() {
    let input = r"
p cnf 3 1
1 2 4 0
";
    let result = parse_str(input);
    assert!(matches!(
        result,
        Err(DimacsError::VariableOutOfRange { var: 4, max: 3, .. })
    ));
}

#[test]
fn test_qdimacs_quantifier_line_rejected_with_redirect() {
    // Regression: a QDIMACS file passes the `p cnf` content sniff, so its
    // quantifier lines used to be rejected by abusing InvalidLiteral with a
    // sentence stuffed into the token field ("invalid literal ... expected
    // integer"). They must instead produce a dedicated error that names the
    // tag and points at the QBF subcommand.
    let input = r"
p cnf 3 2
a 1 2 0
e 3 0
1 -2 0
-1 2 3 0
";
    let result = parse_str(input);
    assert!(matches!(
        result,
        Err(DimacsError::UnsupportedTaggedLine { tag: 'a' })
    ));
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("QDIMACS") && msg.contains("ay qbf solve"),
        "expected QDIMACS redirect message, got: {msg}"
    );
}

#[test]
fn test_roundtrip() {
    let input = r"
p cnf 3 2
1 -2 3 0
-1 2 0
";
    let formula = parse_str(input).unwrap();

    let mut output = Vec::new();
    write_dimacs(&mut output, formula.num_vars, &formula.clauses).unwrap();

    let reparsed = parse(&output[..]).unwrap();
    assert_eq!(reparsed.num_vars, formula.num_vars);
    assert_eq!(reparsed.clauses.len(), formula.clauses.len());
}

#[test]
fn test_into_solver() {
    let input = r"
p cnf 3 2
1 -2 0
-1 2 0
";
    let formula = parse_str(input).unwrap();
    let solver = formula.into_solver();
    // Just verify it doesn't panic
    assert_eq!(solver.value(Variable(0)), None);
}

#[test]
fn test_percent_terminator() {
    // Some DIMACS files use '%' as end-of-file marker
    // This format is common in SAT competition benchmarks
    let input = r"
p cnf 3 2
1 -2 0
-1 2 0
%
0
";
    let formula = parse_str(input).unwrap();
    assert_eq!(formula.num_vars, 3);
    assert_eq!(formula.clauses.len(), 2);
}

#[test]
fn test_percent_terminates_parsing() {
    // '%' is an end-of-file marker; content after it is not parsed
    let input = r"
p cnf 3 2
1 -2 0
% end of file
-1 2 0
";
    let formula = parse_str(input).unwrap();
    // Only 1 clause before the '%' marker
    assert_eq!(formula.clauses.len(), 1);
}
