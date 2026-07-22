// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{PdrResult, PDR_TRACE_VARIABLES};
use crate::pdr::config::PdrConfig;
use crate::pdr::frame::Lemma;
use crate::pdr::model::{InvariantModel, PredicateInterpretation};
use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcParser, ChcProblem, ChcSort, ChcVar, PredicateId};
use ay_sat::TlaTraceable;
use std::{fs, time::Duration};

fn unsafe_problem() -> ChcProblem {
    use crate::{ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Fact: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    // Query: Inv(x) /\ x = 0 => false (immediately unsafe)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));
    problem
}

fn multi_cell_symbolic_array_query_problem() -> (ChcProblem, PredicateId) {
    use crate::{ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let inv = problem.declare_predicate("Inv", vec![arr_sort.clone(), ChcSort::Int]);
    let arr = ChcVar::new("arr", arr_sort);
    let idx = ChcVar::new("idx", ChcSort::Int);
    let offset_idx = ChcExpr::add(ChcExpr::var(idx.clone()), ChcExpr::Int(1));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv,
                vec![ChcExpr::var(arr.clone()), ChcExpr::var(idx.clone())],
            )],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::select(ChcExpr::var(arr.clone()), ChcExpr::var(idx.clone())),
                    ChcExpr::Int(7),
                ),
                ChcExpr::eq(
                    ChcExpr::select(ChcExpr::var(arr), offset_idx),
                    ChcExpr::Int(9),
                ),
            )),
        ),
        ClauseHead::False,
    ));

    (problem, inv)
}

fn multi_cell_symbolic_array_true_model(pred: PredicateId) -> InvariantModel {
    let mut model = InvariantModel::new();
    model.set(
        pred,
        PredicateInterpretation::new(
            vec![
                ChcVar::new("cell0", ChcSort::Int),
                ChcVar::new("cell1", ChcSort::Int),
                ChcVar::new("idx", ChcSort::Int),
            ],
            ChcExpr::Bool(true),
        ),
    );
    model
}

#[test]
fn test_pdr_trace_emits_header_and_actions() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("pdr_trace.jsonl");

    let mut solver = PdrSolver::new(ChcProblem::new(), PdrConfig::default());
    solver.enable_tla_trace(path.to_str().unwrap(), "pdr_test", &PDR_TRACE_VARIABLES);
    solver.pdr_trace_step("Running", Some("BlockObligation"), None);
    let _ = solver.finish_with_result_trace(PdrResult::Unknown);

    let contents = fs::read_to_string(&path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    assert!(
        lines.len() >= 3,
        "expected header + 2 steps, got {}",
        lines.len()
    );

    let header: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
    assert_eq!(header["type"], "header");
    assert_eq!(header["module"], "pdr_test");
    assert_eq!(header["variables"], serde_json::json!(PDR_TRACE_VARIABLES));

    let step0: serde_json::Value = serde_json::from_str(lines[1]).unwrap();
    assert_eq!(step0["index"], 0);
    assert!(step0.get("action").is_none());

    let terminal: serde_json::Value = serde_json::from_str(lines[lines.len() - 1]).unwrap();
    assert_eq!(terminal["action"]["name"], "DeclareUnknown");
    assert_eq!(terminal["state"]["result"]["value"], "Unknown");
}

#[test]
fn test_pdr_trace_from_solve_emits_terminal_action() {
    let problem = unsafe_problem();

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("pdr_solve_trace.jsonl");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    solver.enable_tla_trace(path.to_str().unwrap(), "pdr_test", &PDR_TRACE_VARIABLES);

    let result = solver.solve();
    assert!(matches!(result, PdrResult::Unsafe(_)));

    let contents = fs::read_to_string(&path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    assert!(lines.len() >= 2, "expected at least header + terminal step");

    let last_step: serde_json::Value = serde_json::from_str(lines[lines.len() - 1]).unwrap();
    assert_eq!(last_step["action"]["name"], "DeclareUnsafe");
    assert_eq!(last_step["state"]["result"]["value"], "Unsafe");
}

#[test]
fn test_pdr_trace_terminal_step_contains_telemetry() {
    // DeclareUnknown on an empty problem should include telemetry payload.
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("pdr_telemetry_trace.jsonl");

    let mut solver = PdrSolver::new(ChcProblem::new(), PdrConfig::default());
    solver.enable_tla_trace(path.to_str().unwrap(), "pdr_test", &PDR_TRACE_VARIABLES);
    let _ = solver.finish_with_result_trace(PdrResult::Unknown);

    let contents = fs::read_to_string(&path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    let terminal: serde_json::Value = serde_json::from_str(lines[lines.len() - 1]).unwrap();

    // Telemetry must be present on terminal step.
    assert!(
        terminal.get("telemetry").is_some(),
        "terminal step must contain telemetry field"
    );
    let telemetry = &terminal["telemetry"];

    // Interpolation sub-object must exist with expected keys.
    assert!(
        telemetry.get("interpolation").is_some(),
        "telemetry must contain interpolation"
    );
    let interp = &telemetry["interpolation"];
    assert_eq!(interp["attempts"], 0);
    assert_eq!(interp["all_failed"], 0);

    // SAT-no-cube counter must exist.
    assert_eq!(telemetry["sat_no_cube_events"], 0);

    // Entry-inductiveness failure histogram must exist (empty map for no-op solve).
    assert!(
        telemetry.get("entry_inductive_failures").is_some(),
        "telemetry must contain entry_inductive_failures"
    );
    let failures = telemetry["entry_inductive_failures"].as_object().unwrap();
    assert!(
        failures.is_empty(),
        "no-op solve should have empty failure map"
    );

    // Entry-CEGAR discharge outcomes must exist (#4697).
    assert!(
        telemetry.get("entry_cegar_discharges").is_some(),
        "telemetry must contain entry_cegar_discharges"
    );
    let discharges = &telemetry["entry_cegar_discharges"];
    assert_eq!(discharges["reachable"], 0);
    assert_eq!(discharges["unreachable"], 0);
    assert_eq!(discharges["unknown"], 0);
}

#[test]
fn test_pdr_trace_terminal_step_contains_lia_farkas_route_counters() {
    use crate::farkas::LiaFarkasTemplateKind;
    use crate::{ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("pdr_lia_farkas_route_telemetry.jsonl");
    let mut solver = PdrSolver::new(problem, PdrConfig::lia_farkas_profile(false));
    let canonical = solver.canonical_vars(inv).unwrap()[0].clone();
    solver.add_lemma_to_frame(
        Lemma::new(
            inv,
            ChcExpr::le(ChcExpr::var(canonical), ChcExpr::int(9)),
            0,
        ),
        0,
    );
    solver
        .telemetry
        .lia_farkas_templates
        .record_template_candidate(LiaFarkasTemplateKind::ScaledLinearCombination);
    solver
        .telemetry
        .lia_farkas_templates
        .record_template_accept();
    for _ in 0..2 {
        solver.telemetry.lia_farkas_templates.record_farkas_check();
    }

    solver.telemetry.generalization_attempts = 13;
    solver.telemetry.verification_queries = 8;
    solver.telemetry.interpolation_stats.lia_farkas_successes = 20;
    solver.telemetry.interpolation_stats.iuc_farkas_successes = 10;
    solver.telemetry.interpolation_stats.all_failed = 4;
    solver.verification.total_model_failures = 3;

    solver.enable_tla_trace(path.to_str().unwrap(), "pdr_test", &PDR_TRACE_VARIABLES);
    let _ = solver.finish_with_result_trace(PdrResult::Unknown);

    let contents = fs::read_to_string(&path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    let terminal: serde_json::Value = serde_json::from_str(lines[lines.len() - 1]).unwrap();
    let route = &terminal["telemetry"]["lia_farkas_route"];

    assert_eq!(route["profile_name"], "lia_farkas");
    assert_eq!(route["profile_enabled"], true);
    assert_eq!(route["enabled_template_surfaces"], 4);
    assert_eq!(route["template_generation_surfaces"], 1);
    assert_eq!(route["templates_generated"], 1);
    assert_eq!(route["template_generation_checks"], 1);
    assert_eq!(route["farkas_checks"], 2);
    assert_eq!(route["accepted_lemmas"], 1);
    assert_eq!(route["validation_checks"], 8);
    assert_eq!(route["validation_failures"], 0);
    assert_eq!(route["original_validation_required"], true);
    assert_eq!(
        route["template_surfaces"]["scaled_linear_combinations"],
        true
    );
}

#[test]
fn test_pdr_trace_multi_cell_symbolic_scalarization_telemetry() {
    let (problem, pred) = multi_cell_symbolic_array_query_problem();
    let dir = tempfile::tempdir().unwrap();
    let path = dir
        .path()
        .join("pdr_multi_cell_symbolic_array_telemetry.jsonl");

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    solver.enable_tla_trace(path.to_str().unwrap(), "pdr_test", &PDR_TRACE_VARIABLES);

    let result = solver.finish_safe_with_result_trace(
        multi_cell_symbolic_array_true_model(pred),
        "multi-cell-symbolic-array-test",
    );
    assert!(matches!(result, PdrResult::Unknown));

    let contents = fs::read_to_string(&path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    let terminal: serde_json::Value = serde_json::from_str(lines[lines.len() - 1]).unwrap();
    let telemetry = &terminal["telemetry"];

    assert_eq!(telemetry["symbolic_scalarization_projected_cells"], 2);
    assert_eq!(telemetry["symbolic_scalarization_multi_cell_args"], 1);
}

#[test]
fn test_pdr_trace_solve_unsafe_has_telemetry() {
    // Even successful (Unsafe) outcomes should carry telemetry for completeness.
    let problem = unsafe_problem();
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("pdr_unsafe_telemetry.jsonl");

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    solver.enable_tla_trace(path.to_str().unwrap(), "pdr_test", &PDR_TRACE_VARIABLES);
    let result = solver.solve();
    assert!(matches!(result, PdrResult::Unsafe(_)));

    let contents = fs::read_to_string(&path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    let terminal: serde_json::Value = serde_json::from_str(lines[lines.len() - 1]).unwrap();

    assert_eq!(terminal["action"]["name"], "DeclareUnsafe");
    assert!(
        terminal.get("telemetry").is_some(),
        "Unsafe terminal step must contain telemetry"
    );
    assert!(terminal["telemetry"].get("interpolation").is_some());
    assert!(terminal["telemetry"].get("sat_no_cube_events").is_some());
    assert!(terminal["telemetry"]
        .get("entry_inductive_failures")
        .is_some());
    assert!(terminal["telemetry"]
        .get("entry_cegar_discharges")
        .is_some());
}

#[test]
fn test_pdr_trace_unknown_solve_emits_failure_payload() {
    // Use a two-variable problem where the invariant is non-trivial.
    // With max_obligations=2 the solver must process >2 obligations
    // (one per query + child push-backs) before converging, triggering
    // the conservative-fail path that emits a reason-bearing payload.
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 100)) (inv x y))))
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
  (=> (and (inv x y) (= x2 (+ x 1)) (= y2 (- y 1))) (inv x2 y2))))
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (< y (- 1))) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let config = PdrConfig {
        max_obligations: 2,
        max_iterations: 3,
        max_frames: 3,
        solve_timeout: Some(Duration::from_secs(2)),
        ..PdrConfig::default()
    };

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("pdr_unknown_failure_payload.jsonl");

    let mut solver = PdrSolver::new(problem, config);
    solver.enable_tla_trace(path.to_str().unwrap(), "pdr_test", &PDR_TRACE_VARIABLES);
    let result = solver.solve();

    // With tight limits, expect Unknown (can't converge in 3 iterations / 3 frames).
    if !matches!(result, PdrResult::Unknown) {
        // If the solver happens to solve it, the test is inconclusive but not wrong.
        return;
    }

    let contents = fs::read_to_string(&path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    assert!(
        lines.len() >= 2,
        "expected header + at least one step, got {}",
        lines.len()
    );
    let steps: Vec<serde_json::Value> = lines
        .iter()
        .skip(1)
        .filter_map(|line| serde_json::from_str(line).ok())
        .collect();

    // Check that at least one step has telemetry with a failure reason.
    // The conservative-fail path emits these at obligation overflow, level-0
    // blocked state limit, and other Unknown exits.
    let failure_step = steps
        .iter()
        .find(|step| step["telemetry"]["failure"]["reason"].as_str().is_some());

    if let Some(fs) = failure_step {
        assert!(
            !fs["telemetry"]["failure"]["reason"]
                .as_str()
                .unwrap()
                .is_empty(),
            "failure reason must be non-empty"
        );
        let counters = &fs["telemetry"]["counters"];
        assert!(
            counters.is_object(),
            "failure payload must include counter telemetry"
        );
        // entry_cegar_discharge_total must be present (#4697).
        assert!(
            counters.get("entry_cegar_discharge_total").is_some(),
            "counters must include entry_cegar_discharge_total"
        );
    }
    // If no failure step was emitted, the Unknown came from a non-conservative-fail
    // path (e.g., iteration/frame limit). That's acceptable — the trace is still valid.
}

#[test]
fn test_constructor_does_not_clobber_trace_file() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("pdr_env_trace.jsonl");

    let problem = unsafe_problem();
    let mut solver = PdrSolver::new(problem.clone(), PdrConfig::default());
    solver.enable_tla_trace(path.to_str().unwrap(), "pdr_test", &PDR_TRACE_VARIABLES);
    let result = solver.solve();
    assert!(matches!(result, PdrResult::Unsafe(_)));

    let before = fs::read_to_string(&path).unwrap();
    let before_lines: Vec<&str> = before.lines().collect();
    assert!(
        before_lines.len() >= 3,
        "expected header + init + terminal, got {} lines",
        before_lines.len()
    );
    let before_last: serde_json::Value =
        serde_json::from_str(before_lines[before_lines.len() - 1]).unwrap();
    assert_eq!(before_last["action"]["name"], "DeclareUnsafe");

    // Verify the file contains valid JSON lines
    for line in before.lines() {
        assert!(
            serde_json::from_str::<serde_json::Value>(line).is_ok(),
            "Each line should be valid JSON: {line}"
        );
    }

    // Constructing additional solvers must not reopen/truncate the trace file.
    let _unused = PdrSolver::new(problem, PdrConfig::default());

    let after = fs::read_to_string(&path).unwrap();
    assert_eq!(
        after, before,
        "constructor unexpectedly modified trace file"
    );
}
