// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Diagnostic trace, TLA trace, and decision trace tests.
//!
//! Extracted from tests.rs for code-quality (Part of #5142).

use super::*;

fn enable_cdcl_tla_trace(solver: &mut Solver, path: &std::path::Path) {
    solver.enable_tla_trace(
        path.to_str().expect("trace path should be UTF-8"),
        Solver::tla_module(),
        Solver::tla_variables(),
    );
}

fn assert_trace_uses_only_cdcl_spec_actions(trace: &[serde_json::Value]) {
    for event in trace {
        let Some(action) = event
            .get("action")
            .and_then(|action| action.get("name"))
            .and_then(serde_json::Value::as_str)
        else {
            continue;
        };
        assert!(
            Solver::tla_actions().contains(&action),
            "trace emitted action {action:?}, which has no cdcl_test.tla operator"
        );
    }
}

#[test]
fn test_tla_trace_early_sat_emits_terminal_action() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("early_sat_trace.jsonl");

    let mut solver = Solver::new(0);
    enable_cdcl_tla_trace(&mut solver, &path);

    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));

    let trace = read_tla_trace(&path);
    assert!(
        trace.len() >= 3,
        "expected header + initial step + terminal SAT step, got {} lines",
        trace.len()
    );
    let last = trace.last().unwrap();
    assert_eq!(last["action"]["name"], "DeclareSat");
    assert_eq!(last["state"]["state"]["value"], "SAT");
}

#[test]
fn test_tla_trace_early_unsat_emits_terminal_action() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("early_unsat_trace.jsonl");

    let mut solver = Solver::new(1);
    enable_cdcl_tla_trace(&mut solver, &path);
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(0))]);

    assert!(solver.solve().into_inner().is_unsat());

    let trace = read_tla_trace(&path);
    assert!(
        trace.len() >= 3,
        "expected header + initial step + terminal UNSAT step, got {} lines",
        trace.len()
    );
    let last = trace.last().unwrap();
    assert_eq!(last["action"]["name"], "DeclareUnsat");
    assert_eq!(last["state"]["state"]["value"], "UNSAT");
}

#[test]
fn test_tla_trace_interruptible_flushes_terminal_step() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("interruptible_trace.jsonl");

    let mut solver = Solver::new(1);
    enable_cdcl_tla_trace(&mut solver, &path);
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    let result = solver.solve_interruptible(|| false).into_inner();
    assert!(matches!(result, SatResult::Sat(_)));

    // Read while solver is still alive. solve_interruptible() must flush.
    let trace = read_tla_trace(&path);
    assert!(
        trace.len() >= 3,
        "expected header + initial step + terminal SAT step, got {} lines",
        trace.len()
    );
    let last = trace.last().unwrap();
    assert_eq!(last["action"]["name"], "DeclareSat");
    assert_eq!(last["state"]["state"]["value"], "SAT");
}

#[test]
fn test_tla_trace_theory_path_emits_steps() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("theory_trace.jsonl");

    // Create a simple SAT problem: (x0 OR x1)
    let mut solver = Solver::new(2);
    enable_cdcl_tla_trace(&mut solver, &path);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    // Theory callback that always says "continue" (no theory conflicts)
    let result = solver
        .solve_with_theory(|_| TheoryPropResult::Continue)
        .into_inner();
    assert!(matches!(result, SatResult::Sat(_)));

    let trace = read_tla_trace(&path);
    // Must have at least header + initial state + terminal SAT
    assert!(
        trace.len() >= 3,
        "theory path trace should have at least 3 lines (header + initial + terminal), got {}",
        trace.len()
    );

    // First line is header
    assert_eq!(trace[0]["type"], "header");
    assert_eq!(trace[0]["module"], Solver::tla_module());

    // Second line is initial state (no action)
    assert_eq!(trace[1]["type"], "step");
    assert!(trace[1].get("action").is_none());

    // Last step must be terminal SAT
    let last = trace.last().unwrap();
    assert_eq!(last["action"]["name"], "DeclareSat");
    assert_eq!(last["state"]["state"]["value"], "SAT");
}

#[test]
fn test_tla_trace_theory_path_unsat_emits_steps() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("theory_unsat_trace.jsonl");

    // Create contradictory clauses: x0 AND NOT x0
    let mut solver = Solver::new(1);
    enable_cdcl_tla_trace(&mut solver, &path);
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(0))]);

    let result = solver
        .solve_with_theory(|_| TheoryPropResult::Continue)
        .into_inner();
    assert!(matches!(result, SatResult::Unsat(_)));

    let trace = read_tla_trace(&path);
    assert!(
        trace.len() >= 3,
        "theory path UNSAT trace should have at least 3 lines, got {}",
        trace.len()
    );

    // Last step must be terminal UNSAT
    let last = trace.last().unwrap();
    assert_eq!(last["action"]["name"], "DeclareUnsat");
    assert_eq!(last["state"]["state"]["value"], "UNSAT");
}

#[test]
fn test_tla_trace_extension_path_emits_steps() {
    use crate::extension::*;

    struct SuggestedDecisionExtension {
        suggestion_requested: std::cell::Cell<bool>,
    }
    impl Extension for SuggestedDecisionExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }
        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }
        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            false
        }
        fn suggest_decision(&self, _ctx: &dyn SolverContext) -> Option<Literal> {
            self.suggestion_requested.set(true);
            Some(Literal::positive(Variable(0)))
        }
    }

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("extension_trace.jsonl");

    // Create a simple SAT problem: (x0 OR x1)
    let mut solver = Solver::new(2);
    enable_cdcl_tla_trace(&mut solver, &path);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    let mut ext = SuggestedDecisionExtension {
        suggestion_requested: std::cell::Cell::new(false),
    };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(matches!(result, SatResult::Sat(_)));
    assert!(
        ext.suggestion_requested.get(),
        "fixture must exercise the extension-selected decision path"
    );

    let trace = read_tla_trace(&path);
    assert_trace_uses_only_cdcl_spec_actions(&trace);
    // Must have at least header + initial state + terminal SAT
    assert!(
        trace.len() >= 3,
        "extension path trace should have at least 3 lines, got {}",
        trace.len()
    );

    // First line is header
    assert_eq!(trace[0]["type"], "header");

    // Second line is initial state (no action)
    assert_eq!(trace[1]["type"], "step");
    assert!(trace[1].get("action").is_none());

    // Last step must be terminal SAT
    let last = trace.last().unwrap();
    assert_eq!(last["action"]["name"], "DeclareSat");
    assert_eq!(last["state"]["state"]["value"], "SAT");

    // Check that at least one Decide step exists (solver needs to make decisions
    // since the clause is not unit)
    let has_decide = trace.iter().any(|step| {
        step.get("action")
            .and_then(|a| a.get("name"))
            .is_some_and(|n| n == "Decide")
    });
    assert!(
        has_decide,
        "extension path trace should contain a Decide step"
    );
}

#[test]
fn test_tla_trace_extension_path_unsat_emits_steps() {
    use crate::extension::*;

    struct PassthroughExtension;
    impl Extension for PassthroughExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }
        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }
        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            false
        }
    }

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("extension_unsat_trace.jsonl");

    // Create contradictory clauses: x0 AND NOT x0
    let mut solver = Solver::new(1);
    enable_cdcl_tla_trace(&mut solver, &path);
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(0))]);

    let mut ext = PassthroughExtension;
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(matches!(result, SatResult::Unsat(_)));

    let trace = read_tla_trace(&path);
    assert!(
        trace.len() >= 3,
        "extension path UNSAT trace should have at least 3 lines, got {}",
        trace.len()
    );

    // Last step must be terminal UNSAT
    let last = trace.last().unwrap();
    assert_eq!(last["action"]["name"], "DeclareUnsat");
    assert_eq!(last["state"]["state"]["value"], "UNSAT");
}

/// Wave 1 acceptance: diagnostic trace emits header when enabled, no file when disabled.
#[test]
fn test_diagnostic_trace_emits_header_on_enable() {
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag.jsonl");

    let mut solver = Solver::new(2);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();

    // Simple SAT formula: (x0) & (x1)
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);

    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Sat(_)));

    // Diagnostic file must exist and contain at least the header line
    let contents = std::fs::read_to_string(&diag_path).expect("read diag file");
    let lines: Vec<&str> = contents.lines().collect();
    assert!(!lines.is_empty(), "diagnostic file must not be empty");

    let header: serde_json::Value = serde_json::from_str(lines[0]).expect("parse header JSON");
    assert_eq!(header["type"], "header");
    assert_eq!(header["version"], "1");
    assert_eq!(header["tool"], "ay-sat-diagnostic");
}

/// Wave 1 acceptance: no diagnostic file is created when diagnostics are disabled.
#[test]
fn test_diagnostic_trace_no_file_when_disabled() {
    let mut solver = Solver::new(2);
    // Do NOT enable diagnostic trace
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);

    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Sat(_)));

    // diagnostic_enabled should be false
    assert!(!solver.diagnostic_enabled());
}

/// Wave 2 acceptance: clause_add events emitted for each clause added to the database.
#[test]
fn test_diagnostic_trace_clause_add_events() {
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag_wave2.jsonl");

    let mut solver = Solver::new(3);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();

    // Add 3 clauses: (x0 v x1), (x1 v x2), (x0 v ~x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(2)),
    ]);

    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Sat(_)));

    let contents = std::fs::read_to_string(&diag_path).expect("read diag file");
    let events: Vec<serde_json::Value> = contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect();

    // Header + at least 3 clause_add events (one per input clause)
    let clause_adds: Vec<&serde_json::Value> = events
        .iter()
        .filter(|e| e["type"] == "clause_add")
        .collect();

    assert!(
        clause_adds.len() >= 3,
        "expected at least 3 clause_add events, got {}",
        clause_adds.len()
    );

    // Verify first clause_add has correct schema
    let first = &clause_adds[0];
    assert!(first["clause_id"].is_number(), "clause_id must be numeric");
    assert!(first["lits"].is_array(), "lits must be an array");
    assert!(first["kind"].is_string(), "kind must be a string");
    assert_eq!(
        first["kind"], "original",
        "input clauses should be 'original'"
    );
}

/// Wave 2 acceptance: trivial UNSAT instance emits original clause_add events.
/// Note: (x0) & (~x0) is resolved by unit propagation — no learned clauses.
#[test]
fn test_diagnostic_trace_original_clauses_unsat() {
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag_unsat.jsonl");

    let mut solver = Solver::new(2);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();

    // Trivial UNSAT: (x0) & (~x0) — detected by unit propagation, no CDCL.
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(0))]);

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let contents = std::fs::read_to_string(&diag_path).expect("read diag file");
    let events: Vec<serde_json::Value> = contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect();

    let clause_adds: Vec<&serde_json::Value> = events
        .iter()
        .filter(|e| e["type"] == "clause_add")
        .collect();

    assert!(
        clause_adds.len() >= 2,
        "expected at least 2 clause_add events for UNSAT instance, got {}",
        clause_adds.len()
    );

    let original_count = clause_adds
        .iter()
        .filter(|e| e["kind"] == "original")
        .count();
    assert!(
        original_count >= 2,
        "expected at least 2 'original' clause_add events, got {original_count}"
    );
}

/// Wave 2 acceptance: UNSAT instance that requires CDCL produces learned clause events.
/// Uses PHP(3,2) (3 pigeons, 2 holes) — a well-known UNSAT formula requiring
/// multi-level CDCL search. Inprocessing disabled to prevent BVE shortcut.
///
/// Gap found during audit: learned unit clauses from lucky phases (preprocess.rs:126-138)
/// bypass add_clause_db and are invisible to diagnostic trace. This test uses a formula
/// complex enough that lucky phases fail and CDCL produces non-unit learned clauses.
#[test]
fn test_diagnostic_trace_learned_clause_events() {
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag_learned.jsonl");

    let mut solver = Solver::new(7);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();

    // PHP(3,2): 3 pigeons, 2 holes. Variables: p_i_j = pigeon i in hole j.
    // p1h1=v1, p1h2=v2, p2h1=v3, p2h2=v4, p3h1=v5, p3h2=v6
    let p = |pigeon: u32, hole: u32| Variable(pigeon * 2 + hole - 2);

    // Each pigeon must go to some hole (at-least-one constraints)
    solver.add_clause(vec![Literal::positive(p(1, 1)), Literal::positive(p(1, 2))]);
    solver.add_clause(vec![Literal::positive(p(2, 1)), Literal::positive(p(2, 2))]);
    solver.add_clause(vec![Literal::positive(p(3, 1)), Literal::positive(p(3, 2))]);

    // At most one pigeon per hole (at-most-one constraints)
    // Hole 1: no two of {p1h1, p2h1, p3h1}
    solver.add_clause(vec![Literal::negative(p(1, 1)), Literal::negative(p(2, 1))]);
    solver.add_clause(vec![Literal::negative(p(1, 1)), Literal::negative(p(3, 1))]);
    solver.add_clause(vec![Literal::negative(p(2, 1)), Literal::negative(p(3, 1))]);
    // Hole 2: no two of {p1h2, p2h2, p3h2}
    solver.add_clause(vec![Literal::negative(p(1, 2)), Literal::negative(p(2, 2))]);
    solver.add_clause(vec![Literal::negative(p(1, 2)), Literal::negative(p(3, 2))]);
    solver.add_clause(vec![Literal::negative(p(2, 2)), Literal::negative(p(3, 2))]);

    // Disable all inprocessing to force CDCL.
    solver.disable_all_inprocessing();

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let contents = std::fs::read_to_string(&diag_path).expect("read diag file");
    let events: Vec<serde_json::Value> = contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect();

    let clause_adds: Vec<&serde_json::Value> = events
        .iter()
        .filter(|e| e["type"] == "clause_add")
        .collect();

    // Must have at least 9 original clause events (3 ALO + 6 AMO)
    let original_count = clause_adds
        .iter()
        .filter(|e| e["kind"] == "original")
        .count();
    assert!(
        original_count >= 9,
        "expected at least 9 'original' clause_add events, got {original_count}"
    );

    // Must have at least 1 learned clause event from CDCL conflict analysis
    let learned_count = clause_adds
        .iter()
        .filter(|e| e["kind"] == "learned")
        .count();
    assert!(
        learned_count >= 1,
        "expected at least 1 'learned' clause_add event from CDCL, got {learned_count}; \
         all clause_add events: {:?}",
        clause_adds
            .iter()
            .map(|e| format!("kind={}", e["kind"]))
            .collect::<Vec<_>>()
    );
}

/// Wave 3 acceptance: pass attribution appears on diagnostic events.
/// Subsumption preprocessing deletes a subsumed clause; the clause_delete
/// event must carry `"pass": "subsume"`.
#[test]
fn test_diagnostic_trace_pass_attribution() {
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag_wave3.jsonl");

    // (x0 v x1) subsumes (x0 v x1 v x2): subsumption deletes the ternary clause.
    let mut solver: Solver = Solver::new(5);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();

    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    // Padding clauses to avoid trivial short-circuits.
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
    ]);
    assert!(solver.process_initial_clauses().is_none());

    // Enable only subsumption.
    solver.disable_all_inprocessing();
    solver.inproc_ctrl.subsume.enabled = true;
    solver.preprocessing_quick_mode = false; // test needs subsumption during preprocess

    solver.preprocess();
    solver.finish_diagnostic_trace();

    let contents = std::fs::read_to_string(&diag_path).expect("read diag file");
    let events: Vec<serde_json::Value> = contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect();

    // Look for clause_delete events with pass == "subsume".
    let subsume_deletes: Vec<&serde_json::Value> = events
        .iter()
        .filter(|e| e["type"] == "clause_delete" && e["pass"] == "subsume")
        .collect();

    assert!(
        !subsume_deletes.is_empty(),
        "expected at least one clause_delete with pass='subsume', got events: {:?}",
        events
            .iter()
            .filter(|e| e["type"] == "clause_delete")
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_inprocessing_round_reports_cce_in_bve_cascade_before_factor() {
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag_interleaved_cce.jsonl");

    let mut solver: Solver = Solver::new(6);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();
    solver.disable_all_inprocessing();
    solver.set_subsume_enabled(true);
    solver.set_bve_enabled(true);
    solver.set_bce_enabled(true);
    solver.set_cce_enabled(true);
    solver.set_factor_enabled(true);

    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(2)),
        Literal::positive(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(3)),
        Literal::positive(Variable(5)),
    ]);

    assert!(
        solver.process_initial_clauses().is_none(),
        "deterministic inprocessing setup should remain satisfiable",
    );
    solver.initialize_watches();

    solver.num_conflicts = 500;
    solver.cold.next_inprobe_conflict = 0;
    solver.cold.num_reductions = 1;
    solver.inproc_ctrl.subsume.next_conflict = 0;
    solver.inproc_ctrl.bve.next_conflict = 0;
    solver.inproc_ctrl.bce.next_conflict = 0;
    solver.inproc_ctrl.cce.next_conflict = 0;
    solver.inproc_ctrl.factor.next_conflict = 0;
    solver.cold.factor_marked_epoch = solver.cold.factor_last_completed_epoch + 1;
    solver.cold.last_bve_marked = solver.cold.bve_marked.wrapping_sub(1);

    assert!(
        !solver.run_restart_inprocessing(),
        "focused inprocessing setup should not derive UNSAT",
    );
    solver.finish_diagnostic_trace();

    let events = read_diagnostic_trace(&diag_path);
    let round_event = events
        .iter()
        .find(|e| e.get("type").and_then(|t| t.as_str()) == Some("inprocessing_round"))
        .expect("expected at least one inprocessing_round event");
    let passes = round_event
        .get("passes")
        .and_then(|v| v.as_array())
        .expect("inprocessing_round must include passes array");
    let pass_names: Vec<&str> = passes
        .iter()
        .filter_map(serde_json::Value::as_str)
        .collect();

    let factor_idx = pass_names
        .iter()
        .position(|pass| *pass == "factor")
        .expect("factor should also run in this diagnostic setup");
    let cce_idx = pass_names
        .iter()
        .position(|pass| *pass == "cce")
        .expect("CCE should run in the elimination pipeline");

    // CaDiCaL elim.cpp:1093-1098 ordering: BVE+subsume+BCE+CCE interleaved → factor.
    // CCE runs inside the BVE cascade (after BCE), before factor.
    // This matches CaDiCaL's cover() call inside the elimination loop.
    assert!(
        cce_idx < factor_idx,
        "CCE must execute before factor (CaDiCaL elim.cpp cascade ordering); passes were {pass_names:?}",
    );
}

#[test]
fn test_diagnostic_trace_incremental_scope_and_assumption_events() {
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag_incremental_scope_assume.jsonl");

    let mut solver = Solver::new(3);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();

    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.push();
    solver.add_clause(vec![Literal::positive(Variable(1))]);

    let result = solver
        .solve_with_assumptions(&[Literal::negative(Variable(0))])
        .into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            assert_eq!(core, vec![Literal::negative(Variable(0))]);
        }
        other => panic!("expected UNSAT from scoped assumption solve, got {other:?}"),
    }

    assert!(solver.pop(), "pop should succeed after one push");
    solver.finish_diagnostic_trace();

    let events = read_diagnostic_trace(&diag_path);

    let push = events
        .iter()
        .find(|e| e["type"] == "scope_push")
        .expect("expected scope_push event");
    assert_eq!(push["scope_depth"], 1);
    assert_eq!(push["restored_clause_count"], 0);
    let selector_var = push["selector_var"]
        .as_u64()
        .expect("scope_push selector_var must be numeric");

    let batch = events
        .iter()
        .find(|e| e["type"] == "assumption_batch")
        .expect("expected assumption_batch event");
    assert_eq!(batch["count"], 2);
    assert_eq!(batch["composed_with_scope"], true);
    let lits = batch["lits"]
        .as_array()
        .expect("assumption_batch lits must be an array");
    assert_eq!(
        lits.first().and_then(serde_json::Value::as_i64),
        Some(-((selector_var as i64) + 1)),
        "scope selector should be prefixed to the assumption batch"
    );
    assert!(
        lits.iter().any(|lit| lit.as_i64() == Some(-1)),
        "user assumption should remain in the batch: {lits:?}"
    );

    let assume_result = events
        .iter()
        .find(|e| e["type"] == "assumption_result")
        .expect("expected assumption_result event");
    assert_eq!(assume_result["result"], "unsat");
    assert_eq!(assume_result["core_size"], 1);
    assert_eq!(assume_result["reason"], serde_json::Value::Null);

    let pop = events
        .iter()
        .find(|e| e["type"] == "scope_pop")
        .expect("expected scope_pop event");
    assert_eq!(pop["scope_depth_before"], 1);
    assert_eq!(pop["scope_depth_after"], 0);
    assert_eq!(pop["selector_var"].as_u64(), Some(selector_var));
    assert_eq!(pop["retracted_empty_clause"], false);
}

/// Wave 4 acceptance: SAT result_summary emitted with model_size and stats.
#[test]
fn test_diagnostic_trace_sat_result_summary() {
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag_wave4_sat.jsonl");

    let mut solver: Solver = Solver::new(3);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();

    // Simple SAT: (x0) & (x1) & (x2)
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);
    solver.add_clause(vec![Literal::positive(Variable(2))]);

    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Sat(_)), "formula is SAT");

    let contents = std::fs::read_to_string(&diag_path).expect("read diag file");
    let events: Vec<serde_json::Value> = contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect();

    let summaries: Vec<&serde_json::Value> = events
        .iter()
        .filter(|e| e["type"] == "result_summary" && e["result"] == "sat")
        .collect();

    assert_eq!(
        summaries.len(),
        1,
        "expected exactly one SAT result_summary, got: {summaries:?}"
    );

    let s = summaries[0];
    assert_eq!(s["model_size"], 3, "model_size should match num_vars");
    assert_eq!(s["num_original_clauses"], 3);
    // Unit-clause-only SAT: no conflicts, no decisions, no reconstruction
    assert_eq!(s["num_conflicts"], 0);
    assert_eq!(s["num_decisions"], 0);
    assert_eq!(s["reconstruction_steps"], 0);
    assert!(s["num_clauses"].is_u64(), "num_clauses must be present");
}

/// Wave 4 acceptance: UNSAT result_summary emitted with proof metadata and enabled passes.
#[test]
fn test_diagnostic_trace_unsat_result_summary() {
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag_wave4_unsat.jsonl");

    let mut solver: Solver = Solver::new(1);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();

    // Trivial UNSAT: (x0) & (NOT x0)
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(0))]);

    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Unsat(_)), "formula is UNSAT");

    let contents = std::fs::read_to_string(&diag_path).expect("read diag file");
    let events: Vec<serde_json::Value> = contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect();

    let summaries: Vec<&serde_json::Value> = events
        .iter()
        .filter(|e| e["type"] == "result_summary" && e["result"] == "unsat")
        .collect();

    assert_eq!(
        summaries.len(),
        1,
        "expected exactly one UNSAT result_summary, got: {summaries:?}"
    );

    let s = summaries[0];
    assert_eq!(s["num_original_clauses"], 2);
    // No proof writer attached — proof_steps_added must be 0
    assert_eq!(s["proof_steps_added"], 0);
    assert_eq!(s["empty_clause_written"], false);
    // Trivial UNSAT detected by unit propagation — no decisions needed
    assert_eq!(s["num_conflicts"], 0);
    assert_eq!(s["num_decisions"], 0);
    assert!(
        s["enabled_passes"].is_array(),
        "enabled_passes must be an array"
    );
}

/// Deterministic trace round-trip: record then replay on identical CNF.
#[test]
fn test_decision_trace_roundtrip_replay_matches() {
    let dir = tempfile::tempdir().expect("tempdir");
    let trace_path = dir.path().join("decision.trace");
    let trace_path_str = trace_path.to_str().expect("utf8 path");

    let mut recorder = Solver::new(2);
    recorder.set_preprocess_enabled(false);
    recorder.disable_all_inprocessing();
    // Unsat XOR parity pair: requires decisions/conflicts in pure CDCL.
    recorder.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    recorder.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    recorder.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    recorder.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    recorder.enable_decision_trace(trace_path_str).unwrap();
    let recorded = recorder.solve().into_inner();
    assert!(recorded.is_unsat());

    let mut replay = Solver::new(2);
    replay.set_preprocess_enabled(false);
    replay.disable_all_inprocessing();
    replay.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    replay.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    replay.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    replay.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    replay.enable_replay_trace(trace_path_str).unwrap();
    let replayed = replay.solve().into_inner();
    assert!(replayed.is_unsat());
}

/// Replay must fail fast when solver behavior diverges from the trace stream.
#[test]
fn test_decision_trace_replay_detects_divergence() {
    let dir = tempfile::tempdir().expect("tempdir");
    let trace_path = dir.path().join("decision.trace");
    let trace_path_str = trace_path.to_str().expect("utf8 path");

    let mut recorder = Solver::new(2);
    recorder.set_preprocess_enabled(false);
    recorder.disable_all_inprocessing();
    recorder.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    recorder.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    recorder.enable_decision_trace(trace_path_str).unwrap();
    let recorded = recorder.solve().into_inner();
    assert!(matches!(recorded, SatResult::Sat(_)));

    let mut replay = Solver::new(2);
    replay.set_preprocess_enabled(false);
    replay.disable_all_inprocessing();
    // Different CNF shape triggers a different event stream.
    replay.add_clause(vec![Literal::positive(Variable(0))]);
    replay.add_clause(vec![Literal::negative(Variable(0))]);
    replay.enable_replay_trace(trace_path_str).unwrap();

    let result =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| replay.solve().into_inner()));
    assert!(result.is_err(), "expected replay divergence panic");
}

/// Regression test for #4624: enable_diagnostic_trace returns Err on
/// bad path instead of panicking. Solver remains usable after the error.
#[test]
fn test_diagnostic_trace_bad_path_returns_err() {
    let mut solver: Solver = Solver::new(2);

    // Non-existent directory -> file creation fails.
    let result = solver.enable_diagnostic_trace("/nonexistent_dir_abc/diag.jsonl");
    assert!(result.is_err(), "expected Err for unwritable path, got Ok");

    // Solver remains usable after failed diagnostic setup.
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);
    let solve_result = solver.solve().into_inner();
    assert_eq!(solve_result, SatResult::Sat(vec![true, true]));
}

/// Round-trip test for deterministic decision trace: solve -> record -> replay.
///
/// Verifies that a SAT formula produces the same decision/conflict/learn event
/// stream when replayed, confirming deterministic behavior. This covers the
/// acceptance criterion "Round-trip test: solve, record, replay, verify
/// identical result" from issue #4541.
#[test]
fn test_decision_trace_roundtrip_sat() {
    let dir = tempfile::tempdir().expect("tempdir");
    let trace_path = dir.path().join("sat_decisions.trace");
    let trace_str = trace_path.to_str().expect("utf8 path");

    // Build a satisfiable formula with enough structure to generate conflicts.
    // 4 variables, mix of positive/negative clauses.
    let mut solver = Solver::new(4);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::negative(Variable(2)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(3)),
        Literal::positive(Variable(0)),
    ]);

    // Disable inprocessing to keep the formula stable across runs.
    solver.disable_all_inprocessing();
    solver.enable_decision_trace(trace_str).unwrap();

    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Sat(_)), "expected SAT");
    drop(solver);

    // Verify trace file was written and is non-empty.
    let trace_len = std::fs::metadata(&trace_path)
        .expect("trace file exists")
        .len();
    assert!(
        trace_len > 9,
        "trace file too small ({trace_len} bytes), expected header + events"
    );

    // Replay: solve the same formula and validate against the recorded trace.
    let mut solver2 = Solver::new(4);
    solver2.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver2.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver2.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::negative(Variable(2)),
        Literal::positive(Variable(3)),
    ]);
    solver2.add_clause(vec![
        Literal::negative(Variable(3)),
        Literal::positive(Variable(0)),
    ]);
    solver2.disable_all_inprocessing();
    solver2.enable_replay_trace(trace_str).unwrap();

    // Replay should not panic -- identical event stream.
    let result2 = solver2.solve().into_inner();
    assert!(matches!(result2, SatResult::Sat(_)), "replay expected SAT");
}

/// Round-trip test for UNSAT formula: record and replay decision trace.
///
/// Uses the pigeonhole principle PHP(3,2) which requires CDCL with learned
/// clauses, restarts, and reductions -- exercising all trace event types.
#[test]
fn test_decision_trace_roundtrip_unsat() {
    let dir = tempfile::tempdir().expect("tempdir");
    let trace_path = dir.path().join("unsat_decisions.trace");
    let trace_str = trace_path.to_str().expect("utf8 path");

    // Helper: variable for pigeon i in hole j (1-indexed).
    let p = |pigeon: u32, hole: u32| Variable(pigeon * 2 + hole - 2);

    // Build PHP(3,2): 3 pigeons, 2 holes -- UNSAT.
    let build_php = |solver: &mut Solver| {
        // Each pigeon in some hole.
        solver.add_clause(vec![Literal::positive(p(1, 1)), Literal::positive(p(1, 2))]);
        solver.add_clause(vec![Literal::positive(p(2, 1)), Literal::positive(p(2, 2))]);
        solver.add_clause(vec![Literal::positive(p(3, 1)), Literal::positive(p(3, 2))]);
        // At most one pigeon per hole.
        solver.add_clause(vec![Literal::negative(p(1, 1)), Literal::negative(p(2, 1))]);
        solver.add_clause(vec![Literal::negative(p(1, 1)), Literal::negative(p(3, 1))]);
        solver.add_clause(vec![Literal::negative(p(2, 1)), Literal::negative(p(3, 1))]);
        solver.add_clause(vec![Literal::negative(p(1, 2)), Literal::negative(p(2, 2))]);
        solver.add_clause(vec![Literal::negative(p(1, 2)), Literal::negative(p(3, 2))]);
        solver.add_clause(vec![Literal::negative(p(2, 2)), Literal::negative(p(3, 2))]);
    };

    // Record.
    let mut solver = Solver::new(7);
    build_php(&mut solver);
    solver.disable_all_inprocessing();
    solver.enable_decision_trace(trace_str).unwrap();
    assert!(solver.solve().into_inner().is_unsat());
    drop(solver);

    // Verify trace exists.
    let trace_len = std::fs::metadata(&trace_path).expect("trace file").len();
    assert!(trace_len > 9, "trace file too small: {trace_len}");

    // Replay.
    let mut solver2 = Solver::new(7);
    build_php(&mut solver2);
    solver2.disable_all_inprocessing();
    solver2.enable_replay_trace(trace_str).unwrap();
    assert!(solver2.solve().into_inner().is_unsat());
}

/// Verify that trace file size is reasonable (acceptance criterion: <200MB for 1M conflicts).
///
/// This test uses a moderately sized UNSAT formula that produces many conflicts
/// and checks the trace file stays compact.
#[test]
fn test_decision_trace_compact_size() {
    let dir = tempfile::tempdir().expect("tempdir");
    let trace_path = dir.path().join("size_check.trace");
    let trace_str = trace_path.to_str().expect("utf8 path");

    // Build PHP(4,3): 4 pigeons, 3 holes -- more conflicts than PHP(3,2).
    let mut solver = Solver::new(13);
    let p = |pigeon: u32, hole: u32| Variable((pigeon - 1) * 3 + hole - 1);
    for i in 1..=4 {
        solver.add_clause(vec![
            Literal::positive(p(i, 1)),
            Literal::positive(p(i, 2)),
            Literal::positive(p(i, 3)),
        ]);
    }
    for h in 1..=3 {
        for i in 1..=4 {
            for j in (i + 1)..=4 {
                solver.add_clause(vec![Literal::negative(p(i, h)), Literal::negative(p(j, h))]);
            }
        }
    }
    solver.disable_all_inprocessing();
    solver.enable_decision_trace(trace_str).unwrap();
    assert!(solver.solve().into_inner().is_unsat());
    drop(solver);

    let trace_len = std::fs::metadata(&trace_path).expect("trace file").len();
    // PHP(4,3) is small, but verify the ratio is reasonable:
    // ~5-20 bytes per event, well under 1KB for this formula.
    assert!(
        trace_len < 100_000,
        "trace file unexpectedly large: {trace_len} bytes for PHP(4,3)"
    );

    // Analytical size criterion: propagation events are omitted (they're
    // deterministic), so the per-conflict cost is dominated by:
    //   Decide: 5 bytes, Conflict: 9 bytes, Learn: 9 bytes = 23 bytes/conflict
    // With ~5 decisions per conflict on average: ~43 bytes/conflict.
    // 1M conflicts x 200 bytes/conflict (generous upper bound) = 200MB.
    //
    // Read back the trace to compute the actual bytes-per-conflict ratio.
    let events = decision_trace::read_trace(trace_str).expect("read trace");
    let conflict_count = events
        .iter()
        .filter(|e| matches!(e, TraceEvent::Conflict { .. }))
        .count();
    let propagate_count = events
        .iter()
        .filter(|e| matches!(e, TraceEvent::Propagate { .. }))
        .count();
    // Propagations must NOT appear in the trace (omitted for compactness).
    assert_eq!(
        propagate_count, 0,
        "propagation events should not be recorded in the trace"
    );
    if conflict_count > 0 {
        let header_bytes = 9u64; // 8-byte magic + 1-byte version
        let data_bytes = trace_len - header_bytes;
        let bytes_per_conflict = data_bytes / conflict_count as u64;
        // Upper bound: 200 bytes/conflict -> 200MB for 1M conflicts.
        assert!(
            bytes_per_conflict < 200,
            "trace too large: {bytes_per_conflict} bytes/conflict \
             (projected {:.0}MB for 1M conflicts, limit 200MB)",
            bytes_per_conflict as f64 * 1_000_000.0 / 1_048_576.0
        );
    }
}

/// Verifies that every inprocessing_round event's `passes` array length is
/// strictly less than the total number of enabled techniques (14). If the
/// old bug were present, each round would report all 14 enabled passes.
/// With the fix, only actually-executed passes appear (most rounds have 0-3
/// since techniques have different conflict-count thresholds).
#[test]
fn test_inprocessing_round_reports_executed_passes_not_enabled() {
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag_inproc_passes.jsonl");

    // Deterministic SAT instance (no unit clauses) to avoid vacuous failures
    // from random formulas that occasionally solve without emitting any restart
    // inprocessing rounds.
    let mut solver = Solver::new(6);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();

    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(2)),
        Literal::negative(Variable(3)),
        Literal::positive(Variable(5)),
    ]);

    assert!(
        solver.process_initial_clauses().is_none(),
        "deterministic setup should remain satisfiable"
    );
    solver.initialize_watches();
    // Force one inprocessing round gate hit.
    solver.num_conflicts = 500;
    // Simulate a reduce_db having occurred so the reduction gate passes (#5130).
    solver.cold.num_reductions = 1;
    assert!(
        !solver.run_restart_inprocessing(),
        "deterministic setup should not derive UNSAT during inprocessing round"
    );
    solver.finish_diagnostic_trace();

    let events = read_diagnostic_trace(&diag_path);
    let round_events: Vec<&serde_json::Value> = events
        .iter()
        .filter(|e| e.get("type").and_then(|t| t.as_str()) == Some("inprocessing_round"))
        .collect();

    // The formula must generate enough conflicts for at least one restart
    // and inprocessing round. If this fails, increase num_vars or ratio.
    assert!(
        !round_events.is_empty(),
        "no inprocessing_round events emitted — formula too easy, test is vacuous",
    );

    // The solver has 14 enabled inprocessing techniques by default. If the
    // old bug (reporting collect_enabled_passes()) were present, every round
    // would report all 14. With the fix (reporting passes_run), rounds report
    // only the techniques that actually executed — typically 0-3 per round
    // since each technique has a different conflict-count threshold.
    let total_enabled_passes = 14;
    for (i, event) in round_events.iter().enumerate() {
        let passes = event
            .get("passes")
            .and_then(|v| v.as_array())
            .unwrap_or_else(|| panic!("inprocessing_round[{i}] must have passes array"));

        assert!(
            passes.len() < total_enabled_passes,
            "inprocessing_round[{i}] reported {} passes (same as total enabled {}) — \
             suggests over-reporting the full enabled set instead of executed passes",
            passes.len(),
            total_enabled_passes,
        );
    }
}
