// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Regression test: stric-bmc-ibm-12 feature-combination soundness (#3961)

use ay_sat::{parse_dimacs, SatResult, Solver};
use ntest::timeout;
use std::path::PathBuf;

fn should_run_ibm12_bisect() -> bool {
    if ibm12_path().is_none() {
        eprintln!("Skipping ibm12 bisect: benchmark file not found.");
        return false;
    }
    if !cfg!(debug_assertions) {
        return true;
    }
    let enabled = matches!(
        std::env::var("AY_RUN_IBM12_BISECT").as_deref(),
        Ok("1") | Ok("true") | Ok("TRUE")
    );
    if !enabled {
        eprintln!("Skipping ibm12 bisect in debug mode. Set AY_RUN_IBM12_BISECT=1 to enable.");
    }
    enabled
}

fn ibm12_path() -> Option<PathBuf> {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest.parent().unwrap().parent().unwrap();
    let candidates = [
        repo_root.join("reference/creusat/tests/cnf-hard/stric-bmc-ibm-12.cnf"),
        repo_root.join("benchmarks/sat/stric-bmc-ibm-12.cnf"),
    ];
    candidates.into_iter().find(|path| path.exists())
}

fn load_ibm12() -> String {
    let path = ibm12_path().expect("Cannot locate stric-bmc-ibm-12.cnf");
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("Cannot read {}: {e}", path.display()))
}

fn make_solver(
    bve: bool,
    cong: bool,
    cond: bool,
    probe: bool,
    subsume: bool,
    vivify: bool,
    bce: bool,
    preprocess: bool,
    gate: bool,
) -> (Solver, Vec<Vec<ay_sat::Literal>>) {
    let cnf = load_ibm12();
    let formula = parse_dimacs(&cnf).expect("parse");
    let original_clauses = formula.clauses.clone();
    let num_vars = formula.num_vars;
    let mut solver: Solver = Solver::new(num_vars);

    // Start with all disabled
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_gate_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_preprocess_enabled(preprocess);

    // Enable requested features
    solver.set_bve_enabled(bve);
    solver.set_congruence_enabled(cong);
    solver.set_condition_enabled(cond);
    solver.set_probe_enabled(probe);
    solver.set_subsume_enabled(subsume);
    solver.set_vivify_enabled(vivify);
    solver.set_bce_enabled(bce);
    solver.set_gate_enabled(gate);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    (solver, original_clauses)
}

fn assert_sat(solver: &mut Solver, label: &str) {
    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(_) => {}
        SatResult::Unsat(_) => {
            panic!("BUG: {label} returned UNSAT on known-SAT stric-bmc-ibm-12");
        }
        SatResult::Unknown => {
            let reason = solver.last_unknown_reason();
            panic!("{label} returned Unknown (reason: {reason:?}) on stric-bmc-ibm-12");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

// ========== Baseline ==========

#[test]
#[timeout(120_000)]
fn ibm12_baseline_all_disabled() {
    if !should_run_ibm12_bisect() {
        return;
    }
    let (mut solver, _) = make_solver(
        false, false, false, false, false, false, false, false, false,
    );
    assert_sat(&mut solver, "baseline");
}

// ========== Individual features ==========

#[test]
#[timeout(120_000)]
fn ibm12_bve_only() {
    if !should_run_ibm12_bisect() {
        return;
    }
    let (mut solver, _) = make_solver(true, false, false, false, false, false, false, true, true);
    assert_sat(&mut solver, "bve-only");
}

#[test]
#[timeout(120_000)]
fn ibm12_congruence_only() {
    if !should_run_ibm12_bisect() {
        return;
    }
    let (mut solver, _) = make_solver(false, true, false, false, false, false, false, true, true);
    assert_sat(&mut solver, "congruence-only");
}

#[test]
#[timeout(120_000)]
fn ibm12_condition_only() {
    if !should_run_ibm12_bisect() {
        return;
    }
    let (mut solver, _) = make_solver(false, false, true, false, false, false, false, true, false);
    assert_sat(&mut solver, "condition-only");
}

// ========== Pairwise: congruence + elimination (THE BUG) ==========

#[test]
#[timeout(120_000)]
fn ibm12_bve_plus_cong_preprocess_on() {
    if !should_run_ibm12_bisect() {
        return;
    }
    let (mut solver, _) = make_solver(true, true, false, false, false, false, false, true, true);
    assert_sat(&mut solver, "bve+cong (preprocess=on)");
}

#[test]
#[timeout(120_000)]
fn ibm12_bve_plus_cong_preprocess_off() {
    if !should_run_ibm12_bisect() {
        return;
    }
    // Only inprocessing: is the bug in preprocessing or inprocessing?
    let (mut solver, _) = make_solver(true, true, false, false, false, false, false, false, true);
    assert_sat(&mut solver, "bve+cong (preprocess=off)");
}

#[test]
#[timeout(120_000)]
fn ibm12_cong_plus_cond_preprocess_on() {
    if !should_run_ibm12_bisect() {
        return;
    }
    let (mut solver, _) = make_solver(false, true, true, false, false, false, false, true, true);
    assert_sat(&mut solver, "cong+cond (preprocess=on)");
}

#[test]
#[timeout(120_000)]
fn ibm12_cong_plus_cond_preprocess_off() {
    if !should_run_ibm12_bisect() {
        return;
    }
    let (mut solver, _) = make_solver(false, true, true, false, false, false, false, false, true);
    assert_sat(&mut solver, "cong+cond (preprocess=off)");
}

// ========== Other pairwise (should pass) ==========

#[test]
#[timeout(120_000)]
fn ibm12_bve_plus_cond() {
    if !should_run_ibm12_bisect() {
        return;
    }
    let (mut solver, _) = make_solver(true, false, true, false, false, false, false, true, true);
    assert_sat(&mut solver, "bve+cond");
}

#[test]
#[timeout(120_000)]
fn ibm12_cong_plus_bce() {
    if !should_run_ibm12_bisect() {
        return;
    }
    let (mut solver, _) = make_solver(false, true, false, false, false, false, true, true, true);
    assert_sat(&mut solver, "cong+bce");
}

// ========== All enabled ==========

#[test]
#[timeout(120_000)]
fn ibm12_all_enabled() {
    if !should_run_ibm12_bisect() {
        return;
    }
    let (mut solver, _) = make_solver(true, true, true, true, true, true, true, true, true);
    assert_sat(&mut solver, "all-enabled");
}
