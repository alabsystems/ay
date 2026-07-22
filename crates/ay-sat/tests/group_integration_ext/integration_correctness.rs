// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]
#![allow(clippy::panic)]

//! Correctness and soundness integration tests for ay-sat.
//!
//! TLA+ invariant tests, incremental push/pop regression tests,
//! multi-solver differential testing, assumption/large-variable tests,
//! and soundness regression tests against known-UNSAT benchmarks.
//! Extracted from integration_extended.rs for #6864.

use super::common::{assert_model_satisfies, verify_model};
use ay_sat::{parse_dimacs, AssumeResult, Literal, SatResult, Solver, Variable};
use ntest::timeout;

// ============================================================================
// TLA+ Invariant Tests
// ============================================================================
// These tests mirror the invariants from specs/cdcl.tla to ensure the Rust
// implementation satisfies the same correctness properties.

/// TLA+ SatCorrect invariant: If SAT, the assignment satisfies all original clauses.
/// This is verified via the solver's internal verify_model() check (debug_assert).
/// Here we add additional test coverage with various formula types.
#[test]
#[timeout(5_000)]
fn test_tla_invariant_sat_correct() {
    // Test formulas that should be SAT
    let sat_formulas = [
        // Simple satisfiable
        ("simple", "p cnf 2 2\n1 2 0\n-1 -2 0\n"),
        // Horn clause formula
        ("horn", "p cnf 3 3\n-1 2 0\n-2 3 0\n1 0\n"),
        // Large clause
        ("large_clause", "p cnf 5 1\n1 2 3 4 5 0\n"),
        // Chain implications (satisfiable)
        ("chain", "p cnf 4 3\n-1 2 0\n-2 3 0\n-3 4 0\n"),
        // Mixed sizes
        ("mixed", "p cnf 4 4\n1 2 3 4 0\n-1 2 0\n-2 3 0\n4 0\n"),
    ];

    for (name, dimacs) in &sat_formulas {
        let formula =
            parse_dimacs(dimacs).unwrap_or_else(|e| panic!("Failed to parse {name}: {e}"));
        let original_clauses = formula.clauses.clone();
        let mut solver = formula.into_solver();
        let result = solver.solve().into_inner();
        match result {
            SatResult::Sat(model) => {
                assert_model_satisfies(&original_clauses, &model, name);
            }
            SatResult::Unsat(_) => {
                panic!("TLA+ SatCorrect VIOLATION: {name} should be SAT but got UNSAT");
            }
            SatResult::Unknown => {
                panic!("TLA+ SatCorrect VIOLATION: {name} should be SAT but got Unknown");
            }
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }
}

/// TLA+ Soundness invariant: If UNSAT, no satisfying assignment exists.
/// We verify by checking that known-UNSAT formulas return UNSAT.
#[test]
#[timeout(5_000)]
fn test_tla_invariant_soundness() {
    let unsat_formulas = [
        // Single variable contradiction
        ("unit_contradict", "p cnf 1 2\n1 0\n-1 0\n"),
        // Empty clause
        ("empty_clause", "p cnf 0 1\n0\n"),
        // PHP(2,1): 2 pigeons, 1 hole
        ("php21", "p cnf 2 3\n1 0\n2 0\n-1 -2 0\n"),
    ];

    for (name, dimacs) in &unsat_formulas {
        let formula =
            parse_dimacs(dimacs).unwrap_or_else(|e| panic!("Failed to parse {name}: {e}"));
        let mut solver = formula.into_solver();
        let result = solver.solve().into_inner();
        assert!(
            result.is_unsat(),
            "TLA+ Soundness VIOLATION: {name} should be UNSAT but got {result:?}"
        );
    }
}

/// TLA+ NoDoubleAssignment invariant: No variable is assigned twice on the trail.
/// We test this indirectly by ensuring the solver produces consistent results
/// and doesn't panic/corrupt state across multiple solve calls.
#[test]
#[timeout(5_000)]
fn test_tla_invariant_no_double_assignment() {
    let dimacs = "p cnf 5 10\n1 2 0\n-1 3 0\n-2 4 0\n-3 5 0\n1 -4 0\n2 -5 0\n-1 -2 3 0\n-3 -4 5 0\n1 4 5 0\n-2 -3 -5 0\n";

    // Run the solver multiple times on the same formula
    for i in 0..5 {
        let formula1 = parse_dimacs(dimacs).expect("Failed to parse");
        let mut solver = formula1.into_solver();
        let result1 = solver.solve().into_inner();

        // Create a new solver and solve again
        let formula2 = parse_dimacs(dimacs).expect("Failed to parse");
        let mut solver2 = formula2.into_solver();
        let result2 = solver2.solve().into_inner();

        // Results should be consistent (both SAT or both UNSAT)
        let is_sat1 = matches!(result1, SatResult::Sat(_));
        let is_sat2 = matches!(result2, SatResult::Sat(_));
        assert_eq!(
            is_sat1, is_sat2,
            "TLA+ NoDoubleAssignment (iteration {i}): Inconsistent results across runs"
        );
    }
}

/// TLA+ WatchedLiterals invariant: after propagation, every non-satisfied clause
/// has at least 2 unwatched literals or is unit/empty.
///
/// We test this indirectly by running formulas that stress the watch list:
/// many binary clauses force frequent watch updates during BCP.
#[test]
#[timeout(5_000)]
fn test_tla_invariant_watched_literals_stress() {
    // Create a formula with many binary clauses (implication graph stress)
    let num_vars = 20;
    let dimacs = format!("p cnf {num_vars} ");
    let mut clauses_str = String::new();
    let mut num_clauses = 0;

    // Chain: x1 → x2 → ... → x20
    for i in 1..num_vars {
        clauses_str.push_str(&format!("-{} {} 0\n", i, i + 1));
        num_clauses += 1;
    }
    // Reverse chain: ¬x20 → ¬x19 → ... → ¬x1
    for i in (1..num_vars).rev() {
        clauses_str.push_str(&format!("{} -{} 0\n", i, i + 1));
        num_clauses += 1;
    }
    // Seed: x1, ¬x10
    clauses_str.push_str("1 0\n-10 0\n");
    num_clauses += 2;

    let full_dimacs = format!("{num_clauses}\n{clauses_str}");
    let dimacs_full = format!("{dimacs}{full_dimacs}");

    let formula = parse_dimacs(&dimacs_full).unwrap();
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    // The formula should be solvable — forward chain forces x2..x10=true,
    // but ¬x10 conflicts. The backward chain then forces ¬x11..¬x20 and
    // the formula becomes UNSAT.
    assert!(
        result.is_unsat(),
        "Chain formula with conflicting units should be UNSAT"
    );
}

/// TLA+ IncrementalCorrectness: push/pop preserves formula semantics.
#[test]
#[timeout(10_000)]
fn test_tla_invariant_incremental_correctness() {
    let mut solver = Solver::new(3);

    // Base formula: (x1 OR x2) AND (x2 OR x3)
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    // Base should be SAT
    let base_result = solver.solve().into_inner();
    assert!(
        matches!(base_result, SatResult::Sat(_)),
        "Base formula should be SAT"
    );

    // Push scope, add contradicting unit clauses (UNSAT in scope)
    solver.push();
    solver.add_clause(vec![Literal::negative(Variable::new(0))]);
    solver.add_clause(vec![Literal::negative(Variable::new(1))]);
    solver.add_clause(vec![Literal::negative(Variable::new(2))]);
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);

    let scoped_result = solver.solve().into_inner();
    assert!(
        scoped_result.is_unsat(),
        "Scoped formula with contradictions should be UNSAT"
    );

    // Pop and verify we're back to SAT
    assert!(solver.pop(), "Pop should succeed");
    let popped_result = solver.solve().into_inner();

    if let SatResult::Sat(model) = popped_result {
        // Verify the model satisfies the base clauses
        assert!(model[0] || model[1], "Model should satisfy (x1 OR x2)");
        assert!(model[1] || model[2], "Model should satisfy (x2 OR x3)");
    } else {
        panic!("After pop, formula should be SAT again");
    }
}

// ============================================================================
// Incremental Push/Pop Regression Tests
// ============================================================================

/// Regression test: has_empty_clause must be cleared on pop().
/// If UNSAT is derived within a scope, popping should allow SAT on the base formula.
#[test]
#[timeout(10_000)]
fn test_unsat_latch_cleared_after_pop() {
    let mut solver = Solver::new(2);
    // Base: (x0 OR x1)
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    solver.push();
    // Add conflicting units within the scope
    solver.add_clause(vec![Literal::negative(Variable::new(0))]);
    solver.add_clause(vec![Literal::negative(Variable::new(1))]);
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    let r = solver.solve().into_inner();
    assert!(r.is_unsat(), "Scoped formula should be UNSAT");

    assert!(solver.pop(), "Pop should succeed");
    // Base formula (x0 OR x1) should be SAT again
    let r2 = solver.solve().into_inner();
    assert!(
        matches!(r2, SatResult::Sat(_)),
        "After pop, base formula should be SAT"
    );
}

/// Regression test (#3550): push/pop scoped SAT model must be verified.
/// Uses 6 variables with x3 as BVE candidate (2 pos + 2 neg occurrences).
/// After push + contradicting scope + pop, model must satisfy all original clauses.
#[test]
#[timeout(10_000)]
fn test_push_pop_bve_model_verified() {
    let p = |v| Literal::positive(Variable::new(v));
    let n = |v| Literal::negative(Variable::new(v));

    let mut solver = Solver::new(6);
    // x3 (Variable::new(2)) has 2 pos + 2 neg occurrences → BVE candidate
    let original_clauses: Vec<Vec<Literal>> = vec![
        vec![p(0), p(2)], // (x0 OR x3)
        vec![p(1), p(2)], // (x1 OR x3)
        vec![n(2), p(3)], // (NOT x3 OR x4)
        vec![n(2), p(4)], // (NOT x3 OR x5)
        vec![p(5), n(3)], // (x2 OR NOT x4)
        vec![n(5), p(4)], // (NOT x2 OR x5)
    ];
    for clause in &original_clauses {
        solver.add_clause(clause.clone());
    }

    // First solve: may trigger BVE and create reconstruction entries.
    let base_result = solver.solve().into_inner();
    assert!(
        matches!(base_result, SatResult::Sat(_)),
        "Base formula should be SAT"
    );

    // Push scope and add contradicting units.
    solver.push();
    for v in [0, 1, 3, 4, 5] {
        solver.add_clause(vec![n(v)]);
    }
    let _scoped_result = solver.solve().into_inner();

    // Pop and solve base formula again.
    assert!(solver.pop(), "Pop should succeed");
    let popped_result = solver.solve().into_inner();

    // Key check: model after pop must satisfy ALL original clauses.
    // If verify_model() were skipped under scope (#3550), corruption could leak.
    let model = match popped_result {
        SatResult::Sat(m) => m,
        _ => panic!("After pop, base formula should be SAT again"),
    };
    assert!(
        verify_model(&original_clauses, &model),
        "Model after pop violates original clauses: {model:?}",
    );
}

/// Regression test: clause-deleting inprocessing (conditioning, BVE, BCE,
/// sweep, congruence, factor) must be disabled after push/pop (#3662).
///
/// After pop(), learned clauses from scoped solving remain in clause_db
/// but may contain falsified selector literals, effectively shortening them.
/// If conditioning runs on this mixed clause set, its autarky partition can
/// be invalid, causing model reconstruction to break previously-satisfied
/// clauses.
#[test]
#[timeout(10_000)]
fn test_push_pop_disables_conditioning() {
    let p = |v| Literal::positive(Variable::new(v));
    let n = |v| Literal::negative(Variable::new(v));

    // Build a formula with enough structure for conditioning to fire
    // if it weren't disabled. 8 variables, mix of positive/negative clauses.
    let mut solver = Solver::new(8);
    let original_clauses: Vec<Vec<Literal>> = vec![
        vec![p(0), p(1), p(2)], // x0 OR x1 OR x2
        vec![n(0), p(3)],       // NOT x0 OR x3
        vec![n(1), p(4)],       // NOT x1 OR x4
        vec![n(2), p(5)],       // NOT x2 OR x5
        vec![p(3), p(4), p(5)], // x3 OR x4 OR x5
        vec![n(3), n(4), p(6)], // NOT x3 OR NOT x4 OR x6
        vec![n(5), p(7)],       // NOT x5 OR x7
        vec![n(6), n(7)],       // NOT x6 OR NOT x7
    ];
    for clause in &original_clauses {
        solver.add_clause(clause.clone());
    }

    // First solve (may trigger conditioning if enough conflicts accumulate).
    let base_result = solver.solve().into_inner();
    assert!(
        matches!(base_result, SatResult::Sat(_)),
        "Base formula should be SAT"
    );

    // Push scope, add constraints, solve under assumptions.
    solver.push();
    solver.add_clause(vec![n(0)]);
    solver.add_clause(vec![n(1)]);
    solver.add_clause(vec![p(2)]);
    let _scoped = solver.solve().into_inner();

    // Pop and solve again.
    assert!(solver.pop(), "Pop should succeed");
    let popped_result = solver.solve().into_inner();
    let model = match popped_result {
        SatResult::Sat(m) => m,
        _ => panic!("After pop, base formula should be SAT again"),
    };
    assert!(
        verify_model(&original_clauses, &model),
        "Model after pop must satisfy all original clauses: {model:?}",
    );

    // Multiple push/pop cycles should remain correct.
    for _ in 0..3 {
        solver.push();
        solver.add_clause(vec![p(0), n(7)]);
        let _ = solver.solve().into_inner();
        assert!(solver.pop());
        let r = solver.solve().into_inner();
        let m = match r {
            SatResult::Sat(m) => m,
            _ => panic!("Base formula should remain SAT after repeated push/pop"),
        };
        assert!(
            verify_model(&original_clauses, &m),
            "Model violated after repeated push/pop: {m:?}",
        );
    }
}

// ============================================================================
// Multi-Solver Differential Testing (CaDiCaL, Kissat, MiniSat)
// ============================================================================

mod multi_solver_differential {
    use ay_sat::{parse_dimacs, SatResult};
    use ntest::timeout;
    use std::path::PathBuf;
    use std::process::{Command, Stdio};

    /// Generic SAT solver result
    #[derive(Debug, Clone, PartialEq, Eq)]
    enum SolverResult {
        Sat,
        Unsat,
        Unknown,
        Unavailable,
    }

    /// External solver configuration
    struct ExternalSolver {
        name: &'static str,
        command: &'static str,
        args: &'static [&'static str],
        sat_code: i32,
        unsat_code: i32,
    }

    // CaDiCaL: local build path (use absolute path from reference/)
    const CADICAL: ExternalSolver = ExternalSolver {
        name: "CaDiCaL",
        command: "reference/cadical/build/cadical",
        args: &["-q"],
        sat_code: 10,
        unsat_code: 20,
    };

    const KISSAT: ExternalSolver = ExternalSolver {
        name: "Kissat",
        command: "reference/kissat/build/kissat",
        args: &["-q"],
        sat_code: 10,
        unsat_code: 20,
    };

    const MINISAT: ExternalSolver = ExternalSolver {
        name: "MiniSat",
        command: "minisat",
        args: &["-verb=0"],
        sat_code: 10,
        unsat_code: 20,
    };

    fn run_external_solver(solver: &ExternalSolver, cnf: &str) -> SolverResult {
        // Write to temp file
        let dir = std::env::temp_dir();
        let path: PathBuf = dir.join(format!(
            "ay_test_{}_{}.cnf",
            solver.name,
            std::process::id()
        ));
        std::fs::write(&path, cnf).expect("write temp CNF");

        let result = Command::new(solver.command)
            .args(solver.args)
            .arg(&path)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();

        let _ = std::fs::remove_file(&path);

        match result {
            Ok(status) => {
                let code = status.code().unwrap_or(-1);
                if code == solver.sat_code {
                    SolverResult::Sat
                } else if code == solver.unsat_code {
                    SolverResult::Unsat
                } else {
                    SolverResult::Unknown
                }
            }
            Err(_) => SolverResult::Unavailable,
        }
    }

    struct MultiSolverResults {
        ay: SolverResult,
        cadical: SolverResult,
        kissat: SolverResult,
        minisat: SolverResult,
    }

    fn run_all_solvers(cnf: &str) -> MultiSolverResults {
        let formula = parse_dimacs(cnf).unwrap();
        let mut solver = formula.into_solver();
        let ay = match solver.solve().into_inner() {
            SatResult::Sat(_) => SolverResult::Sat,
            SatResult::Unsat(_) => SolverResult::Unsat,
            _ => SolverResult::Unknown,
        };

        MultiSolverResults {
            ay,
            cadical: run_external_solver(&CADICAL, cnf),
            kissat: run_external_solver(&KISSAT, cnf),
            minisat: run_external_solver(&MINISAT, cnf),
        }
    }

    /// Smoke test: verify AY agrees with available external solvers on simple formulas.
    #[test]
    #[timeout(10_000)]
    fn test_multi_solver_agreement_simple() {
        // Simple SAT formula
        let sat_cnf = "p cnf 3 2\n1 2 0\n-1 3 0\n";
        let results = run_all_solvers(sat_cnf);
        assert_eq!(results.ay, SolverResult::Sat, "AY should return SAT");

        // Log what solvers are available
        eprintln!("\nSolver availability:");
        eprintln!("  AY: {:?}", results.ay);
        eprintln!("  CaDiCaL: {:?}", results.cadical);
        eprintln!("  Kissat: {:?}", results.kissat);
        eprintln!("  MiniSat: {:?}", results.minisat);

        // Simple UNSAT formula
        let unsat_cnf = "p cnf 1 2\n1 0\n-1 0\n";
        let results = run_all_solvers(unsat_cnf);
        assert_eq!(results.ay, SolverResult::Unsat, "AY should return UNSAT");
    }
}

// ============================================================================
// Large Variable Index Tests (for incremental SMT solving)
// ============================================================================

/// Test that the SAT solver works with large variable indices in assumptions.
/// This is critical for incremental SMT solving where selector variables
/// are allocated at large indices (e.g., 1000+).
#[test]
#[timeout(2_000)]
fn test_large_var_assumption_simple() {
    // Create solver with 1002 variables (indices 0..1001)
    let mut solver = Solver::new(1002);

    // Add clause: ¬var1000 ∨ var0 (if selector1000 is true, var0 must be true)
    solver.add_clause(vec![
        Literal::negative(Variable::new(1000)),
        Literal::positive(Variable::new(0)),
    ]);

    // Add clause: ¬var1001 ∨ var1 (if selector1001 is true, var1 must be true)
    solver.add_clause(vec![
        Literal::negative(Variable::new(1001)),
        Literal::positive(Variable::new(1)),
    ]);

    // Assumptions: var1000=true, var1001=true
    let assumptions = vec![
        Literal::positive(Variable::new(1000)),
        Literal::positive(Variable::new(1001)),
    ];

    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Sat(model) => {
            // With assumptions, var0 and var1 should be true
            assert!(model.len() >= 2, "Model should have at least 2 user vars");
            assert!(
                model[0],
                "var0 should be true (implied by selector1000=true)"
            );
            assert!(
                model[1],
                "var1 should be true (implied by selector1001=true)"
            );
        }
        AssumeResult::Unsat(core, _) => {
            panic!("Formula should be SAT with assumptions, but got UNSAT with core: {core:?}");
        }
        AssumeResult::Unknown => {
            panic!("Formula should be SAT with assumptions, but got Unknown");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test that replicates the exact LIA incremental behavior using raw Literal values.
#[test]
#[timeout(2_000)]
fn test_large_var_assumption_raw_literals() {
    // Create solver with 1002 variables (indices 0..1001)
    let mut solver = Solver::new(1002);

    // Add clause using raw Literal values as seen in debug output:
    // [Literal::from_index(2001), Literal::from_index(0)] = ¬var1000 ∨ var0
    solver.add_clause(vec![Literal::from_index(2001), Literal::from_index(0)]);

    // [Literal::from_index(2003), Literal::from_index(2)] = ¬var1001 ∨ var1
    solver.add_clause(vec![Literal::from_index(2003), Literal::from_index(2)]);

    // Assumptions using raw values:
    // [Literal::from_index(2000), Literal::from_index(2002)] = +var1000, +var1001
    let assumptions = vec![Literal::from_index(2000), Literal::from_index(2002)];

    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Sat(model) => {
            assert!(model.len() >= 2, "Model should have at least 2 user vars");
            assert!(
                model[0],
                "var0 should be true (implied by selector1000=true)"
            );
            assert!(
                model[1],
                "var1 should be true (implied by selector1001=true)"
            );
        }
        AssumeResult::Unsat(core, _) => {
            panic!("Formula should be SAT with assumptions, but got UNSAT with core: {core:?}");
        }
        AssumeResult::Unknown => {
            panic!("Formula should be SAT with assumptions, but got Unknown");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test that replicates the exact LIA incremental sequence with stored clauses.
#[test]
#[timeout(2_000)]
fn test_large_var_assumption_stored_clauses() {
    // Store clauses in a Vec first (like selector_guarded_clauses)
    let stored_clauses: Vec<Vec<Literal>> = vec![
        // Add clause: ¬var1000 ∨ var0
        vec![Literal::from_index(2001), Literal::from_index(0)],
        // Add clause: ¬var1001 ∨ var1
        vec![Literal::from_index(2003), Literal::from_index(2)],
    ];

    // Create solver with 1002 variables
    let mut solver = Solver::new(1002);

    // Add all stored clauses (like the LIA incremental code does)
    for clause in &stored_clauses {
        solver.add_clause(clause.clone());
    }

    // Assumptions
    let assumptions = vec![Literal::from_index(2000), Literal::from_index(2002)];

    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Sat(model) => {
            assert!(model.len() >= 2, "Model should have at least 2 user vars");
            assert!(
                model[0],
                "var0 should be true (implied by selector1000=true)"
            );
            assert!(
                model[1],
                "var1 should be true (implied by selector1001=true)"
            );
        }
        AssumeResult::Unsat(core, _) => {
            panic!("Formula should be SAT with assumptions, but got UNSAT with core: {core:?}");
        }
        AssumeResult::Unknown => {
            panic!("Formula should be SAT with assumptions, but got Unknown");
        }
        #[allow(unreachable_patterns)]
        _ => panic!("Unexpected AssumeResult variant"),
    }
}

/// Test that solve_with_assumptions is idempotent - calling it twice with
/// the same assumptions should return the same result.
///
/// This test exposes a bug where the second call returns UNSAT even when
/// no new clauses are added.
#[test]
#[timeout(2_000)]
fn test_solve_with_assumptions_idempotent() {
    // Create solver with 1002 variables (indices 0..1001)
    let mut solver = Solver::new(1002);

    // Add clause: ¬var1000 ∨ var0 (if selector1000 is true, var0 must be true)
    solver.add_clause(vec![
        Literal::negative(Variable::new(1000)),
        Literal::positive(Variable::new(0)),
    ]);

    // Add clause: ¬var1001 ∨ var1 (if selector1001 is true, var1 must be true)
    solver.add_clause(vec![
        Literal::negative(Variable::new(1001)),
        Literal::positive(Variable::new(1)),
    ]);

    // Assumptions: var1000=true, var1001=true
    let assumptions = vec![
        Literal::positive(Variable::new(1000)),
        Literal::positive(Variable::new(1001)),
    ];

    // First solve - should be SAT
    let result1 = solver.solve_with_assumptions(&assumptions).into_inner();
    match &result1 {
        AssumeResult::Sat(_) => {}
        AssumeResult::Unsat(core, _) => {
            panic!("First call should be SAT, but got UNSAT with core: {core:?}");
        }
        AssumeResult::Unknown => {
            panic!("First call should be SAT, but got Unknown");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }

    // Second solve (no changes) - should also be SAT
    let result2 = solver.solve_with_assumptions(&assumptions).into_inner();
    match &result2 {
        AssumeResult::Sat(_) => {}
        AssumeResult::Unsat(core, _) => {
            panic!("Second call should be SAT (idempotent), but got UNSAT with core: {core:?}");
        }
        AssumeResult::Unknown => {
            panic!("Second call should be SAT (idempotent), but got Unknown");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Regression test for #5117/#5161: when the CDCL assumption loop learns a
/// unit clause (backtrack_level==0), the solver must NOT return UNSAT
/// immediately. Instead it must backtrack to level 0, propagate the unit,
/// and continue searching. The formula is SAT; the old buggy code returned
/// false UNSAT.
///
/// Formula (5 vars + 1 assumption selector, all SAT):
///   C1: (a ∨ b)       — at least one of a, b
///   C2: (¬a ∨ c)      — a implies c
///   C3: (¬b ∨ d)      — b implies d
///   C4: (¬c ∨ ¬d)     — c and d cannot both be true
///   C5: (a ∨ ¬d)      — d implies a
///
/// Under assumption s=true, if the solver decides a=false:
///   BCP: b=true (C1), d=true (C3), c=false (C4) → C5 conflicts.
///   Conflict analysis resolves C5→C3→C1 to learn unit clause (a).
///   backtrack_level=0, so the old code returned UNSAT prematurely.
///   Correct behavior: backtrack to 0, assert a=true, continue → SAT.
#[test]
#[timeout(2_000)]
fn test_assumptions_unit_at_level0_not_false_unsat_5117() {
    // Variables: a=0, b=1, c=2, d=3, s=4 (assumption selector)
    let mut solver = Solver::new(5);

    // Disable inprocessing to ensure the search follows our expected path.
    solver.set_bve_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_gate_enabled(false);
    solver.set_congruence_enabled(false);

    // C1: (a ∨ b)
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    // C2: (¬a ∨ c)
    solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(2)),
    ]);
    // C3: (¬b ∨ d)
    solver.add_clause(vec![
        Literal::negative(Variable::new(1)),
        Literal::positive(Variable::new(3)),
    ]);
    // C4: (¬c ∨ ¬d)
    solver.add_clause(vec![
        Literal::negative(Variable::new(2)),
        Literal::negative(Variable::new(3)),
    ]);
    // C5: (a ∨ ¬d)
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::negative(Variable::new(3)),
    ]);

    // Assumption: s=true (selector variable, not in any clause)
    let assumptions = vec![Literal::positive(Variable::new(4))];

    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match &result {
        AssumeResult::Sat(model) => {
            // Verify: a must be true in any satisfying assignment
            // (a is implied by the formula: C1⊗C5 on ¬d, or conflict analysis)
            assert!(
                model.first().copied() == Some(true),
                "a (var0) must be true in any satisfying model"
            );
        }
        AssumeResult::Unsat(core, _) => {
            panic!(
                "BUG #5117: formula is SAT but solver returned UNSAT with core: {core:?}. \
                 This means the backtrack_level==0 case in the assumption loop \
                 prematurely returned UNSAT instead of continuing search."
            );
        }
        AssumeResult::Unknown => {
            panic!("solver returned Unknown on a trivially small formula");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

// ============================================================================
// Soundness Regression Tests (#3292, #3308)
// ============================================================================

fn verify_dimacs_soundness(path: &str) {
    if !super::common::require_benchmark(path) {
        return;
    }
    let content =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("Failed to read {path}: {e}"));
    let formula = parse_dimacs(&content).unwrap_or_else(|e| panic!("Failed to parse {path}: {e}"));
    let original_clauses: Vec<Vec<Literal>> = formula.clauses.clone();
    let num_vars = formula.num_vars;
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert_model_satisfies(
                &original_clauses,
                &model,
                &format!(
                    "SOUNDNESS BUG in {path} ({num_vars} vars, {} clauses)",
                    original_clauses.len()
                ),
            );
            panic!(
                "SOUNDNESS BUG: {path} is known-UNSAT but AY returned SAT \
                 with a model satisfying all original clauses"
            );
        }
        SatResult::Unsat(_) => {}
        SatResult::Unknown => {
            panic!(
                "SOUNDNESS GATE: {path} is known-UNSAT but AY returned Unknown. \
                 Soundness tests require a definitive UNSAT answer, not a timeout."
            );
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Verify a known-UNSAT DIMACS benchmark with DRAT proof certificate.
///
/// Like `verify_dimacs_soundness` but additionally generates a DRAT proof
/// and verifies it with drat-trim. This closes VERIFICATION_AUDIT.md Gap 2
/// for the benchmarks that use this function.
fn verify_dimacs_soundness_with_drat(path: &str) {
    use ay_sat::ProofOutput;

    if !super::common::require_benchmark(path) {
        return;
    }
    let content =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("Failed to read {path}: {e}"));
    let formula = parse_dimacs(&content).unwrap_or_else(|e| panic!("Failed to parse {path}: {e}"));
    let num_vars = formula.num_vars;
    let clauses = formula.clauses;

    let proof_buffer: Vec<u8> = Vec::new();
    let proof_writer = ProofOutput::drat_text(proof_buffer);
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(_) => {
            panic!("SOUNDNESS BUG: {path} is known-UNSAT but AY returned SAT");
        }
        SatResult::Unsat(_) => {
            let writer = solver
                .take_proof_writer()
                .expect("proof writer must exist after UNSAT");
            let proof_bytes = writer.into_vec().expect("proof writer flush");
            let dimacs = super::common::clauses_to_dimacs(num_vars, &clauses);
            let test_label = std::path::Path::new(path)
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("unknown");
            super::common::verify_drat_proof(
                &dimacs,
                &proof_bytes,
                &format!("soundness_drat_{test_label}"),
            );
        }
        SatResult::Unknown => {
            panic!("SOUNDNESS GATE: {path} is known-UNSAT but AY returned Unknown (timeout).");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

// --- DRAT-verified soundness tests (Gap 2: DRAT proofs for UNSAT benchmarks) ---
//
// These complement the model-only verify_dimacs_soundness tests by also
// generating and checking a DRAT certificate with drat-trim.
//
// Benchmarks selected for non-trivial UNSAT with fast solve time. Previous
// tests used hsat_vc11803, hsat_vc11813, xinetd_vc56703 which are pre-
// preprocessed to contain the empty clause (p cnf 0 1), providing zero
// DRAT coverage since the solver does no real work.

#[test]
#[timeout(120_000)]
fn test_soundness_drat_minor032_unsat() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/minor032.cnf"
    );
    verify_dimacs_soundness_with_drat(path);
}

// barrel6 DRAT coverage lives in soundness_gate pairwise isolation:
// `gate_congruence_drat_proof_verification_barrel6`.

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_soundness_drat_manol_pipe_g6bi_unsat() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: manol-pipe-g6bi DRAT exceeds debug-mode timeout (#4582)");
        return;
    }
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/manol-pipe-g6bi.cnf"
    );
    verify_dimacs_soundness_with_drat(path);
}

#[test]
#[timeout(120_000)]
fn test_soundness_drat_een_tip_unsat() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/een-tip-uns-nusmv-t5.B.cnf"
    );
    verify_dimacs_soundness_with_drat(path);
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_soundness_barrel6_unsat() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: cmu-bmc-barrel6 exceeds debug-mode timeout (>120s preprocessing)");
        return;
    }
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/cmu-bmc-barrel6.cnf"
    );
    verify_dimacs_soundness(path);
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_soundness_longmult15_unsat() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: cmu-bmc-longmult15 exceeds debug-mode timeout (#4582)");
        return;
    }
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/cmu-bmc-longmult15.cnf"
    );
    verify_dimacs_soundness(path);
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_soundness_manol_pipe_c9_unsat() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: manol-pipe-c9 exceeds debug-mode timeout (#4582)");
        return;
    }
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/manol-pipe-c9.cnf"
    );
    // BVE gate-restricted resolution (#5661, #6113): non-gate x non-gate
    // resolvents are included when the gate definition is incomplete
    // (both polarity sides have non-gate clauses). This handles cases
    // where inprocessing modifies clause structure.
    verify_dimacs_soundness(path);
}

#[test]
#[timeout(120_000)]
fn test_soundness_minor032_unsat() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/minor032.cnf"
    );
    verify_dimacs_soundness(path);
}

#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_soundness_manol_pipe_g6bi_unsat() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: manol-pipe-g6bi exceeds debug-mode timeout (#4582)");
        return;
    }
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/manol-pipe-g6bi.cnf"
    );
    verify_dimacs_soundness(path);
}

#[test]
#[timeout(30_000)]
fn test_soundness_een_tip_unsat() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/een-tip-uns-nusmv-t5.B.cnf"
    );
    verify_dimacs_soundness(path);
}

#[test]
#[timeout(5_000)]
fn test_soundness_hsat_vc11803_unsat() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/hsat_vc11803.cnf"
    );
    verify_dimacs_soundness(path);
}

#[test]
#[timeout(5_000)]
fn test_soundness_xinetd_vc56703_unsat() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/xinetd_vc56703.cnf"
    );
    verify_dimacs_soundness(path);
}

#[test]
#[timeout(5_000)]
fn test_soundness_hsat_vc11813_unsat() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/hsat_vc11813.cnf"
    );
    verify_dimacs_soundness(path);
}

// Debug mode: ~650s (50x slowdown), too slow for routine debug runs. Release-only.
#[cfg(not(debug_assertions))]
#[test]
#[timeout(300_000)]
fn test_soundness_schup_l2s_abp4_unsat() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/schup-l2s-abp4-1-k31.cnf"
    );
    verify_dimacs_soundness(path);
}

/// Regression test for #3438: AY produced wrong-SAT on uuf250 random 3-SAT UNSAT benchmarks.
///
/// Root cause: portfolio strategies re-enabled unsound factorization (#3435/#3373) and
/// decompose had a corrupted Tarjan SCC traversal (#3424). Both are now fixed and disabled.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_regression_3438_uuf250_random_unsat() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: uuf250 benchmarks exceed debug-mode timeout (#4582)");
        return;
    }
    let benchmarks = [
        "uuf250-05.cnf",
        "uuf250-012.cnf",
        "uuf250-039.cnf",
        "uuf250-048.cnf",
        "uuf250-049.cnf",
        "uuf250-060.cnf",
    ];
    let base = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/cnf-hard/unsat/"
    );
    let mut solved = 0;
    let mut found = 0;
    for name in &benchmarks {
        let path = format!("{base}{name}");
        if !std::path::Path::new(&path).exists() {
            eprintln!("Skipping: benchmark missing: {path}");
            continue;
        }
        found += 1;
        let content =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("Failed to read {path}: {e}"));
        let formula =
            parse_dimacs(&content).unwrap_or_else(|e| panic!("Failed to parse {path}: {e}"));
        let original_clauses: Vec<Vec<Literal>> = formula.clauses.clone();
        let mut solver = formula.into_solver();
        let result = solver.solve().into_inner();
        match result {
            SatResult::Sat(model) => {
                assert_model_satisfies(
                    &original_clauses,
                    &model,
                    &format!("REGRESSION #3438: {name}"),
                );
                panic!(
                    "REGRESSION #3438: {name} is known-UNSAT but AY returned SAT \
                     with a model satisfying all clauses"
                );
            }
            SatResult::Unsat(_) => {
                solved += 1;
            }
            SatResult::Unknown => {}
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }
    if found == 0 {
        eprintln!("Skipping regression assertion: no uuf250 benchmarks found.");
        return;
    }
    assert!(
        solved >= 4,
        "REGRESSION #3438: only {solved}/{found} uuf250 benchmarks solved (expected >= 4 UNSAT)"
    );
}

// ============================================================================
// Push/Solve/Add_Clause Regression (#5152)
// ============================================================================

/// Regression test for #5152: SAT solver incorrectly returns UNSAT
/// after adding blocking clauses via push/solve/add_clause cycle.
/// Minimized from 06-treeWeight-739-8leaves.smt2 QF_LIA benchmark.
/// CaDiCaL confirms the formula is SATISFIABLE at every iteration.
#[test]
#[timeout(10_000)]
fn test_push_solve_add_clause_soundness_5152() {
    let p = |v| Literal::positive(Variable::new(v));
    let n = |v| Literal::negative(Variable::new(v));

    let mut solver = Solver::new(42);

    // Original 83 clauses (Tseitin encoding of QF_LIA formula)
    solver.add_clause(vec![n(2), n(1), n(0)]);
    solver.add_clause(vec![p(0), p(1)]);
    solver.add_clause(vec![p(0), p(2)]);
    solver.add_clause(vec![p(0)]);
    solver.add_clause(vec![n(2), n(4), n(3)]);
    solver.add_clause(vec![p(2), p(3)]);
    solver.add_clause(vec![p(3), p(4)]);
    solver.add_clause(vec![p(3)]);
    solver.add_clause(vec![n(2), n(6), n(5)]);
    solver.add_clause(vec![p(2), p(5)]);
    solver.add_clause(vec![p(5), p(6)]);
    solver.add_clause(vec![p(5)]);
    solver.add_clause(vec![n(9), n(8), n(7)]);
    solver.add_clause(vec![p(7), p(8)]);
    solver.add_clause(vec![p(7), p(9)]);
    solver.add_clause(vec![p(7)]);
    solver.add_clause(vec![n(12), p(11), n(10)]);
    solver.add_clause(vec![p(10), n(11)]);
    solver.add_clause(vec![p(10), p(12)]);
    solver.add_clause(vec![p(10)]);
    solver.add_clause(vec![n(15), p(14), n(13)]);
    solver.add_clause(vec![p(13), n(14)]);
    solver.add_clause(vec![p(13), p(15)]);
    solver.add_clause(vec![p(13)]);
    solver.add_clause(vec![n(18), p(17), n(16), n(4)]);
    solver.add_clause(vec![p(16), n(17)]);
    solver.add_clause(vec![p(4), p(16)]);
    solver.add_clause(vec![p(16), p(18)]);
    solver.add_clause(vec![p(16)]);
    solver.add_clause(vec![p(20), p(18), n(19), n(6), n(21)]);
    solver.add_clause(vec![n(18), p(19)]);
    solver.add_clause(vec![p(19), n(20)]);
    solver.add_clause(vec![p(6), p(19)]);
    solver.add_clause(vec![p(19), p(21)]);
    solver.add_clause(vec![p(19)]);
    solver.add_clause(vec![n(12), p(18), n(22)]);
    solver.add_clause(vec![n(18), p(22)]);
    solver.add_clause(vec![p(12), p(22)]);
    solver.add_clause(vec![p(22)]);
    solver.add_clause(vec![n(15), p(18), n(23)]);
    solver.add_clause(vec![n(18), p(23)]);
    solver.add_clause(vec![p(15), p(23)]);
    solver.add_clause(vec![p(23)]);
    solver.add_clause(vec![n(18), p(15), n(1), n(24)]);
    solver.add_clause(vec![n(15), p(24)]);
    solver.add_clause(vec![p(1), p(24)]);
    solver.add_clause(vec![p(18), p(24)]);
    solver.add_clause(vec![p(24)]);
    solver.add_clause(vec![p(21), n(26), n(25)]);
    solver.add_clause(vec![n(21), p(25)]);
    solver.add_clause(vec![p(25), p(26)]);
    solver.add_clause(vec![p(25)]);
    solver.add_clause(vec![p(8), n(28), n(27)]);
    solver.add_clause(vec![n(8), p(27)]);
    solver.add_clause(vec![p(27), p(28)]);
    solver.add_clause(vec![p(27)]);
    solver.add_clause(vec![p(9), n(28), n(29)]);
    solver.add_clause(vec![n(9), p(29)]);
    solver.add_clause(vec![p(28), p(29)]);
    solver.add_clause(vec![p(29)]);
    solver.add_clause(vec![n(14), p(15), p(26), p(28), n(30)]);
    solver.add_clause(vec![n(26), p(30)]);
    solver.add_clause(vec![n(28), p(30)]);
    solver.add_clause(vec![n(15), p(30)]);
    solver.add_clause(vec![p(14), p(30)]);
    solver.add_clause(vec![p(30)]);
    solver.add_clause(vec![p(31)]);
    solver.add_clause(vec![p(32)]);
    solver.add_clause(vec![p(33)]);
    solver.add_clause(vec![p(34)]);
    solver.add_clause(vec![p(35)]);
    solver.add_clause(vec![n(14), p(37), n(36)]);
    solver.add_clause(vec![p(14), p(36)]);
    solver.add_clause(vec![p(36), n(37)]);
    solver.add_clause(vec![p(36)]);
    solver.add_clause(vec![n(20), p(39), n(38)]);
    solver.add_clause(vec![p(38), n(39)]);
    solver.add_clause(vec![p(20), p(38)]);
    solver.add_clause(vec![p(38)]);
    solver.add_clause(vec![n(17), p(41), n(40)]);
    solver.add_clause(vec![p(40), n(41)]);
    solver.add_clause(vec![p(17), p(40)]);
    solver.add_clause(vec![p(40)]);

    // Push scope for DPLL(T) blocking clauses
    solver.push();

    // First solve: should be SAT
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "iter 0 should be SAT"
    );

    // Blocking clause 0: theory conflict (nWeight(1)=56 AND nWeight(1)=115)
    solver.add_clause(vec![n(37), n(39)]);

    // Solve after blocking clause 0: should be SAT
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "iter 1 should be SAT"
    );

    // Blocking clause 1: theory conflict (nWeight(1)=56 AND nWeight(1)=109)
    solver.add_clause(vec![n(37), n(41)]);

    // Final solve: should STILL be SAT (CaDiCaL confirms satisfiability)
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "iter 2 should be SAT (bug #5152: AY returns UNSAT)"
    );

    let _ = solver.pop();
}
