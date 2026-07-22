// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #8480: SAT solver returns spurious UNSAT when an
//! Extension's check() adds circuit clauses mid-solve.
//!
//! The test constructs a satisfiable formula where some "result" variables
//! are unconstrained. An Extension's check() is called when a complete model
//! is found, and it adds clauses that constrain the result variables to
//! specific values. The combined formula is satisfiable, so the solver must
//! return SAT, not UNSAT.

use ay_sat::{
    ExtCheckResult, ExtPropagateResult, Extension, Literal, SatResult, Solver, SolverContext,
    Variable,
};
use std::sync::Mutex;

/// Extension that adds constraining clauses when check() is called.
struct DelayedCircuitExtension {
    /// Clauses to add on first check() call.
    circuit_clauses: Mutex<Option<Vec<Vec<Literal>>>>,
    check_count: Mutex<u32>,
}

impl Extension for DelayedCircuitExtension {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::default()
    }

    fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
        let mut count = self.check_count.lock().unwrap();
        *count += 1;

        // On first check, add the circuit clauses
        let mut clauses_opt = self.circuit_clauses.lock().unwrap();
        if let Some(clauses) = clauses_opt.take() {
            return ExtCheckResult::AddClauses(clauses);
        }

        // On subsequent checks, accept the model
        ExtCheckResult::Sat
    }

    fn backtrack(&mut self, _new_level: u32) {}
}

fn dimacs_to_literal(l: i32) -> Literal {
    let var = Variable::new(l.unsigned_abs() - 1);
    if l > 0 {
        Literal::positive(var)
    } else {
        Literal::negative(var)
    }
}

/// Parse a DIMACS CNF string into (num_vars, clauses as DIMACS literals).
fn parse_cnf(cnf: &str) -> (usize, Vec<Vec<i32>>) {
    let mut num_vars = 0;
    let mut clauses = Vec::new();
    for line in cnf.lines() {
        if line.starts_with('c') || line.is_empty() {
            continue;
        }
        if line.starts_with('p') {
            let parts: Vec<&str> = line.split_whitespace().collect();
            num_vars = parts[2].parse().unwrap();
            continue;
        }
        let lits: Vec<i32> = line
            .split_whitespace()
            .filter_map(|s| s.parse::<i32>().ok())
            .filter(|&l| l != 0)
            .collect();
        if !lits.is_empty() {
            clauses.push(lits);
        }
    }
    (num_vars, clauses)
}

/// Test: Extension::check() returning AddClauses must not cause spurious UNSAT.
///
/// Loads the BV combined CNF + circuit CNF from the #8480 investigation.
/// First solves the base formula (SAT), then checks that solving with an
/// extension that adds the circuit on check() also returns SAT.
#[test]
fn test_extension_addclauses_no_spurious_unsat() {
    // Read the combined (base) and combined+circuit CNFs
    let base_cnf = match std::fs::read_to_string("/tmp/combined.cnf") {
        Ok(c) => c,
        Err(_) => {
            eprintln!("Skipping: /tmp/combined.cnf not found (run AY with AY_DEBUG_8480 first)");
            return;
        }
    };
    let circuit_cnf = match std::fs::read_to_string("/tmp/combined_with_circuit.cnf") {
        Ok(c) => c,
        Err(_) => {
            eprintln!("Skipping: /tmp/combined_with_circuit.cnf not found");
            return;
        }
    };

    let (base_vars, base_clauses) = parse_cnf(&base_cnf);
    let (circuit_vars, circuit_clauses) = parse_cnf(&circuit_cnf);

    // Verify base is SAT
    {
        let mut solver = Solver::new(base_vars);
        for clause in &base_clauses {
            let lits: Vec<Literal> = clause.iter().map(|&l| dimacs_to_literal(l)).collect();
            solver.add_clause(lits);
        }
        let result = solver.solve().into_inner();
        assert!(
            matches!(result, SatResult::Sat(_)),
            "Base formula must be SAT"
        );
    }

    // Verify combined+circuit is SAT
    {
        let mut solver = Solver::new(circuit_vars);
        for clause in &circuit_clauses {
            let lits: Vec<Literal> = clause.iter().map(|&l| dimacs_to_literal(l)).collect();
            solver.add_clause(lits);
        }
        let result = solver.solve().into_inner();
        assert!(
            matches!(result, SatResult::Sat(_)),
            "Combined+circuit formula must be SAT"
        );
    }

    // Now test: base formula + extension that adds circuit clauses on check()
    // This is the pattern that triggers #8480.
    {
        // Extract the "circuit-only" clauses (those in combined+circuit but not in base)
        let circuit_only: Vec<Vec<i32>> = circuit_clauses[base_clauses.len()..].to_vec();
        assert!(
            !circuit_only.is_empty(),
            "Circuit clauses must exist beyond base"
        );
        eprintln!(
            "Base: {} clauses, {} vars. Circuit-only: {} clauses. Total vars: {}",
            base_clauses.len(),
            base_vars,
            circuit_only.len(),
            circuit_vars
        );

        let circuit_lits: Vec<Vec<Literal>> = circuit_only
            .iter()
            .map(|clause| clause.iter().map(|&l| dimacs_to_literal(l)).collect())
            .collect();

        let mut ext = DelayedCircuitExtension {
            circuit_clauses: Mutex::new(Some(circuit_lits)),
            check_count: Mutex::new(0),
        };

        let mut solver = Solver::new(base_vars);
        solver.set_congruence_enabled(false);
        solver.set_condition_enabled(false);
        for clause in &base_clauses {
            let lits: Vec<Literal> = clause.iter().map(|&l| dimacs_to_literal(l)).collect();
            solver.add_clause(lits);
        }

        let result = solver.solve_with_extension(&mut ext).into_inner();

        assert!(
            matches!(result, SatResult::Sat(_)),
            "Extension adding circuit clauses must produce SAT (got UNSAT = #8480 bug)"
        );
    }
}

/// Minimal test: simple formula with Extension::check() adding one constraint.
///
/// x1 OR x2 (satisfiable)
/// Extension adds: x1 AND x2 (both must be true)
/// Combined: SAT (x1=true, x2=true)
#[test]
fn test_extension_addclauses_simple() {
    struct SimpleExt {
        added: bool,
    }
    impl Extension for SimpleExt {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::default()
        }
        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            if !self.added {
                self.added = true;
                // Add: x1 must be true AND x2 must be true
                let x1_pos = Literal::positive(Variable::new(0));
                let x2_pos = Literal::positive(Variable::new(1));
                return ExtCheckResult::AddClauses(vec![vec![x1_pos], vec![x2_pos]]);
            }
            ExtCheckResult::Sat
        }
        fn backtrack(&mut self, _new_level: u32) {}
    }

    let mut solver = Solver::new(2);
    // x1 OR x2
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    let mut ext = SimpleExt { added: false };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "Simple extension test must be SAT"
    );
}

/// Test: Extension adds clauses with NEW variables not in the original formula.
///
/// Original: x1 OR x2 (2 vars)
/// Extension adds: x3 <=> (x1 AND x2), i.e.:
///   -x3 OR x1
///   -x3 OR x2
///   x3 OR -x1 OR -x2
///   x3  (x3 must be true, forcing both x1 and x2 true)
/// Combined: SAT (x1=true, x2=true, x3=true)
#[test]
fn test_extension_addclauses_with_new_vars() {
    struct NewVarExt {
        added: bool,
    }
    impl Extension for NewVarExt {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::default()
        }
        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            if !self.added {
                self.added = true;
                let x1 = Variable::new(0);
                let x2 = Variable::new(1);
                let x3 = Variable::new(2); // NEW variable!
                return ExtCheckResult::AddClauses(vec![
                    vec![Literal::negative(x3), Literal::positive(x1)],
                    vec![Literal::negative(x3), Literal::positive(x2)],
                    vec![
                        Literal::positive(x3),
                        Literal::negative(x1),
                        Literal::negative(x2),
                    ],
                    vec![Literal::positive(x3)], // Force x3=true
                ]);
            }
            ExtCheckResult::Sat
        }
        fn backtrack(&mut self, _new_level: u32) {}
    }

    let mut solver = Solver::new(2);
    // x1 OR x2
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    let mut ext = NewVarExt { added: false };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "Extension with new vars must be SAT"
    );
}
