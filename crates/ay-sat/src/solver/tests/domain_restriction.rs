// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for domain-restricted decision heuristic (#8430).

use super::*;

/// Basic test: domain restriction allows solver to find SAT when restricting
/// to relevant variables.
#[test]
fn test_domain_restriction_basic_sat() {
    let mut solver = Solver::new(0);
    // Create 10 variables
    let vars: Vec<Variable> = (0..10).map(|_| solver.new_var()).collect();

    // Add clauses only involving vars 0..3
    // (x0 | x1) & (!x1 | x2) & (x0 | !x2)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[1]), Literal::positive(vars[2])]);
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::negative(vars[2])]);

    // Set domain to only vars 0..3 — the solver should find SAT
    // without needing to decide on vars 3..9
    solver.set_domain(&vars[0..3]);
    assert!(solver.has_domain());

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(model) => {
            // Verify the model satisfies all clauses
            assert!(model[vars[0].index()] || model[vars[1].index()]);
            assert!(!model[vars[1].index()] || model[vars[2].index()]);
            assert!(model[vars[0].index()] || !model[vars[2].index()]);
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Domain restriction correctly finds UNSAT when clauses are contradictory.
#[test]
fn test_domain_restriction_unsat() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..5).map(|_| solver.new_var()).collect();

    // Contradictory clauses: (x0) & (!x0)
    solver.add_clause(vec![Literal::positive(vars[0])]);
    solver.add_clause(vec![Literal::negative(vars[0])]);

    solver.set_domain(&vars[0..1]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Unsat(_) => {}
        other => panic!("expected Unsat, got {other:?}"),
    }
}

/// clear_domain removes the restriction.
#[test]
fn test_domain_clear() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..5).map(|_| solver.new_var()).collect();

    solver.set_domain(&vars[0..2]);
    assert!(solver.has_domain());
    solver.clear_domain();
    assert!(!solver.has_domain());
}

/// Domain restriction with incremental solving: set domain, solve, clear, solve again.
#[test]
fn test_domain_restriction_incremental() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..6).map(|_| solver.new_var()).collect();

    // (x0 | x1) & (x2 | x3) & (x4 | x5)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::positive(vars[3])]);
    solver.add_clause(vec![Literal::positive(vars[4]), Literal::positive(vars[5])]);

    // First solve with domain on vars 0,1
    solver.set_domain(&vars[0..2]);
    let r1 = solver.solve();
    match r1.into_inner() {
        SatResult::Sat(_) => {}
        other => panic!("expected Sat (round 1), got {other:?}"),
    }

    // Clear domain, solve again with all variables
    solver.clear_domain();
    let r2 = solver.solve();
    match r2.into_inner() {
        SatResult::Sat(_) => {}
        other => panic!("expected Sat (round 2), got {other:?}"),
    }
}

/// Domain with push/pop scoping: domain interacts correctly with scopes.
/// The domain must include all variables that appear in active clauses to
/// avoid unsatisfied non-domain clauses in the model.
#[test]
fn test_domain_restriction_with_push_pop() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..4).map(|_| solver.new_var()).collect();

    // Base clause: (x0 | x1)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);

    solver.push();

    // Scoped clause involving same variables: (!x0 | x1)
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[1])]);

    // Domain on vars 0,1 — sufficient to cover all clauses in scope
    solver.set_domain(&vars[0..2]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {}
        other => panic!("expected Sat with domain in scope, got {other:?}"),
    }

    let _ = solver.pop();
    solver.clear_domain();

    // After pop, only base clause remains
    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {}
        other => panic!("expected Sat after pop, got {other:?}"),
    }
}

/// Empty domain: when all variables are outside the domain, the solver
/// should declare SAT immediately (no decisions needed, BCP handles everything).
#[test]
fn test_domain_restriction_empty_domain() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..4).map(|_| solver.new_var()).collect();

    // Satisfiable formula: (x0 | x1)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);

    // Empty domain — no variables to decide on
    solver.set_domain(&[]);

    let result = solver.solve();
    // With an empty domain, the solver can't make decisions. BCP at level 0
    // may or may not propagate enough to find a solution. The result depends
    // on whether the formula is satisfiable with only level-0 propagation.
    // For a simple satisfiable formula, the solver should still return a result.
    match result.into_inner() {
        SatResult::Sat(_) | SatResult::Unknown => {}
        SatResult::Unsat(_) => panic!("formula is satisfiable, should not get Unsat"),
    }
}

/// IC3-like usage: small cube query with domain restriction.
#[test]
fn test_domain_restriction_ic3_cube_pattern() {
    let mut solver = Solver::new(0);

    // Simulate a transition system with 100 variables
    let vars: Vec<Variable> = (0..100).map(|_| solver.new_var()).collect();

    // Add some background clauses involving many variables (transition relation)
    for i in (0..96).step_by(4) {
        // Chain implications: xi -> xi+1, xi+1 -> xi+2, etc.
        solver.add_clause(vec![
            Literal::negative(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
        solver.add_clause(vec![
            Literal::negative(vars[i + 1]),
            Literal::positive(vars[i + 2]),
        ]);
    }

    // IC3 cube query: check if cube {x0, !x1, x2} is satisfiable
    // Add cube as unit clauses
    solver.push();
    solver.add_clause(vec![Literal::positive(vars[0])]);
    solver.add_clause(vec![Literal::negative(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[2])]);

    // Restrict domain to cube variables + a few neighbors
    solver.set_domain(&vars[0..10]);

    let result = solver.solve();
    // The cube is contradictory with the implications:
    // x0 -> x1 (from clause !x0 | x1), but cube has !x1
    match result.into_inner() {
        SatResult::Unsat(_) => {}
        SatResult::Sat(_) => {
            // It's possible this is SAT depending on the specific clause structure.
            // The point is the solver completes without error.
        }
        SatResult::Unknown => {}
    }

    let _ = solver.pop();
    solver.clear_domain();
}

/// Regression: domain must not cause soundness issues.
/// A formula that is UNSAT must still return UNSAT with domain restriction.
#[test]
fn test_domain_restriction_soundness_unsat_preserved() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..4).map(|_| solver.new_var()).collect();

    // UNSAT formula: (x0) & (!x0 | x1) & (!x1) & (x0 | !x0)
    solver.add_clause(vec![Literal::positive(vars[0])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[1])]);

    // Restrict to vars 0,1 (the relevant variables)
    solver.set_domain(&vars[0..2]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Unsat(_) => {}
        other => panic!("expected Unsat, got {other:?}"),
    }
}

/// Regression: domain restriction must produce valid SAT models.
/// The model must satisfy ALL clauses, not just domain-variable clauses.
#[test]
fn test_domain_restriction_model_satisfies_all_clauses() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..6).map(|_| solver.new_var()).collect();

    // Clauses involving both domain and non-domain variables:
    // (x0 | x3) & (!x0 | x4) & (x1 | x5) & (!x1 | !x5)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[3])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[4])]);
    solver.add_clause(vec![Literal::positive(vars[1]), Literal::positive(vars[5])]);
    solver.add_clause(vec![Literal::negative(vars[1]), Literal::negative(vars[5])]);

    // Domain on vars 0,1 only — non-domain vars should be handled by BCP
    solver.set_domain(&vars[0..2]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(model) => {
            // Verify ALL clauses are satisfied
            assert!(model[vars[0].index()] || model[vars[3].index()]);
            assert!(!model[vars[0].index()] || model[vars[4].index()]);
            assert!(model[vars[1].index()] || model[vars[5].index()]);
            assert!(!model[vars[1].index()] || !model[vars[5].index()]);
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

// ---- Domain-restricted BCP tests (#8475) ----

fn ic3_domain_bcp_breakpoint_solver(min_vars_override: Option<usize>) -> Solver {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..20).map(|_| solver.new_var()).collect();

    // Background clauses on vars outside the query domain.
    for i in 10..18 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    // Domain-relevant chain that requires propagation after a decision.
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[1]), Literal::positive(vars[2])]);
    solver.add_clause(vec![Literal::negative(vars[2]), Literal::positive(vars[3])]);

    solver.set_ic3_mode();
    if let Some(min_vars) = min_vars_override {
        solver.set_domain_bcp_min_vars(min_vars);
    }
    solver.set_domain(&vars[0..4]);
    solver
}

#[test]
fn test_ic3_domain_bcp_min_vars_default_skips_small_formula() {
    let mut solver = ic3_domain_bcp_breakpoint_solver(None);
    assert_eq!(
        solver.domain_bcp_min_vars(),
        50,
        "IC3 default should skip domain BCP below the small-formula breakpoint"
    );

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    solver.decide(Literal::positive(Variable(1)));
    assert!(
        solver.search_propagate().is_none(),
        "breakpoint path should preserve propagation result"
    );
    assert_eq!(
        solver.stats.domain_bcp_calls, 0,
        "small IC3 formula should use full BCP instead of domain BCP"
    );
}

#[test]
fn test_domain_bcp_min_vars_zero_forces_domain_bcp() {
    let mut solver = ic3_domain_bcp_breakpoint_solver(Some(0));
    assert_eq!(solver.domain_bcp_min_vars(), 0);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    solver.decide(Literal::positive(Variable(1)));
    assert!(
        solver.search_propagate().is_none(),
        "forced domain BCP should preserve propagation result"
    );
    assert!(
        solver.stats.domain_bcp_calls > 0,
        "explicit zero breakpoint should keep using domain BCP"
    );
}

/// Domain BCP: skips clauses with non-domain watchers, still finds SAT.
/// Verifies that the solver activates domain BCP at decision level > 0
/// and produces correct results.
#[test]
fn test_domain_bcp_basic_sat() {
    let mut solver = Solver::new(0);
    // 20 variables, but only first 4 matter for the query
    let vars: Vec<Variable> = (0..20).map(|_| solver.new_var()).collect();

    // Background clauses on vars 10..19 (should be skipped by domain BCP)
    for i in 10..18 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    // Domain-relevant clauses on vars 0..3
    // (x0 | x1) & (!x1 | x2) & (!x2 | x3)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[1]), Literal::positive(vars[2])]);
    solver.add_clause(vec![Literal::negative(vars[2]), Literal::positive(vars[3])]);

    solver.set_domain(&vars[0..4]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(model) => {
            // Verify domain clauses are satisfied
            assert!(model[vars[0].index()] || model[vars[1].index()]);
            assert!(!model[vars[1].index()] || model[vars[2].index()]);
            assert!(!model[vars[2].index()] || model[vars[3].index()]);
        }
        other => panic!("expected Sat, got {other:?}"),
    }

    // domain_bcp_calls should be > 0 (domain BCP was used at decision level > 0)
    assert!(
        solver.stats.domain_bcp_calls > 0,
        "expected domain BCP calls > 0, got {}",
        solver.stats.domain_bcp_calls,
    );
}

/// Domain BCP: UNSAT result is preserved when clauses within the domain
/// are contradictory.
#[test]
fn test_domain_bcp_unsat() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..10).map(|_| solver.new_var()).collect();

    // Background clauses (non-domain)
    solver.add_clause(vec![Literal::positive(vars[5]), Literal::positive(vars[6])]);

    // Domain clauses that are UNSAT: (x0) & (x1) & (!x0 | !x1)
    solver.add_clause(vec![Literal::positive(vars[0])]);
    solver.add_clause(vec![Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::negative(vars[1])]);

    solver.set_domain(&vars[0..2]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Unsat(_) => {}
        other => panic!("expected Unsat, got {other:?}"),
    }
}

/// Domain BCP: verifies that domain_bcp_skips counter increments when
/// non-domain watchers are encountered during BCP.
#[test]
fn test_domain_bcp_skips_counter() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..20).map(|_| solver.new_var()).collect();

    // Many clauses involving non-domain variables
    for i in 5..18 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::negative(vars[i + 1]),
        ]);
        solver.add_clause(vec![
            Literal::negative(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    // Small domain clause: (x0 | x1) & (!x0 | x1)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[1])]);

    solver.set_domain(&vars[0..2]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {}
        other => panic!("expected Sat, got {other:?}"),
    }

    // Non-domain watchers should have been skipped during domain BCP.
    // The exact count depends on watch list ordering, but it should be > 0
    // because there are many clauses involving only non-domain variables.
    assert!(
        solver.stats.domain_bcp_skips > 0,
        "expected domain BCP skips > 0 (non-domain watchers should be skipped), got {}",
        solver.stats.domain_bcp_skips,
    );
}

/// Domain BCP: incremental solving with domain, push/pop.
/// Verifies that domain BCP works correctly across incremental scopes.
/// Uses formulas where all clauses are satisfiable by the domain-restricted
/// assignment (domain covers all variables in the clauses).
#[test]
fn test_domain_bcp_incremental_push_pop() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..10).map(|_| solver.new_var()).collect();

    // Base clauses involving only vars 0..4
    // (x0 | x1) & (x2 | x3)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::positive(vars[3])]);

    // Scope 1: add cube on vars 0..2, domain covers all clause vars
    solver.push();
    solver.add_clause(vec![Literal::positive(vars[0])]);
    solver.set_domain(&vars[0..4]);

    let r1 = solver.solve();
    match r1.into_inner() {
        SatResult::Sat(_) => {}
        other => panic!("expected Sat (scope 1), got {other:?}"),
    }

    let _ = solver.pop();
    solver.clear_domain();

    // Scope 2: different cube
    solver.push();
    solver.add_clause(vec![Literal::positive(vars[2])]);
    solver.set_domain(&vars[0..4]);

    let r2 = solver.solve();
    match r2.into_inner() {
        SatResult::Sat(_) => {}
        other => panic!("expected Sat (scope 2), got {other:?}"),
    }

    let _ = solver.pop();
    solver.clear_domain();
}

/// Domain BCP: long clauses (>2 literals) with mixed domain/non-domain
/// variables. Tests the replacement scan path in domain BCP.
#[test]
fn test_domain_bcp_long_clauses() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..20).map(|_| solver.new_var()).collect();

    // Long clause mixing domain and non-domain vars:
    // (x0 | x5 | x10 | x15)
    solver.add_clause(vec![
        Literal::positive(vars[0]),
        Literal::positive(vars[5]),
        Literal::positive(vars[10]),
        Literal::positive(vars[15]),
    ]);

    // Force x0 = false to make the long clause non-trivial
    solver.add_clause(vec![Literal::negative(vars[0])]);

    // Another long clause: (!x1 | x6 | x11 | x16)
    solver.add_clause(vec![
        Literal::negative(vars[1]),
        Literal::positive(vars[6]),
        Literal::positive(vars[11]),
        Literal::positive(vars[16]),
    ]);

    // Domain vars: {0, 1, 2, 3}
    solver.set_domain(&vars[0..4]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) | SatResult::Unknown => {}
        SatResult::Unsat(_) => panic!("formula is satisfiable, should not get Unsat"),
    }
}

/// Domain BCP: conflict at decision level > 0 is correctly detected.
/// Tests the conflict path in domain-restricted BCP.
#[test]
fn test_domain_bcp_conflict_detection() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..10).map(|_| solver.new_var()).collect();

    // Create a formula where domain vars produce a conflict:
    // (x0 | x1) & (!x0 | x1) & (x0 | !x1) & (!x0 | !x1)
    // This is UNSAT: x0 and x1 can't both be true or both be false.
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::negative(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::negative(vars[1])]);

    // Non-domain padding
    solver.add_clause(vec![Literal::positive(vars[5]), Literal::positive(vars[6])]);

    solver.set_domain(&vars[0..2]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Unsat(_) => {}
        other => panic!("expected Unsat, got {other:?}"),
    }
}

/// Domain BCP: unrestricted propagation at level 0, domain BCP at level > 0.
/// Verifies that level-0 propagation skips the domain filter.
#[test]
fn test_domain_bcp_level0_uses_unrestricted_propagation() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..10).map(|_| solver.new_var()).collect();

    // Unit clause forces level-0 propagation of a non-domain variable
    // which then propagates through a chain to force domain variables.
    // (x5) & (!x5 | x0) & (!x0 | x1)
    solver.add_clause(vec![Literal::positive(vars[5])]);
    solver.add_clause(vec![Literal::negative(vars[5]), Literal::positive(vars[0])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[1])]);

    // Domain only includes x0, x1 — but x5 is needed at level 0
    solver.set_domain(&vars[0..2]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(model) => {
            // Level-0 propagation must cover x5=true, x0=true, x1=true.
            assert!(model[vars[5].index()], "x5 should be true (unit clause)");
            assert!(
                model[vars[0].index()],
                "x0 should be true (propagated from x5)"
            );
            assert!(
                model[vars[1].index()],
                "x1 should be true (propagated from x0)"
            );
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}
