// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for formula component analysis (#8168).

use super::*;

/// Build a solver with two completely disconnected groups of clauses.
/// Group 1: vars 0-4, Group 2: vars 5-9.
#[test]
fn test_component_analysis_two_groups() {
    let mut solver = Solver::new(0);
    solver.set_decompose_enabled(true);
    let vars: Vec<Variable> = (0..10).map(|_| solver.new_var()).collect();

    // Group 1: chain 0-1-2-3-4
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[1]), Literal::positive(vars[2])]);
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::positive(vars[3])]);
    solver.add_clause(vec![Literal::positive(vars[3]), Literal::positive(vars[4])]);

    // Group 2: chain 5-6-7-8-9
    solver.add_clause(vec![Literal::positive(vars[5]), Literal::positive(vars[6])]);
    solver.add_clause(vec![Literal::positive(vars[6]), Literal::positive(vars[7])]);
    solver.add_clause(vec![Literal::positive(vars[7]), Literal::positive(vars[8])]);
    solver.add_clause(vec![Literal::positive(vars[8]), Literal::positive(vars[9])]);

    // Run solver (preprocessing will call analyze_components).
    let result = solver.solve();
    let result = result.into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "disconnected satisfiable formula should be SAT"
    );

    // Component analysis should have run during preprocessing.
    let stats = solver.component_stats();
    assert!(
        stats.runs > 0,
        "component analysis should have run at least once"
    );
}

/// Single fully-connected component: one contiguous group of variables.
#[test]
fn test_component_analysis_single_group() {
    let mut solver = Solver::new(0);
    solver.set_decompose_enabled(true);
    let vars: Vec<Variable> = (0..5).map(|_| solver.new_var()).collect();

    // All variables connected through a chain.
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[1]), Literal::positive(vars[2])]);
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::positive(vars[3])]);
    solver.add_clause(vec![Literal::positive(vars[3]), Literal::positive(vars[4])]);

    let result = solver.solve();
    let result = result.into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "connected satisfiable formula should be SAT"
    );

    let stats = solver.component_stats();
    assert!(
        stats.runs > 0,
        "component analysis should have run at least once"
    );
    // Fully connected formula: should detect 0 decomposable formulas.
    assert_eq!(
        stats.decomposable_found, 0,
        "single component formula should not be decomposable"
    );
}

/// Two large disconnected SAT components: decomposition should solve each
/// independently and combine models.
#[test]
fn test_decompose_solve_two_large_sat_components() {
    let mut solver = Solver::new(0);
    solver.set_decompose_enabled(true);
    // Component 1: 15 variables (0..14) in a satisfiable chain.
    let vars: Vec<Variable> = (0..30).map(|_| solver.new_var()).collect();

    for i in 0..14 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }
    // Component 2: 15 variables (15..29) in a satisfiable chain.
    for i in 15..29 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    let result = solver.solve();
    let result = result.into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "two disconnected SAT components should yield SAT"
    );

    let stats = solver.component_stats();
    // Component analysis should detect 2 components.
    assert!(
        stats.decomposable_found > 0,
        "should detect decomposable formula"
    );
}

/// One large SAT component and one large UNSAT component: formula is UNSAT.
#[test]
fn test_decompose_solve_one_unsat_component() {
    let mut solver = Solver::new(0);
    solver.set_decompose_enabled(true);
    let vars: Vec<Variable> = (0..30).map(|_| solver.new_var()).collect();

    // Component 1 (vars 0..14): satisfiable chain
    for i in 0..14 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    // Component 2 (vars 15..29): unsatisfiable
    // Force var 15 true AND false.
    solver.add_clause(vec![Literal::positive(vars[15])]);
    solver.add_clause(vec![Literal::negative(vars[15])]);
    // Add chain to make it >= 10 vars so it's "beneficial".
    for i in 15..29 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    let result = solver.solve();
    let result = result.into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "formula with one UNSAT component should be UNSAT"
    );
}

/// Verify combined model satisfies all original clauses from both components.
#[test]
fn test_decompose_solve_model_correctness() {
    let mut solver = Solver::new(0);
    solver.set_decompose_enabled(true);
    let vars: Vec<Variable> = (0..30).map(|_| solver.new_var()).collect();

    // Component 1: vars 0..14
    let mut clauses_1 = Vec::new();
    for i in 0..14 {
        let c = vec![Literal::positive(vars[i]), Literal::positive(vars[i + 1])];
        clauses_1.push(c.clone());
        solver.add_clause(c);
    }

    // Component 2: vars 15..29
    let mut clauses_2 = Vec::new();
    for i in 15..29 {
        let c = vec![Literal::positive(vars[i]), Literal::positive(vars[i + 1])];
        clauses_2.push(c.clone());
        solver.add_clause(c);
    }

    let result = solver.solve();
    let result = result.into_inner();
    match result {
        SatResult::Sat(model) => {
            // Verify all clauses are satisfied.
            for clause in clauses_1.iter().chain(clauses_2.iter()) {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    if vi < model.len() {
                        if lit.is_positive() {
                            model[vi]
                        } else {
                            !model[vi]
                        }
                    } else {
                        false
                    }
                });
                assert!(satisfied, "clause {clause:?} not satisfied by model");
            }
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// Regression test (husk adjudication #1, FALSE-UNSAT): a garbage-kept
/// ("husked") irredundant clause whose variable was BVE-eliminated must never
/// contribute a strengthened phantom clause to a decompose sub-solve.
///
/// Shape of the original bug: congruence forward subsumption husks an
/// irredundant clause C = [x0, x30] via mark_garbage_keep_data (no watch/occ
/// notification), BVE cannot see C (occ built with is_dead filters) and
/// eliminates x30. try_decompose_solve collected C through active_indices
/// (husks pass), remapped x30 to u32::MAX and silently dropped the literal,
/// injecting the phantom unit [x0] into the sub-solver. With component 1
/// forcing x0=false, the sub-solver reported UNSAT and the parent declared
/// a false UNSAT with no proof gate (this path requires proofs off).
#[test]
fn test_decompose_excludes_garbage_kept_husk() {
    let mut solver = Solver::new(0);
    solver.set_decompose_enabled(true);
    let vars: Vec<Variable> = (0..31).map(|_| solver.new_var()).collect();

    // Component 1 (vars 0..=14, 15 vars): forces x0 = false.
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::negative(vars[1])]);
    for i in 1..14 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    // Component 2 (vars 15..=29, 15 vars): satisfiable chain.
    for i in 15..29 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    // The husk: irredundant [x0, x30], logically deleted but data kept.
    // Added directly to the arena (mirroring how the live clause was already
    // present pre-husking; kept out of the original ledger because the clause
    // is semantically deleted from the formula).
    let husk_lits = [Literal::positive(vars[0]), Literal::positive(vars[30])];
    let husk_idx = solver.arena.add(&husk_lits, false);
    solver.arena.mark_garbage_keep_data(husk_idx);
    // x30 was "BVE-eliminated": removed from the active variable set.
    solver.var_lifecycle.mark_eliminated(30);

    let result = solver.try_decompose_solve();

    assert!(
        !matches!(result, Some(SatResult::Unsat(_))),
        "FALSE UNSAT: husked clause contributed a strengthened phantom to a \
         decompose sub-solve (husk adjudication #1 regression)"
    );
    assert!(
        matches!(result, Some(SatResult::Sat(_))),
        "expected decompose to solve both live components SAT, got {result:?}"
    );
}

/// Defense-in-depth companion to the husk fix: a LIVE clause containing an
/// unassigned variable that maps to no component (e.g. a removed variable
/// leaking into a live clause) must ABORT decomposition, not silently drop
/// the literal (which strengthens the clause into a phantom).
#[test]
fn test_decompose_aborts_on_component_less_unassigned_var() {
    let mut solver = Solver::new(0);
    solver.set_decompose_enabled(true);
    let vars: Vec<Variable> = (0..31).map(|_| solver.new_var()).collect();

    // Same two components as the husk regression test.
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::negative(vars[1])]);
    for i in 1..14 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }
    for i in 15..29 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    // LIVE (non-garbage) clause [x0, x30] with x30 marked removed and
    // unassigned: the invariant-violating state the abort defends against.
    let leak_lits = [Literal::positive(vars[0]), Literal::positive(vars[30])];
    let _leak_idx = solver.arena.add(&leak_lits, false);
    solver.var_lifecycle.mark_eliminated(30);

    let result = solver.try_decompose_solve();
    assert!(
        result.is_none(),
        "decomposition must abort (None) on an unassigned component-less \
         variable in a live clause instead of dropping the literal, got {result:?}"
    );
}
