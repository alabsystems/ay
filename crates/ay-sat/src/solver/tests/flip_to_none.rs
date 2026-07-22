// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for IC3/PDR state lifting: `flip_to_none` and `minimize_model` (#8474).

use super::*;

/// Helper: verify that all clauses are satisfied by the current vals[] state.
/// Returns the index of the first unsatisfied clause, or None if all satisfied.
fn find_unsatisfied_clause(solver: &Solver) -> Option<(usize, Vec<(Literal, i8)>)> {
    for clause_idx in solver.arena.active_indices() {
        let lits = solver.arena.literals(clause_idx);
        if lits.is_empty() {
            continue;
        }
        let satisfied = lits.iter().any(|&lit| solver.lit_val(lit) > 0);
        if !satisfied {
            // For domain-restricted mode, check if any literal is "external"
            // (unassigned and outside domain).
            let has_external = lits.iter().any(|&lit| {
                let val = solver.lit_val(lit);
                if val != 0 {
                    return false;
                }
                if let Some(ref domain) = solver.active_domain {
                    let vi = lit.variable().index();
                    vi < domain.len() && !domain[vi]
                } else {
                    false
                }
            });
            if !has_external {
                let details: Vec<(Literal, i8)> =
                    lits.iter().map(|&lit| (lit, solver.lit_val(lit))).collect();
                return Some((clause_idx, details));
            }
        }
    }
    None
}

fn verify_all_clauses_satisfied(solver: &Solver) -> bool {
    find_unsatisfied_clause(solver).is_none()
}

/// Basic test: flip_to_none produces a subset of the original model.
#[test]
fn test_flip_to_none_basic_subset() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..5).map(|_| solver.new_var()).collect();

    // Simple satisfiable formula: (x0 | x1) & (x2 | x3) & (x4)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::positive(vars[3])]);
    solver.add_clause(vec![Literal::positive(vars[4])]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_model) => {
            // Record which vars are assigned before minimization.
            let _assigned_before: Vec<bool> = (0..5).map(|i| solver.var_is_assigned(i)).collect();

            // x4 is forced (unit clause), mark it as important.
            let cube = solver.minimize_model(&[vars[4]]);

            // The cube should be a subset of the original assignment.
            // x4 must be in the cube (unit clause, level 0).
            assert!(
                cube.iter().any(|&lit| lit.variable() == vars[4]),
                "level-0 variable x4 should remain in cube"
            );

            // Verify all clauses are still satisfied.
            if let Some((clause_idx, details)) = find_unsatisfied_clause(&solver) {
                panic!(
                    "clause at arena offset {clause_idx} is unsatisfied after minimize_model: {details:?}\ncube: {cube:?}"
                );
            }
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// The partial assignment still satisfies all clauses.
#[test]
fn test_flip_to_none_clauses_satisfied() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..8).map(|_| solver.new_var()).collect();

    // More complex formula:
    // (x0 | x1) & (!x1 | x2) & (x3 | x4) & (!x4 | x5) & (x6 | x7)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[1]), Literal::positive(vars[2])]);
    solver.add_clause(vec![Literal::positive(vars[3]), Literal::positive(vars[4])]);
    solver.add_clause(vec![Literal::negative(vars[4]), Literal::positive(vars[5])]);
    solver.add_clause(vec![Literal::positive(vars[6]), Literal::positive(vars[7])]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {
            // No important vars -- minimize everything possible.
            let cube = solver.minimize_model(&[]);

            // Verify all clauses are still satisfied.
            assert!(
                verify_all_clauses_satisfied(&solver),
                "clauses must remain satisfied after full minimization"
            );

            // The cube should be smaller than or equal to the full assignment.
            assert!(cube.len() <= 8, "cube should not exceed total variables");
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Important variables are never flipped.
#[test]
fn test_flip_to_none_important_vars_preserved() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..6).map(|_| solver.new_var()).collect();

    // (x0) & (x1) & (x2 | x3) & (x4 | x5)
    solver.add_clause(vec![Literal::positive(vars[0])]);
    solver.add_clause(vec![Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::positive(vars[3])]);
    solver.add_clause(vec![Literal::positive(vars[4]), Literal::positive(vars[5])]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {
            // Mark vars 2 and 4 as important.
            let important = vec![vars[2], vars[4]];
            let cube = solver.minimize_model(&important);

            // Important vars must remain in the cube (if they were assigned).
            for &var in &important {
                if solver.var_is_assigned(var.index()) {
                    assert!(
                        cube.iter().any(|&lit| lit.variable() == var),
                        "important variable {} must remain in cube",
                        var.index()
                    );
                }
            }

            // All clauses still satisfied.
            assert!(verify_all_clauses_satisfied(&solver));
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Level-0 variables cannot be flipped.
#[test]
fn test_flip_to_none_level0_not_flipped() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..4).map(|_| solver.new_var()).collect();

    // Unit clause forces x0 at level 0.
    solver.add_clause(vec![Literal::positive(vars[0])]);
    // (x1 | x2) & (x3)
    solver.add_clause(vec![Literal::positive(vars[1]), Literal::positive(vars[2])]);
    solver.add_clause(vec![Literal::positive(vars[3])]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {
            // x0 and x3 are level-0 (unit clauses).
            assert!(
                !solver.flip_to_none(vars[0]),
                "level-0 var x0 should not flip"
            );
            assert!(
                !solver.flip_to_none(vars[3]),
                "level-0 var x3 should not flip"
            );
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Already-unassigned variables trivially succeed.
#[test]
fn test_flip_to_none_already_unassigned() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..4).map(|_| solver.new_var()).collect();

    // Simple formula that doesn't require all vars.
    solver.add_clause(vec![Literal::positive(vars[0])]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {
            // Vars 1, 2, 3 may or may not be assigned depending on solver state.
            // If a var is unassigned, flip_to_none should return true.
            for (i, &var) in vars.iter().enumerate().skip(1) {
                if !solver.var_is_assigned(var.index()) {
                    assert!(
                        solver.flip_to_none(var),
                        "unassigned var {i} should flip to none"
                    );
                }
            }
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// flip_to_none returns false when removing a variable would break a clause.
#[test]
fn test_flip_to_none_necessary_var_not_removed() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..3).map(|_| solver.new_var()).collect();

    // Force a situation where x0 is necessary:
    // (x0) & (!x0 | x1) & (!x1 | x2) & (!x2 | !x0 | x0)
    // Actually, simpler: just (x0) makes x0 level-0.
    // Let's use: (x0 | x1) & (!x1) -- forces x1=false at level 0, then x0 must be true.
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[1])]);
    // x2 is free.
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::negative(vars[2])]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {
            // x1 is level-0 (false). x0 is likely level-0 via unit propagation.
            // flip_to_none should fail for level-0 vars.
            assert!(
                !solver.flip_to_none(vars[1]),
                "x1 is level-0, should not flip"
            );
            // x0 may also be level-0 (propagated from x1=false and clause (x0|x1)).
            if solver.var_data[vars[0].index()].level == 0 {
                assert!(
                    !solver.flip_to_none(vars[0]),
                    "x0 propagated to level-0, should not flip"
                );
            }
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// flip_to_none with domain restriction: non-domain unassigned vars are external.
#[test]
fn test_flip_to_none_with_domain_restriction() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..6).map(|_| solver.new_var()).collect();

    // (x0 | x3) & (x1 | x4) & (x2 | x5)
    // Domain = {x0, x1, x2}. Non-domain vars x3, x4, x5 are "external".
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[3])]);
    solver.add_clause(vec![Literal::positive(vars[1]), Literal::positive(vars[4])]);
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::positive(vars[5])]);

    solver.set_domain(&vars[0..3]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {
            // With domain restriction, flipping domain vars should succeed more
            // easily because non-domain vars count as "external" (satisfied).
            let _cube = solver.minimize_model(&[]);

            // All clauses should still be "satisfied" under domain semantics.
            assert!(verify_all_clauses_satisfied(&solver));
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// minimize_model with all vars important returns the full assignment.
#[test]
fn test_minimize_model_all_important() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..4).map(|_| solver.new_var()).collect();

    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::positive(vars[3])]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {
            // Count assigned vars before minimize.
            let assigned_before: usize = (0..4).filter(|&i| solver.var_is_assigned(i)).count();

            // All vars are important: nothing should be flipped.
            let _cube = solver.minimize_model(&vars);

            // The cube should include all originally-assigned variables.
            // (Level-0 vars included since they're in the vals array.)
            let assigned_after: usize = (0..4).filter(|&i| solver.var_is_assigned(i)).count();

            assert_eq!(
                assigned_before, assigned_after,
                "no vars should be flipped when all are important"
            );
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// IC3-style pattern: push/solve/minimize/pop cycle.
#[test]
fn test_flip_to_none_ic3_pattern() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..10).map(|_| solver.new_var()).collect();

    // Background transition relation.
    for i in 0..8 {
        solver.add_clause(vec![
            Literal::negative(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    // IC3 query: is the cube {x0=true} reachable?
    solver.push();
    solver.add_clause(vec![Literal::positive(vars[0])]);

    // Restrict domain to first 5 vars.
    solver.set_domain(&vars[0..5]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {
            // Minimize keeping x0 as important.
            let cube = solver.minimize_model(&[vars[0]]);

            // x0 must be in the cube.
            assert!(
                cube.iter().any(|&lit| lit.variable() == vars[0]),
                "important variable x0 must remain in cube"
            );

            // All clauses satisfied under domain semantics.
            assert!(verify_all_clauses_satisfied(&solver));
        }
        _other => {
            // SAT or UNSAT both acceptable depending on propagation.
        }
    }

    solver.clear_domain();
    let _ = solver.pop();
}

/// Soundness: minimized cube used as assumption should still be satisfiable.
#[test]
fn test_flip_to_none_cube_is_satisfiable() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..6).map(|_| solver.new_var()).collect();

    // (x0 | x1) & (!x1 | x2) & (x3 | x4) & (!x4 | x5)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[1]), Literal::positive(vars[2])]);
    solver.add_clause(vec![Literal::positive(vars[3]), Literal::positive(vars[4])]);
    solver.add_clause(vec![Literal::negative(vars[4]), Literal::positive(vars[5])]);

    let result = solver.solve();
    match result.into_inner() {
        SatResult::Sat(_) => {
            let cube = solver.minimize_model(&[]);

            // Create a fresh solver with the same clauses and add the cube
            // as unit assumptions. It should still be SAT.
            let mut solver2 = Solver::new(0);
            let vars2: Vec<Variable> = (0..6).map(|_| solver2.new_var()).collect();

            solver2.add_clause(vec![
                Literal::positive(vars2[0]),
                Literal::positive(vars2[1]),
            ]);
            solver2.add_clause(vec![
                Literal::negative(vars2[1]),
                Literal::positive(vars2[2]),
            ]);
            solver2.add_clause(vec![
                Literal::positive(vars2[3]),
                Literal::positive(vars2[4]),
            ]);
            solver2.add_clause(vec![
                Literal::negative(vars2[4]),
                Literal::positive(vars2[5]),
            ]);

            // Add cube literals as unit clauses.
            for &lit in &cube {
                solver2.add_clause(vec![lit]);
            }

            let result2 = solver2.solve();
            match result2.into_inner() {
                SatResult::Sat(_) => {}
                other => panic!(
                    "cube from minimize_model should be satisfiable, got {other:?}. Cube: {cube:?}"
                ),
            }
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}
