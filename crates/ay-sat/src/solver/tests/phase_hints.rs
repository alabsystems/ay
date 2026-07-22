// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for per-variable phase hint API (`set_phase`, `clear_phase`, `clear_phases`).
//!
//! Part of #8212: Per-variable phase saving API for IC3.
//!
//! Test design: we use real constraints (e.g., `(x0 OR x1)`) rather than
//! tautological clauses `(x0 OR !x0)` because tautological clauses are
//! simplified during preprocessing and variables may never reach the decision
//! phase where phase hints are applied. With `(x0 OR x1)`, hinting x0=false
//! forces x1=true by BCP, giving deterministic verification.

use super::*;

/// Verify that `set_phase` hints guide decisions when the formula allows choice.
///
/// Uses (x0 OR x1) AND (x2 OR x3). Hinting x0=true and x2=true should cause
/// the solver to pick those polarities, satisfying both clauses directly.
#[test]
fn test_set_phase_positive_hint_affects_model() {
    let mut solver = Solver::new(4);
    // (x0 OR x1)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    // (x2 OR x3)
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ]);

    // Hint all variables: x0=true, x1=false, x2=true, x3=false
    solver.set_phase(Variable(0), true);
    solver.set_phase(Variable(1), false);
    solver.set_phase(Variable(2), true);
    solver.set_phase(Variable(3), false);

    let result = solver.solve_with_assumptions(&[]).into_inner();
    match result {
        AssumeResult::Sat(model) => {
            // x0 hinted true satisfies clause 1 directly.
            assert!(model[0], "var 0 should be positive (phase hint = true)");
            // x2 hinted true satisfies clause 2 directly.
            assert!(model[2], "var 2 should be positive (phase hint = true)");
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

/// Verify that `clear_phase` removes the forced hint, reverting to default.
///
/// Strategy: hint x0=false, then clear it. After clearing, x0 defaults to
/// positive, satisfying (x0 OR x1) directly. Control: x2 keeps its hint.
#[test]
fn test_clear_phase_removes_hint() {
    let mut solver = Solver::new(4);
    // (x0 OR x1)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    // (x2 OR x3)
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ]);

    // Set hint to negative, then clear it
    solver.set_phase(Variable(0), false);
    solver.clear_phase(Variable(0));
    // x2 stays hinted true as a control
    solver.set_phase(Variable(2), true);

    let result = solver.solve_with_assumptions(&[]).into_inner();
    match result {
        AssumeResult::Sat(model) => {
            // After clearing x0's hint, default phase (positive) is used.
            assert!(
                model[0],
                "var 0 should be positive after clear_phase (default)"
            );
            // Control: x2 hint was not cleared
            assert!(model[2], "var 2 should follow its phase hint (positive)");
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

/// Verify that `clear_phases` resets all hints, reverting to defaults.
///
/// Strategy: hint all variables negative, then clear_phases(). After clearing,
/// defaults (positive) apply, so x0=true and x2=true satisfy both clauses.
#[test]
fn test_clear_phases_resets_all() {
    let mut solver = Solver::new(4);
    // (x0 OR x1)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    // (x2 OR x3)
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ]);

    solver.set_phase(Variable(0), false);
    solver.set_phase(Variable(1), false);
    solver.set_phase(Variable(2), false);
    solver.set_phase(Variable(3), false);
    solver.clear_phases();

    // After clearing all, defaults should be used (positive).
    let result = solver.solve_with_assumptions(&[]).into_inner();
    match result {
        AssumeResult::Sat(model) => {
            assert!(model[0], "var 0 should be positive after clear_phases");
            assert!(model[2], "var 2 should be positive after clear_phases");
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

/// Verify that phase hints persist across multiple `solve_with_assumptions` calls.
#[test]
fn test_phase_hints_persist_across_solves() {
    let mut solver = Solver::new(4);
    // (x0 OR x1) — satisfiable with x0=true or x1=true
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    // (x2 OR x3)
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ]);

    // Set phase hints: x0=false, x1=true, x2=false, x3=true
    solver.set_phase(Variable(0), false);
    solver.set_phase(Variable(1), true);
    solver.set_phase(Variable(2), false);
    solver.set_phase(Variable(3), true);

    // First solve
    let r1 = solver.solve_with_assumptions(&[]).into_inner();
    match r1 {
        AssumeResult::Sat(model) => {
            // x1 should be true (hinted true, and x0 hinted false)
            assert!(model[1], "x1 should be true (first solve, hint=true)");
            assert!(model[3], "x3 should be true (first solve, hint=true)");
        }
        other => panic!("Expected SAT on first solve, got {other:?}"),
    }

    // Second solve — hints should still be active
    let r2 = solver.solve_with_assumptions(&[]).into_inner();
    match r2 {
        AssumeResult::Sat(model) => {
            assert!(model[1], "x1 should be true (second solve, hint persists)");
            assert!(model[3], "x3 should be true (second solve, hint persists)");
        }
        other => panic!("Expected SAT on second solve, got {other:?}"),
    }
}

/// Verify that `set_phase` panics on out-of-bounds variable.
#[test]
#[should_panic(expected = "set_phase: variable out of bounds")]
fn test_set_phase_oob_panics() {
    let mut solver = Solver::new(2);
    solver.set_phase(Variable(5), true);
}

/// Verify that `clear_phase` panics on out-of-bounds variable.
#[test]
#[should_panic(expected = "clear_phase: variable out of bounds")]
fn test_clear_phase_oob_panics() {
    let mut solver = Solver::new(2);
    solver.clear_phase(Variable(5));
}

/// Verify that phase hints work with dynamically added variables via `new_var`.
#[test]
fn test_phase_hints_with_new_var() {
    let mut solver = Solver::new(2);
    let v2 = solver.new_var();
    let v3 = solver.new_var();

    // (x0 OR v2) AND (x1 OR v3)
    solver.add_clause(vec![Literal::positive(Variable(0)), Literal::positive(v2)]);
    solver.add_clause(vec![Literal::positive(Variable(1)), Literal::positive(v3)]);

    // Hint: x0=false forces v2=true; v3 hinted negative forces x1=true
    solver.set_phase(Variable(0), false);
    solver.set_phase(v2, true);
    solver.set_phase(v3, false);
    solver.set_phase(Variable(1), true);

    let result = solver.solve_with_assumptions(&[]).into_inner();
    match result {
        AssumeResult::Sat(model) => {
            assert!(
                model[v2.index()],
                "dynamically-added var should follow phase hint (positive)"
            );
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

/// Verify that phase hints work with `ensure_num_vars`.
#[test]
fn test_phase_hints_with_ensure_num_vars() {
    let mut solver = Solver::new(2);
    solver.ensure_num_vars(6);

    // (x0 OR x4) AND (x1 OR x5)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(5)),
    ]);

    // Hint: x0=false forces x4=true by BCP
    solver.set_phase(Variable(0), false);
    solver.set_phase(Variable(4), true);
    solver.set_phase(Variable(1), false);
    solver.set_phase(Variable(5), true);

    let result = solver.solve_with_assumptions(&[]).into_inner();
    match result {
        AssumeResult::Sat(model) => {
            assert!(
                model[4],
                "var 4 should follow phase hint after ensure_num_vars"
            );
            assert!(
                model[5],
                "var 5 should follow phase hint after ensure_num_vars"
            );
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}
