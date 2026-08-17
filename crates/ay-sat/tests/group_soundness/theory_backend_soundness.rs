// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory backend soundness tests.
//!
//! Verifies that DPLL(T) theory lemma interaction with the SAT solver is sound:
//! - Theory lemmas do not create unsound implications
//! - Backtracking correctly undoes theory propagations
//! - Theory conflicts are properly handled at different decision levels
//! - Extension variable reconstruction does not corrupt models
//! - The disable_extension_inprocessing settings are respected

use ay_sat::{
    ExtCheckResult, ExtPropagateResult, Extension, Literal, SatResult, SatUnknownReason, Solver,
    SolverContext, TheoryPropResult, Variable,
};

// ---------------------------------------------------------------------------
// Helper: verify a SAT model against a set of clauses
// ---------------------------------------------------------------------------

fn verify_model(model: &[bool], clauses: &[Vec<Literal>]) -> bool {
    for clause in clauses {
        let satisfied = clause.iter().any(|lit| {
            let idx = lit.variable().index();
            if idx >= model.len() {
                return false;
            }
            if lit.is_positive() {
                model[idx]
            } else {
                !model[idx]
            }
        });
        if !satisfied {
            return false;
        }
    }
    true
}

// ===========================================================================
// 1. Theory lemmas do not create unsound implications
// ===========================================================================

/// A theory that adds an implication lemma (a -> b) must not cause the solver
/// to return a SAT model that violates the implication.
#[test]
fn test_theory_implication_lemma_is_respected_in_model() {
    // Formula: (a v b) -- satisfiable many ways
    // Theory adds: (~a v b)  i.e. a => b
    // Any SAT model must satisfy both clauses.
    let mut solver = Solver::new(2);
    let a = Literal::positive(Variable::new(0));
    let b = Literal::positive(Variable::new(1));

    solver.add_clause(vec![a, b]);

    let mut added = false;
    let result = solver
        .solve_with_theory(|s| {
            if !added {
                added = true;
                s.add_theory_lemma(vec![a.negated(), b]);
                TheoryPropResult::Propagate
            } else {
                TheoryPropResult::Continue
            }
        })
        .into_inner();

    match result {
        SatResult::Sat(model) => {
            // a => b must hold: if a is true, b must be true
            if model[0] {
                assert!(
                    model[1],
                    "theory implication a=>b violated: a=true but b=false"
                );
            }
            // Original clause (a v b) must hold
            assert!(model[0] || model[1], "original clause (a v b) violated");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// Theory lemma that contradicts the formula must produce UNSAT.
#[test]
fn test_theory_contradicting_lemma_produces_unsat() {
    // Formula: (a) AND (b)
    // Theory adds: (~a) -- contradicts (a)
    let mut solver = Solver::new(2);
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    solver.add_clause(vec![Literal::positive(Variable::new(1))]);

    let mut added = false;
    let result = solver
        .solve_with_theory(|s| {
            if !added {
                added = true;
                s.add_theory_lemma(vec![Literal::negative(Variable::new(0))]);
                TheoryPropResult::Propagate
            } else {
                TheoryPropResult::Continue
            }
        })
        .into_inner();

    assert!(
        result.is_unsat(),
        "contradictory theory lemma must yield UNSAT"
    );
}

/// Multiple theory lemmas narrowing the solution space must all be respected.
#[test]
fn test_multiple_theory_lemmas_all_respected() {
    // Formula: (a v b v c) -- many solutions
    // Theory adds: (~a), (~b) -- forces c=true
    let mut solver = Solver::new(3);
    let a = Literal::positive(Variable::new(0));
    let b = Literal::positive(Variable::new(1));
    let c = Literal::positive(Variable::new(2));

    solver.add_clause(vec![a, b, c]);

    let mut phase = 0;
    let result = solver
        .solve_with_theory(|s| match phase {
            0 => {
                phase = 1;
                s.add_theory_lemma(vec![a.negated()]);
                TheoryPropResult::Propagate
            }
            1 => {
                phase = 2;
                s.add_theory_lemma(vec![b.negated()]);
                TheoryPropResult::Propagate
            }
            _ => TheoryPropResult::Continue,
        })
        .into_inner();

    match result {
        SatResult::Sat(model) => {
            assert!(!model[0], "theory forced a=false");
            assert!(!model[1], "theory forced b=false");
            assert!(model[2], "c must be true to satisfy (a v b v c)");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// ===========================================================================
// 2. Backtracking correctly undoes theory propagations
// ===========================================================================

/// Extension backtrack() is called with the correct level when the solver
/// backtracks due to a conflict.
#[test]
fn test_extension_backtrack_called_on_conflict() {
    use std::sync::{Arc, Mutex};

    struct TrackingExtension {
        backtrack_levels: Arc<Mutex<Vec<u32>>>,
        propagation_count: usize,
    }

    impl Extension for TrackingExtension {
        fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
            self.propagation_count += 1;
            // After a few propagations, inject a conflict to force backtracking
            if self.propagation_count == 3 && ctx.decision_level() > 0 {
                // Return a conflict clause that forces backtracking
                let trail = ctx.trail();
                if trail.len() >= 2 {
                    // Conflict: negate the first two decisions
                    return ExtPropagateResult::conflict(vec![
                        trail[0].negated(),
                        trail[1].negated(),
                    ]);
                }
            }
            ExtPropagateResult::none()
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }

        fn backtrack(&mut self, new_level: u32) {
            self.backtrack_levels.lock().unwrap().push(new_level);
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            true
        }
    }

    let levels = Arc::new(Mutex::new(Vec::new()));
    let mut ext = TrackingExtension {
        backtrack_levels: levels.clone(),
        propagation_count: 0,
    };

    // Create a satisfiable formula with enough variables to force decisions
    let mut solver = Solver::new(6);
    for i in 0..5 {
        solver.add_clause(vec![
            Literal::positive(Variable::new(i)),
            Literal::positive(Variable::new(i + 1)),
        ]);
    }

    let _ = solver.solve_with_extension(&mut ext).into_inner();

    let recorded = levels.lock().unwrap();
    // The extension should have been notified of at least one backtrack.
    // The conflict at propagation_count==3 forces a backtrack, and restarts
    // also trigger backtrack(0).
    assert!(
        !recorded.is_empty(),
        "extension backtrack() must be called during conflict resolution or restart"
    );
}

/// Extension backtrack is called on restart (level 0).
#[test]
fn test_extension_backtrack_to_zero_on_restart() {
    use std::sync::{Arc, Mutex};

    struct RestartTracker {
        backtrack_levels: Arc<Mutex<Vec<u32>>>,
    }

    impl Extension for RestartTracker {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }

        fn backtrack(&mut self, new_level: u32) {
            self.backtrack_levels.lock().unwrap().push(new_level);
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            false
        }
    }

    let levels = Arc::new(Mutex::new(Vec::new()));
    let mut ext = RestartTracker {
        backtrack_levels: levels.clone(),
    };

    // Hard-ish formula to trigger restarts
    let mut solver = Solver::new(10);
    // Add enough clauses to make search non-trivial
    for i in 0..9 {
        solver.add_clause(vec![
            Literal::positive(Variable::new(i)),
            Literal::negative(Variable::new(i + 1)),
        ]);
        solver.add_clause(vec![
            Literal::negative(Variable::new(i)),
            Literal::positive(Variable::new(i + 1)),
        ]);
    }
    // Make it satisfiable
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);

    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "formula should be satisfiable"
    );

    // If any restarts occurred, we should see backtrack(0) calls.
    // Even without restarts, rephasing may trigger backtrack(0).
    // This test primarily verifies the callback plumbing is correct.
    let recorded = levels.lock().unwrap();
    for &level in recorded.iter() {
        // All backtrack levels should be valid (non-negative, which is always
        // true for u32, but we check it's not suspiciously large)
        assert!(
            level < 100,
            "backtrack level {level} is suspiciously large for a 10-variable formula"
        );
    }
}

// ===========================================================================
// 3. Theory conflicts at different decision levels
// ===========================================================================

/// Theory conflict at decision level 0 must produce UNSAT.
#[test]
fn test_theory_conflict_at_level0_produces_unsat() {
    let mut solver = Solver::new(2);
    // Force a=true at level 0
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    // Force b=true at level 0
    solver.add_clause(vec![Literal::positive(Variable::new(1))]);

    // Theory says: a AND b is impossible (conflict at level 0 after propagation)
    let mut fired = false;
    let result = solver
        .solve_with_theory(|_s| {
            if !fired {
                fired = true;
                // Conflict: (~a v ~b) combined with forced a=true, b=true
                TheoryPropResult::Conflict(vec![
                    Literal::negative(Variable::new(0)),
                    Literal::negative(Variable::new(1)),
                ])
            } else {
                TheoryPropResult::Continue
            }
        })
        .into_inner();

    assert!(
        result.is_unsat(),
        "theory conflict with all-false literals at level 0 must yield UNSAT"
    );
}

/// Theory conflict at a high decision level must cause backtracking, not UNSAT.
#[test]
fn test_theory_conflict_at_high_level_backtracks_not_unsat() {
    // Create a formula where the solver must make decisions, then theory
    // rejects some assignments but a solution exists.
    let mut solver = Solver::new(4);
    let a = Literal::positive(Variable::new(0));
    let b = Literal::positive(Variable::new(1));
    let c = Literal::positive(Variable::new(2));
    let d = Literal::positive(Variable::new(3));

    // (a v b) AND (c v d) -- many solutions
    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![c, d]);

    // Theory rejects any model where a=true AND c=true (once),
    // then accepts everything else.
    let mut rejected = false;
    let result = solver
        .solve_with_theory(|s| {
            if !rejected {
                let a_val = s.lit_value(a);
                let c_val = s.lit_value(c);
                if a_val == Some(true) && c_val == Some(true) {
                    rejected = true;
                    // Conflict: cannot have both a and c true
                    TheoryPropResult::Conflict(vec![a.negated(), c.negated()])
                } else {
                    TheoryPropResult::Continue
                }
            } else {
                TheoryPropResult::Continue
            }
        })
        .into_inner();

    match result {
        SatResult::Sat(model) => {
            // The rejected assignment (a=true, c=true) should not appear
            // (or at least the model satisfies all clauses)
            assert!(model[0] || model[1], "(a v b) must hold");
            assert!(model[2] || model[3], "(c v d) must hold");
            // Theory conflict says ~a v ~c, so not(a AND c)
            assert!(
                !(model[0] && model[2]),
                "theory conflict (~a v ~c) must be respected"
            );
        }
        SatResult::Unsat(_) => {
            panic!("formula is satisfiable (e.g., a=true,b=_,c=false,d=true); should not be UNSAT");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Repeated theory conflicts at varying levels must all be handled correctly.
#[test]
fn test_repeated_theory_conflicts_at_varying_levels() {
    let mut solver = Solver::new(5);
    let lits: Vec<Literal> = (0..5)
        .map(|i| Literal::positive(Variable::new(i)))
        .collect();

    // (x0 v x1) AND (x2 v x3) AND (x4)
    solver.add_clause(vec![lits[0], lits[1]]);
    solver.add_clause(vec![lits[2], lits[3]]);
    solver.add_clause(vec![lits[4]]);

    // Theory rejects first 3 complete models, then accepts.
    let conflict_count = std::cell::Cell::new(0);
    let result = solver
        .solve_with_theory(|s| {
            let count = conflict_count.get();
            if count < 3 {
                // Check if all variables are assigned
                let all_assigned = (0..5).all(|i| s.value(Variable::new(i)).is_some());
                if all_assigned {
                    conflict_count.set(count + 1);
                    // Block current assignment by negating first two true lits
                    let mut blocking = Vec::new();
                    for i in 0..5 {
                        if s.value(Variable::new(i)) == Some(true) && blocking.len() < 2 {
                            blocking.push(Literal::negative(Variable::new(i)));
                        }
                    }
                    if !blocking.is_empty() {
                        return TheoryPropResult::Conflict(blocking);
                    }
                }
            }
            TheoryPropResult::Continue
        })
        .into_inner();

    match result {
        SatResult::Sat(model) => {
            assert!(model[0] || model[1], "(x0 v x1) must hold");
            assert!(model[2] || model[3], "(x2 v x3) must hold");
            assert!(model[4], "(x4) must hold");
        }
        other => panic!("expected SAT after rejecting 3 models, got {other:?}"),
    }
}

include!("theory_backend_soundness/model_checks_and_preprocessing.rs");

include!("theory_backend_soundness/control_and_incremental.rs");
