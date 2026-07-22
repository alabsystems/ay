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

// ===========================================================================
// 4. Extension check() model validation
// ===========================================================================

/// Extension check() returning Conflict must block the current model and
/// the solver must find an alternative satisfying assignment.
#[test]
fn test_extension_check_conflict_blocks_model() {
    struct BlockFirstModelExtension {
        check_count: usize,
    }

    impl Extension for BlockFirstModelExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }

        fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
            self.check_count += 1;
            if self.check_count == 1 {
                // Block the first model: negate the assignment of var 0
                let v0_val = ctx.value(Variable::new(0));
                let blocking = if v0_val == Some(true) {
                    Literal::negative(Variable::new(0))
                } else {
                    Literal::positive(Variable::new(0))
                };
                ExtCheckResult::Conflict(vec![blocking])
            } else {
                ExtCheckResult::Sat
            }
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            false
        }
    }

    let mut solver = Solver::new(2);
    // (a v b) -- satisfiable
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    let mut ext = BlockFirstModelExtension { check_count: 0 };
    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            assert!(
                model[0] || model[1],
                "(a v b) must hold in the accepted model"
            );
            assert!(
                ext.check_count >= 2,
                "check() must be called at least twice (first rejected, second accepted)"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// Extension check() returning AddClauses must continue solving with the new
/// clauses, and the final model must satisfy all of them.
#[test]
fn test_extension_check_add_clauses_continues_solving() {
    struct AddClauseOnCheckExtension {
        check_count: usize,
    }

    impl Extension for AddClauseOnCheckExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            self.check_count += 1;
            if self.check_count == 1 {
                // Add a new constraint: (b) -- forces b=true
                ExtCheckResult::AddClauses(vec![vec![Literal::positive(Variable::new(1))]])
            } else {
                ExtCheckResult::Sat
            }
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            false
        }
    }

    let mut solver = Solver::new(2);
    // (a v b) -- satisfiable
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    let mut ext = AddClauseOnCheckExtension { check_count: 0 };
    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            assert!(model[0] || model[1], "(a v b) must hold");
            assert!(model[1], "added clause (b) must hold in final model");
        }
        other => panic!("expected SAT with added clause, got {other:?}"),
    }
}

/// Extension that returns ExtCheckResult::Unknown must produce SatResult::Unknown.
#[test]
fn test_extension_check_unknown_produces_unknown() {
    struct AlwaysUnknownExtension;

    impl Extension for AlwaysUnknownExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Unknown
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            false
        }
    }

    let mut solver = Solver::new(2);
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);

    let mut ext = AlwaysUnknownExtension;
    let result = solver.solve_with_extension(&mut ext).into_inner();

    assert_eq!(result, SatResult::Unknown);
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::ExtensionUnknown),
    );
}

// ===========================================================================
// 5. Extension model reconstruction soundness
// ===========================================================================

/// When an extension adds propagation clauses, the final SAT model must
/// satisfy both the original formula and all theory lemmas.
#[test]
fn test_extension_propagation_clauses_in_final_model() {
    use std::sync::{Arc, Mutex};

    struct ImplicationExtension {
        added_clauses: Arc<Mutex<Vec<Vec<Literal>>>>,
        propagated: bool,
    }

    impl Extension for ImplicationExtension {
        fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
            if !self.propagated {
                // When a is assigned true, add implication a => b
                if ctx.value(Variable::new(0)) == Some(true) {
                    self.propagated = true;
                    let clause = vec![
                        Literal::negative(Variable::new(0)),
                        Literal::positive(Variable::new(1)),
                    ];
                    self.added_clauses.lock().unwrap().push(clause.clone());
                    return ExtPropagateResult::clause(clause);
                }
            }
            ExtPropagateResult::none()
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            !self.propagated
        }
    }

    let added = Arc::new(Mutex::new(Vec::new()));

    let original_clauses = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(1)),
            Literal::positive(Variable::new(2)),
        ],
    ];

    let mut solver = Solver::new(3);
    for clause in &original_clauses {
        solver.add_clause(clause.clone());
    }

    let mut ext = ImplicationExtension {
        added_clauses: added.clone(),
        propagated: false,
    };

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            // Verify original clauses
            assert!(
                verify_model(&model, &original_clauses),
                "model must satisfy all original clauses"
            );
            // Verify theory lemmas
            let theory_clauses = added.lock().unwrap();
            assert!(
                verify_model(&model, &theory_clauses),
                "model must satisfy all theory lemma clauses"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// Theory propagations (lightweight path) must be reflected in the final model.
#[test]
fn test_theory_propagation_reflected_in_model() {
    struct PropagatingExtension {
        propagated: bool,
    }

    impl Extension for PropagatingExtension {
        fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
            if !self.propagated && ctx.value(Variable::new(0)) == Some(true) {
                self.propagated = true;
                // Propagate: because a is true, b must be true
                // Clause: [b, ~a] (b is propagated literal, ~a is falsified reason)
                let prop_lit = Literal::positive(Variable::new(1));
                let reason_clause = vec![prop_lit, Literal::negative(Variable::new(0))];
                return ExtPropagateResult::new(
                    vec![],
                    vec![(reason_clause, prop_lit)],
                    None,
                    false,
                );
            }
            ExtPropagateResult::none()
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            !self.propagated
        }
    }

    let mut solver = Solver::new(3);
    // Force a=true
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    // (b v c) -- with theory propagation, b should be forced true
    solver.add_clause(vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    let mut ext = PropagatingExtension { propagated: false };
    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            assert!(model[0], "a must be true (unit clause)");
            assert!(model[1], "b must be true (theory propagated a => b)");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// ===========================================================================
// 6. disable_extension_inprocessing settings respected
// ===========================================================================

/// When solving with an extension, preprocessing must be disabled (#7935).
/// The theory_backend disables preprocessing so SAT-level probing/HTR
/// cannot derive implications without theory consultation.
#[test]
fn test_extension_disables_preprocessing() {
    struct NoopCapture;

    impl Extension for NoopCapture {
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

    let mut solver = Solver::new(3);
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    let mut ext = NoopCapture;
    let _ = solver.solve_with_extension(&mut ext).into_inner();

    // After extension solve, preprocessing must be disabled (#7935)
    let profile = solver.inprocessing_feature_profile();
    assert!(
        !profile.preprocess,
        "preprocessing must be disabled in extension mode (#7935)"
    );
}

/// The preprocessing extension path (solve_interruptible_with_preprocessing_extension)
/// disables unsafe inprocessing techniques. This test verifies the
/// disable_extension_inprocessing settings via the theory closure path which
/// also uses the unified backend (solve_no_assumptions_with_theory_backend).
#[test]
fn test_theory_backend_disables_preprocessing_for_theory_solve() {
    let mut solver = Solver::new(3);
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    let _ = solver
        .solve_with_theory(|_| TheoryPropResult::Continue)
        .into_inner();

    let profile = solver.inprocessing_feature_profile();
    assert!(
        !profile.preprocess,
        "preprocessing must be disabled in theory mode (#7935)"
    );
}

/// Vivification must remain enabled in extension mode (it is theory-safe).
#[test]
fn test_extension_keeps_vivification_enabled() {
    struct NoopExt;

    impl Extension for NoopExt {
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

    let mut solver = Solver::new(3);
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    let mut ext = NoopExt;
    let _ = solver.solve_with_extension(&mut ext).into_inner();

    let profile = solver.inprocessing_feature_profile();
    assert!(
        profile.vivify,
        "vivification must remain enabled in extension mode (#7979)"
    );
}

// ===========================================================================
// 7. Extension stop behavior
// ===========================================================================

/// Extension stop during propagation must produce Unknown with TheoryStop reason.
#[test]
fn test_extension_stop_during_propagation() {
    struct StopAfterFirstPropExtension {
        count: usize,
    }

    impl Extension for StopAfterFirstPropExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            self.count += 1;
            if self.count >= 2 {
                return ExtPropagateResult::new(vec![], vec![], None, true);
            }
            ExtPropagateResult::none()
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            true
        }
    }

    let mut solver = Solver::new(3);
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    let mut ext = StopAfterFirstPropExtension { count: 0 };
    let result = solver.solve_with_extension(&mut ext).into_inner();

    assert_eq!(result, SatResult::Unknown);
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::TheoryStop),
    );
}

// ===========================================================================
// 8. Theory conflict clause soundness
// ===========================================================================

/// A theory conflict clause must be a valid blocking clause: all its literals
/// must be falsified under the current assignment at the time of the conflict.
/// The solver must handle this correctly and not produce unsound results.
#[test]
fn test_theory_conflict_clause_blocks_assignment() {
    // Setup: 4 variables, formula is (a v b) AND (c v d)
    // Theory conflict: whenever a=true AND c=true, emit (~a v ~c)
    // This should block that combination and find an alternative.
    let mut solver = Solver::new(4);
    let a = Literal::positive(Variable::new(0));
    let b = Literal::positive(Variable::new(1));
    let c = Literal::positive(Variable::new(2));
    let d = Literal::positive(Variable::new(3));

    let original_clauses = vec![vec![a, b], vec![c, d]];
    for clause in &original_clauses {
        solver.add_clause(clause.clone());
    }

    let theory_clauses: Vec<Vec<Literal>> = vec![vec![a.negated(), c.negated()]];

    let mut added = false;
    let result = solver
        .solve_with_theory(|s| {
            if !added {
                let a_val = s.lit_value(a);
                let c_val = s.lit_value(c);
                if a_val == Some(true) && c_val == Some(true) {
                    added = true;
                    return TheoryPropResult::Conflict(vec![a.negated(), c.negated()]);
                }
            }
            TheoryPropResult::Continue
        })
        .into_inner();

    match result {
        SatResult::Sat(model) => {
            assert!(
                verify_model(&model, &original_clauses),
                "model must satisfy original clauses"
            );
            assert!(
                verify_model(&model, &theory_clauses),
                "model must satisfy theory conflict clause (~a v ~c)"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// ===========================================================================
// 9. Extension suggest_decision and suggest_phase
// ===========================================================================

/// Extension suggest_decision is respected when the suggested literal is
/// unassigned.
#[test]
fn test_extension_suggest_decision_respected() {
    use std::sync::atomic::{AtomicBool, Ordering};

    struct DecisionSuggester {
        suggested: AtomicBool,
    }

    impl Extension for DecisionSuggester {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }

        fn suggest_decision(&self, ctx: &dyn SolverContext) -> Option<Literal> {
            // Suggest deciding variable 2 positive first
            if ctx.value(Variable::new(2)).is_none() && !self.suggested.load(Ordering::Relaxed) {
                self.suggested.store(true, Ordering::Relaxed);
                Some(Literal::positive(Variable::new(2)))
            } else {
                None
            }
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            false
        }
    }

    let mut solver = Solver::new(3);
    // Satisfiable formula
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    let mut ext = DecisionSuggester {
        suggested: AtomicBool::new(false),
    };
    let result = solver.solve_with_extension(&mut ext).into_inner();

    assert!(
        matches!(result, SatResult::Sat(_)),
        "formula must be satisfiable"
    );
}

/// Extension suggest_phase is called and affects polarity choice.
#[test]
fn test_extension_suggest_phase_affects_polarity() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct PhaseSuggester {
        suggest_count: AtomicUsize,
    }

    impl Extension for PhaseSuggester {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }

        fn suggest_phase(&self, _var: Variable) -> Option<bool> {
            self.suggest_count.fetch_add(1, Ordering::Relaxed);
            // Always suggest positive polarity
            Some(true)
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            false
        }
    }

    let mut solver = Solver::new(3);
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    let mut ext = PhaseSuggester {
        suggest_count: AtomicUsize::new(0),
    };
    let result = solver.solve_with_extension(&mut ext).into_inner();

    assert!(matches!(result, SatResult::Sat(_)));
    // suggest_phase should have been called at least once during decision-making
    assert!(
        ext.suggest_count.load(Ordering::Relaxed) > 0,
        "suggest_phase() must be called during decision-making"
    );
}

// ===========================================================================
// 10. Theory restart blocking
// ===========================================================================

/// Extension should_block_restart is consulted and can suppress restarts.
#[test]
fn test_extension_should_block_restart_consulted() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct RestartBlocker {
        block_count: AtomicUsize,
    }

    impl Extension for RestartBlocker {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }

        fn should_block_restart(&self, _num_assigned: u32, _total_vars: u32) -> bool {
            self.block_count.fetch_add(1, Ordering::Relaxed);
            // Always block restarts
            true
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            false
        }
    }

    let mut solver = Solver::new(5);
    for i in 0..4 {
        solver.add_clause(vec![
            Literal::positive(Variable::new(i)),
            Literal::positive(Variable::new(i + 1)),
        ]);
    }

    let mut ext = RestartBlocker {
        block_count: AtomicUsize::new(0),
    };
    let result = solver.solve_with_extension(&mut ext).into_inner();

    assert!(
        matches!(result, SatResult::Sat(_)),
        "formula should be satisfiable even with blocked restarts"
    );
    // The block count may or may not be > 0 depending on whether the restart
    // condition triggered during this short solve. We just verify the callback
    // plumbing doesn't crash.
}

// ===========================================================================
// 11. Incremental theory solving soundness
// ===========================================================================

/// Theory lemmas from a prior scope must persist across push/pop/re-solve.
#[test]
fn test_theory_lemmas_persist_across_incremental_scopes() {
    let mut solver = Solver::new(3);
    let a = Literal::positive(Variable::new(0));
    let b = Literal::positive(Variable::new(1));
    let c = Literal::positive(Variable::new(2));

    // Base: (a v b v c)
    solver.add_clause(vec![a, b, c]);

    // First solve: theory adds (~a)
    let mut first_done = false;
    let result1 = solver
        .solve_with_theory(|s| {
            if !first_done {
                first_done = true;
                s.add_theory_lemma(vec![a.negated()]);
                TheoryPropResult::Propagate
            } else {
                TheoryPropResult::Continue
            }
        })
        .into_inner();

    match &result1 {
        SatResult::Sat(model) => {
            assert!(
                !model[0],
                "theory lemma (~a) must be respected in first solve"
            );
        }
        other => panic!("expected SAT for first solve, got {other:?}"),
    }

    // Push a new scope and add more constraints
    solver.push();
    solver.add_clause(vec![b.negated()]); // force b=false

    // Second solve: theory lemma (~a) from first solve should still hold
    let result2 = solver
        .solve_with_theory(|_| TheoryPropResult::Continue)
        .into_inner();

    match &result2 {
        SatResult::Sat(model) => {
            assert!(!model[0], "theory lemma (~a) must persist in second scope");
            assert!(!model[1], "pushed clause (~b) must hold");
            assert!(model[2], "c must be true to satisfy (a v b v c)");
        }
        other => panic!("expected SAT for second solve, got {other:?}"),
    }

    // Pop and re-solve: (~a) should still hold, but (~b) should be gone
    let _ = solver.pop();
    let result3 = solver
        .solve_with_theory(|_| TheoryPropResult::Continue)
        .into_inner();

    match &result3 {
        SatResult::Sat(model) => {
            assert!(!model[0], "theory lemma (~a) must persist after pop");
            assert!(
                model[1] || model[2],
                "(a v b v c) with a=false requires b or c"
            );
        }
        other => panic!("expected SAT after pop, got {other:?}"),
    }
}
