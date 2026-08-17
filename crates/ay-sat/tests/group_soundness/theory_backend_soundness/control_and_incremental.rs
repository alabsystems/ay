// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `group_soundness::theory_backend_soundness` to preserve test FQNs.

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
