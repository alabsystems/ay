// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `group_soundness::theory_backend_soundness` to preserve test FQNs.

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
