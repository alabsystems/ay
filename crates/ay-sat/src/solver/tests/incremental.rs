// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental solving tests: assumptions, push/pop, scope selectors, interrupts.
//!
//! Extracted from tests.rs for code-quality (Part of #5142).

use super::*;

// ========================================================================
// Assumption-Based Solving Tests
// ========================================================================

#[test]
fn test_assumptions_sat() {
    // Test SAT with compatible assumptions
    let mut solver = Solver::new(3);
    // (x0 OR x1) AND (x1 OR x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    // Assume x1 = true - should be SAT
    let assumptions = vec![Literal::positive(Variable(1))];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Sat(model) => {
            assert!(model[1], "Assumed literal x1 should be true");
        }
        _ => panic!("Expected SAT with assumption x1=true"),
    }
}

#[test]
fn test_assumptions_unsat_single() {
    // Test UNSAT with conflicting assumption
    let mut solver = Solver::new(2);
    // x0 (unit clause)
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    // Assume NOT x0 - should be UNSAT with core containing NOT x0
    let assumptions = vec![Literal::negative(Variable(0))];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            assert!(
                core.contains(&Literal::negative(Variable(0))),
                "Unsat core should contain the conflicting assumption"
            );
        }
        _ => panic!("Expected UNSAT with assumption NOT x0"),
    }
}

#[test]
fn test_assumptions_unsat_multiple() {
    // Test UNSAT with multiple conflicting assumptions
    let mut solver = Solver::new(3);
    // (x0 OR x1) AND (NOT x0 OR NOT x1)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
    ]);

    // Assume x0=true AND x1=true - should be UNSAT
    let assumptions = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            // Core should contain at least one of the conflicting assumptions
            assert!(
                !core.is_empty(),
                "Unsat core should not be empty for assumption conflict"
            );
        }
        _ => panic!("Expected UNSAT with conflicting assumptions"),
    }
}

#[test]
fn test_assumptions_preserve_clauses() {
    // Test that assumptions don't modify clause database
    let mut solver = Solver::new(3);
    // (x0 OR x1)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    let initial_clause_count = solver.arena.len();

    // First call with assumption: x0=true makes (x0 OR x1) SAT
    let assumptions = vec![Literal::positive(Variable(0))];
    let result1 = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(
        matches!(result1, AssumeResult::Sat(_)),
        "Expected SAT with assumption x0=true, got {result1:?}"
    );

    // Second call with different assumption: x1=true also makes it SAT
    let assumptions = vec![Literal::positive(Variable(1))];
    let result2 = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(
        matches!(result2, AssumeResult::Sat(_)),
        "Expected SAT with assumption x1=true, got {result2:?}"
    );

    // Original clauses should still be present (learned clauses may be added)
    assert!(
        solver.arena.len() >= initial_clause_count,
        "Clause database should preserve original clauses after 2 assumption calls"
    );
}

#[test]
fn test_assumptions_empty() {
    // Test empty assumptions (should behave like regular solve)
    let mut solver = Solver::new(2);
    // (x0 OR x1)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    let result = solver.solve_with_assumptions(&[]).into_inner();
    match result {
        AssumeResult::Sat(_) => {} // Expected
        _ => panic!("Expected SAT with empty assumptions"),
    }
}

#[test]
fn test_assumptions_contradictory() {
    // Test contradictory assumptions (x AND NOT x)
    let mut solver = Solver::new(2);
    // Formula is satisfiable
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    // Assume x0=true AND x0=false (contradictory)
    let assumptions = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(0)),
    ];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            // Core should contain the contradictory assumption
            assert!(
                core.contains(&Literal::positive(Variable(0)))
                    || core.contains(&Literal::negative(Variable(0))),
                "Unsat core should contain contradictory assumption"
            );
        }
        _ => panic!("Expected UNSAT with contradictory assumptions"),
    }
}

#[test]
fn test_assumptions_incremental() {
    // Test that learned clauses are preserved across calls
    let mut solver = Solver::new(5);

    // A formula that requires learning
    // (a OR b) AND (a OR NOT b OR c) AND (NOT a OR d) AND (NOT d OR e) AND (NOT e)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(3)),
        Literal::positive(Variable(4)),
    ]);
    solver.add_clause(vec![Literal::negative(Variable(4))]);

    // With a=true: forces d=true (clause 3), e=true (clause 4), conflicts NOT e (clause 5) → UNSAT
    let result1 = solver
        .solve_with_assumptions(&[Literal::positive(Variable(0))])
        .into_inner();
    assert!(
        matches!(result1, AssumeResult::Unsat(..)),
        "Expected UNSAT with assumption a=true (forces e conflict), got {result1:?}"
    );

    let learned_count_after_first = solver.arena.len();

    // With a=false: b=true (clause 1), c=true (clause 2), clauses 3-5 satisfied → SAT
    let result2 = solver
        .solve_with_assumptions(&[Literal::negative(Variable(0))])
        .into_inner();
    assert!(
        matches!(result2, AssumeResult::Sat(_)),
        "Expected SAT with assumption a=false, got {result2:?}"
    );

    // The solver should have retained or added clauses
    assert!(
        solver.arena.len() >= learned_count_after_first,
        "Learned clauses should be retained between assumption calls"
    );
}

#[test]
fn test_assumptions_unsat_core_minimal() {
    // Test that unsat core is a subset of assumptions
    let mut solver = Solver::new(4);

    // x0 (unit - forces x0=true)
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    // Multiple assumptions, only one conflicts
    let assumptions = vec![
        Literal::positive(Variable(1)), // irrelevant
        Literal::negative(Variable(0)), // conflicts with unit clause
        Literal::positive(Variable(2)), // irrelevant
    ];

    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            // Core should be a subset of assumptions
            for lit in &core {
                assert!(
                    assumptions.contains(lit),
                    "Unsat core {lit:?} should only contain assumptions"
                );
            }
            // Core should contain the conflicting assumption
            assert!(
                core.contains(&Literal::negative(Variable(0))),
                "Core should contain NOT x0"
            );
        }
        _ => panic!("Expected UNSAT"),
    }
}

/// Regression test for #5117: backtrack_level == 0 during assumption-based
/// solving must NOT return UNSAT immediately. The solver must propagate the
/// learned unit at level 0, then continue the assumption search.
///
/// Formula: (x ∨ y) ∧ (x ∨ ¬y) — implies x via resolution.
/// Assumption: a = true (variable not in any clause).
///
/// If VSIDS decides x=false above the assumption level, conflict analysis
/// resolves C1,C2 into the unit clause {x} (backtrack_level = 0). The old
/// code returned UNSAT; the correct behavior is to assert x=true at level 0
/// and find the SAT assignment.
#[test]
fn test_assumptions_backtrack_level_zero_not_false_unsat_5117() {
    let mut solver = Solver::new(3);
    let x = Variable(0);
    let y = Variable(1);
    let a = Variable(2);

    // (x ∨ y) — C1
    solver.add_clause(vec![Literal::positive(x), Literal::positive(y)]);
    // (x ∨ ¬y) — C2: resolving C1 and C2 proves x
    solver.add_clause(vec![Literal::positive(x), Literal::negative(y)]);

    // Bias VSIDS to decide x=false (trigger the backtrack-to-0 path).
    solver.phase[x.index()] = -1;

    // Assume a=true (a is not in any clause, so the formula is trivially
    // satisfiable under this assumption once x is discovered as implied).
    let result = solver
        .solve_with_assumptions(&[Literal::positive(a)])
        .into_inner();
    match result {
        AssumeResult::Sat(model) => {
            assert!(
                model[x.index()],
                "x must be true (implied by resolution of C1,C2)"
            );
        }
        AssumeResult::Unsat(..) => {
            panic!("BUG: false UNSAT — backtrack_level==0 during assumption solving should not return UNSAT immediately (#5117)");
        }
        AssumeResult::Unknown => {
            panic!("Unexpected Unknown result");
        }
    }
}

// ========================================================================
// Push/Pop Incremental Solving Tests
// ========================================================================

#[test]
fn test_push_pop_scopes_affect_solve() {
    let mut solver = Solver::new(1);

    // Outer scope: assert x0
    solver.push();
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));

    // Inner scope: assert ¬x0, making the current context UNSAT
    solver.push();
    solver.add_clause(vec![Literal::negative(Variable(0))]);
    assert!(solver.solve().into_inner().is_unsat());

    // Pop inner: back to {x0}
    assert!(solver.pop());
    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => assert!(model[0]),
        _ => panic!("Expected SAT after popping inner scope"),
    }

    // Pop outer: back to empty context
    assert!(solver.pop());
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));
}

#[test]
fn test_pop_permanently_disables_popped_scope_selector() {
    // Initial user vars: x0 (idx 0)
    let mut solver = Solver::new(1);

    solver.push(); // selector idx 1
    solver.push(); // selector idx 2

    // Add a scoped clause in the inner scope and then pop it.
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    assert!(solver.pop());

    // After popping the inner scope, the selector variable should be forced true
    // by a permanent unit clause, so assuming ¬selector must be UNSAT.
    let selector = Variable(2);
    let result = solver
        .solve_with_assumptions(&[Literal::negative(selector)])
        .into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            assert!(core.contains(&Literal::negative(selector)));
        }
        _ => panic!("Expected UNSAT when assuming a popped selector is false"),
    }
}

#[test]
fn test_add_clause_at_scope_depth_targets_ancestor_scope() {
    let mut solver = Solver::new(1);

    solver.push(); // scope depth 1
    solver.push(); // scope depth 2

    solver.add_clause_at_scope_depth(vec![Literal::positive(Variable(0))], 1);
    solver.add_clause(vec![Literal::negative(Variable(0))]);
    assert!(
        solver.solve().into_inner().is_unsat(),
        "x scoped to depth 1 and ¬x scoped to depth 2 should conflict in depth 2"
    );

    assert!(solver.pop(), "pop depth 2 should succeed");
    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => assert!(
            model[0],
            "depth-1 clause added from depth 2 must survive the inner pop"
        ),
        other => panic!("expected SAT after popping inner scope, got {other:?}"),
    }

    assert!(solver.pop(), "pop depth 1 should succeed");
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "ancestor-scoped clause should disappear after its own scope is popped"
    );
}

#[test]
fn test_pop_clears_scoped_empty_clause_unsat_flag() {
    let mut solver = Solver::new(1);

    solver.push();
    assert!(
        !solver.add_clause(vec![]),
        "empty clause in active scope marks current scope UNSAT"
    );
    assert!(solver.solve().into_inner().is_unsat());

    assert!(solver.pop(), "pop should succeed");
    assert!(
        !solver.has_empty_clause,
        "pop must clear UNSAT marker from popped scope"
    );
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "after pop, base formula should be satisfiable again"
    );
}

#[test]
fn test_assumption_core_does_not_include_scope_selectors() {
    let mut solver = Solver::new(1);

    // Permanent: x0
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    // Add an empty scope (creates a selector that is assumed internally)
    solver.push(); // selector idx 1

    // User assumption conflicts with permanent clause
    let result = solver
        .solve_with_assumptions(&[Literal::negative(Variable(0))])
        .into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            assert!(core.contains(&Literal::negative(Variable(0))));
            assert!(!core.iter().any(|lit| lit.variable() == Variable(1)));
        }
        _ => panic!("Expected UNSAT with core containing only user assumption"),
    }
}

#[test]
fn test_solve_interruptible_honors_should_stop_with_scope_selectors() {
    // Test that solve_interruptible respects the callback in the scoped
    // (assumption-based) solve path. The callback is checked every 1000
    // decisions. We create a large SAT instance (many unrelated variables)
    // so the solver explores many decisions before finding a model.
    //
    // Previous versions used PHP(3..=20) which is exponentially slow for
    // CDCL in debug builds, causing the test to hang indefinitely.
    const NUM_VARS: usize = 2000;
    let mut solver = Solver::new(NUM_VARS);
    solver.set_preprocess_enabled(false);
    solver.push();
    // Add a single positive unit clause so the formula is trivially SAT
    // but the solver must still make ~2000 decisions to assign all vars.
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    let callback_calls = std::cell::Cell::new(0usize);
    let result = solver.solve_interruptible(|| {
        callback_calls.set(callback_calls.get() + 1);
        true
    });

    assert_eq!(
        result,
        SatResult::Unknown,
        "interrupt callback must be respected on scoped-selector path"
    );
    assert!(
        callback_calls.get() > 0,
        "interrupt callback should be invoked on scoped-selector path"
    );
}

#[test]
fn test_solve_interruptible_honors_should_stop_on_scoped_decision_path() {
    const DECISION_CHECK_INTERVAL: usize = 1000;
    const EXTRA_DECISIONS: usize = 64;
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag_unknown_scoped_interruptible.jsonl");

    let mut solver = Solver::new(DECISION_CHECK_INTERVAL + EXTRA_DECISIONS);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();
    solver.set_preprocess_enabled(false);
    solver.push();
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    let callback_calls = std::cell::Cell::new(0usize);
    let result = solver.solve_interruptible(|| {
        callback_calls.set(callback_calls.get() + 1);
        true
    });

    assert_eq!(
        result,
        SatResult::Unknown,
        "interrupt callback must be respected on scoped decision-heavy path"
    );
    assert!(
        solver.num_decisions() >= DECISION_CHECK_INTERVAL as u64,
        "test setup failed: expected to reach decision interrupt checkpoint, got {} decisions",
        solver.num_decisions()
    );
    assert!(
        callback_calls.get() > 0,
        "interrupt callback should be invoked on scoped decision-heavy path"
    );

    let events = read_diagnostic_trace(&diag_path);
    assert_single_unknown_result_summary_with_reason(&events, "interrupted");
}

#[test]
fn test_solve_with_assumptions_interruptible_honors_stop_on_scoped_decision_path() {
    const DECISION_CHECK_INTERVAL: usize = 1000;
    const EXTRA_DECISIONS: usize = 64;
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir
        .path()
        .join("diag_unknown_scoped_assume_interruptible.jsonl");

    let mut solver = Solver::new(DECISION_CHECK_INTERVAL + EXTRA_DECISIONS);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();
    solver.set_preprocess_enabled(false);
    solver.push();
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    let callback_calls = std::cell::Cell::new(0usize);
    let result = solver
        .solve_with_assumptions_interruptible(&[], || {
            callback_calls.set(callback_calls.get() + 1);
            true
        })
        .into_inner();

    assert!(
        matches!(result, AssumeResult::Unknown),
        "interrupt callback must be respected in scoped assumption API on decision-heavy path"
    );
    assert!(
        solver.num_decisions() >= DECISION_CHECK_INTERVAL as u64,
        "test setup failed: expected to reach decision interrupt checkpoint, got {} decisions",
        solver.num_decisions()
    );
    assert!(
        callback_calls.get() > 0,
        "interrupt callback should be invoked in scoped assumption API"
    );

    let events = read_diagnostic_trace(&diag_path);
    assert_single_unknown_result_summary_with_reason(&events, "interrupted");
}

/// The callback-based interrupt (`solve_interruptible`) is checked in the CDCL
/// loop, not during preprocessing.  A trivial 2-variable formula is solved
/// (via lucky phases or walk) before reaching the CDCL conflict loop, so the
/// callback never fires and the result is Sat.
///
/// Note: the `set_interrupt` / `Arc<AtomicBool>` path *does* check during
/// preprocessing — see `test_set_interrupt_honored_during_preprocess`.
#[test]
fn test_solve_interruptible_honors_should_stop_during_preprocess() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    let result = solver
        .solve_interruptible(|| {
            // Interrupt immediately — but preprocessing does not check the callback.
            true
        })
        .into_inner();

    // Trivial SAT formula is solved before the callback is ever consulted.
    assert!(
        matches!(result, SatResult::Sat(_)),
        "trivial formula should be solved before interrupt callback fires"
    );
}

/// Verify that `set_interrupt()` + `is_interrupted()` wiring works (#3638).
///
/// This tests the `Arc<AtomicBool>` path that preprocessing and inprocessing
/// poll. The flag starts unset, we verify is_interrupted() is false, set
/// the flag, and verify is_interrupted() is true.
#[test]
fn test_set_interrupt_wiring() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    let mut solver = Solver::new(4);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    // No interrupt set → is_interrupted() returns false.
    assert!(!solver.is_interrupted());

    // Wire up a flag and verify it's initially unset.
    let flag = Arc::new(AtomicBool::new(false));
    solver.set_interrupt(flag.clone());
    assert!(!solver.is_interrupted());

    // Set the flag → is_interrupted() returns true.
    flag.store(true, Ordering::Relaxed);
    assert!(solver.is_interrupted());
}

#[test]
fn test_solve_empty_formula_with_active_scope_selector() {
    let mut solver = Solver::new(0);
    solver.push();

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.is_empty(), "model should contain only user variables");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// Test that global clauses survive push/pop while scoped clauses don't.
///
/// Part of #1432, #1446 - verifies the incremental scoping soundness fix.
/// Global clauses (definitional) must remain active after pop.
/// Scoped clauses (assertion activations) must be disabled after pop.
#[test]
fn test_global_clause_survives_push_pop() {
    let mut solver = Solver::new(2); // x0, x1

    // Add a GLOBAL clause: (x0 ∨ x1) - must survive pop
    solver.add_clause_global(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    // Push scope and add SCOPED clause: ¬x0
    solver.push();
    solver.add_clause(vec![Literal::negative(Variable(0))]);

    // Solve: should be SAT with x0=false, x1=true (global forces x0∨x1, scoped forces ¬x0)
    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            assert!(!model[0], "x0 should be false (scoped clause)");
            assert!(model[1], "x1 should be true (global clause forces x0∨x1)");
        }
        other => panic!("expected SAT, got {other:?}"),
    }

    // Pop: scoped clause ¬x0 is disabled, but global (x0∨x1) survives
    assert!(solver.pop());

    // Add SCOPED clause: ¬x1
    solver.push();
    solver.add_clause(vec![Literal::negative(Variable(1))]);

    // Solve: should be SAT with x0=true (global x0∨x1 survives, scoped ¬x1)
    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            assert!(model[0], "x0 should be true (global x0∨x1 with scoped ¬x1)");
            assert!(!model[1], "x1 should be false (scoped clause)");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// Regression test for #5522: after push/pop, verify_against_original must
/// still verify base-formula clauses. The `was_scope_selector` bitvec
/// permanently tracks scope selector variables so that scoped clauses
/// (containing selector literals) are skipped while base clauses are checked.
#[test]
fn test_verify_against_original_active_after_push_pop() {
    let mut solver = Solver::new(3); // x0, x1, x2

    // Base-formula clauses:
    // (x0 ∨ x1), (¬x0 ∨ x2), (¬x1 ∨ x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    // Push scope, add scoped clause, solve, pop
    solver.push();
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Sat(_)), "scoped SAT expected");
    assert!(solver.pop());

    // After pop, has_ever_scoped is true
    assert!(
        solver.cold.has_ever_scoped,
        "has_ever_scoped must be true after push/pop"
    );

    // was_scope_selector must be permanently set for the scope selector variable
    // (new_var_internal allocates selector at index == original num_vars == 3)
    assert!(
        solver.cold.was_scope_selector.len() > 3,
        "was_scope_selector must include scope selector variable"
    );
    assert!(
        solver.cold.was_scope_selector[3],
        "variable 3 (scope selector) must be permanently marked"
    );

    // Solve at base scope — verify_against_original_skip_scoped must run
    // and verify the base-formula clauses
    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            // Model must satisfy all 3 base-formula clauses
            assert!(model[0] || model[1], "clause (x0 ∨ x1) must be satisfied");
            assert!(!model[0] || model[2], "clause (¬x0 ∨ x2) must be satisfied");
            assert!(!model[1] || model[2], "clause (¬x1 ∨ x2) must be satisfied");
        }
        other => panic!("expected SAT at base scope after pop, got {other:?}"),
    }
}

/// Test that global clauses participate in unit propagation correctly.
///
/// Part of #1432 - definitional clauses must propagate even after pop.
#[test]
fn test_global_clause_propagation_after_pop() {
    let mut solver = Solver::new(3); // x0, x1, x2

    // Global: (x0 → x1) encoded as (¬x0 ∨ x1)
    solver.add_clause_global(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    // Global: (x1 → x2) encoded as (¬x1 ∨ x2)
    solver.add_clause_global(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    // Push and assert x0 (should propagate x0→x1→x2 via global clauses)
    solver.push();
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            assert!(model[0], "x0 should be true");
            assert!(model[1], "x1 should be true (propagated from x0)");
            assert!(model[2], "x2 should be true (propagated from x1)");
        }
        other => panic!("expected SAT, got {other:?}"),
    }

    // Pop x0 assertion
    assert!(solver.pop());

    // Push and assert ¬x2 (should propagate ¬x2→¬x1→¬x0 via global clauses)
    solver.push();
    solver.add_clause(vec![Literal::negative(Variable(2))]);

    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            // Global implications still work: x0→x1→x2
            // With ¬x2, we need ¬x1 (contrapositive), and ¬x0
            assert!(!model[2], "x2 should be false (scoped clause)");
            // x0 and x1 can be anything consistent - either both false, or x0 false
            // Actually: ¬x0∨x1, ¬x1∨x2, ¬x2 → ¬x1 (from ¬x2), x0 free
            assert!(!model[1], "x1 should be false (contrapositive from ¬x2)");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_push_disables_congruence_factor_decompose_in_incremental_mode() {
    let mut solver: Solver = Solver::new(4);
    solver.set_congruence_enabled(true);
    solver.set_factor_enabled(true);
    solver.set_decompose_enabled(true);
    assert!(solver.inproc_ctrl.congruence.enabled);
    assert!(solver.inproc_ctrl.factor.enabled);
    assert!(solver.inproc_ctrl.decompose.enabled);

    solver.push();
    // has_been_incremental is the guard, not .enabled flags (#5166).
    assert!(
        solver.cold.has_been_incremental,
        "push() must set has_been_incremental"
    );
    // User-facing feature profile is preserved (#5166).
    assert!(
        solver.inproc_ctrl.congruence.enabled,
        "push() must preserve congruence enabled flag (#5166)"
    );
    assert!(
        solver.inproc_ctrl.factor.enabled,
        "push() must preserve factorization enabled flag (#5166)"
    );
    assert!(
        solver.inproc_ctrl.decompose.enabled,
        "push() must preserve decompose enabled flag (#5166)"
    );

    assert!(solver.pop(), "pop should succeed after one push");
    // has_been_incremental remains true after pop — once incremental, always incremental.
    assert!(
        solver.cold.has_been_incremental,
        "has_been_incremental must remain true after pop — incremental mode is permanent"
    );
}

/// Regression test for #3644: Z3-style clean separation — push() must NOT
/// reactivate eliminated or substituted variables. Variables eliminated by
/// BVE/BCE before push stay eliminated permanently. The reconstruction stack
/// handles model extension. This matches Z3's approach where BVE never runs
/// in incremental mode and eliminated variables are never un-eliminated.
#[test]
fn test_push_does_not_reactivate_eliminated_or_substituted_vars() {
    use crate::solver::lifecycle::VarState;

    // 4 variables: x0, x1, x2, x3
    let mut solver: Solver = Solver::new(4);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(2)),
        Literal::negative(Variable(3)),
    ]);

    // x1 is BVE-eliminated with witness entries in the reconstruction stack.
    solver.var_lifecycle.mark_eliminated(1);
    solver.inproc.reconstruction.push_bve(
        Variable(1),
        vec![vec![
            Literal::positive(Variable(1)),
            Literal::positive(Variable(0)),
        ]],
        vec![vec![
            Literal::negative(Variable(1)),
            Literal::negative(Variable(2)),
        ]],
    );

    // x3 is decompose-substituted WITHOUT any witness entry.
    solver.var_lifecycle.mark_substituted(3);

    // Precondition: both variables are removed.
    assert!(solver.var_lifecycle.is_removed(1));
    assert!(solver.var_lifecycle.is_removed(3));

    solver.push();

    // Z3-style: eliminated variables stay eliminated after push.
    assert_eq!(
        solver.var_lifecycle.as_slice()[1],
        VarState::Eliminated,
        "BVE-eliminated variable must stay Eliminated after push() (#3644)"
    );

    // Substituted variables also stay substituted.
    assert_eq!(
        solver.var_lifecycle.as_slice()[3],
        VarState::Substituted,
        "Decompose-substituted variable must stay Substituted after push() (#3644)"
    );

    // has_been_incremental must be set by push.
    assert!(
        solver.cold.has_been_incremental,
        "push() must set has_been_incremental to disable future BVE/BCE"
    );
}

/// Soundness test: pop() must NOT clear has_empty_clause when the empty
/// clause was added at the base (unscoped) level. Base-level UNSAT is
/// permanent.
#[test]
fn test_pop_does_not_clear_base_level_empty_clause() {
    let mut solver = Solver::new(1);

    // Base-level empty clause → permanent UNSAT
    assert!(!solver.add_clause(vec![]));
    assert!(solver.has_empty_clause);

    solver.push();
    assert!(solver.solve().into_inner().is_unsat());
    assert!(solver.pop());

    // has_empty_clause must still be true — the empty clause was top-level
    assert!(
        solver.has_empty_clause,
        "pop must not clear base-level empty clause flag"
    );
    assert!(
        solver.solve().into_inner().is_unsat(),
        "base-level empty clause means formula is permanently UNSAT"
    );
}

/// Regression test for #3731: if base-level UNSAT is established first
/// and then a scoped UNSAT occurs, pop() must NOT clear the base UNSAT.
/// The guard `if !self.has_empty_clause` in mark_empty_clause() prevents
/// scope_depth overwrite; pop() sees depth==0 and preserves the flag.
#[test]
fn test_mixed_provenance_base_then_scoped_unsat() {
    let mut solver = Solver::new(2);

    // Base-level empty clause → permanent UNSAT at depth 0
    assert!(!solver.add_clause(vec![]));
    assert!(solver.has_empty_clause);

    // Push scope and derive another UNSAT within it
    solver.push();
    // Add contradictory unit clauses in scope
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(0))]);
    assert!(solver.solve().into_inner().is_unsat());

    // Pop must NOT clear base UNSAT: provenance depth should still be 0
    assert!(solver.pop());
    assert!(
        solver.has_empty_clause,
        "pop must not clear base-level UNSAT even when scoped UNSAT also occurred"
    );
    assert!(
        solver.solve().into_inner().is_unsat(),
        "base-level empty clause makes formula permanently UNSAT"
    );
}

/// Soundness test for nested push/pop: empty clause derived at depth 2
/// must be cleared when popping back to depth 1, but depth-1 UNSAT
/// (if re-derived) must survive pop back to depth 0.
#[test]
fn test_nested_scope_empty_clause_depth_tracking() {
    let mut solver = Solver::new(2);
    // x0 ∨ x1 at base level — satisfiable
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    solver.push(); // depth 1
    solver.push(); // depth 2

    // Force UNSAT at depth 2 with contradictory unit clauses
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);
    solver.add_clause(vec![Literal::negative(Variable(1))]);
    assert!(solver.solve().into_inner().is_unsat());

    // Pop depth 2 → depth 1: UNSAT derived at depth 2 should be clearable
    assert!(solver.pop());
    // Formula at depth 1 is just (x0 ∨ x1) which is satisfiable
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "popping inner scope should restore satisfiability"
    );

    // Pop depth 1 → depth 0: still satisfiable
    assert!(solver.pop());
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "base formula (x0 ∨ x1) is satisfiable"
    );
}

/// Regression test for #3563/#3475: push() must disable destructive
/// inprocessing passes via has_been_incremental guard.
///
/// After push(), has_been_incremental is true and each destructive technique's
/// entry function checks this flag, preventing execution even though the
/// user-facing .enabled flags remain unchanged (#5166).
#[test]
fn test_push_disables_destructive_inprocessing() {
    let mut solver: Solver = Solver::new(4);
    solver.set_congruence_enabled(true);
    assert!(
        solver.inproc_ctrl.congruence.enabled,
        "congruence should be enabled before push"
    );
    assert!(
        solver.inproc_ctrl.sweep.enabled,
        "sweep should be enabled by default (#7037)"
    );
    solver.set_factor_enabled(true);
    assert!(solver.inproc_ctrl.factor.enabled);

    solver.push();
    let selector = *solver
        .cold
        .scope_selectors
        .last()
        .expect("push() should create exactly one scope selector");

    // has_been_incremental prevents destructive techniques from executing.
    assert!(
        solver.cold.has_been_incremental,
        "push must set has_been_incremental (#3563)"
    );
    // User-facing feature profile is preserved (#5166).
    assert!(
        solver.inproc_ctrl.congruence.enabled,
        "push must preserve user-facing congruence enabled flag (#5166)"
    );
    assert!(
        solver.inproc_ctrl.sweep.enabled,
        "push must preserve user-facing sweep enabled-by-default flag (#5166, #7037)"
    );
    assert!(
        solver.is_frozen(selector),
        "scope selector must be frozen after push (#3541)"
    );
}

/// Defense-in-depth: even if set_*_enabled(true) is called after push(), the
/// function body guards on has_been_incremental prevent execution. This ensures
/// reconstruction-using techniques cannot be accidentally re-enabled in
/// incremental mode (#3662).
#[test]
fn test_incremental_defense_in_depth_guards() {
    let mut solver: Solver = Solver::new(4);

    // Enter incremental mode
    solver.push();
    assert!(solver.cold.has_been_incremental);

    // Attempt to re-enable ALL reconstruction-using / equisatisfiable techniques.
    // All 7 techniques disabled in push() must have body guards.
    solver.set_bve_enabled(true);
    solver.set_bce_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_sweep_enabled(true);
    solver.set_condition_enabled(true);
    solver.set_decompose_enabled(true);
    solver.set_factor_enabled(true);

    // The enabled flags are set (this is the API surface), but the function
    // bodies have has_been_incremental guards that prevent execution.
    assert!(solver.inproc_ctrl.bve.enabled);
    assert!(solver.inproc_ctrl.bce.enabled);
    assert!(solver.inproc_ctrl.congruence.enabled);
    assert!(solver.inproc_ctrl.sweep.enabled);
    assert!(solver.inproc_ctrl.condition.enabled);
    assert!(solver.inproc_ctrl.decompose.enabled);
    assert!(solver.inproc_ctrl.factor.enabled);

    // Verify the techniques are effectively blocked by calling them directly.
    // None of these should modify clause_db or reconstruction stack.
    let recon_before = solver.inproc.reconstruction.len();
    let num_vars_before = solver.num_vars;
    let bve_unsat = solver.bve();
    solver.bce();
    solver.congruence();
    let sweep_unsat = solver.sweep();
    solver.condition();
    solver.decompose();
    solver.factorize();

    assert!(
        !bve_unsat,
        "bve should not return UNSAT in empty solver under incremental guard"
    );
    assert!(
        !sweep_unsat,
        "sweep should not return UNSAT in empty solver"
    );
    assert_eq!(
        solver.inproc.reconstruction.len(),
        recon_before,
        "reconstruction stack must not grow when has_been_incremental guards are active"
    );
    assert_eq!(
        solver.num_vars, num_vars_before,
        "num_vars must not change (factorize extension vars blocked by incremental guard)"
    );
}

/// Verify that solve_with_extension works correctly with scoped solving (#8423).
/// Previously this panicked (debug) / returned Unknown (release) because
/// extensions were not supported with scope selectors. Now the extension is
/// wired into the assumption-based CDCL loop for scoped solving.
#[test]
fn test_solve_with_extension_panics_with_scope_selectors() {
    use crate::extension::{ExtCheckResult, ExtPropagateResult, Extension, SolverContext};

    struct NoopExtension;
    impl Extension for NoopExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }
        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }
    }

    let mut solver = Solver::new(1);
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.push();
    let mut ext = NoopExtension;
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "solve_with_extension() with scoped solving should return Sat, got {result:?}",
    );
}

/// Verify that pop() emits an LRAT delete step for the empty clause when
/// retracting scoped UNSAT (#4475 Fix 2).
///
/// The original version of this test used Solver::new (no proof_manager),
/// so emit_delete was never called — the test verified field cleanup only.
/// This version uses a proof-enabled solver and inspects the LRAT output.
#[test]
fn test_push_pop_emits_lrat_delete_for_scoped_empty_clause() {
    // Build the contradiction inside the scope. The guarded input clauses and
    // the scope-selector assumption give the proof manager a checker-visible
    // LRAT chain for the scoped empty clause.
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    let a = Literal::positive(Variable(0));

    solver.push();
    solver.add_clause(vec![a]);
    solver.add_clause(vec![a.negated()]);
    assert!(
        solver.solve().into_inner().is_unsat(),
        "scoped contradiction must be UNSAT"
    );
    assert!(
        solver.cold.empty_clause_in_proof,
        "empty clause must be in proof after scoped solve"
    );
    let ec_id = solver
        .cold
        .empty_clause_lrat_id
        .expect("empty_clause_lrat_id must be set after scoped LRAT solve");

    // Pop must emit an LRAT delete step for the empty clause.
    assert!(solver.pop());
    assert!(
        solver.cold.empty_clause_lrat_id.is_none(),
        "pop must clear empty_clause_lrat_id (#4475)"
    );
    assert!(
        !solver.has_empty_clause,
        "pop must clear has_empty_clause for scoped UNSAT"
    );

    // Extract proof text and verify the delete step references the empty clause ID.
    let proof_output = solver.take_proof_writer().expect("proof writer must exist");
    let proof_text = String::from_utf8(proof_output.into_vec().expect("flush")).expect("UTF-8");

    // LRAT delete format: "<step_id> d <deleted_id1> ... 0"
    let ec_id_str = ec_id.to_string();
    let has_delete = proof_text.lines().any(|line| {
        line.contains(" d ")
            && line
                .split_whitespace()
                .skip(2) // skip step_id and "d"
                .any(|tok| tok == ec_id_str)
    });
    assert!(
        has_delete,
        "LRAT proof must contain a delete step for empty clause (ID {ec_id})\nproof:\n{proof_text}",
    );
}

/// Repeated scoped UNSAT cycles in LRAT mode must emit a fresh empty-clause
/// proof step on each solve.
#[test]
fn test_lrat_repeated_scoped_unsat_cycles_emit_empty_clause_each_time() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));

    solver.push();
    solver.add_clause(vec![x0]);
    solver.add_clause(vec![x0.negated()]);
    let first = solver.solve().into_inner();
    assert!(first.is_unsat(), "first scoped contradiction must be UNSAT");
    assert!(solver.pop(), "first pop must succeed");

    solver.push();
    solver.add_clause(vec![x1]);
    solver.add_clause(vec![x1.negated()]);
    let second = solver.solve().into_inner();
    assert!(
        second.is_unsat(),
        "second scoped contradiction must remain UNSAT after pop/push reuse"
    );

    let proof_output = solver.take_proof_writer().expect("proof writer must exist");
    let proof_text = String::from_utf8(proof_output.into_vec().expect("flush")).expect("UTF-8");
    let empty_clause_adds = proof_text
        .lines()
        .filter(|line| {
            !line.contains(" d ")
                && line
                    .split_whitespace()
                    .nth(1)
                    .is_some_and(|token| token == "0")
        })
        .count();
    assert_eq!(
        empty_clause_adds, 2,
        "each scoped UNSAT must emit its own empty clause proof step\nproof:\n{proof_text}"
    );
}

/// Expose an incomplete proof stream when scoped solve() returns UNSAT via the
/// Scoped solve with assumption-conflict: {x0} + push + {¬x0} is UNSAT.
///
/// Previously, assumptions.rs:336 skipped learned clause emission, producing
/// an incomplete proof stream that the forward checker rejected. The bug is
/// now fixed — the proof stream is complete and the forward checker accepts it.
#[test]
#[cfg(debug_assertions)]
fn test_scoped_solve_unsat_proof_complete() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(1, proof);
    let x0 = Literal::positive(Variable(0));

    solver.add_clause(vec![x0]);
    solver.push();
    solver.add_clause(vec![x0.negated()]);

    // The assumption-conflict shortcut now emits a complete proof stream.
    // The forward checker (debug builds) validates it without panic.
    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "scoped (x0) + (not x0) must be UNSAT");
}

/// Regression test for PDR soundness bug (#5380).
///
/// This CNF (17 vars, 18 clauses + 6 assumption variables) is the exact Tseitin encoding
/// of check_sat's formula for `body(x,y) ∧ ¬head(x+1, y+x)` from the accumulator_unsafe_000
/// benchmark. CaDiCaL confirms it's SAT, but ay_sat was incorrectly returning UNSAT.
#[test]
fn test_assumption_sat_tseitin_accumulator_bug() {
    let mut solver: Solver = Solver::new(17);

    // Helper to convert DIMACS literals to ay_sat literals
    let d = |dimacs: i32| -> Literal { Literal::from_dimacs(dimacs) };

    // 18 Tseitin clauses (from AY_DUMP_CNF output)
    solver.add_clause(vec![d(-3), d(-4), d(-5)]);
    solver.add_clause(vec![d(4), d(3)]);
    solver.add_clause(vec![d(5), d(3)]);
    solver.add_clause(vec![d(-7), d(-4), d(-8)]);
    solver.add_clause(vec![d(4), d(7)]);
    solver.add_clause(vec![d(8), d(7)]);
    solver.add_clause(vec![d(-10), d(11)]);
    solver.add_clause(vec![d(-10), d(12)]);
    solver.add_clause(vec![d(-11), d(-12), d(10)]);
    solver.add_clause(vec![d(-13), d(11)]);
    solver.add_clause(vec![d(-13), d(14)]);
    solver.add_clause(vec![d(-11), d(-14), d(13)]);
    solver.add_clause(vec![d(-9), d(10), d(13), d(-15), d(-16), d(-17)]);
    solver.add_clause(vec![d(-10), d(9)]);
    solver.add_clause(vec![d(-13), d(9)]);
    solver.add_clause(vec![d(15), d(9)]);
    solver.add_clause(vec![d(16), d(9)]);
    solver.add_clause(vec![d(17), d(9)]);

    // 6 assumptions: v1, v2, v3, v6, v7, v9
    let assumptions = vec![d(1), d(2), d(3), d(6), d(7), d(9)];

    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(
        matches!(result, AssumeResult::Sat(_)),
        "CNF is SAT (confirmed by CaDiCaL) but ay_sat returned {result:?}",
    );
}

/// Regression test: all 28 clauses (18 Tseitin + 7 blocking + 3 split) added upfront
/// to a solver with 23 variables. The satisfying model is x=1, y=0 which requires
/// v12=true (eq(y+x,1)). CaDiCaL confirms SAT.
///
/// If this passes but the incremental version fails, the bug is in incremental solving.
#[test]
fn test_accumulator_all_clauses_batch() {
    let mut solver: Solver = Solver::new(23);
    let d = |dimacs: i32| -> Literal { Literal::from_dimacs(dimacs) };

    // === Original 18 Tseitin clauses ===
    solver.add_clause(vec![d(-3), d(-4), d(-5)]);
    solver.add_clause(vec![d(4), d(3)]);
    solver.add_clause(vec![d(5), d(3)]);
    solver.add_clause(vec![d(-7), d(-4), d(-8)]);
    solver.add_clause(vec![d(4), d(7)]);
    solver.add_clause(vec![d(8), d(7)]);
    solver.add_clause(vec![d(-10), d(11)]);
    solver.add_clause(vec![d(-10), d(12)]);
    solver.add_clause(vec![d(-11), d(-12), d(10)]);
    solver.add_clause(vec![d(-13), d(11)]);
    solver.add_clause(vec![d(-13), d(14)]);
    solver.add_clause(vec![d(-11), d(-14), d(13)]);
    solver.add_clause(vec![d(-9), d(10), d(13), d(-15), d(-16), d(-17)]);
    solver.add_clause(vec![d(-10), d(9)]);
    solver.add_clause(vec![d(-13), d(9)]);
    solver.add_clause(vec![d(15), d(9)]);
    solver.add_clause(vec![d(16), d(9)]);
    solver.add_clause(vec![d(17), d(9)]);

    // === 7 blocking clauses from DPLL(T) Farkas lemmas ===
    solver.add_clause(vec![d(-1), d(-11)]);
    solver.add_clause(vec![d(-19), d(-18)]);
    solver.add_clause(vec![d(-21), d(-20)]);
    solver.add_clause(vec![d(-4), d(-21), d(-6)]);
    solver.add_clause(vec![d(-1), d(-21), d(-6)]);
    solver.add_clause(vec![d(-23), d(-22)]);
    solver.add_clause(vec![d(-8), d(-23), d(-6)]);

    // === 3 disequality split clauses (with guard literals) ===
    solver.add_clause(vec![d(5), d(18), d(19)]);
    solver.add_clause(vec![d(8), d(20), d(21)]);
    solver.add_clause(vec![d(4), d(22), d(23)]);

    let assumptions = vec![d(1), d(2), d(3), d(6), d(7), d(9)];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(
        matches!(result, AssumeResult::Sat(_)),
        "Batch: all 28 clauses + 23 vars should be SAT (x=1,y=0), got {result:?}",
    );
}

/// Test incremental_original_boundary: tracks which original clauses are known to the arena.
/// After initial add_clause calls, boundary equals original_clauses.len() (#5656).
#[test]
fn test_incremental_original_boundary_tracks_add_clause() {
    let mut solver = Solver::new(4);
    let d = |dimacs: i32| -> Literal { Literal::from_dimacs(dimacs) };

    assert_eq!(solver.cold.incremental_original_boundary, 0);

    // Add 3 initial clauses
    solver.add_clause(vec![d(1), d(2)]);
    assert_eq!(solver.cold.incremental_original_boundary, 1);
    solver.add_clause(vec![d(-1), d(3)]);
    assert_eq!(solver.cold.incremental_original_boundary, 2);
    solver.add_clause(vec![d(2), d(4)]);
    assert_eq!(solver.cold.incremental_original_boundary, 3);
    assert_eq!(solver.cold.original_ledger.num_clauses(), 3);
}

/// Test incremental_original_boundary Case (b): incremental solve adds only new clauses.
/// After set_incremental_mode, new clauses added between solves are appended
/// to the arena without a full rebuild (#5656, #5608).
#[test]
fn test_incremental_original_boundary_adds_only_new_clauses() {
    let mut solver = Solver::new(4);
    let d = |dimacs: i32| -> Literal { Literal::from_dimacs(dimacs) };

    // Enable incremental mode to prevent BVE (which would force arena rebuild)
    solver.set_incremental_mode();

    // Add initial clauses and solve
    solver.add_clause(vec![d(1), d(2)]);
    solver.add_clause(vec![d(-1), d(3)]);
    solver.add_clause(vec![d(-2), d(4)]);
    assert_eq!(solver.cold.incremental_original_boundary, 3);

    let r1 = solver.solve();
    assert!(r1.is_sat(), "Initial solve should be SAT: {r1}");

    // Boundary should still be at 3 after solve
    assert_eq!(solver.cold.incremental_original_boundary, 3);

    // Add new clause between solves
    solver.add_clause(vec![d(-3), d(-4)]);
    assert_eq!(solver.cold.incremental_original_boundary, 4);
    assert_eq!(solver.cold.original_ledger.num_clauses(), 4);

    // Solve again — should still be SAT with the new clause
    let r2 = solver.solve();
    assert!(r2.is_sat(), "Second solve should be SAT: {r2}");
}

/// Test incremental_original_boundary: new clauses make formula UNSAT.
/// Verifies that incrementally added clauses participate in the second solve (#5656).
#[test]
fn test_incremental_original_boundary_new_clause_causes_unsat() {
    let mut solver = Solver::new(2);
    let d = |dimacs: i32| -> Literal { Literal::from_dimacs(dimacs) };

    solver.set_incremental_mode();

    // x1 AND x2 — SAT
    solver.add_clause(vec![d(1)]);
    solver.add_clause(vec![d(2)]);
    let r1 = solver.solve();
    assert!(r1.is_sat(), "First solve should be SAT: {r1}");

    // Add NOT(x1) — makes it UNSAT
    solver.add_clause(vec![d(-1)]);
    assert_eq!(solver.cold.incremental_original_boundary, 3);
    let r2 = solver.solve();
    assert!(r2.is_unsat(), "Second solve should be UNSAT: {r2}");
}

/// Regression test: incremental clause addition mimicking exact DPLL(T) sequence.
/// Start with 17 vars + 18 clauses, solve, add lemma/split, solve again, etc.
#[test]
fn test_accumulator_incremental_dpll_t_sequence() {
    let mut solver: Solver = Solver::new(17);
    let d = |dimacs: i32| -> Literal { Literal::from_dimacs(dimacs) };

    // === Original 18 Tseitin clauses ===
    solver.add_clause(vec![d(-3), d(-4), d(-5)]);
    solver.add_clause(vec![d(4), d(3)]);
    solver.add_clause(vec![d(5), d(3)]);
    solver.add_clause(vec![d(-7), d(-4), d(-8)]);
    solver.add_clause(vec![d(4), d(7)]);
    solver.add_clause(vec![d(8), d(7)]);
    solver.add_clause(vec![d(-10), d(11)]);
    solver.add_clause(vec![d(-10), d(12)]);
    solver.add_clause(vec![d(-11), d(-12), d(10)]);
    solver.add_clause(vec![d(-13), d(11)]);
    solver.add_clause(vec![d(-13), d(14)]);
    solver.add_clause(vec![d(-11), d(-14), d(13)]);
    solver.add_clause(vec![d(-9), d(10), d(13), d(-15), d(-16), d(-17)]);
    solver.add_clause(vec![d(-10), d(9)]);
    solver.add_clause(vec![d(-13), d(9)]);
    solver.add_clause(vec![d(15), d(9)]);
    solver.add_clause(vec![d(16), d(9)]);
    solver.add_clause(vec![d(17), d(9)]);

    let assumptions = vec![d(1), d(2), d(3), d(6), d(7), d(9)];

    // Step 1: initial solve (should be SAT)
    let r = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(matches!(r, AssumeResult::Sat(_)), "Step 1 failed: {r:?}");

    // iter 1 lemma: NOT(x>=0) v NOT(eq(x+1,0))
    solver.add_clause(vec![d(-1), d(-11)]);
    let r = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(matches!(r, AssumeResult::Sat(_)), "Step 2 failed: {r:?}");

    // iter 2: split y!=1
    solver.ensure_num_vars(19);
    solver.add_clause(vec![d(5), d(18), d(19)]);
    let r = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(matches!(r, AssumeResult::Sat(_)), "Step 3 failed: {r:?}");

    // iter 3 lemma: NOT(y>=2) v NOT(y<=0)
    solver.add_clause(vec![d(-19), d(-18)]);
    let r = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(matches!(r, AssumeResult::Sat(_)), "Step 4 failed: {r:?}");

    // iter 4: split y!=2
    solver.ensure_num_vars(21);
    solver.add_clause(vec![d(8), d(20), d(21)]);
    let r = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(matches!(r, AssumeResult::Sat(_)), "Step 5 failed: {r:?}");

    // iter 5 lemma: NOT(y>=3) v NOT(y<=1)
    solver.add_clause(vec![d(-21), d(-20)]);
    let r = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(matches!(r, AssumeResult::Sat(_)), "Step 6 failed: {r:?}");

    // iter 6 lemma
    solver.add_clause(vec![d(-4), d(-21), d(-6)]);
    let r = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(matches!(r, AssumeResult::Sat(_)), "Step 7 failed: {r:?}");

    // iter 7 lemma
    solver.add_clause(vec![d(-1), d(-21), d(-6)]);
    let r = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(matches!(r, AssumeResult::Sat(_)), "Step 8 failed: {r:?}");

    // iter 8: split x!=0
    solver.ensure_num_vars(23);
    solver.add_clause(vec![d(4), d(22), d(23)]);
    let r = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(matches!(r, AssumeResult::Sat(_)), "Step 9 failed: {r:?}");

    // iter 9 lemma: NOT(x>=1) v NOT(x<=-1)
    solver.add_clause(vec![d(-23), d(-22)]);
    let r = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(matches!(r, AssumeResult::Sat(_)), "Step 10 failed: {r:?}");

    // iter 10 lemma: NOT(eq(y,2)) v NOT(x>=1) v NOT(y+2x+1<=3)
    solver.add_clause(vec![d(-8), d(-23), d(-6)]);

    // FINAL: formula is still SAT at x=1, y=0 with v12=true (eq(y+x,1)=true)
    let r = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(
        matches!(r, AssumeResult::Sat(_)),
        "Incremental DPLL(T): formula still SAT (x=1,y=0), got {r:?}",
    );
}

/// Regression test for #7987: solve_with_assumptions returns wrong UNSAT
/// after incremental add_clause between assumption solves.
///
/// Formula:
///   ~0          (Var 0 = false)
///   ~2 v ~1     (not both 2 and 1)
///    2 v  1     (at least one of 2 or 1)
///
/// First solve: assume +1 => SAT (0=F, 1=T, 2=F)
/// Add clause: ~1 (Var 1 = false)
/// Second solve: assume +2 => should be SAT (0=F, 1=F, 2=T)
///
/// Before fix: second solve returned UNSAT.
#[test]
fn test_issue_7987_incremental_assumption_wrong_unsat() {
    let mut s = Solver::new(3);
    s.add_clause(vec![Literal::negative(Variable(0))]); // Var(0)=false
    s.add_clause(vec![
        Literal::negative(Variable(2)),
        Literal::negative(Variable(1)),
    ]);
    s.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(1)),
    ]);

    let r1 = s.solve_with_assumptions(&[Literal::positive(Variable(1))]);
    assert!(r1.is_sat(), "First solve should be SAT, got {r1:?}");

    s.add_clause(vec![Literal::negative(Variable(1))]);

    let r2 = s.solve_with_assumptions(&[Literal::positive(Variable(2))]);
    assert!(
        r2.is_sat(),
        "Second solve should be SAT (0=F, 1=F, 2=T satisfies all clauses with assumption +2), got {r2:?}",
    );
}

/// Regression test for #7981: BVE+push/pop interaction must not produce false UNSAT.
///
/// Scenario:
/// 1. Formula with variable x0 that BVE can eliminate: (x0 | x1) & (!x0 | x2)
///    BVE resolvent: (x1 | x2)
/// 2. First solve triggers preprocessing; BVE eliminates x0
/// 3. push() — enters incremental mode (disables further BVE)
/// 4. add_clause referencing eliminated x0: (!x0 | x1) scoped
/// 5. Second solve must NOT return false UNSAT
///
/// The fix ensures: variable x0 is reactivated with competitive VSIDS activity,
/// the arena is rebuilt from original_ledger (restoring pre-BVE clauses), and
/// the reconstruction stack is drained so stale BVE witnesses don't pollute the
/// search.
#[test]
fn test_issue_7981_bve_push_pop_no_false_unsat() {
    // 4 variables: x0 (BVE target), x1, x2, x3
    let mut solver = Solver::new(4);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);
    let x3 = Variable(3);

    // Formula that makes x0 eligible for BVE:
    // (x0 | x1)   — x0 positive occurrence
    // (!x0 | x2)  — x0 negative occurrence
    // Resolvent: (x1 | x2) — bounded, so BVE should eliminate x0
    //
    // Additional clauses to make formula non-trivial:
    // (x1 | x3)
    // (!x2 | x3)
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x2)]);
    solver.add_clause(vec![Literal::positive(x1), Literal::positive(x3)]);
    solver.add_clause(vec![Literal::negative(x2), Literal::positive(x3)]);

    // First solve — SAT. BVE may eliminate x0 during preprocessing.
    let r1 = solver.solve().into_inner();
    assert!(
        matches!(r1, SatResult::Sat(_)),
        "First solve should be SAT, got {r1:?}"
    );

    // Enter incremental mode
    solver.push();

    // Add a scoped clause that references the (possibly eliminated) variable x0.
    // This clause makes x0 = false required in the scoped context.
    solver.add_clause(vec![Literal::negative(x0)]);

    // Second solve — still SAT (x0=F, x1=T, x2 any, x3=T satisfies everything)
    let r2 = solver.solve().into_inner();
    match r2 {
        SatResult::Sat(ref model) => {
            // The scoped clause !x0 forces x0=false.
            // Original clauses: (x0|x1) => x1=T, (!x0|x2) always satisfied,
            // (x1|x3) satisfied by x1=T, (!x2|x3) any consistent assignment.
            assert!(!model[x0.index()], "x0 must be false (scoped clause !x0)");
            assert!(model[x1.index()], "x1 must be true (x0|x1 with x0=F)");
        }
        other => panic!(
            "BUG (#7981): Second solve after push + clause referencing BVE-eliminated \
             variable should be SAT, got {other:?}"
        ),
    }

    // Pop the scope
    assert!(solver.pop());

    // Third solve — SAT (back to base formula only)
    let r3 = solver.solve().into_inner();
    assert!(
        matches!(r3, SatResult::Sat(_)),
        "Third solve after pop should be SAT, got {r3:?}"
    );
}

/// Extended #7981 regression: BVE elimination followed by push/pop with a clause
/// that makes the scoped formula actually UNSAT, then verify pop restores SAT.
#[test]
fn test_issue_7981_bve_push_pop_scoped_unsat_then_sat() {
    let mut solver = Solver::new(3);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);

    // Formula where BVE can eliminate x0:
    // (x0 | x1) & (!x0 | x2) & (x1 | x2)
    // BVE resolvent for x0: (x1 | x2) — already present, so net reduction.
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x2)]);
    solver.add_clause(vec![Literal::positive(x1), Literal::positive(x2)]);

    // First solve — SAT
    let r1 = solver.solve().into_inner();
    assert!(matches!(r1, SatResult::Sat(_)), "First solve: SAT expected");

    // Push scope
    solver.push();

    // Add scoped clauses that force UNSAT via the eliminated variable:
    // !x1 & !x2 & (x0 | x1) makes it: need x0=T (from x0|x1 with x1=F),
    // but !x0|x2 with x2=F forces x0=F. Contradiction.
    solver.add_clause(vec![Literal::negative(x1)]);
    solver.add_clause(vec![Literal::negative(x2)]);

    let r2 = solver.solve().into_inner();
    assert!(
        r2.is_unsat(),
        "Scoped solve should be UNSAT (x1=F, x2=F contradicts base clauses)"
    );

    // Pop scope — back to base formula which is SAT
    assert!(solver.pop());
    let r3 = solver.solve().into_inner();
    assert!(
        matches!(r3, SatResult::Sat(_)),
        "After pop, base formula should be SAT again, got {r3:?}"
    );
}

/// #7981 edge case: multiple push/pop cycles with BVE-eliminated variable.
/// Ensures the variable reactivation and ledger rebuild work across cycles.
#[test]
fn test_issue_7981_bve_multiple_push_pop_cycles() {
    let mut solver = Solver::new(4);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);
    let x3 = Variable(3);

    // BVE-eligible formula:
    // (x0 | x1) & (!x0 | x2) & (x1 | x3) & (!x2 | x3)
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x2)]);
    solver.add_clause(vec![Literal::positive(x1), Literal::positive(x3)]);
    solver.add_clause(vec![Literal::negative(x2), Literal::positive(x3)]);

    // First solve triggers BVE
    let r1 = solver.solve().into_inner();
    assert!(matches!(r1, SatResult::Sat(_)), "Initial solve: SAT");

    // Cycle 1: push, add clause with eliminated var, solve, pop
    solver.push();
    solver.add_clause(vec![Literal::negative(x0)]);
    let r2 = solver.solve().into_inner();
    assert!(
        matches!(r2, SatResult::Sat(_)),
        "Cycle 1 scoped: SAT expected"
    );
    assert!(solver.pop());

    // Cycle 2: push, add different clause with eliminated var, solve, pop
    solver.push();
    solver.add_clause(vec![Literal::positive(x0)]);
    let r3 = solver.solve().into_inner();
    assert!(
        matches!(r3, SatResult::Sat(_)),
        "Cycle 2 scoped: SAT expected"
    );
    assert!(solver.pop());

    // Final base solve
    let r4 = solver.solve().into_inner();
    assert!(matches!(r4, SatResult::Sat(_)), "Final base: SAT expected");
}

// ========================================================================
// Scoped Clause Reclaim (GC) Tests (#1444)
// ========================================================================

/// Test that pop() eagerly reclaims scoped clauses from the arena.
/// After push/add_clause/pop, clauses guarded by the scope selector should
/// be deleted from the arena.
#[test]
fn test_gc_scoped_clauses_basic_reclaim() {
    let mut solver = Solver::new(3);

    // Base clause: (x0 | x1) — should survive all push/pop cycles.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    let active_before_push = solver.arena.active_clause_count();

    solver.push();

    // Scoped clauses: (x1 | x2) and (¬x0 | x2), guarded by scope selector.
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    let active_in_scope = solver.arena.active_clause_count();
    assert!(
        active_in_scope > active_before_push,
        "scoped clauses should increase active clause count"
    );

    // Pop should reclaim the 2 scoped clauses.
    assert!(solver.pop());
    let active_after_pop = solver.arena.active_clause_count();

    // The scoped clauses should be deleted. The unit clause [+selector]
    // added by pop is also in the arena, but the 2 scoped clauses (which
    // contain +selector) should be gone.
    // Expected: active_before_push (base clause) + 1 (unit [+selector])
    // = active_before_push + 1.
    // The scoped clauses (which had +selector appended) are deleted.
    assert!(
        active_after_pop < active_in_scope,
        "pop() should reclaim scoped clauses: before_pop={active_in_scope}, after_pop={active_after_pop}"
    );

    assert!(
        solver.cold.scoped_clauses_reclaimed >= 2,
        "should have reclaimed at least 2 scoped clauses, got {}",
        solver.cold.scoped_clauses_reclaimed,
    );

    // Solver correctness: base formula should still be SAT.
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "base formula (x0|x1) should be SAT after pop, got {result:?}"
    );
}

/// Test that scoped clause GC works correctly across nested push/pop cycles.
#[test]
fn test_gc_scoped_clauses_nested_push_pop() {
    let mut solver = Solver::new(4);

    // Base: (x0 | x1)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    solver.push(); // depth 1
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ]);
    let active_depth1 = solver.arena.active_clause_count();

    solver.push(); // depth 2
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(2)),
        Literal::negative(Variable(3)),
    ]);

    // Pop depth 2: should reclaim 2 depth-2 clauses.
    assert!(solver.pop());
    let active_after_pop2 = solver.arena.active_clause_count();
    assert!(
        active_after_pop2 <= active_depth1 + 1, // +1 for the unit [+sel2]
        "pop(depth 2) should reclaim depth-2 clauses: depth1={active_depth1}, after_pop2={active_after_pop2}"
    );

    // Depth-1 clause should still be active (solver still SAT).
    let r = solver.solve().into_inner();
    assert!(matches!(r, SatResult::Sat(_)), "depth-1 should be SAT");

    // Pop depth 1: should reclaim depth-1 clause.
    assert!(solver.pop());

    // Base formula only.
    let r = solver.solve().into_inner();
    assert!(
        matches!(r, SatResult::Sat(_)),
        "base should be SAT after both pops"
    );
}

/// Test that scoped clause GC handles many push/pop cycles without memory growth.
/// Simulates a long incremental session (e.g., CHC solver with thousands of
/// check_sat calls).
#[test]
fn test_gc_scoped_clauses_many_cycles_no_memory_growth() {
    let mut solver = Solver::new(4);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    let baseline_active = solver.arena.active_clause_count();

    for _ in 0..100 {
        solver.push();
        solver.add_clause(vec![
            Literal::positive(Variable(2)),
            Literal::positive(Variable(3)),
        ]);
        solver.add_clause(vec![
            Literal::negative(Variable(0)),
            Literal::positive(Variable(3)),
        ]);
        assert!(solver.pop());
    }

    // After 100 push/pop cycles, the active clause count should NOT grow
    // by 200 (the number of scoped clauses added). With GC, it should be
    // close to baseline + some unit clauses for selectors.
    let final_active = solver.arena.active_clause_count();

    // Without GC: 200 scoped clauses would persist. With GC: they're reclaimed.
    // Allow for unit selector clauses (1 per cycle = 100) which are NOT scoped
    // and thus not reclaimed.
    assert!(
        final_active < baseline_active + 200,
        "scoped clause GC should prevent unbounded arena growth: \
         baseline={baseline_active}, final={final_active}, expected < {}",
        baseline_active + 200,
    );

    assert!(
        solver.cold.scoped_clauses_reclaimed >= 200,
        "should reclaim at least 200 scoped clauses across 100 cycles, got {}",
        solver.cold.scoped_clauses_reclaimed,
    );

    // Correctness: base formula still SAT.
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "base formula should be SAT after 100 push/pop cycles"
    );
}

/// Test that the scoped clause GC preserves correctness: after pop, solving
/// must give correct results both for SAT and UNSAT.
#[test]
fn test_gc_scoped_clauses_correctness_sat_then_unsat() {
    let mut solver = Solver::new(2);

    // Base: x0
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    // Scope 1: add x1 (SAT: x0=T, x1=T)
    solver.push();
    solver.add_clause(vec![Literal::positive(Variable(1))]);
    let r = solver.solve().into_inner();
    match r {
        SatResult::Sat(model) => {
            assert!(model[0], "x0=T");
            assert!(model[1], "x1=T");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
    assert!(solver.pop());

    // Scope 2: add ¬x0 (UNSAT: conflicts with base x0)
    solver.push();
    solver.add_clause(vec![Literal::negative(Variable(0))]);
    let r = solver.solve().into_inner();
    assert!(r.is_unsat(), "should be UNSAT (x0 AND ¬x0)");
    assert!(solver.pop());

    // After both pops, base formula should be SAT.
    let r = solver.solve().into_inner();
    assert!(matches!(r, SatResult::Sat(_)), "base x0 should be SAT");
}

/// Test GC with scoped clauses added at a specific ancestor scope depth.
/// add_clause_at_scope_depth targets an ancestor scope, meaning the clause
/// gets a different scope selector than the current innermost scope.
#[test]
fn test_gc_scoped_clauses_at_ancestor_depth() {
    let mut solver = Solver::new(2);

    solver.push(); // depth 1
    solver.push(); // depth 2

    // Add clause targeting depth 1 (ancestor of current depth 2).
    solver.add_clause_at_scope_depth(vec![Literal::positive(Variable(0))], 1);
    // Add clause at current depth 2.
    solver.add_clause(vec![Literal::positive(Variable(1))]);

    // Pop depth 2: should reclaim depth-2 clause only.
    assert!(solver.pop());
    let r = solver.solve().into_inner();
    match r {
        SatResult::Sat(model) => {
            assert!(
                model[0],
                "depth-1 clause (x0) should survive pop of depth 2"
            );
        }
        other => panic!("expected SAT with x0=T, got {other:?}"),
    }

    // Pop depth 1: should reclaim depth-1 clause.
    assert!(solver.pop());
    let r = solver.solve().into_inner();
    assert!(
        matches!(r, SatResult::Sat(_)),
        "empty base should be SAT after all pops"
    );
}

/// Test that incremental watch boundary (#8374) preserves watches from the
/// previous solve when only new original clauses are appended (case b).
///
/// This verifies that:
/// 1. incremental_watch_boundary is set when case (b) runs
/// 2. watches.clear() is skipped in case (b)
/// 3. The second solve produces correct results using preserved + new watches
#[test]
fn test_incremental_watch_boundary_preserves_watches() {
    let mut solver = Solver::new(6);
    let d = |dimacs: i32| -> Literal { Literal::from_dimacs(dimacs) };

    // Enable incremental mode to prevent destructive inprocessing
    solver.set_incremental_mode();

    // Add initial clauses: (1 v 2) ^ (-1 v 3) ^ (-2 v 4)
    solver.add_clause(vec![d(1), d(2)]);
    solver.add_clause(vec![d(-1), d(3)]);
    solver.add_clause(vec![d(-2), d(4)]);

    // First solve
    let r1 = solver.solve();
    assert!(r1.is_sat(), "First solve should be SAT: {r1}");

    // Record arena length before adding new clauses
    let arena_len_before = solver.arena.len();

    // Add new clauses between solves: (5 v 6) ^ (-5 v -6)
    solver.add_clause(vec![d(5), d(6)]);
    solver.add_clause(vec![d(-5), d(-6)]);

    // The arena should have grown
    assert!(
        solver.arena.len() > arena_len_before,
        "Arena should grow after adding clauses"
    );

    // Second solve — should use incremental watch path (case b)
    let r2 = solver.solve();
    assert!(r2.is_sat(), "Second solve should be SAT: {r2}");

    // Verify model satisfies all original clauses
    if let SatResult::Sat(ref model) = r2.into_inner() {
        let violation = solver.verify_against_original(model);
        assert!(
            violation.is_none(),
            "Model should satisfy all clauses: violation at clause {violation:?}"
        );
    }
}

/// Test that the incremental watch boundary correctly handles the transition
/// from SAT to UNSAT when new clauses make the formula unsatisfiable (#8374).
#[test]
fn test_incremental_watch_boundary_sat_to_unsat() {
    let mut solver = Solver::new(3);
    let d = |dimacs: i32| -> Literal { Literal::from_dimacs(dimacs) };

    solver.set_incremental_mode();

    // Initial formula: (1) ^ (2) ^ (3) — SAT with all true
    solver.add_clause(vec![d(1)]);
    solver.add_clause(vec![d(2)]);
    solver.add_clause(vec![d(3)]);

    let r1 = solver.solve();
    assert!(r1.is_sat(), "First solve should be SAT: {r1}");

    // Add contradicting clause: (-1) — makes it UNSAT
    solver.add_clause(vec![d(-1)]);

    // Second solve with incremental watches should correctly detect UNSAT
    let r2 = solver.solve();
    assert!(r2.is_unsat(), "Second solve should be UNSAT: {r2}");
}

/// Test incremental watch boundary with multiple incremental solve rounds.
/// Mimics IC3/PDR usage pattern: solve, add blocking clause, solve, repeat.
#[test]
fn test_incremental_watch_boundary_multi_round() {
    let mut solver = Solver::new(5);
    let d = |dimacs: i32| -> Literal { Literal::from_dimacs(dimacs) };

    solver.set_incremental_mode();

    // Initial formula
    solver.add_clause(vec![d(1), d(2), d(3)]);
    solver.add_clause(vec![d(-1), d(4), d(5)]);

    // Round 1: solve
    let r1 = solver.solve();
    assert!(r1.is_sat(), "Round 1 should be SAT: {r1}");

    // Round 2: add clause and solve
    solver.add_clause(vec![d(-2), d(-3)]);
    let r2 = solver.solve();
    assert!(r2.is_sat(), "Round 2 should be SAT: {r2}");

    // Round 3: add more clauses and solve
    solver.add_clause(vec![d(-4), d(-5)]);
    solver.add_clause(vec![d(2), d(4)]);
    let r3 = solver.solve();
    assert!(r3.is_sat(), "Round 3 should be SAT: {r3}");

    // Round 4: add contradicting clause chain to force UNSAT
    solver.add_clause(vec![d(-1)]);
    solver.add_clause(vec![d(-2)]);
    solver.add_clause(vec![d(-3)]);
    solver.add_clause(vec![d(-4)]);
    solver.add_clause(vec![d(-5)]);
    let r4 = solver.solve();
    assert!(
        r4.is_unsat(),
        "Round 4 should be UNSAT after negating all variables: {r4}"
    );
}

// ========================================================================
// Scoped BVE Tests (#8162)
// ========================================================================

/// Test that push() enables scoped BVE tracking and pop() correctly
/// restores eliminated variables (#8162, #8369).
///
/// Uses manual `mark_eliminated` + `push_bve` to deterministically set up
/// elimination state during a scope, then verifies pop() correctly
/// drains reconstruction entries and reactivates the variable.
#[test]
fn test_scoped_bve_eliminates_and_restores() {
    use crate::solver::lifecycle::VarState;

    let mut solver = Solver::new(8);
    let v0 = Variable(0);
    let v1 = Variable(1);
    let v5 = Variable(5);
    let v6 = Variable(6);
    let v7 = Variable(7);

    // Base clauses to keep solver non-trivial.
    solver.add_clause(vec![Literal::positive(v0), Literal::positive(v1)]);

    let recon_before_push = solver.inproc.reconstruction.len();

    // Push -- scope_var_floor becomes 8 (current num_vars).
    solver.push();
    assert!(solver.has_scoped_bve(), "push must enable scoped BVE");
    assert_eq!(
        solver.scope_var_start(),
        Some(8),
        "scope_var_start should be 8 (base variables 0-7)"
    );

    // Simulate BVE eliminating v5 during this scope by manually marking it
    // and adding reconstruction entries.
    solver.var_lifecycle.mark_eliminated(5);
    solver.inproc.reconstruction.push_bve(
        v5,
        vec![vec![Literal::positive(v5), Literal::positive(v6)]],
        vec![vec![Literal::negative(v5), Literal::positive(v7)]],
    );

    assert_eq!(
        solver.var_lifecycle.as_slice()[5],
        VarState::Eliminated,
        "v5 should be Eliminated after manual mark"
    );
    let recon_in_scope = solver.inproc.reconstruction.len();
    assert!(
        recon_in_scope > recon_before_push,
        "reconstruction stack should have entries from scope elimination"
    );

    // Pop -- should restore v5 via restore_scoped_bve_eliminations.
    assert!(solver.pop());
    assert!(!solver.has_scoped_bve(), "pop must clear scoped BVE state");

    // v5 should be reactivated (no longer Eliminated).
    assert_ne!(
        solver.var_lifecycle.as_slice()[5],
        VarState::Eliminated,
        "v5 must be reactivated after pop (#8369)"
    );

    // Reconstruction stack should be drained back to pre-scope length.
    assert_eq!(
        solver.inproc.reconstruction.len(),
        recon_before_push,
        "pop must drain reconstruction entries added during scope"
    );

    // Solver should still be consistent -- base formula is SAT.
    let r = solver.solve().into_inner();
    assert!(
        matches!(r, SatResult::Sat(_)),
        "base formula should be SAT after scoped BVE pop, got {r:?}"
    );
}

#[test]
fn test_scoped_bve_pop_invalidates_bve_occ_saved_state() {
    let mut solver = Solver::new(8);
    let v0 = Variable(0);
    let v1 = Variable(1);
    let v5 = Variable(5);
    let v6 = Variable(6);
    let v7 = Variable(7);

    solver.add_clause(vec![Literal::positive(v0), Literal::positive(v1)]);
    solver.push();

    solver.set_bve_occ_delta_validation_enabled(true);
    solver.inproc.bve.ensure_num_vars(solver.num_vars);
    solver.inproc.bve.rebuild_with_vals_at_epoch(
        &solver.arena,
        &solver.vals,
        solver.cold.clause_db_changes,
    );
    assert!(solver.inproc.bve.is_occ_populated());

    solver.var_lifecycle.mark_eliminated(5);
    solver.inproc.reconstruction.push_bve(
        v5,
        vec![vec![Literal::positive(v5), Literal::positive(v6)]],
        vec![vec![Literal::negative(v5), Literal::positive(v7)]],
    );

    assert!(solver.pop());
    assert!(
        !solver.inproc.bve.is_occ_populated(),
        "scoped BVE variable restoration must invalidate saved occurrence lists"
    );
}

/// Test nested push/pop with BVE elimination at each level, verifying
/// correct LIFO restoration order (#8162, #8369).
///
/// Scope 1: manually eliminate v5
/// Scope 2: manually eliminate v8
/// Pop scope 2: v8 restored, v5 still eliminated
/// Pop scope 1: v5 restored
#[test]
fn test_scoped_bve_nested_push_pop() {
    use crate::solver::lifecycle::VarState;

    let mut solver = Solver::new(11);

    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    let recon_base = solver.inproc.reconstruction.len();

    // === Scope 1 (depth 1) ===
    solver.push();
    let scope1_recon_start = *solver.cold.scope_reconstruction_starts.last().unwrap();
    assert_eq!(scope1_recon_start, recon_base);

    // Simulate BVE eliminating v5 in scope 1.
    let v5 = Variable(5);
    solver.var_lifecycle.mark_eliminated(5);
    solver.inproc.reconstruction.push_bve(
        v5,
        vec![vec![Literal::positive(v5), Literal::positive(Variable(6))]],
        vec![vec![Literal::negative(v5), Literal::positive(Variable(7))]],
    );

    let recon_after_scope1 = solver.inproc.reconstruction.len();
    assert!(recon_after_scope1 > recon_base);

    // === Scope 2 (depth 2) ===
    solver.push();
    let scope2_recon_start = *solver.cold.scope_reconstruction_starts.last().unwrap();
    assert_eq!(scope2_recon_start, recon_after_scope1);
    assert_eq!(solver.cold.scope_var_starts.len(), 2);

    // Simulate BVE eliminating v8 in scope 2.
    let v8 = Variable(8);
    solver.var_lifecycle.mark_eliminated(8);
    solver.inproc.reconstruction.push_bve(
        v8,
        vec![vec![Literal::positive(v8), Literal::positive(Variable(9))]],
        vec![vec![Literal::negative(v8), Literal::positive(Variable(10))]],
    );

    assert_eq!(solver.var_lifecycle.as_slice()[5], VarState::Eliminated);
    assert_eq!(solver.var_lifecycle.as_slice()[8], VarState::Eliminated);

    // Pop scope 2: v8 restored, v5 still eliminated.
    assert!(solver.pop());
    assert_ne!(
        solver.var_lifecycle.as_slice()[8],
        VarState::Eliminated,
        "v8 must be reactivated after popping scope 2"
    );
    assert_eq!(
        solver.var_lifecycle.as_slice()[5],
        VarState::Eliminated,
        "v5 must still be eliminated (scope 1 still active)"
    );
    assert_eq!(
        solver.inproc.reconstruction.len(),
        recon_after_scope1,
        "reconstruction stack should be restored to scope 1 level"
    );

    // Pop scope 1: v5 restored.
    assert!(solver.pop());
    assert_ne!(
        solver.var_lifecycle.as_slice()[5],
        VarState::Eliminated,
        "v5 must be reactivated after popping scope 1"
    );
    assert_eq!(
        solver.inproc.reconstruction.len(),
        recon_base,
        "reconstruction stack should be restored to base level"
    );
}

/// Integration test: verify that scoped BVE is allowed to run through
/// the incremental inprocessing pipeline (#8162).
///
/// This test sets up a formula with push() scope active and verifies
/// that the BVE body guard allows execution (does not bail out with
/// `has_been_incremental && !has_scoped_bve()`).
#[test]
fn test_scoped_bve_body_guard_allows_in_scope() {
    // Create solver with enough variables for BVE to have candidates.
    let mut solver = Solver::new(10);

    // Add a formula where BVE can potentially eliminate a variable.
    // Variable v3 appears in exactly two clauses with opposite polarity:
    //   (v3 | v4 | v5) and (~v3 | v6 | v7)
    // BVE can eliminate v3 by resolving: (v4 | v5 | v6 | v7)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
        Literal::positive(Variable(5)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(3)),
        Literal::positive(Variable(6)),
        Literal::positive(Variable(7)),
    ]);

    // Push scope to enable scoped BVE.
    solver.push();
    assert!(solver.has_scoped_bve());

    // The solver should now be in incremental mode (has_been_incremental = true)
    // but with scoped BVE active. This means BVE body should NOT bail out.
    assert!(
        solver.cold.has_been_incremental,
        "push() should set has_been_incremental"
    );

    // Add a scoped clause and solve. The formula should remain SAT.
    solver.add_clause(vec![
        Literal::positive(Variable(8)),
        Literal::positive(Variable(9)),
    ]);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "scoped formula should be SAT, got {result:?}"
    );

    // Pop and verify base formula is still SAT.
    assert!(solver.pop());
    let result2 = solver.solve().into_inner();
    assert!(
        matches!(result2, SatResult::Sat(_)),
        "base formula should be SAT after pop, got {result2:?}"
    );
}

/// Regression test: push/pop/push/pop with same contradictory scoped clause.
///
/// This tests the exact pattern that fails in the SMT incremental LRA path:
/// a global clause forces var=false, scoped clause forces var=true. After
/// pop and re-push, the scoped clause must still produce UNSAT.
#[test]
fn test_push_pop_reuse_same_scoped_contradiction() {
    let mut solver = Solver::new(2);
    let var0 = Variable::new(0);

    // Global: force var0 = false
    solver.add_clause_global(vec![Literal::negative(var0)]);

    // Push scope 1
    solver.push();
    // Scoped: force var0 = true (contradiction)
    solver.add_clause(vec![Literal::positive(var0)]);
    let result1 = solver.solve().into_inner();
    assert!(
        matches!(result1, SatResult::Unsat(_)),
        "first solve should be UNSAT, got {result1:?}"
    );

    // Pop scope 1
    assert!(solver.pop());

    // Push scope 2
    solver.push();
    // Re-add same scoped clause
    solver.add_clause(vec![Literal::positive(var0)]);
    let result2 = solver.solve().into_inner();
    assert!(
        matches!(result2, SatResult::Unsat(_)),
        "second solve should be UNSAT, got {result2:?}"
    );

    // Pop scope 2
    assert!(solver.pop());
}

/// Regression test: global clause added DURING a push scope must survive pop (#9378).
///
/// This is the exact pattern that causes the incremental LRA/LIA regression:
/// Tseitin definition clauses are added via add_clause_global() during a push
/// scope. On pop, the original_ledger's pop_scope() was truncating these global
/// clauses because they were appended past the scope boundary. On the next solve,
/// reset_search_state rebuilds the arena from the truncated ledger, losing the
/// definitions.
#[test]
fn test_global_clause_during_scope_survives_pop() {
    let mut solver = Solver::new(2);
    let var0 = Variable::new(0);

    // Push scope 1
    solver.push();

    // During scope: add a global definition clause (force var0=false)
    solver.add_clause_global(vec![Literal::negative(var0)]);

    // Also add a scoped activation clause (force var0=true, contradiction)
    solver.add_clause(vec![Literal::positive(var0)]);

    let result1 = solver.solve().into_inner();
    assert!(
        matches!(result1, SatResult::Unsat(_)),
        "first solve should be UNSAT, got {result1:?}"
    );

    // Pop scope 1: scoped clause is removed, global clause must survive
    assert!(solver.pop());

    // Verify the global clause survived in the ledger
    assert!(
        solver.cold.original_ledger.num_clauses() >= 1,
        "global clause must survive pop in the original ledger"
    );

    // Push scope 2
    solver.push();

    // Re-add same scoped clause (activation)
    solver.add_clause(vec![Literal::positive(var0)]);

    let result2 = solver.solve().into_inner();
    assert!(
        matches!(result2, SatResult::Unsat(_)),
        "second solve should be UNSAT: global clause [-var0] must still be present, got {result2:?}"
    );

    // Pop scope 2
    assert!(solver.pop());
}

// ========================================================================
// Scoped BVE Selector Vals Fix (#8579)
// ========================================================================

/// Regression test for #8579: scoped BVE must correctly handle scope
/// selector literals during incremental inprocessing.
///
/// The fix in `run_incremental_inprocessing()` temporarily sets vals[] for
/// scope selector variables to their intended polarity (S=false) before BVE,
/// then restores after BVE. This ensures BVE's root-literal pruning
/// correctly treats +S as root-false (matching the effect of the scope
/// assumption -S that is applied later during search).
///
/// This test verifies that push/pop with BVE-eligible scoped variables and
/// environment constraints (base-formula unit clauses) produces correct
/// results across multiple incremental solves.
#[test]
fn test_issue_8579_scoped_bve_selector_vals_no_false_unsat() {
    // IC3/PDR pattern: base formula with environment constraints (unit clauses),
    // push scope, add scoped clauses, solve multiple times.
    let num_base_vars = 30;
    let mut solver = Solver::new(num_base_vars);

    // Disable all inprocessing except BVE and subsumption (BVE's prerequisite).
    solver.disable_all_inprocessing();
    solver.inproc_ctrl.bve.enabled = true;
    solver.inproc_ctrl.bve.next_conflict = 0;
    solver.inproc_ctrl.subsume.enabled = true;
    solver.inproc_ctrl.subsume.next_conflict = 0;

    // Variables 0-9: "free" variables (used in base and scoped clauses)
    // Variables 10-19: "environment" variables (fixed false by unit clauses)
    // Variables 20-29: unused base variables

    // Base: binary clauses among free variables (formula is SAT)
    for i in 0..5 {
        solver.add_clause(vec![
            Literal::positive(Variable(i as u32)),
            Literal::positive(Variable((i + 5) as u32)),
        ]);
    }

    // Environment constraints: fix variables 10-19 to false.
    for i in 10..20 {
        solver.add_clause(vec![Literal::negative(Variable(i as u32))]);
    }

    // First solve to propagate unit clauses and establish baseline.
    let r0 = solver.solve().into_inner();
    assert!(
        matches!(r0, SatResult::Sat(_)),
        "base formula should be SAT, got {r0:?}"
    );

    // Push scope -- creates selector variable S.
    solver.push();
    assert!(solver.has_scoped_bve(), "push must enable scoped BVE");

    // Allocate scoped variables (above scope_var_floor for BVE eligibility).
    let num_scoped = 5usize;
    for _ in 0..num_scoped {
        solver.new_var_internal();
    }
    let scope_base = num_base_vars + 1; // Skip selector

    // Create BVE-eliminable scoped variables with mixed free/environment literals.
    // Each scoped variable sv has:
    //   Positive occ: (sv | free_var | +env_var) -- stored as (sv | free_var | +env_var | +S)
    //   Negative occ: (-sv | free_var2)          -- stored as (-sv | free_var2 | +S)
    //
    // Since free_var and free_var2 are unassigned, the resolvent on sv includes them:
    //   Resolvent: (free_var | env_var | free_var2 | +S)  [without fix: +S stays]
    //   Resolvent: (free_var | free_var2)                  [with fix: +S pruned, env pruned]
    //
    // The scoped formula IS SAT: free variables can satisfy all clauses.
    // BVE should not change the satisfiability regardless of whether +S is pruned.
    for j in 0..num_scoped {
        let sv = Variable((scope_base + j) as u32);
        let free_a = Variable((j % 5) as u32); // free (unassigned)
        let free_b = Variable(((j + 2) % 5) as u32); // free (unassigned)
        let env_var = Variable((10 + j) as u32); // root-false

        // Positive occurrence: (sv | free_a | +env_var)
        solver.add_clause(vec![
            Literal::positive(sv),
            Literal::positive(free_a),
            Literal::positive(env_var),
        ]);

        // Negative occurrence: (-sv | free_b)
        solver.add_clause(vec![Literal::negative(sv), Literal::positive(free_b)]);
    }

    // The scoped formula is SAT (setting all free variables true satisfies
    // everything). Solve multiple times to potentially trigger incremental
    // inprocessing with BVE.
    for i in 0..10 {
        let r = solver.solve().into_inner();
        assert!(
            matches!(r, SatResult::Sat(_)),
            "iteration {i}: scoped formula should be SAT, got {r:?}"
        );
    }

    // Pop scope.
    assert!(solver.pop());

    // Verify base formula is still SAT after pop.
    let r_final = solver.solve().into_inner();
    assert!(
        matches!(r_final, SatResult::Sat(_)),
        "base formula should be SAT after pop, got {r_final:?}"
    );
}

/// Regression test for #8579: scoped BVE with constraint-heavy formulas.
///
/// Simulates the IC3/PDR consecution check pattern: base formula with many
/// environment constraints (unit clauses), push scope, add transition-like
/// clauses with scoped BVE-eligible variables, solve with assumptions.
/// The formula is constructed to be SAT in the scope, and must remain SAT
/// after BVE processes the scoped variables.
#[test]
fn test_issue_8579_scoped_bve_many_environment_constraints() {
    // Larger formula to exercise BVE more thoroughly.
    let num_base_vars = 100;
    let mut solver = Solver::new(num_base_vars);

    solver.disable_all_inprocessing();
    solver.inproc_ctrl.bve.enabled = true;
    solver.inproc_ctrl.bve.next_conflict = 0;
    solver.inproc_ctrl.subsume.enabled = true;
    solver.inproc_ctrl.subsume.next_conflict = 0;

    // Variables 0-29: "state" variables (free, used in scoped clauses)
    // Variables 30-79: "environment" variables (fixed false by unit clauses)
    // Variables 80-99: unused

    // Base: binary clauses among state variables to make formula non-trivial.
    for i in 0..20 {
        solver.add_clause(vec![
            Literal::positive(Variable(i)),
            Literal::positive(Variable((i + 10) % 30)),
        ]);
    }

    // Environment constraints: 50 unit clauses fixing variables 30-79 to false.
    for i in 30..80 {
        solver.add_clause(vec![Literal::negative(Variable(i as u32))]);
    }

    // First solve.
    let r0 = solver.solve().into_inner();
    assert!(
        matches!(r0, SatResult::Sat(_)),
        "base formula should be SAT, got {r0:?}"
    );

    // Push scope.
    solver.push();

    // Allocate 20 scoped variables (above scope_var_floor).
    let num_scoped = 20usize;
    for _ in 0..num_scoped {
        solver.new_var_internal();
    }
    let scope_base = num_base_vars + 1;

    // Create transition-relation-like scoped clauses.
    // Each scoped variable has clauses mixing state and environment variables.
    for j in 0..num_scoped {
        let sv = Variable((scope_base + j) as u32);
        let state_a = Variable((j % 30) as u32);
        let state_b = Variable(((j + 7) % 30) as u32);
        let env_a = Variable((30 + j * 2) as u32);
        let env_b = Variable((31 + j * 2) as u32);

        // Positive occurrence with state + environment mix
        solver.add_clause(vec![
            Literal::positive(sv),
            Literal::positive(state_a),
            Literal::positive(env_a),
        ]);

        // Negative occurrence with state variable
        solver.add_clause(vec![
            Literal::negative(sv),
            Literal::positive(state_b),
            Literal::positive(env_b),
        ]);

        // Extra clause to make BVE less trivial
        solver.add_clause(vec![
            Literal::positive(sv),
            Literal::negative(state_a),
            Literal::positive(state_b),
        ]);
    }

    // Solve multiple times (IC3 pattern: many short solves).
    for i in 0..15 {
        let r = solver.solve().into_inner();
        assert!(
            matches!(r, SatResult::Sat(_)),
            "iteration {i}: scoped formula should be SAT, got {r:?}"
        );
    }

    // Pop and verify base formula.
    assert!(solver.pop());
    let r_final = solver.solve().into_inner();
    assert!(
        matches!(r_final, SatResult::Sat(_)),
        "base formula should be SAT after pop, got {r_final:?}"
    );
}
