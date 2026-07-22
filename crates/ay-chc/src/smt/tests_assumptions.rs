// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for smt/assumptions.rs — assumption-based solving with UNSAT core.

#![allow(clippy::unwrap_used)]

use super::context::SmtContext;
use super::types::{SmtResult, SmtValue};
use crate::{ChcExpr, ChcSort, ChcVar};

// ---------------------------------------------------------------------------
// Empty assumptions delegates to check_sat
// ---------------------------------------------------------------------------

/// Empty assumptions on a SAT background returns SAT.
#[test]
fn test_assumption_conjuncts_empty_assumptions_delegates_to_check_sat() {
    let mut ctx = SmtContext::new();
    let background = vec![ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(5),
    )];
    let result = ctx.check_sat_with_assumption_conjuncts(&background, &[]);

    assert!(
        matches!(result, SmtResult::Sat(_)),
        "empty assumptions + SAT background should return SAT, got {result:?}"
    );
}

/// Empty assumptions on UNSAT background returns UNSAT.
#[test]
fn test_assumption_conjuncts_empty_assumptions_unsat_background() {
    let mut ctx = SmtContext::new();
    let background = vec![ChcExpr::Bool(false)];
    let result = ctx.check_sat_with_assumption_conjuncts(&background, &[]);

    assert!(
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "empty assumptions + UNSAT background should return UNSAT, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Basic assumption SAT/UNSAT
// ---------------------------------------------------------------------------

/// SAT background with SAT assumption returns SAT model.
#[test]
fn test_assumption_conjuncts_sat_with_model() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let background = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let assumptions = vec![ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5))];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    match result {
        SmtResult::Sat(model) => {
            assert_eq!(
                model.get("x"),
                Some(&SmtValue::Int(5)),
                "model should have x = 5"
            );
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Background + assumption contradiction → UNSAT with core.
#[test]
fn test_assumption_conjuncts_contradiction_returns_unsat_with_core() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    // Background: x = 1
    let background = vec![ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1))];
    // Assumption: x = 2 (contradicts background)
    let assumptions = vec![ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(2))];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    assert!(
        matches!(
            result,
            SmtResult::UnsatWithCore(_) | SmtResult::Unsat | SmtResult::UnsatWithFarkas(_)
        ),
        "contradictory assumption should return UNSAT, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Transitive equality contradiction detection (#2445)
// ---------------------------------------------------------------------------

/// Contradiction from transitive equality closure: A=B, A=1, B=2 → UNSAT.
#[test]
fn test_assumption_conjuncts_transitive_equality_contradiction() {
    let mut ctx = SmtContext::new();
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    // Background: a = b, a = 1
    let background = vec![
        ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ChcExpr::eq(ChcExpr::var(a), ChcExpr::int(1)),
    ];
    // Assumption: b = 2 (contradicts a = b AND a = 1)
    let assumptions = vec![ChcExpr::eq(ChcExpr::var(b), ChcExpr::int(2))];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    assert!(
        matches!(
            result,
            SmtResult::UnsatWithCore(_) | SmtResult::Unsat | SmtResult::UnsatWithFarkas(_)
        ),
        "transitive equality contradiction should return UNSAT, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Multiple assumptions
// ---------------------------------------------------------------------------

/// Multiple consistent assumptions produce SAT with combined model.
#[test]
fn test_assumption_conjuncts_multiple_assumptions_sat() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let background = vec![ChcExpr::Bool(true)];
    let assumptions = vec![
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(3)),
        ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(7)),
    ];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    match result {
        SmtResult::Sat(model) => {
            assert_eq!(model.get("x"), Some(&SmtValue::Int(3)));
            assert_eq!(model.get("y"), Some(&SmtValue::Int(7)));
        }
        other => panic!("expected Sat for consistent multiple assumptions, got {other:?}"),
    }
}

/// Multiple contradictory assumptions produce UNSAT.
#[test]
fn test_assumption_conjuncts_multiple_contradictory_assumptions() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let background = vec![ChcExpr::Bool(true)];
    let assumptions = vec![
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(2)),
    ];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    assert!(
        matches!(
            result,
            SmtResult::UnsatWithCore(_) | SmtResult::Unsat | SmtResult::UnsatWithFarkas(_)
        ),
        "contradictory assumptions should return UNSAT, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Bound reasoning across background + assumptions
// ---------------------------------------------------------------------------

/// Background lower bound + assumption upper bound with tight window → SAT.
#[test]
fn test_assumption_conjuncts_bound_reasoning_sat() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let background = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let assumptions = vec![ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10))];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    match result {
        SmtResult::Sat(model) => {
            if let Some(SmtValue::Int(v)) = model.get("x") {
                assert!(*v >= 0 && *v <= 10, "x should be in [0, 10], got {v}");
            }
        }
        other => panic!("expected Sat for bounded range, got {other:?}"),
    }
}

/// Background + assumption bounds with empty range → UNSAT.
#[test]
fn test_assumption_conjuncts_bound_reasoning_unsat() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    // x >= 10
    let background = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10))];
    // x < 5 (empty range)
    let assumptions = vec![ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(5))];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    assert!(
        matches!(
            result,
            SmtResult::UnsatWithCore(_) | SmtResult::Unsat | SmtResult::UnsatWithFarkas(_)
        ),
        "empty bound range should return UNSAT, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// IncrementalQueryContext lifecycle
// ---------------------------------------------------------------------------

/// IncrementalQueryContext: assert_background → finalize → push → check_sat_incremental → pop.
#[test]
fn test_incremental_context_lifecycle_sat() {
    use super::incremental::IncrementalQueryContext;

    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();

    // Assert background: x >= 0
    let x = ChcVar::new("x", ChcSort::Int);
    let bg = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    inc.assert_background(&bg, &mut smt);

    // Finalize
    inc.finalize_background(&smt);

    // Push (no-op but exercises API)
    inc.push();

    // Check with assumption x = 5
    let assumption = vec![ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5))];
    let result = inc.check_sat_incremental(&assumption, &mut smt, None);

    // Pop (no-op but exercises API)
    inc.pop();

    assert!(
        matches!(result, super::incremental::IncrementalCheckResult::Sat(_)),
        "incremental check with consistent assumption should return SAT, got {result:?}"
    );
}

/// IncrementalQueryContext: UNSAT assumption against background.
#[test]
fn test_incremental_context_lifecycle_unsat() {
    use super::incremental::IncrementalQueryContext;

    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();

    // Assert background: x = 1
    let x = ChcVar::new("x", ChcSort::Int);
    let bg = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1));
    inc.assert_background(&bg, &mut smt);
    inc.finalize_background(&smt);

    inc.push();

    // Check with contradictory assumption: x = 2
    let assumption = vec![ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(2))];
    let result = inc.check_sat_incremental(&assumption, &mut smt, None);

    inc.pop();

    assert!(
        matches!(result, super::incremental::IncrementalCheckResult::Unsat),
        "contradictory incremental assumption should return UNSAT, got {result:?}"
    );
}

/// IncrementalQueryContext: multiple push/pop cycles with different assumptions.
#[test]
fn test_incremental_context_multiple_cycles() {
    use super::incremental::IncrementalQueryContext;

    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let bg = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    inc.assert_background(&bg, &mut smt);
    inc.finalize_background(&smt);

    // First cycle: x = 5
    inc.push();
    let r1 = inc.check_sat_incremental(
        &[ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5))],
        &mut smt,
        None,
    );
    inc.pop();
    assert!(
        matches!(r1, super::incremental::IncrementalCheckResult::Sat(_)),
        "first cycle should be SAT"
    );

    // Second cycle: x = -1 (violates x >= 0)
    inc.push();
    let r2 = inc.check_sat_incremental(
        &[ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(-1))],
        &mut smt,
        None,
    );
    inc.pop();
    assert!(
        matches!(r2, super::incremental::IncrementalCheckResult::Unsat),
        "second cycle should be UNSAT (x=-1 violates x>=0)"
    );

    // Third cycle: x = 10 (should still work after UNSAT)
    inc.push();
    let r3 = inc.check_sat_incremental(
        &[ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(10))],
        &mut smt,
        None,
    );
    inc.pop();
    assert!(
        matches!(r3, super::incremental::IncrementalCheckResult::Sat(_)),
        "third cycle should be SAT (solver reusable after UNSAT)"
    );
}

// ---------------------------------------------------------------------------
// new_assumption_sat_solver
// ---------------------------------------------------------------------------

/// new_assumption_sat_solver creates a solver with preprocessing disabled.
#[test]
fn test_new_assumption_sat_solver_preprocessing_disabled() {
    let sat = super::assumptions::new_assumption_sat_solver(10);
    // Assumption-mode solvers disable preprocessing to avoid distorting
    // assumption-sensitive clauses. Verify the flag is correctly set.
    assert!(
        !sat.is_preprocess_enabled(),
        "assumption solver should have preprocessing disabled"
    );
}

// ---------------------------------------------------------------------------
// Conversion budget strikes (#2472)
// ---------------------------------------------------------------------------

/// After MAX_CONVERSION_STRIKES consecutive budget-exceeded checks,
/// check_sat_with_assumption_conjuncts short-circuits to Unknown.
#[test]
fn test_assumption_budget_strikes_short_circuit_to_unknown() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let bg = vec![ChcExpr::Bool(true)];
    let assumptions = vec![ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1))];

    // Simulate MAX_CONVERSION_STRIKES consecutive budget exceedances.
    ctx.conversion_budget_exceeded = true;
    ctx.conversion_budget_strikes = super::context::MAX_CONVERSION_STRIKES;

    let result = ctx.check_sat_with_assumption_conjuncts(&bg, &assumptions);
    assert!(
        matches!(result, SmtResult::Unknown),
        "should short-circuit to Unknown after MAX_CONVERSION_STRIKES, got {result:?}"
    );
}

/// A single budget exceedance increments strikes but doesn't short-circuit.
#[test]
fn test_assumption_budget_single_strike_does_not_short_circuit() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let bg = vec![ChcExpr::Bool(true)];
    let assumptions = vec![ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1))];

    // Simulate one prior budget exceedance (strikes = 1, < MAX).
    ctx.conversion_budget_exceeded = true;
    ctx.conversion_budget_strikes = 1;

    let result = ctx.check_sat_with_assumption_conjuncts(&bg, &assumptions);
    // Should NOT short-circuit (strikes incremented to 2, but MAX is 3).
    assert!(
        !matches!(result, SmtResult::Unknown),
        "single strike should not short-circuit to Unknown, got {result:?}"
    );
}

/// Strikes reset to 0 when the previous check did NOT exceed budget.
#[test]
fn test_assumption_budget_strikes_reset_on_success() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let bg = vec![ChcExpr::Bool(true)];
    let assumptions = vec![ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1))];

    // Simulate prior strikes that accumulated but last check succeeded.
    ctx.conversion_budget_exceeded = false;
    ctx.conversion_budget_strikes = 2;

    let result = ctx.check_sat_with_assumption_conjuncts(&bg, &assumptions);
    // Strikes should reset to 0 (exceeded was false), then proceed normally.
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "strikes should reset after non-exceeded check, got {result:?}"
    );
    assert_eq!(
        ctx.conversion_budget_strikes, 0,
        "strikes should be 0 after a non-exceeded check"
    );
}

// ---------------------------------------------------------------------------
// False assumption fast path
// ---------------------------------------------------------------------------

/// A single `false` assumption short-circuits to UNSAT with core containing it.
#[test]
fn test_assumption_false_assumption_returns_unsat_core() {
    let mut ctx = SmtContext::new();
    let bg = vec![ChcExpr::Bool(true)];
    let false_assumption = ChcExpr::Bool(false);
    let assumptions = vec![false_assumption];

    let result = ctx.check_sat_with_assumption_conjuncts(&bg, &assumptions);

    match result {
        SmtResult::UnsatWithCore(core) => {
            assert_eq!(
                core.conjuncts.len(),
                1,
                "core should contain exactly the false assumption"
            );
            assert_eq!(
                core.conjuncts[0],
                ChcExpr::Bool(false),
                "core should contain the original false assumption"
            );
        }
        other => panic!("false assumption should return UnsatWithCore, got {other:?}"),
    }
}

/// Multiple assumptions where one normalizes to false: returns UNSAT core
/// with just the false one.
#[test]
fn test_assumption_mixed_with_false_returns_unsat_core_for_false() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let bg = vec![ChcExpr::Bool(true)];
    // Second assumption is x=5 (SAT), but first assumption is x>0 ∧ false → false
    let false_expr = ChcExpr::Bool(false);
    let assumptions = vec![ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5)), false_expr];

    let result = ctx.check_sat_with_assumption_conjuncts(&bg, &assumptions);

    // The false assumption triggers the fast path after normalization.
    // Iteration order means x=5 is processed first (passes), then false triggers return.
    match result {
        SmtResult::UnsatWithCore(core) => {
            assert_eq!(core.conjuncts.len(), 1);
            assert_eq!(core.conjuncts[0], ChcExpr::Bool(false));
        }
        other => panic!("false in assumptions should yield UnsatWithCore, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// True assumption filtering
// ---------------------------------------------------------------------------

/// An assumption that normalizes to `true` is skipped silently.
#[test]
fn test_assumption_true_assumption_skipped() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let bg = vec![ChcExpr::Bool(true)];
    let assumptions = vec![
        ChcExpr::Bool(true), // should be skipped
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(42)),
    ];

    let result = ctx.check_sat_with_assumption_conjuncts(&bg, &assumptions);

    match result {
        SmtResult::Sat(model) => {
            assert_eq!(model.get("x"), Some(&SmtValue::Int(42)));
        }
        other => panic!("true assumption should be skipped, result should be SAT, got {other:?}"),
    }
}

/// All assumptions normalize to `true` — delegates to background-only check_sat.
#[test]
fn test_assumption_all_true_delegates_to_check_sat() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let bg = vec![ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(7))];
    // All assumptions are trivially true
    let assumptions = vec![ChcExpr::Bool(true), ChcExpr::Bool(true)];

    let result = ctx.check_sat_with_assumption_conjuncts(&bg, &assumptions);

    // All assumption_terms empty after filtering → delegates to check_sat on background.
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "all-true assumptions should delegate to check_sat and return SAT, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Transitive equality propagation into model (#2913)
// ---------------------------------------------------------------------------

/// Propagated equalities appear in model even if eliminated by preprocessing.
#[test]
fn test_assumption_propagated_equalities_in_model() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // Background: x = 5
    let bg = vec![ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5))];
    // Assumption: y = x (will be resolved via transitive closure to y = 5)
    let assumptions = vec![ChcExpr::eq(ChcExpr::var(y), ChcExpr::var(x))];

    let result = ctx.check_sat_with_assumption_conjuncts(&bg, &assumptions);

    match result {
        SmtResult::Sat(model) => {
            // y should be in the model via propagated equalities fallback
            if let Some(SmtValue::Int(yv)) = model.get("y") {
                assert_eq!(*yv, 5, "y should be 5 via transitive propagation");
            }
            // x should definitely be in the model
            if let Some(SmtValue::Int(xv)) = model.get("x") {
                assert_eq!(*xv, 5, "x should be 5");
            }
        }
        other => panic!("expected SAT with propagated equalities, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Empty background
// ---------------------------------------------------------------------------

/// Empty background + non-trivial assumption → behaves correctly.
#[test]
fn test_assumption_empty_background() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let bg: Vec<ChcExpr> = vec![];
    let assumptions = vec![ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(99))];

    let result = ctx.check_sat_with_assumption_conjuncts(&bg, &assumptions);

    match result {
        SmtResult::Sat(model) => {
            assert_eq!(model.get("x"), Some(&SmtValue::Int(99)));
        }
        other => panic!("empty background with consistent assumption should be SAT, got {other:?}"),
    }
}

/// Both background and assumptions empty → delegates to check_sat(true) → SAT.
#[test]
fn test_assumption_both_empty() {
    let mut ctx = SmtContext::new();
    let result = ctx.check_sat_with_assumption_conjuncts(&[], &[]);

    assert!(
        matches!(result, SmtResult::Sat(_)),
        "empty background + empty assumptions should be SAT, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Push/pop ordering with IncrementalQueryContext
// ---------------------------------------------------------------------------

/// Trivial background + finalize + push/check/pop works.
#[test]
fn test_incremental_push_without_finalize() {
    use super::incremental::IncrementalQueryContext;

    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();

    // assert_background + finalize_background required before push/check.
    // Use a trivial `true` background to satisfy the contract.
    inc.assert_background(&ChcExpr::Bool(true), &mut smt);
    inc.finalize_background(&smt);
    inc.push();
    let x = ChcVar::new("x", ChcSort::Int);
    let result = inc.check_sat_incremental(
        &[ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5))],
        &mut smt,
        None,
    );
    inc.pop();

    assert!(
        matches!(result, super::incremental::IncrementalCheckResult::Sat(_)),
        "trivial-background finalize + push should allow queries, got {result:?}"
    );
}

/// Nested push/pop maintains correct scoping (no-ops, but exercises ordering).
#[test]
fn test_incremental_nested_push_pop() {
    use super::incremental::IncrementalQueryContext;

    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let bg = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    inc.assert_background(&bg, &mut smt);
    inc.finalize_background(&smt);

    // Outer push/pop
    inc.push();

    // Inner push/pop with SAT query
    inc.push();
    let r1 = inc.check_sat_incremental(
        &[ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5))],
        &mut smt,
        None,
    );
    inc.pop();
    assert!(
        matches!(r1, super::incremental::IncrementalCheckResult::Sat(_)),
        "inner query should be SAT"
    );

    // Outer query after inner pop
    let r2 = inc.check_sat_incremental(
        &[ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(10))],
        &mut smt,
        None,
    );
    inc.pop();
    assert!(
        matches!(r2, super::incremental::IncrementalCheckResult::Sat(_)),
        "outer query after inner pop should be SAT"
    );
}

/// Pop without push is a no-op (defensive — doesn't panic).
#[test]
fn test_incremental_pop_without_push_is_noop() {
    use super::incremental::IncrementalQueryContext;

    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let bg = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    inc.assert_background(&bg, &mut smt);
    inc.finalize_background(&smt);

    // Pop without push — should not panic.
    inc.pop();

    // Context should still be usable after spurious pop.
    inc.push();
    let result = inc.check_sat_incremental(
        &[ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0))],
        &mut smt,
        None,
    );
    inc.pop();

    assert!(
        matches!(result, super::incremental::IncrementalCheckResult::Sat(_)),
        "context should be usable after spurious pop, got {result:?}"
    );
}
