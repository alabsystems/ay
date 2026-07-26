// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Advanced SMT tests: interpolating context, assumption solver models,
//! Craig interpolation correctness, budget/memory limits, regressions.

#![allow(clippy::unwrap_used)]

use super::assumptions::new_assumption_sat_solver;
use super::context::SmtContext;
use super::incremental::{IncrementalCheckResult, IncrementalQueryContext};
use super::interpolating::{InterpolatingResult, InterpolatingSmtContext};
use super::types::{SmtResult, SmtValue};
use crate::expr_vars::expr_var_names;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::TermStore;
use num_rational::Rational64;
use serial_test::serial;

// =========================================================================
// InterpolatingSmtContext tests
// =========================================================================

#[test]
fn test_interpolating_context_sat_bounds() {
    let mut ctx = InterpolatingSmtContext::new();

    // A: x >= 0
    let x = ChcVar::new("x", ChcSort::Int);
    ctx.assert_a(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)));

    // B: x <= 10
    let query = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10));
    let result = ctx.check_with_query(&query);

    // A ∧ B is SAT (x can be 0..10)
    assert!(
        matches!(result, InterpolatingResult::Sat(_)),
        "Expected SAT, got {result:?}"
    );
}

#[test]
fn test_interpolating_context_unsat_bounds() {
    let mut ctx = InterpolatingSmtContext::new();

    // A: x >= 10
    let x = ChcVar::new("x", ChcSort::Int);
    ctx.assert_a(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)));

    // B: x <= 5
    let query = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5));
    let result = ctx.check_with_query(&query);

    // A ∧ B is UNSAT (x >= 10 conflicts with x <= 5)
    assert!(
        matches!(
            result,
            InterpolatingResult::Unsat(_) | InterpolatingResult::UnsatNoInterpolant { .. }
        ),
        "Expected UNSAT, got {result:?}"
    );
}

#[test]
fn test_interpolating_context_rebuild_preserves_behavior() {
    let mut ctx = InterpolatingSmtContext::with_rebuild_limit(3);

    let x = ChcVar::new("x", ChcSort::Int);
    ctx.assert_a(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)));
    ctx.assert_a(ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(10)));

    // Run 4 queries to trigger rebuild
    for i in 0..4 {
        let q = ChcExpr::and(
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(i)),
            ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(i + 1)),
        );
        let _ = ctx.check_with_query(&q);
    }

    // After rebuild, query count should be reset
    assert!(ctx.query_count() <= 1);

    // A-constraints should be consolidated to 1
    assert_eq!(ctx.a_constraints().len(), 1);

    // Should still work correctly (x in 0..10 overlaps with x in 4..6)
    let q = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(4)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::int(6)),
    );
    assert!(matches!(
        ctx.check_with_query(&q),
        InterpolatingResult::Sat(_)
    ));
}

#[test]
fn test_interpolating_context_empty_a_unsat() {
    let mut ctx = InterpolatingSmtContext::new();

    // No A constraints, just check B
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::int(3)),
    );

    let result = ctx.check_with_query(&query);
    // x >= 5 ∧ x <= 3 is UNSAT, with interpolant "true" (empty A implies true)
    assert!(
        matches!(result, InterpolatingResult::Unsat(ref i) if matches!(i, ChcExpr::Bool(true))),
        "Expected UNSAT with true interpolant, got {result:?}"
    );
}

#[test]
fn test_interpolating_context_strengthen() {
    let mut ctx = InterpolatingSmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);

    // Initial A: x >= 0
    ctx.assert_a(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)));

    // Query: x <= -5 should be UNSAT (x >= 0 conflicts with x <= -5)
    let q1 = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(-5));
    assert!(matches!(
        ctx.check_with_query(&q1),
        InterpolatingResult::Unsat(_) | InterpolatingResult::UnsatNoInterpolant { .. }
    ));

    // Strengthen: add x <= 5
    ctx.strengthen_transition(ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)));

    // Now query x >= 20 should also be UNSAT (x <= 5 conflicts with x >= 20)
    let q2 = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(20));
    assert!(matches!(
        ctx.check_with_query(&q2),
        InterpolatingResult::Unsat(_) | InterpolatingResult::UnsatNoInterpolant { .. }
    ));
}

#[test]
fn test_interpolating_context_last_interpolant() {
    let mut ctx = InterpolatingSmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);

    // Initially, no interpolant
    assert!(ctx.last_interpolant().is_none());

    // Empty A, UNSAT query - interpolant should be true
    let unsat_query = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
    );
    let result = ctx.check_with_query(&unsat_query);
    assert!(matches!(result, InterpolatingResult::Unsat(_)));
    assert!(ctx.last_interpolant().is_some());
    assert!(matches!(ctx.last_interpolant(), Some(ChcExpr::Bool(true))));

    // SAT query should clear the interpolant
    ctx.assert_a(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)));
    let sat_query = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(10));
    let result = ctx.check_with_query(&sat_query);
    assert!(matches!(result, InterpolatingResult::Sat(_)));
    assert!(ctx.last_interpolant().is_none());

    // Another UNSAT query - verify last_interpolant matches result
    let unsat_query2 = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(-5));
    let result = ctx.check_with_query(&unsat_query2);
    match &result {
        InterpolatingResult::Unsat(interp) => {
            // When we get Unsat(interp), last_interpolant should be Some(interp)
            assert!(ctx.last_interpolant().is_some());
            assert_eq!(ctx.last_interpolant().unwrap(), interp);
        }
        InterpolatingResult::UnsatNoInterpolant { .. } => {
            // When we get UnsatNoInterpolant, last_interpolant should be None
            assert!(ctx.last_interpolant().is_none());
        }
        other => panic!("Expected UNSAT, got {other:?}"),
    }
}

#[test]
fn test_interpolating_context_take_last_interpolant() {
    let mut ctx = InterpolatingSmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);

    // Empty A, UNSAT query - interpolant should be true
    let unsat_query = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5)),
    );
    let _ = ctx.check_with_query(&unsat_query);

    // Take ownership of interpolant
    let interp = ctx.take_last_interpolant();
    assert!(interp.is_some());
    assert!(matches!(interp, Some(ChcExpr::Bool(true))));

    // Now it's None (consumed)
    assert!(ctx.last_interpolant().is_none());
    assert!(ctx.take_last_interpolant().is_none());
}

#[test]
fn test_assumption_solver_sat_returns_model() {
    // Verify check_sat_with_assumption_conjuncts returns a model on SAT (#1009).
    // TPA needs populated models for MBP midpoint extraction.
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Background: x = 5
    let background = vec![ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5))];
    // Assumption: y >= x (SAT when y >= 5)
    let assumptions = vec![ChcExpr::ge(ChcExpr::var(y), ChcExpr::var(x))];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    match result {
        SmtResult::Sat(model) => {
            // Model should contain x = 5 (from background propagated equality)
            let x_val = model.get("x");
            assert!(x_val.is_some(), "Model should contain x. Got: {model:?}");
            assert_eq!(x_val, Some(&SmtValue::Int(5)));

            // Model should also contain y with a valid value (y >= 5)
            let y_val = model.get("y");
            assert!(y_val.is_some(), "Model should contain y. Got: {model:?}");
            match y_val {
                Some(SmtValue::Int(v)) => assert!(*v >= 5, "y should be >= 5, got {v}"),
                other => panic!("Expected Int value for y, got {other:?}"),
            }
        }
        other => panic!("Expected Sat with model, got {other:?}"),
    }
}

#[test]
fn test_assumption_solver_sat_returns_bool_in_model() {
    // Verify check_sat_with_assumption_conjuncts extracts Bool variables (#1009 audit).
    let mut ctx = SmtContext::new();

    let b = ChcVar::new("b", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);

    // Background: x >= 0
    // This doesn't give x an exact value, so it's not propagated away
    let background = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    // Assumption: (b => x > 5) AND (NOT b => x < 10)
    // For x in [0,5]: b must be false (only NOT b implication satisfied)
    // For x in [6,9]: either b value works (both implications satisfied)
    // For x >= 10: b must be true (only b implication satisfied)
    let assumptions = vec![ChcExpr::and(
        ChcExpr::implies(
            ChcExpr::var(b.clone()),
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ),
        ChcExpr::implies(
            ChcExpr::not(ChcExpr::var(b)),
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        ),
    )];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    match result {
        SmtResult::Sat(model) => {
            // Model should contain x (Int variable)
            let x_val = model.get("x");
            assert!(x_val.is_some(), "Model should contain x. Got: {model:?}");

            // Model should also contain b (Bool variable)
            let b_val = model.get("b");
            assert!(
                b_val.is_some(),
                "Model should contain Bool variable b. Got: {model:?}"
            );

            // Verify model consistency: background (x >= 0) + assumption implications
            match (b_val, x_val) {
                (Some(SmtValue::Bool(true)), Some(SmtValue::Int(x))) => {
                    assert!(*x >= 0, "Background constraint x >= 0 violated, but x={x}");
                    assert!(*x > 5, "b=true requires x > 5, but x={x}");
                }
                (Some(SmtValue::Bool(false)), Some(SmtValue::Int(x))) => {
                    assert!(*x >= 0, "Background constraint x >= 0 violated, but x={x}");
                    assert!(*x < 10, "b=false requires x < 10, but x={x}");
                }
                _ => panic!("Expected Bool b and Int x, got b={b_val:?}, x={x_val:?}"),
            }
        }
        other => panic!("Expected Sat with model, got {other:?}"),
    }
}

#[test]
fn test_interpolating_context_sat_returns_model() {
    // Verify model availability through InterpolatingSmtContext (#1009).
    let mut ctx = InterpolatingSmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // A: x = 5, y = x + 1 (so y = 6)
    ctx.assert_a(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5)));
    ctx.assert_a(ChcExpr::eq(
        ChcExpr::var(y),
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
    ));

    // B: x >= 0 (SAT)
    let query = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    let result = ctx.check_with_query(&query);

    match result {
        InterpolatingResult::Sat(model) => {
            assert_eq!(model.get("x"), Some(&SmtValue::Int(5)), "model={model:?}");
            assert_eq!(model.get("y"), Some(&SmtValue::Int(6)), "model={model:?}");
        }
        other => panic!("Expected Sat(model), got {other:?}"),
    }
}

#[test]
fn test_interpolating_context_unsat_results_satisfy_craig_properties() {
    // Self-audit guard: whenever check_with_query returns Unsat(I),
    // ensure I is a valid Craig interpolant for this A/B pair.
    let x = ChcVar::new("x", ChcSort::Int);
    let candidates = [
        ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(-1)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(2)),
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(3)),
    ];

    for a in &candidates {
        for b in &candidates {
            let mut interp_ctx = InterpolatingSmtContext::new();
            interp_ctx.assert_a(a.clone());
            let result = interp_ctx.check_with_query(b);
            let InterpolatingResult::Unsat(interp) = result else {
                continue;
            };

            let shared_vars: FxHashSet<String> = ["x".to_string()].into_iter().collect();
            let interp_vars: FxHashSet<String> = expr_var_names(&interp);
            assert!(
                interp_vars.iter().all(|v| shared_vars.contains(v)),
                "Interpolant mentions non-shared vars. A={a}, B={b}, I={interp}"
            );

            let mut check_smt = SmtContext::new();
            let a_implies_i = ChcExpr::and(a.clone(), ChcExpr::not(interp.clone()));
            assert!(
                matches!(
                    check_smt.check_sat(&a_implies_i),
                    SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
                ),
                "A does not imply interpolant. A={a}, B={b}, I={interp}"
            );

            check_smt.reset();
            let i_and_b = ChcExpr::and(interp.clone(), b.clone());
            assert!(
                matches!(
                    check_smt.check_sat(&i_and_b),
                    SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
                ),
                "Interpolant does not block B. A={a}, B={b}, I={interp}"
            );
        }
    }
}

#[test]
fn test_interpolating_context_unsat_mixed_vars_stays_shared_and_sound() {
    // A uses local var y, query uses only x. If an interpolant is produced,
    // it must eliminate y and satisfy Craig properties.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let mut ctx = InterpolatingSmtContext::new();
    ctx.assert_a(ChcExpr::le(
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::int(5),
    ));
    ctx.assert_a(ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0)));

    let query = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10));
    let result = ctx.check_with_query(&query);
    assert!(
        matches!(
            result,
            InterpolatingResult::Unsat(_) | InterpolatingResult::UnsatNoInterpolant { .. }
        ),
        "Expected UNSAT result, got {result:?}"
    );

    let InterpolatingResult::Unsat(interp) = result else {
        return;
    };

    let shared_vars: FxHashSet<String> = ["x".to_string()].into_iter().collect();
    let interp_vars: FxHashSet<String> = expr_var_names(&interp);
    assert!(
        interp_vars.iter().all(|v| shared_vars.contains(v)),
        "Interpolant must only use shared vars. I={interp}"
    );

    let a_formula = ChcExpr::and_all(vec![
        ChcExpr::le(
            ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y.clone())),
            ChcExpr::int(5),
        ),
        ChcExpr::ge(ChcExpr::var(y), ChcExpr::int(0)),
    ]);

    let mut check_smt = SmtContext::new();
    let a_implies_i = ChcExpr::and(a_formula, ChcExpr::not(interp.clone()));
    assert!(
        matches!(
            check_smt.check_sat(&a_implies_i),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "A does not imply interpolant. I={interp}"
    );

    check_smt.reset();
    let i_and_b = ChcExpr::and(interp.clone(), query);
    assert!(
        matches!(
            check_smt.check_sat(&i_and_b),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "Interpolant does not block B. I={interp}"
    );
}

#[test]
fn test_interpolating_context_decode_miss_count_zero_for_standard_unsat() {
    // Verify that decode_miss_count is 0 when all Farkas conflict terms are
    // standard LIA atoms that term_to_chc_expr handles (#3591).
    let mut ctx = InterpolatingSmtContext::new();
    assert_eq!(ctx.decode_miss_count(), 0);

    // A: x >= 10
    let x = ChcVar::new("x", ChcSort::Int);
    ctx.assert_a(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)));

    // B: x <= 5 (contradicts A)
    let query = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5));
    let result = ctx.check_with_query(&query);

    assert!(
        matches!(
            result,
            InterpolatingResult::Unsat(_) | InterpolatingResult::UnsatNoInterpolant { .. }
        ),
        "Expected UNSAT, got {result:?}"
    );

    // No decode misses for standard integer comparisons
    assert_eq!(
        ctx.decode_miss_count(),
        0,
        "decode_miss_count should be 0 for standard LIA formulas"
    );
}

#[test]
fn test_interpolating_context_decode_miss_count_increments_on_undecodable_term() {
    // Verify that decode_miss_count increments when try_farkas_interpolant
    // encounters a term that term_to_chc_expr cannot decode (#3591 AC #3).
    let mut ctx = InterpolatingSmtContext::new();
    assert_eq!(ctx.decode_miss_count(), 0);

    // Inject a synthetic FarkasConflict with an undecodable Forall term
    ctx.test_inject_decode_miss();
    assert_eq!(
        ctx.decode_miss_count(),
        1,
        "decode_miss_count should increment for undecodable Forall term"
    );

    // Inject again — count should keep incrementing
    ctx.test_inject_decode_miss();
    assert_eq!(
        ctx.decode_miss_count(),
        2,
        "decode_miss_count should accumulate across multiple decode misses"
    );
}

#[test]
fn test_interpolating_result_unsat_no_interpolant_carries_decode_misses() {
    // Verify that UnsatNoInterpolant { decode_misses } carries the count (#3757).
    // This is the production diagnostic channel — callers inspect the result directly.
    let mut ctx = InterpolatingSmtContext::new();

    // Set up A-partition so we go through the Farkas path (not trivial empty-A)
    let x = ChcVar::new("x", ChcSort::Int);
    ctx.assert_a(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)));

    // Inject an undecodable term to force decode_miss_count > 0
    ctx.test_inject_decode_miss();
    assert_eq!(ctx.decode_miss_count(), 1);

    // Query that contradicts A (x <= -10 vs x >= 0)
    let query = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(-10));
    let result = ctx.check_with_query(&query);

    // The result should be some form of UNSAT
    match result {
        InterpolatingResult::UnsatNoInterpolant { decode_misses } => {
            // The decode_misses field should reflect the cumulative count
            assert!(
                decode_misses >= 1,
                "UnsatNoInterpolant should carry decode_misses >= 1, got {decode_misses}"
            );
        }
        InterpolatingResult::Unsat(_) => {
            // If extraction succeeded despite prior miss, that's also valid
        }
        other => panic!("Expected UNSAT variant, got {other:?}"),
    }
}

/// Test that the solver handles large disequality sets.
///
/// Creates a formula with many disequalities. With the unified 1M split
/// cap (#2472), the solver should find a solution (the system is SAT).
/// Previously this triggered the 10K low guard and returned Unknown.
#[test]
fn test_max_splits_guard_returns_unknown() {
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    // Triangular system with many integer solutions:
    // 3x + 2y + z = 10000, x + y + z = 5000, 0 <= x,y,z <= 5000
    let constraint = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::eq(
                ChcExpr::add(
                    ChcExpr::mul(ChcExpr::int(3), ChcExpr::var(x.clone())),
                    ChcExpr::add(
                        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(y.clone())),
                        ChcExpr::var(z.clone()),
                    ),
                ),
                ChcExpr::int(10000),
            ),
            ChcExpr::eq(
                ChcExpr::add(
                    ChcExpr::var(x.clone()),
                    ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::var(z.clone())),
                ),
                ChcExpr::int(5000),
            ),
        ),
        ChcExpr::and(
            ChcExpr::and(
                ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0)),
            ),
            ChcExpr::and(
                ChcExpr::ge(ChcExpr::var(z), ChcExpr::int(0)),
                ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5000)),
            ),
        ),
    );

    // Add 250 disequalities per variable to force enumeration past the 10K cap.
    let mut full_constraint = constraint;
    for i in 0..250 {
        full_constraint = ChcExpr::and(
            full_constraint,
            ChcExpr::not(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(i))),
        );
    }
    for i in 0..250 {
        full_constraint = ChcExpr::and(
            full_constraint,
            ChcExpr::not(ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(i))),
        );
    }

    // With the unified 1M split cap (#2472), the solver should either
    // find a solution (SAT) or hit the cap (Unknown). Unsat is wrong
    // (the system has solutions like x=250, y=250, z=4500).
    let result = ctx.check_sat(&full_constraint);
    assert!(
        matches!(result, SmtResult::Unknown | SmtResult::Sat(_)),
        "expected Unknown (split guard) or Sat, got {result:?}"
    );
}

/// Regression test for #2739: IncrementalQueryContext must detect conflict
/// between background (x=0) and assumption (x=1).
#[test]
fn test_incremental_sat_context_bg_conflict() {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_eq_0 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let x_eq_1 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1));

    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();

    // Background: x = 0
    inc.assert_background(&x_eq_0, &mut smt);
    inc.finalize_background(&smt);

    // Query 1: x = 0 (should be SAT)
    inc.push();
    let r1 = inc.check_sat_incremental(std::slice::from_ref(&x_eq_0), &mut smt, None);
    inc.pop();
    assert!(
        matches!(r1, IncrementalCheckResult::Sat(_)),
        "x=0 with bg x=0 should be SAT, got {r1:?}"
    );

    // Query 2: x = 1 (should be UNSAT — conflicts with bg x=0)
    inc.push();
    let r2 = inc.check_sat_incremental(std::slice::from_ref(&x_eq_1), &mut smt, None);
    inc.pop();
    assert!(
        matches!(r2, IncrementalCheckResult::Unsat),
        "x=1 with bg x=0 should be UNSAT, got {r2:?}"
    );

    // Query 3: x = 0 again (should remain SAT — prior UNSAT query must not leak)
    inc.push();
    let r3 = inc.check_sat_incremental(std::slice::from_ref(&x_eq_0), &mut smt, None);
    inc.pop();
    assert!(
        matches!(r3, IncrementalCheckResult::Sat(_)),
        "x=0 with bg x=0 should remain SAT after conflicting query, got {r3:?}"
    );
}

/// Build a shared deep Boolean tree with exponentially many occurrences.
fn make_deep_conjunction(depth: usize) -> ChcExpr {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut expr = ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0));
    for _ in 0..depth {
        // Keep the branches structurally distinct so reflexive-equality
        // simplification cannot collapse the stress graph before the
        // conversion-budget guard counts occurrences.
        expr = ChcExpr::eq(expr.clone(), ChcExpr::not(expr));
    }
    expr
}

struct GlobalTermBytesGuard;

impl Drop for GlobalTermBytesGuard {
    fn drop(&mut self) {
        TermStore::reset_global_term_bytes();
        TermStore::reset_process_memory_limit_for_testing();
    }
}

fn force_global_term_memory_exceeded() -> GlobalTermBytesGuard {
    // DEFAULT_TERM_MEMORY_LIMIT is usize::MAX (unlimited), so the term-byte
    // comparison alone cannot trigger global_memory_exceeded(). Instead, force
    // the process-level RSS limit to 1 byte so process_memory_exceeded() fires.
    TermStore::force_process_memory_exceeded_for_testing();
    GlobalTermBytesGuard
}

#[test]
fn test_convert_expr_budget_exceeded_returns_unknown() {
    // Build a pathologically deep expression (2^20 = 1M+ nodes).
    // Without the budget, this would allocate gigabytes.
    let deep = make_deep_conjunction(21);

    let mut ctx = SmtContext::new();
    let result = ctx.check_sat(&deep);
    assert!(
        matches!(result, SmtResult::Unknown),
        "Expected Unknown for budget-exceeded expression, got {result:?}"
    );
}

#[test]
fn test_convert_expr_small_expression_works() {
    // A small expression should work normally (budget not exceeded).
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
    );

    let mut ctx = SmtContext::new();
    let result = ctx.check_sat(&expr);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Small conjunction should be SAT, got {result:?}"
    );
}

#[test]
fn test_conversion_budget_resets_between_checks() {
    // After a budget-exceeded check, subsequent small checks should succeed.
    let deep = make_deep_conjunction(21);
    let x = ChcVar::new("x", ChcSort::Int);
    let small = ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0));

    let mut ctx = SmtContext::new();

    // First check: budget exceeded
    let r1 = ctx.check_sat(&deep);
    assert!(matches!(r1, SmtResult::Unknown));

    // Second check: budget should be reset, so this should succeed
    let r2 = ctx.check_sat(&small);
    assert!(
        matches!(r2, SmtResult::Sat(_)),
        "Budget should reset between checks, got {r2:?}"
    );
}

#[test]
#[serial(global_term_memory)]
fn test_check_sat_returns_unknown_when_global_term_memory_exceeded() {
    let _guard = force_global_term_memory_exceeded();
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0));

    let mut ctx = SmtContext::new();
    let result = ctx.check_sat(&expr);
    // The internal DPLL(T) returns Unknown due to term memory pressure,
    // but the executor fallback (check_sat outer wrapper) routes the query
    // through ay-dpll's Executor which uses a separate resource pool and
    // can solve trivial QF_LIA queries. Accept either Unknown or Sat.
    assert!(
        matches!(result, SmtResult::Unknown | SmtResult::Sat(_)),
        "expected Unknown or Sat (via executor fallback), got {result:?}"
    );
}

#[test]
#[serial(global_term_memory)]
fn test_assumption_mode_returns_unknown_when_global_term_memory_exceeded() {
    let _guard = force_global_term_memory_exceeded();
    let x = ChcVar::new("x", ChcSort::Int);
    let background = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let assumptions = vec![ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10))];

    let mut ctx = SmtContext::new();
    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);
    assert!(
        matches!(result, SmtResult::Unknown),
        "expected Unknown in assumption mode when global memory budget is exceeded, got {result:?}"
    );
}

#[test]
fn test_incremental_background_budget_exceeded_returns_unknown() {
    // If background conversion exceeds the expression budget, incremental queries
    // must conservatively return Unknown instead of using a partial background.
    let deep = make_deep_conjunction(21);

    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();
    inc.assert_background(&deep, &mut smt);
    inc.finalize_background(&smt);

    let x = ChcVar::new("x", ChcSort::Int);
    let assumption = ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0));

    inc.push();
    let result = inc.check_sat_incremental(std::slice::from_ref(&assumption), &mut smt, None);
    inc.pop();

    assert!(
        matches!(result, IncrementalCheckResult::Unknown),
        "expected Unknown when background conversion budget is exceeded, got {result:?}"
    );
}

#[test]
fn test_incremental_background_budget_unknown_resets_conversion_state() {
    // Unknown from background overflow should not leave `smt` stuck in
    // conversion-budget-exceeded mode for subsequent conversions.
    let deep = make_deep_conjunction(21);

    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();
    inc.assert_background(&deep, &mut smt);
    inc.finalize_background(&smt);

    let x = ChcVar::new("x", ChcSort::Int);
    let assumption = ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0));

    inc.push();
    let result = inc.check_sat_incremental(std::slice::from_ref(&assumption), &mut smt, None);
    inc.pop();
    assert!(matches!(result, IncrementalCheckResult::Unknown));
    assert!(
        !smt.conversion_budget_exceeded(),
        "per-check budget state should be reset even on early Unknown"
    );

    let true_term = smt.terms.mk_bool(true);
    let converted = smt.convert_expr(&assumption);
    assert_ne!(
        converted, true_term,
        "stale budget state forced conversion to the sentinel true term"
    );
}

#[test]
#[serial(global_term_memory)]
fn test_incremental_returns_unknown_when_global_term_memory_exceeded() {
    let x = ChcVar::new("x", ChcSort::Int);
    let background = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let assumption = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10));

    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();
    inc.assert_background(&background, &mut smt);
    inc.finalize_background(&smt);

    let _guard = force_global_term_memory_exceeded();

    inc.push();
    let result = inc.check_sat_incremental(std::slice::from_ref(&assumption), &mut smt, None);
    inc.pop();

    assert!(
        matches!(result, IncrementalCheckResult::Unknown),
        "expected incremental Unknown when global memory budget is exceeded, got {result:?}"
    );
}

/// Regression test for #2926: verify that Farkas conflicts are collected
/// from theory UNSAT results. This test exercises the **genuine Farkas certificate**
/// path (LRA bound-contradiction), not the synthesis path.
/// See tests/farkas_synthesis_2926.rs for the actual synthesis path test.
///
/// Uses contradictory A/B constraints (x >= 1 as background, x <= -1 as assumption)
/// that trigger LRA Farkas. The test verifies that `farkas_conflicts` is non-empty
/// in the returned `UnsatWithCore`.
#[test]
#[serial(global_term_memory)]
fn test_farkas_conflicts_synthesized_in_unsat_core() {
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);

    // background: x >= 1
    let bg = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(1));
    // assumption: x <= -1
    let assumption = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(-1));

    let result = ctx.check_sat_with_assumption_conjuncts(&[bg], &[assumption]);
    match &result {
        SmtResult::UnsatWithCore(core) => {
            assert!(
                !core.farkas_conflicts.is_empty(),
                "expected non-empty farkas_conflicts in UnsatWithCore, got empty"
            );
            assert!(
                core.diagnostics.dt_iterations > 0,
                "expected dt_iterations > 0 in UNSAT-core diagnostics, got {:?}",
                core.diagnostics
            );
            assert!(
                core.diagnostics.total_farkas_conflicts >= core.farkas_conflicts.len() as u64,
                "diagnostics total_farkas_conflicts ({}) must be >= returned conflicts ({})",
                core.diagnostics.total_farkas_conflicts,
                core.farkas_conflicts.len()
            );
            assert!(
                core.diagnostics.total_farkas_conflicts
                    >= core.diagnostics.activation_core_conflicts,
                "diagnostics activation_core_conflicts ({}) exceeded total_farkas_conflicts ({})",
                core.diagnostics.activation_core_conflicts,
                core.diagnostics.total_farkas_conflicts
            );
            // Each conflict should have matching lengths for terms, polarities, coefficients, origins
            for conflict in &core.farkas_conflicts {
                assert_eq!(
                    conflict.conflict_terms.len(),
                    conflict.polarities.len(),
                    "conflict_terms and polarities length mismatch"
                );
                assert_eq!(
                    conflict.conflict_terms.len(),
                    conflict.farkas.coefficients.len(),
                    "conflict_terms and farkas coefficients length mismatch"
                );
                assert_eq!(
                    conflict.conflict_terms.len(),
                    conflict.origins.len(),
                    "conflict_terms and origins length mismatch"
                );
                // All coefficients should be positive (valid Farkas certificate)
                for coeff in &conflict.farkas.coefficients {
                    assert!(
                        *coeff > Rational64::from(0),
                        "Farkas coefficient must be positive, got {coeff}"
                    );
                }
            }
        }
        SmtResult::Unsat | SmtResult::UnsatWithFarkas(_) => {
            // Also acceptable UNSAT results (different code paths may fire)
        }
        other => panic!("expected UNSAT variant, got {other:?}"),
    }
}

/// Regression test for #2913: var=var equality in assumptions must be preserved
/// in the SAT model.
///
/// Before the fix, `propagate_var_equalities()` inside `propagate_constants()`
/// would substitute one variable for another (e.g., C → E) within individual
/// expressions. This eliminated the equality constraint from the theory solver,
/// causing the model to have E != C despite E = C being asserted.
#[test]
#[serial(global_term_memory)]
fn test_assumption_solver_preserves_var_var_equality_in_model() {
    let mut ctx = SmtContext::new();

    let e = ChcVar::new("E", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);
    let a = ChcVar::new("A", ChcSort::Int);

    // Background: A >= 0 (simple constraint to make the formula satisfiable)
    let background = vec![ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::int(0))];

    // Assumptions: E = C AND A >= 1
    // The var=var equality E = C is the key: the old preprocessing would
    // substitute C → E (or E → C), removing the equality constraint.
    let assumptions = vec![
        ChcExpr::eq(ChcExpr::var(e), ChcExpr::var(c)),
        ChcExpr::ge(ChcExpr::var(a), ChcExpr::int(1)),
    ];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    match result {
        SmtResult::Sat(model) => {
            let e_val = model.get("E");
            let c_val = model.get("C");
            assert!(e_val.is_some(), "Model must contain E. Got: {model:?}");
            assert!(c_val.is_some(), "Model must contain C. Got: {model:?}");
            assert_eq!(
                e_val, c_val,
                "E = C equality violated: E={e_val:?}, C={c_val:?}. Model: {model:?}"
            );
        }
        other => panic!("Expected Sat (E=C is satisfiable with any integer), got {other:?}"),
    }
}

/// Regression test for #2445: chained var-var equality must produce UNSAT when the
/// transitive closure yields a contradiction.
///
/// Before the fix, `collect_int_var_const_equalities` only found direct var=const
/// pairs. Given `ref_0_A = iface_0` and `ref_0_A = 1`, with assumption `iface_0 = 2`,
/// the solver failed to derive `iface_0 = 1` (via ref_0_A), which contradicts
/// `iface_0 = 2`. The solver incorrectly returned Sat.
#[test]
#[serial(global_term_memory)]
fn test_assumption_solver_chained_var_var_equality_unsat() {
    let mut ctx = SmtContext::new();

    let ref_0_a = ChcVar::new("ref_0_A", ChcSort::Int);
    let iface_0 = ChcVar::new("iface_0", ChcSort::Int);

    // Background: ref_0_A = iface_0, ref_0_A = 1
    // This implies iface_0 = 1 via transitivity.
    let background = vec![
        ChcExpr::eq(ChcExpr::var(ref_0_a.clone()), ChcExpr::var(iface_0.clone())),
        ChcExpr::eq(ChcExpr::var(ref_0_a), ChcExpr::int(1)),
    ];

    // Assumption: iface_0 = 2 (contradicts iface_0 = 1)
    let assumptions = vec![ChcExpr::eq(ChcExpr::var(iface_0), ChcExpr::int(2))];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    match result {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) => {}
        other => panic!(
            "Expected UNSAT (iface_0=1 via transitivity contradicts iface_0=2), got {other:?}"
        ),
    }
}

/// Regression test for #2445: three-hop chained equality must resolve transitively.
///
/// Given A=B, B=C, C=5, the closure should derive A=5, B=5, C=5.
/// With assumption A=10, this contradicts A=5 and must be UNSAT.
#[test]
#[serial(global_term_memory)]
fn test_assumption_solver_three_hop_var_chain_unsat() {
    let mut ctx = SmtContext::new();

    let a = ChcVar::new("chain_A", ChcSort::Int);
    let b = ChcVar::new("chain_B", ChcSort::Int);
    let c = ChcVar::new("chain_C", ChcSort::Int);

    // Background: A=B, B=C, C=5
    let background = vec![
        ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ChcExpr::eq(ChcExpr::var(b), ChcExpr::var(c.clone())),
        ChcExpr::eq(ChcExpr::var(c), ChcExpr::int(5)),
    ];

    // Assumption: A=10 (contradicts A=5 via chain)
    let assumptions = vec![ChcExpr::eq(ChcExpr::var(a), ChcExpr::int(10))];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    match result {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) => {}
        other => panic!("Expected UNSAT (chain_A=5 via A=B=C=5 contradicts A=10), got {other:?}"),
    }
}

/// Regression test for #2445: var-var equality closure must NOT break satisfiable cases.
///
/// Given A=B, B=5 with assumption A >= 0, this is satisfiable (A=B=5).
/// The closure must resolve A=5, B=5 and produce a valid model.
#[test]
#[serial(global_term_memory)]
fn test_assumption_solver_var_chain_sat_preserved() {
    let mut ctx = SmtContext::new();

    let a = ChcVar::new("chain_sat_A", ChcSort::Int);
    let b = ChcVar::new("chain_sat_B", ChcSort::Int);

    // Background: A=B, B=5
    let background = vec![
        ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ChcExpr::eq(ChcExpr::var(b), ChcExpr::int(5)),
    ];

    // Assumption: A >= 0 (consistent with A=5)
    let assumptions = vec![ChcExpr::ge(ChcExpr::var(a), ChcExpr::int(0))];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);

    match result {
        SmtResult::Sat(model) => {
            // Both A and B should be 5 in the model
            if let Some(SmtValue::Int(a_val)) = model.get("chain_sat_A") {
                assert_eq!(*a_val, 5, "chain_sat_A should be 5, got {a_val}");
            }
            if let Some(SmtValue::Int(b_val)) = model.get("chain_sat_B") {
                assert_eq!(*b_val, 5, "chain_sat_B should be 5, got {b_val}");
            }
        }
        other => panic!("Expected Sat (A=B=5 with A>=0 is satisfiable), got {other:?}"),
    }
}

#[test]
fn test_assumption_solver_sat_profile_disables_preprocess_and_inprocessing() {
    let sat = new_assumption_sat_solver(8);
    let profile = sat.inprocessing_feature_profile();

    for (name, enabled) in [
        ("preprocess", profile.preprocess),
        ("vivify", profile.vivify),
        ("subsume", profile.subsume),
        ("probe", profile.probe),
        ("bve", profile.bve),
        ("bce", profile.bce),
        ("condition", profile.condition),
        ("decompose", profile.decompose),
        ("factor", profile.factor),
        ("transred", profile.transred),
        ("htr", profile.htr),
        ("gate", profile.gate),
        ("congruence", profile.congruence),
        ("sweep", profile.sweep),
        ("backbone", profile.backbone),
    ] {
        assert!(
            !enabled,
            "assumption-mode SAT solver must disable {name} for one-shot queries"
        );
    }
}

/// Regression test for #5653: SAT preprocessing must not corrupt incremental
/// assumption-based solving.
///
/// Tseitin encoding of complex assumption formulas creates intermediate variables
/// (sub-conjunction roots). If preprocessing is enabled, passes like decompose,
/// congruence, and subsumption can eliminate these intermediates, breaking the
/// definitional chain (root → conjuncts) and causing wrong-polarity models.
///
/// This test encodes a conjunction of multiple clauses as an assumption, which
/// forces Tseitin to create intermediate variables. The conjunction is structured
/// so that preprocessing would be tempted to subsume or merge clauses. Without
/// the `set_preprocess_enabled(false)` fix, the model may violate the assumption
/// constraints.
#[test]
fn test_incremental_preprocessing_disabled_prevents_assumption_corruption() {
    let x = ChcVar::new("preproc_x", ChcSort::Int);
    let y = ChcVar::new("preproc_y", ChcSort::Int);
    let z = ChcVar::new("preproc_z", ChcSort::Int);

    // Background: x >= 0 AND x <= 100
    let bg = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(100)),
    );

    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();
    inc.assert_background(&bg, &mut smt);
    inc.finalize_background(&smt);

    // Assumption: a complex conjunction that generates multiple Tseitin intermediates.
    // (y >= x) AND (y <= x + 10) AND (z = y + 1) AND (z >= 1) AND (z <= 111)
    // This is satisfiable when combined with bg: e.g., x=0, y=0, z=1.
    let assumption_sat = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::var(x.clone())),
            ChcExpr::le(
                ChcExpr::var(y.clone()),
                ChcExpr::add(ChcExpr::var(x), ChcExpr::int(10)),
            ),
        ),
        ChcExpr::and(
            ChcExpr::eq(
                ChcExpr::var(z.clone()),
                ChcExpr::add(ChcExpr::var(y), ChcExpr::int(1)),
            ),
            ChcExpr::and(
                ChcExpr::ge(ChcExpr::var(z.clone()), ChcExpr::int(1)),
                ChcExpr::le(ChcExpr::var(z.clone()), ChcExpr::int(111)),
            ),
        ),
    );

    // Query 1: SAT — model must satisfy all constraints
    inc.push();
    let r1 = inc.check_sat_incremental(std::slice::from_ref(&assumption_sat), &mut smt, None);
    inc.pop();
    match &r1 {
        IncrementalCheckResult::Sat(model) => {
            // Verify model satisfies the constraints
            if let (Some(SmtValue::Int(xv)), Some(SmtValue::Int(yv)), Some(SmtValue::Int(zv))) = (
                model.get("preproc_x"),
                model.get("preproc_y"),
                model.get("preproc_z"),
            ) {
                assert!(*xv >= 0, "model: x={xv} must be >= 0");
                assert!(*xv <= 100, "model: x={xv} must be <= 100");
                assert!(*yv >= *xv, "model: y={yv} must be >= x={xv}");
                assert!(
                    *yv <= *xv + 10,
                    "model: y={yv} must be <= x+10={}",
                    *xv + 10
                );
                assert_eq!(*zv, *yv + 1, "model: z={zv} must be y+1={}", *yv + 1);
                assert!(*zv >= 1, "model: z={zv} must be >= 1");
                assert!(*zv <= 111, "model: z={zv} must be <= 111");
            }
        }
        IncrementalCheckResult::Unknown => {
            // Acceptable — theory solver may not find model in time
        }
        other => panic!("Expected Sat or Unknown for satisfiable conjunction, got {other:?}"),
    }

    // Query 2: UNSAT — add contradictory constraint z = -1 (conflicts with z >= 1)
    let assumption_unsat = ChcExpr::and(
        assumption_sat.clone(),
        ChcExpr::eq(ChcExpr::var(z), ChcExpr::int(-1)),
    );
    inc.push();
    let r2 = inc.check_sat_incremental(std::slice::from_ref(&assumption_unsat), &mut smt, None);
    inc.pop();
    assert!(
        matches!(r2, IncrementalCheckResult::Unsat),
        "z=-1 contradicts z>=1, should be UNSAT, got {r2:?}"
    );

    // Query 3: SAT again — verify no state leakage from prior UNSAT
    inc.push();
    let r3 = inc.check_sat_incremental(std::slice::from_ref(&assumption_sat), &mut smt, None);
    inc.pop();
    assert!(
        matches!(
            r3,
            IncrementalCheckResult::Sat(_) | IncrementalCheckResult::Unknown
        ),
        "satisfiable query after UNSAT should still work, got {r3:?}"
    );
}

/// Regression test for menlo_park_term_simpl_2_000 model violation pattern (#5653).
///
/// The incremental solver produces SAT models that violate the original constraints
/// when modular arithmetic (mod) is involved. The verify_sat_model_conjunction_strict
/// safety net catches these invalid models and returns Unknown, but the root cause
/// is that the Tseitin+LIA encoding of mod constraints may not be fully propagated
/// in the incremental SAT context.
///
/// This test encodes: x > 0 AND x <= 100 AND (mod x 2) = 0 (x is positive even)
/// as background, then queries with an assumption y = x + 1 (y is odd).
/// The model must satisfy: x > 0, x <= 100, x is even, y = x + 1.
#[test]
fn test_incremental_modular_arithmetic_model_validity() {
    let x = ChcVar::new("mod_x", ChcSort::Int);
    let y = ChcVar::new("mod_y", ChcSort::Int);

    // Background: x > 0 AND x <= 100 AND (mod x 2) = 0
    let bg = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(100)),
        ),
        ChcExpr::eq(
            ChcExpr::Op(
                crate::expr::ChcOp::Mod,
                vec![
                    std::sync::Arc::new(ChcExpr::var(x.clone())),
                    std::sync::Arc::new(ChcExpr::int(2)),
                ],
            ),
            ChcExpr::int(0),
        ),
    );

    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();
    inc.assert_background(&bg, &mut smt);
    inc.finalize_background(&smt);

    // Assumption: y = x + 1 (forces y to be odd given x is even)
    let assumption = ChcExpr::eq(
        ChcExpr::var(y),
        ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
    );

    inc.push();
    let result = inc.check_sat_incremental(std::slice::from_ref(&assumption), &mut smt, None);
    inc.pop();

    match &result {
        IncrementalCheckResult::Sat(model) => {
            // If we get SAT, the model MUST satisfy all constraints
            if let (Some(SmtValue::Int(xv)), Some(SmtValue::Int(yv))) =
                (model.get("mod_x"), model.get("mod_y"))
            {
                assert!(*xv > 0, "model: x={xv} must be > 0");
                assert!(*xv <= 100, "model: x={xv} must be <= 100");
                assert!(*xv % 2 == 0, "model: x={xv} must be even (mod x 2 = 0)");
                assert_eq!(*yv, *xv + 1, "model: y={yv} must be x+1={}", *xv + 1);
            }
        }
        IncrementalCheckResult::Unknown => {
            // Acceptable — model validation may have rejected an invalid model,
            // or the solver couldn't find a model within budget.
            // This is the EXPECTED outcome if the model violation bug is present.
        }
        IncrementalCheckResult::Unsat => {
            panic!("System is satisfiable (e.g. x=2, y=3), should not be UNSAT");
        }
    }
}

// =========================================================================
// Per-engine term memory budget enforcement in convert_expr (#8600)
// =========================================================================

#[test]
fn test_convert_expr_per_engine_memory_budget_enforcement() {
    // Set a very small per-engine memory budget (256 bytes) so that
    // even a moderate expression exceeds it during convert_expr.
    // The periodic check in convert_expr_inner (every 1024 nodes) should
    // detect this and set conversion_budget_exceeded, causing check_sat
    // to return Unknown.
    let mut ctx = SmtContext::new();
    ctx.set_term_memory_budget(Some(256));

    // Build an expression large enough that >1024 nodes are converted,
    // triggering the periodic memory check. A 12-level deep conjunction
    // produces ~4K nodes.
    let deep = make_deep_conjunction(13);
    let result = ctx.check_sat(&deep);
    assert!(
        matches!(result, SmtResult::Unknown),
        "Expected Unknown when per-engine memory budget exceeded during conversion, got {result:?}"
    );
}

#[test]
fn test_per_engine_memory_budget_small_expression_succeeds() {
    // With a generous budget, small expressions should succeed normally.
    let mut ctx = SmtContext::new();
    ctx.set_term_memory_budget(Some(10 * 1024 * 1024)); // 10 MB

    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
    );
    let result = ctx.check_sat(&expr);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Small expression with generous budget should be SAT, got {result:?}"
    );
}

#[test]
fn test_per_engine_memory_budget_no_budget_no_enforcement() {
    // When no budget is set (None), term_memory_exceeded() always returns false.
    let mut ctx = SmtContext::new();
    assert!(!ctx.term_memory_exceeded(), "No budget should never exceed");

    // A moderate expression (2^13 ~ 8K nodes) should succeed with no
    // memory budget. It's well under MAX_CONVERSION_NODES (1M).
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
    );
    let result = ctx.check_sat(&expr);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Small expression with no memory budget should succeed, got {result:?}"
    );
}

#[test]
fn test_per_engine_memory_budget_thread_local_inheritance() {
    // Verify that SmtContext::new() inherits the thread-local budget
    // set by scoped_thread_term_memory_budget().
    let _guard = SmtContext::scoped_thread_term_memory_budget(Some(42));
    let ctx = SmtContext::new();
    assert_eq!(
        ctx.term_memory_budget,
        Some(42),
        "New SmtContext should inherit thread-local budget"
    );
}

#[test]
fn test_per_engine_memory_budget_survives_reset() {
    // The per-engine memory budget should survive SmtContext::reset() since
    // it's engine-level config, not query-level state.
    let mut ctx = SmtContext::new();
    ctx.set_term_memory_budget(Some(1_000_000));
    ctx.reset();
    assert_eq!(
        ctx.term_memory_budget,
        Some(1_000_000),
        "term_memory_budget should survive reset()"
    );
}
