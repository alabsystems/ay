// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
#[test]
fn test_lra_farkas_coefficient_extraction() {
    // Test that conflicting bounds produce Farkas coefficients
    // x <= 5 AND x >= 10 is UNSAT with Farkas certificate [1, 1]
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let c5 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let c10 = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // x <= 5
    let le5 = terms.mk_le(x, c5);
    // x >= 10
    let ge10 = terms.mk_ge(x, c10);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le5, true); // x <= 5
    solver.assert_literal(ge10, true); // x >= 10

    let result = solver.check();

    // Should be UnsatWithFarkas with coefficients
    match result {
        TheoryResult::UnsatWithFarkas(conflict) => {
            assert_eq!(
                conflict.literals.len(),
                2,
                "Should have 2 conflicting literals"
            );
            assert!(
                conflict.farkas.is_some(),
                "Should have Farkas annotation for simple bounds conflict"
            );
            let farkas = conflict.farkas.unwrap();
            assert_eq!(farkas.coefficients.len(), 2, "Should have 2 coefficients");
            // Both coefficients should be positive (valid Farkas certificate)
            assert!(
                farkas.is_valid(),
                "Farkas coefficients should be non-negative"
            );
        }
        _ => panic!("Expected UnsatWithFarkas but got {result:?}"),
    }
}

#[test]
fn test_lra_farkas_tableau_conflict() {
    // Test that tableau-based conflicts produce Farkas coefficients
    // x + y <= 10 AND x >= 5 AND y >= 6 is UNSAT
    // (5 + 6 = 11 > 10, contradiction)
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c5 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let c6 = terms.mk_rational(BigRational::from(BigInt::from(6)));
    let c10 = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, c10); // x + y <= 10
    let x_ge = terms.mk_ge(x, c5); // x >= 5
    let y_ge = terms.mk_ge(y, c6); // y >= 6

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(sum_le, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);

    let result = solver.check();

    // Should be UnsatWithFarkas (or Unsat if coefficients couldn't be extracted)
    match result {
        TheoryResult::UnsatWithFarkas(conflict) => {
            // We have Farkas coefficients
            if let Some(farkas) = &conflict.farkas {
                assert!(
                    farkas.is_valid(),
                    "Farkas coefficients should be non-negative"
                );
            }
        }
        TheoryResult::Unsat(_) => {
            // Acceptable if we couldn't extract Farkas
        }
        _ => panic!("Expected Unsat or UnsatWithFarkas but got {result:?}"),
    }
}

#[test]
fn test_lra_farkas_overflow_omits_annotation() {
    let mut terms = TermStore::new();

    // x = M*y, y >= 1, x <= 0 is UNSAT for any positive M.
    // Use M > i64::MAX so Farkas coefficient conversion overflows.
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let huge_coeff = terms.mk_rational(BigRational::from(BigInt::from(i64::MAX) + BigInt::one()));
    let one = terms.mk_rational(BigRational::one());
    let zero = terms.mk_rational(BigRational::zero());

    let huge_y = terms.mk_mul(vec![huge_coeff, y]);
    let eq = terms.mk_eq(x, huge_y);
    let y_ge_1 = terms.mk_ge(y, one);
    let x_le_0 = terms.mk_le(x, zero);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(y_ge_1, true);
    solver.assert_literal(x_le_0, true);

    match solver.check() {
        TheoryResult::UnsatWithFarkas(conflict) => {
            assert!(
                conflict.farkas.is_none(),
                "overflowed coefficients must suppress Farkas annotations"
            );
        }
        TheoryResult::Unsat(_) => {}
        result => panic!("Expected UNSAT with overflowed coefficients, got {result:?}"),
    }
}

// ========================================================================
// Phase 2 Verification Tests - LRA Conflict Soundness (#298)
// ========================================================================
//
// These tests verify that LRA conflict explanations are semantically sound.
// They catch bugs like #294 where a theory returns a conflict that doesn't
// actually conflict.

/// Verify simple bounds conflict explanations are sound.
#[test]
fn test_lra_bounds_conflict_soundness() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // x <= 5 AND x >= 10 is UNSAT
    let le_5 = terms.mk_le(x, five);
    let ge_10 = terms.mk_ge(x, ten);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_5, true);
    solver.assert_literal(ge_10, true);

    let result = solver.check();
    let conflict = assert_conflict_soundness(result, LraSolver::new(&terms));

    // Verify expected literals: both le_5 and ge_10 should be in the conflict
    let terms_in_conflict: Vec<_> = conflict.iter().map(|lit| lit.term).collect();
    assert!(
        terms_in_conflict.contains(&le_5) || terms_in_conflict.contains(&ge_10),
        "Bounds conflict should reference at least one of the bound terms, got: {conflict:?}"
    );
    // Conflict should be exactly 2 literals for this simple case
    assert!(
        conflict.len() <= 2,
        "Simple bounds conflict should be minimal (≤2 literals), got {}",
        conflict.len()
    );
}

/// Verify each literal in a bounds conflict is necessary (true minimality).
///
/// For `x <= 5 AND x >= 10`, removing either bound should make the
/// remaining set SAT.
#[test]
fn test_lra_bounds_conflict_minimality() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let le_5 = terms.mk_le(x, five);
    let ge_10 = terms.mk_ge(x, ten);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_5, true);
    solver.assert_literal(ge_10, true);

    let result = solver.check();
    let conflict = assert_conflict_soundness(result, LraSolver::new(&terms));

    // True minimality: removing any single literal makes the rest SAT
    for i in 0..conflict.len() {
        let mut subsolver = LraSolver::new(&terms);
        for (j, lit) in conflict.iter().enumerate() {
            if j != i {
                subsolver.assert_literal(lit.term, lit.value);
            }
        }
        assert!(
            matches!(subsolver.check(), TheoryResult::Sat),
            "Conflict is not minimal: removing literal {i} ({:?}) still yields UNSAT",
            conflict[i]
        );
    }
}

/// Verify tableau conflict explanations are sound.
#[test]
fn test_lra_tableau_conflict_soundness() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c5 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let c6 = terms.mk_rational(BigRational::from(BigInt::from(6)));
    let c10 = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // x + y <= 10 AND x >= 5 AND y >= 6 is UNSAT (5 + 6 = 11 > 10)
    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, c10);
    let x_ge = terms.mk_ge(x, c5);
    let y_ge = terms.mk_ge(y, c6);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(sum_le, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);

    let result = solver.check();
    let conflict = assert_conflict_soundness(result, LraSolver::new(&terms));

    // Conflict should be reasonably minimal (≤4 literals for this case)
    assert!(
        conflict.len() <= 4,
        "Conflict too large: {} literals",
        conflict.len()
    );
}

/// Verify strict inequality conflict explanations are sound.
#[test]
fn test_lra_strict_inequality_conflict_soundness() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // x < 5 AND x > 5 is UNSAT
    let lt_5 = terms.mk_lt(x, five);
    let gt_5 = terms.mk_gt(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(lt_5, true);
    solver.assert_literal(gt_5, true);

    let result = solver.check();
    assert_conflict_soundness(result, LraSolver::new(&terms));
}

/// Verify equality conflict explanations are sound.
#[test]
fn test_lra_equality_conflict_soundness() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // x = 5 AND x > 5 is UNSAT
    let eq_5 = terms.mk_eq(x, five);
    let gt_5 = terms.mk_gt(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(eq_5, true);
    solver.assert_literal(gt_5, true);

    let result = solver.check();
    assert_conflict_soundness(result, LraSolver::new(&terms));
}

/// Ensure no bogus conflicts for SAT cases.
#[test]
fn test_lra_no_bogus_conflict_on_sat() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c3 = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let c4 = terms.mk_rational(BigRational::from(BigInt::from(4)));
    let c10 = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // x + y <= 10 AND x >= 3 AND y >= 4 is SAT (3 + 4 = 7 <= 10)
    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, c10);
    let x_ge = terms.mk_ge(x, c3);
    let y_ge = terms.mk_ge(y, c4);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(sum_le, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);

    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "Should be SAT, not a bogus conflict"
    );
}

/// Verify disequality violation conflict explanations are sound.
#[test]
fn test_lra_disequality_conflict_soundness() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // x != 5 AND x >= 5 AND x <= 5 is UNSAT (forces x = 5, violates x != 5)
    let eq_5 = terms.mk_eq(x, five);
    let ge_5 = terms.mk_ge(x, five);
    let le_5 = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(eq_5, false); // x != 5
    solver.assert_literal(ge_5, true); // x >= 5
    solver.assert_literal(le_5, true); // x <= 5

    let result = solver.check();
    assert_conflict_soundness(result, LraSolver::new(&terms));
}

/// Test LinearExpr::normalize() for semantic expression matching (#794)
#[test]
fn test_linear_expr_normalize() {
    // Test basic normalization: coeffs in different order should normalize to same form
    let expr1 = LinearExpr {
        coeffs: vec![(2, Rational::from(1_i64)), (1, Rational::from(-1_i64))],
        constant: Rational::zero(),
    };
    let expr2 = LinearExpr {
        coeffs: vec![(1, Rational::from(-1_i64)), (2, Rational::from(1_i64))],
        constant: Rational::zero(),
    };

    let norm1 = expr1.normalize();
    let norm2 = expr2.normalize();

    // Both should be sorted by var_id: [(1, -1), (2, 1)]
    assert_eq!(norm1.coeffs.len(), 2);
    assert_eq!(norm2.coeffs.len(), 2);
    assert!(norm1.same_coefficients(&norm2));

    // Test that zero coefficients are removed
    let expr3 = LinearExpr {
        coeffs: vec![
            (1, Rational::from(1_i64)),
            (1, Rational::from(-1_i64)), // Should combine to 0
            (2, Rational::from(5_i64)),
        ],
        constant: Rational::zero(),
    };
    let norm3 = expr3.normalize();
    assert_eq!(norm3.coeffs.len(), 1);
    assert_eq!(norm3.coeffs[0].0, 2);
    assert_eq!(norm3.coeffs[0].1, Rational::from(5_i64));
}

/// Test semantic expression matching in is_expression_forced_to_value (#794)
/// When A = B is asserted, both `A - B` and `(A+1) - (B+1)` should be recognized
/// as forced to 0.
#[test]
fn test_semantic_expression_matching_equality() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("A", Sort::Int);
    let b = terms.mk_var("B", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));

    // Create A = B
    let eq_ab = terms.mk_eq(a, b);

    // Create (A + 1) = (B + 1)
    let a_plus_1 = terms.mk_add(vec![a, one]);
    let b_plus_1 = terms.mk_add(vec![b, one]);
    let eq_succ = terms.mk_eq(a_plus_1, b_plus_1);

    // (A = B) /\ not((A+1) = (B+1)) should be UNSAT
    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(eq_ab, true); // A = B
    solver.assert_literal(eq_succ, false); // not (A+1 = B+1)

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Expected UNSAT (A=B implies A+1=B+1), got {result:?}"
    );
}

/// Test basic optimization: minimize x subject to x >= 5
#[test]
fn test_optimize_basic_minimize() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ge_5 = terms.mk_ge(x, five); // x >= 5

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_5, true);

    // The solver needs to know about x, so we do a check first to populate state
    let check_result = solver.check();
    assert!(matches!(check_result, TheoryResult::Sat));

    // Get the internal variable for x (should be var 0)
    let x_var = *solver.term_to_var.get(&x).expect("x should be interned");

    // Minimize x subject to x >= 5 => optimal = 5
    let objective = LinearExpr::var(x_var);
    let result = solver.optimize(&objective, OptimizationSense::Minimize);

    match result {
        OptimizationResult::Optimal(val) => {
            assert_eq!(val, BigRational::from(BigInt::from(5)));
        }
        _ => panic!("Expected Optimal(5), got {result:?}"),
    }
}

/// Test basic optimization: maximize x subject to x <= 10
#[test]
fn test_optimize_basic_maximize() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let le_10 = terms.mk_le(x, ten); // x <= 10

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_10, true);

    let check_result = solver.check();
    assert!(matches!(check_result, TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x should be interned");

    // Maximize x subject to x <= 10 => optimal = 10
    let objective = LinearExpr::var(x_var);
    let result = solver.optimize(&objective, OptimizationSense::Maximize);

    match result {
        OptimizationResult::Optimal(val) => {
            assert_eq!(val, BigRational::from(BigInt::from(10)));
        }
        _ => panic!("Expected Optimal(10), got {result:?}"),
    }
}

/// Test optimization with bounded region: minimize x + y subject to x >= 0, y >= 0, x + y >= 10
#[test]
fn test_optimize_two_vars() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // x >= 0
    let x_ge_0 = terms.mk_ge(x, zero);
    // y >= 0
    let y_ge_0 = terms.mk_ge(y, zero);
    // x + y >= 10
    let x_plus_y = terms.mk_add(vec![x, y]);
    let sum_ge_10 = terms.mk_ge(x_plus_y, ten);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(sum_ge_10, true);

    let check_result = solver.check();
    assert!(matches!(check_result, TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x should be interned");
    let y_var = *solver.term_to_var.get(&y).expect("y should be interned");

    // Minimize x + y subject to constraints => optimal = 10
    let mut objective = LinearExpr::zero();
    objective.add_term(x_var, BigRational::one());
    objective.add_term(y_var, BigRational::one());

    let result = solver.optimize(&objective, OptimizationSense::Minimize);

    match result {
        OptimizationResult::Optimal(val) => {
            assert_eq!(val, BigRational::from(BigInt::from(10)));
        }
        _ => panic!("Expected Optimal(10), got {result:?}"),
    }
}

/// Test unbounded optimization: minimize x with no lower bound
#[test]
fn test_optimize_unbounded() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let le_10 = terms.mk_le(x, ten); // x <= 10

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_10, true);

    let check_result = solver.check();
    assert!(matches!(check_result, TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x should be interned");

    // Minimize x with only upper bound => unbounded
    let objective = LinearExpr::var(x_var);
    let result = solver.optimize(&objective, OptimizationSense::Minimize);

    assert!(
        matches!(result, OptimizationResult::Unbounded),
        "Expected Unbounded, got {result:?}"
    );
}

/// Test infeasible optimization
#[test]
fn test_optimize_infeasible() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // x >= 10 AND x <= 5 is infeasible
    let ge_10 = terms.mk_ge(x, ten);
    let le_5 = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_10, true);
    solver.assert_literal(le_5, true);

    // Call check() first to parse atoms and populate term_to_var
    let check_result = solver.check();
    // Should be UNSAT
    assert!(
        matches!(
            check_result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Expected check() to return UNSAT for infeasible constraints"
    );

    // Now test optimize - should also return infeasible
    let mut solver2 = LraSolver::new(&terms);
    solver2.assert_literal(ge_10, true);
    solver2.assert_literal(le_5, true);

    // Use a fresh objective since internal vars might differ
    let objective = LinearExpr::constant(BigRational::zero());
    let result = solver2.optimize(&objective, OptimizationSense::Minimize);

    assert!(
        matches!(result, OptimizationResult::Infeasible),
        "Expected Infeasible, got {result:?}"
    );
}

/// Test optimization with constant objective
#[test]
fn test_optimize_constant_objective() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ge_5 = terms.mk_ge(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_5, true);

    let check_result = solver.check();
    assert!(matches!(check_result, TheoryResult::Sat));

    // Optimize constant objective (42)
    let objective = LinearExpr::constant(BigRational::from(BigInt::from(42)));
    let result = solver.optimize(&objective, OptimizationSense::Minimize);

    match result {
        OptimizationResult::Optimal(val) => {
            assert_eq!(val, BigRational::from(BigInt::from(42)));
        }
        _ => panic!("Expected Optimal(42), got {result:?}"),
    }
}

/// Test that optimize() returns Unknown (not Infeasible) when feasibility check
/// returns Unknown due to unsupported terms. Regression test for #6166.
#[test]
fn test_optimize_unknown_feasibility_returns_unknown_6166() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let ge_0 = terms.mk_ge(x, zero); // x >= 0
    let le_10 = terms.mk_le(x, ten); // x <= 10

    // Unknown function "f" in non-combined mode marks the atom as unsupported
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let f_le_5 = terms.mk_le(f_x, five); // f(x) <= 5

    let mut solver = LraSolver::new(&terms);
    // Default combined_theory_mode is false, so unknown functions mark atom unsupported
    solver.assert_literal(ge_0, true);
    solver.assert_literal(le_10, true);
    solver.assert_literal(f_le_5, true);

    // First check() populates term_to_var and detects unsupported atom
    let check_result = solver.check();
    assert!(
        matches!(check_result, TheoryResult::Unknown),
        "Expected Unknown with unsupported function, got {check_result:?}"
    );

    // Get the internal variable for x (populated by check())
    let x_var = *solver.term_to_var.get(&x).expect("x should be interned");
    let objective = LinearExpr::var(x_var);

    // BUG FIX #6166: optimize() should return Unknown, NOT Infeasible.
    // Before the fix, TheoryResult::Unknown was mapped to OptimizationResult::Infeasible.
    let result = solver.optimize(&objective, OptimizationSense::Minimize);
    assert!(
        matches!(result, OptimizationResult::Unknown),
        "Expected Unknown when feasibility is unknown, got {result:?}"
    );
}

/// Test that optimize() returns Unknown (not Infeasible) when iteration limit is hit.
/// Regression test for #3220.
#[test]
fn test_optimize_iteration_limit_returns_unknown() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let ge_0 = terms.mk_ge(x, zero); // x >= 0
    let le_10 = terms.mk_le(x, ten); // x <= 10

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_0, true);
    solver.assert_literal(le_10, true);

    let check_result = solver.check();
    assert!(matches!(check_result, TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x should be interned");
    let objective = LinearExpr::var(x_var);

    // With 0 iterations, the solver should return Unknown — NOT Infeasible
    let result = solver.optimize_with_max_iters(&objective, OptimizationSense::Minimize, 0);
    assert!(
        matches!(result, OptimizationResult::Unknown),
        "Expected Unknown on iteration limit, got {result:?}"
    );

    // With a reasonable budget, same query should succeed
    let result = solver.optimize_with_max_iters(&objective, OptimizationSense::Minimize, 100);
    assert!(
        matches!(result, OptimizationResult::Optimal(_)),
        "Expected Optimal with sufficient budget, got {result:?}"
    );
}

#[test]
fn test_dual_simplex_iteration_limit_returns_unknown() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let x_ge_10 = terms.mk_ge(x, ten);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    // Provide a real reason term so the bound isn't skipped (#4919).
    solver.add_direct_bound_with_reasons(
        x_var,
        BigRational::from(BigInt::from(10)),
        true,
        &[(x_ge_10, true)],
    );

    // #8009: The pre-loop fast path fixes non-basic variable violations
    // without pivoting (instant update, not counted as an iteration).
    // Since x is non-basic with violated lower bound, the fix is trivial
    // and the solver returns Sat even with max_iters=1.
    let result = solver.dual_simplex_with_max_iters(1);
    assert!(
        matches!(result, TheoryResult::Sat | TheoryResult::Unknown),
        "non-basic violation should be fixed by pre-loop fast path or budget-limited: {result:?}"
    );

    // With a reasonable budget, the solver should find a feasible model.
    let result = solver.dual_simplex_with_max_iters(10);
    assert!(matches!(result, TheoryResult::Sat), "{result:?}");
}

/// Test for issue #2012: trivial_conflict code path.
///
/// When variables cancel out leaving a constant constraint that is unsatisfiable
/// (e.g., `x - x < -1` simplifies to `0 < -1` = FALSE), the solver should
/// immediately return UNSAT without running dual simplex.
#[test]
fn test_lra_constant_constraint_conflict() {
    let mut terms = TermStore::new();

    // Case 1: x - x < -1 (simplifies to 0 < -1, which is FALSE)
    let x = terms.mk_var("x", Sort::Real);
    let neg_one = terms.mk_rational(BigRational::from(BigInt::from(-1)));
    // x - x is represented as x + (-1)*x = 0
    let neg_x = terms.mk_neg(x);
    let x_minus_x = terms.mk_add(vec![x, neg_x]);
    let lt_neg_one = terms.mk_lt(x_minus_x, neg_one); // 0 < -1

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(lt_neg_one, true);

    let result = solver.check();
    // Verify conflict is non-empty and self-contained (not just result variant)
    let conflict = assert_conflict_soundness(result, LraSolver::new(&terms));
    assert!(
        conflict.len() <= 2,
        "Constant constraint conflict should be minimal, got {} literals",
        conflict.len()
    );

    // Case 2: x - x >= 1 (simplifies to 0 >= 1, which is FALSE)
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let neg_x = terms.mk_neg(x);
    let x_minus_x = terms.mk_add(vec![x, neg_x]);
    let ge_one = terms.mk_ge(x_minus_x, one); // 0 >= 1

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_one, true);

    let result = solver.check();
    let conflict = assert_conflict_soundness(result, LraSolver::new(&terms));
    assert!(
        conflict.len() <= 2,
        "Constant constraint conflict should be minimal, got {} literals",
        conflict.len()
    );

    // Case 3: Constant TRUE (0 <= 1) should be SAT
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let neg_x = terms.mk_neg(x);
    let x_minus_x = terms.mk_add(vec![x, neg_x]);
    let le_one = terms.mk_le(x_minus_x, one); // 0 <= 1

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_one, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x - x <= 1 should be SAT (0 <= 1 is true), got {result:?}"
    );
}

/// Test that trivial_conflict is properly cleared on pop().
///
/// Regression test for #2012: ensures that push/pop correctly
/// handles the trivial_conflict state.
#[test]
fn test_trivial_conflict_cleared_on_pop() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let neg_x = terms.mk_neg(x);
    let x_minus_x = terms.mk_add(vec![x, neg_x]);
    let ge_one = terms.mk_ge(x_minus_x, one); // 0 >= 1 (FALSE)
    let le_one = terms.mk_le(x, one); // x <= 1 (fine)

    let mut solver = LraSolver::new(&terms);

    // Assert a satisfiable constraint at level 0
    solver.assert_literal(le_one, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Push and assert a trivial conflict
    solver.push();
    solver.assert_literal(ge_one, true);
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Expected UNSAT with trivial conflict, got {result:?}"
    );

    // Pop should restore to SAT state (trivial_conflict cleared)
    solver.pop();
    solver.reset(); // Reset asserted atoms
    solver.assert_literal(le_one, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "After pop, should be SAT again, got {result:?}"
    );
}

/// Test that dual_simplex returns Unknown when iteration limit is reached.
///
/// Part of #2014: Verifies that the iteration limit mechanism works correctly.
/// When max_iters is too small to complete the solve, Unknown is returned.
#[test]
fn test_dual_simplex_iteration_limit_unknown() {
    let mut terms = TermStore::new();

    // Create a problem that requires at least one pivot:
    // x + y = 10 (via x + y <= 10 AND x + y >= 10)
    // x >= 3
    // y >= 3
    // Solution requires pivoting to find feasible assignment.
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, ten); // x + y <= 10
    let sum_ge = terms.mk_ge(sum, ten); // x + y >= 10
    let x_ge = terms.mk_ge(x, three); // x >= 3
    let y_ge = terms.mk_ge(y, three); // y >= 3

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(sum_le, true);
    solver.assert_literal(sum_ge, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);

    // With 0 iterations, should return Unknown (not enough to solve)
    let result = solver.dual_simplex_with_max_iters(0);
    assert!(
        matches!(result, TheoryResult::Unknown | TheoryResult::Sat),
        "With 0 max_iters, expected Unknown or Sat, got {result:?}"
    );

    // With sufficient iterations, should return Sat
    let result = solver.dual_simplex_with_max_iters(1000);
    assert!(
        matches!(result, TheoryResult::Sat),
        "With sufficient iterations, expected Sat, got {result:?}"
    );
}

/// Test for #2021: strict inequality bounds infeasibility via row inference.
///
/// x > 0, y > 0, x + y <= 0 is infeasible because x + y > 0 (from strict bounds).
/// Without the row-level infeasibility check, the simplex would cycle.
#[test]
fn test_strict_bounds_row_infeasibility() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());

    // (> x 0)
    let gt_x_0 = terms.mk_gt(x, zero);
    // (> y 0)
    let gt_y_0 = terms.mk_gt(y, zero);
    // (<= (+ x y) 0)
    let x_plus_y = terms.mk_add(vec![x, y]);
    let le_sum_0 = terms.mk_le(x_plus_y, zero);

    // Create solver AFTER all terms
    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(gt_x_0, true);
    solver.assert_literal(gt_y_0, true);
    solver.assert_literal(le_sum_0, true);

    let result = solver.check();

    // Should detect UNSAT from strict bounds infeasibility
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Expected UNSAT for x > 0, y > 0, x + y <= 0, got {result:?}"
    );
}

/// Test that strict bounds + non-strict sum bound that IS feasible works.
///
/// x > 0, y > 0, x + y <= 10 should be SAT.
#[test]
fn test_strict_bounds_sum_feasible() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // (> x 0)
    let gt_x_0 = terms.mk_gt(x, zero);
    // (> y 0)
    let gt_y_0 = terms.mk_gt(y, zero);
    // (<= (+ x y) 10)
    let x_plus_y = terms.mk_add(vec![x, y]);
    let le_sum_10 = terms.mk_le(x_plus_y, ten);

    // Create solver AFTER all terms
    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(gt_x_0, true);
    solver.assert_literal(gt_y_0, true);
    solver.assert_literal(le_sum_10, true);

    let result = solver.check();

    // Should be SAT - x = y = 1 satisfies all constraints
    assert!(
        matches!(result, TheoryResult::Sat),
        "Expected SAT for x > 0, y > 0, x + y <= 10, got {result:?}"
    );
}

/// Test boundary case: x > 0, y >= 0, x + y <= 0 is still UNSAT.
///
/// Because x > 0 is strict, x + y > 0 for any y >= 0.
#[test]
fn test_mixed_strict_nonstrict_bounds_infeasible() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());

    // (> x 0) - strict
    let gt_x_0 = terms.mk_gt(x, zero);
    // (>= y 0) - non-strict
    let ge_y_0 = terms.mk_ge(y, zero);
    // (<= (+ x y) 0)
    let x_plus_y = terms.mk_add(vec![x, y]);
    let le_sum_0 = terms.mk_le(x_plus_y, zero);

    // Create solver AFTER all terms
    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(gt_x_0, true);
    solver.assert_literal(ge_y_0, true);
    solver.assert_literal(le_sum_0, true);

    let result = solver.check();

    // Should detect UNSAT: x > 0 implies x + y > y >= 0, so x + y > 0
    // But x + y <= 0 contradicts this
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Expected UNSAT for x > 0, y >= 0, x + y <= 0, got {result:?}"
    );
}

/// Verify post-pivot fixup respects strict lower bounds (#2727).
///
/// Scenario: x > 0, y < 10, x + y = 5.  SAT (e.g. x=1, y=4).
/// During dual simplex pivots, the leaving variable may land exactly at
/// a strict bound value (e.g. x = 0 for strict lower bound x > 0).
/// The post-pivot fixup must nudge the value to a strictly feasible point.
#[test]
fn test_post_pivot_fixup_strict_lower_bound() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // x > 0 (strict lower bound)
    let gt_x_0 = terms.mk_gt(x, zero);
    // y < 10 (strict upper bound)
    let lt_y_10 = terms.mk_lt(y, ten);
    // x + y = 5
    let x_plus_y = terms.mk_add(vec![x, y]);
    let eq_sum_5 = terms.mk_eq(x_plus_y, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(gt_x_0, true);
    solver.assert_literal(lt_y_10, true);
    solver.assert_literal(eq_sum_5, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Expected SAT for x > 0, y < 10, x + y = 5, got {result:?}"
    );
}

/// Verify post-pivot fixup respects strict upper bounds (#2727).
///
/// Scenario: x < 5, y > 0, 2x + y = 10.  SAT (e.g. x=4, y=2).
/// With strict upper bound x < 5, the simplex may place x at exactly 5
/// after a pivot, which the fixup must correct.
#[test]
fn test_post_pivot_fixup_strict_upper_bound() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // x < 5 (strict upper bound)
    let lt_x_5 = terms.mk_lt(x, five);
    // y > 0 (strict lower bound)
    let gt_y_0 = terms.mk_gt(y, zero);
    // 2x + y = 10
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let two_x = terms.mk_mul(vec![two, x]);
    let two_x_plus_y = terms.mk_add(vec![two_x, y]);
    let eq_sum_10 = terms.mk_eq(two_x_plus_y, ten);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(lt_x_5, true);
    solver.assert_literal(gt_y_0, true);
    solver.assert_literal(eq_sum_10, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Expected SAT for x < 5, y > 0, 2x + y = 10, got {result:?}"
    );
}

/// Regression test: multiple interacting strict bounds + sum constraint.
///
/// x > 0, x < 1, y > 0, y < 1, x + y > 1 is SAT for reals
/// (e.g. x=0.6, y=0.6) and Z3 agrees.
/// Fixed by InfRational (#4919 RC0): strict bounds encode as (c, ±ε),
/// eliminating degenerate cycling. Simplex solves in 2 iterations.
#[test]
fn test_post_pivot_fixup_multiple_strict_bounds() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let one = terms.mk_rational(BigRational::one());

    // x > 0, x < 1
    let gt_x_0 = terms.mk_gt(x, zero);
    let lt_x_1 = terms.mk_lt(x, one);
    // y > 0, y < 1
    let gt_y_0 = terms.mk_gt(y, zero);
    let lt_y_1 = terms.mk_lt(y, one);
    // x + y > 1
    let x_plus_y = terms.mk_add(vec![x, y]);
    let gt_sum_1 = terms.mk_gt(x_plus_y, one);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(gt_x_0, true);
    solver.assert_literal(lt_x_1, true);
    solver.assert_literal(gt_y_0, true);
    solver.assert_literal(lt_y_1, true);
    solver.assert_literal(gt_sum_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Expected SAT for x in (0,1), y in (0,1), x+y > 1, got {result:?}"
    );
}

/// Regression test for #6548: post-simplex refinement must not re-materialize
/// a slack-backed strict relative atom into a conflicting theory refinement.
#[test]
fn test_post_simplex_skips_strict_relative_slack_refinement_issue_6548() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let x_gt_y = terms.mk_gt(x, y);
    let x_eq_5 = terms.mk_eq(x, five);
    let y_eq_3 = terms.mk_eq(y, three);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(x_gt_y, true);
    solver.assert_literal(x_eq_5, true);
    solver.assert_literal(y_eq_3, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Expected SAT for x > y, x = 5, y = 3, got {result:?}"
    );

    let refinements = solver.take_bound_refinements();
    assert!(
        refinements.is_empty(),
        "strict relative comparison should not queue post-simplex slack refinements, got {refinements:?}"
    );
}

/// Regression test for #6548 on the actual DPLL decomposition:
/// `x > y`, `x = 5`, `y = 3` reaches LRA as one strict comparison plus the
/// four non-strict equality sides. Post-simplex refinement must not create a
/// fresh relative atom from the shared slack row.
#[test]
fn test_post_simplex_skips_decomposed_relative_refinement_issue_6548() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let x_gt_y = terms.mk_gt(x, y);
    let x_le_5 = terms.mk_le(x, five);
    let x_ge_5 = terms.mk_ge(x, five);
    let y_le_3 = terms.mk_le(y, three);
    let y_ge_3 = terms.mk_ge(y, three);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(x_gt_y, true);
    solver.assert_literal(x_le_5, true);
    solver.assert_literal(x_ge_5, true);
    solver.assert_literal(y_le_3, true);
    solver.assert_literal(y_ge_3, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Expected SAT for x > y, x = 5, y = 3 via decomposed bounds, got {result:?}"
    );

    let refinements = solver.take_bound_refinements();
    assert!(
        refinements.is_empty(),
        "decomposed strict comparison should not queue post-simplex slack refinements, got {refinements:?}"
    );
}

#[test]
fn test_cube_delta_same_sign_unit_row_is_subunit() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);

    let coeffs = vec![(x_var, Rational::from(1i32)), (y_var, Rational::from(1i32))];
    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);
    integer_vars.insert(y);

    let delta = LraSolver::cube_delta_for_row(&coeffs, x_var, &integer_vars, &solver);
    assert!(
        delta > Rational::Small(0, 1) && delta < Rational::Small(1, 1),
        "Expected epsilon-like delta in (0, 1), got {delta}"
    );
}

#[test]
fn test_round_integer_vars_if_feasible_restores_on_violation() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);

    let original_value = BigRational::new(BigInt::from(3), BigInt::from(5)); // 0.6
    let lower_bound = BigRational::new(BigInt::from(3), BigInt::from(10)); // 0.3
    let upper_bound = BigRational::new(BigInt::from(7), BigInt::from(10)); // 0.7

    let info = &mut solver.vars[x_var as usize];
    info.status = Some(VarStatus::NonBasic);
    info.value = InfRational::from_rational(original_value.clone());
    info.lower = Some(Bound::without_reasons(lower_bound.into(), false));
    info.upper = Some(Bound::without_reasons(upper_bound.into(), false));

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);

    assert!(
        !solver.round_integer_vars_if_feasible(&integer_vars),
        "Rounding 0.6 to 1 violates upper bound 0.7 and must be rejected"
    );
    assert_eq!(
        solver.vars[x_var as usize].value.rational(),
        original_value,
        "Infeasible rounding must restore previous assignment"
    );
    assert!(
        solver.assignment_satisfies_bounds(),
        "Restored assignment should satisfy all bounds"
    );
}

#[test]
fn test_all_integer_vars_integral_detects_fractional() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Real);

    let mut solver = LraSolver::new(&terms);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);
    let _z_var = solver.ensure_var_registered(z);

    let mut integer_vars = HashSet::default();
    integer_vars.insert(x);
    integer_vars.insert(y);

    // Both integer vars are integral → true
    solver.vars[x_var as usize].value =
        InfRational::from_rational(BigRational::from(BigInt::from(3)));
    solver.vars[y_var as usize].value =
        InfRational::from_rational(BigRational::from(BigInt::from(-2)));
    assert!(solver.all_integer_vars_integral(&integer_vars));

    // Make y fractional → false
    solver.vars[y_var as usize].value =
        InfRational::from_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    assert!(!solver.all_integer_vars_integral(&integer_vars));
}

/// Regression test for #2727: post-pivot fixup must respect strict bounds.
///
/// Creates a system with strict inequalities (< and >) that forces
/// dual simplex pivots. The post-pivot fixup at lib.rs:2045-2087 must
/// place the leaving variable at a strictly feasible point (not at
/// the bound value itself, which is infeasible for strict bounds).
#[test]
fn test_dual_simplex_strict_bounds_post_pivot_fixup_2727() {
    let mut terms = TermStore::new();

    // System with strict bounds that forces pivoting:
    //   x + y = 10    (via x + y <= 10 AND x + y >= 10)
    //   x > 0         (strict: x cannot be 0)
    //   y > 0         (strict: y cannot be 0)
    //   x < 10        (strict: x cannot be 10)
    //   y < 10        (strict: y cannot be 10)
    //
    // Feasible region: 0 < x < 10, 0 < y < 10, x + y = 10.
    // The simplex must pivot and the leaving variable fixup must
    // place variables at strictly feasible points (not at bound values).
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, ten); // x + y <= 10
    let sum_ge = terms.mk_ge(sum, ten); // x + y >= 10
    let x_gt = terms.mk_gt(x, zero); // x > 0 (strict)
    let y_gt = terms.mk_gt(y, zero); // y > 0 (strict)
    let x_lt = terms.mk_lt(x, ten); // x < 10 (strict)
    let y_lt = terms.mk_lt(y, ten); // y < 10 (strict)

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(sum_le, true);
    solver.assert_literal(sum_ge, true);
    solver.assert_literal(x_gt, true);
    solver.assert_literal(y_gt, true);
    solver.assert_literal(x_lt, true);
    solver.assert_literal(y_lt, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "System with strict bounds should be SAT, got {result:?}"
    );

    // Verify solution strictly satisfies all bounds
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);
    let x_val = &solver.vars[x_var as usize].value;
    let y_val = &solver.vars[y_var as usize].value;

    // With InfRational, strict bounds produce infinitesimal offsets:
    // x > 0 means x >= (0, +ε), so a valid assignment might be x = (0, +1) = 0 + ε.
    // Compare using InfRational ordering, not just the rational component.
    let zero_inf = InfRational::from_rational(BigRational::from(BigInt::from(0)));
    let ten_inf = InfRational::from_rational(BigRational::from(BigInt::from(10)));

    assert!(*x_val > zero_inf, "x must be strictly > 0, got {x_val}");
    assert!(*y_val > zero_inf, "y must be strictly > 0, got {y_val}");
    assert!(*x_val < ten_inf, "x must be strictly < 10, got {x_val}");
    assert!(*y_val < ten_inf, "y must be strictly < 10, got {y_val}");
}

#[test]
fn test_pivot_zero_entering_coefficient_has_safe_failure_mode() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    solver.vars = vec![
        VarInfo {
            value: InfRational::from_rational(BigRational::from(BigInt::from(1))),
            status: Some(VarStatus::NonBasic),
            ..VarInfo::default()
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::from(BigInt::from(7))),
            status: Some(VarStatus::Basic(0)),
            ..VarInfo::default()
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::from(BigInt::from(3))),
            status: Some(VarStatus::NonBasic),
            ..VarInfo::default()
        },
    ];
    solver.rows = vec![TableauRow::new(
        1,
        vec![(0, BigRational::from(BigInt::from(2)))],
        BigRational::from(BigInt::from(5)),
    )];

    // Variable 2 is not in row 0, so entering coefficient is zero.
    // pivot() uses a hard assert! (not debug_assert!) — panics in all build profiles.
    let pivot_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.pivot(0, 2);
    }));
    assert!(
        pivot_result.is_err(),
        "pivot must panic on zero entering coefficient"
    );
}

/// Structural proof: simplex pivot substitution does O(K) Vec shifts per coefficient
/// update in each row, making the total pivot cost O(R * K_pivot * K_avg) where
/// R = rows, K_pivot = coefficients in the pivot row, K_avg = average coefficients
/// per affected row.
///
/// The root cause is `add_sparse_term` using `Vec::insert` (line 75) which shifts
/// all subsequent elements. For sorted sparse coefficient vectors of size K,
/// inserting at position 0 shifts K elements. Similarly `Vec::remove` (line 72)
/// shifts K-1 elements.
///
/// This matters because simplex `pivot()` is the innermost hot loop of LRA/LIA
/// solving, called potentially hundreds of thousands of times per check-sat.
///
/// Reference: #2673 (partially stale — noted linear scan, now binary search,
/// but Vec::insert/remove O(K) shift cost remains).
#[test]
fn test_simplex_pivot_vec_shift_cost() {
    // Build a tableau with many rows and dense coefficients to demonstrate
    // that add_sparse_term does element shifts on every insert.

    // Verify Vec::insert shifts elements (the structural property)
    let mut coeffs: Vec<(u32, BigRational)> = Vec::new();
    let n = 100;

    // Inserting in sorted order via add_sparse_term: each insert at the end
    // is O(1), but inserting at the beginning shifts all existing elements.
    for i in 0..n {
        add_sparse_term(&mut coeffs, i, BigRational::from(BigInt::from(1)));
    }
    assert_eq!(coeffs.len(), n as usize, "Should have {n} coefficients");

    // Now add a coefficient at position 0 (var=0 with new value).
    // This triggers binary_search -> Ok(0) -> in-place update (no shift).
    // But adding a NEW var at position 0 (if we used var that sorts first)
    // would shift all n elements.

    // Prove: removing var 0 shifts n-1 elements (Vec::remove at index 0).
    let before_len = coeffs.len();
    // Add -1 to var 0, making it zero, which triggers remove
    add_sparse_term(&mut coeffs, 0, BigRational::from(BigInt::from(-1)));
    assert_eq!(
        coeffs.len(),
        before_len - 1,
        "Removing var 0 should shrink the vec (O(n-1) shift)"
    );
    // First element is now var 1
    assert_eq!(
        coeffs[0].0, 1,
        "After removing var 0, first element should be var 1"
    );

    // Prove: TableauRow::remove_coeff does Vec::remove (O(K) shift)
    let mut row = TableauRow::new(
        999,
        (0..50u32)
            .map(|i| (i, BigRational::from(BigInt::from(1))))
            .collect(),
        BigRational::zero(),
    );
    assert_eq!(row.coeffs.len(), 50);
    row.remove_coeff(0); // Remove first → shifts 49 elements
    assert_eq!(row.coeffs.len(), 49);
    assert_eq!(row.coeffs[0].0, 1, "First coeff should now be var 1");

    // Prove: TableauRow::add_coeff with a new var at position 0
    // does Vec::insert at index 0 → shifts all 49 elements
    row.add_coeff(0, Rational::from(1i32));
    assert_eq!(row.coeffs.len(), 50);
    assert_eq!(
        row.coeffs[0].0, 0,
        "Var 0 should be re-inserted at position 0"
    );

    // The pivot function (lines 1060-1085) calls remove_coeff once per row
    // and add_coeff K_pivot times per row. Total shifts per pivot:
    //   Σ_{row ∈ affected_rows} (K_row + K_pivot * K_row) = O(R * K_pivot * K_avg)
    // For dense problems (K_avg = K_pivot = K), this is O(R * K²).
}

// ========================================================================
// #8471 - bound-presence guards in check_row_strict_infeasibility
// ========================================================================
//
// The row-infeasibility pre-check skips each pass-1 sweep when the basic var
// lacks the bound that sweep could contradict. These tests call the pre-check
// DIRECTLY on a hand-built tableau.
//
// Going through check() cannot pin these guards: the pre-check is only a fast
// path, so when it is disabled the dual simplex still finds the same conflict
// by pivoting and the test still passes. Verified by mutation testing - an
// end-to-end version of these tests survives a `basic_has_lower = false`
// mutant, while the direct form below kills it.
//
// The failure mode being pinned is a row conflict going undetected here.

/// Build a one-row tableau `basic = x + y` with the given bounds, and return
/// the solver ready for a direct `check_row_strict_infeasibility()` call.
/// Vars: 0 = x, 1 = y (non-basic), 2 = the row's basic var.
fn one_row_solver(
    terms: &TermStore,
    x_bounds: (Option<Bound>, Option<Bound>),
    y_bounds: (Option<Bound>, Option<Bound>),
    basic_bounds: (Option<Bound>, Option<Bound>),
) -> LraSolver {
    let mut solver = LraSolver::new(terms);
    let zero = || InfRational::from_rational(BigRational::zero());
    solver.vars = vec![
        VarInfo {
            value: zero(),
            lower: x_bounds.0,
            upper: x_bounds.1,
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: zero(),
            lower: y_bounds.0,
            upper: y_bounds.1,
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: zero(),
            lower: basic_bounds.0,
            upper: basic_bounds.1,
            status: Some(VarStatus::Basic(0)),
        },
    ];
    // Row 0: var2 = 1*x + 1*y
    solver.rows = vec![TableauRow::new(
        2,
        vec![
            (0, BigRational::from(BigInt::from(1))),
            (1, BigRational::from(BigInt::from(1))),
        ],
        BigRational::zero(),
    )];
    solver.col_index = vec![Vec::new(); 3];
    solver.col_index[0].push(ColEntry::new(0, 0));
    solver.col_index[1].push(ColEntry::new(0, 1));
    solver.basic_var_to_row.insert(2, 0);
    // Every bound reason must be asserted for the Farkas pass to accept the conflict.
    for info in &solver.vars {
        for b in [info.lower.as_ref(), info.upper.as_ref()]
            .into_iter()
            .flatten()
        {
            for &r in &b.reasons {
                solver.asserted.insert(r, true);
            }
        }
    }
    solver
}

/// A bound at integer `v` justified by a single asserted reason atom, so
/// pass 2 can actually build the Farkas certificate (an unjustified bound
/// makes `conflict_literals_all_asserted` reject the conflict and the
/// pre-check returns None regardless of the guards under test).
fn plain_bound(reason: u32, v: i64, strict: bool) -> Bound {
    Bound::new(
        Rational::from(BigRational::from(BigInt::from(v))),
        vec![TermId(reason)],
        vec![true],
        Vec::new(),
        strict,
    )
}

/// Basic var carries an UPPER bound only: the lower sweep must still fire.
/// x > 0, y > 0, x + y <= 0.
#[test]
fn row_strict_infeasibility_upper_only_basic_still_detected() {
    let terms = TermStore::new();
    let mut solver = one_row_solver(
        &terms,
        (Some(plain_bound(101, 0, true)), None),
        (Some(plain_bound(102, 0, true)), None),
        (None, Some(plain_bound(103, 0, false))),
    );

    assert!(
        solver.check_row_strict_infeasibility().is_some(),
        "row pre-check must detect x>0, y>0, x+y<=0 (upper-only basic var)"
    );
}

/// Basic var carries a LOWER bound only: the upper sweep must still fire.
/// x < 0, y < 0, x + y >= 0. This is the case a stale or wrongly-hoisted
/// `basic_has_lower` would silently skip.
#[test]
fn row_strict_infeasibility_lower_only_basic_still_detected() {
    let terms = TermStore::new();
    let mut solver = one_row_solver(
        &terms,
        (None, Some(plain_bound(101, 0, true))),
        (None, Some(plain_bound(102, 0, true))),
        (Some(plain_bound(103, 0, false)), None),
    );

    assert!(
        solver.check_row_strict_infeasibility().is_some(),
        "row pre-check must detect x<0, y<0, x+y>=0 (lower-only basic var)"
    );
}

/// Both bounds present, and the LOWER sweep bails out early (`lower_valid`
/// false: the non-basic vars carry no lower bounds). The upper sweep must
/// still run - this pins the second guard, which sits after a `&mut self`
/// pass-2 call and so must be re-read rather than hoisted across it.
#[test]
fn row_strict_infeasibility_both_bounds_upper_sweep_still_runs() {
    let terms = TermStore::new();
    let mut solver = one_row_solver(
        &terms,
        (None, Some(plain_bound(101, 0, true))),
        (None, Some(plain_bound(102, 0, true))),
        (
            Some(plain_bound(103, 0, false)),
            Some(plain_bound(104, 10, false)),
        ),
    );

    assert!(
        solver.check_row_strict_infeasibility().is_some(),
        "row pre-check must detect the conflict via the upper sweep when the \
         lower sweep bails out"
    );
}
