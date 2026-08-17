// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod conflict_soundness;

// ========================================================================
// LIA Completeness Property Tests (#800)
// ========================================================================
//
// These tests verify algebraic properties that ensure LIA completeness.
// They catch bugs like #793 where the solver returned Unknown for decidable QF_LIA.

use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 100,
        max_shrink_iters: 10,
        .. ProptestConfig::default()
    })]

    /// Property: If A = B, then (A + k) = (B + k) must be implied.
    /// Equivalently: A = B implies A + k != B + k is UNSAT.
    ///
    /// This is the exact property that #793 violated.
    #[test]
    fn proptest_equality_implies_offset_equality(
        k in -50i64..50i64,
    ) {
        let mut terms = TermStore::new();

        let a = terms.mk_var("A", Sort::Int);
        let b = terms.mk_var("B", Sort::Int);
        let k_term = terms.mk_int(BigInt::from(k));
        let one = terms.mk_int(BigInt::from(1));

        // A = B (using multiplication by 1 to match PDR's pattern)
        let one_times_b = terms.mk_mul(vec![one, b]);
        let eq_ab = terms.mk_eq(a, one_times_b);

        // (A + k) != (B + k)
        let a_plus_k = terms.mk_add(vec![a, k_term]);
        let b_plus_k = terms.mk_add(vec![b, k_term]);
        let diseq = terms.mk_eq(a_plus_k, b_plus_k);

        // Create solver and assert: A = B AND (A + k) != (B + k)
        // This must be UNSAT because A = B => A + k = B + k
        let mut solver = LiaSolver::new(&terms);
        solver.assert_literal(eq_ab, true);
        solver.assert_literal(diseq, false); // NOT (A + k = B + k), i.e., A + k != B + k

        let result = solver.check();

        // Must be UNSAT. Unknown is a bug (this is what #793 returned).
        prop_assert!(
            matches!(result, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)),
            "A = B AND (A + k) != (B + k) should be UNSAT, got {:?}",
            result
        );
    }

    /// Property: Transitivity of equality.
    /// If A = B and B = C, then A = C must be implied.
    /// Equivalently: A = B AND B = C AND A != C is UNSAT.
    #[test]
    fn proptest_equality_transitivity(
        _val in -50i64..50i64, // proptest needs at least one parameter
    ) {
        let mut terms = TermStore::new();

        let a = terms.mk_var("A", Sort::Int);
        let b = terms.mk_var("B", Sort::Int);
        let c = terms.mk_var("C", Sort::Int);

        // A = B
        let eq_ab = terms.mk_eq(a, b);
        // B = C
        let eq_bc = terms.mk_eq(b, c);
        // A = C
        let eq_ac = terms.mk_eq(a, c);

        // Assert: A = B, B = C, A != C
        let mut solver = LiaSolver::new(&terms);
        solver.assert_literal(eq_ab, true);
        solver.assert_literal(eq_bc, true);
        solver.assert_literal(eq_ac, false); // A != C

        let result = solver.check();

        // Must be UNSAT by transitivity.
        prop_assert!(
            matches!(result, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)),
            "A = B AND B = C AND A != C must be UNSAT, got {:?}",
            result
        );
    }

    /// Property: Reflexivity of equality.
    /// `X != X` must be UNSAT.
    #[test]
    fn proptest_reflexivity(
        _val in -50i64..50i64, // proptest needs at least one parameter
    ) {
        let mut terms = TermStore::new();

        // X != X should be UNSAT (reflexivity of equality)
        let x = terms.mk_var("X", Sort::Int);
        let eq_xx = terms.mk_eq(x, x);

        let mut solver = LiaSolver::new(&terms);
        solver.assert_literal(eq_xx, false); // X != X

        let result = solver.check();

        prop_assert!(
            matches!(result, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)),
            "X != X must be UNSAT (reflexivity), got {:?}",
            result
        );
    }

    /// Property: QF_LIA should never return Unknown on decidable formulas.
    ///
    /// This tests random combinations of linear integer arithmetic constraints:
    /// - Equalities: a = b, a = c + k
    /// - Inequalities: a <= b + k, a < b
    /// - Bounds: a >= k, a <= k
    ///
    /// The solver should return Sat, Unsat, or a split request - never Unknown.
    /// This is the key completeness property that #793 violated.
    #[test]
    fn proptest_no_unknown_on_decidable(
        // Generate random constraint parameters
        c1 in -20i64..20i64,  // constant 1
        c2 in -20i64..20i64,  // constant 2
        c3 in -20i64..20i64,  // constant 3
        constraint_type in 0u8..6u8,  // which type of constraints to generate
    ) {
        let mut terms = TermStore::new();

        // Create all terms first before borrowing for solver
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let k1 = terms.mk_int(BigInt::from(c1));
        let k2 = terms.mk_int(BigInt::from(c2));

        // Generate constraint-specific terms and literals
        let literals: Vec<(TermId, bool)> = match constraint_type {
            0 => {
                // x = k1, x <= k2 (SAT if k1 <= k2, UNSAT otherwise)
                let eq = terms.mk_eq(x, k1);
                let le = terms.mk_le(x, k2);
                vec![(eq, true), (le, true)]
            }
            1 => {
                // x >= k1, x <= k2 (SAT if k1 <= k2, UNSAT if k1 > k2)
                let ge = terms.mk_ge(x, k1);
                let le = terms.mk_le(x, k2);
                vec![(ge, true), (le, true)]
            }
            2 => {
                // x + y = k1, x = k2 (SAT: y = k1 - k2)
                let x_plus_y = terms.mk_add(vec![x, y]);
                let eq1 = terms.mk_eq(x_plus_y, k1);
                let eq2 = terms.mk_eq(x, k2);
                vec![(eq1, true), (eq2, true)]
            }
            3 => {
                // x < y, y < x (UNSAT: antisymmetry)
                // Fixed by integer strict bound canonicalization (#2665):
                // x < y becomes x <= y-1, y < x becomes y <= x-1
                let lt_xy = terms.mk_lt(x, y);
                let lt_yx = terms.mk_lt(y, x);
                vec![(lt_xy, true), (lt_yx, true)]
            }
            4 => {
                // x = y, x != y (UNSAT: contradiction)
                let eq = terms.mk_eq(x, y);
                vec![(eq, true), (eq, false)]
            }
            5 => {
                // k1*x + k2*y = k3 with k1, k2, k3 from input
                // This may or may not have integer solutions
                let k1_term = terms.mk_int(BigInt::from(c1));
                let k2_term = terms.mk_int(BigInt::from(c2));
                let k3_term = terms.mk_int(BigInt::from(c3));
                let k1x = terms.mk_mul(vec![k1_term, x]);
                let k2y = terms.mk_mul(vec![k2_term, y]);
                let sum = terms.mk_add(vec![k1x, k2y]);
                let eq = terms.mk_eq(sum, k3_term);
                vec![(eq, true)]
            }
            _ => vec![]
        };

        // Now create solver and assert literals
        let mut solver = LiaSolver::new(&terms);
        for (lit, polarity) in &literals {
            solver.assert_literal(*lit, *polarity);
        }

        let result = solver.check();

        // QF_LIA is decidable: the solver should NEVER return Unknown
        // It may return:
        // - Sat: satisfiable
        // - Unsat/UnsatWithFarkas: unsatisfiable with proof
        // - NeedSplit/NeedDisequalitySplit: needs DPLL(T) branching
        //
        // Unknown is a completeness bug.
        prop_assert!(
            !matches!(result, TheoryResult::Unknown),
            "QF_LIA should never return Unknown, got {:?} for constraint_type={}, c1={}, c2={}, c3={}",
            result, constraint_type, c1, c2, c3
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 200,
        max_shrink_iters: 20,
        .. ProptestConfig::default()
    })]

    /// Property: Strict inequality edge cases after #2665 canonicalization.
    /// Tests that x < y is correctly canonicalized to x <= y-1 for integers.
    #[test]
    fn proptest_strict_inequality_correctness(
        a_val in -50i64..50i64,
        b_val in -50i64..50i64,
        case in 0u8..8u8,
    ) {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let k1 = terms.mk_int(BigInt::from(a_val));
        let k2 = terms.mk_int(BigInt::from(b_val));

        let (literals, must_be_unsat) = match case {
            0 => {
                // x < x must be UNSAT (irreflexivity)
                let lt = terms.mk_lt(x, x);
                (vec![(lt, true)], true)
            }
            1 => {
                // x < y AND y <= x must be UNSAT
                let lt_xy = terms.mk_lt(x, y);
                let le_yx = terms.mk_le(y, x);
                (vec![(lt_xy, true), (le_yx, true)], true)
            }
            2 => {
                // x < y AND x >= y must be UNSAT
                let lt_xy = terms.mk_lt(x, y);
                let ge_xy = terms.mk_ge(x, y);
                (vec![(lt_xy, true), (ge_xy, true)], true)
            }
            3 => {
                // x < k1 AND x >= k1-1 should be SAT (x = k1-1)
                let lt = terms.mk_lt(x, k1);
                let bound = terms.mk_int(BigInt::from(a_val - 1));
                let ge = terms.mk_ge(x, bound);
                (vec![(lt, true), (ge, true)], false)
            }
            4 => {
                // x < k1 AND x > k1-1 must be UNSAT for integers
                // (x < k1 means x <= k1-1, x > k1-1 means x >= k1, contradiction)
                let lt = terms.mk_lt(x, k1);
                let bound = terms.mk_int(BigInt::from(a_val - 1));
                let gt = terms.mk_lt(bound, x); // bound < x means x > bound
                (vec![(lt, true), (gt, true)], true)
            }
            5 => {
                // x < y AND y < x must be UNSAT (antisymmetry, existing case 3)
                let lt_xy = terms.mk_lt(x, y);
                let lt_yx = terms.mk_lt(y, x);
                (vec![(lt_xy, true), (lt_yx, true)], true)
            }
            6 => {
                // x < k1, x >= k2: SAT iff k2 < k1 (i.e., k2 <= k1-1)
                let lt = terms.mk_lt(x, k1);
                let ge = terms.mk_ge(x, k2);
                (vec![(lt, true), (ge, true)], b_val >= a_val)
            }
            7 => {
                // x < y, y < x+2: should always be SAT (y = x+1)
                let lt_xy = terms.mk_lt(x, y);
                let two = terms.mk_int(BigInt::from(2));
                let x_plus_2 = terms.mk_add(vec![x, two]);
                let lt_y_xp2 = terms.mk_lt(y, x_plus_2);
                (vec![(lt_xy, true), (lt_y_xp2, true)], false)
            }
            _ => unreachable!()
        };

        let mut solver = LiaSolver::new(&terms);
        for (lit, polarity) in &literals {
            solver.assert_literal(*lit, *polarity);
        }
        let result = solver.check();

        // Never return Unknown on decidable QF_LIA
        prop_assert!(
            !matches!(result, TheoryResult::Unknown),
            "QF_LIA strict inequality case {} must not return Unknown, got {:?}",
            case, result
        );

        if must_be_unsat {
            prop_assert!(
                !matches!(result, TheoryResult::Sat),
                "Strict inequality case {} (a={}, b={}) must be UNSAT, got Sat",
                case, a_val, b_val
            );
        } else {
            // When the formula is satisfiable, verify the solver doesn't return false UNSAT.
            // NeedSplit/NeedDisequalitySplit are acceptable (DPLL will find SAT).
            prop_assert!(
                !matches!(result, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)),
                "Strict inequality case {} (a={}, b={}) is satisfiable but got UNSAT",
                case, a_val, b_val
            );
        }
    }
}

/// Integration test for the exact bug pattern from #793.
/// This is the formula that PDR generates for self-inductiveness checks.
#[test]
fn test_lia_equality_implies_offset_equality_exact_pattern() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("A", Sort::Int);
    let b = terms.mk_var("B", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));

    // A = 1 * B (PDR's pattern with multiplication)
    let one_times_b = terms.mk_mul(vec![one, b]);
    let eq = terms.mk_eq(a, one_times_b);

    // (1 + A) != 1 * (1 + B)
    let one_plus_a = terms.mk_add(vec![one, a]);
    let one_plus_b = terms.mk_add(vec![one, b]);
    let one_times_one_plus_b = terms.mk_mul(vec![one, one_plus_b]);
    let diseq = terms.mk_eq(one_plus_a, one_times_one_plus_b);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(diseq, false);

    let result = solver.check();

    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Exact #793 pattern must be UNSAT, got {result:?}"
    );
}
