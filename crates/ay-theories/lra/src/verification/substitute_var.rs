// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// substitute_var Invariants (#6194)
// ========================================================================

/// substitute_var produces the same result as the naive remove_coeff + add_coeff loop.
///
/// This is the key correctness property: the optimized O(w log w) sorted-merge
/// must be equivalent to the naive O(w²) approach for all valid inputs.
#[kani::proof]
#[kani::unwind(6)]
fn proof_substitute_var_matches_naive() {
    // Generate symbolic row coefficients (2 terms, variables 1..4)
    let v0: u32 = kani::any();
    let v1: u32 = kani::any();
    kani::assume(v0 >= 1 && v0 <= 4);
    kani::assume(v1 >= 1 && v1 <= 4);
    kani::assume(v0 < v1); // sorted, unique

    let c0: i32 = kani::any();
    let c1: i32 = kani::any();
    kani::assume(c0 != 0 && c0 > -100 && c0 < 100);
    kani::assume(c1 != 0 && c1 > -100 && c1 < 100);

    // entering_var to substitute out (must exist in row)
    let entering: u32 = kani::any();
    kani::assume(entering == v0 || entering == v1);

    // Generate substitution coefficients (1 term)
    let sv: u32 = kani::any();
    kani::assume(sv >= 1 && sv <= 5);

    let sc: i32 = kani::any();
    kani::assume(sc != 0 && sc > -100 && sc < 100);

    // Scale factor
    let scale_val: i32 = kani::any();
    kani::assume(scale_val != 0 && scale_val > -50 && scale_val < 50);

    let row_coeffs = vec![(v0, Rational::from(c0)), (v1, Rational::from(c1))];
    let constant = Rational::from(42i32);
    let subst_coeffs = vec![(sv, Rational::from(sc))];
    let scale = Rational::from(scale_val);

    // --- Optimized path ---
    let mut opt = TableauRow::new_rat(0, row_coeffs.clone(), constant.clone());
    opt.substitute_var(entering, &subst_coeffs, &scale);

    // --- Naive path ---
    // substitute_var(entering, subst_coeffs, scale) means:
    //   remove entering_var, then add c*scale for each (v,c) in subst_coeffs where v != entering
    let mut naive = TableauRow::new_rat(0, row_coeffs, constant.clone());
    naive.remove_coeff(entering);
    for (v, c) in &subst_coeffs {
        if *v != entering {
            naive.add_coeff(*v, c * &scale);
        }
    }

    // Verify equivalence
    assert!(
        opt.coeffs.len() == naive.coeffs.len(),
        "substitute_var length mismatch"
    );
    for i in 0..opt.coeffs.len() {
        assert!(
            opt.coeffs[i].0 == naive.coeffs[i].0,
            "variable mismatch at position"
        );
        assert!(
            opt.coeffs[i].1 == naive.coeffs[i].1,
            "coefficient mismatch at position"
        );
    }

    // Constant must be unchanged (caller handles constant adjustment)
    assert!(
        opt.constant == constant,
        "substitute_var must not modify constant"
    );
}

/// substitute_var preserves the sorted invariant of coefficients.
#[kani::proof]
#[kani::unwind(6)]
fn proof_substitute_var_preserves_sorted() {
    let v0: u32 = kani::any();
    let v1: u32 = kani::any();
    kani::assume(v0 >= 1 && v0 <= 3);
    kani::assume(v1 >= 1 && v1 <= 3);
    kani::assume(v0 < v1);

    let c0: i32 = kani::any();
    let c1: i32 = kani::any();
    kani::assume(c0 != 0 && c0 > -50 && c0 < 50);
    kani::assume(c1 != 0 && c1 > -50 && c1 < 50);

    let entering = v0;
    let sv: u32 = kani::any();
    kani::assume(sv >= 1 && sv <= 4);
    let sc: i32 = kani::any();
    kani::assume(sc != 0 && sc > -50 && sc < 50);
    let scale_val: i32 = kani::any();
    kani::assume(scale_val != 0 && scale_val > -50 && scale_val < 50);

    let mut row = TableauRow::new_rat(
        0,
        vec![(v0, Rational::from(c0)), (v1, Rational::from(c1))],
        Rational::zero(),
    );
    row.substitute_var(
        entering,
        &[(sv, Rational::from(sc))],
        &Rational::from(scale_val),
    );

    // Verify sorted invariant
    for i in 1..row.coeffs.len() {
        assert!(
            row.coeffs[i - 1].0 < row.coeffs[i].0,
            "coefficients must be strictly sorted by variable index"
        );
    }

    // Verify no zero coefficients remain
    for (_, c) in &row.coeffs {
        assert!(!c.is_zero(), "zero coefficients must be filtered out");
    }
}

/// substitute_var on empty row with empty subst is a no-op.
/// With non-empty subst, additions are applied even if entering_var is absent.
#[kani::proof]
fn proof_substitute_var_empty_row() {
    // Empty row + empty subst = no-op
    let mut row = TableauRow::new_rat(0, vec![], Rational::from(7i32));
    row.substitute_var(1, &[], &Rational::from(2i32));
    assert!(row.coeffs.is_empty(), "empty row + empty subst stays empty");
    assert!(row.constant == Rational::from(7i32), "constant unchanged");
}

/// substitute_var with empty substitution just removes entering_var.
#[kani::proof]
fn proof_substitute_var_empty_subst() {
    let mut row = TableauRow::new_rat(
        0,
        vec![(1, Rational::from(3i32)), (2, Rational::from(5i32))],
        Rational::from(10i32),
    );
    row.substitute_var(1, &[], &Rational::from(1i32));
    assert!(row.coeffs.len() == 1, "one variable removed");
    assert!(row.coeffs[0].0 == 2, "remaining variable is 2");
    assert!(
        row.coeffs[0].1 == Rational::from(5i32),
        "remaining coefficient unchanged"
    );
    assert!(row.constant == Rational::from(10i32), "constant unchanged");
}
