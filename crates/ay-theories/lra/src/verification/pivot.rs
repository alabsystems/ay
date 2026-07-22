// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Pivot Function Invariants (#2013)
// ========================================================================

/// After pivot, entering_var becomes Basic and leaving_var becomes NonBasic.
///
/// Part of #2013: The pivot operation must correctly swap variable statuses.
#[kani::proof]
#[kani::unwind(3)]
fn proof_pivot_preserves_variable_status() {
    let mut terms = ay_core::term::TermStore::new();
    let x = terms.mk_var("x", ay_core::Sort::Real);
    let y = terms.mk_var("y", ay_core::Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // Create constraint: x + y <= 5
    // This creates a tableau row with a basic slack variable.
    let sum = terms.mk_add(vec![x, y]);
    let le_five = terms.mk_le(sum, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_five, true);

    // Find the row that has x as a non-basic variable
    if solver.rows.is_empty() {
        return; // No tableau to pivot
    }

    let row_idx = 0;
    let entering_var = solver.term_to_var.get(&x).copied();

    if let Some(ev) = entering_var {
        // Check that entering_var has non-zero coefficient in row
        let coeff = solver.rows[row_idx].coeff(ev);
        if coeff.is_zero() {
            return; // Cannot pivot on zero coefficient
        }

        let leaving_var = solver.rows[row_idx].basic_var;

        // Perform pivot
        solver.pivot(row_idx, ev);

        // Verify status swap
        assert!(
            matches!(solver.vars[ev as usize].status, Some(VarStatus::Basic(_))),
            "Entering variable must be Basic after pivot"
        );
        assert!(
            matches!(
                solver.vars[leaving_var as usize].status,
                Some(VarStatus::NonBasic)
            ),
            "Leaving variable must be NonBasic after pivot"
        );
    }
}

/// Pivot with zero coefficient is a no-op (defensive early return).
///
/// Part of #2013: The function handles the degenerate case gracefully.
#[kani::proof]
fn proof_pivot_zero_coeff_is_noop() {
    let mut terms = ay_core::term::TermStore::new();
    let x = terms.mk_var("x", ay_core::Sort::Real);
    let y = terms.mk_var("y", ay_core::Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let le_five = terms.mk_le(x, five);
    let le_ten = terms.mk_le(y, ten);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_five, true);
    solver.assert_literal(le_ten, true);

    if solver.rows.is_empty() {
        return;
    }

    // Find a variable that has ZERO coefficient in row 0
    // (any variable not in the row)
    let row_idx = 0;
    let basic_before = solver.rows[row_idx].basic_var;

    // Pick a variable unrelated to row 0 so its coefficient is zero.
    if let Some(yv) = solver.term_to_var.get(&y).copied() {
        assert!(
            solver.rows[row_idx].coeff(yv).is_zero(),
            "expected unrelated variable to have zero coefficient"
        );
        solver.pivot(row_idx, yv);
        // Should be no-op: basic_var unchanged
        assert_eq!(
            solver.rows[row_idx].basic_var, basic_before,
            "Pivot with zero coeff should not change basic var"
        );
    }
}

/// Pivot preserves the entering variable in the resulting row.
///
/// Part of #2013: After pivot, the new row's basic_var equals entering_var.
#[kani::proof]
#[kani::unwind(3)]
fn proof_pivot_row_has_correct_basic_var() {
    let mut terms = ay_core::term::TermStore::new();
    let x = terms.mk_var("x", ay_core::Sort::Real);
    let y = terms.mk_var("y", ay_core::Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // Create constraint: x + y <= 5
    let sum = terms.mk_add(vec![x, y]);
    let le_five = terms.mk_le(sum, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_five, true);

    if solver.rows.is_empty() {
        return;
    }

    let row_idx = 0;
    if let Some(&xv) = solver.term_to_var.get(&x) {
        let coeff = solver.rows[row_idx].coeff(xv);
        if coeff.is_zero() {
            return;
        }

        // After pivot, the row's basic_var should be xv
        solver.pivot(row_idx, xv);
        assert_eq!(
            solver.rows[row_idx].basic_var, xv,
            "After pivot, row's basic_var should be the entering variable"
        );
    }
}
