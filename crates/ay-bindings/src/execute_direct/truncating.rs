// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact standard-operation route, not a reinterpretation of IEEE fp.rem.
//! Keep both original terms; no private intrinsic or source declaration escapes.

use ay_dpll::api::{Solver, SolverError, Term};

pub(super) fn lower(solver: &mut Solver, x: Term, y: Term) -> Result<Term, SolverError> {
    let r = solver.try_fp_rem(x, y)?;
    let nan = solver.try_fp_is_nan(r)?;
    let not_nan = solver.try_not(nan)?;
    let zero = solver.try_fp_is_zero(r)?;
    let not_zero = solver.try_not(zero)?;
    let r_negative = solver.try_fp_is_negative(r)?;
    let x_negative = solver.try_fp_is_negative(x)?;
    let different_signs = solver.try_xor(r_negative, x_negative)?;
    let correct = solver.try_and_many(&[not_nan, not_zero, different_signs])?;
    let magnitude = solver.try_fp_abs(y)?;
    let negative_magnitude = solver.try_fp_neg(magnitude)?;
    let signed_y = solver.try_ite(x_negative, negative_magnitude, magnitude)?;
    let rne = solver.try_fp_rounding_mode("RNE")?;
    let corrected = solver.try_fp_add(rne, r, signed_y)?;
    solver.try_ite(correct, corrected, r)
}

#[cfg(test)]
mod tests;
