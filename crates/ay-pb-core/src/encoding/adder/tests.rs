// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the adder encoding and its comparator.

use super::encode_adder;

/// Regression: auxiliary ids past `i32::MAX` used to wrap through
/// `as i32` into `i32::MIN`, whose negation panicked (or, unchecked,
/// produced a clause over the wrong variable). The adder now declines.
#[test]
fn declines_when_auxiliaries_leave_the_dimacs_range() -> Result<(), String> {
    let mut clauses = Vec::new();
    let mut next_var = u32::try_from(i32::MAX).map_err(|err| err.to_string())?;
    if encode_adder(&[3, 5], &[1, 2], 4, &mut clauses, &mut next_var).is_some() {
        return Err("an auxiliary past i32::MAX must decline the row".into());
    }
    Ok(())
}

/// Regression: an `i32::MIN` input literal passes through the adder tree
/// unchanged into the comparator, whose bare `-r_bit` overflowed on it.
/// The adder now declines the row, as its contract says.
#[test]
fn declines_an_i32_min_input_literal() -> Result<(), String> {
    let mut clauses = Vec::new();
    let mut next_var = 6;
    if encode_adder(&[1, 2], &[i32::MIN, 5], 1, &mut clauses, &mut next_var).is_some() {
        return Err("an i32::MIN input literal must decline the row".into());
    }
    Ok(())
}

/// The clauses restricted to `inputs` (literal `i + 1` is `inputs[i]`),
/// decided by unit propagation: `Some(true)` when every clause ends
/// satisfied, `Some(false)` on a conflict, `None` if propagation stalls.
/// The adder is a functional circuit (every auxiliary is defined by an
/// equivalence over earlier bits), so propagation from the inputs decides it.
fn propagate(clauses: &[Vec<i32>], inputs: &[bool], num_vars: u32) -> Option<bool> {
    // The test rows need a few thousand variables; refuse anything huge.
    let width = usize::try_from(num_vars).ok().filter(|&w| w <= 1 << 20)?;
    let mut value: Vec<Option<bool>> = vec![None; width];
    for (slot, &input) in value.iter_mut().zip(inputs) {
        *slot = Some(input);
    }
    let lit_value = |value: &[Option<bool>], lit: i32| -> Option<Option<bool>> {
        let index = usize::try_from(lit.unsigned_abs()).ok()?.checked_sub(1)?;
        Some(value.get(index)?.map(|v| v == (lit > 0)))
    };
    loop {
        let mut changed = false;
        for clause in clauses {
            let mut open = None;
            let mut open_count = 0usize;
            let mut satisfied = false;
            for &lit in clause {
                match lit_value(&value, lit)? {
                    Some(true) => satisfied = true,
                    Some(false) => {}
                    None => {
                        open = Some(lit);
                        open_count = open_count.saturating_add(1);
                    }
                }
            }
            if satisfied {
                continue;
            }
            match (open_count, open) {
                (0, _) => return Some(false),
                (1, Some(lit)) => {
                    let index = usize::try_from(lit.unsigned_abs()).ok()?.checked_sub(1)?;
                    *value.get_mut(index)? = Some(lit > 0);
                    changed = true;
                }
                _ => {}
            }
        }
        if !changed {
            return value.iter().all(Option::is_some).then_some(true);
        }
    }
}

/// Regression: the adder tree appends a structural carry bit per level
/// when the top bits of both operands are literals, so the sum of these
/// five coefficients (total below `i128::MAX`) is 129 bits wide and the
/// comparator evaluated `rhs >> 128`, which overflowed (a panic under
/// overflow checks; without them the shift wrapped to `rhs >> 0` and
/// compared against the wrong bit). The encoding must now agree with the
/// constraint on every input assignment.
#[test]
fn compares_a_result_wider_than_i128() -> Result<(), String> {
    let coeffs: [i128; 5] = [
        61_426_560_348_576_772_096_418_911_863_765_901_303,
        39_432_297_459_926_570_641_314_223_123_637_353_785,
        23_691_439_105_683_716_836_429_890_520_888,
        2_472_423_123_907_618_291_651_033_658_775_317_395,
        5_018_907_387_860_129_152_038_707_846_506_994_752,
    ];
    let lits = [1, 2, 3, 4, 5];
    let total = coeffs
        .iter()
        .try_fold(0i128, |acc, &c| acc.checked_add(c))
        .ok_or("the test coefficients sum within i128")?;
    let [c0, c1, _, c3, _] = coeffs;
    let pair = c0.checked_add(c1).ok_or("c0 + c1 fits i128")?;
    for rhs in [c3, c0, pair, total] {
        let mut clauses = Vec::new();
        let mut next_var = 6;
        encode_adder(&coeffs, &lits, rhs, &mut clauses, &mut next_var)
            .ok_or("an in-range row must encode")?;
        let num_vars = next_var.checked_sub(1).ok_or("next_var starts at 6")?;
        for mask in 0u32..32 {
            let inputs: Vec<bool> = (0u32..5)
                .map(|bit| mask.checked_shr(bit).is_some_and(|m| m & 1 == 1))
                .collect();
            let mut sum: i128 = 0;
            for (&coeff, &on) in coeffs.iter().zip(&inputs) {
                if on {
                    sum = sum.checked_add(coeff).ok_or("subset sum fits i128")?;
                }
            }
            let expected = sum >= rhs;
            let encoded = propagate(&clauses, &inputs, num_vars)
                .ok_or_else(|| format!("propagation stalled for rhs {rhs}, mask {mask}"))?;
            if encoded != expected {
                return Err(format!(
                    "rhs {rhs}, mask {mask}: constraint says {expected}, CNF says {encoded}"
                ));
            }
        }
    }
    Ok(())
}

/// The in-range encoding still succeeds and allocates auxiliaries from
/// `next_var` upward.
#[test]
fn encodes_in_range_rows() -> Result<(), String> {
    let mut clauses = Vec::new();
    let mut next_var = 3;
    encode_adder(&[3, 5], &[1, 2], 4, &mut clauses, &mut next_var)
        .ok_or("an in-range row must encode")?;
    if next_var <= 3 || clauses.is_empty() {
        return Err(format!(
            "expected auxiliaries and clauses, got next_var {next_var}, {} clauses",
            clauses.len()
        ));
    }
    Ok(())
}
