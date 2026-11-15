// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact model-field to bitvector construction; never route fractions via i64.

use super::*;
use num_bigint::BigInt;

#[cfg(test)]
mod tests;

pub(super) fn value_to_term(solver: &mut Solver, value: &ModelValue, sort: &Sort) -> Option<Term> {
    let Sort::FloatingPoint(eb, sb) = scalar_value_sort(value)? else {
        return None;
    };
    if sort != &solver.try_fp_sort(eb, sb).ok()? {
        return None;
    }
    let stored = sb - 1;
    let (sign, exponent, significand) = if let ModelValue::FloatingPointExact(fields) = value {
        // Original sort/namespace checks precede both variable-sized copies.
        (
            fields.sign(),
            BigInt::from(fields.exponent().clone()),
            BigInt::from(fields.significand().clone()),
        )
    } else {
        let (sign, exponent, significand, _, _) = value.as_fp_wide()?;
        if sb > 129 || exponent >= 1u64 << eb || (stored < 128 && significand >= 1u128 << stored) {
            return None;
        }
        (sign, BigInt::from(exponent), BigInt::from(significand))
    };
    let sign = solver
        .try_bv_const_bigint(&BigInt::from(u8::from(sign)), 1)
        .ok()?;
    let exponent = solver.try_bv_const_bigint(&exponent, eb).ok()?;
    let significand = solver.try_bv_const_bigint(&significand, stored).ok()?;
    solver
        .try_fp_from_bvs(sign, exponent, significand, eb, sb)
        .ok()
}
