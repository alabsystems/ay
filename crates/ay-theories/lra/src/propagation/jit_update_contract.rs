// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lowering contracts for prospective LRA `update_nonbasic` JIT code (#8174).
//!
//! This module intentionally does not compile or execute machine code. It
//! extracts the column-index row updates that the interpreted
//! `update_nonbasic` loop would visit, then classifies each update as safe for
//! an i64/i64 lowering or as requiring the existing exact bignum path.

#![allow(dead_code)]

use super::*;
use crate::rational::gcd_u64;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LraJitI64Rational {
    pub(crate) num: i64,
    pub(crate) den: i64,
}

impl LraJitI64Rational {
    fn new(num: i64, den: i64) -> Option<Self> {
        if den <= 0 {
            return None;
        }
        Some(Self { num, den })
    }

    fn from_i128(num: i128, den: i128) -> Option<Self> {
        if den == 0 {
            return None;
        }
        let (num, den) = if den < 0 {
            (num.checked_neg()?, den.checked_neg()?)
        } else {
            (num, den)
        };
        if num == 0 {
            return Some(Self { num: 0, den: 1 });
        }
        let gcd = gcd_u128(num.unsigned_abs(), den.unsigned_abs());
        let reduced_num = num / gcd as i128;
        let reduced_den = den / gcd as i128;
        Some(Self {
            num: i64::try_from(reduced_num).ok()?,
            den: i64::try_from(reduced_den).ok()?,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LraJitUpdateBignumReason {
    BigCoefficient,
    NonSmallDelta,
    NonSmallBasicValue,
    ProductOverflow,
    AdditionOverflow,
    InvalidDenominator,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LraJitUpdateExtractionError {
    MissingRow {
        row_idx: usize,
    },
    RowIndexTooLarge {
        row_idx: usize,
    },
    RowPositionTooLarge {
        row_pos: usize,
    },
    MissingBasicValue {
        row_idx: u32,
        basic_var: u32,
    },
    StaleColumnEntry {
        row_idx: u32,
        row_pos: u32,
        expected_var: u32,
        actual_var: Option<u32>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LraJitI64UpdateRow {
    pub(crate) row_idx: u32,
    pub(crate) row_pos: u32,
    pub(crate) basic_var: u32,
    pub(crate) coeff: LraJitI64Rational,
    pub(crate) result_x: LraJitI64Rational,
    pub(crate) result_y: LraJitI64Rational,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LraJitBignumUpdateRow {
    pub(crate) row_idx: u32,
    pub(crate) row_pos: u32,
    pub(crate) basic_var: u32,
    pub(crate) reason: LraJitUpdateBignumReason,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LraJitUpdateRow {
    I64FastPath(LraJitI64UpdateRow),
    BignumRequired(LraJitBignumUpdateRow),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LraJitUpdateContract {
    pub(crate) rows: Vec<LraJitUpdateRow>,
    pub(crate) i64_rows: usize,
    pub(crate) bignum_rows: usize,
}

impl LraJitUpdateContract {
    fn new(rows: Vec<LraJitUpdateRow>) -> Self {
        let i64_rows = rows
            .iter()
            .filter(|row| matches!(row, LraJitUpdateRow::I64FastPath(_)))
            .count();
        let bignum_rows = rows.len() - i64_rows;
        Self {
            rows,
            i64_rows,
            bignum_rows,
        }
    }

    pub(crate) fn requires_bignum(&self) -> bool {
        self.bignum_rows != 0
    }
}

pub(crate) fn extract_update_nonbasic_jit_contract(
    var: u32,
    delta: &InfRational,
    rows: &[TableauRow],
    vars: &[VarInfo],
    col_entries: &[ColEntry],
) -> Result<LraJitUpdateContract, LraJitUpdateExtractionError> {
    let mut updates = Vec::with_capacity(col_entries.len());
    for entry in col_entries {
        let row_idx = u32::try_from(entry.row_idx).map_err(|_| {
            LraJitUpdateExtractionError::RowIndexTooLarge {
                row_idx: entry.row_idx,
            }
        })?;
        let row_pos = u32::try_from(entry.row_pos).map_err(|_| {
            LraJitUpdateExtractionError::RowPositionTooLarge {
                row_pos: entry.row_pos,
            }
        })?;
        let row = rows
            .get(entry.row_idx)
            .ok_or(LraJitUpdateExtractionError::MissingRow {
                row_idx: entry.row_idx,
            })?;
        let Some((actual_var, coeff)) = row.coeffs.get(entry.row_pos) else {
            return Err(LraJitUpdateExtractionError::StaleColumnEntry {
                row_idx,
                row_pos,
                expected_var: var,
                actual_var: None,
            });
        };
        if *actual_var != var {
            return Err(LraJitUpdateExtractionError::StaleColumnEntry {
                row_idx,
                row_pos,
                expected_var: var,
                actual_var: Some(*actual_var),
            });
        }
        if matches!(coeff, Rational::Small(0, _)) {
            continue;
        }
        let basic_var = row.basic_var;
        let basic_value = &vars
            .get(basic_var as usize)
            .ok_or(LraJitUpdateExtractionError::MissingBasicValue { row_idx, basic_var })?
            .value;

        updates.push(classify_update_row(
            row_idx,
            row_pos,
            basic_var,
            coeff,
            delta,
            basic_value,
        ));
    }

    Ok(LraJitUpdateContract::new(updates))
}

fn classify_update_row(
    row_idx: u32,
    row_pos: u32,
    basic_var: u32,
    coeff: &Rational,
    delta: &InfRational,
    basic_value: &InfRational,
) -> LraJitUpdateRow {
    match try_classify_i64_update(row_idx, row_pos, basic_var, coeff, delta, basic_value) {
        Ok(row) => LraJitUpdateRow::I64FastPath(row),
        Err(reason) => LraJitUpdateRow::BignumRequired(LraJitBignumUpdateRow {
            row_idx,
            row_pos,
            basic_var,
            reason,
        }),
    }
}

fn try_classify_i64_update(
    row_idx: u32,
    row_pos: u32,
    basic_var: u32,
    coeff: &Rational,
    delta: &InfRational,
    basic_value: &InfRational,
) -> Result<LraJitI64UpdateRow, LraJitUpdateBignumReason> {
    let coeff = match coeff.try_as_i64() {
        Some((num, den)) => {
            LraJitI64Rational::new(num, den).ok_or(LraJitUpdateBignumReason::InvalidDenominator)?
        }
        None => return Err(LraJitUpdateBignumReason::BigCoefficient),
    };
    let ((delta_x_num, delta_x_den), (delta_y_num, delta_y_den)) = delta
        .try_as_i64_parts()
        .ok_or(LraJitUpdateBignumReason::NonSmallDelta)?;
    let ((basic_x_num, basic_x_den), (basic_y_num, basic_y_den)) =
        basic_value
            .try_as_i64_parts()
            .ok_or(LraJitUpdateBignumReason::NonSmallBasicValue)?;

    let delta_x = LraJitI64Rational::new(delta_x_num, delta_x_den)
        .ok_or(LraJitUpdateBignumReason::InvalidDenominator)?;
    let delta_y = LraJitI64Rational::new(delta_y_num, delta_y_den)
        .ok_or(LraJitUpdateBignumReason::InvalidDenominator)?;
    let basic_x = LraJitI64Rational::new(basic_x_num, basic_x_den)
        .ok_or(LraJitUpdateBignumReason::InvalidDenominator)?;
    let basic_y = LraJitI64Rational::new(basic_y_num, basic_y_den)
        .ok_or(LraJitUpdateBignumReason::InvalidDenominator)?;

    let adj_x = checked_mul(delta_x, coeff).ok_or(LraJitUpdateBignumReason::ProductOverflow)?;
    let adj_y = checked_mul(delta_y, coeff).ok_or(LraJitUpdateBignumReason::ProductOverflow)?;
    let result_x = checked_add(basic_x, adj_x).ok_or(LraJitUpdateBignumReason::AdditionOverflow)?;
    let result_y = checked_add(basic_y, adj_y).ok_or(LraJitUpdateBignumReason::AdditionOverflow)?;

    Ok(LraJitI64UpdateRow {
        row_idx,
        row_pos,
        basic_var,
        coeff,
        result_x,
        result_y,
    })
}

fn checked_mul(a: LraJitI64Rational, b: LraJitI64Rational) -> Option<LraJitI64Rational> {
    let g1 = gcd_u64(a.num.unsigned_abs(), b.den.unsigned_abs());
    let g2 = gcd_u64(b.num.unsigned_abs(), a.den.unsigned_abs());
    let an = a.num / g1 as i64;
    let bd = b.den / g1 as i64;
    let bn = b.num / g2 as i64;
    let ad = a.den / g2 as i64;
    LraJitI64Rational::from_i128(
        i128::from(an) * i128::from(bn),
        i128::from(ad) * i128::from(bd),
    )
}

fn checked_add(a: LraJitI64Rational, b: LraJitI64Rational) -> Option<LraJitI64Rational> {
    let gcd = gcd_u64(a.den as u64, b.den as u64);
    let a_den_reduced = a.den / gcd as i64;
    let b_den_reduced = b.den / gcd as i64;
    let lhs = i128::from(a.num) * i128::from(b_den_reduced);
    let rhs = i128::from(b.num) * i128::from(a_den_reduced);
    let num = lhs.checked_add(rhs)?;
    let den = i128::from(a_den_reduced).checked_mul(i128::from(b.den))?;
    LraJitI64Rational::from_i128(num, den)
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    let shift = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }
        b -= a;
        if b == 0 {
            return a << shift;
        }
    }
}

#[cfg(test)]
mod tests;
