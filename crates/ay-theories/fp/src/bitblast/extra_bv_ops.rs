// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bitvector operators the FP pipeline's BV value encoder had no arm for.
//!
//! Under `(set-logic ALL)` (or QF_BVFP / QF_ABVFP / QF_FP) a query with
//! floating point is decided by the FP bit-blaster, which encodes the
//! bitvector terms around the floats itself. An operator missing from its
//! value encoder makes the encoder return `None`, and the whole query answers
//! `unknown` in milliseconds, while the same text declared QF_AUFBV, where
//! the BV engine owns these operators, is decided (the class DR-47 recorded
//! for BV atoms hidden in an ITE condition). A symbolic `bvashr`, the
//! `rotate_left`/`rotate_right` family, `repeat` over a symbolic operand (the
//! term store folds only constant operands and `i = 1`) and `bvcomp` (which
//! `bvredor` and `bvredand` elaborate into) were such operators.
//!
//! Each encoding is exact:
//! - `rotate_left i` / `rotate_right i` permute the operand's bits (index
//!   taken modulo the width, as SMT-LIB defines it); no gate is added.
//! - `repeat i` concatenates `i` copies of the operand's bits; no gate is
//!   added.
//! - `bvcomp a b` is the one-bit equality comparator.
//! - `bvashr a b` is `lshr(a, b)` when the sign bit is clear and
//!   `bvnot(lshr(bvnot a, b))` when it is set. Both are the existing logical
//!   barrel shifter, which already yields all zeros for a shift at or past the
//!   width, so the set-sign case yields all ones there, as SMT-LIB requires.
//!
//! An operand without an exact encoding still makes the result `None`.

use ay_core::term::{Symbol, TermId};
use ay_core::CnfLit;

use crate::construction::control::BuildControl;
use crate::FpSolver;

impl FpSolver<'_> {
    pub(super) fn bitblast_extra_bv_app_value_with_control<C: BuildControl>(
        &mut self,
        sym: &Symbol,
        args: &[TermId],
        expected_sz: usize,
        control: &mut C,
    ) -> Result<Option<Vec<CnfLit>>, C::Error> {
        match (sym.name(), args) {
            ("bvashr", &[value, amount]) => {
                let Some(bits) =
                    self.bitblast_bv_value_with_control(value, expected_sz, control)?
                else {
                    return Ok(None);
                };
                let Some(shift_sz) = self.bv_width(amount) else {
                    return Ok(None);
                };
                let Some(shift) = self.bitblast_bv_value_with_control(amount, shift_sz, control)?
                else {
                    return Ok(None);
                };
                let Some(&sign) = bits.last() else {
                    return Ok(None);
                };
                let logical = self.bv_lshr(&bits, &shift);
                let inverted: Vec<CnfLit> = bits.iter().map(|&bit| -bit).collect();
                let filled: Vec<CnfLit> = self
                    .bv_lshr(&inverted, &shift)
                    .into_iter()
                    .map(|bit| -bit)
                    .collect();
                Ok(Some(self.make_ite_bits(sign, &filled, &logical)))
            }
            ("rotate_left" | "rotate_right", &[value]) => {
                let Symbol::Indexed(_, indices) = sym else {
                    return Ok(None);
                };
                let &[index] = indices.as_slice() else {
                    return Ok(None);
                };
                let Some(bits) =
                    self.bitblast_bv_value_with_control(value, expected_sz, control)?
                else {
                    return Ok(None);
                };
                let width = bits.len();
                if width == 0 {
                    return Ok(None);
                }
                let turn = index as usize % width;
                // `bits[0]` is the least significant bit. Rotating left by
                // `turn` moves bit `j - turn` to position `j`.
                let source = |j: usize| {
                    if sym.name() == "rotate_left" {
                        (j + width - turn) % width
                    } else {
                        (j + turn) % width
                    }
                };
                Ok(Some((0..width).map(|j| bits[source(j)]).collect()))
            }
            ("repeat", &[value]) => {
                self.bitblast_repeat_with_control(sym, value, expected_sz, control)
            }
            ("bvcomp", &[lhs, rhs]) if expected_sz == 1 => {
                let Some(width) = self.bv_width(lhs) else {
                    return Ok(None);
                };
                if self.bv_width(rhs) != Some(width) {
                    return Ok(None);
                }
                let Some(lhs_bits) = self.bitblast_bv_value_with_control(lhs, width, control)?
                else {
                    return Ok(None);
                };
                let Some(rhs_bits) = self.bitblast_bv_value_with_control(rhs, width, control)?
                else {
                    return Ok(None);
                };
                Ok(Some(vec![self.make_bits_equal(&lhs_bits, &rhs_bits)]))
            }
            _ => Ok(None),
        }
    }

    /// `(_ repeat i) a`: `i` copies of `a`'s bits. Every copy is the same
    /// word, so copy order is immaterial. A result width other than
    /// `i * width(a)` declines.
    fn bitblast_repeat_with_control<C: BuildControl>(
        &mut self,
        sym: &Symbol,
        value: TermId,
        expected_sz: usize,
        control: &mut C,
    ) -> Result<Option<Vec<CnfLit>>, C::Error> {
        let Symbol::Indexed(_, indices) = sym else {
            return Ok(None);
        };
        let &[count] = indices.as_slice() else {
            return Ok(None);
        };
        let Some(width) = self.bv_width(value) else {
            return Ok(None);
        };
        if width == 0 || width.checked_mul(count as usize) != Some(expected_sz) {
            return Ok(None);
        }
        let Some(bits) = self.bitblast_bv_value_with_control(value, width, control)? else {
            return Ok(None);
        };
        Ok(Some(
            bits.iter().copied().cycle().take(expected_sz).collect(),
        ))
    }
}

#[cfg(test)]
#[path = "extra_bv_ops_tests.rs"]
mod tests;
