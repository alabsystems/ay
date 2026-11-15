// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP constant construction and BV-constant extraction helpers.

use ay_core::term::{Constant, TermData, TermId};
use num_bigint::BigInt;

use super::{FpDecomposed, FpPrecision, FpSolver};

impl FpSolver<'_> {
    /// Preserve literal bits as canonical CNF constants so arithmetic gates
    /// can simplify them before any SAT search. These are source constants,
    /// never values inferred from a candidate assignment.
    pub(crate) fn make_constant(
        &mut self,
        precision: FpPrecision,
        negative: bool,
        exponent_bit: impl Fn(u32) -> bool,
        significand_bit: impl Fn(u32) -> bool,
    ) -> FpDecomposed {
        let one = self.const_true();
        let zero = self.const_false();
        FpDecomposed {
            sign: if negative { one } else { zero },
            exponent: (0..precision.exponent_bits())
                .map(|i| if exponent_bit(i) { one } else { zero })
                .collect(),
            significand: (0..precision.significand_bits() - 1)
                .map(|i| if significand_bit(i) { one } else { zero })
                .collect(),
            precision,
        }
    }

    /// Extract a BigInt value from a bitvector constant term.
    pub(crate) fn extract_bv_const(&self, term: TermId) -> Option<BigInt> {
        match self.terms.get(term) {
            TermData::Const(Constant::BitVec { value, .. }) => Some(value.clone()),
            _ => None,
        }
    }

    /// Create +0 or -0: exponent all zero, significand all zero.
    pub fn make_zero(&mut self, precision: FpPrecision, negative: bool) -> FpDecomposed {
        self.make_constant(precision, negative, |_| false, |_| false)
    }

    /// The exact zero IEEE 754 §6.3 gives a cancelling sum: `-0` toward
    /// negative, `+0` under every other mode.
    pub(crate) fn make_rm_signed_zero(
        &mut self,
        precision: FpPrecision,
        rm: crate::RmOperand,
    ) -> FpDecomposed {
        match rm {
            crate::RmOperand::Literal(mode) => {
                self.make_zero(precision, mode == crate::RoundingMode::RTN)
            }
            crate::RmOperand::Symbolic(_) => {
                let mut zero = self.make_zero(precision, false);
                zero.sign = self.rm_is(rm, crate::RoundingMode::RTN);
                zero
            }
        }
    }

    /// Create +infinity or -infinity: exponent all ones, significand all zero.
    pub fn make_infinity(&mut self, precision: FpPrecision, negative: bool) -> FpDecomposed {
        self.make_constant(precision, negative, |_| true, |_| false)
    }

    /// Create NaN (quiet NaN): positive sign, exponent all ones,
    /// significand has MSB set (quiet NaN bit).
    pub fn make_nan_value(&mut self, precision: FpPrecision) -> FpDecomposed {
        let sb = precision.significand_bits();
        self.make_constant(precision, false, |_| true, |i| i == sb - 2)
    }

    /// Negate an FP value.
    /// IEEE 754-2008 Section 5.5.1: negate always flips the sign bit,
    /// even for NaN (it is a bit-level operation, not arithmetic).
    pub fn make_neg(&mut self, x: &FpDecomposed) -> FpDecomposed {
        FpDecomposed {
            sign: -x.sign,
            exponent: x.exponent.clone(),
            significand: x.significand.clone(),
            precision: x.precision,
        }
    }

    /// Absolute value.
    /// IEEE 754-2008 Section 5.5.1: abs always clears the sign bit,
    /// even for NaN (it is a bit-level operation, not arithmetic).
    pub fn make_abs(&mut self, x: &FpDecomposed) -> FpDecomposed {
        let pos_sign = self.const_false();

        FpDecomposed {
            sign: pos_sign,
            exponent: x.exponent.clone(),
            significand: x.significand.clone(),
            precision: x.precision,
        }
    }
}
