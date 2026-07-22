// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP constant construction and BV-constant extraction helpers.

use ay_core::term::{Constant, TermData, TermId};
use num_bigint::BigInt;

use super::{FpDecomposed, FpPrecision, FpSolver};

impl FpSolver<'_> {
    /// Extract a BigInt value from a bitvector constant term.
    pub(crate) fn extract_bv_const(&self, term: TermId) -> Option<BigInt> {
        match self.terms.get(term) {
            TermData::Const(Constant::BitVec { value, .. }) => Some(value.clone()),
            _ => None,
        }
    }

    /// Create +0 or -0: exponent all zero, significand all zero.
    pub fn make_zero(&mut self, precision: FpPrecision, negative: bool) -> FpDecomposed {
        let fp = self.fresh_decomposed(precision);
        self.constrain_constant(&fp, negative, |_| false, |_| false);
        fp
    }

    /// Create +infinity or -infinity: exponent all ones, significand all zero.
    pub fn make_infinity(&mut self, precision: FpPrecision, negative: bool) -> FpDecomposed {
        let fp = self.fresh_decomposed(precision);
        self.constrain_constant(&fp, negative, |_| true, |_| false);
        fp
    }

    /// Create NaN (quiet NaN): positive sign, exponent all ones,
    /// significand has MSB set (quiet NaN bit).
    pub fn make_nan_value(&mut self, precision: FpPrecision) -> FpDecomposed {
        let fp = self.fresh_decomposed(precision);
        let sb = precision.significand_bits();
        self.constrain_constant(&fp, false, |_| true, |i| i == sb - 2);
        fp
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
        let pos_sign = self.fresh_var();
        self.add_clause(ay_core::CnfClause::unit(-pos_sign));

        FpDecomposed {
            sign: pos_sign,
            exponent: x.exponent.clone(),
            significand: x.significand.clone(),
            precision: x.precision,
        }
    }
}
