// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! CNF gate helpers and FP classification predicates.
//!
//! These helpers sit at the bottom of the floating-point bit-blasting stack and
//! are reused by the arithmetic, rounding, and decomposition modules.

use ay_core::{CnfClause, CnfLit};

use super::{FpDecomposed, FpPrecision, FpSolver};

// ── CNF gate primitives ─────────────────────────────────────────────────────

impl FpSolver<'_> {
    /// Create a literal that represents (a AND b)
    pub(crate) fn make_and(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        let result = self.fresh_var();
        // result <-> (a AND b)
        self.add_clause(CnfClause::new(vec![-result, a]));
        self.add_clause(CnfClause::new(vec![-result, b]));
        self.add_clause(CnfClause::new(vec![-a, -b, result]));
        result
    }

    /// Create a literal that represents (a OR b)
    pub(crate) fn make_or(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        let result = self.fresh_var();
        // result <-> (a OR b)
        self.add_clause(CnfClause::new(vec![-result, a, b]));
        self.add_clause(CnfClause::new(vec![-a, result]));
        self.add_clause(CnfClause::new(vec![-b, result]));
        result
    }

    /// Create a literal that represents (a XOR b)
    pub(crate) fn make_xor(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        let result = self.fresh_var();
        self.add_clause(CnfClause::new(vec![a, b, -result]));
        self.add_clause(CnfClause::new(vec![a, -b, result]));
        self.add_clause(CnfClause::new(vec![-a, b, result]));
        self.add_clause(CnfClause::new(vec![-a, -b, -result]));
        result
    }

    /// Create a literal that is true iff all bits are zero
    pub(crate) fn make_all_zero(&mut self, bits: &[CnfLit]) -> CnfLit {
        if bits.is_empty() {
            let result = self.fresh_var();
            self.add_clause(CnfClause::unit(result));
            return result;
        }
        let mut result = -bits[0];
        for &bit in &bits[1..] {
            let neg_bit = -bit;
            result = self.make_and(result, neg_bit);
        }
        result
    }

    /// Create a literal that is true iff all bits are one
    pub(crate) fn make_all_ones(&mut self, bits: &[CnfLit]) -> CnfLit {
        if bits.is_empty() {
            let result = self.fresh_var();
            self.add_clause(CnfClause::unit(result));
            return result;
        }
        let mut result = bits[0];
        for &bit in &bits[1..] {
            result = self.make_and(result, bit);
        }
        result
    }

    /// Create a literal that is true iff NOT all bits are one
    pub(crate) fn make_not_all_ones(&mut self, bits: &[CnfLit]) -> CnfLit {
        let all_ones = self.make_all_ones(bits);
        -all_ones
    }

    /// Create a literal that is true iff any bit is nonzero
    pub(crate) fn make_any_nonzero(&mut self, bits: &[CnfLit]) -> CnfLit {
        if bits.is_empty() {
            let result = self.fresh_var();
            self.add_clause(CnfClause::unit(-result));
            return result;
        }
        let mut result = bits[0];
        for &bit in &bits[1..] {
            result = self.make_or(result, bit);
        }
        result
    }

    /// Create bits representing equality of two bit vectors
    pub(crate) fn make_bits_equal(&mut self, a: &[CnfLit], b: &[CnfLit]) -> CnfLit {
        debug_assert_eq!(a.len(), b.len(), "Bit vectors must have same length");
        if a.is_empty() {
            let result = self.fresh_var();
            self.add_clause(CnfClause::unit(result));
            return result;
        }
        let mut result = self.make_xnor(a[0], b[0]);
        for i in 1..a.len() {
            let bit_eq = self.make_xnor(a[i], b[i]);
            result = self.make_and(result, bit_eq);
        }
        result
    }

    /// Create a literal that represents (a XNOR b) = NOT (a XOR b)
    pub(crate) fn make_xnor(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        let xor = self.make_xor(a, b);
        -xor
    }

    /// Create an if-then-else on bits: result = cond ? then_bits : else_bits
    pub(crate) fn make_ite_bits(
        &mut self,
        cond: CnfLit,
        then_bits: &[CnfLit],
        else_bits: &[CnfLit],
    ) -> Vec<CnfLit> {
        debug_assert_eq!(then_bits.len(), else_bits.len());
        let mut result = Vec::with_capacity(then_bits.len());
        for i in 0..then_bits.len() {
            result.push(self.make_ite(cond, then_bits[i], else_bits[i]));
        }
        result
    }

    /// Create if-then-else: result = cond ? then_val : else_val
    pub(crate) fn make_ite(&mut self, cond: CnfLit, then_val: CnfLit, else_val: CnfLit) -> CnfLit {
        let result = self.fresh_var();
        self.add_clause(CnfClause::new(vec![-cond, -then_val, result]));
        self.add_clause(CnfClause::new(vec![-cond, then_val, -result]));
        self.add_clause(CnfClause::new(vec![cond, -else_val, result]));
        self.add_clause(CnfClause::new(vec![cond, else_val, -result]));
        result
    }

    /// ITE for decomposed FP values: cond ? then_fp : else_fp
    pub(crate) fn make_ite_fp(
        &mut self,
        cond: CnfLit,
        then_fp: &FpDecomposed,
        else_fp: &FpDecomposed,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let sign = self.make_ite(cond, then_fp.sign, else_fp.sign);
        let exponent = self.make_ite_bits(cond, &then_fp.exponent, &else_fp.exponent);
        let significand = self.make_ite_bits(cond, &then_fp.significand, &else_fp.significand);
        FpDecomposed {
            sign,
            exponent,
            significand,
            precision,
        }
    }

    /// Bitvector equality: returns a CnfLit true iff a == b bit-by-bit.
    pub(crate) fn make_bv_eq(&mut self, a: &[CnfLit], b: &[CnfLit]) -> CnfLit {
        debug_assert_eq!(a.len(), b.len());
        let mut result = self.const_true();
        for i in 0..a.len() {
            // bit_eq = NOT (a[i] XOR b[i])
            let xor_bit = self.make_xor(a[i], b[i]);
            result = self.make_and(result, -xor_bit);
        }
        result
    }
}

// ── FP classification predicates ────────────────────────────────────────────

impl FpSolver<'_> {
    /// Check if decomposed value represents zero
    pub(crate) fn is_zero(&mut self, fp: &FpDecomposed) -> CnfLit {
        let exp_zero = self.make_all_zero(&fp.exponent);
        let sig_zero = self.make_all_zero(&fp.significand);
        self.make_and(exp_zero, sig_zero)
    }

    /// Check if decomposed value represents infinity
    pub(crate) fn is_infinite(&mut self, fp: &FpDecomposed) -> CnfLit {
        let exp_max = self.make_all_ones(&fp.exponent);
        let sig_zero = self.make_all_zero(&fp.significand);
        self.make_and(exp_max, sig_zero)
    }

    /// Check if decomposed value represents NaN
    pub(crate) fn is_nan(&mut self, fp: &FpDecomposed) -> CnfLit {
        let exp_max = self.make_all_ones(&fp.exponent);
        let sig_nonzero = self.make_any_nonzero(&fp.significand);
        self.make_and(exp_max, sig_nonzero)
    }

    /// Check if decomposed value is subnormal
    pub(crate) fn is_subnormal(&mut self, fp: &FpDecomposed) -> CnfLit {
        let exp_zero = self.make_all_zero(&fp.exponent);
        let sig_nonzero = self.make_any_nonzero(&fp.significand);
        self.make_and(exp_zero, sig_nonzero)
    }

    /// Check if decomposed value is normal
    pub(crate) fn is_normal(&mut self, fp: &FpDecomposed) -> CnfLit {
        let exp_nonzero = self.make_any_nonzero(&fp.exponent);
        let exp_not_max = self.make_not_all_ones(&fp.exponent);
        self.make_and(exp_nonzero, exp_not_max)
    }
}
