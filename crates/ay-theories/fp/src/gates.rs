// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! CNF gate helpers and FP classification predicates.
//!
//! These helpers sit at the bottom of the floating-point bit-blasting stack and
//! are reused by the arithmetic, rounding, and decomposition modules.

use ay_core::{CnfClause, CnfLit};

use super::{FpDecomposed, FpPrecision, FpSolver};

mod simplification;

/// Negate a CNF literal.
///
/// Every literal this solver builds is `±v` for a variable `v >= 1` handed out
/// by `fresh_var`, so `-lit` never overflows `i32`; `wrapping_neg` is total and
/// identical to `-lit` on that domain (the same form as `ay_core`'s Tseitin
/// `negate`). The one `i32` without a negation, `i32::MIN`, is not a literal.
#[inline]
pub(crate) fn neg_lit(lit: CnfLit) -> CnfLit {
    lit.wrapping_neg()
}

// ── CNF gate primitives ─────────────────────────────────────────────────────

impl FpSolver<'_> {
    /// Create a literal that represents (a AND b)
    pub(crate) fn make_and(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        if let Some(result) = self.simplify_and(a, b) {
            return result;
        }
        let result = self.fresh_var();
        // result <-> (a AND b)
        self.add_clause(CnfClause::new(vec![neg_lit(result), a]));
        self.add_clause(CnfClause::new(vec![neg_lit(result), b]));
        self.add_clause(CnfClause::new(vec![neg_lit(a), neg_lit(b), result]));
        result
    }

    /// Create a literal that represents (a OR b)
    pub(crate) fn make_or(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        if let Some(result) = self.simplify_or(a, b) {
            return result;
        }
        let result = self.fresh_var();
        // result <-> (a OR b)
        self.add_clause(CnfClause::new(vec![neg_lit(result), a, b]));
        self.add_clause(CnfClause::new(vec![neg_lit(a), result]));
        self.add_clause(CnfClause::new(vec![neg_lit(b), result]));
        result
    }

    /// Create a literal that represents (a XOR b)
    pub(crate) fn make_xor(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        if let Some(result) = self.simplify_xor(a, b) {
            return result;
        }
        let result = self.fresh_var();
        self.add_clause(CnfClause::new(vec![a, b, neg_lit(result)]));
        self.add_clause(CnfClause::new(vec![a, neg_lit(b), result]));
        self.add_clause(CnfClause::new(vec![neg_lit(a), b, result]));
        self.add_clause(CnfClause::new(vec![
            neg_lit(a),
            neg_lit(b),
            neg_lit(result),
        ]));
        result
    }

    /// Create a literal that is true iff all bits are zero
    pub(crate) fn make_all_zero(&mut self, bits: &[CnfLit]) -> CnfLit {
        let Some((&first, rest)) = bits.split_first() else {
            let result = self.fresh_var();
            self.add_clause(CnfClause::unit(result));
            return result;
        };
        let mut result = neg_lit(first);
        for &bit in rest {
            let neg_bit = neg_lit(bit);
            result = self.make_and(result, neg_bit);
        }
        result
    }

    /// Create a literal that is true iff all bits are one
    pub(crate) fn make_all_ones(&mut self, bits: &[CnfLit]) -> CnfLit {
        let Some((&first, rest)) = bits.split_first() else {
            let result = self.fresh_var();
            self.add_clause(CnfClause::unit(result));
            return result;
        };
        let mut result = first;
        for &bit in rest {
            result = self.make_and(result, bit);
        }
        result
    }

    /// Create a literal that is true iff NOT all bits are one
    pub(crate) fn make_not_all_ones(&mut self, bits: &[CnfLit]) -> CnfLit {
        let all_ones = self.make_all_ones(bits);
        neg_lit(all_ones)
    }

    /// Create a literal that is true iff any bit is nonzero
    pub(crate) fn make_any_nonzero(&mut self, bits: &[CnfLit]) -> CnfLit {
        let Some((&first, rest)) = bits.split_first() else {
            let result = self.fresh_var();
            self.add_clause(CnfClause::unit(neg_lit(result)));
            return result;
        };
        let mut result = first;
        for &bit in rest {
            result = self.make_or(result, bit);
        }
        result
    }

    /// Create bits representing equality of two bit vectors
    pub(crate) fn make_bits_equal(&mut self, a: &[CnfLit], b: &[CnfLit]) -> CnfLit {
        debug_assert_eq!(a.len(), b.len(), "Bit vectors must have same length");
        let mut pairs = a.iter().zip(b);
        let Some((&a0, &b0)) = pairs.next() else {
            let result = self.fresh_var();
            self.add_clause(CnfClause::unit(result));
            return result;
        };
        let mut result = self.make_xnor(a0, b0);
        for (&ai, &bi) in pairs {
            let bit_eq = self.make_xnor(ai, bi);
            result = self.make_and(result, bit_eq);
        }
        result
    }

    /// Create a literal that represents (a XNOR b) = NOT (a XOR b)
    pub(crate) fn make_xnor(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        let xor = self.make_xor(a, b);
        neg_lit(xor)
    }

    /// Create an if-then-else on bits: result = cond ? then_bits : else_bits
    pub(crate) fn make_ite_bits(
        &mut self,
        cond: CnfLit,
        then_bits: &[CnfLit],
        else_bits: &[CnfLit],
    ) -> Vec<CnfLit> {
        debug_assert_eq!(then_bits.len(), else_bits.len());
        let mut result = Vec::new();
        // A capacity hint only: on failure `push` grows the vector as before.
        let _ = result.try_reserve_exact(then_bits.len());
        for (&then_bit, &else_bit) in then_bits.iter().zip(else_bits) {
            result.push(self.make_ite(cond, then_bit, else_bit));
        }
        result
    }

    /// Create if-then-else: result = cond ? then_val : else_val
    pub(crate) fn make_ite(&mut self, cond: CnfLit, then_val: CnfLit, else_val: CnfLit) -> CnfLit {
        if let Some(result) = self.simplify_ite(cond, then_val, else_val) {
            return result;
        }
        let result = self.fresh_var();
        let (not_cond, not_result) = (neg_lit(cond), neg_lit(result));
        self.add_clause(CnfClause::new(vec![not_cond, neg_lit(then_val), result]));
        self.add_clause(CnfClause::new(vec![not_cond, then_val, not_result]));
        self.add_clause(CnfClause::new(vec![cond, neg_lit(else_val), result]));
        self.add_clause(CnfClause::new(vec![cond, else_val, not_result]));
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
        for (&ai, &bi) in a.iter().zip(b) {
            // bit_eq = NOT (a[i] XOR b[i])
            let xor_bit = self.make_xor(ai, bi);
            result = self.make_and(result, neg_lit(xor_bit));
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
