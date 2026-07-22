// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Remaining FP operations: remainder, min, and max.

use ay_core::CnfLit;

use super::{FpDecomposed, FpPrecision, FpSolver, RoundingMode};

struct RemSpecialCases {
    nan: FpDecomposed,
    pzero: FpDecomposed,
    c1: CnfLit,
    c2: CnfLit,
    c3: CnfLit,
    c4: CnfLit,
    c5: CnfLit,
    c6: CnfLit,
}

struct RemCore {
    rndd: FpDecomposed,
    adj_cnd: CnfLit,
    b_sgn: CnfLit,
}

impl FpSolver<'_> {
    /// IEEE 754 remainder: `fp.rem(x, y)`.
    pub fn make_rem(&mut self, x: &FpDecomposed, y: &FpDecomposed) -> FpDecomposed {
        let precision = x.precision;
        let special_cases = self.rem_special_cases(x, y);
        let core = self.rem_round_down_candidate(x, y);
        let signs_differ = self.make_xor(core.rndd.sign, core.b_sgn);
        let rounded_add = self.make_add(&core.rndd, y, RoundingMode::RNE);
        let rounded_sub = self.make_sub(&core.rndd, y, RoundingMode::RNE);
        let adjusted = self.make_ite_fp(signs_differ, &rounded_add, &rounded_sub, precision);
        let base = self.make_ite_fp(core.adj_cnd, &adjusted, &core.rndd, precision);
        let result = self.rem_apply_special_cases(x, &special_cases, &base, precision);
        self.rem_fix_zero_sign(x, &result, precision)
    }

    fn rem_special_cases(&mut self, x: &FpDecomposed, y: &FpDecomposed) -> RemSpecialCases {
        let precision = x.precision;
        let eb = precision.exponent_bits() as usize;
        let x_nan = self.is_nan(x);
        let y_nan = self.is_nan(y);
        let c1 = self.make_or(x_nan, y_nan);
        let c2 = self.is_infinite(x);
        let c3 = self.is_infinite(y);
        let c4 = self.is_zero(y);
        let c5 = self.is_zero(x);

        let y_exp_zero = self.make_all_zero(&y.exponent);
        let one_eb = self.const_bv(1, eb);
        let y_exp_m1 = self.bv_sub(&y.exponent, &one_eb);
        let xe_lt_yem1 = self.make_unsigned_lt(&x.exponent, &y_exp_m1);
        let c6 = self.make_and(-y_exp_zero, xe_lt_yem1);

        RemSpecialCases {
            nan: self.make_nan_value(precision),
            pzero: self.make_zero(precision, false),
            c1,
            c2,
            c3,
            c4,
            c5,
            c6,
        }
    }

    fn rem_round_down_candidate(&mut self, x: &FpDecomposed, y: &FpDecomposed) -> RemCore {
        let precision = x.precision;
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;
        let (a_sgn, a_sig, a_exp, a_lz) = self.unpack(x, true);
        let (b_sgn, b_sig, b_exp, b_lz) = self.unpack(y, true);

        let a_exp_ext = self.sign_extend(&a_exp, 2);
        let b_exp_ext = self.sign_extend(&b_exp, 2);
        let a_lz_ext = self.zero_extend(&a_lz, 2);
        let b_lz_ext = self.zero_extend(&b_lz, 2);
        let a_eff_exp = self.bv_sub(&a_exp_ext, &a_lz_ext);
        let b_eff_exp = self.bv_sub(&b_exp_ext, &b_lz_ext);
        let exp_diff = self.bv_sub(&a_eff_exp, &b_eff_exp);

        // The rounded-down remainder candidate is the guarded remainder
        //   rndd_sig = 8 * R,   R = (a_sig * 2^exp_diff) mod b_sig,
        // together with the parity `quot_odd` of the exact quotient
        //   Q = floor(a_sig * 2^exp_diff / b_sig).
        // `a_sig`/`b_sig` are the normalized significands (value in
        // `[2^(sb-1), 2^sb)` for nonzero operands); the factor `8` supplies the
        // three GRS guard bits that `fp_round` expects at the bottom of the
        // significand, and `rem_adjustment_condition` compares `8*R` against
        // `4*b_sig` to test `R >= b_sig/2`.
        //
        // A direct realization shifts `a_sig` left by `exp_diff` (up to
        // `2^eb + sb - 4` for the largest normal over the smallest subnormal) and
        // divides by `b_sig`, needing a `~2*sb + 2^eb`-bit divider — intractable
        // for Float64+ (2153 bits). Instead we compute the same `(8R, quot_odd)`
        // via bounded modular reduction: working modulo `M2 = 16*b_sig` we compute
        //   T = (8*a_sig * 2^exp_diff) mod M2
        // by square-and-multiply over the `eb+2` bits of `exp_diff`, using only
        // `~sb`-bit multiplies/divides. Writing `N = 8*a_sig*2^exp_diff = Q*(8*b_sig) + 8R`
        // with `0 <= 8R < 8*b_sig`, we have `N mod (2*(8*b_sig)) = (Q mod 2)*(8*b_sig) + 8R`,
        // so `8R = T` when `T < 8*b_sig` and `8R = T - 8*b_sig` otherwise, and
        // `Q` is odd exactly when `T >= 8*b_sig`. The result is exact (no
        // intermediate rounding), matching the wide-divide encoding bit for bit.
        let (rndd_sig, quot_odd) = self.rem_modular_reduce(&a_sig, &b_sig, &exp_diff, eb, sb);

        let adj_cnd = self.rem_adjustment_condition(quot_odd, &rndd_sig, &b_sig, eb);
        let rndd = self.fp_round(precision, RoundingMode::RNE, a_sgn, &rndd_sig, &b_eff_exp);
        RemCore {
            rndd,
            adj_cnd,
            b_sgn,
        }
    }

    /// Multiply-modulo: returns `(x * y) mod m`, all values `< m`, width `= m.len()`.
    fn mulmod(&mut self, x: &[CnfLit], y: &[CnfLit], m: &[CnfLit]) -> Vec<CnfLit> {
        let wm = m.len();
        let dw = 2 * wm;
        let xw = self.zero_extend(x, dw - x.len());
        let yw = self.zero_extend(y, dw - y.len());
        let prod = self.bv_mul(&xw, &yw);
        let mw = self.zero_extend(m, dw - wm);
        let (_, rem) = self.bv_udiv_urem(&prod, &mw);
        rem[..wm].to_vec()
    }

    /// Double-modulo: returns `(2 * p) mod m`, given `p < m`, width `= m.len()`.
    fn double_mod(&mut self, p: &[CnfLit], m: &[CnfLit]) -> Vec<CnfLit> {
        let wm = m.len();
        let false_lit = self.const_false();
        let doubled = Self::bv_concat(&[false_lit], p); // width wm+1, value 2p
        let m_ext = self.zero_extend(m, 1);
        let ge = self.make_unsigned_ge(&doubled, &m_ext);
        let sub = self.bv_sub(&doubled, &m_ext);
        let res = self.make_ite_bits(ge, &sub, &doubled);
        res[..wm].to_vec()
    }

    /// Exact bounded computation of `(rndd_sig, quot_odd)` (see caller). Returns
    /// `rndd_sig = 8*R` (width `sb+4`) and the quotient-parity bit.
    fn rem_modular_reduce(
        &mut self,
        a_sig: &[CnfLit],
        b_sig: &[CnfLit],
        exp_diff: &[CnfLit],
        eb: usize,
        sb: usize,
    ) -> (Vec<CnfLit>, CnfLit) {
        let wm = sb + 4;
        let false_lit = self.const_false();
        // M2 = 16 * b_sig  (< 2^(sb+4)), MB = 8 * b_sig, both width wm.
        let m2 = {
            let four_zeros = vec![false_lit; 4];
            let v = Self::bv_concat(&four_zeros, b_sig); // width sb+4, value 16*b_sig
            debug_assert_eq!(v.len(), wm);
            v
        };
        let mb = {
            let three_zeros = vec![false_lit; 3];
            let v = Self::bv_concat(&three_zeros, b_sig); // width sb+3, value 8*b_sig
            self.zero_extend(&v, 1) // width wm
        };
        // A = 8 * a_sig, width wm.
        let a8 = {
            let three_zeros = vec![false_lit; 3];
            let v = Self::bv_concat(&three_zeros, a_sig); // width sb+3
            self.zero_extend(&v, 1) // width wm
        };

        // Positive branch: T_pos = A * (2^exp_diff mod M2) mod M2 via
        // square-and-multiply over the bits of exp_diff (MSB first).
        let mut p = self.const_bv(1, wm); // 2^0 mod M2
        for i in (0..exp_diff.len()).rev() {
            p = self.mulmod(&p, &p, &m2); // square
            let doubled = self.double_mod(&p, &m2);
            p = self.make_ite_bits(exp_diff[i], &doubled, &p);
        }
        let t_pos = self.mulmod(&a8, &p, &m2);

        // Negative branch: right-shift A by |exp_diff| (lossy, keeping the guard
        // bits), staying `< M2` so no reduction is needed before the MB step.
        let neg_exp_diff = self.bv_neg(exp_diff);
        let t_neg = self.bv_lshr(&a8, &neg_exp_diff);

        let zero_ed = self.const_bv(0, exp_diff.len());
        let exp_diff_is_neg = self.bv_slt(exp_diff, &zero_ed);
        let t = self.make_ite_bits(exp_diff_is_neg, &t_neg, &t_pos); // width wm

        // Reduce T in [0, 16*b_sig) to rndd_sig = T mod (8*b_sig) and parity.
        let quot_odd = self.make_unsigned_ge(&t, &mb);
        let t_minus_mb = self.bv_sub(&t, &mb);
        let rndd_sig = self.make_ite_bits(quot_odd, &t_minus_mb, &t); // width wm = sb+4
        let _ = eb;
        (rndd_sig, quot_odd)
    }

    fn rem_adjustment_condition(
        &mut self,
        quot_odd: CnfLit,
        rndd_sig: &[CnfLit],
        b_sig: &[CnfLit],
        eb: usize,
    ) -> CnfLit {
        let rndd_sig_lz = self.bv_leading_zeros(rndd_sig, eb + 2);
        let one_lz = self.const_bv(1, eb + 2);
        let two_lz = self.const_bv(2, eb + 2);
        let rndd_exp_eq_y_exp = self.make_bv_eq(&rndd_sig_lz, &one_lz);
        let rndd_exp_eq_y_exp_m1 = self.make_bv_eq(&rndd_sig_lz, &two_lz);

        let two_zeros = self.const_bv(0, 2);
        let b_sig_pad = Self::bv_concat(&two_zeros, &self.zero_extend(b_sig, 2));
        let y_sig_le_rndd = self.bv_sle(&b_sig_pad, rndd_sig);
        let y_sig_eq_rndd = self.make_bv_eq(&b_sig_pad, rndd_sig);

        let case1 = self.make_and(rndd_exp_eq_y_exp, y_sig_le_rndd);
        let case2_inner = self.make_and(y_sig_le_rndd, -y_sig_eq_rndd);
        let case2 = self.make_and(rndd_exp_eq_y_exp_m1, case2_inner);
        let case3_inner = self.make_and(y_sig_eq_rndd, quot_odd);
        let case3 = self.make_and(rndd_exp_eq_y_exp_m1, case3_inner);
        let case2_or_3 = self.make_or(case2, case3);
        self.make_or(case1, case2_or_3)
    }

    fn rem_apply_special_cases(
        &mut self,
        x: &FpDecomposed,
        special_cases: &RemSpecialCases,
        base: &FpDecomposed,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let mut result = base.clone();
        result = self.make_ite_fp(special_cases.c6, x, &result, precision);
        result = self.make_ite_fp(special_cases.c5, &special_cases.pzero, &result, precision);
        result = self.make_ite_fp(special_cases.c4, &special_cases.nan, &result, precision);
        result = self.make_ite_fp(special_cases.c3, x, &result, precision);
        result = self.make_ite_fp(special_cases.c2, &special_cases.nan, &result, precision);
        self.make_ite_fp(special_cases.c1, &special_cases.nan, &result, precision)
    }

    fn rem_fix_zero_sign(
        &mut self,
        x: &FpDecomposed,
        result: &FpDecomposed,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let pos_zero = self.make_zero(precision, false);
        let neg_zero = self.make_zero(precision, true);
        let correct_zero = self.make_ite_fp(-x.sign, &pos_zero, &neg_zero, precision);
        let result_is_zero = self.is_zero(result);
        self.make_ite_fp(result_is_zero, &correct_zero, result, precision)
    }

    /// Minimum of two FP values.
    pub fn make_min(&mut self, x: &FpDecomposed, y: &FpDecomposed) -> FpDecomposed {
        let precision = x.precision;
        let x_nan = self.is_nan(x);
        let x_zero = self.is_zero(x);
        let y_zero = self.is_zero(y);
        let both_zero = self.make_and(x_zero, y_zero);
        let diff_zero_sign = self.make_xor(x.sign, y.sign);
        let zero_tie = self.make_and(both_zero, diff_zero_sign);
        let y_lt = self.make_lt_result(y, x);
        let use_y = self.make_or(x_nan, y_lt);

        let chosen_sign = self.make_ite(use_y, y.sign, x.sign);
        let tie_sign = self.fresh_var();
        let sign = self.make_ite(zero_tie, tie_sign, chosen_sign);
        let exponent = self.make_ite_bits(use_y, &y.exponent, &x.exponent);
        let significand = self.make_ite_bits(use_y, &y.significand, &x.significand);

        FpDecomposed {
            sign,
            exponent,
            significand,
            precision,
        }
    }

    /// Maximum of two FP values.
    pub fn make_max(&mut self, x: &FpDecomposed, y: &FpDecomposed) -> FpDecomposed {
        let precision = x.precision;
        let x_nan = self.is_nan(x);
        let x_zero = self.is_zero(x);
        let y_zero = self.is_zero(y);
        let both_zero = self.make_and(x_zero, y_zero);
        let diff_zero_sign = self.make_xor(x.sign, y.sign);
        let zero_tie = self.make_and(both_zero, diff_zero_sign);
        let y_gt = self.make_lt_result(x, y);
        let use_y = self.make_or(x_nan, y_gt);

        let chosen_sign = self.make_ite(use_y, y.sign, x.sign);
        let tie_sign = self.fresh_var();
        let sign = self.make_ite(zero_tie, tie_sign, chosen_sign);
        let exponent = self.make_ite_bits(use_y, &y.exponent, &x.exponent);
        let significand = self.make_ite_bits(use_y, &y.significand, &x.significand);

        FpDecomposed {
            sign,
            exponent,
            significand,
            precision,
        }
    }
}
