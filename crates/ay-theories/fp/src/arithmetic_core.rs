// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Core FP arithmetic encodings: add/sub/mul.

use ay_core::CnfClause;

use super::{FpDecomposed, FpSolver, RoundingMode};

impl FpSolver<'_> {
    /// Add two FP values with IEEE 754 rounding.
    pub fn make_add(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        rm: RoundingMode,
    ) -> FpDecomposed {
        let precision = x.precision;
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;

        let x_nan = self.is_nan(x);
        let y_nan = self.is_nan(y);
        let x_inf = self.is_infinite(x);
        let y_inf = self.is_infinite(y);
        let x_zero = self.is_zero(x);
        let y_zero = self.is_zero(y);

        let both_inf = self.make_and(x_inf, y_inf);
        let diff_sign = self.make_xor(x.sign, y.sign);
        let inf_minus_inf = self.make_and(both_inf, diff_sign);
        let either_nan = self.make_or(x_nan, y_nan);
        let result_nan = self.make_or(either_nan, inf_minus_inf);

        let result = self.fresh_decomposed(precision);
        let sign = result.sign;
        let exponent = result.exponent.clone();
        let significand = result.significand.clone();
        let canonical_nan = self.make_nan_value(precision);
        self.constrain_fp_when(result_nan, &result, &canonical_nan);

        let not_result_nan = -result_nan;
        let x_inf_only = self.make_and(x_inf, not_result_nan);
        let not_x_inf = -x_inf;
        let y_inf_only = self.make_and(y_inf, not_result_nan);
        let y_inf_not_x = self.make_and(y_inf_only, not_x_inf);

        let not_y_zero = -y_zero;
        let x_zero_only = self.make_and(x_zero, not_result_nan);
        let x_zero_not_y = self.make_and(x_zero_only, not_y_zero);
        let not_x_zero = -x_zero;
        let y_zero_only = self.make_and(y_zero, not_result_nan);
        let y_zero_not_x = self.make_and(y_zero_only, not_x_zero);
        let both_zero = self.make_and(x_zero, y_zero);

        for ((&exp_bit, &x_exp), &y_exp) in exponent.iter().zip(&x.exponent).zip(&y.exponent) {
            self.add_clause(CnfClause::new(vec![-result_nan, exp_bit]));
            self.add_clause(CnfClause::new(vec![-x_inf_only, x_exp, -exp_bit]));
            self.add_clause(CnfClause::new(vec![-x_inf_only, -x_exp, exp_bit]));
            self.add_clause(CnfClause::new(vec![-y_inf_not_x, y_exp, -exp_bit]));
            self.add_clause(CnfClause::new(vec![-y_inf_not_x, -y_exp, exp_bit]));
            self.add_clause(CnfClause::new(vec![-x_zero_not_y, y_exp, -exp_bit]));
            self.add_clause(CnfClause::new(vec![-x_zero_not_y, -y_exp, exp_bit]));
            self.add_clause(CnfClause::new(vec![-y_zero_not_x, x_exp, -exp_bit]));
            self.add_clause(CnfClause::new(vec![-y_zero_not_x, -x_exp, exp_bit]));
        }

        let sig_len = significand.len();
        for (i, ((&sig_bit, &x_sig), &y_sig)) in significand
            .iter()
            .zip(&x.significand)
            .zip(&y.significand)
            .enumerate()
        {
            if i == sig_len - 1 {
                self.add_clause(CnfClause::new(vec![-result_nan, sig_bit]));
            }
            self.add_clause(CnfClause::new(vec![-x_inf_only, x_sig, -sig_bit]));
            self.add_clause(CnfClause::new(vec![-x_inf_only, -x_sig, sig_bit]));
            self.add_clause(CnfClause::new(vec![-y_inf_not_x, y_sig, -sig_bit]));
            self.add_clause(CnfClause::new(vec![-y_inf_not_x, -y_sig, sig_bit]));
            self.add_clause(CnfClause::new(vec![-x_zero_not_y, y_sig, -sig_bit]));
            self.add_clause(CnfClause::new(vec![-x_zero_not_y, -y_sig, sig_bit]));
            self.add_clause(CnfClause::new(vec![-y_zero_not_x, x_sig, -sig_bit]));
            self.add_clause(CnfClause::new(vec![-y_zero_not_x, -x_sig, sig_bit]));
        }

        self.add_clause(CnfClause::new(vec![-x_inf_only, x.sign, -sign]));
        self.add_clause(CnfClause::new(vec![-x_inf_only, -x.sign, sign]));
        self.add_clause(CnfClause::new(vec![-y_inf_not_x, y.sign, -sign]));
        self.add_clause(CnfClause::new(vec![-y_inf_not_x, -y.sign, sign]));
        self.add_clause(CnfClause::new(vec![-x_zero_not_y, y.sign, -sign]));
        self.add_clause(CnfClause::new(vec![-x_zero_not_y, -y.sign, sign]));
        self.add_clause(CnfClause::new(vec![-y_zero_not_x, x.sign, -sign]));
        self.add_clause(CnfClause::new(vec![-y_zero_not_x, -x.sign, sign]));

        let (c_sgn, c_sig, c_exp, _c_lz) = self.unpack(x, false);
        let (d_sgn, d_sig, d_exp, _d_lz) = self.unpack(y, false);

        let d_larger = self.bv_slt(&c_exp, &d_exp);
        let c_sgn_s = self.make_ite(d_larger, d_sgn, c_sgn);
        let d_sgn_s = self.make_ite(d_larger, c_sgn, d_sgn);
        let c_sig_s = self.make_ite_bits(d_larger, &d_sig, &c_sig);
        let d_sig_s = self.make_ite_bits(d_larger, &c_sig, &d_sig);
        let c_exp_s = self.make_ite_bits(d_larger, &d_exp, &c_exp);
        let d_exp_s = self.make_ite_bits(d_larger, &c_exp, &d_exp);

        let exp_delta = self.bv_sub(&c_exp_s, &d_exp_s);
        let cap_val = (sb + 2) as u64;
        let cap_bv = self.const_bv(cap_val, eb);
        let delta_too_large = self.make_unsigned_lt(&cap_bv, &exp_delta);
        let capped_delta = self.make_ite_bits(delta_too_large, &cap_bv, &exp_delta);

        let three_zeros = self.const_bv(0, 3);
        let c_sig_grs = Self::bv_concat(&three_zeros, &c_sig_s);
        let d_sig_grs = Self::bv_concat(&three_zeros, &d_sig_s);
        let dz = self.const_bv(0, sb + 3);
        let big_d_sig = Self::bv_concat(&dz, &d_sig_grs);

        let shift_width = 2 * (sb + 3);
        let shift_amount = self.zero_extend(&capped_delta, shift_width - eb);
        let shifted_big = self.bv_lshr(&big_d_sig, &shift_amount);
        let aligned_d: Vec<_> = shifted_big[sb + 3..shift_width].to_vec();
        let sticky_bits: Vec<_> = shifted_big[..sb + 3].to_vec();
        let sticky = self.bv_or_reduce(&sticky_bits);
        let mut aligned_d_sticky = aligned_d;
        aligned_d_sticky[0] = self.make_or(aligned_d_sticky[0], sticky);

        let c_ext = self.zero_extend(&c_sig_grs, 2);
        let d_ext = self.zero_extend(&aligned_d_sticky, 2);
        let same_sign = self.make_xnor(c_sgn_s, d_sgn_s);
        let same_magnitude = self.make_bits_equal(&c_ext, &d_ext);
        let c_plus_d = self.bv_add(&c_ext, &d_ext);
        let c_minus_d = self.bv_sub(&c_ext, &d_ext);
        let sum = self.make_ite_bits(same_sign, &c_plus_d, &c_minus_d);

        let sum_msb = sum[sb + 4];
        let not_sum_msb = -sum_msb;
        let not_c_sgn = -c_sgn_s;
        let not_d_sgn = -d_sgn_s;
        let c1 = {
            let t = self.make_and(not_c_sgn, d_sgn_s);
            self.make_and(t, sum_msb)
        };
        let c2 = {
            let t = self.make_and(c_sgn_s, not_d_sgn);
            self.make_and(t, not_sum_msb)
        };
        let c3 = self.make_and(c_sgn_s, d_sgn_s);
        let res_sgn_12 = self.make_or(c1, c2);
        let res_sgn = self.make_or(res_sgn_12, c3);

        let neg_sum = self.bv_neg(&sum);
        let sig_abs = self.make_ite_bits(sum_msb, &neg_sum, &sum);
        let res_sig: Vec<_> = sig_abs[..sb + 4].to_vec();
        let res_exp = self.sign_extend(&c_exp_s, 2);

        let normal_result = self.fp_round(precision, rm, res_sgn, &res_sig, &res_exp);
        let either_special = {
            let inf_or_nan = self.make_or(result_nan, x_inf);
            self.make_or(inf_or_nan, y_inf)
        };
        let any_zero = self.make_or(x_zero, y_zero);
        let special_add = self.make_or(either_special, any_zero);
        let not_special_add = -special_add;
        let exact_cancel = self.make_and(-same_sign, same_magnitude);
        let cancel_zero = self.make_and(not_special_add, exact_cancel);
        let cancel_zero_result = self.make_zero(precision, rm == RoundingMode::RTN);
        self.constrain_fp_when(cancel_zero, &result, &cancel_zero_result);
        let normal_applies = self.make_and(not_special_add, -cancel_zero);
        self.constrain_fp_when(normal_applies, &result, &normal_result);

        let not_nan_both_zero = self.make_and(not_result_nan, both_zero);
        for &exp_bit in &exponent {
            self.add_clause(CnfClause::new(vec![-not_nan_both_zero, -exp_bit]));
        }
        for &sig_bit in &significand {
            self.add_clause(CnfClause::new(vec![-not_nan_both_zero, -sig_bit]));
        }
        let bz_same = {
            let ss = self.make_and(both_zero, -diff_sign);
            self.make_and(not_result_nan, ss)
        };
        self.add_clause(CnfClause::new(vec![-bz_same, -x.sign, sign]));
        self.add_clause(CnfClause::new(vec![-bz_same, x.sign, -sign]));
        let bz_diff = {
            let ds = self.make_and(both_zero, diff_sign);
            self.make_and(not_result_nan, ds)
        };
        if rm == RoundingMode::RTN {
            self.add_clause(CnfClause::new(vec![-bz_diff, sign]));
        } else {
            self.add_clause(CnfClause::new(vec![-bz_diff, -sign]));
        }

        result
    }

    /// Subtract: x - y = x + (-y).
    pub fn make_sub(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        rm: RoundingMode,
    ) -> FpDecomposed {
        let neg_y = self.make_neg(y);
        self.make_add(x, &neg_y, rm)
    }

    /// Multiply two FP values with IEEE 754 rounding.
    pub fn make_mul(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        rm: RoundingMode,
    ) -> FpDecomposed {
        let precision = x.precision;
        let sb = precision.significand_bits() as usize;

        let x_nan = self.is_nan(x);
        let y_nan = self.is_nan(y);
        let x_inf = self.is_infinite(x);
        let y_inf = self.is_infinite(y);
        let x_zero = self.is_zero(x);
        let y_zero = self.is_zero(y);

        let x_inf_y_zero = self.make_and(x_inf, y_zero);
        let y_inf_x_zero = self.make_and(y_inf, x_zero);
        let inf_times_zero = self.make_or(x_inf_y_zero, y_inf_x_zero);
        let either_nan = self.make_or(x_nan, y_nan);
        let result_nan = self.make_or(either_nan, inf_times_zero);
        let result_sign_xor = self.make_xor(x.sign, y.sign);

        let result = self.fresh_decomposed(precision);
        let sign = result.sign;
        let not_nan = -result_nan;
        self.add_clause(CnfClause::new(vec![-not_nan, -result_sign_xor, sign]));
        self.add_clause(CnfClause::new(vec![-not_nan, result_sign_xor, -sign]));

        let either_inf = self.make_or(x_inf, y_inf);
        let not_inf_times_zero = -inf_times_zero;
        let inf_no_zero = self.make_and(either_inf, not_inf_times_zero);
        // NaN strictly dominates Inf (IEEE-754): a NaN operand yields NaN, never
        // Inf. Without `not_nan` here, `+oo * NaN` sets BOTH result_nan and
        // result_inf, and constrain_nan_inf then forces the significand to be both
        // zero (inf) and the canonical-NaN pattern — an unsatisfiable conflict that
        // wrongly makes the branch UNSAT. make_div / make_add already gate on
        // not_nan; mirror them.
        let result_inf = self.make_and(inf_no_zero, not_nan);
        let special = self.constrain_nan_inf(&result, result_nan, result_inf);
        let either_zero = self.make_or(x_zero, y_zero);

        let (_a_sgn, a_sig, a_exp, a_lz) = self.unpack(x, true);
        let (_b_sgn, b_sig, b_exp, b_lz) = self.unpack(y, true);

        let a_sig_ext = self.zero_extend(&a_sig, sb);
        let b_sig_ext = self.zero_extend(&b_sig, sb);
        let product = self.bv_mul(&a_sig_ext, &b_sig_ext);

        let a_exp_ext = self.sign_extend(&a_exp, 2);
        let b_exp_ext = self.sign_extend(&b_exp, 2);
        let a_lz_ext = self.zero_extend(&a_lz, 2);
        let b_lz_ext = self.zero_extend(&b_lz, 2);
        let a_effective = self.bv_sub(&a_exp_ext, &a_lz_ext);
        let b_effective = self.bv_sub(&b_exp_ext, &b_lz_ext);
        let res_exp = self.bv_add(&a_effective, &b_effective);

        let h_p: Vec<_> = product[sb..2 * sb].to_vec();
        let rbits = if sb >= 4 {
            let sticky = self.bv_or_reduce(&product[..sb - 3]);
            vec![sticky, product[sb - 3], product[sb - 2], product[sb - 1]]
        } else {
            let mut r = product[..sb].to_vec();
            let zero = self.const_false();
            while r.len() < 4 {
                r.push(zero);
            }
            r
        };

        let mut res_sig = rbits;
        res_sig.extend_from_slice(&h_p);
        debug_assert_eq!(res_sig.len(), sb + 4);

        let normal_result = self.fp_round(precision, rm, result_sign_xor, &res_sig, &res_exp);
        let special_or_zero = self.make_or(special, either_zero);
        let not_special = -special_or_zero;
        self.constrain_fp_when(not_special, &result, &normal_result);

        let not_nan_and_zero = self.make_and(not_nan, either_zero);
        for &exp_bit in &result.exponent {
            self.add_clause(CnfClause::new(vec![-not_nan_and_zero, -exp_bit]));
        }
        for &sig_bit in &result.significand {
            self.add_clause(CnfClause::new(vec![-not_nan_and_zero, -sig_bit]));
        }

        result
    }
}
