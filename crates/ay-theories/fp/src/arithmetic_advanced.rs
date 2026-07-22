// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Higher-cost FP arithmetic encodings: div and sqrt.

use ay_core::{CnfClause, CnfLit};

use super::{FpDecomposed, FpSolver, RoundingMode};

impl FpSolver<'_> {
    /// Divide two FP values with IEEE 754 rounding.
    pub fn make_div(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        rm: RoundingMode,
    ) -> FpDecomposed {
        let precision = x.precision;
        let sb = precision.significand_bits() as usize;
        let extra_bits = sb + 2;

        let x_nan = self.is_nan(x);
        let y_nan = self.is_nan(y);
        let x_inf = self.is_infinite(x);
        let y_inf = self.is_infinite(y);
        let x_zero = self.is_zero(x);
        let y_zero = self.is_zero(y);

        let zero_div_zero = self.make_and(x_zero, y_zero);
        let inf_div_inf = self.make_and(x_inf, y_inf);
        let special_nan = self.make_or(zero_div_zero, inf_div_inf);
        let either_nan = self.make_or(x_nan, y_nan);
        let result_nan = self.make_or(either_nan, special_nan);

        let not_x_zero = -x_zero;
        let div_by_zero = self.make_and(y_zero, not_x_zero);
        let not_y_inf = -y_inf;
        let x_inf_not_y = self.make_and(x_inf, not_y_inf);
        let inf_result = self.make_or(x_inf_not_y, div_by_zero);
        let not_nan = -result_nan;
        let result_inf = self.make_and(inf_result, not_nan);
        let result_sign_xor = self.make_xor(x.sign, y.sign);

        let result = self.fresh_decomposed(precision);
        let sign = result.sign;
        self.add_clause(CnfClause::new(vec![-not_nan, -result_sign_xor, sign]));
        self.add_clause(CnfClause::new(vec![-not_nan, result_sign_xor, -sign]));

        let special = self.constrain_nan_inf(&result, result_nan, result_inf);
        let x_zero_not_nan = self.make_and(x_zero, not_nan);
        let y_inf_not_nan = self.make_and(y_inf, not_nan);
        let zero_result = self.make_or(x_zero_not_nan, y_inf_not_nan);

        let (_a_sgn, a_sig, a_exp, a_lz) = self.unpack(x, true);
        let (_b_sgn, b_sig, b_exp, b_lz) = self.unpack(y, true);

        let div_width = 3 * sb + 2;
        let dividend_zeros = self.const_bv(0, sb + extra_bits);
        let a_sig_ext = Self::bv_concat(&dividend_zeros, &a_sig);
        debug_assert_eq!(a_sig_ext.len(), div_width);

        let b_sig_ext = self.zero_extend(&b_sig, sb + extra_bits);
        debug_assert_eq!(b_sig_ext.len(), div_width);

        let (quotient, _rem) = self.bv_udiv_urem(&a_sig_ext, &b_sig_ext);
        debug_assert_eq!(quotient.len(), div_width);

        let a_exp_ext = self.sign_extend(&a_exp, 2);
        let b_exp_ext = self.sign_extend(&b_exp, 2);
        let a_lz_ext = self.zero_extend(&a_lz, 2);
        let b_lz_ext = self.zero_extend(&b_lz, 2);
        let a_effective = self.bv_sub(&a_exp_ext, &a_lz_ext);
        let b_effective = self.bv_sub(&b_exp_ext, &b_lz_ext);
        let res_exp = self.bv_sub(&a_effective, &b_effective);

        let sticky = if extra_bits >= 2 {
            self.bv_or_reduce(&quotient[..extra_bits - 1])
        } else {
            self.const_false()
        };
        let main_sig: Vec<CnfLit> = quotient[extra_bits - 1..extra_bits + sb + 2].to_vec();
        debug_assert_eq!(main_sig.len(), sb + 3);

        let mut res_sig = vec![sticky];
        res_sig.extend_from_slice(&main_sig);
        debug_assert_eq!(res_sig.len(), sb + 4);

        let upper: Vec<CnfLit> = quotient[extra_bits + sb + 2..].to_vec();
        let too_large = if upper.is_empty() {
            self.const_false()
        } else {
            self.bv_or_reduce(&upper)
        };

        let res_sig_lz = self.bv_leading_zeros(&res_sig, sb + 4);
        let one_sig = self.const_bv(1, sb + 4);
        let shift_amount = self.bv_sub(&res_sig_lz, &one_sig);
        let lz_le_1 = {
            let two_sig = self.const_bv(2, sb + 4);
            self.make_unsigned_lt(&res_sig_lz, &two_sig)
        };
        let shifted_sig = self.bv_shl(&res_sig, &shift_amount);
        let eb = precision.exponent_bits() as usize;
        let shift_for_exp = if sb + 4 >= eb + 2 {
            shift_amount[..eb + 2].to_vec()
        } else {
            self.zero_extend(&shift_amount, (eb + 2) - (sb + 4))
        };
        let shifted_exp = self.bv_sub(&res_exp, &shift_for_exp);

        let norm_sig = self.make_ite_bits(lz_le_1, &res_sig, &shifted_sig);
        let norm_exp = self.make_ite_bits(lz_le_1, &res_exp, &shifted_exp);
        let normal_result = self.fp_round(precision, rm, result_sign_xor, &norm_sig, &norm_exp);

        let not_too_large = -too_large;
        let special_or_zero = self.make_or(special, zero_result);
        let not_special_or_zero = -special_or_zero;
        let normal_applies = self.make_and(not_special_or_zero, not_too_large);
        self.constrain_fp_when(normal_applies, &result, &normal_result);

        let too_large_not_special = self.make_and(too_large, -special);
        for &exp_bit in &result.exponent {
            self.add_clause(CnfClause::new(vec![-too_large_not_special, exp_bit]));
        }
        for &sig_bit in &result.significand {
            self.add_clause(CnfClause::new(vec![-too_large_not_special, -sig_bit]));
        }

        for &exp_bit in &result.exponent {
            self.add_clause(CnfClause::new(vec![-zero_result, -exp_bit]));
        }
        for &sig_bit in &result.significand {
            self.add_clause(CnfClause::new(vec![-zero_result, -sig_bit]));
        }

        result
    }

    /// Square root with IEEE 754 rounding.
    pub fn make_sqrt(&mut self, x: &FpDecomposed, rm: RoundingMode) -> FpDecomposed {
        let precision = x.precision;
        let x_nan = self.is_nan(x);
        let x_zero = self.is_zero(x);
        let x_neg_nonzero = self.make_and(x.sign, -x_zero);
        let result_nan = self.make_or(x_nan, x_neg_nonzero);

        let result = self.fresh_decomposed(precision);
        let (special, x_zero_not_nan) =
            self.constrain_sqrt_special_cases(x, &result, result_nan, x_zero);
        let (res_sig, res_exp) = self.sqrt_rounding_terms(x);

        let pos_sign = self.const_false();
        let normal_result = self.fp_round(precision, rm, pos_sign, &res_sig, &res_exp);
        let special_or_zero = self.make_or(special, x_zero_not_nan);
        self.constrain_fp_when(-special_or_zero, &result, &normal_result);
        self.constrain_zero_result(x_zero_not_nan, &result);
        result
    }

    fn constrain_sqrt_special_cases(
        &mut self,
        x: &FpDecomposed,
        result: &FpDecomposed,
        result_nan: CnfLit,
        x_zero: CnfLit,
    ) -> (CnfLit, CnfLit) {
        let sign = result.sign;
        let not_nan = -result_nan;
        // IEEE 754: sqrt is sign-preserving on zero (sqrt(+0)=+0, sqrt(-0)=-0)
        // and positive for every other non-NaN result. The result sign is only
        // forced positive when the input is neither NaN nor zero; the zero case
        // is pinned to x's sign by the two clauses below (#bug14: previously the
        // unconditional `-sign` clause conflicted with the negative-zero case,
        // making sqrt(-0) unsat for both polarities).
        self.add_clause(CnfClause::new(vec![-not_nan, x_zero, -sign]));
        self.add_clause(CnfClause::new(vec![-x_zero, x.sign, -sign]));
        self.add_clause(CnfClause::new(vec![-x_zero, -x.sign, sign]));

        let x_inf = self.is_infinite(x);
        let pos_inf = self.make_and(x_inf, -x.sign);
        let special = self.constrain_nan_inf(result, result_nan, pos_inf);
        (special, self.make_and(x_zero, not_nan))
    }

    fn sqrt_rounding_terms(&mut self, x: &FpDecomposed) -> (Vec<CnfLit>, Vec<CnfLit>) {
        let precision = x.precision;
        let sb = precision.significand_bits() as usize;
        let (_a_sgn, a_sig, a_exp, a_lz) = self.unpack(x, true);
        let a_exp_ext = self.sign_extend(&a_exp, 1);
        let a_lz_ext = self.zero_extend(&a_lz, 1);
        let real_exp = self.bv_sub(&a_exp_ext, &a_lz_ext);
        let halved_exp: Vec<CnfLit> = real_exp[1..].to_vec();
        let res_exp = self.sign_extend(&halved_exp, 2);

        let sig_base = self.sqrt_significand_base(&a_sig, real_exp[0]);
        let zeros4 = self.const_bv(0, 4);
        let sig_work = Self::bv_concat(&zeros4, &sig_base);
        let (q_bits, r_bits) = self.sqrt_digit_recurrence(&sig_work, sb + 3);
        let res_sig = self.sqrt_result_significand(&q_bits, &r_bits, sb);
        (res_sig, res_exp)
    }

    fn sqrt_significand_base(&mut self, a_sig: &[CnfLit], e_is_odd: CnfLit) -> Vec<CnfLit> {
        let zero = self.const_false();
        let sig_shifted = Self::bv_concat(&[zero], a_sig);
        let sig_unshifted = self.zero_extend(a_sig, 1);
        self.make_ite_bits(e_is_odd, &sig_shifted, &sig_unshifted)
    }

    fn sqrt_digit_recurrence(
        &mut self,
        sig_work: &[CnfLit],
        iterations: usize,
    ) -> (Vec<CnfLit>, Vec<CnfLit>) {
        let sig_width = sig_work.len();
        let zero = self.const_false();
        let mut q_bits = vec![zero; sig_width];
        q_bits[iterations] = self.const_true();
        let mut r_bits = self.bv_sub(sig_work, &q_bits);
        let mut s_bits = q_bits.clone();

        for _ in 0..iterations {
            let mut new_s = vec![zero; sig_width];
            new_s[..sig_width - 1].copy_from_slice(&s_bits[1..sig_width]);
            s_bits = new_s;

            let r_wide = Self::bv_concat(&[zero], &r_bits);
            let q_wide = Self::bv_concat(&[zero], &q_bits);
            let s_wide = self.zero_extend(&s_bits, 1);
            let two_q_plus_s = self.bv_add(&q_wide, &s_wide);
            let t_wide = self.bv_sub(&r_wide, &two_q_plus_s);
            let t_neg = t_wide[sig_width];

            let q_or_s = self.bv_or(&q_bits, &s_bits);
            q_bits = self.make_ite_bits(t_neg, &q_bits, &q_or_s);
            let mut r_shifted = vec![zero; sig_width];
            r_shifted[1..sig_width].copy_from_slice(&r_bits[..sig_width - 1]);
            r_bits = self.make_ite_bits(t_neg, &r_shifted, &t_wide[..sig_width]);
        }

        (q_bits, r_bits)
    }

    fn sqrt_result_significand(
        &mut self,
        q_bits: &[CnfLit],
        r_bits: &[CnfLit],
        sb: usize,
    ) -> Vec<CnfLit> {
        let r_is_zero = self.make_all_zero(r_bits);
        let rest: Vec<CnfLit> = q_bits[1..1 + sb + 3].to_vec();
        let rest_ext = self.zero_extend(&rest, 1);
        let one = self.const_true();
        let sticky_val = self.make_ite(r_is_zero, q_bits[0], one);
        let mut sticky_bv = vec![self.const_false(); sb + 4];
        sticky_bv[0] = sticky_val;
        self.bv_or(&rest_ext, &sticky_bv)
    }

    fn constrain_zero_result(&mut self, guard: CnfLit, result: &FpDecomposed) {
        for &exp_bit in &result.exponent {
            self.add_clause(CnfClause::new(vec![-guard, -exp_bit]));
        }
        for &sig_bit in &result.significand {
            self.add_clause(CnfClause::new(vec![-guard, -sig_bit]));
        }
    }
}
