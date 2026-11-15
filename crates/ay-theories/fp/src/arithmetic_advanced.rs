// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Higher-cost FP arithmetic encodings: div and sqrt.

use ay_core::{CnfClause, CnfLit};

use crate::construction::control::{uninterrupted, BuildControl};
use crate::construction::FpBuildStage;

use super::gates::neg_lit;
use super::{FpDecomposed, FpSolver, RmOperand};

impl FpSolver<'_> {
    /// Divide two FP values with IEEE 754 rounding.
    pub fn make_div(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        rm: impl Into<RmOperand>,
    ) -> FpDecomposed {
        let rm = rm.into();
        uninterrupted(|control| self.make_div_with_control(x, y, rm, control))
    }

    pub(crate) fn make_div_with_control<C: BuildControl>(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        rm: RmOperand,
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
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

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.fresh_decomposed(precision);
        let sign = result.sign;
        self.add_clause(CnfClause::new(vec![-not_nan, -result_sign_xor, sign]));
        self.add_clause(CnfClause::new(vec![-not_nan, result_sign_xor, -sign]));

        let special = self.constrain_nan_inf(&result, result_nan, result_inf);
        let x_zero_not_nan = self.make_and(x_zero, not_nan);
        let y_inf_not_nan = self.make_and(y_inf, not_nan);
        let zero_result = self.make_or(x_zero_not_nan, y_inf_not_nan);

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let (_a_sgn, a_sig, a_exp, a_lz) = self.unpack(x, true);
        let (_b_sgn, b_sig, b_exp, b_lz) = self.unpack(y, true);

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let div_width = 3 * sb + 2;
        let dividend_zeros = self.const_bv(0, sb + extra_bits);
        let a_sig_ext = Self::bv_concat(&dividend_zeros, &a_sig);
        debug_assert_eq!(a_sig_ext.len(), div_width);

        let b_sig_ext = self.zero_extend(&b_sig, sb + extra_bits);
        debug_assert_eq!(b_sig_ext.len(), div_width);

        let (quotient, _rem) = self.bv_udiv_urem_with_control(&a_sig_ext, &b_sig_ext, control)?;
        debug_assert_eq!(quotient.len(), div_width);

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        // Signed, `eb + 2` bits (z3's) unless the quotient's exponent needs
        // more (`div_exponent_width`).
        let eb = precision.exponent_bits() as usize;
        let dw = Self::div_exponent_width(eb, sb);
        let a_exp_ext = self.sign_extend(&a_exp, dw - eb);
        let b_exp_ext = self.sign_extend(&b_exp, dw - eb);
        let a_lz_ext = self.zero_extend(&a_lz, dw - a_lz.len());
        let b_lz_ext = self.zero_extend(&b_lz, dw - b_lz.len());
        let a_effective = self.bv_sub(&a_exp_ext, &a_lz_ext);
        let b_effective = self.bv_sub(&b_exp_ext, &b_lz_ext);
        let res_exp = self.bv_sub(&a_effective, &b_effective);

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
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

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let res_sig_lz = self.bv_leading_zeros(&res_sig, sb + 4);
        let one_sig = self.const_bv(1, sb + 4);
        let shift_amount = self.bv_sub(&res_sig_lz, &one_sig);
        let lz_le_1 = {
            let two_sig = self.const_bv(2, sb + 4);
            self.make_unsigned_lt(&res_sig_lz, &two_sig)
        };
        let shifted_sig = self.bv_shl(&res_sig, &shift_amount);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        // The shift is used only when it is one place (`lz == 2`), which any
        // width holds.
        let shift_for_exp = self.resize_unsigned(&shift_amount, dw);
        let shifted_exp = self.bv_sub(&res_exp, &shift_for_exp);

        let norm_sig = self.make_ite_bits(lz_le_1, &res_sig, &shifted_sig);
        let norm_exp = self.make_ite_bits(lz_le_1, &res_exp, &shifted_exp);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let normal_result = self.fp_round(precision, rm, result_sign_xor, &norm_sig, &norm_exp);

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
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

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        Ok(result)
    }

    /// Square root with IEEE 754 rounding.
    pub fn make_sqrt(&mut self, x: &FpDecomposed, rm: impl Into<RmOperand>) -> FpDecomposed {
        let rm = rm.into();
        uninterrupted(|control| self.make_sqrt_with_control(x, rm, control))
    }

    pub(crate) fn make_sqrt_with_control<C: BuildControl>(
        &mut self,
        x: &FpDecomposed,
        rm: RmOperand,
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let precision = x.precision;
        let x_nan = self.is_nan(x);
        let x_zero = self.is_zero(x);
        let x_neg_nonzero = self.make_and(x.sign, neg_lit(x_zero));
        let result_nan = self.make_or(x_nan, x_neg_nonzero);

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.fresh_decomposed(precision);
        let (special, x_zero_not_nan) =
            self.constrain_sqrt_special_cases(x, &result, result_nan, x_zero);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let (res_sig, res_exp) = self.sqrt_rounding_terms_with_control(x, control)?;

        let pos_sign = self.const_false();
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let normal_result = self.fp_round(precision, rm, pos_sign, &res_sig, &res_exp);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let special_or_zero = self.make_or(special, x_zero_not_nan);
        self.constrain_fp_when(neg_lit(special_or_zero), &result, &normal_result);
        self.constrain_zero_result(x_zero_not_nan, &result);
        drop(normal_result);
        drop(res_sig);
        drop(res_exp);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        Ok(result)
    }

    fn constrain_sqrt_special_cases(
        &mut self,
        x: &FpDecomposed,
        result: &FpDecomposed,
        result_nan: CnfLit,
        x_zero: CnfLit,
    ) -> (CnfLit, CnfLit) {
        let sign = result.sign;
        let not_sign = neg_lit(sign);
        let not_x_zero = neg_lit(x_zero);
        let not_x_sign = neg_lit(x.sign);
        let not_nan = neg_lit(result_nan);
        // IEEE 754: sqrt is sign-preserving on zero (sqrt(+0)=+0, sqrt(-0)=-0)
        // and positive for every other non-NaN result. The result sign is only
        // forced positive when the input is neither NaN nor zero; the zero case
        // is pinned to x's sign by the two clauses below (#bug14: previously the
        // unconditional `-sign` clause conflicted with the negative-zero case,
        // making sqrt(-0) unsat for both polarities).
        self.add_clause(CnfClause::new(vec![result_nan, x_zero, not_sign]));
        self.add_clause(CnfClause::new(vec![not_x_zero, x.sign, not_sign]));
        self.add_clause(CnfClause::new(vec![not_x_zero, not_x_sign, sign]));

        let x_inf = self.is_infinite(x);
        let pos_inf = self.make_and(x_inf, not_x_sign);
        let special = self.constrain_nan_inf(result, result_nan, pos_inf);
        (special, self.make_and(x_zero, not_nan))
    }

    fn sqrt_rounding_terms_with_control<C: BuildControl>(
        &mut self,
        x: &FpDecomposed,
        control: &mut C,
    ) -> Result<(Vec<CnfLit>, Vec<CnfLit>), C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let precision = x.precision;
        let sb = precision.significand_bits() as usize;
        let (_a_sgn, a_sig, a_exp, a_lz) = self.unpack(x, true);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        // z3 holds the normalised exponent in `eb + 1` bits and rounds the
        // halved one at `eb + 2`; both widen where the format needs it
        // (`sqrt_exponent_widths`).
        let eb = precision.exponent_bits() as usize;
        let (uw, rw) = Self::sqrt_exponent_widths(eb, sb);
        let a_exp_ext = self.sign_extend(&a_exp, uw - eb);
        let a_lz_ext = self.zero_extend(&a_lz, uw - a_lz.len());
        let real_exp = self.bv_sub(&a_exp_ext, &a_lz_ext);
        let halved_exp: Vec<CnfLit> = real_exp[1..].to_vec();
        let res_exp = self.sign_extend(&halved_exp, rw - halved_exp.len());

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let sig_base = self.sqrt_significand_base(&a_sig, real_exp[0]);
        let zeros4 = self.const_bv(0, 4);
        let sig_work = Self::bv_concat(&zeros4, &sig_base);
        let (q_bits, r_bits) =
            self.sqrt_digit_recurrence_with_control(&sig_work, sb + 3, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let res_sig = self.sqrt_result_significand(&q_bits, &r_bits, sb);
        drop(q_bits);
        drop(r_bits);
        drop(sig_work);
        drop(zeros4);
        drop(sig_base);
        drop(halved_exp);
        drop(real_exp);
        drop(a_lz_ext);
        drop(a_exp_ext);
        drop(a_lz);
        drop(a_exp);
        drop(a_sig);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        Ok((res_sig, res_exp))
    }

    fn sqrt_significand_base(&mut self, a_sig: &[CnfLit], e_is_odd: CnfLit) -> Vec<CnfLit> {
        let zero = self.const_false();
        let sig_shifted = Self::bv_concat(&[zero], a_sig);
        let sig_unshifted = self.zero_extend(a_sig, 1);
        self.make_ite_bits(e_is_odd, &sig_shifted, &sig_unshifted)
    }

    fn sqrt_digit_recurrence_with_control<C: BuildControl>(
        &mut self,
        sig_work: &[CnfLit],
        iterations: usize,
        control: &mut C,
    ) -> Result<(Vec<CnfLit>, Vec<CnfLit>), C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let sig_width = sig_work.len();
        let zero = self.const_false();
        let mut q_bits = vec![zero; sig_width];
        let one = self.const_true();
        // The caller passes `iterations = sb + 3` for a `sb + 5`-bit `sig_work`.
        if let Some(bit) = q_bits.get_mut(iterations) {
            *bit = one;
        }
        let mut r_bits = self.bv_sub(sig_work, &q_bits);
        let mut s_bits = q_bits.clone();

        for _ in 0..iterations {
            control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
            // Logical shift right by one: new_s[i] = s_bits[i + 1], MSB zero.
            let mut new_s = vec![zero; sig_width];
            for (dst, &src) in new_s.iter_mut().zip(s_bits.iter().skip(1)) {
                *dst = src;
            }
            s_bits = new_s;

            let r_wide = Self::bv_concat(&[zero], &r_bits);
            let q_wide = Self::bv_concat(&[zero], &q_bits);
            let s_wide = self.zero_extend(&s_bits, 1);
            let two_q_plus_s = self.bv_add(&q_wide, &s_wide);
            let t_wide = self.bv_sub(&r_wide, &two_q_plus_s);
            // `t_wide` is `sig_width + 1` bits wide: its MSB (bit `sig_width`)
            // is the sign, the rest the low `sig_width` bits. A zero-width
            // difference would be 0, which is not negative.
            let (t_neg, t_low) = match t_wide.split_last() {
                Some((&msb, low)) => (msb, low),
                None => (zero, &[][..]),
            };

            let q_or_s = self.bv_or(&q_bits, &s_bits);
            q_bits = self.make_ite_bits(t_neg, &q_bits, &q_or_s);
            // Shift left by one: r_shifted[i + 1] = r_bits[i], LSB zero.
            let mut r_shifted = vec![zero; sig_width];
            for (dst, &src) in r_shifted.iter_mut().skip(1).zip(r_bits.iter()) {
                *dst = src;
            }
            r_bits = self.make_ite_bits(t_neg, &r_shifted, t_low);
            drop(r_shifted);
            drop(q_or_s);
            drop(t_wide);
            drop(two_q_plus_s);
            drop(s_wide);
            drop(q_wide);
            drop(r_wide);
            control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        }

        drop(s_bits);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        Ok((q_bits, r_bits))
    }

    fn sqrt_result_significand(
        &mut self,
        q_bits: &[CnfLit],
        r_bits: &[CnfLit],
        sb: usize,
    ) -> Vec<CnfLit> {
        let r_is_zero = self.make_all_zero(r_bits);
        // `q_bits` is `sb + 5` bits wide (`sqrt_rounding_terms`): bits
        // `1..=sb + 3` are the result, bit 0 feeds the sticky bit. `sb` comes
        // from a `u32`, so the saturating sums equal `sb + 3` and `sb + 4`.
        let mut rest = q_bits.get(1..).map_or_else(Vec::new, <[CnfLit]>::to_vec);
        rest.truncate(sb.saturating_add(3));
        let rest_ext = self.zero_extend(&rest, 1);
        let one = self.const_true();
        let q_lsb = match q_bits.first() {
            Some(&lsb) => lsb,
            None => self.const_false(),
        };
        let sticky_val = self.make_ite(r_is_zero, q_lsb, one);
        let mut sticky_bv = vec![self.const_false(); sb.saturating_add(4)];
        if let Some(lsb) = sticky_bv.first_mut() {
            *lsb = sticky_val;
        }
        self.bv_or(&rest_ext, &sticky_bv)
    }

    fn constrain_zero_result(&mut self, guard: CnfLit, result: &FpDecomposed) {
        let not_guard = neg_lit(guard);
        for &exp_bit in &result.exponent {
            self.add_clause(CnfClause::new(vec![not_guard, neg_lit(exp_bit)]));
        }
        for &sig_bit in &result.significand {
            self.add_clause(CnfClause::new(vec![not_guard, neg_lit(sig_bit)]));
        }
    }
}

#[cfg(test)]
#[path = "arithmetic_advanced/sqrt_rows.rs"]
mod sqrt_rows;
