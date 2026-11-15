// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only exact old square-root circuit, apart from private helper names.

use crate::gates::neg_lit;
use crate::{FpDecomposed, FpSolver, RmOperand};
use ay_core::{CnfClause, CnfLit};

impl FpSolver<'_> {
    /// Square root with IEEE 754 rounding.
    pub(super) fn legacy_make_sqrt(
        &mut self,
        x: &FpDecomposed,
        rm: impl Into<RmOperand>,
    ) -> FpDecomposed {
        let rm = rm.into();
        let precision = x.precision;
        let x_nan = self.is_nan(x);
        let x_zero = self.is_zero(x);
        let x_neg_nonzero = self.make_and(x.sign, neg_lit(x_zero));
        let result_nan = self.make_or(x_nan, x_neg_nonzero);

        let result = self.fresh_decomposed(precision);
        let (special, x_zero_not_nan) =
            self.legacy_constrain_sqrt_special_cases(x, &result, result_nan, x_zero);
        let (res_sig, res_exp) = self.legacy_sqrt_rounding_terms(x);

        let pos_sign = self.const_false();
        let normal_result = self.fp_round(precision, rm, pos_sign, &res_sig, &res_exp);
        let special_or_zero = self.make_or(special, x_zero_not_nan);
        self.constrain_fp_when(neg_lit(special_or_zero), &result, &normal_result);
        self.legacy_constrain_zero_result(x_zero_not_nan, &result);
        result
    }

    fn legacy_constrain_sqrt_special_cases(
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

    fn legacy_sqrt_rounding_terms(&mut self, x: &FpDecomposed) -> (Vec<CnfLit>, Vec<CnfLit>) {
        let precision = x.precision;
        let sb = precision.significand_bits() as usize;
        let (_a_sgn, a_sig, a_exp, a_lz) = self.unpack(x, true);
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

        let sig_base = self.legacy_sqrt_significand_base(&a_sig, real_exp[0]);
        let zeros4 = self.const_bv(0, 4);
        let sig_work = Self::bv_concat(&zeros4, &sig_base);
        let (q_bits, r_bits) = self.legacy_sqrt_digit_recurrence(&sig_work, sb + 3);
        let res_sig = self.legacy_sqrt_result_significand(&q_bits, &r_bits, sb);
        (res_sig, res_exp)
    }

    fn legacy_sqrt_significand_base(&mut self, a_sig: &[CnfLit], e_is_odd: CnfLit) -> Vec<CnfLit> {
        let zero = self.const_false();
        let sig_shifted = Self::bv_concat(&[zero], a_sig);
        let sig_unshifted = self.zero_extend(a_sig, 1);
        self.make_ite_bits(e_is_odd, &sig_shifted, &sig_unshifted)
    }

    fn legacy_sqrt_digit_recurrence(
        &mut self,
        sig_work: &[CnfLit],
        iterations: usize,
    ) -> (Vec<CnfLit>, Vec<CnfLit>) {
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
        }

        (q_bits, r_bits)
    }

    fn legacy_sqrt_result_significand(
        &mut self,
        q_bits: &[CnfLit],
        r_bits: &[CnfLit],
        sb: usize,
    ) -> Vec<CnfLit> {
        let r_is_zero = self.make_all_zero(r_bits);
        // `q_bits` is `sb + 5` bits wide (`legacy_sqrt_rounding_terms`): bits
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

    fn legacy_constrain_zero_result(&mut self, guard: CnfLit, result: &FpDecomposed) {
        let not_guard = neg_lit(guard);
        for &exp_bit in &result.exponent {
            self.add_clause(CnfClause::new(vec![not_guard, neg_lit(exp_bit)]));
        }
        for &sig_bit in &result.significand {
            self.add_clause(CnfClause::new(vec![not_guard, neg_lit(sig_bit)]));
        }
    }
}
