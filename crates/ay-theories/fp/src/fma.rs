// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fused multiply-add encoding.

use ay_core::term::{Constant, TermData, TermId};
use ay_core::{CnfClause, CnfLit};

use super::{FpDecomposed, FpPrecision, FpSolver, RoundingMode};

/// Static classification of an FP operand. Used by the fma-zero rewriter to
/// short-circuit the expensive FMA bit-blast when a multiplicand is known
/// statically to be a particular special value.
///
/// See [`FpSolver::classify_fp_zero_const`] for the recognition predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FpConstClass {
    /// `+0.0` (positive zero).
    PosZero,
    /// `-0.0` (negative zero).
    NegZero,
}

impl FpSolver<'_> {
    /// Classify a syntactic FP term as a concrete zero constant, if recognizable.
    ///
    /// Recognizes:
    /// - `(_ +zero eb sb)` → [`FpConstClass::PosZero`]
    /// - `(_ -zero eb sb)` → [`FpConstClass::NegZero`]
    /// - `(fp (_ bv0 1) (_ bv0 eb) (_ bv0 sb))` → [`FpConstClass::PosZero`]
    /// - `(fp (_ bv1 1) (_ bv0 eb) (_ bv0 sb))` → [`FpConstClass::NegZero`]
    ///
    /// Returns `None` for everything else (including symbolic terms and
    /// non-zero constants such as `+oo`, `NaN`, `0.5`).
    ///
    /// Used by [`FpSolver::try_make_fma_zero_factor`] to detect the
    /// Z3 issue #8185 rewrite pattern at decompose time, avoiding the
    /// expensive full FMA bit-blast circuit.
    pub(crate) fn classify_fp_zero_const(&self, term: TermId) -> Option<FpConstClass> {
        let data = self.terms.get(term);
        let TermData::App(sym, args) = data else {
            return None;
        };
        match sym.name() {
            // Indexed nullary constants from `(_ +zero eb sb)` / `(_ -zero eb sb)`.
            "+zero" | "fp.zero" if args.is_empty() => Some(FpConstClass::PosZero),
            "-zero" if args.is_empty() => Some(FpConstClass::NegZero),
            // `(fp sign exp sig)` triple with concrete zero exponent and significand.
            "fp" if args.len() == 3 => {
                let sign = self.extract_bv_bit(args[0])?;
                if !self.bv_is_zero(args[1]) || !self.bv_is_zero(args[2]) {
                    return None;
                }
                if sign {
                    Some(FpConstClass::NegZero)
                } else {
                    Some(FpConstClass::PosZero)
                }
            }
            _ => None,
        }
    }

    /// Extract a single-bit BV constant as a bool; returns `None` if not a
    /// 1-bit BV constant.
    fn extract_bv_bit(&self, term: TermId) -> Option<bool> {
        match self.terms.get(term) {
            TermData::Const(Constant::BitVec { value, width }) if *width == 1 => {
                Some(value.sign() == num_bigint::Sign::Plus && value.bit(0))
            }
            _ => None,
        }
    }

    /// Check if a BV term is a concrete all-zero constant.
    fn bv_is_zero(&self, term: TermId) -> bool {
        matches!(
            self.terms.get(term),
            TermData::Const(Constant::BitVec { value, .. }) if value.sign() == num_bigint::Sign::NoSign
        )
    }

    /// Detect FP zero-multiplicand fma pattern and emit a reduced encoding.
    ///
    /// Port of Z3 PR #9038 (fix for Z3 issue #8185): when one of the two
    /// multiplicands of `fma(rm, a, b, c)` is a concrete FP zero, the full
    /// FMA bit-blast circuit is unnecessary and can be replaced by a
    /// simpler `ite(isFinite(other), add(product_zero, c), NaN)` form.
    ///
    /// IEEE 754-2008 § 7.2 / § 6.1 semantics:
    /// - `0 * NaN = NaN`, `0 * ±inf = NaN`.
    /// - `±0 * finite = ±0` with sign = sign(zero) XOR sign(finite).
    /// - `fma(rm, ±0, y, c) = fp.add(rm, product_zero, c)` where
    ///   `product_zero` is `±0` chosen by the sign rule above.
    ///
    /// Returns `Some(result)` if the rewrite applies; otherwise `None` so
    /// the caller falls back to the full [`FpSolver::make_fma`] bit-blast.
    pub(crate) fn try_make_fma_zero_factor(
        &mut self,
        x_term: TermId,
        y_term: TermId,
        z: &FpDecomposed,
        rm: RoundingMode,
    ) -> Option<FpDecomposed> {
        // Identify which of (x, y) is the concrete zero multiplicand.
        let (zero_class, other_term) = if let Some(c) = self.classify_fp_zero_const(x_term) {
            (c, y_term)
        } else {
            let c = self.classify_fp_zero_const(y_term)?;
            (c, x_term)
        };

        let precision = z.precision;
        let other = self.get_fp(other_term);
        Some(self.encode_fma_zero_factor(zero_class, &other, z, rm, precision))
    }

    /// Encode the reduced fma-with-zero-factor circuit.
    ///
    /// Produces `ite(isNaN(other) | isInf(other), NaN, add(product_zero, z))`
    /// where `product_zero`'s sign follows IEEE 754 sign-of-product rules:
    /// `sign(±0 * other) = sign(zero) XOR sign(other)`.
    ///
    /// This avoids the multi-thousand-clause FMA bit-blast circuit when
    /// one multiplicand is known statically to be zero.
    fn encode_fma_zero_factor(
        &mut self,
        zero_class: FpConstClass,
        other: &FpDecomposed,
        z: &FpDecomposed,
        rm: RoundingMode,
        precision: FpPrecision,
    ) -> FpDecomposed {
        // product_zero = ±0 with sign = sign(zero) XOR sign(other).
        // - zero = +0: product_sign = sign(other) (0 XOR s = s)
        // - zero = -0: product_sign = NOT sign(other) (1 XOR s = !s)
        let pos_zero = self.make_zero(precision, false);
        let neg_zero = self.make_zero(precision, true);
        let product_sign = match zero_class {
            FpConstClass::PosZero => other.sign,
            FpConstClass::NegZero => -other.sign,
        };
        let product_zero = self.make_ite_fp(product_sign, &neg_zero, &pos_zero, precision);

        // Compute the IEEE 754 sum product_zero + z under the rounding mode.
        // make_add handles: +0 + z = z for finite nonzero z,
        //                    -0 + +0 = +0 (except RTN which gives -0),
        //                    ±0 + NaN = NaN,
        //                    ±0 + ±inf = ±inf.
        let add_result = self.make_add(&product_zero, z, rm);

        // When the symbolic other factor is NaN or ±inf, the result must be
        // NaN (because 0 * NaN = NaN and 0 * ±inf = NaN).
        let other_nan = self.is_nan(other);
        let other_inf = self.is_infinite(other);
        let other_non_finite = self.make_or(other_nan, other_inf);
        let nan_value = self.make_nan_value(precision);

        // Final: ite(other is non-finite, NaN, add_result).
        self.make_ite_fp(other_non_finite, &nan_value, &add_result, precision)
    }

    /// Fused multiply-add: `(x * y) + z` with a single rounding.
    pub fn make_fma(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        z: &FpDecomposed,
        rm: RoundingMode,
    ) -> FpDecomposed {
        let precision = x.precision;
        let sb = precision.significand_bits() as usize;
        let eb = precision.exponent_bits() as usize;

        let x_nan = self.is_nan(x);
        let y_nan = self.is_nan(y);
        let z_nan = self.is_nan(z);
        let x_inf = self.is_infinite(x);
        let y_inf = self.is_infinite(y);
        let z_inf = self.is_infinite(z);
        let x_zero = self.is_zero(x);
        let y_zero = self.is_zero(y);
        let z_zero = self.is_zero(z);

        let yz_nan = self.make_or(y_nan, z_nan);
        let any_nan = self.make_or(x_nan, yz_nan);
        let x_inf_y_zero = self.make_and(x_inf, y_zero);
        let y_inf_x_zero = self.make_and(y_inf, x_zero);
        let inf_times_zero = self.make_or(x_inf_y_zero, y_inf_x_zero);
        let xy_inf = self.make_or(x_inf, y_inf);
        let xy_sign = self.make_xor(x.sign, y.sign);
        let z_opp_sign = self.make_xor(xy_sign, z.sign);
        let z_inf_opp = self.make_and(z_inf, z_opp_sign);
        let inf_cancel = self.make_and(xy_inf, z_inf_opp);
        let inf_zero_or_cancel = self.make_or(inf_times_zero, inf_cancel);
        let result_nan = self.make_or(any_nan, inf_zero_or_cancel);

        let not_nan = -result_nan;
        let not_inf_times_zero = -inf_times_zero;
        let xy_inf_valid = self.make_and(xy_inf, not_inf_times_zero);
        let any_inf = self.make_or(xy_inf_valid, z_inf);
        let result_inf = self.make_and(any_inf, not_nan);
        let inf_sign = self.make_ite(xy_inf_valid, xy_sign, z.sign);

        let result = self.fresh_decomposed(precision);
        let res_sign = result.sign;

        let inf_and_not_nan = self.make_and(result_inf, not_nan);
        self.add_clause(CnfClause::new(vec![-inf_and_not_nan, -inf_sign, res_sign]));
        self.add_clause(CnfClause::new(vec![-inf_and_not_nan, inf_sign, -res_sign]));

        let special = self.constrain_nan_inf(&result, result_nan, result_inf);
        let xy_zero = self.make_or(x_zero, y_zero);
        let both_zero = self.make_and(xy_zero, z_zero);

        let (_a_sgn, a_sig, a_exp, a_lz) = self.unpack(x, true);
        let (_b_sgn, b_sig, b_exp, b_lz) = self.unpack(y, true);
        let (_c_sgn, c_sig, c_exp, c_lz) = self.unpack(z, true);

        let a_ext = self.zero_extend(&a_sig, sb);
        let b_ext = self.zero_extend(&b_sig, sb);
        let product = self.bv_mul(&a_ext, &b_ext);

        let a_exp_ext = self.sign_extend(&a_exp, 2);
        let b_exp_ext = self.sign_extend(&b_exp, 2);
        let a_lz_ext = self.zero_extend(&a_lz, 2);
        let b_lz_ext = self.zero_extend(&b_lz, 2);
        let a_eff = self.bv_sub(&a_exp_ext, &a_lz_ext);
        let b_eff = self.bv_sub(&b_exp_ext, &b_lz_ext);
        let mul_exp = self.bv_add(&a_eff, &b_eff);

        let c_exp_ext = self.sign_extend(&c_exp, 2);
        let c_lz_ext = self.zero_extend(&c_lz, 2);
        let c_eff_exp = self.bv_sub(&c_exp_ext, &c_lz_ext);

        let zeros3 = self.const_bv(0, 3);
        let mul_sig = Self::bv_concat(&zeros3, &product);
        let zeros_sb2 = self.const_bv(0, sb + 2);
        let c_padded = Self::bv_concat(&zeros_sb2, &c_sig);
        let c_sig_ext = self.zero_extend(&c_padded, 1);

        let ww = 2 * sb + 3;
        debug_assert_eq!(mul_sig.len(), ww);
        debug_assert_eq!(c_sig_ext.len(), ww);

        let c_lt_mul = self.bv_slt(&c_eff_exp, &mul_exp);
        let swap_cond = -c_lt_mul;

        let e_sig = self.make_ite_bits(swap_cond, &c_sig_ext, &mul_sig);
        let e_exp = self.make_ite_bits(swap_cond, &c_eff_exp, &mul_exp);
        let f_sig = self.make_ite_bits(swap_cond, &mul_sig, &c_sig_ext);

        let p_sign = xy_sign;
        let c_sign = z.sign;
        let e_sgn = self.make_ite(swap_cond, c_sign, p_sign);
        let f_sgn = self.make_ite(swap_cond, p_sign, c_sign);

        let f_exp = self.make_ite_bits(swap_cond, &mul_exp, &c_eff_exp);
        let exp_delta = self.bv_sub(&e_exp, &f_exp);
        let cap_val = self.const_bv(ww as u64, eb + 2);
        let delta_lt_cap = self.bv_slt(&exp_delta, &cap_val);
        let capped_delta = self.make_ite_bits(delta_lt_cap, &exp_delta, &cap_val);

        let zeros_sb = self.const_bv(0, sb);
        let f_wide = Self::bv_concat(&zeros_sb, &f_sig);
        let wide_w = 3 * sb + 3;
        let shift_wide = self.zero_extend(&capped_delta, wide_w - (eb + 2));
        let shifted_big = self.bv_lshr(&f_wide, &shift_wide);
        let shifted_f_sig: Vec<CnfLit> = shifted_big[sb..sb + ww].to_vec();
        debug_assert_eq!(shifted_f_sig.len(), ww);

        let alignment_sticky = if sb > 0 {
            self.bv_or_reduce(&shifted_big[..sb])
        } else {
            self.const_false()
        };

        let e_wide = self.zero_extend(&e_sig, 2);
        let f_wide_add = self.zero_extend(&shifted_f_sig, 2);
        let add_w = ww + 2;

        let eq_sgn = self.make_xnor(e_sgn, f_sgn);
        let mut sticky_wide = self.const_bv(0, add_w);
        sticky_wide[0] = alignment_sticky;

        let e_plus_f_raw = self.bv_add(&e_wide, &f_wide_add);
        let sum_lsb_zero = -e_plus_f_raw[0];
        let e_plus_f_adj = self.bv_add(&e_plus_f_raw, &sticky_wide);
        let e_plus_f = self.make_ite_bits(sum_lsb_zero, &e_plus_f_adj, &e_plus_f_raw);

        let e_minus_f_raw = self.bv_sub(&e_wide, &f_wide_add);
        let diff_lsb_zero = -e_minus_f_raw[0];
        let e_minus_f_adj = self.bv_sub(&e_minus_f_raw, &sticky_wide);
        let e_minus_f = self.make_ite_bits(diff_lsb_zero, &e_minus_f_adj, &e_minus_f_raw);
        let sum_result = self.make_ite_bits(eq_sgn, &e_plus_f, &e_minus_f);

        let sign_bv = sum_result[add_w - 1];
        let neg_sum = self.bv_neg(&sum_result);
        let sig_abs = self.make_ite_bits(sign_bv, &neg_sum, &sum_result);

        let ne = -e_sgn;
        let nf = -f_sgn;
        let ns = -sign_bv;
        let t1 = {
            let a = self.make_and(ne, f_sgn);
            self.make_and(a, sign_bv)
        };
        let t2 = {
            let a = self.make_and(e_sgn, nf);
            self.make_and(a, ns)
        };
        let t3 = self.make_and(e_sgn, f_sgn);
        let t12 = self.make_or(t1, t2);
        let res_sign_normal = self.make_or(t12, t3);

        let extra_bits = [sig_abs[add_w - 2], sig_abs[add_w - 1]];
        let extra_zero_0 = -extra_bits[0];
        let extra_zero_1 = -extra_bits[1];
        let extra_is_zero = self.make_and(extra_zero_0, extra_zero_1);

        let one_exp = self.const_bv(1, eb + 2);
        let e_exp_plus1 = self.bv_add(&e_exp, &one_exp);
        let res_exp_pre = self.make_ite_bits(extra_is_zero, &e_exp, &e_exp_plus1);

        let sig_lz = self.bv_leading_zeros(&sig_abs, eb + 2);
        let two_exp = self.const_bv(2, eb + 2);
        let sig_lz_adj = self.bv_sub(&sig_lz, &two_exp);
        let bias = u64::from(precision.bias());
        let e_min_val = 1i64 - bias as i64;
        let e_min_bv = self.const_bv(e_min_val as u64, eb + 2);
        let max_exp_delta_renorm = self.bv_sub(&res_exp_pre, &e_min_bv);
        let zero_exp = self.const_bv(0, eb + 2);
        let lz_lt_max = self.bv_slt(&sig_lz_adj, &max_exp_delta_renorm);
        let min_lz = self.make_ite_bits(lz_lt_max, &sig_lz_adj, &max_exp_delta_renorm);
        let min_neg = min_lz[min_lz.len() - 1];
        let renorm_delta = self.make_ite_bits(min_neg, &zero_exp, &min_lz);

        let common_exp = self.bv_sub(&res_exp_pre, &renorm_delta);
        let renorm_shift = self.zero_extend(&renorm_delta, add_w - (eb + 2));
        let sig_renorm = self.bv_shl(&sig_abs, &renorm_shift);

        let no_ovf_start = sb.saturating_sub(1);
        let ovf_start = sb;

        let no_ovf_main: Vec<CnfLit> = sig_renorm[no_ovf_start..add_w].to_vec();
        let no_ovf_sticky = if no_ovf_start > 0 {
            self.bv_or_reduce(&sig_renorm[..no_ovf_start])
        } else {
            self.const_false()
        };
        let mut no_ovf_sig = no_ovf_main[..sb + 4].to_vec();
        let no_ovf_bit0 = self.make_or(no_ovf_sig[0], no_ovf_sticky);
        no_ovf_sig[0] = no_ovf_bit0;

        let ovf_main: Vec<CnfLit> = sig_renorm[ovf_start..add_w].to_vec();
        let ovf_sticky = self.bv_or_reduce(&sig_renorm[..ovf_start]);
        let mut ovf_sig = ovf_main[..sb + 4].to_vec();
        let ovf_bit0 = self.make_or(ovf_sig[0], ovf_sticky);
        ovf_sig[0] = ovf_bit0;

        let fma_sig = self.make_ite_bits(extra_is_zero, &no_ovf_sig, &ovf_sig);
        debug_assert_eq!(fma_sig.len(), sb + 4);

        let normal_result = self.fp_round(precision, rm, res_sign_normal, &fma_sig, &common_exp);
        let special_or_both_zero = self.make_or(special, both_zero);
        let xy_zero_z_not = self.make_and(xy_zero, -z_zero);
        let special_or_trivial = self.make_or(special_or_both_zero, xy_zero_z_not);
        let not_special = -special_or_trivial;

        // IEEE 754-2019 §6.3: when the (infinitely precise) result of the
        // fused multiply-add is *exactly* zero through cancellation of opposite
        // signs, the sign is +0 in every rounding mode except roundTowardNegative
        // (which yields -0) — regardless of the operand signs. The general path
        // derives `res_sign_normal` from the larger-magnitude addend, which is
        // wrong for an exact cancellation. Detect the exact-zero sum (aligned
        // magnitude all-zero AND no bits dropped during alignment, so the true
        // sum — not merely a rounded-down underflow — is zero) and override the
        // result to the correctly-signed zero. We deliberately do NOT trigger on
        // a nonzero `sig_abs` that merely rounds/underflows to zero: that result
        // keeps the computed sign and rounding behaviour (e.g. RTP rounding a
        // tiny positive up off zero), which the normal path already handles.
        let sig_abs_is_zero = self.make_all_zero(&sig_abs);
        let exact_zero_sum = self.make_and(sig_abs_is_zero, -alignment_sticky);
        let cancel_zero = self.make_and(not_special, exact_zero_sum);
        let cancel_zero_result = self.make_zero(precision, rm == RoundingMode::RTN);
        self.constrain_fp_when(cancel_zero, &result, &cancel_zero_result);

        let normal_applies = self.make_and(not_special, -cancel_zero);
        self.constrain_fp_when(normal_applies, &result, &normal_result);

        let xy_zero_z_not_nan = self.make_and(xy_zero_z_not, not_nan);
        self.constrain_fp_when(xy_zero_z_not_nan, &result, z);

        let both_zero_not_nan = self.make_and(both_zero, not_nan);
        let both_neg = self.make_and(xy_sign, z.sign);
        let zero_is_neg = match rm {
            RoundingMode::RTN => self.make_or(xy_sign, z.sign),
            _ => both_neg,
        };
        for &exp_bit in &result.exponent {
            self.add_clause(CnfClause::new(vec![-both_zero_not_nan, -exp_bit]));
        }
        for &sig_bit in &result.significand {
            self.add_clause(CnfClause::new(vec![-both_zero_not_nan, -sig_bit]));
        }
        self.add_clause(CnfClause::new(vec![
            -both_zero_not_nan,
            -zero_is_neg,
            res_sign,
        ]));
        self.add_clause(CnfClause::new(vec![
            -both_zero_not_nan,
            zero_is_neg,
            -res_sign,
        ]));

        result
    }
}
