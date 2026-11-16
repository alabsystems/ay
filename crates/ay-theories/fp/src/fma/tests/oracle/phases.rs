// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

impl FpSolver<'_> {
    pub(super) fn fma_align_legacy(
        &mut self,
        precision: FpPrecision,
        product: Product,
        xy_sign: CnfLit,
        z_sign: CnfLit,
    ) -> Aligned {
        let sb = precision.significand_bits() as usize;
        let eb = precision.exponent_bits() as usize;
        let ew = Self::fma_exponent_width(eb, sb);
        let ww = 2 * sb + 3;
        {
            let Product {
                mul_sig,
                c_sig_ext,
                mul_exp,
                c_eff_exp,
            } = product;
            let c_lt_mul = self.bv_slt(&c_eff_exp, &mul_exp);
            let swap_cond = -c_lt_mul;

            let e_sig = self.make_ite_bits(swap_cond, &c_sig_ext, &mul_sig);
            let e_exp = self.make_ite_bits(swap_cond, &c_eff_exp, &mul_exp);
            let f_sig = self.make_ite_bits(swap_cond, &mul_sig, &c_sig_ext);

            let p_sign = xy_sign;
            let c_sign = z_sign;
            let e_sgn = self.make_ite(swap_cond, c_sign, p_sign);
            let f_sgn = self.make_ite(swap_cond, p_sign, c_sign);

            let f_exp = self.make_ite_bits(swap_cond, &mul_exp, &c_eff_exp);
            let exp_delta = self.bv_sub(&e_exp, &f_exp);
            let cap_val = self.const_bv(ww as u64, ew);
            let delta_lt_cap = self.bv_slt(&exp_delta, &cap_val);
            let capped_delta = self.make_ite_bits(delta_lt_cap, &exp_delta, &cap_val);

            let zeros_sb = self.const_bv(0, sb);
            let f_wide = Self::bv_concat(&zeros_sb, &f_sig);
            let wide_w = 3 * sb + 3;
            // `0 <= capped_delta <= ww < 2^wide_w`: resizing is exact.
            let shift_wide = self.resize_unsigned(&capped_delta, wide_w);
            let shifted_big = self.bv_lshr(&f_wide, &shift_wide);
            let shifted_f_sig: Vec<CnfLit> = shifted_big[sb..sb + ww].to_vec();
            debug_assert_eq!(shifted_f_sig.len(), ww);

            let alignment_sticky = if sb > 0 {
                self.bv_or_reduce(&shifted_big[..sb])
            } else {
                self.const_false()
            };

            Aligned {
                e_sig,
                shifted_f_sig,
                e_exp,
                e_sgn,
                f_sgn,
                alignment_sticky,
            }
        }
    }

    pub(super) fn fma_magnitude_legacy(
        &mut self,
        precision: FpPrecision,
        aligned: Aligned,
    ) -> Magnitude {
        let sb = precision.significand_bits() as usize;
        let ww = 2 * sb + 3;
        {
            let Aligned {
                e_sig,
                shifted_f_sig,
                e_exp,
                e_sgn,
                f_sgn,
                alignment_sticky,
            } = aligned;
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

            Magnitude {
                sig_abs,
                e_exp,
                res_sign_normal,
                extra_is_zero,
                alignment_sticky,
            }
        }
    }

    pub(super) fn fma_normalize_legacy(
        &mut self,
        precision: FpPrecision,
        magnitude: Magnitude,
        rm: RmOperand,
    ) -> Normalized {
        let sb = precision.significand_bits() as usize;
        let eb = precision.exponent_bits() as usize;
        let ew = Self::fma_exponent_width(eb, sb);
        let add_w = 2 * sb + 5;
        let result = {
            let Magnitude {
                sig_abs,
                e_exp,
                res_sign_normal,
                extra_is_zero,
                alignment_sticky,
            } = magnitude;
            let one_exp = self.const_bv(1, ew);
            let e_exp_plus1 = self.bv_add(&e_exp, &one_exp);
            let res_exp_pre = self.make_ite_bits(extra_is_zero, &e_exp, &e_exp_plus1);

            let sig_lz = self.bv_leading_zeros(&sig_abs, ew);
            let two_exp = self.const_bv(2, ew);
            let sig_lz_adj = self.bv_sub(&sig_lz, &two_exp);
            let bias = precision.bias();
            let e_min_val = 1i64 - bias as i64;
            let e_min_bv = self.const_bv(e_min_val as u64, ew);
            let max_exp_delta_renorm = self.bv_sub(&res_exp_pre, &e_min_bv);
            let zero_exp = self.const_bv(0, ew);
            let lz_lt_max = self.bv_slt(&sig_lz_adj, &max_exp_delta_renorm);
            let min_lz = self.make_ite_bits(lz_lt_max, &sig_lz_adj, &max_exp_delta_renorm);
            let min_neg = min_lz[min_lz.len() - 1];
            let renorm_delta = self.make_ite_bits(min_neg, &zero_exp, &min_lz);

            let common_exp = self.bv_sub(&res_exp_pre, &renorm_delta);
            // `0 <= renorm_delta <= sig_lz <= add_w`: resizing is exact.
            let renorm_shift = self.resize_unsigned(&renorm_delta, add_w);
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

            let normal_result =
                self.fp_round(precision, rm, res_sign_normal, &fma_sig, &common_exp);
            Normalized {
                normal_result,
                sig_abs,
                alignment_sticky,
            }
        };
        // Full normalization/rounding words have been discarded, not renewed.
        result
    }
}
