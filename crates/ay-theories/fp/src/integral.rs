// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Round-to-integral encoding.

use ay_core::CnfLit;

use super::{FpDecomposed, FpPrecision, FpSolver, RoundingMode};

struct RoundToIntegralMainInput<'a> {
    x: &'a FpDecomposed,
    a_sig: &'a [CnfLit],
    eff_exp: &'a [CnfLit],
    precision: FpPrecision,
    rm: RoundingMode,
}

struct RoundToIntegralVariants<'a> {
    original: &'a FpDecomposed,
    small: &'a FpDecomposed,
    integral: &'a FpDecomposed,
}

impl FpSolver<'_> {
    /// Round to integral value in FP format.
    pub fn make_round_to_integral(&mut self, x: &FpDecomposed, rm: RoundingMode) -> FpDecomposed {
        let precision = x.precision;
        let sb = precision.significand_bits() as usize;
        let eb = precision.exponent_bits() as usize;
        let result = self.fresh_decomposed(precision);
        let special = self.round_to_integral_special_guard(x, &result);
        let (a_sig, eff_exp, already_integral, exp_negative) =
            self.round_to_integral_classify(x, sb, eb);
        let main_input = RoundToIntegralMainInput {
            x,
            a_sig: &a_sig,
            eff_exp: &eff_exp,
            precision,
            rm,
        };
        let integral_result = self.round_to_integral_main_result(&main_input);
        let small_result = self.round_integral_small_case(x, &a_sig, &eff_exp, rm, precision);
        let variants = RoundToIntegralVariants {
            original: x,
            small: &small_result,
            integral: &integral_result,
        };
        self.constrain_round_to_integral_paths(
            special,
            already_integral,
            exp_negative,
            &result,
            &variants,
        );
        result
    }

    fn round_to_integral_special_guard(
        &mut self,
        x: &FpDecomposed,
        result: &FpDecomposed,
    ) -> CnfLit {
        let x_nan = self.is_nan(x);
        let x_inf = self.is_infinite(x);
        let x_zero = self.is_zero(x);
        let inf_or_zero = self.make_or(x_inf, x_zero);
        let special = self.make_or(x_nan, inf_or_zero);
        self.constrain_fp_when(special, result, x);
        special
    }

    fn round_to_integral_classify(
        &mut self,
        x: &FpDecomposed,
        sb: usize,
        eb: usize,
    ) -> (Vec<CnfLit>, Vec<CnfLit>, CnfLit, CnfLit) {
        let (_a_sgn, a_sig, a_exp, a_lz) = self.unpack(x, true);
        let a_exp_ext = self.sign_extend(&a_exp, 2);
        let a_lz_ext = self.zero_extend(&a_lz, 2);
        let eff_exp = self.bv_sub(&a_exp_ext, &a_lz_ext);
        let sb_minus_1 = self.const_bv((sb - 1) as u64, eb + 2);
        let already_integral = -self.bv_slt(&eff_exp, &sb_minus_1);
        let zero_eb2 = self.const_bv(0, eb + 2);
        let exp_negative = self.bv_slt(&eff_exp, &zero_eb2);
        (a_sig, eff_exp, already_integral, exp_negative)
    }

    fn round_to_integral_shift(&mut self, eff_exp: &[CnfLit], sb: usize, eb: usize) -> Vec<CnfLit> {
        let sb_m1_bv = self.const_bv((sb - 1) as u64, eb + 2);
        let shift_raw = self.bv_sub(&sb_m1_bv, eff_exp);
        let shift_neg = shift_raw[shift_raw.len() - 1];
        let sb_bv_ext = self.const_bv(sb as u64, eb + 2);
        let shift_too_big = self.bv_slt(&sb_bv_ext, &shift_raw);
        let zero_shift = self.const_bv(0, eb + 2);
        let capped = self.make_ite_bits(shift_neg, &zero_shift, &shift_raw);
        let capped = self.make_ite_bits(shift_too_big, &sb_bv_ext, &capped);
        if eb + 2 >= sb {
            capped[..sb].to_vec()
        } else {
            self.zero_extend(&capped, sb - (eb + 2))
        }
    }

    fn mask_bits(&mut self, bits: &[CnfLit], mask: &[CnfLit]) -> Vec<CnfLit> {
        bits.iter()
            .zip(mask.iter())
            .map(|(&bit, &mask_bit)| self.make_and(bit, mask_bit))
            .collect()
    }

    fn round_to_integral_main_result(
        &mut self,
        input: &RoundToIntegralMainInput<'_>,
    ) -> FpDecomposed {
        let x = input.x;
        let a_sig = input.a_sig;
        let eff_exp = input.eff_exp;
        let precision = input.precision;
        let rm = input.rm;
        let sb = precision.significand_bits() as usize;
        let eb = precision.exponent_bits() as usize;
        let shift_sb = self.round_to_integral_shift(eff_exp, sb, eb);
        let all_ones = self.const_bv(u64::MAX, sb);
        let mask = self.bv_shl(&all_ones, &shift_sb);
        let trunc_sig = self.mask_bits(a_sig, &mask);

        let inc_one = self.const_bv(1, sb);
        let inc = self.bv_shl(&inc_one, &shift_sb);
        let last_bits = self.mask_bits(a_sig, &inc);
        let last = self.bv_or_reduce(&last_bits);

        let one_bv = self.const_bv(1, sb);
        let round_mask = self.bv_lshr(&inc, &one_bv);
        let round_bits = self.mask_bits(a_sig, &round_mask);
        let round = self.bv_or_reduce(&round_bits);

        let sticky_mask = self.bv_sub(&round_mask, &one_bv);
        let sticky_bits = self.mask_bits(a_sig, &sticky_mask);
        let sticky = self.bv_or_reduce(&sticky_bits);
        let round_inc = self.make_rounding_decision(rm, x.sign, last, round, sticky);

        let inc_masked: Vec<CnfLit> = inc
            .iter()
            .map(|&bit| self.make_and(bit, round_inc))
            .collect();
        let trunc_ext = self.zero_extend(&trunc_sig, 1);
        let inc_ext = self.zero_extend(&inc_masked, 1);
        let rounded_sig_ext = self.bv_add(&trunc_ext, &inc_ext);

        let sig_ovf = rounded_sig_ext[sb];
        let rounded_sig = rounded_sig_ext[..sb].to_vec();
        let mut sig_after_ovf = vec![self.const_false(); sb];
        sig_after_ovf[sb - 1] = self.const_true();
        let final_sig = self.make_ite_bits(sig_ovf, &sig_after_ovf, &rounded_sig);

        let one_eb = self.const_bv(1, eb);
        let exp_plus_one = self.bv_add(&x.exponent, &one_eb);
        let final_exp = self.make_ite_bits(sig_ovf, &exp_plus_one, &x.exponent);
        FpDecomposed {
            sign: x.sign,
            exponent: final_exp,
            significand: final_sig[..sb - 1].to_vec(),
            precision,
        }
    }

    fn constrain_round_to_integral_paths(
        &mut self,
        special: CnfLit,
        already_integral: CnfLit,
        exp_negative: CnfLit,
        result: &FpDecomposed,
        variants: &RoundToIntegralVariants<'_>,
    ) {
        let not_special = -special;
        let use_already = self.make_and(not_special, already_integral);
        let small_inner = self.make_and(-already_integral, exp_negative);
        let use_small = self.make_and(not_special, small_inner);
        let normal_inner = self.make_and(-already_integral, -exp_negative);
        let use_normal = self.make_and(not_special, normal_inner);
        self.constrain_fp_when(use_already, result, variants.original);
        self.constrain_fp_when(use_small, result, variants.small);
        self.constrain_fp_when(use_normal, result, variants.integral);
    }

    /// Helper for `make_round_to_integral`: handles `|x| < 1`.
    fn round_integral_small_case(
        &mut self,
        x: &FpDecomposed,
        a_sig: &[CnfLit],
        eff_exp: &[CnfLit],
        rm: RoundingMode,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let sb = precision.significand_bits() as usize;
        let eb = precision.exponent_bits() as usize;
        let bias = precision.bias();

        let sig_is_half = {
            let lower_zero = self.make_all_zero(&a_sig[..sb - 1]);
            self.make_and(a_sig[sb - 1], lower_zero)
        };
        let minus_one_eb2 = self.const_bv(u64::MAX, eb + 2);
        let exp_is_minus1 = self.make_bv_eq(eff_exp, &minus_one_eb2);
        let tie = self.make_and(sig_is_half, exp_is_minus1);

        let one_eb2 = self.const_bv(1, eb + 2);
        let minus_two_eb2 = self.bv_sub(&minus_one_eb2, &one_eb2);
        let exp_le_minus2 = self.bv_sle(eff_exp, &minus_two_eb2);

        let round_to_one = match rm {
            RoundingMode::RNE => {
                let not_tie = -tie;
                let not_small = -exp_le_minus2;
                self.make_and(not_tie, not_small)
            }
            RoundingMode::RNA => -exp_le_minus2,
            RoundingMode::RTP => -x.sign,
            RoundingMode::RTN => x.sign,
            RoundingMode::RTZ => self.const_false(),
        };

        let one_exp = self.const_bv(u64::from(bias), eb);
        let zero_sig: Vec<CnfLit> = (0..sb - 1).map(|_| self.const_false()).collect();
        let zero_exp = self.const_bv(0, eb);
        let small_exp = self.make_ite_bits(round_to_one, &one_exp, &zero_exp);
        FpDecomposed {
            sign: x.sign,
            exponent: small_exp,
            significand: zero_sig,
            precision,
        }
    }
}
