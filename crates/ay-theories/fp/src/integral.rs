// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Round-to-integral encoding.

use ay_core::CnfLit;

use super::gates::neg_lit;
use super::{FpDecomposed, FpPrecision, FpSolver, RmOperand, RoundingMode};

struct RoundToIntegralMainInput<'a> {
    x: &'a FpDecomposed,
    a_sig: &'a [CnfLit],
    eff_exp: &'a [CnfLit],
    precision: FpPrecision,
    rm: RmOperand,
}

struct RoundToIntegralVariants<'a> {
    original: &'a FpDecomposed,
    small: &'a FpDecomposed,
    integral: &'a FpDecomposed,
}

impl FpSolver<'_> {
    /// Round to integral value in FP format.
    pub fn make_round_to_integral(
        &mut self,
        x: &FpDecomposed,
        rm: impl Into<RmOperand>,
    ) -> FpDecomposed {
        let rm = rm.into();
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
        // Signed, `eb + 2` bits (z3's) unless the normalised exponent or `sb`
        // needs more (`round_to_integral_exponent_width`).
        let eb2 = Self::round_to_integral_exponent_width(eb, sb);
        let a_exp_ext = self.sign_extend(&a_exp, eb2 - eb);
        let a_lz_ext = self.zero_extend(&a_lz, eb2 - a_lz.len());
        let eff_exp = self.bv_sub(&a_exp_ext, &a_lz_ext);
        // SMT-LIB FP sorts have `eb, sb >= 2` (crates/ay-dpll/src/api/
        // model_parse/typed/sorts.rs:16), so the saturating form equals
        // `sb - 1` for every real caller.
        let sb_minus_1 = self.const_bv(sb.saturating_sub(1) as u64, eb2);
        let already_integral = neg_lit(self.bv_slt(&eff_exp, &sb_minus_1));
        let zero_eb2 = self.const_bv(0, eb2);
        let exp_negative = self.bv_slt(&eff_exp, &zero_eb2);
        (a_sig, eff_exp, already_integral, exp_negative)
    }

    fn round_to_integral_shift(&mut self, eff_exp: &[CnfLit], sb: usize) -> Vec<CnfLit> {
        // `eff_exp`'s width, `round_to_integral_exponent_width`.
        let eb2 = eff_exp.len();
        let sb_m1_bv = self.const_bv(sb.saturating_sub(1) as u64, eb2);
        let shift_raw = self.bv_sub(&sb_m1_bv, eff_exp);
        // The sign bit is the MSB of the `eb2`-bit difference; a zero-width
        // value would be 0, which is not negative.
        let shift_neg = match shift_raw.last() {
            Some(&msb) => msb,
            None => self.const_false(),
        };
        let sb_bv_ext = self.const_bv(sb as u64, eb2);
        let shift_too_big = self.bv_slt(&sb_bv_ext, &shift_raw);
        let zero_shift = self.const_bv(0, eb2);
        let capped = self.make_ite_bits(shift_neg, &zero_shift, &shift_raw);
        let capped = self.make_ite_bits(shift_too_big, &sb_bv_ext, &capped);
        // `0 <= capped <= sb < 2^sb`: resizing is exact.
        self.resize_unsigned(&capped, sb)
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
        let shift_sb = self.round_to_integral_shift(eff_exp, sb);
        let all_ones = self.const_bv_signed(-1, sb);
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

        // `rounded_sig_ext` is `sb + 1` bits wide: bit `sb` is the carry out
        // of the significand. A sum without that bit cannot have overflowed.
        let mut rounded_sig = rounded_sig_ext;
        let sig_ovf = match rounded_sig.get(sb) {
            Some(&carry) => carry,
            None => self.const_false(),
        };
        rounded_sig.truncate(sb);
        let mut sig_after_ovf = vec![self.const_false(); sb];
        let one = self.const_true();
        if let Some(msb) = sig_after_ovf.last_mut() {
            *msb = one;
        }
        let mut final_sig = self.make_ite_bits(sig_ovf, &sig_after_ovf, &rounded_sig);
        // Drop the hidden bit: keep the low `sb - 1` of the `sb` result bits.
        final_sig.truncate(sb.saturating_sub(1));

        let one_eb = self.const_bv(1, eb);
        let exp_plus_one = self.bv_add(&x.exponent, &one_eb);
        let final_exp = self.make_ite_bits(sig_ovf, &exp_plus_one, &x.exponent);
        FpDecomposed {
            sign: x.sign,
            exponent: final_exp,
            significand: final_sig,
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
        let not_special = neg_lit(special);
        let not_already = neg_lit(already_integral);
        let use_already = self.make_and(not_special, already_integral);
        let small_inner = self.make_and(not_already, exp_negative);
        let use_small = self.make_and(not_special, small_inner);
        let normal_inner = self.make_and(not_already, neg_lit(exp_negative));
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
        rm: RmOperand,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let sb = precision.significand_bits() as usize;
        let eb = precision.exponent_bits() as usize;
        let bias = precision.bias();

        // `a_sig` is `sb` bits wide: the significand is one half exactly when
        // its MSB is set and every lower bit is clear. With no MSB it is not.
        let halves = sb
            .checked_sub(1)
            .and_then(|top| Some((*a_sig.get(top)?, a_sig.get(..top)?)));
        let sig_is_half = match halves {
            Some((msb, lower)) => {
                let lower_zero = self.make_all_zero(lower);
                self.make_and(msb, lower_zero)
            }
            None => self.const_false(),
        };
        let minus_one_eb2 = self.const_bv_signed(-1, eff_exp.len());
        let exp_is_minus1 = self.make_bv_eq(eff_exp, &minus_one_eb2);
        let tie = self.make_and(sig_is_half, exp_is_minus1);

        let one_eb2 = self.const_bv(1, eff_exp.len());
        let minus_two_eb2 = self.bv_sub(&minus_one_eb2, &one_eb2);
        let exp_le_minus2 = self.bv_sle(eff_exp, &minus_two_eb2);

        let round_to_one = self.rm_select(rm, |solver, mode| match mode {
            RoundingMode::RNE => {
                let not_tie = neg_lit(tie);
                let not_small = neg_lit(exp_le_minus2);
                solver.make_and(not_tie, not_small)
            }
            RoundingMode::RNA => neg_lit(exp_le_minus2),
            RoundingMode::RTP => neg_lit(x.sign),
            RoundingMode::RTN => x.sign,
            RoundingMode::RTZ => solver.const_false(),
        });

        let one_exp = self.const_bv(bias, eb);
        // `sb - 1` false bits, as `const_bv(0, ..)` builds them (`sb >= 2`).
        let zero_sig = self.const_bv(0, sb.saturating_sub(1));
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
