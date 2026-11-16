// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original rounding phases 6–13, without new gates or rounding decisions.

use super::round::{Format, Normalized, PostRound};
use crate::construction::control::BuildControl;
use crate::{FpDecomposed, FpPrecision, FpSolver, RmOperand, RoundingMode};
use ay_core::CnfLit;

impl FpSolver<'_> {
    pub(super) fn conversion_round_post<C: BuildControl>(
        &mut self,
        format: Format,
        rm: RmOperand,
        sgn: CnfLit,
        normalized: Normalized,
        control: &mut C,
    ) -> Result<PostRound, C::Error> {
        let Format { eb, sb, bias, w } = format;
        let result = (|| -> Result<PostRound, C::Error> {
            let Normalized {
                ovf1_exp,
                norm_sig,
                norm_exp,
            } = normalized;
            self.conversion_poll(control)?;
            // Phase 6: Extract last/round/sticky from sbits+2 sig
            let final_sticky = norm_sig[0];
            let final_round = norm_sig[1];
            let final_last = norm_sig[2];
            let kept_sig: Vec<CnfLit> = norm_sig[2..sb + 2].to_vec(); // sb bits
            debug_assert_eq!(kept_sig.len(), sb);

            self.conversion_poll(control)?;
            // Phase 7: Rounding increment
            let inc = self.make_rounding_decision(rm, sgn, final_last, final_round, final_sticky);

            // Add increment to significand (extend by 1 for carry)
            let inc_bv = {
                let mut v = self.const_bv(0, sb + 1);
                v[0] = inc;
                v
            };
            let sig_ext_for_round = self.zero_extend(&kept_sig, 1); // sb+1 bits
            let rounded_sig = self.bv_add(&sig_ext_for_round, &inc_bv);
            debug_assert_eq!(rounded_sig.len(), sb + 1);

            self.conversion_poll(control)?;
            // Phase 8: Post-normalization (rounding carry)
            let sig_ovf = rounded_sig[sb]; // carry out from rounding

            // If overflow: right shift by 1 (take bits [sb:1]), else take bits [sb-1:0]
            let sig_after_round_ovf: Vec<CnfLit> = rounded_sig[1..=sb].to_vec(); // shifted right
            let sig_after_round_normal: Vec<CnfLit> = rounded_sig[0..sb].to_vec();
            let post_sig =
                self.make_ite_bits(sig_ovf, &sig_after_round_ovf, &sig_after_round_normal);
            debug_assert_eq!(post_sig.len(), sb);

            // Increment exponent if sig overflowed
            let one_exp = self.const_bv(1, w);
            let exp_plus_one = self.bv_add(&norm_exp, &one_exp);
            let post_exp = self.make_ite_bits(sig_ovf, &exp_plus_one, &norm_exp);

            self.conversion_poll(control)?;
            // Phase 9: Bias the exponent
            let bias_bv = self.const_bv(bias, w);
            let biased_exp_full = self.bv_add(&post_exp, &bias_bv);
            let biased_exp: Vec<CnfLit> = biased_exp_full[..eb].to_vec(); // truncate to eb bits

            Ok(PostRound {
                ovf1_exp,
                sig_ovf,
                post_sig,
                biased_exp,
            })
        })()?;
        self.conversion_poll(control)?;
        Ok(result)
    }

    pub(super) fn conversion_round_finish<C: BuildControl>(
        &mut self,
        precision: FpPrecision,
        format: Format,
        rm: RmOperand,
        sgn: CnfLit,
        post: PostRound,
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        let Format { eb, sb, .. } = format;
        let result = (|| -> Result<FpDecomposed, C::Error> {
            let PostRound {
                ovf1_exp,
                sig_ovf,
                post_sig,
                biased_exp,
            } = post;
            self.conversion_poll(control)?;
            // Phase 10: Overflow detection after rounding (OVF2)
            let all_ones_exp = self.const_bv((1u64 << eb) - 1, eb);
            let exp_is_all_ones = self.make_bits_equal(&biased_exp, &all_ones_exp);
            let ovf2 = self.make_and(sig_ovf, exp_is_all_ones);
            let ovf = self.make_or(ovf1_exp, ovf2);

            let (ovf_exp, ovf_sig) = self.conversion_round_overflow(format, rm, sgn, control)?;
            self.conversion_poll(control)?;
            // Phase 12: Subnormal detection
            // If hidden bit (post_sig[sb-1]) is 0, result is denormal -> biased exp = 0
            let hidden_bit = post_sig[sb - 1];
            let is_denormal = -hidden_bit;
            let bot_exp = self.const_bv(0, eb);
            let normal_or_denormal_exp = self.make_ite_bits(is_denormal, &bot_exp, &biased_exp);

            // Strip hidden bit for stored significand
            let stored_sig: Vec<CnfLit> = post_sig[..sb - 1].to_vec(); // sb-1 bits

            self.conversion_poll(control)?;
            // Phase 13: Final MUX for overflow
            let result_exp = self.make_ite_bits(ovf, &ovf_exp, &normal_or_denormal_exp);
            let result_sig = self.make_ite_bits(ovf, &ovf_sig, &stored_sig);

            Ok(FpDecomposed {
                sign: sgn,
                exponent: result_exp,
                significand: result_sig,
                precision,
            })
        })()?;
        self.conversion_poll(control)?;
        Ok(result)
    }

    fn conversion_round_overflow<C: BuildControl>(
        &mut self,
        format: Format,
        rm: RmOperand,
        sgn: CnfLit,
        control: &mut C,
    ) -> Result<(Vec<CnfLit>, Vec<CnfLit>), C::Error> {
        self.conversion_poll(control)?;
        let Format { eb, sb, .. } = format;
        let result = {
            // Phase 11: Overflow result based on rounding mode
            // For ties-to-even and ties-to-away: overflow -> infinity
            // For toward-zero: overflow -> max finite
            // For toward-pos: positive overflow -> inf, negative overflow -> max finite
            // For toward-neg: positive overflow -> max finite, negative overflow -> inf
            let inf_exp = self.const_bv((1u64 << eb) - 1, eb);
            let max_exp = self.const_bv((1u64 << eb) - 2, eb); // all ones except LSB
            let inf_sig: Vec<CnfLit> = (0..sb - 1).map(|_| self.const_false()).collect();
            let max_sig: Vec<CnfLit> = (0..sb - 1).map(|_| self.const_true()).collect();

            let (ovf_exp, ovf_sig) = match rm {
                RmOperand::Literal(RoundingMode::RNE | RoundingMode::RNA) => {
                    // Always infinity on overflow
                    (inf_exp, inf_sig)
                }
                RmOperand::Literal(RoundingMode::RTZ) => {
                    // Always max finite on overflow
                    (max_exp, max_sig)
                }
                RmOperand::Literal(RoundingMode::RTP) => {
                    // Positive -> inf, Negative -> max finite
                    let exp_sel = self.make_ite_bits(sgn, &max_exp, &inf_exp);
                    let sig_sel = self.make_ite_bits(sgn, &max_sig, &inf_sig);
                    (exp_sel, sig_sel)
                }
                RmOperand::Literal(RoundingMode::RTN) => {
                    // Positive -> max finite, Negative -> inf
                    let exp_sel = self.make_ite_bits(sgn, &inf_exp, &max_exp);
                    let sig_sel = self.make_ite_bits(sgn, &inf_sig, &max_sig);
                    (exp_sel, sig_sel)
                }
                RmOperand::Symbolic(_) => {
                    // Infinity for the nearest modes and toward the sign's own
                    // infinity, the largest finite value otherwise.
                    let to_inf = self.rm_select(rm, |solver, mode| match mode {
                        RoundingMode::RNE | RoundingMode::RNA => solver.const_true(),
                        RoundingMode::RTZ => solver.const_false(),
                        RoundingMode::RTP => -sgn,
                        RoundingMode::RTN => sgn,
                    });
                    let exp_sel = self.make_ite_bits(to_inf, &inf_exp, &max_exp);
                    let sig_sel = self.make_ite_bits(to_inf, &inf_sig, &max_sig);
                    (exp_sel, sig_sel)
                }
            };

            (ovf_exp, ovf_sig)
        };
        self.conversion_poll(control)?;
        Ok(result)
    }
}
