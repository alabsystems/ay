// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! IEEE 754 rounding pipeline: unpack, rounding decision, and fp_round.
//!
//! These functions form the core IEEE 754 rounding algorithm, following
//! Z3's fpa2bv_converter approach. They call into BV circuit primitives
//! but are not called by them.

use ay_core::{CnfClause, CnfLit};

use super::{FpDecomposed, FpPrecision, FpSolver, RoundingMode};

impl FpSolver<'_> {
    // ========== IEEE 754 unpack ==========

    /// Unpack an FpDecomposed value into (sign, significand_with_hidden, unbiased_exp, leading_zeros).
    ///
    /// Following Z3's fpa2bv_converter::unpack:
    /// - `sig` has `sbits` bits (hidden bit prepended)
    /// - `exp` has `ebits` bits (unbiased, two's complement)
    /// - `lz` has `ebits` bits (leading zero count, only nonzero for subnormals when normalize=true)
    pub(crate) fn unpack(
        &mut self,
        fp: &FpDecomposed,
        normalize: bool,
    ) -> (CnfLit, Vec<CnfLit>, Vec<CnfLit>, Vec<CnfLit>) {
        let eb = fp.precision.exponent_bits() as usize;
        let sb = fp.precision.significand_bits() as usize;
        let bias = fp.precision.bias();

        let sgn = fp.sign;

        // Detect normal vs subnormal
        let exp_is_zero = self.make_all_zero(&fp.exponent);
        let is_normal_val = -exp_is_zero; // exponent nonzero (includes inf/NaN, but caller handles)

        // Normal case: sig = concat(hidden_1, mantissa), exp = unbias(biased_exp)
        let hidden_one = self.const_true();
        let normal_sig = Self::bv_concat(&fp.significand, &[hidden_one]); // sb bits: [mantissa, 1]
                                                                          // Note: bit layout is [bit0=lsb...bit_{sb-2}=msb_mantissa, bit_{sb-1}=hidden_bit]

        // Unbias: unbiased = biased - bias
        // bias_bv is eb bits wide
        let bias_bv = self.const_bv(u64::from(bias), eb);
        let normal_exp = self.bv_sub(&fp.exponent, &bias_bv);

        // Denormal case: sig = concat(hidden_0, mantissa), exp = 1 - bias
        let hidden_zero = self.const_false();
        let denormal_sig = Self::bv_concat(&fp.significand, &[hidden_zero]); // sb bits

        // Denormal exponent = 1 - bias (same exponent as smallest normal)
        let one_bv = self.const_bv(1, eb);
        let denormal_exp = self.bv_sub(&one_bv, &bias_bv);

        // Leading zeros (only for subnormals when normalizing)
        let zero_lz = self.const_bv(0, eb);

        let (final_sig, final_exp, final_lz) = if normalize {
            // Count leading zeros in denormal significand
            let lz_d = self.bv_leading_zeros(&denormal_sig, eb);

            // sig_is_zero: significand is all zero (denormal zero)
            let sig_is_zero = self.make_all_zero(&fp.significand);

            // lz = is_normal ? 0 : (sig_is_zero ? 0 : lz_d)
            let lz_or_zero = self.make_ite_bits(-sig_is_zero, &lz_d, &zero_lz);
            let lz = self.make_ite_bits(is_normal_val, &zero_lz, &lz_or_zero);

            // Shift denormal sig left by lz to normalize it
            // Need shift amount in sb bits for the barrel shifter
            let shift_bits = if eb <= sb {
                self.zero_extend(&lz_or_zero, sb - eb)
            } else {
                // Cap shift at sb
                lz_or_zero[..sb].to_vec()
            };
            let shifted_sig = self.bv_shl(&denormal_sig, &shift_bits);

            let sig = self.make_ite_bits(is_normal_val, &normal_sig, &shifted_sig);
            let exp = self.make_ite_bits(is_normal_val, &normal_exp, &denormal_exp);

            (sig, exp, lz)
        } else {
            let sig = self.make_ite_bits(is_normal_val, &normal_sig, &denormal_sig);
            let exp = self.make_ite_bits(is_normal_val, &normal_exp, &denormal_exp);
            (sig, exp, zero_lz)
        };

        (sgn, final_sig, final_exp, final_lz)
    }

    // ========== IEEE 754 rounding ==========

    /// Make rounding decision: returns a CnfLit that is true iff we should increment.
    ///
    /// Following Z3's mk_rounding_decision.
    /// Inputs are single bits: sign, last (LSB of kept part), round, sticky.
    pub(crate) fn make_rounding_decision(
        &mut self,
        rm: RoundingMode,
        sgn: CnfLit,
        last: CnfLit,
        round: CnfLit,
        sticky: CnfLit,
    ) -> CnfLit {
        match rm {
            RoundingMode::RNE => {
                // Increment if round AND (last OR sticky)
                let last_or_sticky = self.make_or(last, sticky);
                self.make_and(round, last_or_sticky)
            }
            RoundingMode::RNA => {
                // Increment if round bit is set
                round
            }
            RoundingMode::RTP => {
                // Increment if positive AND (round OR sticky)
                let round_or_sticky = self.make_or(round, sticky);
                let not_sgn = -sgn;
                self.make_and(not_sgn, round_or_sticky)
            }
            RoundingMode::RTN => {
                // Increment if negative AND (round OR sticky)
                let round_or_sticky = self.make_or(round, sticky);
                self.make_and(sgn, round_or_sticky)
            }
            RoundingMode::RTZ => {
                // Never increment
                self.const_false()
            }
        }
    }

    /// Round a significand+exponent pair to an IEEE 754 FpDecomposed.
    ///
    /// Following Z3's fpa2bv_converter::round.
    ///
    /// sig: sbits+4 bits = [sticky, round, last, mantissa..., hidden, overflow]
    /// exp: ebits+2 bits (signed, unbiased, with overflow headroom)
    ///
    /// Bit layout of sig (LSB first):
    ///   sig[0] = sticky, sig[1] = round, sig[2] = last (LSB of kept significand)
    ///   sig[3..sb+1] = mantissa bits
    ///   sig[sb+1] = hidden bit position
    ///   sig[sb+2] = overflow bit 1
    ///   sig[sb+3] = overflow bit 2 (MSB)
    pub(crate) fn fp_round(
        &mut self,
        precision: FpPrecision,
        rm: RoundingMode,
        sgn: CnfLit,
        sig: &[CnfLit],
        exp: &[CnfLit],
    ) -> FpDecomposed {
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;
        let bias = u64::from(precision.bias());

        debug_assert_eq!(sig.len(), sb + 4, "sig must be sbits+4 wide");
        debug_assert_eq!(exp.len(), eb + 2, "exp must be ebits+2 wide");

        // Phase 1: Overflow detection (OVF1)
        // Following Z3's fpa2bv_converter::round.
        // exp is signed (ebits+2 bits). Two conditions trigger OVF1:
        //
        // (a) e_top_three: exp[ebits+1]=0 AND (exp[ebits]=1 OR exp[ebits-1]=1).
        //     This catches large positive exponents that clearly overflow.
        //
        // (b) exp == e_max AND sig MSB is set.
        //     When exp equals e_max and the significand has its MSB set,
        //     beta = exp + 1 - lz = e_max + 1 > e_max, which overflows.
        //     Without this check, the biased exponent becomes all-ones
        //     (infinity encoding) without the overflow MUX selecting the
        //     correct overflow result (infinity vs max finite per RM).
        let e_max_biased = (1u64 << eb) - 2; // max normal biased exponent
        let e_max_unbiased = e_max_biased - bias; // max unbiased exponent
        let e_max_bv = self.const_bv(e_max_unbiased, eb + 2);

        // Condition (a): top 3 bits pattern
        let exp_top = exp[eb + 1]; // sign bit of the (eb+2)-wide signed exp
        let exp_second = exp[eb];
        let exp_third = exp[eb - 1];
        let not_top = -exp_top;
        let second_or_third = self.make_or(exp_second, exp_third);
        let e_top_three = self.make_and(not_top, second_or_third);

        // Condition (b): exp == e_max AND sig MSB set
        let exp_eq_emax = self.make_bits_equal(&e_max_bv, exp);
        let sig_msb = sig[sb + 3]; // MSB of the sb+4 wide significand
        let emax_and_sigmsb = self.make_and(exp_eq_emax, sig_msb);

        let ovf1_exp = self.make_or(e_top_three, emax_and_sigmsb);

        // Phase 2: Leading zero count of sig
        let lz = self.bv_leading_zeros(sig, eb + 2);

        // Phase 3: TINY detection (underflow to subnormal)
        // e_min = 1 - bias (unbiased)
        let e_min_val = 1i64 - bias as i64;
        let e_min_bv = self.const_bv(e_min_val as u64, eb + 2);
        // t = exp + 1 - lz - e_min
        let one_bv = self.const_bv(1, eb + 2);
        let exp_plus_1 = self.bv_add(exp, &one_bv);
        let t = self.bv_sub(&exp_plus_1, &lz);
        let t = self.bv_sub(&t, &e_min_bv);
        // TINY iff t < 0 (signed)
        let zero_bv = self.const_bv(0, eb + 2);
        let tiny = self.bv_slt(&t, &zero_bv);

        // Phase 4: Compute normalization shift (sigma) and result exponent (beta)
        // beta = exp - lz + 1
        let beta = self.bv_sub(&exp_plus_1, &lz);
        // sigma_add = exp - e_min + 1 (shift to subnormal position)
        let sigma_add = self.bv_sub(&exp_plus_1, &e_min_bv);
        // sigma = tiny ? sigma_add : lz
        let sigma = self.make_ite_bits(tiny, &sigma_add, &lz);

        // Phase 5: Normalization shift
        // Extend sig for shifting: sig_ext = concat(sig, zeros(sig_size))
        let sig_size = sb + 4;
        let zeros_ext = self.const_bv(0, sig_size);
        let sig_ext = Self::bv_concat(&zeros_ext, sig); // 2*sig_size bits, sig in upper half

        // Check if sigma is negative (need right shift)
        let sigma_neg = sigma[sigma.len() - 1]; // MSB = sign bit

        // Right shift case: shift_amount = -sigma (capped at sb+2)
        let neg_sigma = self.bv_neg(&sigma);
        let cap = self.const_bv((sb + 2) as u64, eb + 2);
        let neg_sigma_too_large = self.bv_slt(&cap, &neg_sigma);
        let capped_neg_sigma = self.make_ite_bits(neg_sigma_too_large, &cap, &neg_sigma);

        // Extend shift amount to match sig_ext width for barrel shifter
        let shift_width = 2 * sig_size;
        let shift_for_right = self.zero_extend(&capped_neg_sigma, shift_width - (eb + 2));
        let rs_sig = self.bv_lshr(&sig_ext, &shift_for_right);

        // Left shift case
        let shift_for_left = self.zero_extend(&sigma, shift_width - (eb + 2));
        let ls_sig = self.bv_shl(&sig_ext, &shift_for_left);

        // Select based on sigma sign
        let big_sh_sig = self.make_ite_bits(sigma_neg, &rs_sig, &ls_sig);

        // Extract top sbits+2 bits from big_sh_sig
        // big_sh_sig is 2*sig_size bits. We want bits [2*sig_size-1 : sig_size+2]
        // That's sig_size-2 = sb+2 bits starting from position sig_size+2
        let extract_start = sig_size + 2;
        let extracted: Vec<CnfLit> = big_sh_sig[extract_start..extract_start + sb + 2].to_vec();
        debug_assert_eq!(extracted.len(), sb + 2);

        // Compute sticky from remaining bits
        let sticky_bits: Vec<CnfLit> = big_sh_sig[..extract_start].to_vec();
        let sticky_from_shift = self.bv_or_reduce(&sticky_bits);

        // OR sticky into LSB of extracted sig
        let mut norm_sig = extracted;
        norm_sig[0] = self.make_or(norm_sig[0], sticky_from_shift);

        // Update exponent
        let norm_exp = self.make_ite_bits(tiny, &e_min_bv, &beta);

        // Phase 6: Extract last/round/sticky from sbits+2 sig
        let final_sticky = norm_sig[0];
        let final_round = norm_sig[1];
        let final_last = norm_sig[2];
        let kept_sig: Vec<CnfLit> = norm_sig[2..sb + 2].to_vec(); // sb bits
        debug_assert_eq!(kept_sig.len(), sb);

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

        // Phase 8: Post-normalization (rounding carry)
        let sig_ovf = rounded_sig[sb]; // carry out from rounding

        // If overflow: right shift by 1 (take bits [sb:1]), else take bits [sb-1:0]
        let sig_after_round_ovf: Vec<CnfLit> = rounded_sig[1..=sb].to_vec(); // shifted right
        let sig_after_round_normal: Vec<CnfLit> = rounded_sig[0..sb].to_vec();
        let post_sig = self.make_ite_bits(sig_ovf, &sig_after_round_ovf, &sig_after_round_normal);
        debug_assert_eq!(post_sig.len(), sb);

        // Increment exponent if sig overflowed
        let one_exp = self.const_bv(1, eb + 2);
        let exp_plus_one = self.bv_add(&norm_exp, &one_exp);
        let post_exp = self.make_ite_bits(sig_ovf, &exp_plus_one, &norm_exp);

        // Phase 9: Bias the exponent
        let bias_bv = self.const_bv(bias, eb + 2);
        let biased_exp_full = self.bv_add(&post_exp, &bias_bv);
        let biased_exp: Vec<CnfLit> = biased_exp_full[..eb].to_vec(); // truncate to eb bits

        // Phase 10: Overflow detection after rounding (OVF2)
        let all_ones_exp = self.const_bv((1u64 << eb) - 1, eb);
        let exp_is_all_ones = self.make_bits_equal(&biased_exp, &all_ones_exp);
        let ovf2 = self.make_and(sig_ovf, exp_is_all_ones);
        let ovf = self.make_or(ovf1_exp, ovf2);

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
            RoundingMode::RNE | RoundingMode::RNA => {
                // Always infinity on overflow
                (inf_exp, inf_sig)
            }
            RoundingMode::RTZ => {
                // Always max finite on overflow
                (max_exp, max_sig)
            }
            RoundingMode::RTP => {
                // Positive -> inf, Negative -> max finite
                let exp_sel = self.make_ite_bits(sgn, &max_exp, &inf_exp);
                let sig_sel = self.make_ite_bits(sgn, &max_sig, &inf_sig);
                (exp_sel, sig_sel)
            }
            RoundingMode::RTN => {
                // Positive -> max finite, Negative -> inf
                let exp_sel = self.make_ite_bits(sgn, &inf_exp, &max_exp);
                let sig_sel = self.make_ite_bits(sgn, &inf_sig, &max_sig);
                (exp_sel, sig_sel)
            }
        };

        // Phase 12: Subnormal detection
        // If hidden bit (post_sig[sb-1]) is 0, result is denormal -> biased exp = 0
        let hidden_bit = post_sig[sb - 1];
        let is_denormal = -hidden_bit;
        let bot_exp = self.const_bv(0, eb);
        let normal_or_denormal_exp = self.make_ite_bits(is_denormal, &bot_exp, &biased_exp);

        // Strip hidden bit for stored significand
        let stored_sig: Vec<CnfLit> = post_sig[..sb - 1].to_vec(); // sb-1 bits

        // Phase 13: Final MUX for overflow
        let result_exp = self.make_ite_bits(ovf, &ovf_exp, &normal_or_denormal_exp);
        let result_sig = self.make_ite_bits(ovf, &ovf_sig, &stored_sig);

        FpDecomposed {
            sign: sgn,
            exponent: result_exp,
            significand: result_sig,
            precision,
        }
    }

    /// Constrain result to match normal_result when cond is true.
    /// For each bit of sign, exponent, significand: when cond, result bit = normal bit.
    pub(crate) fn constrain_fp_when(
        &mut self,
        cond: CnfLit,
        result: &FpDecomposed,
        normal_result: &FpDecomposed,
    ) {
        // sign: cond => (result.sign <-> normal.sign)
        self.add_clause(CnfClause::new(vec![
            -cond,
            -result.sign,
            normal_result.sign,
        ]));
        self.add_clause(CnfClause::new(vec![
            -cond,
            result.sign,
            -normal_result.sign,
        ]));

        // exponent bits
        for (&r, &n) in result.exponent.iter().zip(&normal_result.exponent) {
            self.add_clause(CnfClause::new(vec![-cond, -r, n]));
            self.add_clause(CnfClause::new(vec![-cond, r, -n]));
        }

        // significand bits
        for (&r, &n) in result.significand.iter().zip(&normal_result.significand) {
            self.add_clause(CnfClause::new(vec![-cond, -r, n]));
            self.add_clause(CnfClause::new(vec![-cond, r, -n]));
        }
    }

    /// Create a literal for x < y
    ///
    /// IEEE 754-2008 Section 5.11: Comparison is quiet (no NaN signal).
    /// - NaN compared to anything is false.
    /// - -0 < +0 is false (they are equal).
    /// - For same sign: compare magnitudes (positive: smaller mag < larger mag;
    ///   negative: larger mag < smaller mag).
    pub(crate) fn make_lt_result(&mut self, x: &FpDecomposed, y: &FpDecomposed) -> CnfLit {
        let x_nan = self.is_nan(x);
        let y_nan = self.is_nan(y);
        let either_nan = self.make_or(x_nan, y_nan);

        // IEEE 754: -0 == +0, so -0 < +0 must be false.
        // Both-zero when exponent and significand are all zero (any sign).
        let x_zero = self.is_zero(x);
        let y_zero = self.is_zero(y);
        let both_zero = self.make_and(x_zero, y_zero);

        let x_neg = x.sign;
        let y_neg = y.sign;
        let not_y_neg = -y_neg;
        let x_neg_y_pos = self.make_and(x_neg, not_y_neg);

        let same_sign = self.make_xnor(x_neg, y_neg);

        let exp_lt = self.make_unsigned_lt(&x.exponent, &y.exponent);
        let exp_eq = self.make_bits_equal(&x.exponent, &y.exponent);
        let sig_lt = self.make_unsigned_lt(&x.significand, &y.significand);

        let sig_lt_and_exp_eq = self.make_and(exp_eq, sig_lt);
        let mag_lt = self.make_or(exp_lt, sig_lt_and_exp_eq);

        // For negative numbers, x < y iff |x| > |y| (larger magnitude = more negative).
        // Compute mag_gt = reverse comparison: y's magnitude < x's magnitude.
        let exp_gt = self.make_unsigned_lt(&y.exponent, &x.exponent);
        let sig_gt = self.make_unsigned_lt(&y.significand, &x.significand);
        let sig_gt_and_exp_eq = self.make_and(exp_eq, sig_gt);
        let mag_gt = self.make_or(exp_gt, sig_gt_and_exp_eq);
        let magnitude_lt = self.make_ite(x_neg, mag_gt, mag_lt);

        let same_sign_mag_lt = self.make_and(same_sign, magnitude_lt);
        let sign_based = self.make_or(x_neg_y_pos, same_sign_mag_lt);
        let not_nan = -either_nan;
        let not_both_zero = -both_zero;
        let not_nan_or_both_zero = self.make_and(not_nan, not_both_zero);
        self.make_and(not_nan_or_both_zero, sign_based)
    }
}
