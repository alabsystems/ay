// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original rounding phase 5; right/left barrel stages retain one control.

use super::round::{Format, Normalized, Prepared};
use crate::construction::control::BuildControl;
use crate::FpSolver;
use ay_core::CnfLit;

impl FpSolver<'_> {
    pub(super) fn conversion_round_normalize<C: BuildControl>(
        &mut self,
        format: Format,
        sig: &[CnfLit],
        prepared: Prepared,
        control: &mut C,
    ) -> Result<Normalized, C::Error> {
        let Format { sb, w, .. } = format;
        let result = (|| -> Result<Normalized, C::Error> {
            let Prepared {
                ovf1_exp,
                tiny,
                e_min_bv,
                beta,
                sigma,
            } = prepared;
            self.conversion_poll(control)?;
            // Phase 5: Normalization shift
            // Extend sig for shifting: sig_ext = concat(sig, zeros(sig_size))
            let sig_size = sb + 4;
            let zeros_ext = self.const_bv(0, sig_size);
            let sig_ext = Self::bv_concat(&zeros_ext, sig); // 2*sig_size bits, sig in upper half

            // Check if sigma is negative (need right shift)
            let sigma_neg = sigma[sigma.len() - 1]; // MSB = sign bit

            // Right shift case: shift_amount = -sigma (capped at sb+2)
            let neg_sigma = self.bv_neg(&sigma);
            let cap = self.const_bv((sb + 2) as u64, w);
            let neg_sigma_too_large = self.bv_slt(&cap, &neg_sigma);
            let capped_neg_sigma = self.make_ite_bits(neg_sigma_too_large, &cap, &neg_sigma);

            // Extend shift amount to match sig_ext width for barrel shifter
            let shift_width = 2 * sig_size;
            // `capped_neg_sigma <= sb + 2` and a left shift's `sigma <= sb + 4` both
            // fit `shift_width` bits, so resizing is exact at any `w`.
            let shift_for_right = self.resize_unsigned(&capped_neg_sigma, shift_width);
            let rs_sig = self.conversion_lshr_with_control(&sig_ext, &shift_for_right, control)?;

            // Left shift case
            let shift_for_left = self.resize_unsigned(&sigma, shift_width);
            let ls_sig = self.bv_shl_with_control(&sig_ext, &shift_for_left, control)?;

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

            Ok(Normalized {
                ovf1_exp,
                norm_sig,
                norm_exp,
            })
        })()?;
        self.conversion_poll(control)?;
        Ok(result)
    }
}
