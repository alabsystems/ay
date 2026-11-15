// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Literal pre-change conversion bodies, using untouched legacy helpers.

use crate::construction::control::BuildControl;
use crate::construction::FpBuildStage;
use crate::{FpDecomposed, FpPrecision, FpSolver, RmOperand};
use ay_core::{CnfLit, Sort, TermId};

impl FpSolver<'_> {
    pub(super) fn oracle_signed<C: BuildControl>(
        &mut self,
        bv_term: TermId,
        rm: RmOperand,
        precision: FpPrecision,
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;
        let sig_sz = sb + 4;

        let bv_sz = match self.terms.sort(bv_term).clone() {
            Sort::BitVec(bvs) => bvs.width as usize,
            _ => {
                tracing::warn!("to_fp signed: argument is not BitVec");
                return Ok(self.fresh_decomposed(precision));
            }
        };
        // Signed, and wide enough for `bv_sz - 2` and for what `fp_round`
        // derives from it (see `int_conversion_exponent_width`).
        let exp_sz = Self::int_conversion_exponent_width(eb, sb, bv_sz);

        let Some(bv_bits) = self.bitblast_conv_bv_arg_with_control(bv_term, bv_sz, control)? else {
            return Ok(self.fresh_decomposed(precision));
        };
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let is_zero = self.make_all_zero(&bv_bits);
        let zero_fp = self.make_zero(precision, false);

        let sign_bit = bv_bits[bv_sz - 1];
        let neg_bv = self.bv_neg(&bv_bits);
        let abs_bv = self.make_ite_bits(sign_bit, &neg_bv, &bv_bits);

        let lz = self.bv_leading_zeros(&abs_bv, exp_sz);
        let lz_extended = if bv_sz > exp_sz {
            self.zero_extend(&lz, bv_sz - exp_sz)
        } else if bv_sz < exp_sz {
            lz[..bv_sz].to_vec()
        } else {
            lz.clone()
        };
        let shifted = self.bv_shl(&abs_bv, &lz_extended);

        let mut sig_bits = Vec::with_capacity(sig_sz);
        if bv_sz >= sig_sz {
            let top_start = bv_sz - (sig_sz - 1);
            let sticky_bits: Vec<CnfLit> = shifted[..top_start].to_vec();
            let sticky = self.bv_or_reduce(&sticky_bits);
            sig_bits.push(sticky);
            sig_bits.extend_from_slice(&shifted[top_start..]);
        } else {
            let pad = sig_sz - bv_sz;
            let zero = self.const_false();
            for _ in 0..pad {
                sig_bits.push(zero);
            }
            sig_bits.extend_from_slice(&shifted);
        }
        debug_assert_eq!(sig_bits.len(), sig_sz);

        let base_exp = self.const_bv((bv_sz as u64).wrapping_sub(2), exp_sz);
        let exp_bits = self.bv_sub(&base_exp, &lz);

        let rounded = self.fp_round(precision, rm, sign_bit, &sig_bits, &exp_bits);
        let result = self.make_ite_fp(is_zero, &zero_fp, &rounded, precision);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        Ok(result)
    }

    pub(super) fn oracle_unsigned<C: BuildControl>(
        &mut self,
        bv_term: TermId,
        rm: RmOperand,
        precision: FpPrecision,
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;
        let sig_sz = sb + 4;

        let bv_sz = match self.terms.sort(bv_term).clone() {
            Sort::BitVec(bvs) => bvs.width as usize,
            _ => {
                tracing::warn!("to_fp_unsigned: argument is not BitVec");
                return Ok(self.fresh_decomposed(precision));
            }
        };
        // Signed, and wide enough for `bv_sz - 2` and for what `fp_round`
        // derives from it (see `int_conversion_exponent_width`).
        let exp_sz = Self::int_conversion_exponent_width(eb, sb, bv_sz);

        let Some(bv_bits) = self.bitblast_conv_bv_arg_with_control(bv_term, bv_sz, control)? else {
            return Ok(self.fresh_decomposed(precision));
        };
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result_sign = self.const_false();
        let is_zero = self.make_all_zero(&bv_bits);
        let zero_fp = self.make_zero(precision, false);

        let lz = self.bv_leading_zeros(&bv_bits, exp_sz);
        let lz_extended = if bv_sz > exp_sz {
            self.zero_extend(&lz, bv_sz - exp_sz)
        } else if bv_sz < exp_sz {
            lz[..bv_sz].to_vec()
        } else {
            lz.clone()
        };
        let shifted = self.bv_shl(&bv_bits, &lz_extended);

        let mut sig_bits = Vec::with_capacity(sig_sz);
        if bv_sz >= sig_sz {
            let top_start = bv_sz - (sig_sz - 1);
            let sticky_bits: Vec<CnfLit> = shifted[..top_start].to_vec();
            let sticky = self.bv_or_reduce(&sticky_bits);
            sig_bits.push(sticky);
            sig_bits.extend_from_slice(&shifted[top_start..]);
        } else {
            let pad = sig_sz - bv_sz;
            let zero = self.const_false();
            for _ in 0..pad {
                sig_bits.push(zero);
            }
            sig_bits.extend_from_slice(&shifted);
        }
        debug_assert_eq!(sig_bits.len(), sig_sz);

        let base_exp = self.const_bv((bv_sz as u64).wrapping_sub(2), exp_sz);
        let exp_bits = self.bv_sub(&base_exp, &lz);

        let rounded = self.fp_round(precision, rm, result_sign, &sig_bits, &exp_bits);
        let result = self.make_ite_fp(is_zero, &zero_fp, &rounded, precision);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        Ok(result)
    }
}
