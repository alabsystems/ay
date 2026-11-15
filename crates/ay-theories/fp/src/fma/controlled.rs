// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct Special {
    pub(super) result: FpDecomposed,
    pub(super) xy_sign: CnfLit,
    pub(super) z_zero: CnfLit,
    pub(super) not_nan: CnfLit,
    pub(super) special: CnfLit,
    pub(super) xy_zero: CnfLit,
    pub(super) both_zero: CnfLit,
}

pub(super) struct Product {
    pub(super) mul_sig: Vec<CnfLit>,
    pub(super) c_sig_ext: Vec<CnfLit>,
    pub(super) mul_exp: Vec<CnfLit>,
    pub(super) c_eff_exp: Vec<CnfLit>,
}

pub(super) struct Aligned {
    pub(super) e_sig: Vec<CnfLit>,
    pub(super) shifted_f_sig: Vec<CnfLit>,
    pub(super) e_exp: Vec<CnfLit>,
    pub(super) e_sgn: CnfLit,
    pub(super) f_sgn: CnfLit,
    pub(super) alignment_sticky: CnfLit,
}

pub(super) struct Magnitude {
    pub(super) sig_abs: Vec<CnfLit>,
    pub(super) e_exp: Vec<CnfLit>,
    pub(super) res_sign_normal: CnfLit,
    pub(super) extra_is_zero: CnfLit,
    pub(super) alignment_sticky: CnfLit,
}

pub(super) struct Normalized {
    pub(super) normal_result: FpDecomposed,
    pub(super) sig_abs: Vec<CnfLit>,
    pub(super) alignment_sticky: CnfLit,
}

impl FpSolver<'_> {
    /// Preserve one borrowed original control through the general FMA phases.
    /// Unpack, add, round, individual gates and allocator frees remain bounded-
    /// format cooperative intervals, not hard preemption or resource grants.
    pub(crate) fn make_fma_with_control<C: BuildControl>(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        z: &FpDecomposed,
        rm: RmOperand,
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        let precision = x.precision;
        let special = self.fma_special_with_control(x, y, z, control)?;
        let product = self.fma_product_with_control(x, y, z, control)?;
        let aligned =
            self.fma_align_with_control(precision, product, special.xy_sign, z.sign, control)?;
        let magnitude = self.fma_magnitude_with_control(precision, aligned, control)?;
        let normalized = self.fma_normalize_with_control(precision, magnitude, rm, control)?;
        self.fma_finish_with_control(special, normalized, z, rm, control)
    }

    fn fma_product_with_control<C: BuildControl>(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        z: &FpDecomposed,
        control: &mut C,
    ) -> Result<Product, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let precision = x.precision;
        let sb = precision.significand_bits() as usize;
        let eb = precision.exponent_bits() as usize;
        let result = {
            let (_a_sgn, a_sig, a_exp, a_lz) = self.unpack(x, true);
            control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
            let (_b_sgn, b_sig, b_exp, b_lz) = self.unpack(y, true);
            control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
            let (_c_sgn, c_sig, c_exp, c_lz) = self.unpack(z, true);

            control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
            let a_ext = self.zero_extend(&a_sig, sb);
            let b_ext = self.zero_extend(&b_sig, sb);
            let product = self.bv_mul_with_control(&a_ext, &b_ext, control)?;

            // Every exponent below is signed and `ew` bits wide: `eb + 2` (z3's
            // choice) unless the format needs more (see `fma_exponent_width`).
            let ew = Self::fma_exponent_width(eb, sb);
            let a_exp_ext = self.sign_extend(&a_exp, ew - eb);
            let b_exp_ext = self.sign_extend(&b_exp, ew - eb);
            let a_lz_ext = self.zero_extend(&a_lz, ew - a_lz.len());
            let b_lz_ext = self.zero_extend(&b_lz, ew - b_lz.len());
            let a_eff = self.bv_sub(&a_exp_ext, &a_lz_ext);
            let b_eff = self.bv_sub(&b_exp_ext, &b_lz_ext);
            let mul_exp = self.bv_add(&a_eff, &b_eff);

            let c_exp_ext = self.sign_extend(&c_exp, ew - eb);
            let c_lz_ext = self.zero_extend(&c_lz, ew - c_lz.len());
            let c_eff_exp = self.bv_sub(&c_exp_ext, &c_lz_ext);

            let zeros3 = self.const_bv(0, 3);
            let mul_sig = Self::bv_concat(&zeros3, &product);
            let zeros_sb2 = self.const_bv(0, sb + 2);
            let c_padded = Self::bv_concat(&zeros_sb2, &c_sig);
            let c_sig_ext = self.zero_extend(&c_padded, 1);

            let ww = 2 * sb + 3;
            debug_assert_eq!(mul_sig.len(), ww);
            debug_assert_eq!(c_sig_ext.len(), ww);

            Product {
                mul_sig,
                c_sig_ext,
                mul_exp,
                c_eff_exp,
            }
        };
        // All unpack, extension and multiplication scratch has been dropped.
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        Ok(result)
    }
}
