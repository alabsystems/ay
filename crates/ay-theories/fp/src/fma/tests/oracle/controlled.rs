// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

impl FpSolver<'_> {
    /// Preserve one borrowed original control through the general FMA phases.
    /// Unpack, add, round, individual gates and allocator frees remain bounded-
    /// format cooperative intervals, not hard preemption or resource grants.
    pub(super) fn make_fma_legacy(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        z: &FpDecomposed,
        rm: RmOperand,
    ) -> FpDecomposed {
        let precision = x.precision;
        let special = self.fma_special_legacy(x, y, z);
        let product = self.fma_product_legacy(x, y, z);
        let aligned = self.fma_align_legacy(precision, product, special.xy_sign, z.sign);
        let magnitude = self.fma_magnitude_legacy(precision, aligned);
        let normalized = self.fma_normalize_legacy(precision, magnitude, rm);
        self.fma_finish_legacy(special, normalized, z, rm)
    }

    fn fma_product_legacy(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        z: &FpDecomposed,
    ) -> Product {
        let precision = x.precision;
        let sb = precision.significand_bits() as usize;
        let eb = precision.exponent_bits() as usize;
        let result = {
            let (_a_sgn, a_sig, a_exp, a_lz) = self.unpack(x, true);
            let (_b_sgn, b_sig, b_exp, b_lz) = self.unpack(y, true);
            let (_c_sgn, c_sig, c_exp, c_lz) = self.unpack(z, true);
            let a_ext = self.zero_extend(&a_sig, sb);
            let b_ext = self.zero_extend(&b_sig, sb);
            let product = self.bv_mul(&a_ext, &b_ext);

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
        result
    }
}
