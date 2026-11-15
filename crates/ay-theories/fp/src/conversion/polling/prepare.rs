// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original rounding phases 1–4, with the same native statement order.

use super::round::{Format, Prepared};
use crate::construction::control::BuildControl;
use crate::FpSolver;
use ay_core::CnfLit;

impl FpSolver<'_> {
    pub(super) fn conversion_round_prepare<C: BuildControl>(
        &mut self,
        format: Format,
        sig: &[CnfLit],
        exp: &[CnfLit],
        control: &mut C,
    ) -> Result<Prepared, C::Error> {
        let Format { eb, sb, bias, w } = format;
        let result = (|| -> Result<Prepared, C::Error> {
            self.conversion_poll(control)?;
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
            let e_max_bv = self.const_bv(e_max_unbiased, w);

            // Condition (a): exp > e_max. At `eb + 2` bits this is the top-three
            // pattern (non-negative, and bit `eb` or `eb - 1` set: exp >= 2^(eb-1)
            // = e_max + 1); at a wider width it is the signed comparison itself.
            let e_top_three = if w == eb + 2 {
                let exp_top = exp[eb + 1]; // sign bit of the (eb+2)-wide signed exp
                let exp_second = exp[eb];
                let exp_third = exp[eb - 1];
                let not_top = -exp_top;
                let second_or_third = self.make_or(exp_second, exp_third);
                self.make_and(not_top, second_or_third)
            } else {
                self.bv_slt(&e_max_bv, exp)
            };

            // Condition (b): exp == e_max AND sig MSB set
            let exp_eq_emax = self.make_bits_equal(&e_max_bv, exp);
            let sig_msb = sig[sb + 3]; // MSB of the sb+4 wide significand
            let emax_and_sigmsb = self.make_and(exp_eq_emax, sig_msb);

            let ovf1_exp = self.make_or(e_top_three, emax_and_sigmsb);

            self.conversion_poll(control)?;
            // Phase 2: Leading zero count of sig
            let lz = self.conversion_lz_with_control(sig, w, control)?;

            self.conversion_poll(control)?;
            // Phase 3: TINY detection (underflow to subnormal)
            // e_min = 1 - bias (unbiased)
            let e_min_val = 1i64 - bias as i64;
            let e_min_bv = self.const_bv_signed(e_min_val, w);
            // t = exp + 1 - lz - e_min
            let one_bv = self.const_bv(1, w);
            let exp_plus_1 = self.bv_add(exp, &one_bv);
            let t = self.bv_sub(&exp_plus_1, &lz);
            let t = self.bv_sub(&t, &e_min_bv);
            // TINY iff t < 0 (signed)
            let zero_bv = self.const_bv(0, w);
            let tiny = self.bv_slt(&t, &zero_bv);

            self.conversion_poll(control)?;
            // Phase 4: Compute normalization shift (sigma) and result exponent (beta)
            // beta = exp - lz + 1
            let beta = self.bv_sub(&exp_plus_1, &lz);
            // sigma_add = exp - e_min + 1 (shift to subnormal position)
            let sigma_add = self.bv_sub(&exp_plus_1, &e_min_bv);
            // sigma = tiny ? sigma_add : lz
            let sigma = self.make_ite_bits(tiny, &sigma_add, &lz);

            Ok(Prepared {
                ovf1_exp,
                tiny,
                e_min_bv,
                beta,
                sigma,
            })
        })()?;
        // Only returned vectors survive this original-owner fence.
        self.conversion_poll(control)?;
        Ok(result)
    }
}
