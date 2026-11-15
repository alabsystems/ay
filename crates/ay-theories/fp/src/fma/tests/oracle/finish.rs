// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

impl FpSolver<'_> {
    pub(super) fn fma_special_legacy(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        z: &FpDecomposed,
    ) -> Special {
        let precision = x.precision;
        let result = {
            let x_nan = self.is_nan(x);
            let y_nan = self.is_nan(y);
            let z_nan = self.is_nan(z);
            let x_inf = self.is_infinite(x);
            let y_inf = self.is_infinite(y);
            let z_inf = self.is_infinite(z);
            let x_zero = self.is_zero(x);
            let y_zero = self.is_zero(y);
            let z_zero = self.is_zero(z);

            let yz_nan = self.make_or(y_nan, z_nan);
            let any_nan = self.make_or(x_nan, yz_nan);
            let x_inf_y_zero = self.make_and(x_inf, y_zero);
            let y_inf_x_zero = self.make_and(y_inf, x_zero);
            let inf_times_zero = self.make_or(x_inf_y_zero, y_inf_x_zero);
            let xy_inf = self.make_or(x_inf, y_inf);
            let xy_sign = self.make_xor(x.sign, y.sign);
            let z_opp_sign = self.make_xor(xy_sign, z.sign);
            let z_inf_opp = self.make_and(z_inf, z_opp_sign);
            let inf_cancel = self.make_and(xy_inf, z_inf_opp);
            let inf_zero_or_cancel = self.make_or(inf_times_zero, inf_cancel);
            let result_nan = self.make_or(any_nan, inf_zero_or_cancel);

            let not_nan = -result_nan;
            let not_inf_times_zero = -inf_times_zero;
            let xy_inf_valid = self.make_and(xy_inf, not_inf_times_zero);
            let any_inf = self.make_or(xy_inf_valid, z_inf);
            let result_inf = self.make_and(any_inf, not_nan);
            let inf_sign = self.make_ite(xy_inf_valid, xy_sign, z.sign);

            let result = self.fresh_decomposed(precision);
            let res_sign = result.sign;

            let inf_and_not_nan = self.make_and(result_inf, not_nan);
            self.add_clause(CnfClause::new(vec![-inf_and_not_nan, -inf_sign, res_sign]));
            self.add_clause(CnfClause::new(vec![-inf_and_not_nan, inf_sign, -res_sign]));

            let special = self.constrain_nan_inf(&result, result_nan, result_inf);
            let xy_zero = self.make_or(x_zero, y_zero);
            let both_zero = self.make_and(xy_zero, z_zero);

            Special {
                result,
                xy_sign,
                z_zero,
                not_nan,
                special,
                xy_zero,
                both_zero,
            }
        };
        result
    }

    pub(super) fn fma_finish_legacy(
        &mut self,
        special_state: Special,
        normalized: Normalized,
        z: &FpDecomposed,
        rm: RmOperand,
    ) -> FpDecomposed {
        let result = {
            let Special {
                result,
                xy_sign,
                z_zero,
                not_nan,
                special,
                xy_zero,
                both_zero,
            } = special_state;
            let Normalized {
                normal_result,
                sig_abs,
                alignment_sticky,
            } = normalized;
            let precision = result.precision;
            let res_sign = result.sign;
            let special_or_both_zero = self.make_or(special, both_zero);
            let xy_zero_z_not = self.make_and(xy_zero, -z_zero);
            let special_or_trivial = self.make_or(special_or_both_zero, xy_zero_z_not);
            let not_special = -special_or_trivial;

            // IEEE 754-2019 §6.3: when the (infinitely precise) result of the
            // fused multiply-add is *exactly* zero through cancellation of opposite
            // signs, the sign is +0 in every rounding mode except roundTowardNegative
            // (which yields -0) — regardless of the operand signs. The general path
            // derives `res_sign_normal` from the larger-magnitude addend, which is
            // wrong for an exact cancellation. Detect the exact-zero sum (aligned
            // magnitude all-zero AND no bits dropped during alignment, so the true
            // sum — not merely a rounded-down underflow — is zero) and override the
            // result to the correctly-signed zero. We deliberately do NOT trigger on
            // a nonzero `sig_abs` that merely rounds/underflows to zero: that result
            // keeps the computed sign and rounding behaviour (e.g. RTP rounding a
            // tiny positive up off zero), which the normal path already handles.
            let sig_abs_is_zero = self.make_all_zero(&sig_abs);
            let exact_zero_sum = self.make_and(sig_abs_is_zero, -alignment_sticky);
            let cancel_zero = self.make_and(not_special, exact_zero_sum);
            let cancel_zero_result = self.make_rm_signed_zero(precision, rm);
            self.constrain_fp_when(cancel_zero, &result, &cancel_zero_result);

            let normal_applies = self.make_and(not_special, -cancel_zero);
            self.constrain_fp_when(normal_applies, &result, &normal_result);

            let xy_zero_z_not_nan = self.make_and(xy_zero_z_not, not_nan);
            self.constrain_fp_when(xy_zero_z_not_nan, &result, z);

            let both_zero_not_nan = self.make_and(both_zero, not_nan);
            let both_neg = self.make_and(xy_sign, z.sign);
            // Two zeros of opposite signs sum to -0 only toward negative.
            let zero_is_neg = match rm {
                RmOperand::Literal(RoundingMode::RTN) => self.make_or(xy_sign, z.sign),
                RmOperand::Literal(_) => both_neg,
                RmOperand::Symbolic(_) => {
                    let either_neg = self.make_or(xy_sign, z.sign);
                    let rtn = self.rm_is(rm, RoundingMode::RTN);
                    self.make_ite(rtn, either_neg, both_neg)
                }
            };
            for &exp_bit in &result.exponent {
                self.add_clause(CnfClause::new(vec![-both_zero_not_nan, -exp_bit]));
            }
            for &sig_bit in &result.significand {
                self.add_clause(CnfClause::new(vec![-both_zero_not_nan, -sig_bit]));
            }
            self.add_clause(CnfClause::new(vec![
                -both_zero_not_nan,
                -zero_is_neg,
                res_sign,
            ]));
            self.add_clause(CnfClause::new(vec![
                -both_zero_not_nan,
                zero_is_neg,
                -res_sign,
            ]));

            result
        };
        // Rounded/special scratch is gone before the final original observation.
        result
    }
}
