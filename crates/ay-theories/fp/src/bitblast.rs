// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bit-blast query helpers for FP predicates and FP/BV conversions.

use ay_core::term::{Symbol, TermData, TermId};
use ay_core::{CnfLit, Sort};
use num_bigint::BigInt;

use crate::construction::control::{uninterrupted, BuildControl};
use crate::construction::FpBuildStage;

use super::{FpSolver, HashMap, RmOperand};

mod extra_bv_ops;

impl FpSolver<'_> {
    /// Bit-blast `fp.isNaN`.
    pub fn bitblast_is_nan(&mut self, term: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_is_nan_with_control(term, control))
    }

    pub(crate) fn bitblast_is_nan_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let fp = self.get_fp_with_control(term, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.is_nan(&fp);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.isInfinite`.
    pub fn bitblast_is_infinite(&mut self, term: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_is_infinite_with_control(term, control))
    }

    pub(crate) fn bitblast_is_infinite_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let fp = self.get_fp_with_control(term, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.is_infinite(&fp);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.isZero`.
    pub fn bitblast_is_zero(&mut self, term: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_is_zero_with_control(term, control))
    }

    pub(crate) fn bitblast_is_zero_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let fp = self.get_fp_with_control(term, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.is_zero(&fp);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.isNormal`.
    pub fn bitblast_is_normal(&mut self, term: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_is_normal_with_control(term, control))
    }

    pub(crate) fn bitblast_is_normal_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let fp = self.get_fp_with_control(term, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.is_normal(&fp);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.isSubnormal`.
    pub fn bitblast_is_subnormal(&mut self, term: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_is_subnormal_with_control(term, control))
    }

    pub(crate) fn bitblast_is_subnormal_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let fp = self.get_fp_with_control(term, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.is_subnormal(&fp);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.isPositive`.
    pub fn bitblast_is_positive(&mut self, term: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_is_positive_with_control(term, control))
    }

    pub(crate) fn bitblast_is_positive_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let fp = self.get_fp_with_control(term, control)?;
        let is_nan = self.is_nan(&fp);
        let not_nan = -is_nan;
        let not_sign = -fp.sign;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.make_and(not_nan, not_sign);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.isNegative`.
    pub fn bitblast_is_negative(&mut self, term: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_is_negative_with_control(term, control))
    }

    pub(crate) fn bitblast_is_negative_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let fp = self.get_fp_with_control(term, control)?;
        let is_nan = self.is_nan(&fp);
        let not_nan = -is_nan;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.make_and(not_nan, fp.sign);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast SMT-LIB structural equality `(=)` on FP sort.
    pub fn bitblast_fp_structural_eq(&mut self, x: TermId, y: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_fp_structural_eq_with_control(x, y, control))
    }

    pub(crate) fn bitblast_fp_structural_eq_with_control<C: BuildControl>(
        &mut self,
        x: TermId,
        y: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let fp_x = self.get_fp_with_control(x, control)?;
        let fp_y = self.get_fp_with_control(y, control)?;

        let sign_eq = self.make_xnor(fp_x.sign, fp_y.sign);
        let exp_eq = self.make_bits_equal(&fp_x.exponent, &fp_y.exponent);
        let sig_eq = self.make_bits_equal(&fp_x.significand, &fp_y.significand);
        let exp_sig_eq = self.make_and(exp_eq, sig_eq);
        let bit_equal = self.make_and(sign_eq, exp_sig_eq);

        // SMT-LIB FP has a SINGLE abstract NaN: structural `=` is true whenever
        // BOTH operands are NaN, regardless of sign/payload bits. (Unlike `fp.eq`,
        // it does NOT collapse +0/-0 — those stay distinct via `bit_equal`.) The
        // NaN literal is built as the canonical 0x7FC00000, so without this any
        // other NaN encoding — e.g. a bitcast `((_ to_fp ..) bv)` landing on a
        // non-canonical NaN — would compare unequal and the assertion go UNSAT.
        let x_nan = self.is_nan(&fp_x);
        let y_nan = self.is_nan(&fp_y);
        let both_nan = self.make_and(x_nan, y_nan);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.make_or(both_nan, bit_equal);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.eq`.
    pub fn bitblast_fp_eq(&mut self, x: TermId, y: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_fp_eq_with_control(x, y, control))
    }

    pub(crate) fn bitblast_fp_eq_with_control<C: BuildControl>(
        &mut self,
        x: TermId,
        y: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let fp_x = self.get_fp_with_control(x, control)?;
        let fp_y = self.get_fp_with_control(y, control)?;

        let x_nan = self.is_nan(&fp_x);
        let y_nan = self.is_nan(&fp_y);
        let either_nan = self.make_or(x_nan, y_nan);

        let x_zero = self.is_zero(&fp_x);
        let y_zero = self.is_zero(&fp_y);
        let both_zero = self.make_and(x_zero, y_zero);

        let sign_eq = self.make_xnor(fp_x.sign, fp_y.sign);
        let exp_eq = self.make_bits_equal(&fp_x.exponent, &fp_y.exponent);
        let sig_eq = self.make_bits_equal(&fp_x.significand, &fp_y.significand);
        let exp_sig_eq = self.make_and(exp_eq, sig_eq);
        let bit_equal = self.make_and(sign_eq, exp_sig_eq);

        let eq = self.make_or(both_zero, bit_equal);
        let not_nan = -either_nan;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.make_and(not_nan, eq);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.lt`.
    pub fn bitblast_fp_lt(&mut self, x: TermId, y: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_fp_lt_with_control(x, y, control))
    }

    pub(crate) fn bitblast_fp_lt_with_control<C: BuildControl>(
        &mut self,
        x: TermId,
        y: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let fp_x = self.get_fp_with_control(x, control)?;
        let fp_y = self.get_fp_with_control(y, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.make_lt_result(&fp_x, &fp_y);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.leq`.
    pub fn bitblast_fp_le(&mut self, x: TermId, y: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_fp_le_with_control(x, y, control))
    }

    pub(crate) fn bitblast_fp_le_with_control<C: BuildControl>(
        &mut self,
        x: TermId,
        y: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let lt = self.bitblast_fp_lt_with_control(x, y, control)?;
        let eq = self.bitblast_fp_eq_with_control(x, y, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.make_or(lt, eq);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.gt`.
    pub fn bitblast_fp_gt(&mut self, x: TermId, y: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_fp_gt_with_control(x, y, control))
    }

    pub(crate) fn bitblast_fp_gt_with_control<C: BuildControl>(
        &mut self,
        x: TermId,
        y: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.bitblast_fp_lt_with_control(y, x, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.geq`.
    pub fn bitblast_fp_ge(&mut self, x: TermId, y: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_fp_ge_with_control(x, y, control))
    }

    pub(crate) fn bitblast_fp_ge_with_control<C: BuildControl>(
        &mut self,
        x: TermId,
        y: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.bitblast_fp_le_with_control(y, x, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.to_ubv` or `fp.to_sbv`.
    pub fn bitblast_to_bv(
        &mut self,
        fp_term: TermId,
        rm: impl Into<RmOperand>,
        bv_sz: usize,
        is_signed: bool,
    ) -> Vec<CnfLit> {
        let rm = rm.into();
        uninterrupted(|control| {
            self.bitblast_to_bv_with_control(fp_term, rm, bv_sz, is_signed, control)
        })
    }

    pub(crate) fn bitblast_to_bv_with_control<C: BuildControl>(
        &mut self,
        fp_term: TermId,
        rm: RmOperand,
        bv_sz: usize,
        is_signed: bool,
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let fp = self.get_fp_with_control(fp_term, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let (sgn, sig, exp, lz) = self.unpack(&fp, true);

        let ebits = fp.precision.exponent_bits() as usize;
        let sbits = fp.precision.significand_bits() as usize;
        // Signed, `ebits + 2` bits (z3's) unless the normalised exponent or its
        // negation needs more (`to_bv_exponent_width`).
        let ew = Self::to_bv_exponent_width(ebits, sbits);
        // SMT-LIB: fp.to_{s,u}bv on NaN/Inf or an out-of-range value is a
        // fixed-but-unspecified bitvector — unconstrained, but consistent across
        // occurrences of the same conversion (the executor caches this term's
        // bits). Modelling it as fresh (rather than a pinned constant 0) avoids
        // wrong-unsat when the formula asserts the partial result equals some
        // specific value, e.g. (= (_ bv9223372036854775807 64)
        // ((_ fp.to_sbv 64) RNE (_ +oo 11 53))) (#bug13).
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let unspec: Vec<CnfLit> = (0..bv_sz).map(|_| self.fresh_var()).collect();

        let x_is_nan = self.is_nan(&fp);
        let x_is_inf = self.is_infinite(&fp);
        let x_is_zero = self.is_zero(&fp);
        let c1 = self.make_or(x_is_nan, x_is_inf);
        let v2 = self.const_bv(0, bv_sz);

        let mut sig_ext = sig;
        debug_assert_eq!(sig_ext.len(), sbits);
        if sig_ext.len() < (bv_sz + 3) {
            let zero = self.const_false();
            let pad = bv_sz + 3 - sig_ext.len();
            let mut new_sig = vec![zero; pad];
            new_sig.extend_from_slice(&sig_ext);
            sig_ext = new_sig;
        }

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let exp_ext = self.sign_extend(&exp, ew - ebits);
        let lz_ext = self.zero_extend(&lz, ew - lz.len());
        let exp_m_lz = self.bv_sub(&exp_ext, &lz_ext);

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let zero = self.const_false();
        let mut big_sig = vec![zero];
        big_sig.extend_from_slice(&sig_ext);
        for _ in 0..(bv_sz + 2) {
            big_sig.push(zero);
        }
        let big_sig_sz = big_sig.len();

        let zero_exp = self.const_bv(0, ew);
        let is_neg_shift = self.bv_sle(&exp_m_lz, &zero_exp);
        let neg_exp_m_lz = self.bv_neg(&exp_m_lz);
        let shift_mag = self.make_ite_bits(is_neg_shift, &neg_exp_m_lz, &exp_m_lz);

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let shift = if ew < big_sig_sz {
            self.zero_extend(&shift_mag, big_sig_sz - ew)
        } else if ew > big_sig_sz {
            let upper = &shift_mag[big_sig_sz..];
            let lower: Vec<CnfLit> = shift_mag[..big_sig_sz].to_vec();
            let upper_zero = self.make_all_zero(upper);
            let cap = self.const_bv((big_sig_sz - 1) as u64, big_sig_sz);
            self.make_ite_bits(upper_zero, &lower, &cap)
        } else {
            shift_mag
        };

        let shift_limit = self.const_bv((bv_sz + 2) as u64, big_sig_sz);
        let shift_exceeds = self.make_unsigned_lt(&shift_limit, &shift);
        let capped_shift = self.make_ite_bits(shift_exceeds, &shift_limit, &shift);

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let right_shifted = self.bv_lshr(&big_sig, &capped_shift);
        let left_shifted = self.bv_shl(&big_sig, &capped_shift);
        let big_sig_shifted = self.make_ite_bits(is_neg_shift, &right_shifted, &left_shifted);

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let int_start = big_sig_sz - (bv_sz + 3);
        let int_part: Vec<CnfLit> = big_sig_shifted[int_start..big_sig_sz].to_vec();
        let last = big_sig_shifted[big_sig_sz - (bv_sz + 3)];
        let round = big_sig_shifted[big_sig_sz - (bv_sz + 4)];
        let stickies: Vec<CnfLit> = big_sig_shifted[..big_sig_sz - (bv_sz + 4)].to_vec();
        let sticky = if stickies.is_empty() {
            self.const_false()
        } else {
            self.bv_or_reduce(&stickies)
        };

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let inc = self.make_rounding_decision(rm, sgn, last, round, sticky);
        let mut inc_bv = self.const_bv(0, bv_sz + 3);
        inc_bv[0] = inc;
        let pre_rounded = self.bv_add(&int_part, &inc_bv);

        let pre_rounded_zero = self.make_all_zero(&pre_rounded);
        let ovfl = self.make_and(inc, pre_rounded_zero);

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let in_range = if !is_signed {
            let not_neg = -sgn;
            let ok_sign = self.make_or(not_neg, pre_rounded_zero);
            let not_ovfl = -ovfl;
            // SMT-LIB's bound is 2^m - 1, even when m exceeds a host word.
            let max_val = (BigInt::from(1u8) << bv_sz) - BigInt::from(1u8);
            let ul = self.const_bv_bigint(&max_val, bv_sz + 3);
            let exceeds = self.make_unsigned_lt(&ul, &pre_rounded);
            let not_exceeds = -exceeds;
            let t = self.make_and(ok_sign, not_ovfl);
            self.make_and(t, not_exceeds)
        } else {
            let one_bv = self.const_bv(1, bv_sz + 3);
            let neg1 = self.bv_neg(&one_bv);
            let pre_all_neg_one = self.bv_sle(&pre_rounded, &neg1);
            let ovfl_signed = self.make_or(ovfl, pre_all_neg_one);

            let neg_pre_rounded = self.bv_neg(&pre_rounded);
            let signed_result = self.make_ite_bits(sgn, &neg_pre_rounded, &pre_rounded);
            let not_ovfl = -ovfl_signed;

            // Compare in the existing m+3-bit circuit, without a u64 shift.
            let min_signed = BigInt::from(1u8) << (bv_sz - 1);
            let ll_mag = self.const_bv_bigint(&min_signed, bv_sz + 3);
            let ll = self.bv_neg(&ll_mag);
            let max_signed = &min_signed - BigInt::from(1u8);
            let ul = self.const_bv_bigint(&max_signed, bv_sz + 3);

            let below_min = self.bv_slt(&signed_result, &ll);
            let above_min = -below_min;
            let above_max = self.bv_slt(&ul, &signed_result);
            let below_max = -above_max;

            let in_bounds = self.make_and(above_min, below_max);
            self.make_and(not_ovfl, in_bounds)
        };

        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let rounded: Vec<CnfLit> = if is_signed {
            let neg_pre = self.bv_neg(&pre_rounded);
            let signed_val = self.make_ite_bits(sgn, &neg_pre, &pre_rounded);
            signed_val[..bv_sz].to_vec()
        } else {
            pre_rounded[..bv_sz].to_vec()
        };

        let not_in_range = -in_range;
        let r1 = self.make_ite_bits(not_in_range, &unspec, &rounded);
        let r2 = self.make_ite_bits(x_is_zero, &v2, &r1);
        let result = self.make_ite_bits(c1, &unspec, &r2);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        // Ackermannize the unspecified value so it remains free yet congruent.
        self.register_to_bv_unspec_site_with_control(&fp, rm, &unspec, is_signed, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Record a `fp.to_{s,u}bv` site and Ackermannize its unspecified value.
    ///
    /// The unspecified result on NaN/Inf/out-of-range is a fixed-but-unspecified
    /// bitvector (SMT-LIB partial function). Modelling it as fresh per site keeps
    /// it free (so `(= K (to_sbv +oo))` is satisfiable, #bug13), but congruence
    /// must still hold: two applications of the SAME function symbol to equal
    /// arguments must yield identical results (ay#8870). We enforce this
    /// pairwise: `inputs_equal → unspec_a == unspec_b`.
    ///
    /// # The function is `(rm, x) ↦ bv`, per format
    ///
    /// `((_ fp.to_ubv m) rm x)` is a function of BOTH arguments, so congruence
    /// relates two sites only when their rounding modes are equal as well:
    /// SMT-LIB leaves the value on NaN/Inf/out-of-range unspecified, not
    /// independent of `rm`, and z3 answers `sat` for
    /// `(distinct ((_ fp.to_ubv 3) RNE x) ((_ fp.to_ubv 3) RTZ x))` with
    /// `x = 12.0`. Keying on `(signedness, width, x)` alone forced those two
    /// values equal — the D7 wrong `unsat` (2026-09-23 hunt, witness w10).
    /// Each `(_ FloatingPoint eb sb)` instance is its own symbol too, so the
    /// inputs must share exponent AND significand width, not merely their
    /// total: `(3,5)` and `(4,4)` are both 8 bits wide, and comparing their
    /// fields bit-by-bit would relate values of two different sorts.
    ///
    /// Two literal modes are compared here, at encoding time; a symbolic mode
    /// contributes the premise `rm_a == rm_b` to the congruence clause.
    fn register_to_bv_unspec_site_with_control<C: BuildControl>(
        &mut self,
        input: &super::FpDecomposed,
        rm: RmOperand,
        unspec: &[CnfLit],
        is_signed: bool,
        control: &mut C,
    ) -> Result<(), C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let mut prior = Vec::new();
        for site in &self.to_bv_unspec_sites {
            control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
            let literal_modes_differ = matches!(
                (site.rm, rm),
                (RmOperand::Literal(a), RmOperand::Literal(b)) if a != b
            );
            if site.is_signed == is_signed
                && !literal_modes_differ
                && site.unspec.len() == unspec.len()
            {
                prior.push((site.input.clone(), site.rm, site.unspec.clone()));
            }
        }

        for (other_input, other_rm, other_unspec) in prior {
            control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
            // Inputs are comparable only in the same format; congruence does
            // not relate two different sorts' conversion functions.
            if other_input.exponent.len() != input.exponent.len()
                || other_input.significand.len() != input.significand.len()
            {
                continue;
            }
            let sign_eq = self.make_xnor(input.sign, other_input.sign);
            let exp_eq = self.make_bits_equal(&input.exponent, &other_input.exponent);
            let sig_eq = self.make_bits_equal(&input.significand, &other_input.significand);
            let se = self.make_and(sign_eq, exp_eq);
            let bit_equal = self.make_and(se, sig_eq);
            // Congruence is on the ABSTRACT FP value, not the bit encoding. SMT-LIB
            // FP has a single NaN, so two NaN inputs (any payload/sign) are equal
            // and must yield the same unspecified bv — matching structural `=`,
            // which also treats all NaN encodings as equal. Without this, after
            // `(= x y)` is satisfied by two distinct NaN encodings, `to_sbv(x)` and
            // `to_sbv(y)` were left free to differ (the `_not_sat` congruence canary
            // regressed to `unknown`).
            let x_nan = self.is_nan(input);
            let y_nan = self.is_nan(&other_input);
            let both_nan = self.make_and(x_nan, y_nan);
            let values_equal = self.make_or(both_nan, bit_equal);
            // Two literal modes reaching here are equal: no premise, and the
            // literal-mode CNF stays exactly what it was.
            let inputs_equal = match (rm, other_rm) {
                (RmOperand::Literal(_), RmOperand::Literal(_)) => values_equal,
                _ => {
                    let modes_equal = self.rm_equal(rm, other_rm);
                    self.make_and(values_equal, modes_equal)
                }
            };
            for (&a, &b) in unspec.iter().zip(other_unspec.iter()) {
                control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
                self.add_clause(ay_core::CnfClause::new(vec![-inputs_equal, -a, b]));
                self.add_clause(ay_core::CnfClause::new(vec![-inputs_equal, a, -b]));
            }
        }

        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        self.to_bv_unspec_sites.push(super::ToBvUnspecSite {
            input: input.clone(),
            rm,
            unspec: unspec.to_vec(),
            is_signed,
        });
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(())
    }

    /// Bit-blast equality between a BV-returning FP operation and another BV term.
    pub fn bitblast_bv_eq_with_to_bv(&mut self, to_bv_term: TermId, other_term: TermId) -> CnfLit {
        uninterrupted(|control| {
            self.bitblast_bv_eq_with_to_bv_with_control(to_bv_term, other_term, control)
        })
    }

    pub(crate) fn bitblast_bv_eq_with_to_bv_with_control<C: BuildControl>(
        &mut self,
        to_bv_term: TermId,
        other_term: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let result = (|| -> Result<CnfLit, C::Error> {
            let data = self.terms.get(to_bv_term).clone();

            if let TermData::App(ref sym, ref args) = data {
                if sym.name() == "fp.to_ieee_bv" && args.len() == 1 {
                    let bv_result = self.bitblast_to_ieee_bv_with_control(args[0], control)?;
                    let bv_sz = bv_result.len();
                    let other_bv =
                        self.bitblast_bv_term_with_control(other_term, bv_sz, control)?;
                    return Ok(self.make_bits_equal(&bv_result, &other_bv));
                }
            }

            let (is_signed, rm, fp_term, bv_sz) = match data {
                TermData::App(ref sym, ref args) if args.len() == 2 => {
                    let name = sym.name();
                    let is_signed = name == "fp.to_sbv";
                    let rm = self.rounding_operand_with_control(args[0], control)?;
                    let bv_width = match sym {
                        Symbol::Indexed(_, indices) if !indices.is_empty() => indices[0] as usize,
                        _ => match self.terms.sort(to_bv_term) {
                            Sort::BitVec(bv) => bv.width as usize,
                            _ => 32,
                        },
                    };
                    (is_signed, rm, args[1], bv_width)
                }
                _ => return Ok(self.const_false()),
            };

            let bv_result =
                self.bitblast_to_bv_with_control(fp_term, rm, bv_sz, is_signed, control)?;
            let other_bv = self.bitblast_bv_term_with_control(other_term, bv_sz, control)?;
            Ok(self.make_bits_equal(&bv_result, &other_bv))
        })()?;
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast `fp.to_ieee_bv`.
    ///
    /// # NaN is unspecified but still FUNCTIONAL
    ///
    /// A `(_ FloatingPoint eb sb)` sort has exactly ONE NaN element (SMT-LIB
    /// 2.6 FloatingPoint theory: all NaN bit-patterns denote the same value,
    /// which is why `(= (fp.neg NaN) NaN)` holds), but IEEE 754 has many NaN
    /// bit-patterns for it. `fp.to_ieee_bv` therefore leaves the returned
    /// pattern unspecified on NaN — *unspecified*, not non-functional: SMT-LIB
    /// 2.6 §5.2 makes every function symbol denote a total function and `=`
    /// denote identity, so equal arguments MUST give equal results.
    ///
    /// The internal decomposition cannot serve that role directly: `fp.neg`
    /// flips the raw sign bit even on NaN (IEEE 754-2008 §5.5.1), so the raw
    /// bits of `NaN` and `(fp.neg NaN)` differ although the two terms denote
    /// the same element. Returning the raw bits let AY refute the satisfiable
    /// `(= (fp.to_ieee_bv NaN) (fp.to_ieee_bv (fp.neg NaN)))` and report two
    /// different values for one function at one argument.
    ///
    /// Fix: on NaN return one fixed-but-unspecified NaN *encoding* per format,
    /// shared by every `fp.to_ieee_bv` site — free enough that no admissible
    /// pattern is refuted, single-valued enough to stay a function.
    pub fn bitblast_to_ieee_bv(&mut self, fp_term: TermId) -> Vec<CnfLit> {
        uninterrupted(|control| self.bitblast_to_ieee_bv_with_control(fp_term, control))
    }

    pub(crate) fn bitblast_to_ieee_bv_with_control<C: BuildControl>(
        &mut self,
        fp_term: TermId,
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let fp = self.get_fp_with_control(fp_term, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let exp_and_sig = Self::bv_concat(&fp.significand, &fp.exponent);
        let raw = Self::bv_concat(&exp_and_sig, &[fp.sign]);
        let is_nan = self.is_nan(&fp);
        let nan_encoding =
            self.ieee_nan_encoding_with_control(fp.exponent.len(), fp.significand.len(), control)?;
        let result = self.make_ite_bits(is_nan, &nan_encoding, &raw);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// The single fixed-but-unspecified IEEE NaN encoding of a format.
    ///
    /// Free in the sign bit and in the payload, but pinned to an actual NaN
    /// pattern (exponent all ones, stored significand non-zero) — a non-NaN
    /// result would contradict the operation's own definition (reinterpreting
    /// it back with `to_fp` must recover NaN). Cached per format so that all
    /// NaN arguments — necessarily equal, there being one NaN per sort — map
    /// to the same bitvector.
    fn ieee_nan_encoding_with_control<C: BuildControl>(
        &mut self,
        exp_bits: usize,
        sig_bits: usize,
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        if let Some(bits) = self.ieee_nan_encodings.get(&(exp_bits, sig_bits)) {
            let bits = bits.clone();
            control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
            return Ok(bits);
        }
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let significand: Vec<CnfLit> = (0..sig_bits).map(|_| self.fresh_var()).collect();
        // Payload non-zero: an all-zero significand with a max exponent is an
        // infinity encoding, not a NaN encoding.
        if !significand.is_empty() {
            self.add_clause(ay_core::CnfClause::new(significand.clone()));
        }
        let one = self.const_true();
        let exponent = vec![one; exp_bits];
        let sign = self.fresh_var();
        let exp_and_sig = Self::bv_concat(&significand, &exponent);
        let bits = Self::bv_concat(&exp_and_sig, &[sign]);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        self.ieee_nan_encodings
            .insert((exp_bits, sig_bits), bits.clone());
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(bits)
    }

    fn bitblast_bv_app_value_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        sym: &Symbol,
        args: &[TermId],
        expected_sz: usize,
        control: &mut C,
    ) -> Result<Option<Vec<CnfLit>>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let result = (|| -> Result<Option<Vec<CnfLit>>, C::Error> {
            Ok(match sym.name() {
                "fp.to_ieee_bv" if args.len() == 1 => {
                    let bits = self.bitblast_to_ieee_bv_with_control(args[0], control)?;
                    (bits.len() == expected_sz).then_some(bits)
                }
                "fp.to_ubv" | "fp.to_sbv" if args.len() == 2 => {
                    let bv_sz = match sym {
                        Symbol::Indexed(_, indices) if !indices.is_empty() => indices[0] as usize,
                        _ => match self.terms.sort(term) {
                            Sort::BitVec(bv) => bv.width as usize,
                            _ => expected_sz,
                        },
                    };
                    if bv_sz != expected_sz {
                        return Ok(None);
                    }
                    let is_signed = sym.name() == "fp.to_sbv";
                    let rm = self.rounding_operand_with_control(args[0], control)?;
                    Some(self.bitblast_to_bv_with_control(args[1], rm, bv_sz, is_signed, control)?)
                }
                "bvnot" if args.len() == 1 => {
                    let Some(bits) =
                        self.bitblast_bv_value_with_control(args[0], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    Some(bits.into_iter().map(|lit| -lit).collect())
                }
                "bvneg" if args.len() == 1 => {
                    let Some(bits) =
                        self.bitblast_bv_value_with_control(args[0], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    Some(self.bv_neg(&bits))
                }
                "bvadd" if args.len() >= 2 => {
                    let Some(mut acc) =
                        self.bitblast_bv_value_with_control(args[0], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    for &arg in &args[1..] {
                        let Some(rhs) =
                            self.bitblast_bv_value_with_control(arg, expected_sz, control)?
                        else {
                            return Ok(None);
                        };
                        acc = self.bv_add(&acc, &rhs);
                    }
                    Some(acc)
                }
                "bvsub" if args.len() == 2 => {
                    let Some(lhs) =
                        self.bitblast_bv_value_with_control(args[0], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    let Some(rhs) =
                        self.bitblast_bv_value_with_control(args[1], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    Some(self.bv_sub(&lhs, &rhs))
                }
                "bvmul" if args.len() >= 2 => {
                    let Some(mut acc) =
                        self.bitblast_bv_value_with_control(args[0], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    for &arg in &args[1..] {
                        let Some(rhs) =
                            self.bitblast_bv_value_with_control(arg, expected_sz, control)?
                        else {
                            return Ok(None);
                        };
                        acc = self.bv_mul_with_control(&acc, &rhs, control)?;
                    }
                    Some(acc)
                }
                "bvand" if args.len() >= 2 => {
                    let Some(mut acc) =
                        self.bitblast_bv_value_with_control(args[0], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    for &arg in &args[1..] {
                        let Some(rhs) =
                            self.bitblast_bv_value_with_control(arg, expected_sz, control)?
                        else {
                            return Ok(None);
                        };
                        acc = acc
                            .iter()
                            .zip(rhs.iter())
                            .map(|(&a, &b)| self.make_and(a, b))
                            .collect();
                    }
                    Some(acc)
                }
                "bvor" if args.len() >= 2 => {
                    let Some(mut acc) =
                        self.bitblast_bv_value_with_control(args[0], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    for &arg in &args[1..] {
                        let Some(rhs) =
                            self.bitblast_bv_value_with_control(arg, expected_sz, control)?
                        else {
                            return Ok(None);
                        };
                        acc = self.bv_or(&acc, &rhs);
                    }
                    Some(acc)
                }
                "bvxor" if args.len() >= 2 => {
                    let Some(mut acc) =
                        self.bitblast_bv_value_with_control(args[0], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    for &arg in &args[1..] {
                        let Some(rhs) =
                            self.bitblast_bv_value_with_control(arg, expected_sz, control)?
                        else {
                            return Ok(None);
                        };
                        acc = acc
                            .iter()
                            .zip(rhs.iter())
                            .map(|(&a, &b)| self.make_xor(a, b))
                            .collect();
                    }
                    Some(acc)
                }
                // Division and remainder — circuit, exactness obligations and their
                // oracle verdicts all live in `bv_division.rs`. Without this arm the
                // query bails to `unknown (:reason-unknown unsupported)`.
                "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod" => {
                    self.bitblast_bv_div_app_with_control(sym, args, expected_sz, control)?
                }
                "bvshl" if args.len() == 2 => {
                    let Some(lhs) =
                        self.bitblast_bv_value_with_control(args[0], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    let Some(shift_sz) = self.bv_width(args[1]) else {
                        return Ok(None);
                    };
                    let Some(rhs) =
                        self.bitblast_bv_value_with_control(args[1], shift_sz, control)?
                    else {
                        return Ok(None);
                    };
                    Some(self.bv_shl(&lhs, &rhs))
                }
                "bvlshr" if args.len() == 2 => {
                    let Some(lhs) =
                        self.bitblast_bv_value_with_control(args[0], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    let Some(shift_sz) = self.bv_width(args[1]) else {
                        return Ok(None);
                    };
                    let Some(rhs) =
                        self.bitblast_bv_value_with_control(args[1], shift_sz, control)?
                    else {
                        return Ok(None);
                    };
                    Some(self.bv_lshr(&lhs, &rhs))
                }
                "concat" if args.len() >= 2 => {
                    control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
                    let mut bits = Vec::with_capacity(expected_sz);
                    for &arg in args.iter().rev() {
                        let Some(width) = self.bv_width(arg) else {
                            return Ok(None);
                        };
                        let Some(arg_bits) =
                            self.bitblast_bv_value_with_control(arg, width, control)?
                        else {
                            return Ok(None);
                        };
                        bits.extend(arg_bits);
                    }
                    (bits.len() == expected_sz).then_some(bits)
                }
                "extract" if args.len() == 1 => {
                    let Symbol::Indexed(_, indices) = sym else {
                        return Ok(None);
                    };
                    if indices.len() != 2 {
                        return Ok(None);
                    }
                    let high = indices[0] as usize;
                    let low = indices[1] as usize;
                    if high < low {
                        return Ok(None);
                    }
                    let Some(width) = self.bv_width(args[0]) else {
                        return Ok(None);
                    };
                    if high >= width || high - low + 1 != expected_sz {
                        return Ok(None);
                    }
                    let Some(bits) =
                        self.bitblast_bv_value_with_control(args[0], width, control)?
                    else {
                        return Ok(None);
                    };
                    Some(bits[low..=high].to_vec())
                }
                "zero_extend" if args.len() == 1 => {
                    let Symbol::Indexed(_, indices) = sym else {
                        return Ok(None);
                    };
                    if indices.len() != 1 {
                        return Ok(None);
                    }
                    let extra = indices[0] as usize;
                    let Some(width) = self.bv_width(args[0]) else {
                        return Ok(None);
                    };
                    if width + extra != expected_sz {
                        return Ok(None);
                    }
                    let Some(bits) =
                        self.bitblast_bv_value_with_control(args[0], width, control)?
                    else {
                        return Ok(None);
                    };
                    Some(self.zero_extend(&bits, extra))
                }
                "sign_extend" if args.len() == 1 => {
                    let Symbol::Indexed(_, indices) = sym else {
                        return Ok(None);
                    };
                    if indices.len() != 1 {
                        return Ok(None);
                    }
                    let extra = indices[0] as usize;
                    let Some(width) = self.bv_width(args[0]) else {
                        return Ok(None);
                    };
                    if width + extra != expected_sz {
                        return Ok(None);
                    }
                    let Some(bits) =
                        self.bitblast_bv_value_with_control(args[0], width, control)?
                    else {
                        return Ok(None);
                    };
                    Some(self.sign_extend(&bits, extra))
                }
                // Name-form ITE over BV values. The elaborator produces `ite` as an
                // ordinary application (`App("ite", [c, t, e])`), not `TermData::Ite`
                // — without this arm a CSET-style lowering like
                // `(bvor (ite (fp.eq a b) #b1 #b0) (ite (fp.isNaN a) #b1 #b0))`
                // fell through to `None` and the whole QF_BVFP query bailed to
                // `unknown (:reason-unknown unsupported)` even though every piece
                // is bit-blastable (external-codegen UEQ lowering proofs, 2026-07-10).
                // Mirrors the `TermData::Ite` arm of `bitblast_bv_value`.
                "ite" if args.len() == 3 => {
                    let cond_lit = self.encode_bool_condition_with_control(args[0], control)?;
                    let Some(then_bits) =
                        self.bitblast_bv_value_with_control(args[1], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    let Some(else_bits) =
                        self.bitblast_bv_value_with_control(args[2], expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    Some(self.make_ite_bits(cond_lit, &then_bits, &else_bits))
                }
                _ if args.is_empty() => {
                    Some(self.bitblast_bv_term_with_control(term, expected_sz, control)?)
                }
                _ => {
                    self.bitblast_extra_bv_app_value_with_control(sym, args, expected_sz, control)?
                }
            })
        })()?;
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    pub(crate) fn bv_width(&self, term: TermId) -> Option<usize> {
        match self.terms.sort(term) {
            Sort::BitVec(bv) => Some(bv.width as usize),
            _ => None,
        }
    }

    fn unsupported_bv_value(&mut self, term: TermId, expected_sz: usize) -> Option<Vec<CnfLit>> {
        tracing::warn!(
            ?term,
            expected_sz,
            "FP bit-blasting: unsupported composite BV value, returning Unknown"
        );
        self.has_encoding_gap = true;
        None
    }

    /// Get BV bits for terms that the FP pipeline owns semantically.
    ///
    /// `fp.to_{s,u}bv` and `fp.to_ieee_bv` must expand to their conversion
    /// circuits. Composite BV terms that appear in FP-linked predicates are
    /// recursively encoded when supported and fail closed otherwise; only leaf
    /// BV values may allocate cached fresh bits.
    pub(crate) fn bitblast_bv_value(
        &mut self,
        term: TermId,
        expected_sz: usize,
    ) -> Option<Vec<CnfLit>> {
        uninterrupted(|control| self.bitblast_bv_value_with_control(term, expected_sz, control))
    }

    pub(crate) fn bitblast_bv_value_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        expected_sz: usize,
        control: &mut C,
    ) -> Result<Option<Vec<CnfLit>>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let result = (|| -> Result<Option<Vec<CnfLit>>, C::Error> {
            if let Some(val) = self.extract_bv_const(term) {
                let mut bits = Vec::with_capacity(expected_sz);
                for i in 0..expected_sz {
                    let bit_val = val.bit(i as u64);
                    bits.push(if bit_val {
                        self.const_true()
                    } else {
                        self.const_false()
                    });
                }
                return Ok(Some(bits));
            }

            if let Some(cached) = self.bv_term_bits.get(&term) {
                if cached.len() == expected_sz {
                    return Ok(Some(cached.clone()));
                }
                return Ok(self.unsupported_bv_value(term, expected_sz));
            }

            control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
            let data = self.terms.get(term).clone();
            let bits = match data {
                TermData::Const(_) | TermData::Var(..) => {
                    self.bitblast_bv_term_with_control(term, expected_sz, control)?
                }
                TermData::App(ref sym, ref args) => {
                    let Some(bits) = self.bitblast_bv_app_value_with_control(
                        term,
                        sym,
                        args,
                        expected_sz,
                        control,
                    )?
                    else {
                        return Ok(None);
                    };
                    bits
                }
                // A bitvector-sorted ITE (e.g. `(bvor (ite (fp.eq a b) #b1 #b0) ...)`
                // from a CSET-style lowering). Mirror the FP-value ITE path in
                // `decompose_fp`: encode the boolean condition and mux the two
                // branch bit-vectors. Without this the term fell through to the `_`
                // arm below and fail-closed as `unsupported`, defeating any BV op
                // (bvor/bvand/…) whose operand is a theory-conditioned select.
                TermData::Ite(cond, then_term, else_term) => {
                    let cond_lit = self.encode_bool_condition_with_control(cond, control)?;
                    let Some(then_bits) =
                        self.bitblast_bv_value_with_control(then_term, expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    let Some(else_bits) =
                        self.bitblast_bv_value_with_control(else_term, expected_sz, control)?
                    else {
                        return Ok(None);
                    };
                    self.make_ite_bits(cond_lit, &then_bits, &else_bits)
                }
                _ => return Ok(self.unsupported_bv_value(term, expected_sz)),
            };

            if bits.len() != expected_sz {
                return Ok(self.unsupported_bv_value(term, expected_sz));
            }

            control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
            if matches!(self.terms.get(term), TermData::App(..) | TermData::Ite(..)) {
                self.bv_term_bits.insert(term, bits.clone());
            }
            Ok(Some(bits))
        })()?;
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Get BV bits for a leaf term (constant or cached fresh variable).
    pub(crate) fn bitblast_bv_term(&mut self, term: TermId, expected_sz: usize) -> Vec<CnfLit> {
        uninterrupted(|control| self.bitblast_bv_term_with_control(term, expected_sz, control))
    }

    pub(crate) fn bitblast_bv_term_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        expected_sz: usize,
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let result = (|| -> Result<Vec<CnfLit>, C::Error> {
            Ok(if let Some(val) = self.extract_bv_const(term) {
                let mut bits = Vec::with_capacity(expected_sz);
                for i in 0..expected_sz {
                    let bit_val = val.bit(i as u64);
                    bits.push(if bit_val {
                        self.const_true()
                    } else {
                        self.const_false()
                    });
                }
                bits
            } else if let Some(cached) = self.bv_term_bits.get(&term) {
                cached.clone()
            } else {
                let cache_bits = match self.terms.get(term) {
                    TermData::Var(..) => true,
                    TermData::App(_, args) if args.is_empty() => true,
                    data => {
                        tracing::warn!(
                            ?term,
                            ?data,
                            expected_sz,
                            "FP bit-blasting: unsupported non-leaf BV term requested as leaf"
                        );
                        self.has_encoding_gap = true;
                        false
                    }
                };
                let mut bits = Vec::with_capacity(expected_sz);
                for _ in 0..expected_sz {
                    bits.push(self.fresh_var());
                }
                control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
                if cache_bits {
                    self.bv_term_bits.insert(term, bits.clone());
                }
                bits
            })
        })()?;
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Check if a BV term has cached bits from a prior `bitblast_bv_term` call.
    pub fn has_bv_bits(&self, term: TermId) -> bool {
        self.bv_term_bits.contains_key(&term)
    }

    /// Get the cached BV term -> CNF bit mappings.
    pub fn bv_term_bits(&self) -> &HashMap<TermId, Vec<CnfLit>> {
        &self.bv_term_bits
    }

    /// Bit-blast a BV equality `(= a b)` in the FP solver's variable space.
    pub fn bitblast_bv_eq(&mut self, a: TermId, b: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_bv_eq_with_control(a, b, control))
    }

    pub(crate) fn bitblast_bv_eq_with_control<C: BuildControl>(
        &mut self,
        a: TermId,
        b: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let result = (|| -> Result<CnfLit, C::Error> {
            let a_sort = self.terms.sort(a).clone();
            let bv_sz = match a_sort {
                Sort::BitVec(bvs) => bvs.width as usize,
                _ => return Ok(self.const_false()),
            };
            let a_bits = self.bitblast_bv_term_with_control(a, bv_sz, control)?;
            let b_bits = self.bitblast_bv_term_with_control(b, bv_sz, control)?;
            Ok(self.make_bits_equal(&a_bits, &b_bits))
        })()?;
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast a BV equality `(= a b)` without ever failing open.
    ///
    /// Unlike [`Self::bitblast_bv_eq`], composite operands are encoded through
    /// the supported-op path and an unsupported operand yields `None` instead
    /// of fresh unconstrained leaf bits. Callers that need a *sound* premise
    /// (congruence, for instance) must use this and treat `None` as "cannot
    /// encode" rather than as a free literal.
    pub fn try_bitblast_bv_eq(&mut self, a: TermId, b: TermId) -> Option<CnfLit> {
        uninterrupted(|control| self.try_bitblast_bv_eq_with_control(a, b, control))
    }

    pub(crate) fn try_bitblast_bv_eq_with_control<C: BuildControl>(
        &mut self,
        a: TermId,
        b: TermId,
        control: &mut C,
    ) -> Result<Option<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let result = (|| -> Result<Option<CnfLit>, C::Error> {
            let a_sort = self.terms.sort(a).clone();
            if a_sort != *self.terms.sort(b) {
                return Ok(None);
            }
            let Sort::BitVec(bv_sort) = a_sort else {
                return Ok(None);
            };
            let bv_sz = bv_sort.width as usize;
            let Some(a_bits) = self.bitblast_bv_value_with_control(a, bv_sz, control)? else {
                return Ok(None);
            };
            let Some(b_bits) = self.bitblast_bv_value_with_control(b, bv_sz, control)? else {
                return Ok(None);
            };
            Ok(Some(self.make_bits_equal(&a_bits, &b_bits)))
        })()?;
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bit-blast a BV predicate in the FP solver's variable space.
    pub fn bitblast_bv_predicate(&mut self, term: TermId) -> Option<CnfLit> {
        uninterrupted(|control| self.bitblast_bv_predicate_with_control(term, control))
    }

    pub(crate) fn bitblast_bv_predicate_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        control: &mut C,
    ) -> Result<Option<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let result = (|| -> Result<Option<CnfLit>, C::Error> {
            let data = self.terms.get(term).clone();

            let TermData::App(ref sym, ref args) = data else {
                return Ok(None);
            };
            if args.len() != 2 {
                return Ok(None);
            }

            let a_sort = self.terms.sort(args[0]).clone();
            if !matches!(a_sort, Sort::BitVec(..)) || a_sort != *self.terms.sort(args[1]) {
                return Ok(None);
            }
            let Sort::BitVec(bv_sort) = a_sort else {
                return Ok(None);
            };
            let bv_sz = bv_sort.width as usize;

            let Some(a_bits) = self.bitblast_bv_value_with_control(args[0], bv_sz, control)? else {
                return Ok(None);
            };
            let Some(b_bits) = self.bitblast_bv_value_with_control(args[1], bv_sz, control)? else {
                return Ok(None);
            };

            Ok(match sym.name() {
                "=" => Some(self.make_bits_equal(&a_bits, &b_bits)),
                "distinct" => Some(-self.make_bits_equal(&a_bits, &b_bits)),
                "bvult" => Some(self.make_unsigned_lt(&a_bits, &b_bits)),
                "bvule" => Some(-self.make_unsigned_lt(&b_bits, &a_bits)),
                "bvugt" => Some(self.make_unsigned_lt(&b_bits, &a_bits)),
                "bvuge" => Some(-self.make_unsigned_lt(&a_bits, &b_bits)),
                "bvslt" => Some(self.bv_slt(&a_bits, &b_bits)),
                "bvsle" => Some(self.bv_sle(&a_bits, &b_bits)),
                "bvsgt" => Some(self.bv_slt(&b_bits, &a_bits)),
                "bvsge" => Some(self.bv_sle(&b_bits, &a_bits)),
                _ => None,
            })
        })()?;
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }
}
