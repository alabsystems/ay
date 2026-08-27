// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The SMT-LIB `FixedSizeBitVectors` division and remainder family, bit-blasted
//! in the FP solver's variable space.
//!
//! `bitblast_bv_app_value` used to have no arm for these five operators, so any
//! QF_BVFP query mentioning one fell through to `None`, `bitblast_bv_predicate`
//! propagated the `None`, and `solve_fp` published
//! `unknown (:reason-unknown unsupported)` in ~0.02 s — a pure capability gap
//! that declined with zero search.
//!
//! # Exactness
//!
//! The encoding is two layers and each is discharged as an SMT obligation
//! rather than argued here. The generators live in `verification/fp-bv-division`
//! and the verdicts, oracle versions and runtimes in
//! the development design notes.
//!
//! * **Sign fix-up** ([`FpSolver::bv_div_family`]) — AY normalises to
//!   magnitudes, calls the unsigned divider **once**, and fixes the sign;
//!   SMT-LIB instead defines `bvsdiv`/`bvsrem`/`bvsmod` by a four-way case split
//!   over four divider calls. That the two agree holds for *any* function in the
//!   divider's place, so obligations `U3`/`U4`/`U5` state it with the divider
//!   uninterpreted: **`unsat` at width 32 on z3 4.16.0, cvc5 1.3.0 and bitwuzla
//!   0.9.1**, with mutants `U3N`/`U4N`/`U5N` `sat` on all three.
//! * **Unsigned divider** ([`FpSolver::bv_udiv_urem`], pre-existing) —
//!   obligations `O1`/`O2` and the fused `O6`/`O7` are `unsat` on all three
//!   oracles at widths 4, 8, 12 and 16, and `O1` also at 20. The direct miter
//!   does not scale to 32 (bitwuzla: 4 s / 45 s / 556 s / >600 s at 12 / 16 /
//!   20 / 24), so at width 32 the report records what *is* discharged there:
//!   `FR` (the surviving remainder is `<u` the divisor), `Z` and `Szz` (the
//!   `b = 0` case, which the loop gets right with no special case) and the
//!   `S24`/`S31` slices of the divisor case split.
//!
//! Taking the magnitude with a two's-complement negation is exact at `INT_MIN`
//! too: `bvneg INT_MIN = INT_MIN`, whose *unsigned* value `2^(n-1)` is the true
//! magnitude, and the divider that consumes it is unsigned.

use ay_core::term::{Symbol, TermId};
use ay_core::CnfLit;

use super::FpSolver;

/// The five SMT-LIB division/remainder operators [`FpSolver::bv_div_family`]
/// bit-blasts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BvDivOp {
    Udiv,
    Urem,
    Sdiv,
    Srem,
    Smod,
}

impl BvDivOp {
    /// Map an SMT-LIB symbol name onto the operator, or `None` if the name is
    /// not one of the five.
    pub(crate) fn from_name(name: &str) -> Option<Self> {
        match name {
            "bvudiv" => Some(Self::Udiv),
            "bvurem" => Some(Self::Urem),
            "bvsdiv" => Some(Self::Sdiv),
            "bvsrem" => Some(Self::Srem),
            "bvsmod" => Some(Self::Smod),
            _ => None,
        }
    }
}

impl FpSolver<'_> {
    /// Bit-blast an application of one of the five operators.
    ///
    /// Both operands and the result share one width in SMT-LIB, so the width
    /// check is a redundancy guard rather than a conversion: a term whose
    /// declared sort disagrees fails closed instead of being blasted at the
    /// wrong width.
    pub(crate) fn bitblast_bv_div_app(
        &mut self,
        sym: &Symbol,
        args: &[TermId],
        expected_sz: usize,
    ) -> Option<Vec<CnfLit>> {
        let op = BvDivOp::from_name(sym.name())?;
        if args.len() != 2
            || self.bv_width(args[0])? != expected_sz
            || self.bv_width(args[1])? != expected_sz
        {
            return None;
        }
        let lhs = self.bitblast_bv_value(args[0], expected_sz)?;
        let rhs = self.bitblast_bv_value(args[1], expected_sz)?;
        Some(self.bv_div_family(op, &lhs, &rhs))
    }

    /// Emit the circuit for `op` over already-blasted operand bits.
    ///
    /// See the module docs for what is proven and where.
    pub(crate) fn bv_div_family(&mut self, op: BvDivOp, a: &[CnfLit], b: &[CnfLit]) -> Vec<CnfLit> {
        let n = a.len();
        debug_assert_eq!(n, b.len());
        debug_assert!(n > 0);

        if matches!(op, BvDivOp::Udiv | BvDivOp::Urem) {
            let (quot, rem) = self.bv_udiv_urem(a, b);
            return if matches!(op, BvDivOp::Udiv) {
                quot
            } else {
                rem
            };
        }

        // Signed operators: normalise to magnitudes, divide unsigned, fix signs.
        let msb_a = a[n - 1];
        let msb_b = b[n - 1];
        let neg_a = self.bv_neg(a);
        let neg_b = self.bv_neg(b);
        let abs_a = self.make_ite_bits(msb_a, &neg_a, a);
        let abs_b = self.make_ite_bits(msb_b, &neg_b, b);
        let (quot, rem) = self.bv_udiv_urem(&abs_a, &abs_b);

        match op {
            BvDivOp::Udiv | BvDivOp::Urem => unreachable!("handled above"),
            BvDivOp::Sdiv => {
                // Negate the quotient iff the operand signs differ.
                let signs_differ = self.make_xor(msb_a, msb_b);
                let neg_quot = self.bv_neg(&quot);
                self.make_ite_bits(signs_differ, &neg_quot, &quot)
            }
            BvDivOp::Srem => {
                // The remainder takes the sign of the DIVIDEND.
                let neg_rem = self.bv_neg(&rem);
                self.make_ite_bits(msb_a, &neg_rem, &rem)
            }
            BvDivOp::Smod => self.bv_smod_fixup(msb_a, msb_b, &rem, b),
        }
    }

    /// The `bvsmod` sign fix-up: the SMT-LIB nested `ite`, built innermost out.
    ///
    /// ```text
    ///   u = 0            -> u          |  msb_s & !msb_t -> -u + t
    ///   !msb_s & !msb_t  -> u          | !msb_s &  msb_t ->  u + t
    ///   otherwise        -> -u
    /// ```
    fn bv_smod_fixup(
        &mut self,
        msb_a: CnfLit,
        msb_b: CnfLit,
        rem: &[CnfLit],
        b: &[CnfLit],
    ) -> Vec<CnfLit> {
        let neg_rem = self.bv_neg(rem);
        let neg_rem_plus_b = self.bv_add(&neg_rem, b);
        let rem_plus_b = self.bv_add(rem, b);

        let mut result = neg_rem.clone();

        let not_msb_a = -msb_a;
        let pos_neg = self.make_and(not_msb_a, msb_b);
        result = self.make_ite_bits(pos_neg, &rem_plus_b, &result);

        let not_msb_b = -msb_b;
        let neg_pos = self.make_and(msb_a, not_msb_b);
        result = self.make_ite_bits(neg_pos, &neg_rem_plus_b, &result);

        let pos_pos = self.make_and(not_msb_a, not_msb_b);
        result = self.make_ite_bits(pos_pos, rem, &result);

        let rem_nonzero = self.make_any_nonzero(rem);
        let rem_zero = -rem_nonzero;
        self.make_ite_bits(rem_zero, rem, &result)
    }
}
