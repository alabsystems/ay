// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Division by a power of two, encoded as the reciprocal multiply.
//!
//! # Why (#fp-div-pow2)
//!
//! The FP divider is by a wide margin the most expensive circuit this
//! bit-blaster emits. Measured on one Float32 obligation
//! (`r = x / 2.0` with `r` pinned to `+zero`, refuted):
//!
//! ```text
//!   fp.div RNE x 2.0    88,970 vars   91,577 clauses   7.4 s
//!   fp.mul RNE x 0.5    18,201 vars   12,228 clauses   0.9 s
//! ```
//!
//! Same verdict, 7.5x fewer clauses, 8x less wall. Division by a power of two
//! is how real programs halve, average and rescale, so this is not a corner:
//! in the SMT-LIB 2025 `ABVFPLRA/…/exp_loop_true-unreach-call.c` benchmark all
//! 531 `fp.div` applications divide by a power of two, and 316 of them sit
//! under a quantifier whose decision procedure has to refute through the
//! divider.
//!
//! This is the same move [`FpSolver::try_make_fma_zero_factor`] makes for
//! `fma` with a zero multiplicand: recognise a constant operand at decompose
//! time and emit a cheaper — but semantically identical — circuit.
//!
//! # Why it is exact, for every input and every rounding mode
//!
//! Let `c = ±2^k` be finite, non-zero and normal, with `1/c = ±2^-k` also
//! normal (so exactly representable, with a zero significand). IEEE 754-2019
//! §5.4.1 defines both `x / c` and `x * (1/c)` as *the exact arithmetic
//! result, rounded once* under the ambient mode. The two exact results are the
//! same real number, so the two rounded results are the same float — bit for
//! bit, including throughout the subnormal range, where both round the
//! identical exact value. Overflow and underflow are decided by that shared
//! exact result, so they cannot diverge either.
//!
//! The non-finite and zero cases agree operation-class by operation-class,
//! because `c` is finite and non-zero and so is `1/c`:
//!
//! ```text
//!   x = NaN     NaN / c = NaN            NaN * (1/c) = NaN
//!   x = ±inf    ±inf / finite≠0 = ±inf   ±inf * finite≠0 = ±inf
//!   x = ±0      ±0 / finite≠0 = ±0       ±0 * finite≠0 = ±0
//! ```
//!
//! and the sign rule is the same XOR in both directions, `sign(x) ^ sign(c)`,
//! with `sign(1/c) = sign(c)`.
//!
//! The `1/c` normality requirement is doing real work and is checked, not
//! assumed: for the largest normal power of two (`2^127` at Float32) the
//! reciprocal `2^-127` is *subnormal*, is not the zero-significand constant
//! this module would build, and so that divisor is declined and the full
//! divider runs.
//!
//! # Recognising the divisor
//!
//! [`FpSolver::pow2_value`] reads a syntactic term and returns the exact
//! `±2^k` it denotes, or nothing. It descends through `fp.mul`, `fp.div`,
//! `fp.neg` and `fp.abs` because that is how these divisors are actually
//! written — `exp_loop` spells `1.0` as `(fp.mul RNE 0.5 2.0)` 262 times, and
//! 95 of its 228 negated-existential assertions divide by such a term.
//!
//! Descending is exact for the same reason the top-level rewrite is: a product
//! or quotient of two powers of two is a power of two, and when the RESULT IS
//! ITSELF NORMAL no rounding occurs, so every rounding mode agrees and the
//! mode operand can be ignored. That normality check is applied at EVERY node,
//! not just at the root — `2^100 * 2^100` at Float32 is `+oo`, not `2^200`,
//! and a recogniser that only checked the root would have folded it to a
//! finite value and changed the answer.

use ay_core::term::{Constant, TermData, TermId};
use num_bigint::BigInt;

use super::{FpDecomposed, FpPrecision, FpSolver, RoundingMode};

/// Recursion depth for [`FpSolver::pow2_value`].
///
/// The recogniser is a DAG walk with two children per node and no memo, so
/// this bounds its work at a few hundred visits per `fp.div`. The constant
/// divisors that motivate it nest one deep; the margin is for hand-written
/// spellings, not for arbitrary expressions.
const POW2_MAX_DEPTH: u32 = 8;

/// The IEEE fields of a syntactically concrete FP constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FpConstFields {
    /// Sign bit: `true` is negative.
    negative: bool,
    /// Biased exponent field.
    biased_exponent: u32,
    /// Whether the STORED significand (hidden bit excluded) is all zero.
    significand_zero: bool,
}

/// An exact `±2^unbiased_exponent`, known to be a NORMAL value of its format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Pow2Value {
    negative: bool,
    /// Unbiased exponent `k`, i.e. the value is `±2^k`.
    unbiased_exponent: i64,
}

impl FpSolver<'_> {
    /// The IEEE fields of `term`, if it is a concrete FP constant of
    /// `precision`.
    ///
    /// Recognises the two spellings a constant reaches decomposition in:
    ///
    /// * `((_ to_fp eb sb) <BV literal>)` — the one-argument *reinterpret*
    ///   form. Every source-level FP literal arrives this way, because
    ///   `fold_to_fp_real_constants` rewrites `((_ to_fp 8 24) RNE 2.0)` into
    ///   it before the theory ever sees the term.
    /// * `(fp <bv1> <bv_eb> <bv_(sb-1)>)` — the explicit triple.
    ///
    /// Everything else — symbolic terms, `+oo`, `NaN`, `+zero`, a `to_fp` over
    /// a non-literal BV — returns `None`.
    fn fp_const_fields(&self, term: TermId, precision: FpPrecision) -> Option<FpConstFields> {
        let eb = precision.exponent_bits();
        let stored = precision.significand_bits() - 1;
        let TermData::App(sym, args) = self.terms.get(term) else {
            return None;
        };
        match sym.name() {
            "to_fp" if args.len() == 1 => {
                // The BV must be exactly this format's width, and the symbol's
                // own indices must name this format. Reading a `(_ to_fp 5 11)`
                // literal with Float32 field offsets would decode a different
                // number and hand back a confident wrong answer, so neither is
                // assumed from the enclosing operation's sort.
                let ay_core::term::Symbol::Indexed(_, indices) = sym else {
                    return None;
                };
                if !matches!(indices.as_slice(),
                    [format_eb, format_sb]
                        if *format_eb == eb && *format_sb == precision.significand_bits())
                {
                    return None;
                }
                let bits = self.const_bv_field(args[0], precision.total_bits())?;
                let negative = bits.bit(u64::from(precision.total_bits()) - 1);
                let mut biased_exponent: u32 = 0;
                for i in 0..eb {
                    if bits.bit(u64::from(stored) + u64::from(i)) {
                        biased_exponent |= 1 << i;
                    }
                }
                Some(FpConstFields {
                    negative,
                    biased_exponent,
                    significand_zero: (0..stored).all(|i| !bits.bit(u64::from(i))),
                })
            }
            "fp" if args.len() == 3 => {
                let sign = self.const_bv_field(args[0], 1)?;
                let exponent = self.const_bv_field(args[1], eb)?;
                let significand = self.const_bv_field(args[2], stored)?;
                Some(FpConstFields {
                    negative: sign == BigInt::from(1),
                    biased_exponent: u32::try_from(exponent).ok()?,
                    significand_zero: significand == BigInt::from(0),
                })
            }
            _ => None,
        }
    }

    /// A constant BV operand of exactly `width` bits, as a non-negative
    /// integer. Width is checked so a malformed `(fp ...)` triple cannot be
    /// read as a well-formed constant of a different format.
    fn const_bv_field(&self, term: TermId, width: u32) -> Option<BigInt> {
        match self.terms.get(term) {
            TermData::Const(Constant::BitVec { value, width: w })
                if *w == width && value.sign() != num_bigint::Sign::Minus =>
            {
                Some(value.clone())
            }
            _ => None,
        }
    }

    /// `±2^k` as a NORMAL value of `precision`, or `None` if `k` is out of the
    /// normal exponent range.
    ///
    /// Every constructor of [`Pow2Value`] goes through here, so "the value is
    /// exactly `±2^k` AND representable without rounding" is an invariant of
    /// the type rather than a fact each caller has to re-check.
    fn normal_pow2(
        precision: FpPrecision,
        negative: bool,
        unbiased_exponent: i64,
    ) -> Option<Pow2Value> {
        let biased = unbiased_exponent.checked_add(i64::from(precision.bias()))?;
        if biased < 1 || biased >= i64::from(precision.max_exponent()) {
            return None;
        }
        Some(Pow2Value {
            negative,
            unbiased_exponent,
        })
    }

    /// The exact `±2^k` that `term` denotes, when that is decidable from its
    /// syntax and the value is a normal float of `precision`.
    ///
    /// See the module docs for why descending through `fp.mul` / `fp.div` is
    /// rounding-mode-independent, and why the normality check has to hold at
    /// every node rather than only at the root.
    pub(crate) fn pow2_value(
        &self,
        term: TermId,
        precision: FpPrecision,
        depth: u32,
    ) -> Option<Pow2Value> {
        if let Some(fields) = self.fp_const_fields(term, precision) {
            // A power of two has an all-zero stored significand AND a normal
            // exponent. Excluding exponent 0 excludes ±0 and the subnormals;
            // excluding the all-ones exponent excludes ±inf and NaN.
            if !fields.significand_zero
                || fields.biased_exponent == 0
                || fields.biased_exponent >= precision.max_exponent()
            {
                return None;
            }
            return Some(Pow2Value {
                negative: fields.negative,
                unbiased_exponent: i64::from(fields.biased_exponent) - i64::from(precision.bias()),
            });
        }
        if depth == 0 {
            return None;
        }
        let TermData::App(sym, args) = self.terms.get(term) else {
            return None;
        };
        match sym.name() {
            // Sign-bit operations; exact by definition, no rounding involved.
            "fp.neg" if args.len() == 1 => {
                let inner = self.pow2_value(args[0], precision, depth - 1)?;
                Some(Pow2Value {
                    negative: !inner.negative,
                    ..inner
                })
            }
            "fp.abs" if args.len() == 1 => {
                let inner = self.pow2_value(args[0], precision, depth - 1)?;
                Some(Pow2Value {
                    negative: false,
                    ..inner
                })
            }
            // `2^i * 2^j = 2^(i+j)` and `2^i / 2^j = 2^(i-j)`, EXACTLY, so
            // long as the result is itself normal — which `normal_pow2`
            // checks. The rounding-mode operand `args[0]` is therefore
            // irrelevant and is deliberately not read.
            "fp.mul" | "fp.div" if args.len() == 3 => {
                let lhs = self.pow2_value(args[1], precision, depth - 1)?;
                let rhs = self.pow2_value(args[2], precision, depth - 1)?;
                let exponent = if sym.name() == "fp.mul" {
                    lhs.unbiased_exponent.checked_add(rhs.unbiased_exponent)?
                } else {
                    lhs.unbiased_exponent.checked_sub(rhs.unbiased_exponent)?
                };
                Self::normal_pow2(precision, lhs.negative != rhs.negative, exponent)
            }
            _ => None,
        }
    }

    /// `x / c` as `x * (1/c)` when `c` is a power of two whose reciprocal is a
    /// normal float; otherwise `None`, and the caller builds the full divider.
    ///
    /// See the module docs for why the two are the same value for every input
    /// and every rounding mode, and for the measured reason it is worth
    /// recognising.
    pub(crate) fn try_make_div_by_power_of_two(
        &mut self,
        x_term: TermId,
        y_term: TermId,
        rm: RoundingMode,
        precision: FpPrecision,
    ) -> Option<FpDecomposed> {
        let divisor = self.pow2_value(y_term, precision, POW2_MAX_DEPTH)?;
        // `1/c` must itself be a normal power of two, or it is not the
        // zero-significand constant built below.
        let reciprocal =
            Self::normal_pow2(precision, divisor.negative, -divisor.unbiased_exponent)?;
        // `normal_pow2` has already established `1 <= biased < max_exponent`,
        // so this conversion cannot fail; declining rather than panicking keeps
        // the whole module total, and a decline is only ever the slower path.
        let biased =
            u32::try_from(reciprocal.unbiased_exponent + i64::from(precision.bias())).ok()?;
        let constant = self.fresh_decomposed(precision);
        self.constrain_constant(
            &constant,
            reciprocal.negative,
            |i| biased & (1 << i) != 0,
            |_| false,
        );
        let x = self.get_fp(x_term);
        Some(self.make_mul(&x, &constant, rm))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::term::{Symbol, TermStore};
    use ay_core::Sort;

    fn f32_sort() -> Sort {
        Sort::FloatingPoint(8, 24)
    }

    fn rm_sort() -> Sort {
        Sort::Uninterpreted("RoundingMode".to_string())
    }

    /// `((_ to_fp 8 24) <bits>)`, the folded-literal spelling.
    fn f32_literal(terms: &mut TermStore, bits: u32) -> TermId {
        let bv = terms.mk_bitvec(BigInt::from(bits), 32);
        terms.mk_app(Symbol::indexed("to_fp", vec![8, 24]), vec![bv], f32_sort())
    }

    /// The same bit pattern wearing ANOTHER format's indices. Decoding it with
    /// Float32 field offsets would yield a confident wrong value, so the
    /// recogniser must decline it.
    fn mislabelled_literal(terms: &mut TermStore, bits: u32) -> TermId {
        let bv = terms.mk_bitvec(BigInt::from(bits), 32);
        terms.mk_app(Symbol::indexed("to_fp", vec![9, 23]), vec![bv], f32_sort())
    }

    fn rne(terms: &mut TermStore) -> TermId {
        terms.mk_app(Symbol::named("RNE"), vec![], rm_sort())
    }

    fn fp_app(terms: &mut TermStore, name: &str, args: Vec<TermId>) -> TermId {
        terms.mk_app(Symbol::named(name), args, f32_sort())
    }

    fn pow2_of(terms: &TermStore, term: TermId) -> Option<i64> {
        let solver = FpSolver::new(terms);
        solver
            .pow2_value(term, FpPrecision::Float32, POW2_MAX_DEPTH)
            .map(|v| v.unbiased_exponent)
    }

    #[test]
    fn recognises_plain_power_of_two_literals() {
        let mut terms = TermStore::new();
        // 2.0 = 0x40000000, 0.5 = 0x3f000000, 1.0 = 0x3f800000.
        let two = f32_literal(&mut terms, 0x4000_0000);
        let half = f32_literal(&mut terms, 0x3f00_0000);
        let one = f32_literal(&mut terms, 0x3f80_0000);
        assert_eq!(pow2_of(&terms, two), Some(1));
        assert_eq!(pow2_of(&terms, half), Some(-1));
        assert_eq!(pow2_of(&terms, one), Some(0));
    }

    #[test]
    fn rejects_a_literal_labelled_with_another_format() {
        let mut terms = TermStore::new();
        // 0x40000000 is 2.0 read as (8,24); as (9,23) it is a different value.
        let mislabelled = mislabelled_literal(&mut terms, 0x4000_0000);
        assert_eq!(pow2_of(&terms, mislabelled), None);
    }

    #[test]
    fn rejects_non_powers_of_two_and_specials() {
        let mut terms = TermStore::new();
        // 3.0 = 0x40400000 (non-zero significand), +0 = 0x00000000,
        // +oo = 0x7f800000, NaN = 0x7fc00000, min subnormal = 0x00000001.
        for bits in [
            0x4040_0000,
            0x0000_0000,
            0x7f80_0000,
            0x7fc0_0000,
            0x0000_0001,
        ] {
            let term = f32_literal(&mut terms, bits);
            assert_eq!(
                pow2_of(&terms, term),
                None,
                "bits {bits:#x} must be declined"
            );
        }
    }

    #[test]
    fn descends_through_exact_constant_products() {
        let mut terms = TermStore::new();
        let rm = rne(&mut terms);
        let two = f32_literal(&mut terms, 0x4000_0000);
        let half = f32_literal(&mut terms, 0x3f00_0000);
        // (fp.mul RNE 0.5 2.0) = 1.0 = 2^0, exactly.
        let product = fp_app(&mut terms, "fp.mul", vec![rm, half, two]);
        assert_eq!(pow2_of(&terms, product), Some(0));
        // (fp.div RNE 0.5 2.0) = 0.25 = 2^-2, exactly.
        let quotient = fp_app(&mut terms, "fp.div", vec![rm, half, two]);
        assert_eq!(pow2_of(&terms, quotient), Some(-2));
    }

    /// The check the module docs single out: `2^100 * 2^100` is `+oo` at
    /// Float32, NOT `2^200`, so the recogniser must decline the product even
    /// though both operands are powers of two.
    #[test]
    fn declines_products_that_leave_the_normal_range() {
        let mut terms = TermStore::new();
        let rm = rne(&mut terms);
        // 2^100 has biased exponent 227 = 0xe3 -> 0x71800000.
        let big = f32_literal(&mut terms, 0x7180_0000);
        assert_eq!(pow2_of(&terms, big), Some(100));
        let overflow = fp_app(&mut terms, "fp.mul", vec![rm, big, big]);
        assert_eq!(pow2_of(&terms, overflow), None);
        // 2^-100 (biased 27 = 0x1b -> 0x0d800000); the product underflows.
        let tiny = f32_literal(&mut terms, 0x0d80_0000);
        assert_eq!(pow2_of(&terms, tiny), Some(-100));
        let underflow = fp_app(&mut terms, "fp.mul", vec![rm, tiny, tiny]);
        assert_eq!(pow2_of(&terms, underflow), None);
    }

    /// Dividing by the largest normal power of two must be DECLINED: its
    /// reciprocal `2^-127` is subnormal, so the reciprocal-multiply this
    /// module builds would be a different function.
    #[test]
    fn declines_divisor_whose_reciprocal_is_subnormal() {
        let mut terms = TermStore::new();
        // 2^127: biased exponent 254 = 0xfe -> 0x7f000000.
        let huge = f32_literal(&mut terms, 0x7f00_0000);
        assert_eq!(pow2_of(&terms, huge), Some(127));
        let x = terms.mk_var("x", f32_sort());
        let mut solver = FpSolver::new(&terms);
        assert!(solver
            .try_make_div_by_power_of_two(x, huge, RoundingMode::RNE, FpPrecision::Float32)
            .is_none());
    }

    /// The rewrite must FIRE, and firing must be cheaper. A divisor of 2.0 and
    /// a divisor of 3.0 differ only in one bit of a literal, so any drop this
    /// large is the divider circuit not being built.
    #[test]
    fn power_of_two_divisor_emits_a_far_smaller_circuit() {
        fn clauses_for(divisor_bits: u32) -> usize {
            let mut terms = TermStore::new();
            let rm = rne(&mut terms);
            let x = terms.mk_var("x", f32_sort());
            let divisor = f32_literal(&mut terms, divisor_bits);
            let div = fp_app(&mut terms, "fp.div", vec![rm, x, divisor]);
            let mut solver = FpSolver::new(&terms);
            let _ = solver.get_fp(div);
            solver.clauses().len()
        }
        let pow2 = clauses_for(0x4000_0000); // 2.0
        let other = clauses_for(0x4040_0000); // 3.0
        assert!(
            pow2 * 4 < other,
            "div-by-2.0 should not build the divider: {pow2} clauses vs {other} for div-by-3.0"
        );
    }
}
