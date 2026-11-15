// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Collecting a [`BvPolyFingerprint`] from a term.

use super::super::{NormalizeBvArith, BV_NORM_STACK_RED_ZONE, BV_NORM_STACK_SIZE};
use super::{Atom, BvLinearBudget, BvPolyFingerprint, PolyRelation, BV_LINEAR_MAX_WIDTH};

#[path = "fingerprint_narrow.rs"]
mod narrow;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive};

impl NormalizeBvArith {
    /// Prove two same-width BV terms equal by comparing canonical polynomials
    /// in `Z / 2^width`. Failure to recognize or stay within budget simply
    /// declines the fold.
    ///
    /// The conclusion is strictly one-sided: equal fingerprints prove equality
    /// under every assignment (folding `=` to true is verdict-preserving), but
    /// a mismatch concludes NOTHING and falls through to bit-blasting —
    /// formally distinct polynomials can still be semantically equal (at
    /// width 1, `x*x` and `x` agree everywhere yet differ formally).
    #[cfg(test)]
    pub(in crate::preprocess::normalize_bv_arith) fn modular_poly_equal(
        terms: &TermStore,
        lhs: TermId,
        rhs: TermId,
        width: u32,
    ) -> bool {
        Self::modular_poly_compare(terms, lhs, rhs, width) == PolyRelation::Equal
    }

    /// Compare two same-width BV terms by canonical polynomials in
    /// `Z / 2^width`, in both directions. `NotEqual` is concluded only
    /// when the non-constant parts are identical and the constants
    /// differ (`x = x + 3`): the terms then differ by that nonzero
    /// constant under every assignment, so folding `=` to false is
    /// verdict-preserving. Every other mismatch is `Unknown` (see
    /// [`PolyRelation`]). Failure to recognize or stay within budget
    /// declines to `Unknown`.
    pub(in crate::preprocess::normalize_bv_arith) fn modular_poly_compare(
        terms: &TermStore,
        lhs: TermId,
        rhs: TermId,
        width: u32,
    ) -> PolyRelation {
        if width == 0 || width > BV_LINEAR_MAX_WIDTH {
            return PolyRelation::Unknown;
        }
        // Construct the potentially width-sized modulus once per comparison;
        // every recursive reduction borrows it.
        let modulus = BigInt::one() << width;
        let mut budget = BvLinearBudget::new();
        let Some(lhs) = Self::poly_fingerprint(terms, lhs, width, &modulus, &mut budget) else {
            return PolyRelation::Unknown;
        };
        let Some(rhs) = Self::poly_fingerprint(terms, rhs, width, &modulus, &mut budget) else {
            return PolyRelation::Unknown;
        };
        lhs.compare(&rhs)
    }

    /// Collect a modular polynomial fingerprint of `term` in the ring
    /// `Z / 2^ring_width`. Unsupported terms are opaque atoms; only operators
    /// whose ring meaning is exact are expanded.
    ///
    /// `ring_width` may be SMALLER than the term's own bit width (never
    /// larger): reduction mod `2^ring_width` is a ring homomorphism from
    /// `Z / 2^term_width` whenever `ring_width <= term_width`, so a term
    /// well-formed at its own width denotes, in the smaller ring, exactly its
    /// formal polynomial evaluated at the atoms' values mod `2^ring_width`.
    /// This is what lets the collector see through the constructor lowerings
    /// of constant multiplication: `mk_bvmul(2^k, t)` is stored as
    /// `concat(extract(t, w-k-1, 0), 0_k)` — and `mk_bvextract` further
    /// rewrites `extract(w-k-1, 0, bvmul(X, Y))` into
    /// `bvmul(extract(X), extract(Y))` — both of which are exact ring
    /// operations under the two rules below (zero-padded concat = scale by
    /// `2^k` from the narrower ring; low-extract = the mod-`2^(hi+1)`
    /// homomorphism).
    ///
    /// Every arm verifies operand sorts against the term's OWN stored width
    /// before assigning ring semantics, so malformed raw applications (mixed
    /// widths, forged sorts, indexed builtin-lookalikes) stay opaque atoms or
    /// decline — never a wrong interpretation.
    pub(in crate::preprocess::normalize_bv_arith) fn poly_fingerprint(
        terms: &TermStore,
        term: TermId,
        ring_width: u32,
        modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<BvPolyFingerprint> {
        stacker::maybe_grow(BV_NORM_STACK_RED_ZONE, BV_NORM_STACK_SIZE, || {
            let term_width = match terms.sort(term) {
                Sort::BitVec(bv) if bv.width >= ring_width => bv.width,
                _ => return None,
            };
            budget.spend_node()?;

            if let Some(value) = Self::bitvec_constant(terms, term, term_width) {
                budget.spend_coefficient_ops(1)?;
                return Some(BvPolyFingerprint::constant(ring_width, value, modulus));
            }

            let TermData::App(sym, args) = terms.get(term) else {
                return Some(BvPolyFingerprint::atom(ring_width, Atom::Term(term)));
            };
            // Indexed symbols with a builtin-looking base name are not the
            // corresponding SMT-LIB builtin — except the genuine indexed
            // `extract` and `zero_extend`, interpreted in `indexed` below.
            // Only exact symbols may be interpreted algebraically by this
            // trusted fold.
            let name = match sym {
                Symbol::Named(name) => name,
                Symbol::Indexed(name, indices) if args.len() == 1 => {
                    return Self::indexed(
                        terms,
                        term,
                        (name.as_str(), indices.as_slice()),
                        args[0],
                        (term_width, ring_width),
                        modulus,
                        budget,
                    );
                }
                _ => return Some(BvPolyFingerprint::atom(ring_width, Atom::Term(term))),
            };

            // Ring semantics require the application to be well-formed at its
            // own stored width: every operand's sort must be exactly
            // BitVec(term_width) (concat is the exception, handled in-arm).
            let operands_well_formed = |arg_ids: &[TermId]| {
                arg_ids.iter().all(
                    |&arg| matches!(terms.sort(arg), Sort::BitVec(bv) if bv.width == term_width),
                )
            };

            match name.as_str() {
                "bvadd" if !args.is_empty() && operands_well_formed(args) => {
                    let mut sum = BvPolyFingerprint::zero(ring_width);
                    for &arg in args {
                        let part = Self::poly_fingerprint(terms, arg, ring_width, modulus, budget)?;
                        sum.add_assign(part, modulus, budget)?;
                    }
                    Some(sum)
                }
                "bvsub" if args.len() == 2 && operands_well_formed(args) => {
                    let mut lhs =
                        Self::poly_fingerprint(terms, args[0], ring_width, modulus, budget)?;
                    let rhs = Self::poly_fingerprint(terms, args[1], ring_width, modulus, budget)?
                        .negate(modulus, budget)?;
                    lhs.add_assign(rhs, modulus, budget)?;
                    Some(lhs)
                }
                "bvneg" if args.len() == 1 && operands_well_formed(args) => Some(
                    Self::poly_fingerprint(terms, args[0], ring_width, modulus, budget)?
                        .negate(modulus, budget)?,
                ),
                "bvmul" if args.len() >= 2 && operands_well_formed(args) => {
                    // Full polynomial product over all operands. A literal
                    // operand is just a constant polynomial; variable-by-
                    // variable products expand into higher-degree monomials,
                    // capped by degree/monomial-count bounds.
                    let mut product =
                        Self::poly_fingerprint(terms, args[0], ring_width, modulus, budget)?;
                    for &arg in &args[1..] {
                        let factor =
                            Self::poly_fingerprint(terms, arg, ring_width, modulus, budget)?;
                        product = product.multiply(&factor, modulus, budget)?;
                    }
                    Some(product)
                }
                "bvshl" if args.len() == 2 && operands_well_formed(args) => {
                    Self::shift_fingerprint(
                        terms, term, args, term_width, ring_width, modulus, budget,
                    )
                }
                "concat" if args.len() == 2 => Self::concat_fingerprint(
                    terms, term, args, term_width, ring_width, modulus, budget,
                ),
                _ => Some(BvPolyFingerprint::atom(ring_width, Atom::Term(term))),
            }
        })
    }

    /// A `bvshl` by a literal amount: `2^k` times its operand, `0` once `k`
    /// reaches the ring; any other shift is one atom.
    fn shift_fingerprint(
        terms: &TermStore,
        term: TermId,
        args: &[TermId],
        term_width: u32,
        ring_width: u32,
        modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<BvPolyFingerprint> {
        let Some(shift) = Self::bitvec_constant(terms, args[1], term_width) else {
            return Some(BvPolyFingerprint::atom(ring_width, Atom::Term(term)));
        };
        // A shift amount too large for u32 is necessarily >= the
        // u32-sized ring width, hence the ring value is zero
        // (2^shift ≡ 0 mod 2^ring_width; for shift >= term_width
        // SMT-LIB also defines the whole word to be zero).
        let Some(shift) = shift.to_u32() else {
            return Some(BvPolyFingerprint::zero(ring_width));
        };
        if shift >= ring_width {
            return Some(BvPolyFingerprint::zero(ring_width));
        }
        let coefficient = BigInt::one() << shift;
        Self::poly_fingerprint(terms, args[0], ring_width, modulus, budget)?.scale(
            &coefficient,
            modulus,
            budget,
        )
    }

    /// `(concat high low)`, which denotes `2^k * val(high) + val(low)`,
    /// `k = width(low)`, with `val(high) < 2^(term_width - k)`: `high` is
    /// collected in the NARROWER ring `Z/2^(ring_width - k)` and rescaled
    /// via `embed_shifted` (the `2^k` homomorphism), and the EXACT value of
    /// the narrow `low` is added. The child widths must sum to the stored
    /// width. `k >= ring_width` leaves only `low`, read in the ring itself.
    fn concat_fingerprint(
        terms: &TermStore,
        term: TermId,
        args: &[TermId],
        term_width: u32,
        ring_width: u32,
        modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<BvPolyFingerprint> {
        let (high, low) = (args[0], args[1]);
        let shift = match terms.sort(low) {
            Sort::BitVec(bv) if bv.width > 0 => bv.width,
            _ => return Some(BvPolyFingerprint::atom(ring_width, Atom::Term(term))),
        };
        if !matches!(
            terms.sort(high),
            Sort::BitVec(bv) if bv.width.checked_add(shift) == Some(term_width)
        ) {
            return Some(BvPolyFingerprint::atom(ring_width, Atom::Term(term)));
        }
        if shift >= ring_width {
            return Self::poly_fingerprint(terms, low, ring_width, modulus, budget);
        }
        let narrow_width = ring_width - shift;
        let narrow_modulus = BigInt::one() << narrow_width;
        let mut value = Self::poly_fingerprint(terms, high, narrow_width, &narrow_modulus, budget)?
            .embed_shifted(shift, ring_width, modulus, budget)?;
        let low_value = Self::exact_value(terms, low, ring_width, modulus, budget)?;
        value.add_assign(low_value, modulus, budget)?;
        Some(value)
    }

    fn bitvec_constant(terms: &TermStore, term: TermId, width: u32) -> Option<BigInt> {
        match terms.get(term) {
            TermData::Const(Constant::BitVec {
                value,
                width: constant_width,
            }) if *constant_width == width
                && !value.is_negative()
                && value.bits() <= u64::from(width) =>
            {
                Some(value.clone())
            }
            _ => None,
        }
    }
}
