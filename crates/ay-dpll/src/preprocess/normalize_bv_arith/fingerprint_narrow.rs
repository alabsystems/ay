// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Indexed operators and words narrower than the ring.
//!
//! A multi-word lowering spells a `2m`-bit product through `m`-bit limbs: the
//! operands are `concat`s of limbs, the partial products are `m`-bit `bvmul`s
//! and the carry into the high limb is the high half of a zero-extended
//! product, `((_ extract 2m-1 m) (bvmul ((_ zero_extend m) u)
//! ((_ zero_extend m) v)))` (external-codegen's i128 multiply lowering, gate row 2023,
//! is exactly this). Each piece has an exact integer value:
//!
//! * `((_ zero_extend k) x)` is `val(x)`;
//! * `(concat h l)` is `2^k * val(h) + val(l)`, `k = width(l)`;
//! * an `m`-bit `(bvmul u v)` is `val(u) * val(v) - 2^m * floor(val(u) *
//!   val(v) / 2^m)`, and the floor is [`Atom::ProductHigh`];
//! * the high-half extract above is that same floor, since a product of two
//!   zero-extended `m`-bit words cannot wrap at `2m` bits.
//!
//! So a word narrower than the ring is read by its exact value
//! ([`NormalizeBvArith::exact_value`]) instead of as one opaque atom, which is
//! what lets the fold see the limbs of the two sides as one polynomial.

use super::super::super::NormalizeBvArith;
use super::super::{Atom, BvLinearBudget, BvPolyFingerprint};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::One;

impl NormalizeBvArith {
    /// A genuine indexed operator of width `term_width`, read in the ring
    /// `Z / 2^ring_width`: the low `extract` (reduction mod `2^(hi+1)`, a ring
    /// homomorphism), the high-half extract of a zero-extended product, and
    /// `zero_extend`. Anything else, or a malformed application, is one atom.
    pub(super) fn indexed(
        terms: &TermStore,
        term: TermId,
        (name, indices): (&str, &[u32]),
        source: TermId,
        (term_width, ring_width): (u32, u32),
        modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<BvPolyFingerprint> {
        let opaque = || Some(BvPolyFingerprint::atom(ring_width, Atom::Term(term)));
        let Sort::BitVec(source_sort) = terms.sort(source) else {
            return opaque();
        };
        let source_width = source_sort.width;
        match (name, indices) {
            // extract(hi, 0, t) denotes t mod 2^(hi+1). With ring_width <=
            // hi+1 (term_width >= ring_width), the ring value is t mod
            // 2^ring_width: recurse into t in the SAME ring.
            ("extract", &[high, 0])
                if high.checked_add(1) == Some(term_width) && source_width > high =>
            {
                Self::poly_fingerprint(terms, source, ring_width, modulus, budget)
            }
            ("extract", &[high, low])
                if low > 0
                    && low == term_width
                    && {
                        let extracted_end = high.checked_add(1);
                        let double_width = low.checked_mul(2);
                        extracted_end == double_width
                    }
                    && source_width > high =>
            {
                // source may be WIDER than 2*low (e.g. a 32x32 product
                // computed at 96 bits): the true product of two
                // `low`-bit words fits in 2*low bits, so the wider
                // bvmul keeps it exact and bits [2*low-1 : low] are
                // still floor(u*v / 2^low).
                match product_high(terms, source, low) {
                    Some(atom) => Some(BvPolyFingerprint::atom(ring_width, atom)),
                    None => opaque(),
                }
            }
            ("zero_extend", &[extension])
                if source_width.checked_add(extension) == Some(term_width) =>
            {
                Self::exact_value(terms, source, ring_width, modulus, budget)
            }
            _ => opaque(),
        }
    }

    /// A polynomial congruent, mod `2^ring_width`, to the EXACT unsigned
    /// value of `term`. A word at least as wide as the ring is its ordinary
    /// fingerprint (only its residue matters); a narrower one is expanded by
    /// the exact rules in the module docs, and is otherwise one atom.
    pub(super) fn exact_value(
        terms: &TermStore,
        term: TermId,
        ring_width: u32,
        modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<BvPolyFingerprint> {
        let Sort::BitVec(sort) = terms.sort(term) else {
            return None;
        };
        let width = sort.width;
        if width >= ring_width {
            return Self::poly_fingerprint(terms, term, ring_width, modulus, budget);
        }
        budget.spend_node()?;
        if let TermData::Const(Constant::BitVec { value, width: bits }) = terms.get(term) {
            if *bits == width {
                budget.spend_coefficient_ops(1)?;
                return Some(BvPolyFingerprint::constant(
                    ring_width,
                    value.clone(),
                    modulus,
                ));
            }
        }
        let opaque = || Some(BvPolyFingerprint::atom(ring_width, Atom::Term(term)));
        let TermData::App(symbol, args) = terms.get(term) else {
            return opaque();
        };
        let width_of = |arg: TermId| match terms.sort(arg) {
            Sort::BitVec(bv) => Some(bv.width),
            _ => None,
        };
        match (symbol, args.as_slice()) {
            (Symbol::Named(name), &[left, right])
                if name == "bvmul"
                    && width_of(left) == Some(width)
                    && width_of(right) == Some(width) =>
            {
                // val(u * v mod 2^m) = val(u) * val(v) - 2^m * high(u, v).
                let mut value = Self::exact_value(terms, left, ring_width, modulus, budget)?
                    .multiply(
                        &Self::exact_value(terms, right, ring_width, modulus, budget)?,
                        modulus,
                        budget,
                    )?;
                let wrapped = BvPolyFingerprint::atom(ring_width, product_high_key(left, right))
                    .scale(&-(BigInt::one() << width), modulus, budget)?;
                value.add_assign(wrapped, modulus, budget)?;
                Some(value)
            }
            (Symbol::Named(name), &[high, low]) if name == "concat" => {
                let (Some(high_width), Some(low_width)) = (width_of(high), width_of(low)) else {
                    return opaque();
                };
                if high_width.checked_add(low_width) != Some(width) {
                    return opaque();
                }
                let mut value = Self::exact_value(terms, high, ring_width, modulus, budget)?
                    .scale(&(BigInt::one() << low_width), modulus, budget)?;
                value.add_assign(
                    Self::exact_value(terms, low, ring_width, modulus, budget)?,
                    modulus,
                    budget,
                )?;
                Some(value)
            }
            (Symbol::Indexed(name, indices), &[source])
                if name == "zero_extend"
                    && matches!(indices.as_slice(), &[extension]
                        if width_of(source).and_then(|w| w.checked_add(extension)) == Some(width)) =>
            {
                Self::exact_value(terms, source, ring_width, modulus, budget)
            }
            _ => opaque(),
        }
    }
}

/// [`Atom::ProductHigh`] of `(bvmul ((_ zero_extend a) u) ((_ zero_extend a)
/// v))` where `u, v` are `half`-bit words and the product is computed at
/// width `half + a >= 2 * half`, or `None`. The extension amount need not
/// equal `half`: any wider computation preserves the true product (which
/// fits in `2 * half` bits), so its bits `[2*half-1 : half]` agree.
fn product_high(terms: &TermStore, product: TermId, half: u32) -> Option<Atom> {
    let TermData::App(Symbol::Named(name), args) = terms.get(product) else {
        return None;
    };
    let &[left, right] = args.as_slice() else {
        return None;
    };
    if name != "bvmul" {
        return None;
    }
    let Sort::BitVec(product_bv) = terms.sort(product) else {
        return None;
    };
    let product_width = product_bv.width;
    if product_width < half.saturating_mul(2) {
        return None;
    }
    let operand = |extended: TermId| {
        let TermData::App(Symbol::Indexed(name, indices), args) = terms.get(extended) else {
            return None;
        };
        let (&[extension], &[word]) = (indices.as_slice(), args.as_slice()) else {
            return None;
        };
        (name == "zero_extend"
            && half.checked_add(extension) == Some(product_width)
            && matches!(terms.sort(extended), Sort::BitVec(bv) if bv.width == product_width)
            && matches!(terms.sort(word), Sort::BitVec(bv) if bv.width == half))
        .then_some(word)
    };
    Some(product_high_key(operand(left)?, operand(right)?))
}

fn product_high_key(left: TermId, right: TermId) -> Atom {
    Atom::ProductHigh(left.min(right), left.max(right))
}

#[cfg(test)]
#[path = "fingerprint_narrow_tests.rs"]
mod tests;
