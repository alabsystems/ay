// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Modular polynomial fingerprints of bit-vector terms (the equality fold of
//! `NormalizeBvArith`).

use ay_core::TermId;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;

/// Hard work bound for one modular polynomial equality comparison. Exceeding
/// it declines the optimization; it never changes the formula's meaning.
const BV_LINEAR_MAX_NODES: usize = 4096;

/// Hard bound on distinct monomials retained in one fingerprint. Product
/// expansion is exponential in nesting degree; over the cap the fold declines.
const BV_POLY_MAX_MONOMIALS: usize = 512;

/// Hard bound on one monomial's total degree (sum of exponents). Over the cap
/// the fold declines — a sound no-op, never a wrong answer.
pub(super) const BV_POLY_MAX_DEGREE: u32 = 8;

/// Hard bound on modular coefficient operations. A node bound alone is not a
/// work bound: repeatedly scaling a large coefficient map is quadratic.
const BV_LINEAR_MAX_COEFFICIENT_OPS: usize = 65_536;

/// Avoid allocating and repeatedly operating on attacker-sized coefficients.
/// Wider words still take the ordinary, semantics-preserving solver path.
pub(super) const BV_LINEAR_MAX_WIDTH: u32 = 4096;

#[derive(Clone, Copy, Debug)]
pub(super) struct BvLinearBudget {
    pub(super) nodes: usize,
    pub(super) coefficient_ops: usize,
}

impl BvLinearBudget {
    fn new() -> Self {
        Self {
            nodes: BV_LINEAR_MAX_NODES,
            coefficient_ops: BV_LINEAR_MAX_COEFFICIENT_OPS,
        }
    }

    fn spend_node(&mut self) -> Option<()> {
        self.nodes = self.nodes.checked_sub(1)?;
        Some(())
    }

    fn spend_coefficient_ops(&mut self, count: usize) -> Option<()> {
        self.coefficient_ops = self.coefficient_ops.checked_sub(count)?;
        Some(())
    }
}

/// One indivisible factor of a monomial. Its value is an INTEGER, of which a
/// fingerprint in `Z / 2^width` only ever reads the residue mod `2^width`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Atom {
    /// The unsigned value of a term. A term at least as wide as the ring it
    /// occurs in is read mod `2^width`; a narrower one (the operand of a
    /// `zero_extend`, the low half of a `concat`) is its exact value.
    Term(TermId),
    /// `floor(u * v / 2^m)` for two `m`-bit words `u <= v` (by `TermId`): the
    /// high half of their full `2m`-bit product. It is what an `m`-bit
    /// `bvmul` drops, and exactly what `((_ extract 2m-1 m) (bvmul
    /// ((_ zero_extend m) u) ((_ zero_extend m) v)))` keeps.
    ProductHigh(TermId, TermId),
}

/// One monomial: `(atom, exponent)` pairs, strictly ascending by [`Atom`],
/// every exponent `>= 1`. The empty vector is the constant-term monomial.
/// The derived lexicographic `Ord` on the sorted representation gives a
/// canonical `BTreeMap` key: equal multisets of atoms iff equal keys.
type BvMonomial = Vec<(Atom, u32)>;

/// A canonical polynomial in the modular ring `Z / 2^width` (`width` is the
/// RING width; see `NormalizeBvArith::poly_fingerprint` — atoms may be
/// wider terms whose values are taken mod `2^width`).
///
/// Recognized ring operators (`bvadd`, `bvsub`, `bvneg`, `bvmul`, literal
/// `bvshl`, `concat`, `zero_extend`, low `extract`) are expanded into a
/// multiset-of-monomials normal form with coefficients canonical in
/// `[0, 2^width)`; so is the high half of a product of two zero-extended
/// words ([`Atom::ProductHigh`]). Every other term — division, symbolic
/// shifts, bitwise ops, other extracts, uninterpreted applications — is one
/// indivisible atom. A matching fingerprint therefore proves equality under every
/// assignment without assuming algebraic independence or assigning semantics
/// to unsupported ops. Zero-coefficient entries are deleted immediately after
/// every modular reduction so map equality IS formal-polynomial equality.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct BvPolyFingerprint {
    width: u32,
    coeffs: BTreeMap<BvMonomial, BigInt>,
}

/// What a fingerprint comparison proves about two same-width BV terms.
///
/// `NotEqual` is deliberately narrow: it requires the non-constant parts
/// of the two canonical polynomials to be *identical*, so their semantic
/// difference is the (nonzero) constant difference under every atom
/// assignment. Differing non-constant parts conclude nothing — formally
/// distinct polynomials can still be semantically equal (width 1:
/// `x*x` vs `x`), which is why every other mismatch stays `Unknown`
/// and falls through to bit-blasting.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum PolyRelation {
    Equal,
    NotEqual,
    Unknown,
}

impl BvPolyFingerprint {
    /// Compare two fingerprints of the same ring width (see
    /// [`PolyRelation`] for exactly what each outcome proves).
    pub(super) fn compare(&self, other: &Self) -> PolyRelation {
        if self.width != other.width {
            return PolyRelation::Unknown;
        }
        if self == other {
            return PolyRelation::Equal;
        }
        // Zero-coefficient entries are deleted on reduction, so an absent
        // constant entry means offset 0. After the equality check above,
        // identical non-constant parts force the constants to differ.
        let same_nonconstant = self
            .coeffs
            .iter()
            .filter(|(monomial, _)| !monomial.is_empty())
            .eq(other
                .coeffs
                .iter()
                .filter(|(monomial, _)| !monomial.is_empty()));
        if same_nonconstant {
            PolyRelation::NotEqual
        } else {
            PolyRelation::Unknown
        }
    }

    fn zero(width: u32) -> Self {
        Self {
            width,
            coeffs: BTreeMap::new(),
        }
    }

    fn reduced(value: BigInt, modulus: &BigInt) -> BigInt {
        let remainder = value % modulus;
        if remainder.is_negative() {
            remainder + modulus
        } else {
            remainder
        }
    }

    fn constant(width: u32, value: BigInt, modulus: &BigInt) -> Self {
        let mut result = Self::zero(width);
        let reduced = Self::reduced(value, modulus);
        if !reduced.is_zero() {
            result.coeffs.insert(BvMonomial::new(), reduced);
        }
        result
    }

    fn atom(width: u32, atom: Atom) -> Self {
        let mut result = Self::zero(width);
        result.coeffs.insert(vec![(atom, 1)], BigInt::one());
        result
    }

    fn add_assign(
        &mut self,
        other: Self,
        modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<()> {
        if self.width != other.width {
            return None;
        }
        budget.spend_coefficient_ops(1 + other.coeffs.len())?;
        for (monomial, coefficient) in other.coeffs {
            let previous = self.coeffs.remove(&monomial).unwrap_or_else(BigInt::zero);
            let combined = Self::reduced(previous + coefficient, modulus);
            if !combined.is_zero() {
                self.coeffs.insert(monomial, combined);
                if self.coeffs.len() > BV_POLY_MAX_MONOMIALS {
                    return None;
                }
            }
        }
        Some(())
    }

    fn scale(
        mut self,
        coefficient: &BigInt,
        modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<Self> {
        budget.spend_coefficient_ops(1 + self.coeffs.len())?;
        let monomials: Vec<BvMonomial> = self.coeffs.keys().cloned().collect();
        for monomial in monomials {
            let value = self.coeffs.remove(&monomial).unwrap_or_else(BigInt::zero);
            let scaled = Self::reduced(value * coefficient, modulus);
            if !scaled.is_zero() {
                self.coeffs.insert(monomial, scaled);
            }
        }
        Some(self)
    }

    fn negate(self, modulus: &BigInt, budget: &mut BvLinearBudget) -> Option<Self> {
        self.scale(&-BigInt::one(), modulus, budget)
    }

    /// Reinterpret a `Z / 2^self.width` polynomial as `2^shift * self` in the
    /// wider ring `Z / 2^new_width` where `new_width == self.width + shift`.
    ///
    /// Soundness: multiplication by `2^shift` is a ring homomorphism from
    /// `Z / 2^(w-shift)` onto the subgroup `2^shift * Z / 2^w`: for any
    /// integers `c, m`, `2^shift * (c + m * 2^(w-shift)) ≡ 2^shift * c
    /// (mod 2^w)`, so coefficients already reduced in the narrow ring rescale
    /// to exactly the right residues in the wide ring. A nonzero narrow
    /// coefficient `c < 2^(w-shift)` gives `2^shift * c < 2^w`, never zero,
    /// but zero entries are still dropped defensively to keep canonicity
    /// unconditional.
    fn embed_shifted(
        mut self,
        shift: u32,
        new_width: u32,
        new_modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<Self> {
        debug_assert_eq!(
            self.width.checked_add(shift),
            Some(new_width),
            "BUG: embed_shifted requires new_width == width + shift"
        );
        budget.spend_coefficient_ops(1 + self.coeffs.len())?;
        let factor = BigInt::one() << shift;
        let monomials: Vec<BvMonomial> = self.coeffs.keys().cloned().collect();
        for monomial in monomials {
            let value = self.coeffs.remove(&monomial).unwrap_or_else(BigInt::zero);
            let scaled = Self::reduced(value * &factor, new_modulus);
            if !scaled.is_zero() {
                self.coeffs.insert(monomial, scaled);
            }
        }
        self.width = new_width;
        Some(self)
    }

    /// Full polynomial product. The entire `|P| * |Q|` cross-product cost is
    /// pre-charged (checked) against the coefficient-op budget BEFORE any
    /// work, so work stays bounded regardless of term shape. Declines when a
    /// product monomial's total degree exceeds [`BV_POLY_MAX_DEGREE`] or the
    /// result exceeds [`BV_POLY_MAX_MONOMIALS`].
    fn multiply(
        &self,
        other: &Self,
        modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<Self> {
        if self.width != other.width {
            return None;
        }
        let cross_terms = self.coeffs.len().checked_mul(other.coeffs.len())?;
        budget.spend_coefficient_ops(1 + cross_terms)?;
        let mut result = Self::zero(self.width);
        for (left_monomial, left_coefficient) in &self.coeffs {
            for (right_monomial, right_coefficient) in &other.coeffs {
                let monomial = Self::merge_monomials(left_monomial, right_monomial)?;
                let product = Self::reduced(left_coefficient * right_coefficient, modulus);
                if product.is_zero() {
                    continue;
                }
                let previous = result.coeffs.remove(&monomial).unwrap_or_else(BigInt::zero);
                let combined = Self::reduced(previous + product, modulus);
                if !combined.is_zero() {
                    result.coeffs.insert(monomial, combined);
                    if result.coeffs.len() > BV_POLY_MAX_MONOMIALS {
                        return None;
                    }
                }
            }
        }
        Some(result)
    }

    /// Merge two sorted exponent multisets, adding exponents of shared atoms.
    /// Every addition is checked and the running total degree is capped BEFORE
    /// the entry is committed; `None` declines the whole fingerprint.
    fn merge_monomials(left: &BvMonomial, right: &BvMonomial) -> Option<BvMonomial> {
        let mut merged = BvMonomial::with_capacity(left.len() + right.len());
        let mut total_degree: u32 = 0;
        let (mut i, mut j) = (0usize, 0usize);
        let mut push = |entry: (Atom, u32), total: &mut u32| -> Option<()> {
            *total = total.checked_add(entry.1)?;
            if *total > BV_POLY_MAX_DEGREE {
                return None;
            }
            merged.push(entry);
            Some(())
        };
        while i < left.len() && j < right.len() {
            let entry = match left[i].0.cmp(&right[j].0) {
                std::cmp::Ordering::Less => {
                    let entry = left[i];
                    i += 1;
                    entry
                }
                std::cmp::Ordering::Greater => {
                    let entry = right[j];
                    j += 1;
                    entry
                }
                std::cmp::Ordering::Equal => {
                    let exponent = left[i].1.checked_add(right[j].1)?;
                    let entry = (left[i].0, exponent);
                    i += 1;
                    j += 1;
                    entry
                }
            };
            push(entry, &mut total_degree)?;
        }
        for &entry in &left[i..] {
            push(entry, &mut total_degree)?;
        }
        for &entry in &right[j..] {
            push(entry, &mut total_degree)?;
        }
        Some(merged)
    }
}

#[path = "fingerprint_collect.rs"]
mod collect;
