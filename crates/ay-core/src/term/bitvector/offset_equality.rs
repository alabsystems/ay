// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A bit-vector equality between two OFFSET words, read as one difference.
//!
//! `(= (bvadd c1 x) (bvadd c2 y))` holds exactly when `x - y = c2 - c1`
//! modulo `2^w`: `Z / 2^w` is a group under addition, so moving a summand
//! across the equality is an identity, not an approximation. Spelled as
//! authored, every such atom costs a bit-blaster two ripple-carry adders and a
//! comparator of its own, and CDCL re-learns the carry relations between them
//! atom by atom. Read through the difference, every atom over the same pair of
//! words compares the SAME subtractor `x - y` with a constant. Measured on
//! external-codegen's byte-addressed coroutine-slot query (64 byte-address atoms over
//! two base words, 2026-10-08): 214k conflicts as authored, 2.2k through the
//! shared difference.
//!
//! [`TermStore::bv_offset_equality`] is the analysis, and it interns nothing.
//! The search bit-blaster (`ay-bv`), the strict checker's bit-blast lowering
//! and the Alethe printer's circuit and complete bit-blast lanes each read it,
//! and each keeps its own obligation: the bit-blaster encodes the same truth
//! value through one subtractor per pair of words, the checker lowers the same
//! Boolean function, and the printer proves the bridge
//! `(= (= lhs rhs) (= (bvsub x y) k))` (`poly_simp` + `poly_simp_rel`) for the
//! consumer to re-check. No term is rewritten (DR-30 in the development design notes).
//! Each uses a reading only when it pays, because it cancels or because its
//! difference is shared ([`BvOffsetShares`](super::BvOffsetShares), DR-33).
//!
//! THE READING. Each side is walked through `bvadd`, binary `bvsub`, `bvneg`
//! and literals of the equality's width; every other term is one opaque word.
//! The walk sums `lhs - rhs` as `constant + sum(count_i * word_i)` and keeps
//! the equality when, modulo `2^w`, exactly two words survive with unit
//! coefficients of opposite sign. When every integer word coefficient is
//! exactly zero, one actually cancelled word supplies both sides of `x - x`;
//! the complete equality then compares zero with the remaining constant.
//! Words that cancel drop out (they do not
//! change the equality's value). Every count is an integer the walk computed
//! exactly, so the reading is the polynomial identity
//! `lhs - rhs = constant + word_a - word_b`, nothing weaker.

use super::*;

/// Most term nodes the two sides' walk visits together. Equality operands of
/// the shape this reads are a handful of nodes; a larger side is declined, so
/// the analysis never costs more than a constant per equality.
const MAX_OFFSET_WALK: usize = 64;

/// Widest equality read. A wider one keeps its authored form.
const MAX_OFFSET_WIDTH: u32 = 4096;

/// `(= lhs rhs)` read as `(= (bvsub minuend subtrahend) constant)` over
/// `width`-bit words, or as `(= minuend subtrahend)` when `constant` is zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BvOffsetEquality {
    /// The surviving word with the smaller `TermId`, or one actually cancelled
    /// word when all integer coefficients cancel exactly.
    pub minuend: TermId,
    /// The other surviving word, equal to `minuend` on exact full cancellation.
    pub subtrahend: TermId,
    /// `minuend - subtrahend` whenever the equality holds, in `[0, 2^width)`.
    pub constant: BigInt,
    /// The words' width.
    pub width: u32,
    /// Whether word occurrences cancel, or the sides spell more occurrences
    /// than the two surviving words. Exact full cancellation also sets this:
    /// the reading then drops authored arithmetic (`offset_sharing.rs`).
    pub cancels: bool,
}

/// The running sum `lhs - rhs` of one walk.
struct OffsetSum {
    width: u32,
    constant: BigInt,
    words: Vec<(TermId, i64)>,
    /// Word occurrences the walk met, counted with repetition.
    occurrences: usize,
    budget: usize,
    // A new full-cancellation shortcut may not hide unsupported/malformed
    // opaque siblings. Its admitted source is typed affine syntax over Vars.
    full_source_well_formed: bool,
}

impl OffsetSum {
    fn add_word(&mut self, word: TermId, positive: bool) {
        self.occurrences += 1;
        let count = if positive { 1 } else { -1 };
        match self.words.iter_mut().find(|(seen, _)| *seen == word) {
            Some((_, total)) => *total += count,
            None => self.words.push((word, count)),
        }
    }
}

impl TermStore {
    /// Read `(= lhs rhs)` as a difference of two offset words (module docs),
    /// or `None` when it is not one, when it already compares the two words
    /// or their difference with a literal, or when the walk is over its
    /// bound.
    #[must_use]
    pub fn bv_offset_equality(&self, lhs: TermId, rhs: TermId) -> Option<BvOffsetEquality> {
        let width = self.get_bv_width(lhs)?;
        if width > MAX_OFFSET_WIDTH || self.sort(rhs) != self.sort(lhs) {
            return None;
        }
        let mut sum = OffsetSum {
            width,
            constant: BigInt::zero(),
            words: Vec::new(),
            occurrences: 0,
            budget: MAX_OFFSET_WALK,
            full_source_well_formed: true,
        };
        self.offset_walk(lhs, true, &mut sum)?;
        self.offset_walk(rhs, false, &mut sum)?;
        let modulus = BigInt::one() << width;
        let unit = |count: i64| {
            let residue = Self::bv_mask(&BigInt::from(count), width);
            (residue.is_one() || residue == &modulus - 1).then_some(residue)
        };
        let surviving: Vec<(TermId, i64)> = sum
            .words
            .iter()
            .copied()
            .filter(|&(_, count)| !Self::bv_mask(&BigInt::from(count), width).is_zero())
            .collect();
        let (minuend, minuend_count, subtrahend, subtrahend_count) = match surviving.as_slice() {
            [first, second] => {
                if first.0.index() < second.0.index() {
                    (first.0, first.1, second.0, second.1)
                } else {
                    (second.0, second.1, first.0, first.1)
                }
            }
            [] if sum.full_source_well_formed && sum.words.iter().all(|(_, count)| *count == 0) => {
                // Retain a real, same-width source word. The two occurrences
                // cancel identically under every interpretation; no value of
                // this word is assumed. Require INTEGER cancellation so this
                // lane never introduces a coefficient that only vanishes
                // modulo 2^w (the external polynomial bridge preserves it).
                let word = sum
                    .words
                    .iter()
                    .map(|(word, _)| *word)
                    .min_by_key(|word| word.index())?;
                (word, 1, word, -1)
            }
            _ => return None,
        };
        let minuend_unit = unit(minuend_count)?;
        let subtrahend_unit = unit(subtrahend_count)?;
        if !Self::bv_mask(&(&minuend_unit + &subtrahend_unit), width).is_zero() {
            return None;
        }
        // lhs - rhs = c + m*(minuend - subtrahend) with m = +-1, so the
        // equality is minuend - subtrahend = -c (m = 1) or = c (m = -1).
        let constant = if minuend_unit.is_one() {
            Self::bv_mask(&-&sum.constant, width)
        } else {
            Self::bv_mask(&sum.constant, width)
        };
        let reading = BvOffsetEquality {
            minuend,
            subtrahend,
            constant,
            width,
            cancels: sum.occurrences > 2 || minuend == subtrahend,
        };
        (!self.is_offset_equality_spelling(lhs, rhs, &reading)).then_some(reading)
    }

    /// Add `term` (`positive`) or its negation to `sum`.
    fn offset_walk(&self, term: TermId, positive: bool, sum: &mut OffsetSum) -> Option<()> {
        sum.budget = sum.budget.checked_sub(1)?;
        if self.get_bv_width(term)? != sum.width {
            return None;
        }
        match self.get(term) {
            TermData::Const(Constant::BitVec { value, width }) => {
                sum.full_source_well_formed &= *width == sum.width
                    && value.sign() != num_bigint::Sign::Minus
                    && value.bits() <= u64::from(sum.width);
                if positive {
                    sum.constant += value;
                } else {
                    sum.constant -= value;
                }
            }
            TermData::App(Symbol::Named(op), args) if op == "bvadd" && !args.is_empty() => {
                sum.full_source_well_formed &= args.len() >= 2;
                for &arg in args {
                    self.offset_walk(arg, positive, sum)?;
                }
            }
            TermData::App(Symbol::Named(op), args) if op == "bvsub" && args.len() == 2 => {
                self.offset_walk(args[0], positive, sum)?;
                self.offset_walk(args[1], !positive, sum)?;
            }
            TermData::App(Symbol::Named(op), args) if op == "bvneg" && args.len() == 1 => {
                self.offset_walk(args[0], !positive, sum)?;
            }
            _ => {
                sum.full_source_well_formed &= matches!(self.get(term), TermData::Var(..));
                sum.add_word(term, positive);
            }
        }
        Some(())
    }

    /// Whether `(= lhs rhs)` already compares the two words, or their
    /// difference with a literal: the bare `(= x y)`, or a binary `bvsub` of
    /// the two words, in EITHER order, against any literal (zero included).
    ///
    /// Such an equality is left as authored. Read again, it would compare a
    /// difference the term does not name — `x - y` for an authored `y - x`,
    /// or `x` with `y` for an authored `(= (bvsub x y) 0)` — and give up the
    /// subtractor the authored term shares with every other use of it.
    /// Measured on external-codegen's flag rows, which test `(= (bvsub a b) 0)` beside
    /// `((_ extract 63 63) (bvsub a b))` (corpus9 2233, 0225.def0, 2106.def0,
    /// 1494.fpbv): read as `(= a b)`, each took twice the strict CPU time.
    fn is_offset_equality_spelling(
        &self,
        lhs: TermId,
        rhs: TermId,
        reading: &BvOffsetEquality,
    ) -> bool {
        let BvOffsetEquality {
            minuend,
            subtrahend,
            ..
        } = reading;
        let words = |a: TermId, b: TermId| {
            (a, b) == (*minuend, *subtrahend) || (b, a) == (*minuend, *subtrahend)
        };
        let is_difference = |term: TermId| {
            matches!(self.get(term), TermData::App(Symbol::Named(op), args)
                if op == "bvsub" && args.len() == 2 && words(args[0], args[1]))
        };
        let is_literal = |term: TermId| self.get_bitvec(term).is_some();
        words(lhs, rhs)
            || (is_difference(lhs) && is_literal(rhs))
            || (is_difference(rhs) && is_literal(lhs))
    }
}

#[cfg(test)]
#[path = "offset_equality_tests.rs"]
mod tests;
