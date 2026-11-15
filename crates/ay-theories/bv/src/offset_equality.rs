// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An equality between two OFFSET words, blasted through one shared subtractor.
//!
//! `(= (bvadd c1 x) (bvadd c2 y))` holds exactly when `x - y = c2 - c1` in
//! `Z / 2^w` (`TermStore::bv_offset_equality`, whose tests check the reading
//! exhaustively at a small width). Blasted as authored, every such atom is two
//! ripple-carry adders and a comparator of its own, and CDCL re-learns the
//! carry relations between them atom by atom. Blasted through the difference,
//! every atom over one pair of words compares the SAME subtractor with a
//! constant: the subtractor's carry-in is the canonical true literal, so the
//! gate caches build its gates once, and what CDCL learns about `x - y` holds
//! for every atom. Measured on external-codegen's byte-addressed coroutine-slot query
//! (64 such atoms over two base words, 2026-10-08): 214k conflicts as authored,
//! 2.2k through the shared difference.
//!
//! This is an encoding choice, nothing more: the literal returned is the
//! equality's own truth value. Terms are not rewritten, so preprocessing,
//! models and proofs see the formula as before; it reaches every BV equality
//! the solver blasts, including the index equalities select/store expansion
//! creates after preprocessing.
//!
//! A reading is used only when it pays (`ay_core::BvOffsetShares`, DR-33):
//! when it cancels arithmetic the authored sides carry, or when another
//! equality the solver counted reads the same pair of words. Any other
//! equality keeps its authored blast. [`BvSolver::bitblast_all`] counts its
//! assertions first; an equality blasted outside a counted scope is counted
//! when it is blasted. Measured on corpus9 1494.fpbv, whose one reading
//! compared `a` with `b` for an authored `(= (bvneg a) (bvneg b))` beside
//! signed comparisons of the two negations: 0.94 strict CPU-s read, 0.53 as
//! authored.

use super::*;
use num_bigint::{BigInt, Sign};

impl BvSolver<'_> {
    /// Bit-blast `(= lhs rhs)` between two bit-vector terms of one width.
    pub(crate) fn bitblast_term_eq(&mut self, lhs: TermId, rhs: TermId) -> CnfLit {
        if !self.encoding_complete() {
            return 0;
        }
        if !self.encoding.is_counted() {
            if let Some(lit) = self.bitblast_offset_eq(lhs, rhs) {
                return lit;
            }
        }
        let a = self.get_bits(lhs);
        let b = self.get_bits(rhs);
        self.bitblast_eq(&a, &b)
    }

    /// Count the binary equalities `roots` reach, so an equality that does
    /// not cancel is blasted through its pair's difference only when another
    /// one also reads that pair (module docs). [`Self::bitblast_all`] counts its assertions; a
    /// caller that blasts predicates one at a time counts its assertions here
    /// first.
    pub fn count_offset_equalities(&mut self, roots: &[TermId]) {
        let owner = self.encoding_guard();
        if !owner.open() {
            return;
        }
        self.offset_shares
            .count_reachable(self.terms, roots.iter().copied(), false, &mut || {
                owner.open()
            });
        let _ = owner.open();
    }

    /// `minuend - subtrahend = k` for an equality between two offset words
    /// whose reading pays, or `minuend = subtrahend` at `k = 0`; `None` for
    /// any other equality.
    fn bitblast_offset_eq(&mut self, lhs: TermId, rhs: TermId) -> Option<CnfLit> {
        if !self.encoding_complete() {
            return None;
        }
        let reading = self.offset_shares.reading(self.terms, lhs, rhs)?;
        let width = usize::try_from(reading.width).ok()?;
        let minuend = self.get_bits(reading.minuend);
        let subtrahend = self.get_bits(reading.subtrahend);
        if minuend.len() != width || subtrahend.len() != width {
            return None;
        }
        if reading.constant.sign() == Sign::NoSign {
            return Some(self.bitblast_eq(&minuend, &subtrahend));
        }
        let carry = neg_lit(self.fresh_false());
        let negated = self.bitblast_not(&subtrahend);
        let difference = self.bitblast_add_with_carry(&minuend, &negated, carry);
        let constant = self.offset_constant_bits(&reading.constant, width);
        Some(self.bitblast_eq(&difference, &constant))
    }

    /// The bits of `value`, as the constant arm of `bitblast` spells them.
    fn offset_constant_bits(&mut self, value: &BigInt, width: usize) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        let falsum = self.fresh_false();
        let mut bits = Vec::with_capacity(width);
        for bit in 0..width {
            if !self.encoding_step() {
                return Vec::new();
            }
            bits.push(if value.bit(bit as u64) {
                neg_lit(falsum)
            } else {
                falsum
            });
        }
        bits
    }
}

#[cfg(test)]
#[path = "offset_equality_tests.rs"]
mod tests;
