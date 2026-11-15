// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An equality between two OFFSET words, blasted through one shared difference.
//!
//! The strict checker validates `(= (bvadd c1 x) (bvadd c2 y))` as
//! `(= (bvsub x y) k)` (`checker/bv_bitblast/offset_equality.rs`); blasted as
//! authored, the refutation here needs as many conflicts as the solver's own
//! search on the raw form, past this lane's caps (external-codegen's coroutine-slot
//! row: 64 such atoms, 214k conflicts). So the atom is bridged first:
//!
//! 1. `poly_simp`: `(= (bvmul 1 (bvsub lhs rhs)) (bvmul f (bvsub d k)))`, with
//!    `d` the difference `(bvsub x y)` and `f` one or minus one;
//! 2. `poly_simp_rel` (its bit-vector case, both factors odd):
//!    `(= (= lhs rhs) (= d k))`;
//!
//! and `(= d k)` is blasted like any other equality, through ONE subtractor
//! word per pair of words, shared by every atom over that pair. At `k = 0`
//! the target is `(= x y)` and no subtractor is built. A reading that cancels
//! nothing, over a pair only one of the root's equalities reads, is not
//! bridged (`ay_core::BvOffsetShares`, DR-33).
//!
//! WHAT DECIDES THE STEP. The term store's reading
//! (`TermStore::bv_offset_equality`) only SELECTS the two words. Whether the
//! bridge is printed is decided on the PRINTED text, which is what the
//! consumer's `poly_simp` normalizes: both sides of step 1 are read as linear
//! forms over their printed atoms (`bvadd`, binary `bvsub`, `bvneg` and
//! literals of the equality's width; any other printed term is one atom, the
//! way carcara's `Polynomial::from_term` ends at it), and the bridge is
//! printed only when the two forms agree exactly, modulo `2^w`, for `f = 1`
//! or `f = -1`. An authored spelling that reads differently (an override
//! that spells a word another way) prints the atom the ordinary way.

use super::*;
use crate::alethe_printer::offset_bridge::printed_factor;
use ay_core::BvOffsetEquality;
use num_bigint::BigInt;
use num_traits::Zero;

impl Circuit<'_, '_, '_> {
    /// `(op a b)`, when it is `(= a b)` between two offset words, through
    /// their shared difference, or `None` to leave the ordinary lowering in
    /// place.
    pub(super) fn offset_equality(
        &mut self,
        op: &str,
        a: TermId,
        b: TermId,
        depth: usize,
    ) -> Option<(i32, Equality)> {
        if op != "=" {
            return None;
        }
        let reading = self.proof.printer.terms.bv_offset_equality(a, b)?;
        let width = usize::try_from(reading.width).ok()?;
        if width == 0 || width > MAX_WIDTH || !self.offset_shares.uses(&reading) {
            return None;
        }
        let printer = self.proof.printer;
        if reading.minuend == reading.subtrahend {
            printer.full_offset_source_surfaces_agree(a, b, reading.width)?;
        }
        let lhs = printer.format_term(a);
        let rhs = printer.format_term(b);
        let minuend = printer.format_term(reading.minuend);
        let subtrahend = printer.format_term(reading.subtrahend);
        let (left, right) = if reading.constant.is_zero() {
            (minuend, subtrahend)
        } else {
            (
                format!("(bvsub {minuend} {subtrahend})"),
                format!("(_ bv{} {width})", reading.constant),
            )
        };
        let factor = printed_factor(&lhs, &rhs, &left, &right, reading.width)?;
        let (left_text, right_text) = (left, right);
        let (left, right) = self.offset_words(&reading, width, depth)?;
        // The words print what the factor was read off (`word` holds every
        // word to its term's printed spelling); never bridge anything else.
        if left.equality.left != left_text || right.equality.left != right_text {
            return None;
        }
        let target = format!("(= {} {})", left.equality.left, right.equality.left);
        let polynomial = self.proof.equality(
            &format!("(bvmul (_ bv1 {width}) (bvsub {lhs} {rhs}))"),
            &format!(
                "(bvmul {factor} (bvsub {} {}))",
                left.equality.left, right.equality.left
            ),
            "poly_simp",
            &[],
        )?;
        let bridge = self.proof.equality(
            &format!("(= {lhs} {rhs})"),
            &target,
            "poly_simp_rel",
            &[&polynomial.step],
        )?;
        let changed = self
            .proof
            .congruence("=", &[left.equality, right.equality])?;
        let bit = self.comparison("=", &left.bits, &right.bits)?;
        let blasted =
            self.proof
                .equality(&changed.right, &self.text(bit)?, "bitblast_equal", &[])?;
        let compared = self.proof.chain(changed, blasted)?;
        Some((bit, self.proof.chain(bridge, compared)?))
    }

    /// The two words the bridged equality compares: the words themselves at
    /// `k = 0`, else their difference (one per pair) and the literal `k`.
    fn offset_words(
        &mut self,
        reading: &BvOffsetEquality,
        width: usize,
        depth: usize,
    ) -> Option<(Word, Word)> {
        let minuend = self.word(reading.minuend, depth + 1)?;
        let subtrahend = self.word(reading.subtrahend, depth + 1)?;
        if minuend.bits.len() != width || subtrahend.bits.len() != width {
            return None;
        }
        if reading.constant.is_zero() {
            return Some((minuend, subtrahend));
        }
        let pair = (reading.minuend, reading.subtrahend);
        let difference = match self.differences.get(&pair) {
            Some(word) => word.clone(),
            None => {
                let word = self.subtract(minuend, subtrahend)?;
                self.differences.insert(pair, word.clone());
                word
            }
        };
        Some((difference, self.literal_word(&reading.constant, width)?))
    }

    /// The literal `(_ bvK width)` and its bits, by `bitblast_const`.
    pub(super) fn literal_word(&mut self, value: &BigInt, width: usize) -> Option<Word> {
        let bits = (0..width)
            .map(|i| self.atom(if value.bit(i as u64) { "true" } else { "false" }))
            .collect::<Option<Vec<_>>>()?;
        let text = self.bit_text(&bits)?;
        let equality = self.proof.equality(
            &format!("(_ bv{value} {width})"),
            &bbterm(&text),
            "bitblast_const",
            &[],
        )?;
        Some(Word { bits, equality })
    }
}

#[cfg(test)]
#[path = "offset_tests.rs"]
mod tests;
