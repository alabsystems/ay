// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An equality between two OFFSET words, lowered as one difference.
//!
//! `(= (bvadd c1 x) (bvadd c2 y))` and `(= (bvsub x y) (c2 - c1))` are the
//! same Boolean function of `x` and `y`: `Z / 2^w` is a group under addition
//! (`TermStore::bv_offset_equality` reads the equality, and its tests check
//! the reading exhaustively at a small width). Lowered as authored, each such
//! atom is two ripple-carry adders and a comparator, and the producer's
//! refutation re-derives the carry relations atom by atom: external-codegen's
//! coroutine-slot row, 64 byte-address atoms over two base words, ran the
//! LRAT stream past its 32 MiB cap in four seconds and the sweep did not close
//! it (2026-10-08). Lowered through the difference, every atom over one pair
//! of words reads the SAME `Sub` node, which the encoder's gate cache blasts
//! once: the same lemma refutes with 4.6k variables in 0.33 s.
//!
//! A reading is used only when it pays (`ay_core::BvOffsetShares`, DR-33):
//! the census counts the equalities its requests reach before anything is
//! lowered, and an equality that cancels nothing and whose pair no other
//! counted equality reads keeps its authored lowering. Read anyway, such an
//! equality trades the authored circuit for a subtractor nothing else uses:
//! fuzz seed 2541's root lemma, whose four readings each compare a different
//! pair, took 9-13 strict CPU-s read (the monolithic refutation stopped on
//! the 4M-hint cap at 5.4k conflicts) and 0.8 as authored.
//!
//! Nothing is abstracted. The words are lowered exactly as every other term
//! (a word the lowering abstracts is abstracted the same way here), the
//! `bvadd`/`bvsub`/`bvneg` structure around them is read exactly, and the
//! constant is a literal of the equality's width. The census
//! (`lowering_share.rs`) counts the two words as the equality's requests,
//! which is what this lowering asks for.

use super::*;
use ay_core::BvOffsetEquality;

impl ProofProducingLowerer<'_, '_> {
    /// Count the equalities `roots` reach, at most
    /// `MAX_PROOF_PRODUCING_TERM_NODES` terms per lowering: one the count
    /// misses keeps its authored lowering.
    pub(super) fn count_offset_equalities(&mut self, roots: impl IntoIterator<Item = TermId>) {
        let mut room = MAX_PROOF_PRODUCING_TERM_NODES.saturating_sub(self.offset_shares.walked());
        self.offset_shares
            .count_reachable(self.terms, roots, true, &mut || {
                room = room.saturating_sub(1);
                room > 0
            });
    }

    /// `(= lhs rhs)` read as one difference, when the producer's words hold
    /// it and the reading pays (module docs); a wide equality keeps its
    /// slice-by-slice lowering.
    pub(super) fn offset_equality(&self, lhs: TermId, rhs: TermId) -> Option<BvOffsetEquality> {
        // Children are interned before their parents, so two live operands
        // make every term the reading walks live.
        if self.terms.entry_stamp(lhs).is_none()
            || self.terms.entry_stamp(rhs).is_none()
            || self.is_wide(lhs)
        {
            return None;
        }
        self.terms.bv_offset_equality(lhs, rhs).filter(|reading| {
            reading.constant.to_u128().is_some() && self.offset_shares.uses(reading)
        })
    }

    /// `minuend - subtrahend = constant`, or `minuend = subtrahend` at zero.
    pub(super) fn lower_offset_equality(
        &mut self,
        reading: &BvOffsetEquality,
    ) -> Result<BvExpr, String> {
        let (minuend, minuend_width) = self.lower_bv(reading.minuend)?;
        let (subtrahend, subtrahend_width) = self.lower_bv(reading.subtrahend)?;
        Self::require_same_width("=", minuend_width, subtrahend_width)?;
        if minuend_width != reading.width {
            return Err(format!(
                "offset equality over {} bits lowered a {minuend_width}-bit word",
                reading.width
            ));
        }
        let Some(constant) = reading.constant.to_u128() else {
            return Err("offset equality constant is outside the producer's words".to_string());
        };
        Ok(if constant == 0 {
            BvExpr::eq(minuend, subtrahend)
        } else {
            BvExpr::eq(
                BvExpr::sub(minuend, subtrahend),
                BvExpr::const_val(constant, reading.width),
            )
        })
    }
}

#[cfg(test)]
#[path = "offset_equality_tests.rs"]
mod tests;
