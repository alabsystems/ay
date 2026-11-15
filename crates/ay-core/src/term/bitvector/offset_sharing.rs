// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! When an offset reading pays: it is shared, or it cancels (DR-33 in
//! the development design notes).
//!
//! [`TermStore::bv_offset_equality`] reads `(= (bvadd c1 x) (bvadd c2 y))` as
//! `x - y = c2 - c1`. What an encoding gains from that reading is the
//! SHARING: every equality over the same pair of words compares one
//! subtractor with a constant, so what CDCL learns about `x - y` holds for
//! all of them (external-codegen's coroutine-slot row: 64 such atoms over two base
//! words, 214k conflicts as authored, 2.2k through the shared difference).
//!
//! The reading also gains when it CANCELS: when the sides spell a word that
//! drops out, or one added more than once, the authored circuit carries
//! arithmetic the equality does not depend on, and CDCL must discover that
//! it cancels. external-codegen's `base - src*2^k == base - (src << k)` rows (corpus9
//! 0091-0103) take 0.2-0.8 strict CPU-s read as `src*2^k = src << k`, and
//! 0.5-1.3 as authored.
//!
//! An equality that does neither gains nothing from its reading. It trades
//! the authored circuit for a subtractor of two free words that nothing else
//! uses, and the authored circuit is often the cheaper one or the one the
//! rest of the formula shares: a single constant adder (`x = y + c`), or two
//! negations the formula also compares (`(= (bvneg a) (bvneg b))`).
//! Measured 2026-10-09 against DR-30's tree, where no pair of either query
//! is read twice and nothing cancels: fuzz seed 2541 (16-bit) took 9-13
//! strict CPU-s, against 0.8 with its readings left as authored, because the
//! checker's monolithic refutation of its root lemma ran past the 4M-hint cap
//! at 5.4k conflicts where the authored lowering refutes in 2.5-3.4k; and
//! corpus9 1494.fpbv took 0.6-0.95 CPU-s against 0.53, its search's proof
//! taking another route.
//!
//! So an encoding counts the binary equalities of its scope here, each once,
//! and uses a reading that cancels or whose pair at least two of them read.
//! The search's bit-blaster, the strict checker's lowering and both printer
//! lanes count their own scope: the assertions or the lemma they encode. An
//! equality met outside the counted scope is counted when it is met, so a
//! pair is read from the second equality that reads it on.

use super::*;
use crate::kani_compat::{DetHashMap, DetHashSet};

/// The binary equalities one encoding met, counted by the pair of words
/// their offset reading compares.
#[derive(Clone, Debug, Default)]
pub struct BvOffsetShares {
    /// How many counted equalities read each `(minuend, subtrahend)` pair.
    readers: DetHashMap<(TermId, TermId), u32>,
    /// The `(lhs, rhs)` operands already counted.
    counted: DetHashSet<(TermId, TermId)>,
    /// Terms [`Self::count_reachable`] has walked.
    walked: DetHashSet<TermId>,
    /// What [`Self::reading`] answered for each `(lhs, rhs)`: an equality
    /// keeps its first encoding when a later count would change the answer.
    decided: DetHashMap<(TermId, TermId), bool>,
}

impl BvOffsetShares {
    /// Count `(= lhs rhs)`, once: a later count of the same operands adds
    /// nothing.
    pub fn count(&mut self, terms: &TermStore, lhs: TermId, rhs: TermId) {
        if !self.counted.insert((lhs, rhs)) {
            return;
        }
        if let Some(reading) = terms.bv_offset_equality(lhs, rhs) {
            *self
                .readers
                .entry((reading.minuend, reading.subtrahend))
                .or_insert(0) += 1;
        }
    }

    /// Count every binary `=` among the terms `roots` reach (`distinct` too
    /// when `with_distinct`), each term once across calls. `keep_going` is
    /// asked before each term is walked; a `false` stops the walk, which
    /// leaves the rest uncounted. An uncounted equality is not read until it
    /// is counted, so a stop can only keep an authored encoding.
    pub fn count_reachable(
        &mut self,
        terms: &TermStore,
        roots: impl IntoIterator<Item = TermId>,
        with_distinct: bool,
        keep_going: &mut dyn FnMut() -> bool,
    ) {
        let mut stack: Vec<TermId> = roots.into_iter().collect();
        while let Some(term) = stack.pop() {
            // A root may be an untrusted handle (a checked proof's clause):
            // one outside the store is not walked. Children are interned
            // before their parents, so every term below a stored one is
            // stored.
            if self.walked.contains(&term) || terms.entry_stamp(term).is_none() {
                continue;
            }
            if !keep_going() {
                return;
            }
            self.walked.insert(term);
            match terms.get(term) {
                TermData::App(symbol, args) => {
                    if let (Symbol::Named(name), [lhs, rhs]) = (symbol, args.as_slice()) {
                        if name == "=" || (with_distinct && name == "distinct") {
                            self.count(terms, *lhs, *rhs);
                        }
                    }
                    stack.extend_from_slice(args);
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.extend([*condition, *then_term, *else_term]);
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, bound)| *bound));
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                TermData::Const(_) | TermData::Var(..) => {}
            }
        }
    }

    /// How many terms [`Self::count_reachable`] has walked.
    #[must_use]
    pub fn walked(&self) -> usize {
        self.walked.len()
    }

    /// Whether an encoding uses `reading` (module docs): it cancels, or at
    /// least two counted equalities read its pair.
    #[must_use]
    pub fn uses(&self, reading: &BvOffsetEquality) -> bool {
        reading.cancels
            || self
                .readers
                .get(&(reading.minuend, reading.subtrahend))
                .is_some_and(|&readers| readers >= 2)
    }

    /// Count `(= lhs rhs)` and return its reading when an encoding uses it;
    /// `None` keeps the equality as authored. The first answer for an
    /// equality is kept, so an encoding that meets it again encodes it the
    /// same way.
    pub fn reading(
        &mut self,
        terms: &TermStore,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<BvOffsetEquality> {
        self.count(terms, lhs, rhs);
        let reading = terms.bv_offset_equality(lhs, rhs)?;
        let uses = self.uses(&reading);
        self.decided
            .entry((lhs, rhs))
            .or_insert(uses)
            .then_some(reading)
    }
}

#[cfg(test)]
#[path = "offset_sharing_tests.rs"]
mod tests;
