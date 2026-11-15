// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mint-site provenance of the div/mod PURIFICATION pairs.
//!
//! The executor's `mod_div_elim` replaces `(div x k)` / `(mod x k)`, for a
//! non-zero integer literal `k`, by a fresh quotient `q` and remainder `r` and
//! asserts `x = k*q + r`, `0 <= r`, `r < |k|`. This side table records, at
//! that single creation site, the `(x, k)` each pair was minted for, so the
//! proof producer can define `q := (div x k)` and `r := (mod x k)` from what
//! the elimination actually did. It never has to reconstruct the pair from
//! symbol names or from which purification atoms a refutation happened to use.
//! A refutation through `(< r 3)` and the rewritten `(< 2 r)` alone mentions
//! neither `q` nor the equation.
//!
//! PRODUCER-ONLY, unlike `skolem_choice`. Neither the solver nor the strict
//! checker reads it. A `divmod_def` step carries its definientia in its own
//! `:args`, and the checker decides them from those
//! (`proof_validation::recognize_divmod_def`, `FreshDefRegistry`). A missing,
//! stale or wrong entry can therefore only cost a strictly checked proof. It
//! can never admit one and never changes a verdict. That is why it is not one
//! of the checker-visible metadata families and bumps no generation counter.
//!
//! Keyed by BOTH symbols, so a lookup from either one finds the pair. Every
//! value holds four `TermId`s, so `rollback_to` drops an entry if any of them
//! is truncated away, and `mark_and_compact` moves it or drops it.

use super::{RemapTable, TermStore};
use crate::term::{Constant, TermData, TermId};
use crate::Sort;

/// One purification pair as `mod_div_elim` minted it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DivModPurification {
    /// The fresh quotient, standing for `(div dividend divisor)`.
    pub quotient: TermId,
    /// The fresh remainder, standing for `(mod dividend divisor)`.
    pub remainder: TermId,
    /// The (rewritten) dividend the pair was minted for.
    pub dividend: TermId,
    /// The non-zero `Int` literal divisor.
    pub divisor: TermId,
}

impl DivModPurification {
    fn term_ids(self) -> [TermId; 4] {
        [self.quotient, self.remainder, self.dividend, self.divisor]
    }
}

impl TermStore {
    /// Record a purification pair. Call only from the mint site, with the
    /// pair and the `(dividend, divisor)` the elimination actually used.
    ///
    /// A no-op unless `quotient` and `remainder` are two distinct `Int`
    /// variables, `dividend` is `Int`-sorted and `divisor` is a non-zero `Int`
    /// literal: no other shape is a purification, and an entry the producer
    /// could not use is better absent.
    pub fn register_divmod_purification(&mut self, pair: DivModPurification) {
        let int_var = |term: TermId| {
            matches!(self.get(term), TermData::Var(..)) && matches!(self.sort(term), Sort::Int)
        };
        let literal = matches!(
            self.get(pair.divisor),
            TermData::Const(Constant::Int(k)) if !num_traits::Zero::is_zero(k)
        );
        if pair.quotient == pair.remainder
            || !int_var(pair.quotient)
            || !int_var(pair.remainder)
            || !matches!(self.sort(pair.dividend), Sort::Int)
            || !literal
        {
            return;
        }
        self.divmod_purification.insert(pair.quotient, pair);
        self.divmod_purification.insert(pair.remainder, pair);
    }

    /// The purification pair `symbol` is the quotient or remainder of, if the
    /// mint site recorded one.
    #[must_use]
    pub fn divmod_purification(&self, symbol: TermId) -> Option<DivModPurification> {
        self.divmod_purification.get(&symbol).copied()
    }

    /// Whether any purification pair was ever recorded. This lets a consumer
    /// skip its traversal on a div/mod-free problem.
    #[must_use]
    pub fn has_divmod_purifications(&self) -> bool {
        !self.divmod_purification.is_empty()
    }

    /// `rollback_to`: drop every entry naming a truncated term.
    pub(super) fn retain_divmod_purifications_below(&mut self, len: usize) {
        self.divmod_purification.retain(|key, pair| {
            (key.0 as usize) < len && pair.term_ids().iter().all(|id| (id.0 as usize) < len)
        });
    }

    /// `mark_and_compact`: move every entry with the arena, dropping one any of
    /// whose terms was reclaimed.
    pub(super) fn remap_divmod_purifications(&mut self, remap: &RemapTable) {
        let old = std::mem::take(&mut self.divmod_purification);
        for (key, pair) in old {
            let (Some(key), Some(quotient), Some(remainder), Some(dividend), Some(divisor)) = (
                remap.get(key),
                remap.get(pair.quotient),
                remap.get(pair.remainder),
                remap.get(pair.dividend),
                remap.get(pair.divisor),
            ) else {
                continue;
            };
            let moved = DivModPurification {
                quotient,
                remainder,
                dividend,
                divisor,
            };
            self.divmod_purification.insert(key, moved);
        }
    }
}

#[cfg(test)]
#[path = "divmod_purification_tests.rs"]
mod tests;
