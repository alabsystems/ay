// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rolling back the arena's last appends, for clauses the solver holds only
//! for a moment (congruence's XOR ladder rungs, which a run without a proof
//! never adds): after `rollback_appends` the arena is word for word, count
//! for count and in its `memory_bytes` charge what it was at `append_mark`,
//! so later clauses get the offsets, and reduction the cadence, they would
//! have had. Only for irredundant appends: a learned add grows the learned
//! index (`learned_offsets`, `learned_offset_index`), whose capacities
//! `memory_bytes` reads and which a removal does not shrink.

use super::*;

/// The arena's length and memory charge at one moment (`append_mark`).
#[derive(Clone, Copy, Debug)]
pub(crate) struct ArenaAppendMark {
    words: usize,
    accounted_words: usize,
}

impl ClauseArena {
    /// The point `rollback_appends` returns the arena to.
    pub(crate) fn append_mark(&self) -> ArenaAppendMark {
        ArenaAppendMark {
            words: self.words.len(),
            accounted_words: self.accounted_words,
        }
    }

    /// Remove every clause added since `mark`. Nothing may have deleted,
    /// shrunk or compacted the arena since, and every append must have been
    /// irredundant: the clause counts and the `memory_bytes` charge
    /// (`accounted_words`, `phantom_signature_entries`) return to their
    /// values at the mark.
    pub(crate) fn rollback_appends(&mut self, mark: ArenaAppendMark) {
        debug_assert!(
            mark.words <= self.words.len(),
            "BUG: rollback_appends past a compaction"
        );
        let appended: Vec<usize> = self.indices_from(mark.words).collect();
        if appended.is_empty() {
            return;
        }
        // Newest first: a learned offset is then the last of
        // `learned_offsets`, so removing it moves no older entry.
        for &off in appended.iter().rev() {
            debug_assert!(
                self.is_active(off),
                "BUG: rollback_appends over a deleted clause"
            );
            debug_assert!(
                !self.is_learned(off),
                "BUG: rollback_appends over a learned clause (index capacity not restored)"
            );
            if self.is_active(off) {
                if self.is_learned(off) {
                    self.remove_learned_offset(off);
                    self.redundant_count = self.redundant_count.saturating_sub(1);
                } else {
                    self.irredundant_count = self.irredundant_count.saturating_sub(1);
                }
                self.active_count = self.active_count.saturating_sub(1);
            }
            self.num_clauses = self.num_clauses.saturating_sub(1);
            self.phantom_signature_entries = self.phantom_signature_entries.saturating_sub(1);
        }
        self.words.truncate(mark.words);
        self.accounted_words = mark.accounted_words;
        // An append alone needs no bump (`formula_epoch`), but a consumer
        // caching the live formula by offset must drop the removed clauses.
        self.bump_formula_epoch();
    }
}
