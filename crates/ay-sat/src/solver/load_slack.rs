// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Load-time slack reclamation (#load-slack-reclaim).
//!
//! # The gap this closes
//!
//! A whole-formula watch build from offset 0 is the moment the formula is known
//! COMPLETE: no further original clause arrives before the solve. Every buffer
//! that grew geometrically while the formula streamed in is therefore sitting
//! on up to a full doubling of capacity it will never use. Measured on the DtAx
//! lowering of `QF_DT/20210312-Bouvier/vlsat3_b99` (51.9M clauses):
//!
//! ```text
//!   clause arena       662 MB slack   (len 259,383,464 of cap 433,028,352 words)
//!   clause_ids         224 MB slack   (indexed by arena WORD offset)
//!   original ledger    174 MB slack
//! ```
//!
//! That slack is untouched address space physically, so it never shows in RSS —
//! but `--memory` trips on `max(counting-allocator live bytes, phys_footprint)`
//! and the counting allocator charges REQUESTED bytes. It is spent budget
//! either way, and this instance sits outside the 8576 MB competition envelope.
//!
//! Shrinking is a `realloc` down: accounted as a plain subtraction, normally
//! satisfied in place, so there is no transient holding the old and new buffers
//! at once. Each buffer has its own 16 MB floor, so a small formula never pays a
//! realloc to reclaim a few kilobytes.
//!
//! # Why it does not move the search
//!
//! `Solver::clause_db_memory_bytes` is the byte trigger behind
//! `should_reduce_db`, so what it reports decides WHEN reduction fires and
//! therefore the search trajectory. Its arena term is already immune —
//! `ClauseArena::memory_bytes` bills the pinned `accounted_words` rather than
//! the real capacity, precisely so the allocator cannot move the cadence. Its
//! other two terms, `clause_ids.capacity()` and `original_ledger.heap_bytes()`,
//! read REAL capacity, so shrinking those would shrink the trigger's basis and
//! silently change the search with every verdict still correct.
//!
//! So the reclaimed bytes are recorded in `ColdState::load_slack_reclaimed_bytes`
//! and added back in `clause_db_memory_bytes`, keeping the trigger on exactly
//! its pre-shrink basis while the real allocation drops.
//!
//! That is the whole exposure. The only other readers of these capacities are
//! `ClauseArena::words_capacity` (dead code), `Solver::memory_stats`
//! (`#[cfg(test)]`, and it SHOULD report the real post-shrink figure), and the
//! `accounted_words` re-seed in `compact`, which assigns a freshly built `Vec`
//! and so is unaffected by what the old one had reserved.
//!
//! BARRIER: `load_slack_reclamation_does_not_move_the_reduce_db_trigger`
//! (`solver::tests::reduction`) fails by exactly the reclaimed byte count if the
//! compensation term is deleted;
//! `shrink_words_to_fit_reclaims_capacity_without_moving_the_memory_heuristic`
//! (`clause_arena::tests`) fails if the arena shrink is wired to
//! `accounted_words`.

use super::*;

impl Solver {
    /// Hand back the reservation slack the three flat load-time buffers hold,
    /// once the formula is known complete.
    ///
    /// See the module note for the measurement, the soundness of the
    /// compensation, and the barrier tests that pin both halves.
    /// No-op unless `start_offset` is 0, i.e. a build over the WHOLE formula:
    /// an incremental attach appends more originals later, so its buffers are
    /// still mid-schedule and their slack is not slack yet.
    pub(super) fn reclaim_load_time_slack(&mut self, start_offset: usize) {
        const MIN_RECLAIM_BYTES: usize = 16 << 20;
        if start_offset != 0 {
            return;
        }

        // Arena: self-compensating (`accounted_words` is pinned).
        self.arena.shrink_words_to_fit();

        // LRAT clause ids: indexed by arena WORD offset, so this is the biggest
        // of the three on a wide formula whenever it is maintained at all.
        let clause_id_slack =
            (self.cold.clause_ids.capacity() - self.cold.clause_ids.len()) * size_of::<u64>();
        if clause_id_slack >= MIN_RECLAIM_BYTES {
            let before = self.cold.clause_ids.capacity() * size_of::<u64>();
            self.cold.clause_ids.shrink_to_fit();
            let after = self.cold.clause_ids.capacity() * size_of::<u64>();
            self.cold.load_slack_reclaimed_bytes += before - after;
        }

        // Original-formula ledger.
        let ledger_reclaimed = self.cold.original_ledger.shrink_to_fit();
        self.cold.load_slack_reclaimed_bytes += ledger_reclaimed;
    }
}
