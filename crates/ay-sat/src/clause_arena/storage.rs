// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause-arena storage accounting, iteration, and compaction.

use super::*;

impl ClauseArena {
    /// Number of clauses ever added (including deleted, excluding compacted-away).
    #[inline]
    pub(crate) fn num_clauses(&self) -> usize {
        self.num_clauses
    }

    /// Number of currently active clauses.
    ///
    /// Unlike `num_clauses()`, this excludes deleted clauses and therefore
    /// matches the residual formula size seen by inprocessing passes.
    #[inline]
    pub(crate) fn active_clause_count(&self) -> usize {
        self.active_count
    }

    /// Number of active irredundant (non-learned) clauses.
    #[inline]
    pub(crate) fn irredundant_count(&self) -> usize {
        self.irredundant_count
    }

    /// Number of active redundant (learned) clauses.
    ///
    /// This excludes deleted arena slots, so scheduler pressure based on
    /// learned clauses reflects live reduction load rather than historical
    /// allocation churn.
    #[inline]
    pub(crate) fn redundant_count(&self) -> usize {
        self.redundant_count
    }

    /// Override the reported clause count for scheduler-focused tests.
    ///
    /// This is only valid in tests that exercise size-based gates. Production
    /// code must derive the count from actual arena contents.
    #[cfg(test)]
    pub(crate) fn spoof_num_clauses_for_test(&mut self, num_clauses: usize) {
        self.num_clauses = num_clauses;
    }

    /// Override the active clause count for scheduler-focused tests.
    #[cfg(test)]
    pub(crate) fn spoof_active_clause_count_for_test(&mut self, active_clause_count: usize) {
        self.active_count = active_clause_count;
    }

    /// Raw read-only access to the arena word buffer.
    ///
    /// Used by `propagate_bcp_unsafe` to obtain a `*const u32` for direct
    /// pointer-arithmetic literal access, matching CaDiCaL's `lits[k]` pattern.
    #[cfg(feature = "raw-pointer-bcp")]
    #[inline]
    pub(crate) fn words(&self) -> &[u32] {
        &self.words
    }

    /// Issue a software prefetch hint for the clause header at `offset`.
    ///
    /// Prefetches the first cache line of the clause (header + first few
    /// literals). This hides main-memory latency (~60-80 cycles) when the
    /// BCP loop knows it will access a clause's arena data shortly.
    ///
    /// Used in the BCP long-clause path: when a non-binary watcher's blocker
    /// is not satisfied, we will read `arena[clause_ref]`. Prefetching the
    /// next clause's data while processing the current one overlaps the
    /// memory access with computation.
    ///
    /// Reference: CaDiCaL propagate.cpp clause data prefetch pattern (#8000).
    #[inline(always)]
    pub(crate) fn prefetch_clause(&self, offset: usize) {
        // Prefetch word[0] of the clause header. The CPU will bring in the
        // entire cache line (64 bytes = 16 u32 words), which covers the
        // 3-word header + first 13 literal words — enough for most clauses.
        ay_prefetch::prefetch_arena_at(&self.words, offset);
    }

    /// Issue a software prefetch hint for the second cache line of a long clause.
    ///
    /// The first `prefetch_clause()` call brings in 16 u32 words (64-byte cache
    /// line): 3 header words + 13 literal words. Clauses with more than 13
    /// literals spill into a second cache line. This method prefetches that
    /// second line to avoid a stall during the BCP replacement scan.
    ///
    /// Call this after reading the clause header and determining the clause
    /// spills past the first line.
    /// The replacement scan (Gent saved position) accesses literals sequentially,
    /// so the second cache line will be needed shortly after the first.
    ///
    /// Uses L1 prefetch (not L2) because the data is needed within ~10-20 cycles
    /// (the replacement scan is about to start) rather than ~60-80 cycles.
    ///
    /// Reference: #8000 — BCP cache miss reduction.
    #[inline(always)]
    pub(crate) fn prefetch_clause_tail(&self, offset: usize, clause_len: usize) {
        // First cache line covers words [offset..offset+16), i.e. header + lits [0..13).
        // Second cache line starts at words [offset+16..offset+32), i.e. lits [13..29).
        // Only prefetch if the clause actually extends into the second cache line.
        const WORDS_PER_CACHE_LINE: usize = 16; // 64 bytes / 4 bytes per u32
        let total_words = HEADER_WORDS + clause_len;
        if total_words > WORDS_PER_CACHE_LINE {
            ay_prefetch::prefetch_arena_at_l1(&self.words, offset + WORDS_PER_CACHE_LINE);
        }
    }

    /// Total words in the arena. Used for bounds checks: `idx < arena.len()`
    /// works when `idx` is a word offset.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.words.len()
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.words.is_empty()
    }

    /// Iterate over all clause offsets (live and deleted) by walking arena headers.
    pub(crate) fn indices(&self) -> ArenaIter<'_> {
        ArenaIter {
            words: &self.words,
            shrink_map: &self.shrink_map,
            pos: 0,
        }
    }

    /// Iterate over offsets of active (non-deleted) clauses.
    ///
    /// CAUTION: "active" only means "allocated slot with literal data"
    /// (`lit_len_raw != 0`). This INCLUDES garbage-kept husks — clauses
    /// logically deleted via `mark_garbage_keep_data()` / pending-garbage
    /// whose literal data is preserved for reason-pointer windows. Passes
    /// that consume the live formula (occurrence building, census, component
    /// analysis, model verification, falsified-seed scans) must use
    /// `live_indices()` instead. Legitimate uses of `active_indices()` are
    /// the ones that deliberately want husks: reason validation, arena GC
    /// (husks must survive compaction flags-intact), and reaping loops.
    pub(crate) fn active_indices(&self) -> impl Iterator<Item = usize> + '_ {
        self.indices().filter(|&off| self.lit_len_raw(off) != 0)
    }

    /// Iterate over offsets of live clauses: active AND not garbage or
    /// pending-garbage.
    ///
    /// This is the default iterator for formula-semantics consumers.
    /// Garbage-kept husks (see `mark_garbage_keep_data`) are logically
    /// deleted; including them in the live formula has caused false-UNSAT
    /// (decompose phantom strengthening), husk revival through strengthen
    /// paths, and proof-stream corruption (husk adjudication, #8497 family).
    pub(crate) fn live_indices(&self) -> impl Iterator<Item = usize> + '_ {
        self.active_indices()
            .filter(|&off| !self.is_garbage_any(off))
    }

    /// Iterate over active learned-clause offsets.
    ///
    /// This is maintained incrementally by clause add/delete and learned-flag
    /// changes, so learned-only passes do not need to scan the full arena.
    pub(crate) fn learned_indices(&self) -> impl Iterator<Item = usize> + '_ {
        debug_assert_eq!(
            self.learned_offsets.len(),
            self.redundant_count,
            "BUG: learned offset index count must match active redundant count"
        );
        self.learned_offsets.iter().copied()
    }

    /// Iterate over clause offsets starting from `start_offset`.
    ///
    /// Used by incremental watch reconnection (#8093) to iterate only
    /// clauses added after a baseline snapshot (BVE resolvents).
    pub(crate) fn indices_from(&self, start_offset: usize) -> ArenaIter<'_> {
        ArenaIter {
            words: &self.words,
            shrink_map: &self.shrink_map,
            pos: start_offset,
        }
    }

    /// Iterate over offsets of active clauses starting from `start_offset`.
    pub(crate) fn active_indices_from(
        &self,
        start_offset: usize,
    ) -> impl Iterator<Item = usize> + '_ {
        self.indices_from(start_offset)
            .filter(|&off| self.lit_len_raw(off) != 0)
    }

    #[inline]
    pub(crate) fn is_active(&self, offset: usize) -> bool {
        offset < self.words.len() && self.lit_len_raw(offset) != 0
    }

    /// Reorder and compact live clauses into a fresh arena. Returns a flat
    /// remap table where `remap[old_offset] = new_offset` (unmapped offsets
    /// contain `u32::MAX`).
    ///
    /// Clauses are copied in the order specified by `order` (word offsets of
    /// live clauses). Only `HEADER_WORDS + current_lit_len` words are copied
    /// per clause, healing any shrink gaps from `replace()`.
    ///
    /// Reference: CaDiCaL collect.cpp:385-399 (arenatype=3).
    pub(crate) fn compact_reorder(&mut self, order: &[u32]) -> Vec<u32> {
        let mut remap = vec![u32::MAX; self.words.len()];
        let estimated_live = self.active_count * (HEADER_WORDS + 8);
        let mut new_words = Vec::with_capacity(estimated_live);
        let mut new_clause_count = 0usize;
        let mut new_active_count = 0usize;
        let mut new_irredundant = 0usize;
        let mut new_redundant = 0usize;
        let mut new_learned_offsets = Vec::with_capacity(self.learned_offsets.len());
        let mut new_learned_offset_index = DetHashMap::default();
        let mut new_signatures: DetHashMap<u32, ClauseSignature> = DetHashMap::default();

        for &old_off in order {
            let off = old_off as usize;
            let lit_len = self.lit_len_raw(off) as usize;
            if lit_len == 0 {
                // Deleted clause snuck into order — skip.
                continue;
            }
            let new_off = new_words.len();
            // Copy header + current literals (not the original alloc tail).
            let end = off + HEADER_WORDS + lit_len;
            debug_assert!(
                end <= self.words.len(),
                "BUG: compact_reorder clause at {off} extends past arena (end={end}, len={})",
                self.words.len()
            );
            new_words.extend_from_slice(&self.words[off..end]);
            // Carry the side-table signature to the clause's new offset.
            let signature = self
                .signatures
                .get(&(off as u32))
                .copied()
                .unwrap_or_else(|| compute_clause_signature(self.literals(off)));
            new_signatures.insert(new_off as u32, signature);
            remap[off] = new_off as u32;
            new_clause_count += 1;
            new_active_count += 1;
            if self.is_learned(off) {
                new_redundant += 1;
                let pos = new_learned_offsets.len();
                new_learned_offsets.push(new_off);
                new_learned_offset_index.insert(new_off, pos);
            } else {
                new_irredundant += 1;
            }
        }

        self.words = new_words;
        self.num_clauses = new_clause_count;
        self.active_count = new_active_count;
        self.irredundant_count = new_irredundant;
        self.redundant_count = new_redundant;
        self.learned_offsets = new_learned_offsets;
        self.learned_offset_index = new_learned_offset_index;
        self.shrink_map.clear();
        self.signatures = new_signatures;
        self.dead_words = 0;
        remap
    }

    /// Arena size in layout-invariant "accounting words": the length the word
    /// buffer would have had with the legacy 5-word header (signature inline).
    ///
    /// Every clause added since the last compaction contributes exactly
    /// `LEGACY_ACCOUNTING_HEADER_WORDS - HEADER_WORDS` fewer physical words
    /// than it did pre-R2, so adding that delta per clause reproduces the
    /// legacy length bit-for-bit. GC/compaction cadence heuristics
    /// (`should_compact_arena`, `adaptive_compaction_threshold_pct`) consume
    /// these units so the R2 header slimming — a pure layout change — cannot
    /// shift compaction timing and thereby the search trajectory.
    #[inline]
    pub(crate) fn accounting_len(&self) -> usize {
        self.words.len() + (LEGACY_ACCOUNTING_HEADER_WORDS - HEADER_WORDS) * self.num_clauses
    }

    /// Dead words in the same layout-invariant accounting units as
    /// `accounting_len`.
    ///
    /// `delete()` accrues `HEADER_WORDS + alloc_len` per clause; the legacy
    /// value was `LEGACY_ACCOUNTING_HEADER_WORDS + alloc_len`. The number of
    /// deleted-but-not-yet-compacted clauses is `num_clauses - active_count`
    /// (both reset together on compaction), so adding the per-clause header
    /// delta reproduces the legacy dead-word count bit-for-bit. `replace()`
    /// shrink tails carry no header and need no adjustment.
    #[inline]
    pub(crate) fn accounting_dead_words(&self) -> usize {
        self.dead_words
            + (LEGACY_ACCOUNTING_HEADER_WORDS - HEADER_WORDS)
                * self.num_clauses.saturating_sub(self.active_count)
    }

    #[inline]
    pub(super) fn lit_len_raw(&self, off: usize) -> u16 {
        (self.words[off] & 0xFFFF) as u16
    }

    #[inline]
    pub(crate) fn len_of(&self, offset: usize) -> usize {
        self.lit_len_raw(offset) as usize
    }

    #[inline]
    pub(crate) fn is_empty_clause(&self, offset: usize) -> bool {
        self.lit_len_raw(offset) == 0
    }

    #[cfg(test)]
    #[inline]
    pub(crate) fn saved_pos(&self, offset: usize) -> usize {
        (self.words[offset + 2] & 0xFFFF) as usize
    }

    #[inline]
    pub(crate) fn set_saved_pos(&mut self, offset: usize, pos: usize) {
        let w = offset + 2;
        let pos16 = pos.min(u16::MAX as usize) as u16;
        self.words[w] = (self.words[w] & 0xFFFF_0000) | u32::from(pos16);
    }

    #[inline]
    pub(super) fn flags(&self, off: usize) -> u16 {
        (self.words[off + 2] >> 16) as u16
    }

    #[inline]
    pub(super) fn set_flags(&mut self, off: usize, flags: u16) {
        self.words[off + 2] = (self.words[off + 2] & 0x0000_FFFF) | (u32::from(flags) << 16);
    }

    /// Total words in the arena backing store. Test-only (production uses `len()`).
    #[cfg(test)]
    pub(crate) fn total_words(&self) -> usize {
        self.words.len()
    }

    /// Remove deleted clauses in arena order. Returns (old_offset, new_offset) remapping.
    ///
    /// This is the simple sequential-order compaction used in unit tests.
    /// Production code uses `compact_reorder()` instead, which accepts an
    /// explicit visit order (VMTF queue) for cache-locality optimization.
    /// Both methods invalidate all `ClauseRef` values; the solver-level
    /// `compact_arena_locality()` in `arena_gc.rs` handles the full remapping.
    #[cfg(test)]
    pub(crate) fn compact(&mut self) -> Vec<(usize, usize)> {
        let mut new_words = Vec::new();
        let mut remapping = Vec::new();
        let mut new_clause_count = 0usize;
        let mut new_active_count = 0usize;
        let mut new_irredundant = 0usize;
        let mut new_redundant = 0usize;
        let mut new_learned_offsets = Vec::with_capacity(self.learned_offsets.len());
        let mut new_learned_offset_index = DetHashMap::default();
        let mut new_signatures: DetHashMap<u32, ClauseSignature> = DetHashMap::default();
        let mut pos = 0;

        while pos < self.words.len() {
            let current_len = self.lit_len_raw(pos) as usize;
            let alloc_len = if current_len == 0 {
                (self.words[pos + 1] & 0xFFFF) as usize
            } else if let Some(&orig) = self.shrink_map.get(&(pos as u32)) {
                orig as usize
            } else {
                current_len
            };
            debug_assert!(alloc_len > 0, "BUG: zero alloc_len at pos {pos}");

            if current_len > 0 {
                // Live clause: copy header + current literals (not dead tail).
                let new_off = new_words.len();
                new_words.extend_from_slice(&self.words[pos..pos + HEADER_WORDS + current_len]);
                let signature = self
                    .signatures
                    .get(&(pos as u32))
                    .copied()
                    .unwrap_or_else(|| compute_clause_signature(self.literals(pos)));
                new_signatures.insert(new_off as u32, signature);
                remapping.push((pos, new_off));
                new_clause_count += 1;
                new_active_count += 1;
                if self.is_learned(pos) {
                    new_redundant += 1;
                    let learned_pos = new_learned_offsets.len();
                    new_learned_offsets.push(new_off);
                    new_learned_offset_index.insert(new_off, learned_pos);
                } else {
                    new_irredundant += 1;
                }
            }

            pos += HEADER_WORDS + alloc_len;
        }

        self.words = new_words;
        self.num_clauses = new_clause_count;
        self.active_count = new_active_count;
        self.irredundant_count = new_irredundant;
        self.redundant_count = new_redundant;
        self.learned_offsets = new_learned_offsets;
        self.learned_offset_index = new_learned_offset_index;
        self.shrink_map.clear();
        self.signatures = new_signatures;
        self.dead_words = 0;
        remapping
    }
}
