// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::mem::size_of;

/// Snapshot of the clause header words used by the BCP long-clause path.
///
/// Caches word[0] (literal count) and word[2] (saved_pos + flags) from a
/// single call site. This avoids re-reading both header words for the
/// garbage, vivify-skip, saved-position, and clause-length checks, and
/// eliminates the separate `arena.literals()` call (which goes through
/// `bytemuck::cast_slice` + bounds-checked slice creation).
#[derive(Clone, Copy)]
pub(crate) struct ClauseBcpHeader {
    word: u32,
    /// Clause literal count from word[0], cached to avoid re-reading.
    len: usize,
}

impl ClauseBcpHeader {
    #[inline]
    pub(crate) fn saved_pos(self) -> usize {
        (self.word & 0xFFFF) as usize
    }

    #[inline]
    pub(crate) fn is_garbage_any(self) -> bool {
        ((self.word >> 16) as u16) & (GARBAGE_BIT | PENDING_GARBAGE_BIT) != 0
    }

    #[inline]
    pub(crate) fn is_vivify_skipped(self) -> bool {
        ((self.word >> 16) as u16) & VIVIFY_SKIP_BIT != 0
    }

    #[inline]
    pub(crate) fn is_learned(self) -> bool {
        ((self.word >> 16) as u16) & LEARNED_BIT != 0
    }

    /// Clause literal count, cached from word[0] at header read time.
    #[inline]
    pub(crate) fn clause_len(self) -> usize {
        self.len
    }
}

impl ClauseArena {
    /// Read the BCP-relevant header words once for the long-clause slow path.
    ///
    /// Reads both word[0] (literal count) and word[2] (saved_pos + flags)
    /// in one call. The clause length is cached in the header struct so
    /// the BCP loop can skip the `arena.literals()` call entirely and use
    /// direct `bcp_literal()` access instead.
    #[inline]
    pub(crate) fn bcp_header(&self, offset: usize) -> ClauseBcpHeader {
        ClauseBcpHeader {
            word: self.words[offset + 2],
            len: (self.words[offset] & 0xFFFF) as usize,
        }
    }

    /// Unchecked BCP header read via raw pointer (#8465).
    ///
    /// Same semantics as `bcp_header()` but uses a pre-computed raw pointer
    /// to bypass bounds checks in the unsafe BCP hot path. The caller
    /// provides `words_ptr` (cached at the top of the BCP loop) and
    /// guarantees `offset + 2 < self.words.len()`.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    ///  1. `words_ptr == self.words.as_ptr()` — i.e. the pointer was taken
    ///     from the same `ClauseArena::words` Vec as `self`. In particular
    ///     no mutation that reallocates `self.words` has occurred since the
    ///     pointer was captured.
    ///  2. `offset + 2 < self.words.len()`. This holds for every live clause
    ///     header because `ClauseArena::allocate` reserves at least
    ///     `HEADER_WORDS == 3` words per clause, and `offset` is produced by
    ///     the clause allocator or a validated watch-list entry.
    ///  3. No concurrent writes to `self.words[offset..offset+3]` — this
    ///     method takes `&self`, so Rust's aliasing rules plus `raw-pointer-bcp`'s
    ///     single-threaded BCP loop discipline suffice.
    ///
    /// Under those preconditions, the two `*words_ptr.add(..)` reads below
    /// dereference pointers that lie within the `self.words` allocation and
    /// are properly aligned (raw `Vec<u32>` storage). The fn is marked
    /// `unsafe` so the bounds / validity contract is surfaced to callers.
    #[cfg(feature = "raw-pointer-bcp")]
    #[inline(always)]
    #[allow(unsafe_code)]
    pub(crate) unsafe fn bcp_header_unchecked(
        &self,
        words_ptr: *const u32,
        offset: usize,
    ) -> ClauseBcpHeader {
        // SAFETY: Per the fn-level `# Safety` contract, `words_ptr` aliases
        // `self.words[0]` and `offset < self.words.len()`, so
        // `words_ptr.add(offset)` produces a pointer to a valid, initialized
        // `u32` inside the Vec's buffer. Reading that `u32` is sound: the
        // Vec is not dropped (held behind `&self`) and no concurrent
        // writer exists during BCP (the whole `raw-pointer-bcp` loop is
        // single-threaded and holds `&mut Solver` via its caller).
        let len = unsafe { (*words_ptr.add(offset) & 0xFFFF) as usize };
        // SAFETY: Per the fn-level `# Safety` contract, `offset + 2 <
        // self.words.len()`, so `words_ptr.add(offset + 2)` is likewise a
        // pointer into the Vec's buffer and the `u32` it points to is
        // initialized (written at clause-allocation time in
        // `ClauseArena::allocate`, which always writes all `HEADER_WORDS`
        // header words before publishing the clause offset). Same
        // aliasing argument as above.
        let word = unsafe { *words_ptr.add(offset + 2) };
        ClauseBcpHeader { word, len }
    }

    /// Unchecked literal access for the BCP hot path.
    ///
    /// Returns the literal at position `idx` within the clause at `offset`,
    /// bypassing bounds checks in release builds (via `ay_prefetch::word_at`).
    /// This matches CaDiCaL's `lits[k]` raw pointer pattern.
    ///
    /// # Safety contract
    ///
    /// Caller must ensure `offset + HEADER_WORDS + idx < self.words.len()`.
    /// This is guaranteed by construction: clause offsets and lengths are
    /// validated at insertion time, and `idx < clause_len` is maintained
    /// by the BCP replacement scan loop bounds.
    #[inline(always)]
    pub(crate) fn bcp_literal(&self, offset: usize, idx: usize) -> Literal {
        Literal(ay_prefetch::word_at(
            &self.words,
            offset + HEADER_WORDS + idx,
        ))
    }

    #[inline]
    pub(crate) fn is_garbage(&self, offset: usize) -> bool {
        self.flags(offset) & GARBAGE_BIT != 0
    }

    /// Mark a clause as garbage without zeroing its literal data.
    ///
    /// Matches CaDiCaL's `mark_garbage()`: sets the garbage flag so BCP skips
    /// the clause, but keeps literal data intact. Used by eager subsumption
    /// (analyze.cpp:728-766) where the clause might still serve as a reason
    /// for an assigned variable. The clause is fully deleted during the next
    /// `reduce_db` or garbage collection pass.
    #[inline]
    pub(crate) fn mark_garbage_keep_data(&mut self, offset: usize) {
        debug_assert!(offset < self.words.len(), "BUG: mark_garbage out of bounds");
        debug_assert!(
            self.lit_len_raw(offset) != 0,
            "BUG: mark_garbage on already-deleted clause"
        );
        let mut f = self.flags(offset);
        f |= GARBAGE_BIT;
        self.set_flags(offset, f);
    }

    /// Set the garbage flag directly. Test-only; production manages garbage
    /// internally through `delete()`, `replace()`, and `mark_garbage_keep_data()`.
    #[cfg(test)]
    pub(crate) fn set_garbage(&mut self, offset: usize, garbage: bool) {
        let mut f = self.flags(offset);
        if garbage {
            f |= GARBAGE_BIT;
        } else {
            f &= !GARBAGE_BIT;
        }
        self.set_flags(offset, f);
    }

    /// Combined garbage check: returns true if either garbage or pending-garbage.
    /// Single flags() read + single bitmask test avoids two separate word reads
    /// in the BCP hot loop. CaDiCaL propagate.cpp:264 checks `c->garbage` which
    /// covers both states.
    #[inline]
    pub(crate) fn is_garbage_any(&self, offset: usize) -> bool {
        self.flags(offset) & (GARBAGE_BIT | PENDING_GARBAGE_BIT) != 0
    }

    #[inline]
    pub(crate) fn is_pending_garbage(&self, offset: usize) -> bool {
        self.flags(offset) & PENDING_GARBAGE_BIT != 0
    }

    #[inline]
    pub(crate) fn set_pending_garbage(&mut self, offset: usize, pending: bool) {
        let mut f = self.flags(offset);
        if pending {
            f |= PENDING_GARBAGE_BIT;
        } else {
            f &= !PENDING_GARBAGE_BIT;
        }
        self.set_flags(offset, f);
    }

    /// Combined liveness check for BCP: returns true if clause is deleted,
    /// garbage, or pending garbage. Single branch replaces three separate
    /// checks in the BCP hot loop.
    #[inline]
    pub(crate) fn is_dead(&self, offset: usize) -> bool {
        self.lit_len_raw(offset) == 0
            || self.flags(offset) & (GARBAGE_BIT | PENDING_GARBAGE_BIT) != 0
    }

    #[inline]
    pub(crate) fn is_learned(&self, offset: usize) -> bool {
        self.flags(offset) & LEARNED_BIT != 0
    }

    /// Combined candidate filter for eager subsumption (instruction-shave #2).
    ///
    /// Returns `Some(len)` iff the clause at `offset` is active (non-deleted),
    /// learned, and not garbage — i.e. exactly the clauses the previous
    /// `is_active() && is_learned() && !is_garbage()` + `len_of()` accessor
    /// sequence accepted — but with a single bounds check and one read each
    /// of the two header words (word[0] length, word[2] flags) instead of
    /// four separate bounds-checked reads. CaDiCaL's equivalent is a single
    /// `Clause*` header load covering `d->garbage` / `d->redundant` / `d->size`
    /// (analyze.cpp:740-746).
    ///
    /// Deliberately checks `GARBAGE_BIT` only (not `PENDING_GARBAGE_BIT`),
    /// preserving the exact predicate of the original accessor sequence.
    #[inline]
    pub(crate) fn eager_subsume_candidate_len(&self, offset: usize) -> Option<usize> {
        // Mirrors `is_active`: out-of-bounds offsets are treated as inactive.
        if offset >= self.words.len() {
            return None;
        }
        let len = (self.words[offset] & 0xFFFF) as usize;
        if len == 0 {
            return None;
        }
        let flags = (self.words[offset + 2] >> 16) as u16;
        if flags & LEARNED_BIT == 0 || flags & GARBAGE_BIT != 0 {
            return None;
        }
        Some(len)
    }

    #[inline]
    pub(crate) fn set_learned(&mut self, offset: usize, learned: bool) {
        let was_learned = self.is_learned(offset);
        let is_active = self.lit_len_raw(offset) != 0;
        let mut f = self.flags(offset);
        if learned {
            f |= LEARNED_BIT;
        } else {
            f &= !LEARNED_BIT;
        }
        self.set_flags(offset, f);
        if is_active && was_learned != learned {
            if learned {
                self.irredundant_count = self.irredundant_count.saturating_sub(1);
                self.redundant_count += 1;
                self.insert_learned_offset(offset);
            } else {
                self.remove_learned_offset(offset);
                self.redundant_count = self.redundant_count.saturating_sub(1);
                self.irredundant_count += 1;
            }
        }
    }

    #[inline]
    pub(crate) fn used(&self, offset: usize) -> u8 {
        ((self.flags(offset) & USED_MASK) >> USED_SHIFT) as u8
    }

    #[inline]
    pub(crate) fn set_used(&mut self, offset: usize, val: u8) {
        let clamped = u16::from(val.min(MAX_USED));
        let mut f = self.flags(offset);
        f = (f & !USED_MASK) | ((clamped << USED_SHIFT) & USED_MASK);
        self.set_flags(offset, f);
    }

    #[inline]
    pub(crate) fn decay_used(&mut self, offset: usize) {
        let current = self.used(offset);
        self.set_used(offset, current.saturating_sub(1));
    }

    #[cfg(test)]
    #[inline]
    pub(crate) fn is_vivify_skipped(&self, offset: usize) -> bool {
        self.flags(offset) & VIVIFY_SKIP_BIT != 0
    }

    #[inline]
    pub(crate) fn set_vivify_skip(&mut self, offset: usize, skip: bool) {
        let mut f = self.flags(offset);
        if skip {
            f |= VIVIFY_SKIP_BIT;
        } else {
            f &= !VIVIFY_SKIP_BIT;
        }
        self.set_flags(offset, f);
    }

    /// Returns true if this clause was produced by hyper binary or ternary
    /// resolution. CaDiCaL clause.hpp:46 `bool hyper : 1`.
    #[inline]
    pub(crate) fn is_hyper(&self, offset: usize) -> bool {
        self.flags(offset) & HYPER_BIT != 0
    }

    /// Mark or unmark a clause as a hyper resolvent.
    #[inline]
    pub(crate) fn set_hyper(&mut self, offset: usize, hyper: bool) {
        let mut f = self.flags(offset);
        if hyper {
            f |= HYPER_BIT;
        } else {
            f &= !HYPER_BIT;
        }
        self.set_flags(offset, f);
    }

    /// CaDiCaL `c->subsume`: true if this clause should be tried as a
    /// subsumption candidate in the current forward subsumption round.
    #[inline]
    pub(crate) fn is_subsume_candidate(&self, offset: usize) -> bool {
        self.flags(offset) & SUBSUME_TRIED_BIT != 0
    }

    /// Set or clear the per-clause subsumption candidate flag.
    #[inline]
    pub(crate) fn set_subsume_candidate(&mut self, offset: usize, val: bool) {
        let mut f = self.flags(offset);
        if val {
            f |= SUBSUME_TRIED_BIT;
        } else {
            f &= !SUBSUME_TRIED_BIT;
        }
        self.set_flags(offset, f);
    }

    /// CaDiCaL `c->conditioned`: tried as conditioning candidate.
    #[inline]
    pub(crate) fn is_conditioned(&self, offset: usize) -> bool {
        self.flags(offset) & CONDITIONED_BIT != 0
    }

    /// Set/clear per-clause conditioned flag.
    #[inline]
    pub(crate) fn set_conditioned(&mut self, offset: usize, val: bool) {
        let mut f = self.flags(offset);
        if val {
            f |= CONDITIONED_BIT;
        } else {
            f &= !CONDITIONED_BIT;
        }
        self.set_flags(offset, f);
    }

    /// CaDiCaL `c->instantiated`: clause has been tried by post-BVE
    /// instantiation (CaDiCaL instantiate.cpp:211).
    #[inline]
    pub(crate) fn is_instantiated(&self, offset: usize) -> bool {
        self.flags(offset) & INSTANTIATED_BIT != 0
    }

    /// Set/clear per-clause instantiated flag.
    #[inline]
    pub(crate) fn set_instantiated(&mut self, offset: usize, val: bool) {
        let mut f = self.flags(offset);
        if val {
            f |= INSTANTIATED_BIT;
        } else {
            f &= !INSTANTIATED_BIT;
        }
        self.set_flags(offset, f);
    }

    /// Returns true if this clause is an IC3 lemma (blocking clause added
    /// between IC3 queries).
    ///
    /// IC3 lemmas are protected from clause reduction to prevent false UNSAT
    /// on consecution queries. GipSAT equivalent: `ClauseKind::Lemma`.
    #[inline]
    pub(crate) fn is_ic3_lemma(&self, offset: usize) -> bool {
        self.flags(offset) & IC3_LEMMA_BIT != 0
    }

    /// Mark or unmark a clause as an IC3 lemma.
    ///
    /// Set by `add_ic3_lemma()` when IC3/PDR adds blocking clauses between
    /// incremental queries. IC3 lemma clauses are protected from
    /// `reduce_db` deletion and `between_solve_reduce` aging.
    #[inline]
    pub(crate) fn set_ic3_lemma(&mut self, offset: usize, val: bool) {
        let mut f = self.flags(offset);
        if val {
            f |= IC3_LEMMA_BIT;
        } else {
            f &= !IC3_LEMMA_BIT;
        }
        self.set_flags(offset, f);
    }

    /// Read the user-scope depth at which this clause was learned (0-3,
    /// saturated). Ported from Z3 PR #9221 `sat_clause.h::scope_lim()`.
    ///
    /// Only meaningful for learned clauses — irredundant input clauses should
    /// be 0. See `set_scope_lim` for saturation semantics.
    #[inline]
    pub(crate) fn scope_lim(&self, offset: usize) -> u16 {
        (self.flags(offset) & SCOPE_LIM_MASK) >> SCOPE_LIM_SHIFT
    }

    /// Record the user-scope depth at which a learned clause was created.
    ///
    /// Values above `SCOPE_LIM_MAX` (3) are saturated to 3. This stamp is used
    /// by `pop()` (see `Solver::pop`) to delete learned clauses whose recorded
    /// scope depth exceeds the new post-pop scope depth, matching the Z3 fix
    /// for the push/pop learned-clause leak (Z3 PR #9221).
    #[inline]
    pub(crate) fn set_scope_lim(&mut self, offset: usize, depth: u16) {
        let clamped = depth.min(SCOPE_LIM_MAX);
        let mut f = self.flags(offset);
        f = (f & !SCOPE_LIM_MASK) | ((clamped << SCOPE_LIM_SHIFT) & SCOPE_LIM_MASK);
        self.set_flags(offset, f);
    }

    #[inline]
    pub(crate) fn lbd(&self, offset: usize) -> u32 {
        u32::from((self.words[offset] >> 16) as u16)
    }

    #[inline]
    pub(crate) fn set_lbd(&mut self, offset: usize, lbd: u32) {
        let lbd16 = lbd.min(u32::from(u16::MAX)) as u16;
        self.words[offset] = (self.words[offset] & 0x0000_FFFF) | (u32::from(lbd16) << 16);
    }

    /// 64-bit clause signature (bloom filter over variables+polarity) for
    /// subsumption/BVE pre-filtering. Lives in the `signatures` side table
    /// since the R2 header slimming — BCP never reads it, so it is not worth
    /// 8 bytes in every hot clause header.
    #[inline]
    pub(crate) fn signature(&self, offset: usize) -> ClauseSignature {
        debug_assert!(
            self.signatures.contains_key(&(offset as u32)),
            "BUG: signature() on offset {offset} with no side-table entry"
        );
        // Every clause offset is produced by `add` (or remapped by compaction),
        // both of which populate the side table, so the fallback is a
        // release-mode safety net only. The signature is a pure function of the
        // literals, so recomputing yields the same value `refresh_signature`
        // would have stored.
        self.signatures
            .get(&(offset as u32))
            .copied()
            .unwrap_or_else(|| compute_clause_signature(self.literals(offset)))
    }

    /// Read the activity slot (header word 1) as f32. Test-only; clause activity
    /// was removed from production code in #5132 (CaDiCaL uses no clause activity).
    #[cfg(test)]
    #[inline]
    pub(crate) fn activity(&self, offset: usize) -> f32 {
        f32::from_bits(self.words[offset + 1])
    }

    /// Write the activity slot (header word 1) as f32. Test-only.
    #[cfg(test)]
    #[inline]
    pub(crate) fn set_activity(&mut self, offset: usize, activity: f32) {
        self.words[offset + 1] = activity.to_bits();
    }

    #[inline]
    pub(crate) fn literal(&self, offset: usize, idx: usize) -> Literal {
        Literal(self.words[offset + HEADER_WORDS + idx])
    }

    /// Set a single literal by index. Test-only; production uses `literals_mut()`.
    #[cfg(test)]
    pub(crate) fn set_literal(&mut self, offset: usize, idx: usize, lit: Literal) {
        self.words[offset + HEADER_WORDS + idx] = lit.0;
    }

    #[inline]
    pub(crate) fn watched_literals(&self, offset: usize) -> (Literal, Literal) {
        let base = offset + HEADER_WORDS;
        (Literal(self.words[base]), Literal(self.words[base + 1]))
    }

    /// Zero-copy literal slice. Safe via `bytemuck` because `Literal` is
    /// `#[repr(transparent)]` over `u32` and derives `Pod + Zeroable`.
    #[inline]
    pub(crate) fn literals(&self, offset: usize) -> &[Literal] {
        let len = self.lit_len_raw(offset) as usize;
        let base = offset + HEADER_WORDS;
        bytemuck::cast_slice(&self.words[base..base + len])
    }

    /// Recover literals from a clause that may have been deleted by
    /// `elim_propagate` during BVE.
    ///
    /// When `delete()` marks a clause as garbage it zeros the literal count
    /// but preserves the literal data and saves the original `alloc_len` in
    /// `words[offset + 1]`.  This method reads that saved length to return
    /// the original literals even after deletion.
    ///
    /// CaDiCaL pushes ALL defining clauses onto the extension stack before
    /// any deletion (`external.cpp:55-69`, `elim.cpp:628-670`).  AY's
    /// per-variable `elim_propagate` can delete clauses that later variables'
    /// `WitnessEntry` references still need for reconstruction (#5059).
    #[inline]
    pub(crate) fn literals_or_deleted(&self, offset: usize) -> &[Literal] {
        let len = self.lit_len_raw(offset) as usize;
        if len != 0 {
            let base = offset + HEADER_WORDS;
            return bytemuck::cast_slice(&self.words[base..base + len]);
        }
        // Deleted clause: pre-delete literal count in upper 16 bits of word[1].
        let saved_len = (self.words[offset + 1] >> 16) as usize;
        if saved_len == 0 {
            return &[];
        }
        let base = offset + HEADER_WORDS;
        bytemuck::cast_slice(&self.words[base..base + saved_len])
    }

    /// Single-literal access by index within a clause. Returns the literal
    /// by value (Copy), avoiding a slice borrow on the arena. This enables
    /// index-based iteration without borrow conflicts with other Solver fields
    /// (#6989: eliminates clause_buf copy in conflict analysis).
    #[inline]
    pub(crate) fn literal_at(&self, offset: usize, index: usize) -> Literal {
        let base = offset + HEADER_WORDS;
        Literal(self.words[base + index])
    }

    /// Zero-copy mutable literal slice. Same justification as `literals()`.
    #[inline]
    pub(crate) fn literals_mut(&mut self, offset: usize) -> &mut [Literal] {
        let len = self.lit_len_raw(offset) as usize;
        let base = offset + HEADER_WORDS;
        bytemuck::cast_slice_mut(&mut self.words[base..base + len])
    }

    #[inline]
    pub(crate) fn swap_literals(&mut self, offset: usize, i: usize, j: usize) {
        let base = offset + HEADER_WORDS;
        self.words.swap(base + i, base + j);
    }

    /// Total literals stored across all clauses (including deleted). Test-only.
    #[cfg(test)]
    pub(crate) fn total_literals(&self) -> usize {
        let mut total = 0;
        for off in self.indices() {
            total += self.lit_len_raw(off) as usize;
        }
        total
    }

    /// Total literals stored across active clauses. Test-only.
    ///
    /// Note: identical to `total_literals()` because the arena iterator walks
    /// all entries (including deleted) and `lit_len_raw` returns 0 for deleted
    /// clauses, so they contribute nothing. Kept as a separate name for
    /// semantic clarity in callers that want "active" counts.
    #[cfg(test)]
    pub(crate) fn active_literals(&self) -> usize {
        self.total_literals()
    }

    /// Read a raw arena word at `offset + delta`. Debug/diagnostic only.
    #[cfg(debug_assertions)]
    pub(crate) fn raw_word(&self, offset: usize, delta: usize) -> u32 {
        let idx = offset + delta;
        if idx < self.words.len() {
            self.words[idx]
        } else {
            0xDEAD_BEEF
        }
    }

    /// Estimated heap bytes used by the clause arena.
    ///
    /// Includes the word buffer and the shrink_map. The word buffer
    /// dominates but the shrink_map can grow significantly during
    /// inprocessing with many clause replacements (#8672).
    ///
    /// Note: this does NOT include auxiliary per-solver structures that
    /// reference arena offsets (clause_ids, watch buffers). Those are
    /// tracked separately in `MemoryStats` (see `config.rs`).
    ///
    /// For the memory trigger in `should_reduce_db` use
    /// `Solver::clause_db_memory_bytes`, which composes this value with the
    /// watcher heap, LRAT clause-id side vector, reconstruction stack, and
    /// immutable original-ledger (#8672). Using only the arena under-reports
    /// actual clause-DB cost by 2x-5x in typical workloads, which delays
    /// reduction and masks growth under memory pressure.
    pub(crate) fn memory_bytes(&self) -> usize {
        let words_bytes = 24 + self.words.capacity() * 4;
        // hashbrown stores entries as (K, V) tuples (with alignment padding)
        // plus 1 control byte per bucket. (u32, u16) is 8 bytes due to
        // alignment, not 6. The 56 covers the HashMap struct overhead.
        // Under `#[cfg(kani)]` the maps are `BTreeMap` (see `kani_compat`), which
        // has no `capacity()`; `len()` is an adequate proxy for the diagnostic-only
        // memory accounting and keeps the graph compiling for model checking.
        #[cfg(kani)]
        let shrink_map_cap = self.shrink_map.len();
        #[cfg(not(kani))]
        let shrink_map_cap = self.shrink_map.capacity();
        #[cfg(kani)]
        let learned_offset_index_cap = self.learned_offset_index.len();
        #[cfg(not(kani))]
        let learned_offset_index_cap = self.learned_offset_index.capacity();
        #[cfg(kani)]
        let signatures_cap = self.signatures.len();
        #[cfg(not(kani))]
        let signatures_cap = self.signatures.capacity();
        let shrink_map_bytes = 56 + shrink_map_cap.saturating_mul(size_of::<(u32, u16)>() + 1);
        // Signature side table (R2 header slimming): one (u32 offset, u64 sig)
        // entry per clause, 16 bytes with alignment padding + 1 control byte.
        let signatures_bytes = 56 + signatures_cap.saturating_mul(size_of::<(u32, u64)>() + 1);
        let learned_index_bytes = 24
            + self.learned_offsets.capacity() * size_of::<usize>()
            + 56
            + learned_offset_index_cap.saturating_mul(size_of::<(usize, usize)>() + 1);
        let fixed_fields = 64;
        words_bytes + shrink_map_bytes + signatures_bytes + learned_index_bytes + fixed_fields
    }
}
