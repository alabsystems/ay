// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unified clause arena with inline literals (CaDiCaL-style).
//!
//! Layout per clause: 3 header words + N literal words in a contiguous `Vec<u32>`.
//! A 3-literal clause = 24 bytes, fitting comfortably in a single cache line.
//! The 64-bit clause signature (BVE/subsumption bloom filter) lives in the
//! `signatures` side table, NOT in the hot arena: BCP never reads it, and
//! keeping it inline made every clause header 8 bytes larger (R2 slimming;
//! kissat's header is 12 bytes with literals at +12).
//! Reference: CaDiCaL `clause.hpp:31-122`, `arena.hpp:56-101`.
//!
//! # Direct-Offset Design (Step 2 of #3904)
//!
//! `ClauseRef(u32)` stores the **word offset** directly into this arena.
//! There is no indirection table — all methods accept `usize` offsets directly.
//! This eliminates one cache miss per BCP propagation step.

use crate::clause::{compute_clause_signature, ClauseSignature};
use crate::kani_compat::DetHashMap;
use crate::literal::Literal;

/// Number of u32 header words before the literal data.
pub(crate) const HEADER_WORDS: usize = 3;

/// Legacy header size (words) before the R2 header slimming moved the 64-bit
/// clause signature out of the arena. GC/compaction effort heuristics keep
/// their accounting in legacy units (see `accounting_len`) so the layout
/// change does not perturb the tuned compaction cadence or the search
/// trajectory.
pub(crate) const LEGACY_ACCOUNTING_HEADER_WORDS: usize = 5;

// The public `arena_limits::HEADER_WORDS` mirrors this value for downstream
// callers (PB-to-CNF encoders sizing their CNF against the arena limit). Keep
// them in sync: this fails to compile if they ever drift.
const _: () = assert!(HEADER_WORDS as u64 == crate::arena_limits::HEADER_WORDS);
const LEARNED_BIT: u16 = 0b0_0000_0001;
const USED_MASK: u16 = 0b0_0011_1110;
const USED_SHIFT: u32 = 1;
const GARBAGE_BIT: u16 = 0b0_0100_0000;
const VIVIFY_SKIP_BIT: u16 = 0b0_1000_0000;
const PENDING_GARBAGE_BIT: u16 = 0b1_0000_0000;
/// Marks clauses produced by hyper binary resolution (HBR, probing) or hyper
/// ternary resolution (HTR). CaDiCaL clause.hpp:46 `bool hyper : 1`.
/// Hyper resolvents get one-round lifetime in reduce_db: if unused since last
/// reduce, they are deleted immediately without entering the sort pool.
const HYPER_BIT: u16 = 0b10_0000_0000;
/// CaDiCaL clause.hpp `bool subsume : 1`. Per-clause flag for forward
/// subsumption scheduling: marks clauses that should be *tried* as subsumption
/// candidates in the current round. Set for all scheduled size>2 clauses when
/// no left-overs exist from a prior incomplete round; cleared after attempting
/// subsumption. Without this, AY re-attempts subsumption on every dirty clause
/// every round, wasting the effort budget on clauses already tried (#7393).
const SUBSUME_TRIED_BIT: u16 = 0b100_0000_0000;
/// CaDiCaL condition.cpp `c->conditioned`. Round-robin scheduling flag.
const CONDITIONED_BIT: u16 = 0b1000_0000_0000;
/// CaDiCaL clause.hpp `bool instantiated : 1`. Marks clauses that have
/// already been tried by post-BVE instantiation (CaDiCaL instantiate.cpp:211).
/// When the `instantiateonce` strategy is active, instantiated clauses are
/// skipped in subsequent collection rounds.
const INSTANTIATED_BIT: u16 = 0b1_0000_0000_0000;
/// Marks clauses as IC3 lemmas (blocking clauses added between IC3 queries).
///
/// IC3/PDR engines add blocking clauses between incremental SAT queries. These
/// clauses encode reachability facts that the IC3 engine depends on for
/// correctness — deleting them can cause false UNSAT on consecution queries.
/// Unlike standard learned clauses from CDCL conflict analysis, IC3 lemmas
/// must persist across queries and are protected from reduction.
///
/// GipSAT uses 4 clause kinds (Trans/Lemma/Learnt/Temporary) for this purpose.
/// This flag is ay-sat's equivalent of GipSAT's Lemma kind.
///
/// Reference: GipSAT rIC3 gipsat/mod.rs clause kind management.
const IC3_LEMMA_BIT: u16 = 0b10_0000_0000_0000;

/// 2-bit user-scope-depth-at-learn mask (bits 14-15).
///
/// Ported from Z3 PR #9221 (`sat_clause.h` `m_scope_lim:2`).
/// Stores the user-scope depth when the learned clause was created, saturated
/// at 3. On `pop()`, learned clauses with `scope_lim > new_scope_depth` are
/// removed so learned clauses derived during pushed scopes do not pollute the
/// clause database after their scope is popped.
///
/// Saturation semantics: if the current scope depth at learn time is >= 3, the
/// field records 3. This means `pop()` cleanup is precise only when the new
/// scope depth is < 3; for deeper pops the sweep is skipped (clauses may leak
/// but the stored bit pattern is ambiguous).
///
/// The common cases (1–2 nesting levels) are handled exactly.
pub(crate) const SCOPE_LIM_MASK: u16 = 0b1100_0000_0000_0000;
pub(crate) const SCOPE_LIM_SHIFT: u32 = 14;
pub(crate) const SCOPE_LIM_MAX: u16 = 3;

/// Maximum value of the used counter (CaDiCaL internal.hpp:315).
pub(crate) const MAX_USED: u8 = 31;

/// Unified clause arena with inline header + literal storage.
///
/// `ClauseRef(u32)` values are word offsets directly into `words`.
/// All methods accept `usize` offsets; no indirection table.
pub(crate) struct ClauseArena {
    words: Vec<u32>,
    num_clauses: usize,
    /// Number of active (non-deleted) clauses.
    /// Maintained incrementally by `add`, `delete`, and `compact`.
    active_count: usize,
    /// Number of active (non-deleted) irredundant (non-learned) clauses.
    /// CaDiCaL equivalent: `stats.current.irredundant`. Maintained
    /// incrementally by `add`, `delete`, `set_learned`, and `compact`.
    irredundant_count: usize,
    /// Number of active (non-deleted) redundant (learned) clauses.
    /// Maintained incrementally by `add`, `delete`, `set_learned`, and `compact`.
    pub(crate) redundant_count: usize,
    /// Active learned clause offsets.
    ///
    /// Maintained with `learned_offset_index` so learned-only passes can avoid
    /// walking the full mixed arena.
    learned_offsets: Vec<usize>,
    /// Offset -> position in `learned_offsets`.
    learned_offset_index: DetHashMap<usize, usize>,
    /// Tracks clauses shrunk by `replace()`: maps word offset → original allocated
    /// literal count. Needed for arena walking: the header stores the current
    /// (shorter) literal count, but the stride must span the original allocation.
    /// Cleared on `compact()`.
    shrink_map: DetHashMap<u32, u16>,
    /// 64-bit clause signatures keyed by word offset (R2 header slimming).
    ///
    /// Side metadata read only by cold passes (subsumption, BVE backward,
    /// IC3 clause_subsumes) — BCP never touches it, so it lives outside the
    /// hot arena. Maintained exactly like the pre-R2 inline signature words:
    /// written on `add`/`replace`/`refresh_signature`, left in place on
    /// `delete` (the inline words also survived deletion; no caller reads a
    /// deleted clause's signature), and rebuilt with remapped offsets on
    /// `compact_reorder`/`compact` (mirroring `shrink_map`'s GC handling).
    signatures: DetHashMap<u32, ClauseSignature>,
    /// Accumulated dead words from deleted clauses. Gates arena compaction:
    /// compact when `dead_words > arena.len() / 4`. Reset on compaction.
    dead_words: usize,
    /// Set once any clause exceeding the 16-bit length field (`> u16::MAX`
    /// literals) is added. Such a clause is stored truncated (a sound
    /// STRENGTHENING — see `add`), so SAT models remain valid for the original
    /// formula but UNSAT verdicts must be downgraded to `unknown`. Sticky: once
    /// poisoned, stays poisoned for the life of the arena.
    has_oversized_clause: bool,
}

impl Clone for ClauseArena {
    fn clone(&self) -> Self {
        Self {
            words: self.words.clone(),
            num_clauses: self.num_clauses,
            active_count: self.active_count,
            irredundant_count: self.irredundant_count,
            redundant_count: self.redundant_count,
            learned_offsets: self.learned_offsets.clone(),
            learned_offset_index: self.learned_offset_index.clone(),
            shrink_map: self.shrink_map.clone(),
            signatures: self.signatures.clone(),
            dead_words: self.dead_words,
            has_oversized_clause: self.has_oversized_clause,
        }
    }
}

fn triage_content() -> Option<Vec<i64>> {
    use std::sync::OnceLock;
    static T: OnceLock<Option<Vec<i64>>> = OnceLock::new();
    T.get_or_init(|| {
        std::env::var("AY_AB_TRIAGE_ARENA_CLAUSE").ok().map(|s| {
            let mut v: Vec<i64> = s.split(',').filter_map(|t| t.trim().parse().ok()).collect();
            v.sort_unstable();
            v
        })
    })
    .clone()
}

fn lits_to_sorted_dimacs(lits: &[Literal]) -> Vec<i64> {
    let mut v: Vec<i64> = lits
        .iter()
        .map(|l| {
            let d = i64::from(l.variable().0) + 1;
            if l.index() % 2 == 0 {
                d
            } else {
                -d
            }
        })
        .collect();
    v.sort_unstable();
    v
}

fn triage_ref() -> Option<usize> {
    use std::sync::OnceLock;
    static T: OnceLock<Option<usize>> = OnceLock::new();
    *T.get_or_init(|| {
        std::env::var("AY_AB_TRIAGE_REF")
            .ok()
            .and_then(|s| s.trim().parse().ok())
    })
}

impl ClauseArena {
    pub(crate) fn new() -> Self {
        Self {
            words: Vec::new(),
            num_clauses: 0,
            active_count: 0,
            irredundant_count: 0,
            redundant_count: 0,
            learned_offsets: Vec::new(),
            learned_offset_index: DetHashMap::default(),
            shrink_map: DetHashMap::default(),
            signatures: DetHashMap::default(),
            dead_words: 0,
            has_oversized_clause: false,
        }
    }

    pub(crate) fn with_capacity(clause_hint: usize, literal_hint: usize) -> Self {
        Self {
            words: Vec::with_capacity(clause_hint * HEADER_WORDS + literal_hint),
            num_clauses: 0,
            active_count: 0,
            irredundant_count: 0,
            redundant_count: 0,
            learned_offsets: Vec::with_capacity(clause_hint / 4),
            learned_offset_index: DetHashMap::default(),
            shrink_map: DetHashMap::default(),
            signatures: DetHashMap::default(),
            dead_words: 0,
            has_oversized_clause: false,
        }
    }

    /// Whether any clause too large for the 16-bit length field has been added.
    /// When true, the formula was stored with a strengthened (truncated) clause:
    /// SAT models stay valid for the original formula, but UNSAT verdicts are
    /// untrustworthy and the solve must return `unknown`. See `add`.
    #[inline]
    pub(crate) fn has_oversized_clause(&self) -> bool {
        self.has_oversized_clause
    }

    #[inline]
    fn insert_learned_offset(&mut self, offset: usize) {
        if self.learned_offset_index.contains_key(&offset) {
            return;
        }
        let pos = self.learned_offsets.len();
        self.learned_offsets.push(offset);
        self.learned_offset_index.insert(offset, pos);
    }

    #[inline]
    fn remove_learned_offset_at(&mut self, pos: usize) {
        let moved_or_removed = self.learned_offsets.swap_remove(pos);
        debug_assert!(
            !self.learned_offset_index.contains_key(&moved_or_removed),
            "BUG: removed learned offset still indexed"
        );
        if pos < self.learned_offsets.len() {
            let moved = self.learned_offsets[pos];
            self.learned_offset_index.insert(moved, pos);
        }
    }

    #[inline]
    fn remove_learned_offset(&mut self, offset: usize) {
        let Some(pos) = self.learned_offset_index.remove(&offset) else {
            return;
        };
        if pos < self.learned_offsets.len() && self.learned_offsets[pos] == offset {
            self.remove_learned_offset_at(pos);
            return;
        }
        debug_assert!(
            false,
            "BUG: learned offset index out of sync for offset {offset}"
        );
        if let Some(actual_pos) = self.learned_offsets.iter().position(|&off| off == offset) {
            self.remove_learned_offset_at(actual_pos);
        }
    }

    /// Add a new clause. Returns the word offset as `usize`.
    pub(crate) fn add(&mut self, lits: &[Literal], learned: bool) -> usize {
        debug_assert!(!lits.is_empty(), "BUG: ClauseArena::add() with 0 literals");
        let offset = self.words.len();
        // Soundness guard (#9670): a `ClauseRef` and the watch-list clause word
        // hold the offset in 32 bits, and `u32::MAX` is reserved as the
        // relocation-remap "dead" sentinel. The whole clause (header + literals)
        // must therefore fit strictly below `MAX_ARENA_WORDS` (== `u32::MAX`).
        // Allocating at or past it would truncate the offset on `as u32` and
        // alias another clause, corrupting BCP — a fail-stop assert here is the
        // sound outcome (it can never return a wrong verdict). Callers that
        // pre-build large CNFs (PB-to-CNF encoders) keep the static footprint
        // below this bound with learned-clause headroom; see
        // `ay_pb::EncodedCnf::fits_sat_arena`.
        let end = offset
            .checked_add(HEADER_WORDS + lits.len())
            .expect("BUG: clause arena offset overflow");
        assert!(
            (end as u64) <= crate::arena_limits::MAX_ARENA_WORDS,
            "clause arena overflow: allocating clause would reach word offset {end} \
             at/past the addressable limit {} (#9670)",
            crate::arena_limits::MAX_ARENA_WORDS,
        );
        // Clause-length field is 16 bits (`lit_len_raw` reads `words[off] & 0xFFFF`),
        // so a clause with more than `u16::MAX` literals cannot be represented. The
        // historical behavior silently truncated the *length* while storing all
        // literal words, which desynced the arena walk (`ArenaIter` strides by the
        // stored length) and could blow watch init up to tens of GiB (the giant
        // CNF of a large negated `distinct`). Instead we store the clause
        // *consistently* truncated to `u16::MAX` literals (length matches stored
        // words — no desync, no OOM) and poison the arena. Dropping disjuncts from
        // a CNF clause only STRENGTHENS the formula, so any SAT model the solver
        // finds still satisfies the full original clause (sound), but an UNSAT
        // verdict is no longer trustworthy — the solve must downgrade to `unknown`
        // when `has_oversized_clause()` is set (gated at the solve entry / UNSAT
        // finalization). This keeps the arena's `u16` invariant intact.
        let lit_len = lits.len().min(u16::MAX as usize) as u16;
        if lits.len() > u16::MAX as usize {
            self.has_oversized_clause = true;
        }
        let stored = &lits[..lit_len as usize];
        let signature = compute_clause_signature(stored);
        self.words.push(u32::from(lit_len));
        self.words.push(0u32);
        let flags: u16 = if learned { LEARNED_BIT } else { 0 };
        self.words.push(2u32 | (u32::from(flags) << 16));
        self.signatures.insert(offset as u32, signature);
        for lit in stored {
            self.words.push(lit.0);
        }
        self.num_clauses += 1;
        self.active_count += 1;
        if learned {
            self.redundant_count += 1;
            self.insert_learned_offset(offset);
        } else {
            self.irredundant_count += 1;
        }
        if triage_ref() == Some(offset) {
            let l: Vec<u32> = lits.iter().map(|x| x.index() as u32).collect();
            eprintln!("TRIAGE_ARENA: ADD off={offset} learned={learned} lits={l:?}");
        }
        if let Some(t) = triage_content() {
            if lits_to_sorted_dimacs(lits) == t {
                eprintln!("TRIAGE_ARENA_CONTENT: ADD off={offset} learned={learned}");
            }
        }
        offset
    }

    #[inline]
    pub(crate) fn delete(&mut self, offset: usize) {
        debug_assert!(offset < self.words.len(), "BUG: delete out of bounds");
        debug_assert!(
            self.lit_len_raw(offset) != 0,
            "BUG: delete on deleted clause"
        );
        self.active_count = self.active_count.saturating_sub(1);
        if self.is_learned(offset) {
            self.remove_learned_offset(offset);
            self.redundant_count = self.redundant_count.saturating_sub(1);
        } else {
            self.irredundant_count = self.irredundant_count.saturating_sub(1);
        }
        // Save both the allocated literal count (for ArenaIter stride) and the
        // current literal count (for literals_or_deleted reconstruction) in
        // word[1] (activity slot).  Layout: upper 16 bits = current_len,
        // lower 16 bits = alloc_len.  Both are u16, so this is lossless.
        let current_len = self.lit_len_raw(offset);
        let alloc_len = if let Some(orig) = self.shrink_map.remove(&(offset as u32)) {
            orig
        } else {
            current_len
        };
        // Track dead space for compaction gating.
        self.dead_words += HEADER_WORDS + alloc_len as usize;
        self.words[offset + 1] = u32::from(alloc_len) | ((u32::from(current_len)) << 16);
        // Zero the literal count to mark as deleted.
        self.words[offset] &= 0xFFFF_0000;
        let mut f = self.flags(offset);
        f |= GARBAGE_BIT;
        f &= !PENDING_GARBAGE_BIT;
        self.set_flags(offset, f);
    }

    /// Replace a clause's literals in place (clause can only shrink).
    pub(crate) fn replace(&mut self, offset: usize, new_lits: &[Literal]) {
        if triage_ref() == Some(offset) {
            let old: Vec<u32> = self
                .literals(offset)
                .iter()
                .map(|l| l.index() as u32)
                .collect();
            let new: Vec<u32> = new_lits.iter().map(|l| l.index() as u32).collect();
            eprintln!("TRIAGE_ARENA: REPLACE off={offset} old={old:?} new={new:?}");
        }
        if let Some(t) = triage_content() {
            if lits_to_sorted_dimacs(new_lits) == t {
                eprintln!("TRIAGE_ARENA_CONTENT: REPLACE-INTO off={offset}");
            } else if lits_to_sorted_dimacs(self.literals(offset)) == t {
                eprintln!("TRIAGE_ARENA_CONTENT: REPLACE-AWAY off={offset}");
            }
        }
        let current_len = self.lit_len_raw(offset);
        debug_assert!(!new_lits.is_empty(), "BUG: replace with empty literals");
        debug_assert!(
            new_lits.len() <= current_len as usize,
            "BUG: replace grows clause"
        );
        if new_lits.len() < current_len as usize {
            // Track the original allocation for arena walking.
            // `or_insert` preserves the FIRST (largest) allocation if shrunk twice.
            self.shrink_map.entry(offset as u32).or_insert(current_len);
            // Track dead tail words so compaction triggers in incremental mode
            // (#3036). Without this, replace() leaves garbage that is never
            // reclaimed because dead_words only grew on delete().
            // current_len is the pre-replace length, so each replace() adds
            // exactly (current_len - new_len) new dead words.
            self.dead_words += current_len as usize - new_lits.len();
        }
        let signature = compute_clause_signature(new_lits);
        self.words[offset] = (self.words[offset] & 0xFFFF_0000) | (new_lits.len() as u32);
        self.signatures.insert(offset as u32, signature);
        let base = offset + HEADER_WORDS;
        for (i, lit) in new_lits.iter().enumerate() {
            self.words[base + i] = lit.0;
        }
        self.set_saved_pos(offset, 2);
        let mut f = self.flags(offset);
        f &= !(GARBAGE_BIT | PENDING_GARBAGE_BIT);
        self.set_flags(offset, f);
    }

    /// Recompute the cached literal signature after in-place literal mutation.
    #[inline]
    pub(crate) fn refresh_signature(&mut self, offset: usize) {
        let signature = compute_clause_signature(self.literals(offset));
        self.signatures.insert(offset as u32, signature);
    }

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

    /// Accumulated dead words from deleted clauses. Used to gate compaction:
    /// compact when `dead_words() > len() / 4`.
    #[cfg(test)]
    #[inline]
    pub(crate) fn dead_words(&self) -> usize {
        self.dead_words
    }

    /// Allocated capacity of the arena backing store in u32 words.
    ///
    /// Used by IC3 memory pressure checks (#8673) to detect when the arena
    /// has grown disproportionately due to unbounded learned clause accumulation.
    /// `capacity()` includes reserved-but-unused space, while `len()` is the
    /// high-water mark of actually-written words. The ratio `len() / capacity()`
    /// indicates fragmentation; the absolute `len()` value (times 4 bytes per
    /// word) gives the arena memory footprint.
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn words_capacity(&self) -> usize {
        self.words.capacity()
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
    fn lit_len_raw(&self, off: usize) -> u16 {
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
    fn flags(&self, off: usize) -> u16 {
        (self.words[off + 2] >> 16) as u16
    }

    #[inline]
    fn set_flags(&mut self, off: usize, flags: u16) {
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

impl Default for ClauseArena {
    fn default() -> Self {
        Self::new()
    }
}

/// Iterator that walks the arena by reading clause headers to determine stride.
pub(crate) struct ArenaIter<'a> {
    words: &'a [u32],
    shrink_map: &'a DetHashMap<u32, u16>,
    pos: usize,
}

impl Iterator for ArenaIter<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        if self.pos >= self.words.len() {
            return None;
        }
        // Guard: need at least HEADER_WORDS to read the clause header.
        // A partial header at the end of the arena indicates corruption or
        // a prior stride miscalculation. Stop iteration to prevent OOB reads.
        if self.pos + HEADER_WORDS > self.words.len() {
            self.pos = self.words.len();
            return None;
        }
        let off = self.pos;
        let current_len = (self.words[off] & 0xFFFF) as usize;
        let alloc_len = if current_len == 0 {
            // Deleted clause: alloc_len in lower 16 bits of word[1].
            let deleted_alloc = (self.words[off + 1] & 0xFFFF) as usize;
            if deleted_alloc == 0 {
                // Zero alloc_len in a deleted clause header indicates double-
                // delete or corruption (#8231). In release builds the old
                // debug_assert was elided, causing the iterator to advance by
                // only HEADER_WORDS, landing mid-clause on subsequent
                // iterations and interpreting literal data as headers. Fix:
                // skip forward by HEADER_WORDS to prevent infinite loops.
                self.pos += HEADER_WORDS;
                return self.next();
            }
            deleted_alloc
        } else if let Some(&orig) = self.shrink_map.get(&(off as u32)) {
            // Shrunk clause: stride spans original allocation.
            orig as usize
        } else {
            // Normal live clause.
            current_len
        };
        debug_assert!(alloc_len > 0, "BUG: zero alloc_len in arena walk at {off}");
        let stride = HEADER_WORDS + alloc_len;
        self.pos += stride;
        // Validate the clause span fits within the arena. If it doesn't,
        // the iterator landed on a misaligned position where literal data
        // was misinterpreted as a header (#8231). Skip this corrupt entry
        // to prevent downstream OOB panics in literals()/watched_literals().
        if off + stride > self.words.len() {
            self.pos = self.words.len();
            return self.next();
        }
        Some(off)
    }
}

#[path = "clause_arena_accessors.rs"]
mod accessors;

#[cfg(test)]
#[path = "clause_arena_tests.rs"]
mod tests;
