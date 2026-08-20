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

/// Arena capacity (in u32 words) above which `Vec`'s doubling is replaced by
/// bounded-overshoot growth.
///
/// `Vec::push` grows by doubling, so a purely push-grown arena carries up to a
/// full arena's worth of slack. Measured on `vlsat3_b99.smt2` (QF_DT Bouvier,
/// 51,893,377 clauses lowered by the enum finite-domain lane): at peak the
/// arena held `len = 259,383,464` words in `cap = 433,028,352` — 1652 MB
/// mapped for 990 MB of clauses. That 662 MB is never written, so it never
/// shows in RSS, but it is charged in full against `--memory`, which trips on
/// `max(counting-allocator live bytes, phys_footprint)`.
///
/// Below the threshold the absolute waste is at most ~128 MB and doubling's
/// cheaper reallocation ladder is the right trade, so small arenas keep
/// `Vec`'s policy exactly. Above it, growth is +25% per step: still geometric
/// (so growth stays amortized O(1)) but with the overshoot bounded to a
/// quarter of the arena instead of all of it.
const BOUNDED_GROWTH_THRESHOLD_WORDS: usize = 32 * 1024 * 1024; // 128 MB

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
    /// Word count the clause-DB **memory heuristic** bills the arena for.
    ///
    /// `memory_bytes()` feeds `Solver::clause_db_memory_bytes`, which is the
    /// byte trigger in `should_reduce_db` / `explicit_reduce_pressure` — armed
    /// on the BV, strings, and resolution-DAG paths via
    /// `set_max_clause_db_bytes`. It used to read `words.capacity()`, so
    /// changing how the arena grows would move when reduction fires, i.e.
    /// change the search. This field keeps the heuristic on its historical
    /// basis — `Vec`'s doubling ladder — so the reduction cadence and the
    /// search trajectory are bit-identical no matter what the allocator is
    /// actually asked for. Same reasoning as `LEGACY_ACCOUNTING_HEADER_WORDS`
    /// above, which pins the GC effort heuristic to the pre-slimming header
    /// size for exactly this purpose.
    ///
    /// Re-seeded from the real capacity on compaction, which rebuilds `words`
    /// through `Vec`'s own growth in every build.
    accounted_words: usize,
}

/// `RawVec::MIN_NON_ZERO_CAP` for a 4-byte element: the floor `Vec` applies to
/// its first amortized growth. Mirrored here so `accounted_words` reproduces
/// the doubling ladder exactly from an empty arena.
const VEC_MIN_NON_ZERO_CAP: usize = 4;

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
            accounted_words: self.accounted_words,
        }
    }
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
            accounted_words: 0,
        }
    }

    pub(crate) fn with_capacity(clause_hint: usize, literal_hint: usize) -> Self {
        let words: Vec<u32> = Vec::with_capacity(clause_hint * HEADER_WORDS + literal_hint);
        // Seed the heuristic's ladder from the real starting capacity: this is
        // where `words.capacity()` began before the growth policy changed.
        let accounted_words = words.capacity();
        Self {
            words,
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
            accounted_words,
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

    /// Make room for `extra` more words, bounding the overshoot once the arena
    /// is large (see [`BOUNDED_GROWTH_THRESHOLD_WORDS`]).
    ///
    /// What the solver can observe is unchanged. `ClauseRef` offsets are
    /// `words.len()` at insertion time, `words_capacity()` is dead code, and
    /// the IC3 pressure check reads `arena.len()`. The one heuristic that DID
    /// read `words.capacity()` — the clause-DB byte trigger, via
    /// `memory_bytes()` — now reads `accounted_words`, which this function
    /// keeps on `Vec`'s doubling ladder regardless of the real allocation. So
    /// this changes only how much address space is held, never what is stored,
    /// in what order, or when reduction fires.
    #[inline]
    fn reserve_words(&mut self, extra: usize) {
        let len = self.words.len();
        let cap = self.words.capacity();
        // Advance the heuristic's ladder first, on `Vec`'s own rule
        // (`RawVec::grow_amortized`), independently of what is really
        // allocated below. See `accounted_words`.
        let needed_for_accounting = len.saturating_add(extra);
        if needed_for_accounting > self.accounted_words {
            self.accounted_words = self
                .accounted_words
                .saturating_mul(2)
                .max(needed_for_accounting)
                .max(VEC_MIN_NON_ZERO_CAP);
        }
        if extra <= cap - len {
            return;
        }
        if cap < BOUNDED_GROWTH_THRESHOLD_WORDS {
            // Small arena: keep `Vec`'s own amortized doubling verbatim.
            self.words.reserve(extra);
            return;
        }
        let needed = len
            .checked_add(extra)
            .expect("BUG: clause arena word count overflow");
        let target = needed.max(cap + cap / 4);
        self.words.reserve_exact(target - len);
    }

    /// Reserve room for `clauses` clauses totalling `literals` literals.
    ///
    /// Producers that build their CNF from a plan know its exact shape before
    /// they emit it. Reserving the whole thing in one call skips the entire
    /// growth ladder: no slack, and none of the double-live transients where a
    /// realloc holds the old and new buffers at once.
    ///
    /// Advisory in both directions: a low hint still grows normally (via
    /// [`Self::reserve_words`]), and a high one only wastes what it asks for.
    /// It never shrinks an existing reservation and never reserves past the
    /// arena's addressable limit.
    ///
    /// Deliberately does NOT touch `accounted_words`: the clause-DB byte
    /// heuristic must see the same ladder it would have seen with no hint at
    /// all, or the reduction cadence moves and the search with it.
    pub(crate) fn reserve_clauses(&mut self, clauses: usize, literals: usize) {
        let want = clauses
            .saturating_mul(HEADER_WORDS)
            .saturating_add(literals)
            .min(crate::arena_limits::MAX_ARENA_WORDS as usize);
        if want <= self.words.capacity() {
            return;
        }
        self.words.reserve_exact(want - self.words.len());
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
        // Grow deliberately rather than letting the pushes below double the
        // arena: exactly `HEADER_WORDS + lit_len` words are written here.
        self.reserve_words(HEADER_WORDS + lit_len as usize);
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

    /// Accumulated dead words from deleted clauses. Used to gate compaction:
    /// compact when `dead_words() > len() / 4`.
    ///
    /// Exposed to `--stats` because the compaction trigger reads this and
    /// nothing else: a run can sit at 45 k live clauses in a 73 M-word arena
    /// with zero compactions, and without this counter beside `arena_words`
    /// there is no way to see that the trigger has gone blind.
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

/// One step of the header-stride arena walk shared by [`ArenaIter`] and
/// [`ClauseArena::walk_step`].
///
/// Returns `(clause_offset, next_pos)`, or `None` at the end of the arena.
/// This is the SINGLE definition of the walk: a cursor-style caller (one that
/// needs `&mut self` inside its loop body and therefore cannot hold the
/// iterator's borrow) must land on exactly the same offsets in the same order
/// as `indices()` / `indices_from()`.
fn arena_walk_step(
    words: &[u32],
    shrink_map: &DetHashMap<u32, u16>,
    mut pos: usize,
) -> Option<(usize, usize)> {
    loop {
        if pos >= words.len() {
            return None;
        }
        // Guard: need at least HEADER_WORDS to read the clause header.
        // A partial header at the end of the arena indicates corruption or
        // a prior stride miscalculation. Stop iteration to prevent OOB reads.
        if pos + HEADER_WORDS > words.len() {
            return None;
        }
        let off = pos;
        let current_len = (words[off] & 0xFFFF) as usize;
        let alloc_len = if current_len == 0 {
            // Deleted clause: alloc_len in lower 16 bits of word[1].
            let deleted_alloc = (words[off + 1] & 0xFFFF) as usize;
            if deleted_alloc == 0 {
                // Zero alloc_len in a deleted clause header indicates double-
                // delete or corruption (#8231). In release builds the old
                // debug_assert was elided, causing the iterator to advance by
                // only HEADER_WORDS, landing mid-clause on subsequent
                // iterations and interpreting literal data as headers. Fix:
                // skip forward by HEADER_WORDS to prevent infinite loops.
                pos += HEADER_WORDS;
                continue;
            }
            deleted_alloc
        } else if let Some(&orig) = shrink_map.get(&(off as u32)) {
            // Shrunk clause: stride spans original allocation.
            orig as usize
        } else {
            // Normal live clause.
            current_len
        };
        debug_assert!(alloc_len > 0, "BUG: zero alloc_len in arena walk at {off}");
        let stride = HEADER_WORDS + alloc_len;
        // Validate the clause span fits within the arena. If it doesn't,
        // the iterator landed on a misaligned position where literal data
        // was misinterpreted as a header (#8231). Skip this corrupt entry
        // to prevent downstream OOB panics in literals()/watched_literals().
        if off + stride > words.len() {
            return None;
        }
        return Some((off, off + stride));
    }
}

impl ClauseArena {
    /// Cursor form of the arena walk: one clause per call, no iterator borrow.
    ///
    /// Yields `(clause_offset, next_pos)` for the clause at or after `pos`,
    /// matching `indices_from(pos)` offset for offset. Callers that mutate the
    /// solver inside the loop body (watch attachment, literal swaps) use this
    /// instead of collecting every offset into a `Vec` first — on the SC2025
    /// giants that collect was a multi-hundred-megabyte transient sitting
    /// exactly at the peak-RSS moment.
    #[inline]
    pub(crate) fn walk_step(&self, pos: usize) -> Option<(usize, usize)> {
        arena_walk_step(&self.words, &self.shrink_map, pos)
    }
}

impl Iterator for ArenaIter<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        match arena_walk_step(self.words, self.shrink_map, self.pos) {
            Some((off, next_pos)) => {
                self.pos = next_pos;
                Some(off)
            }
            None => {
                self.pos = self.words.len();
                None
            }
        }
    }
}

#[path = "clause_arena_accessors.rs"]
mod accessors;
mod storage;

#[cfg(test)]
#[path = "clause_arena_tests.rs"]
mod tests;
