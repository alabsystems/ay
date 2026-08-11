// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core BCP (Boolean Constraint Propagation) loop and helpers.
//!
//! Split from `propagation.rs` for file-size compliance (#5142).
//! Contains the unified const-generic `propagate_bcp::<MODE>()` function,
//! the hyper-binary resolution (HBR) helper, and conflict finalization.

// BCP replacement scan loops use `for k in pos..len` where k is needed both
// to index `clause_lits[k]` and to call `swap_literals(clause_idx, _, k)`.
// The clippy suggestion `.iter().enumerate().take().skip()` adds iterator
// overhead in the hottest loop of the solver.
#![allow(clippy::needless_range_loop)]

use super::*;
use crate::solver::propagation::bcp_mode;
use crate::solver::solver_stats::BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS;
use crate::solver_log::solver_log;
use crate::watched;
use ay_prefetch::val_at;

/// Scan watch entries for blocker fast-path hits (interleaved 8-byte AoS,
/// #8243, #8465, #9773).
///
/// Packed AoS layout: each 8-byte entry carries the blocker (+ binary flag)
/// in the low half and the clause word offset in the high half. ONE entry
/// load serves both the blocker fast-path check and — on a blocker miss —
/// the clause reference, so there is no second dependent array stream
/// (#9773). 8 entries fit per 64-byte cache line.
///
/// CaDiCaL propagate.cpp:253 pattern: `const Watch w = *j++ = *i++`.
/// Unconditionally copy the entry to the write position on every iteration.
/// The unconditional write is fast because:
/// 1. When j == i, the write is to the same address (no-op in store buffer)
/// 2. When j < i, the write hits an already-cached line (L1 store ~1 cycle)
/// 3. Eliminates a branch comparison that can mispredict at phase boundaries
///
/// Taking `entries` and `vals` as separate slice parameters (instead of
/// through `&mut self`) lets the optimizer cache both data pointers in
/// registers across consecutive fast-path iterations, eliminating pointer
/// reloads per watcher (#3758, #8243).
///
/// All slice accesses use `ay_prefetch::entry_at`/`entry_set`/`val_at`
/// which bypass bounds checks in release builds. The invariants:
/// - `i < entries.len()` from the loop condition
/// - `j <= i` from the compaction invariant (j only increments on fast path)
/// - `blocker_raw < vals.len()` from the literal encoding invariant
///
/// Val prefetch (#8465): on large instances (50K+ vars), vals[] spans
/// ~100KB+. Each blocker indexes randomly into it. Prefetch the NEXT
/// blocker's val while we check the current one, hiding L2/L3 latency.
///
/// On a blocker miss, returns `(blocker_raw, entry, blocker_val)` where
/// `entry` is the raw packed entry (already copied to position j).
#[inline(always)]
fn bcp_scan_blocker_fast_path(
    entries: &mut [u64],
    vals: &[i8],
    mut i: usize,
    mut j: usize,
) -> (usize, usize, Option<(u32, u64, i8)>) {
    let watch_len = entries.len();

    while i < watch_len {
        let entry = ay_prefetch::entry_at(entries, i);
        // Unconditional speculative copy of the full entry (blocker + clause
        // ref) to the compaction position. Slow-path keep paths (binary
        // propagation, binary conflict, unit propagation, conflict-break)
        // increment j without calling set_entry, so the data at position j
        // must already be correct (#8491).
        ay_prefetch::entry_set(entries, j, entry);
        // Prefetch next blocker's val while we process this one.
        if i + 1 < watch_len {
            let next_entry = ay_prefetch::entry_at(entries, i + 1);
            ay_prefetch::prefetch_val_l1(vals, watched::entry_blocker_raw(next_entry) as usize);
        }
        let blocker_raw = watched::entry_blocker_raw(entry);
        let blocker_val = val_at(vals, blocker_raw as usize);
        i += 1;
        if blocker_val > 0 {
            // Satisfied: full entry already copied above.
            j += 1;
            continue;
        }
        // Blocker miss: the clause ref is in the SAME entry already loaded —
        // no second stream (#9773).
        return (i, j, Some((blocker_raw, entry, blocker_val)));
    }

    (i, j, None)
}

/// Domain-restricted twin of `bcp_scan_blocker_fast_path` (#maxsat-domain-bcp-fix).
///
/// The 75ff66d6 clean-room re-expression of domain BCP reused the non-domain
/// `bcp_scan_blocker_fast_path`, which RETURNS on every non-satisfied blocker —
/// so each UNASSIGNED out-of-domain watcher (the DOMINANT case on lb-crawl /
/// small-COI MaxSAT domain queries) tore down the tight scan and re-entered the
/// outer `'watch` loop just to `continue`. That converted the common-case skip
/// from one tight-loop iteration into a loop teardown + re-entry per watcher — a
/// pure throughput loss (identical answers) that regressed weighted MaxSAT −19.
/// This helper fuses the #8475 out-of-domain skip back INTO the tight loop, as
/// the pre-rewrite path did, so the skip stays in-register. Returns the number
/// of fused skips so the caller can bump `domain_bcp_skips`. Byte-identical
/// propagation semantics; no tick/schedule effect.
#[inline(always)]
fn bcp_scan_blocker_fast_path_domain(
    entries: &mut [u64],
    vals: &[i8],
    domain: &[bool],
    mut i: usize,
    mut j: usize,
) -> (usize, usize, u64, Option<(u32, u64, i8)>) {
    let watch_len = entries.len();
    let mut skips: u64 = 0;
    while i < watch_len {
        let entry = ay_prefetch::entry_at(entries, i);
        ay_prefetch::entry_set(entries, j, entry);
        if i + 1 < watch_len {
            let next_entry = ay_prefetch::entry_at(entries, i + 1);
            ay_prefetch::prefetch_val_l1(vals, watched::entry_blocker_raw(next_entry) as usize);
        }
        let blocker_raw = watched::entry_blocker_raw(entry);
        let blocker_val = val_at(vals, blocker_raw as usize);
        i += 1;
        if blocker_val > 0 {
            // Satisfied blocker: kept, full entry already copied.
            j += 1;
            continue;
        }
        // Fused #8475 domain skip: an UNASSIGNED out-of-domain blocker cannot be
        // falsified by the restricted query — keep the watcher, stay in-loop.
        if blocker_val == 0 && !domain_has_lit(domain, blocker_raw) {
            skips += 1;
            j += 1;
            continue;
        }
        return (i, j, skips, Some((blocker_raw, entry, blocker_val)));
    }
    (i, j, skips, None)
}

/// Update only the blocker half of a kept long-clause watcher.
///
/// In all callers, the current watcher's entry has already been copied to
/// the compaction slot and is available in a register; this recomposes it
/// with the new blocker (clause half + flag preserved). CaDiCaL only changes
/// the blocker (`blit`) in these satisfied paths.
#[inline(always)]
fn bcp_set_kept_blocker(deferred: &mut WatchList, index: usize, entry: u64, blocker_raw: u32) {
    let entries = deferred.entries_mut();
    ay_prefetch::entry_set(
        entries,
        index,
        watched::entry_with_blocker(entry, blocker_raw),
    );
}

#[cfg(test)]
fn bcp_len68_replacement_scan_enabled() -> bool {
    true
}

// Production default: OFF. (The former `AY_SAT_BCP_LEN68_REPLACEMENT_SCAN`
// env opt-in and its `experimental-bcp-len68-replacement-scan` cargo feature
// are removed; test builds still exercise the specialized path via the
// `#[cfg(test)]` variant above.)
#[cfg(not(test))]
#[inline(always)]
fn bcp_len68_replacement_scan_enabled() -> bool {
    false
}

#[cfg(test)]
fn bcp_defer_saved_pos_extraction_enabled() -> bool {
    true
}

// Production default: OFF. (The former `AY_SAT_BCP_DEFER_SAVED_POS_EXTRACTION`
// env opt-in is removed; test builds still exercise the deferred path.)
#[cfg(not(test))]
#[inline(always)]
fn bcp_defer_saved_pos_extraction_enabled() -> bool {
    false
}

#[cfg(test)]
fn bcp_len18_false_saved_pos_reset_enabled() -> bool {
    true
}

// Production default: OFF. (The former `AY_SAT_BCP_LEN18_FALSE_SAVED_POS_RESET`
// env opt-in is removed; test builds still exercise the reset path.)
#[cfg(not(test))]
#[inline(always)]
fn bcp_len18_false_saved_pos_reset_enabled() -> bool {
    false
}

impl Solver {
    /// Unified BCP propagation, const-generic over MODE (#5037).
    ///
    /// Three modes are compiled as separate monomorphized functions:
    /// - `SEARCH` (0): Main CDCL search. Tracks `ticks` for stabilization
    ///   phase accounting. No vivify-skip check, no probe parent, no HBR.
    /// - `PROBE` (1): Failed-literal probing. Vivify-skip check, probe_parent
    ///   tracking at level 1, hyper-binary resolution (HBR) at level 1.
    /// - `VIVIFY` (2): Vivification. Vivify-skip check, no probe parent,
    ///   no HBR.
    ///
    /// SEARCH scans the binary-first watch prefix in place before falling back
    /// to the deferred-copy long-watch path. PROBE/VIVIFY still use the
    /// deferred-copy pattern for the whole list; PROBE can add HBR watchers to
    /// `false_lit` during iteration, so it cannot borrow that list in place.
    ///
    /// REQUIRES: qhead <= trail.len(), watches initialized for all clauses
    /// ENSURES: if None returned, qhead == trail.len() (all propagated),
    ///          every binary unit clause propagated, watch lists consistent;
    ///          if Some(cref), conflicting clause identified, qhead frozen
    #[inline]
    pub(super) fn propagate_bcp<const MODE: u8>(&mut self) -> Option<ClauseRef> {
        let advance_saved_pos =
            MODE == bcp_mode::SEARCH && self.cold.bcp_advance_saved_pos_after_unassigned_move;
        let defer_saved_pos_extraction =
            MODE == bcp_mode::SEARCH && bcp_defer_saved_pos_extraction_enabled();
        let reset_len18_false_saved_pos =
            MODE == bcp_mode::SEARCH && bcp_len18_false_saved_pos_reset_enabled();
        let reset_learned_1963_false_saved_pos =
            MODE == bcp_mode::SEARCH && self.cold.bcp_learned_1963_false_saved_pos_reset;
        let relocate_learned_1963_true_tail =
            MODE == bcp_mode::SEARCH && self.cold.bcp_learned_1963_true_tail_relocation;
        let learned_1963_fsw_gent_skip =
            MODE == bcp_mode::SEARCH && self.cold.bcp_learned_1963_fsw_gent_skip;
        let collect_bcp_telemetry = self.should_collect_bcp_telemetry()
            || (MODE == bcp_mode::SEARCH && self.bcp_hot_path_telemetry_forced_by_experiment());

        macro_rules! dispatch_bcp_impl {
            (
                $reset_learned_1963_false_saved_pos:literal,
                $relocate_learned_1963_true_tail:literal,
                $learned_1963_fsw_gent_skip:literal
            ) => {
                match (
                    reset_len18_false_saved_pos,
                    collect_bcp_telemetry,
                    advance_saved_pos,
                    defer_saved_pos_extraction,
                ) {
                    (true, true, true, true) => self
                        .propagate_bcp_impl::<MODE, true, true, true, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (true, true, true, false) => self
                        .propagate_bcp_impl::<MODE, true, true, false, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (true, true, false, true) => self
                        .propagate_bcp_impl::<MODE, true, false, true, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (true, true, false, false) => self
                        .propagate_bcp_impl::<MODE, true, false, false, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (true, false, true, true) => self
                        .propagate_bcp_impl::<MODE, false, true, true, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (true, false, true, false) => self
                        .propagate_bcp_impl::<MODE, false, true, false, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (true, false, false, true) => self
                        .propagate_bcp_impl::<MODE, false, false, true, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (true, false, false, false) => self
                        .propagate_bcp_impl::<MODE, false, false, false, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (false, true, true, true) => self
                        .propagate_bcp_impl::<MODE, true, true, true, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (false, true, true, false) => self
                        .propagate_bcp_impl::<MODE, true, true, false, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (false, true, false, true) => self
                        .propagate_bcp_impl::<MODE, true, false, true, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (false, true, false, false) => self
                        .propagate_bcp_impl::<MODE, true, false, false, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (false, false, true, true) => self
                        .propagate_bcp_impl::<MODE, false, true, true, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (false, false, true, false) => self
                        .propagate_bcp_impl::<MODE, false, true, false, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (false, false, false, true) => self
                        .propagate_bcp_impl::<MODE, false, false, true, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                    (false, false, false, false) => self
                        .propagate_bcp_impl::<MODE, false, false, false, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip>(),
                }
            };
        }

        match (
            reset_learned_1963_false_saved_pos,
            relocate_learned_1963_true_tail,
            learned_1963_fsw_gent_skip,
        ) {
            (true, true, true) => dispatch_bcp_impl!(true, true, true),
            (true, true, false) => dispatch_bcp_impl!(true, true, false),
            (true, false, true) => dispatch_bcp_impl!(true, false, true),
            (true, false, false) => dispatch_bcp_impl!(true, false, false),
            (false, true, true) => dispatch_bcp_impl!(false, true, true),
            (false, true, false) => dispatch_bcp_impl!(false, true, false),
            (false, false, true) => dispatch_bcp_impl!(false, false, true),
            (false, false, false) => dispatch_bcp_impl!(false, false, false),
        }
    }

    /// Scan SEARCH-mode binary-prefix watchers directly from `self.watches`.
    ///
    /// Binary watchers are never compacted or dropped by BCP, and the
    /// binary-first invariant keeps them in `[0..binary_count)`. Scanning this
    /// prefix before `copy_to_deferred` lets binary-only lists and binary-prefix
    /// conflicts avoid the deferred copy/restore path while preserving the old
    /// CaDiCaL behavior of continuing through later binary watchers after the
    /// first binary conflict.
    #[inline]
    fn scan_search_binary_prefix_in_place<const COLLECT_BCP_TELEMETRY: bool>(
        &mut self,
        false_lit: Literal,
        binary_count: usize,
        chrono: bool,
    ) -> (Option<ClauseRef>, u64) {
        let mut ticks = 0;
        let mut binary_conflict: Option<ClauseRef> = None;
        let mut i = 0usize;
        while i < binary_count {
            // One 8-byte entry load yields blocker AND clause ref (#9773).
            let entry = self.watches.entry_raw(false_lit, i);
            let blocker_raw = watched::entry_blocker_raw(entry);
            i += 1;

            if i < binary_count {
                let next_entry = self.watches.entry_raw(false_lit, i);
                ay_prefetch::prefetch_val_l1(
                    &self.vals,
                    watched::entry_blocker_raw(next_entry) as usize,
                );
            }

            let blocker_val = val_at(&self.vals, blocker_raw as usize);
            if blocker_val > 0 {
                if COLLECT_BCP_TELEMETRY {
                    self.stats.bcp_blocker_fastpath_hits += 1;
                }
                continue;
            }

            debug_assert!(
                watched::entry_is_binary(entry),
                "BUG: binary prefix entry {} is not binary",
                i - 1
            );
            if COLLECT_BCP_TELEMETRY {
                self.stats.bcp_binary_path_hits += 1;
            }
            let clause_ref = ClauseRef(watched::entry_clause_off(entry));
            if blocker_val < 0 {
                binary_conflict = Some(clause_ref);
                continue;
            }

            ticks += 1;
            if self.decision_level > 0 && self.cold.jump_reasons_enabled {
                if chrono {
                    self.enqueue_binary_reason(Literal(blocker_raw), false_lit);
                } else {
                    self.enqueue_binary_reason_nochrono(Literal(blocker_raw), false_lit);
                }
            } else if chrono {
                self.enqueue_bcp_binary_with_other(Literal(blocker_raw), clause_ref, false_lit);
            } else {
                self.enqueue_bcp_binary_nochrono(Literal(blocker_raw), clause_ref);
            }
        }
        debug_assert_eq!(
            i, binary_count,
            "BCP: in-place binary prefix scan stopped before binary_count"
        );
        (binary_conflict, ticks)
    }

    #[inline]
    fn propagate_bcp_impl<
        const MODE: u8,
        const COLLECT_BCP_TELEMETRY: bool,
        const ADVANCE_SAVED_POS_AFTER_UNASSIGNED_MOVE: bool,
        const DEFER_SAVED_POS_EXTRACTION: bool,
        const RESET_LEN18_FALSE_SAVED_POS: bool,
        const RESET_LEARNED_1963_FALSE_SAVED_POS: bool,
        const RELOCATE_LEARNED_1963_TRUE_TAIL: bool,
        const LEARNED_1963_FSW_GENT_SKIP: bool,
    >(
        &mut self,
    ) -> Option<ClauseRef> {
        debug_assert!(
            !self.has_empty_clause,
            "BUG: propagate_bcp called with has_empty_clause=true"
        );
        if MODE != bcp_mode::PROBE {
            debug_assert!(
                !self.probing_mode,
                "BUG: propagate_bcp (non-probe) called in probing mode"
            );
        }
        self.last_conflict_clause_ref = None;
        self.last_conflict_clause_id = 0;
        let qhead_start = self.qhead;
        let specialize_len68_replacement_scan = bcp_len68_replacement_scan_enabled();
        let relocate_learned_618_true_tail =
            MODE == bcp_mode::SEARCH && self.cold.bcp_learned_618_true_tail_relocation;
        let update_learned_no_replacement_saved_pos =
            MODE == bcp_mode::SEARCH && self.cold.bcp_learned_no_replacement_saved_pos_update;
        let disable_learned_1963_no_replacement_unit_blocker_refresh = MODE == bcp_mode::SEARCH
            && self
                .cold
                .bcp_disable_learned_1963_no_replacement_unit_blocker_refresh;
        let profile_learned_no_replacement_scan_pressure = COLLECT_BCP_TELEMETRY
            && MODE == bcp_mode::SEARCH
            && self.cold.bcp_learned_no_replacement_scan_pressure;
        let profile_learned_1963_identity = COLLECT_BCP_TELEMETRY
            && MODE == bcp_mode::SEARCH
            && self.cold.bcp_learned_1963_identity_profile;
        let reset_learned_1963_used5_fsw_saved_pos =
            MODE == bcp_mode::SEARCH && self.cold.bcp_learned_1963_used5_fsw_saved_pos_reset;
        let reset_learned_1963_fsw_conflict_saved_pos =
            MODE == bcp_mode::SEARCH && self.cold.bcp_learned_1963_fsw_conflict_saved_pos_reset;
        let learned_1963_fsw_gent_skip = MODE == bcp_mode::SEARCH && LEARNED_1963_FSW_GENT_SKIP;
        let elide_learned_1963_blocker_cert = MODE == bcp_mode::SEARCH
            && self.bcp_learned_1963_blocker_cert_elision_enabled_internal();
        let shadow_learned_1963_blocker_cert = MODE == bcp_mode::SEARCH
            && !elide_learned_1963_blocker_cert
            && self.bcp_learned_1963_blocker_cert_shadow_enabled_internal();
        let demote_learned_1963_blocker_cert_false_reject = MODE == bcp_mode::SEARCH
            && self.bcp_learned_1963_blocker_cert_false_reject_demote_enabled_internal();
        // BCP ticks: counts cache-line work for effort budgeting.
        // CaDiCaL propagate.cpp:238,473. Used in all modes: SEARCH for
        // stabilization, PROBE/VIVIFY for effort limits (#3758).
        let mut ticks: u64 = 0;
        // Cache ChrBT flag once for the entire propagation loop (#8569).
        // This avoids re-reading the field on every enqueue call and lets us
        // dispatch to the stripped-down nochrono enqueue variants which skip
        // the O(clause_len) assignment_level scan + lifecycle checks.
        let chrono = self.chrono_enabled;
        let trail_lookahead_prefetch = self.cold.bcp_trail_lookahead_prefetch;
        debug_assert!(
            self.qhead <= self.trail.len(),
            "BUG: propagate_bcp entry qhead ({}) > trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            if MODE == bcp_mode::PROBE {
                solver_log!(self, "propagate {}", p.to_dimacs());
            }

            let false_lit = p.negated();

            // Trail-level watch list prefetch (#8465): while we process
            // the current literal's watch list, prefetch the next trail
            // literal's watch list blockers into L2 cache. By the time
            // we finish the current watch list scan, the next one will
            // be warm. CaDiCaL propagate.cpp:160-166 pattern.
            if trail_lookahead_prefetch && self.qhead < self.trail.len() {
                let next_p = self.trail[self.qhead];
                self.watches.prefetch_first(next_p.negated());
            }

            let mut pre_scanned_search_binary_count = 0usize;
            if MODE == bcp_mode::SEARCH {
                let watch_len = self.watches.len_of(false_lit);
                let binary_count = self.watches.binary_count_of(false_lit);
                debug_assert!(
                    binary_count <= watch_len,
                    "BCP: binary_count ({binary_count}) > watch_len ({watch_len})"
                );
                // Charge the same per-watch-list cache-line work as the deferred
                // path. If the list is binary-only or a binary conflict is found,
                // this is the only watch-list accounting for this false literal.
                ticks += 1 + (watch_len as u64).div_ceil(32);
                let (binary_conflict, binary_ticks) = self
                    .scan_search_binary_prefix_in_place::<COLLECT_BCP_TELEMETRY>(
                        false_lit,
                        binary_count,
                        chrono,
                    );
                ticks += binary_ticks;
                pre_scanned_search_binary_count = binary_count;
                if let Some(conflict_ref) = binary_conflict {
                    self.flush_bcp_ticks::<MODE>(ticks);
                    if MODE == bcp_mode::SEARCH {
                        self.num_search_propagations += (self.qhead - qhead_start) as u64;
                    }
                    return Some(self.binary_conflict_finalize(conflict_ref, qhead_start));
                }
                if binary_count == watch_len {
                    continue;
                }
            }

            // Copy watch list into deferred buffer for iteration.
            // SEARCH reaches this path only for the long suffix after its
            // binary prefix has already been scanned in place. PROBE/VIVIFY
            // still use this pattern for the entire watch list.
            let (watch_len, saved_bc) = self
                .watches
                .copy_to_deferred(false_lit, &mut self.deferred_watch_list);
            let mut i: usize = pre_scanned_search_binary_count;
            let mut j: usize = pre_scanned_search_binary_count;
            // CaDiCaL propagate.cpp:249: 1 + cache_lines(ws.size(), sizeof Watch).
            // SoA layout (#8243): blocker scan touches 4B/entry (32 per 128B
            // cache line). Clause_refs are accessed only on miss. Use 32
            // entries per cache line for the blocker-dominated fast path.
            if MODE != bcp_mode::SEARCH {
                ticks += 1 + (watch_len as u64).div_ceil(32);
            } else {
                debug_assert_eq!(
                    pre_scanned_search_binary_count, saved_bc as usize,
                    "BCP: copied binary_count changed after in-place SEARCH binary scan"
                );
            }

            // CaDiCaL propagate.cpp:289-302: binary conflicts do NOT
            // immediately break — propagation continues scanning remaining
            // binary watchers (cheap, no arena access). Only long clause
            // processing checks for a prior binary conflict and breaks.
            // This improves conflict analysis by exposing additional
            // conflicting binary clauses (#8043).
            let mut binary_conflict: Option<ClauseRef> = None;

            // SEARCH scanned the binary prefix in place before the deferred
            // copy. Keep the invariant assertions here so the long-suffix scan
            // starts exactly after the prefix.
            if MODE == bcp_mode::SEARCH {
                let binary_count = saved_bc as usize;
                debug_assert!(
                    binary_count <= watch_len,
                    "BCP: binary_count ({binary_count}) > watch_len ({watch_len})"
                );
                debug_assert_eq!(
                    i, binary_count,
                    "BCP: binary prefix scan stopped before binary_count"
                );
                debug_assert_eq!(
                    j, binary_count,
                    "BCP: binary prefix scan changed binary prefix length"
                );
            }

            // Inner watch-scan loop: the blocker fast path is extracted
            // into bcp_scan_blocker_fast_path() which takes the packed
            // entry array plus &[i8] vals. Interleaved AoS (#9773): one
            // 8-byte entry load feeds both the blocker check and, on a
            // miss, the clause reference — no second dependent stream.
            'watch: loop {
                let j_before = j;
                let entries = self.deferred_watch_list.entries_mut();
                let (new_i, new_j, slow_entry) =
                    bcp_scan_blocker_fast_path(entries, &self.vals, i, j);
                i = new_i;
                j = new_j;
                if COLLECT_BCP_TELEMETRY && MODE == bcp_mode::SEARCH {
                    self.stats.bcp_long_blocker_fastpath_hits += (j - j_before) as u64;
                }
                if COLLECT_BCP_TELEMETRY {
                    self.stats.bcp_blocker_fastpath_hits += (j - j_before) as u64;
                }
                let Some((blocker_raw, entry, blocker_val)) = slow_entry else {
                    break 'watch;
                };

                // Speculative copy: CaDiCaL `*j++ = *i++` pattern (#8491).
                // The fast path unconditionally copied the FULL entry (blocker
                // + clause ref) to position j before returning, so slow-path
                // keep paths (which increment j without writing) already see
                // correct data at position j. If the entry is dropped
                // (replacement swap), j stays put and the copy is harmlessly
                // overwritten later.

                // Binary clause handling.
                // Binary watcher lifecycle (#4924): deletion eagerly unlinks
                // binary watches, so hot-path propagation can avoid header
                // liveness checks (CaDiCaL parity).
                let is_binary = watched::entry_is_binary(entry);
                if is_binary {
                    if COLLECT_BCP_TELEMETRY {
                        self.stats.bcp_binary_path_hits += 1;
                    }
                    let clause_ref = ClauseRef(watched::entry_clause_off(entry));
                    if blocker_val < 0 {
                        // CaDiCaL propagate.cpp:289-290: record binary conflict
                        // but continue scanning binary watchers (#8043).
                        binary_conflict = Some(clause_ref);
                        j += 1;
                        continue;
                    }
                    // Unassigned - propagate, keep watcher
                    ticks += 1; // CaDiCaL propagate.cpp:295
                    j += 1;
                    // Set probe_parent for binary propagation at level 1 (#3419).
                    // CaDiCaL probe.cpp:405: parent = negation of watching literal.
                    if MODE == bcp_mode::PROBE && self.probing_mode && self.decision_level == 1 {
                        let propagated_var = Literal(blocker_raw).variable().index();
                        // Guard: after compaction, stale binary watch entries may
                        // reference variables beyond the current num_vars. Skip
                        // probe_parent tracking for out-of-bounds variables rather
                        // than panicking (#9215).
                        if propagated_var < self.probe_parent.len() {
                            self.probe_parent[propagated_var] = Some(p);
                        }
                    }
                    // Jump reasons (#8034): in SEARCH mode at decision_level > 0
                    // with jump reasons enabled, store a tagged literal reason
                    // instead of a ClauseRef. This avoids arena access during
                    // conflict analysis. Gate: only when formula has high binary
                    // clause ratio (>= 99%, Kissat classify.c bigbigfraction=990)
                    // AND LRAT is disabled (LRAT requires clause IDs for hints).
                    //
                    // ChrBT dispatch (#8569): when chrono is off, use the
                    // nochrono variants that skip assignment_level() and
                    // lifecycle bookkeeping, matching the unsafe BCP path.
                    if MODE == bcp_mode::SEARCH
                        && self.decision_level > 0
                        && self.cold.jump_reasons_enabled
                    {
                        if chrono {
                            self.enqueue_binary_reason(Literal(blocker_raw), false_lit);
                        } else {
                            self.enqueue_binary_reason_nochrono(Literal(blocker_raw), false_lit);
                        }
                    } else if MODE == bcp_mode::SEARCH {
                        // Single-call binary enqueue with flag pre-set (#8042).
                        // ChrBT fast path (#8569): pass false_lit as the known
                        // other literal in the binary clause, avoiding the
                        // arena.len_of() + arena.literal() reads that
                        // assignment_level() would do to discover the clause
                        // is binary.
                        if chrono {
                            self.enqueue_bcp_binary_with_other(
                                Literal(blocker_raw),
                                clause_ref,
                                false_lit,
                            );
                        } else {
                            self.enqueue_bcp_binary_nochrono(Literal(blocker_raw), clause_ref);
                        }
                    } else {
                        self.enqueue(Literal(blocker_raw), Some(clause_ref));
                    }
                    continue;
                }

                // CaDiCaL propagate.cpp:301-302: stop at long clauses if
                // a binary conflict was already found (#8043).
                if binary_conflict.is_some() {
                    j += 1; // keep speculatively-copied watcher
                    break 'watch;
                }

                // Lookahead prefetch (#8000): while we process this long clause,
                // peek at the next watcher's clause_ref and prefetch its arena
                // data. By the time we finish the current clause's replacement
                // scan, the next clause's header + first literals will be in cache.
                // This hides ~60-80 cycles of main-memory latency per long clause.
                //
                // We prefetch even if the next entry turns out to be binary or
                // blocker-satisfied — prefetch is a no-op hint with zero penalty.
                // Packed AoS (#9773): the next entry carries the clause offset.
                if i < watch_len {
                    let next_entry = self.deferred_watch_list.entry_raw(i);
                    // Only prefetch non-binary clause data (binary clauses don't
                    // access the arena in the hot path).
                    if !watched::entry_is_binary(next_entry) {
                        self.arena
                            .prefetch_clause(watched::entry_clause_off(next_entry) as usize);
                    }
                }

                // Long clause: garbage check (after blocker shortcut
                // to avoid a cache miss on every watcher — CaDiCaL propagate.cpp:264-280).
                // Watched clauses always have >= 2 literals, so is_empty_clause
                // is unreachable here. Single combined bitmask test covers both
                // garbage and pending_garbage in one cached header read.
                let clause_idx = watched::entry_clause_off(entry) as usize;
                let off = clause_idx;
                let bcp_header = self.arena.bcp_header(off);
                if bcp_header.is_garbage_any() {
                    continue;
                }
                // Vivify-skip: clause is being vivified — keep watcher but
                // skip propagation (CaDiCaL vivify.cpp:268-282). The bit is
                // in the same cached header word we just read.
                // SEARCH mode never vivifies, so this check is compiled out.
                if MODE != bcp_mode::SEARCH && bcp_header.is_vivify_skipped() {
                    j += 1;
                    continue;
                }
                ticks += 1; // CaDiCaL propagate.cpp:309 — long clause cache-line access

                // Non-binary clause. The long-clause path implies the entry
                // flag (bit 31) is clear, so the entry's high half is exactly
                // the clause word offset (#9670, #9773).
                let clause_ref = ClauseRef(watched::entry_clause_off(entry));

                // Clause length cached from bcp_header (word[0]), avoiding the
                // `arena.literals()` call which goes through bytemuck::cast_slice
                // + bounds-checked slice creation. All subsequent literal access
                // uses `arena.bcp_literal()` (unchecked in release) matching
                // CaDiCaL's raw `lits[k]` pattern.
                let mut clause_len = 0usize;
                let mut cached_saved_pos = 0usize;
                if !DEFER_SAVED_POS_EXTRACTION {
                    clause_len = bcp_header.clause_len();
                    cached_saved_pos = bcp_header.saved_pos();
                }

                // XOR trick for the other watched literal.
                // Uses bcp_literal (unchecked release access) instead of
                // creating a &[Literal] slice. CaDiCaL propagate.cpp:328.
                let lit0 = self.arena.bcp_literal(off, 0);
                let lit1 = self.arena.bcp_literal(off, 1);
                // CaDiCaL propagate.cpp:317: watched literal identity
                debug_assert!(
                    lit0 == false_lit || lit1 == false_lit,
                    "BUG: watch list for {false_lit:?} contains clause {clause_idx} \
                     with watched lits {lit0:?}, {lit1:?} — neither matches"
                );
                let first = Literal(lit0.0 ^ lit1.0 ^ false_lit.0);
                let first_val = val_at(&self.vals, first.index());

                let false_pos = usize::from(lit0 != false_lit);

                if first_val > 0 {
                    // Satisfied - update blocker to `first`, keep watcher
                    bcp_set_kept_blocker(&mut self.deferred_watch_list, j, entry, first.0);
                    j += 1;
                    continue;
                }

                if DEFER_SAVED_POS_EXTRACTION {
                    // Default-off experiment (#9078): avoid saved_pos/header-bit
                    // extraction until replacement scanning actually needs it.
                    // The same-host uf250 smoke was noisy/slower, so production
                    // keeps the original eager extraction unless the env guard is
                    // set.
                    clause_len = bcp_header.clause_len();
                }
                let clause_is_learned = (COLLECT_BCP_TELEMETRY
                    || ADVANCE_SAVED_POS_AFTER_UNASSIGNED_MOVE
                    || RESET_LEARNED_1963_FALSE_SAVED_POS
                    || RELOCATE_LEARNED_1963_TRUE_TAIL
                    || relocate_learned_618_true_tail
                    || update_learned_no_replacement_saved_pos
                    || disable_learned_1963_no_replacement_unit_blocker_refresh
                    || profile_learned_no_replacement_scan_pressure
                    || profile_learned_1963_identity
                    || elide_learned_1963_blocker_cert
                    || shadow_learned_1963_blocker_cert
                    || reset_learned_1963_used5_fsw_saved_pos
                    || disable_learned_1963_no_replacement_unit_blocker_refresh)
                    && MODE == bcp_mode::SEARCH
                    && bcp_header.is_learned();

                // Search for replacement literal.
                debug_assert!(clause_len > 2);

                // Replacement scan: CaDiCaL propagate.cpp:348-398 pattern.
                // Uses sentinel (replacement_k = clause_len) instead of
                // Option<usize> to avoid branch overhead on the discriminant.
                // Caches the replacement literal's value (replacement_val) to
                // avoid a duplicate vals[] read after the scan (#3758).
                //
                // All literal access uses arena.bcp_literal() which bypasses
                // bounds checks in release builds via word_at(). This eliminates
                // one cmp+jae branch pair per literal compared to slice indexing.
                let mut replacement_k: usize = clause_len; // sentinel = not found
                let mut replacement_val: i8 = -1;
                let mut replacement_lit = false_lit;
                let mut relocate_true_tail_watch = false;
                // Short clause optimization (#8569): for clauses with <= 5
                // literals, skip saved position (always start at 2) and skip
                // val prefetching (the clause fits in one cache line, so
                // prefetch adds overhead without benefit). Clauses with 6-8
                // literals still use saved_pos, but the bounded scan is
                // unrolled below and avoids generic long-clause prefetch setup.
                if clause_len <= 5 {
                    // Short clause: linear scan from position 2, no saved_pos.
                    // Len-3 and len-4 clauses are specialized to mirror the
                    // unsafe BCP hot path without loop setup/backedge overhead.
                    match clause_len {
                        3 => {
                            if COLLECT_BCP_TELEMETRY {
                                self.stats.record_bcp_replacement_scan_step(
                                    clause_len,
                                    clause_is_learned,
                                );
                            }
                            let lit2 = self.arena.bcp_literal(off, 2);
                            let v2 = val_at(&self.vals, lit2.index());
                            if v2 >= 0 {
                                replacement_k = 2;
                                replacement_val = v2;
                                replacement_lit = lit2;
                            }
                        }
                        4 => {
                            if COLLECT_BCP_TELEMETRY {
                                self.stats.record_bcp_replacement_scan_step(
                                    clause_len,
                                    clause_is_learned,
                                );
                            }
                            let lit2 = self.arena.bcp_literal(off, 2);
                            let v2 = val_at(&self.vals, lit2.index());
                            if v2 >= 0 {
                                replacement_k = 2;
                                replacement_val = v2;
                                replacement_lit = lit2;
                            } else {
                                if COLLECT_BCP_TELEMETRY {
                                    self.stats.record_bcp_replacement_scan_step(
                                        clause_len,
                                        clause_is_learned,
                                    );
                                }
                                let lit3 = self.arena.bcp_literal(off, 3);
                                let v3 = val_at(&self.vals, lit3.index());
                                if v3 >= 0 {
                                    replacement_k = 3;
                                    replacement_val = v3;
                                    replacement_lit = lit3;
                                }
                            }
                        }
                        5 => {
                            if COLLECT_BCP_TELEMETRY {
                                self.stats.record_bcp_replacement_scan_step(
                                    clause_len,
                                    clause_is_learned,
                                );
                            }
                            let lit2 = self.arena.bcp_literal(off, 2);
                            let v2 = val_at(&self.vals, lit2.index());
                            if v2 >= 0 {
                                replacement_k = 2;
                                replacement_val = v2;
                                replacement_lit = lit2;
                            } else {
                                if COLLECT_BCP_TELEMETRY {
                                    self.stats.record_bcp_replacement_scan_step(
                                        clause_len,
                                        clause_is_learned,
                                    );
                                }
                                let lit3 = self.arena.bcp_literal(off, 3);
                                let v3 = val_at(&self.vals, lit3.index());
                                if v3 >= 0 {
                                    replacement_k = 3;
                                    replacement_val = v3;
                                    replacement_lit = lit3;
                                } else {
                                    if COLLECT_BCP_TELEMETRY {
                                        self.stats.record_bcp_replacement_scan_step(
                                            clause_len,
                                            clause_is_learned,
                                        );
                                    }
                                    let lit4 = self.arena.bcp_literal(off, 4);
                                    let v4 = val_at(&self.vals, lit4.index());
                                    if v4 >= 0 {
                                        replacement_k = 4;
                                        replacement_val = v4;
                                        replacement_lit = lit4;
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                } else {
                    // Long clause: use saved position.
                    // Gent's (JAIR'13) saved position optimization.
                    if DEFER_SAVED_POS_EXTRACTION {
                        cached_saved_pos = bcp_header.saved_pos();
                    }
                    let mut pos = cached_saved_pos;
                    debug_assert!(
                        cached_saved_pos <= clause_len,
                        "BUG: saved_pos {cached_saved_pos} > clause_len {clause_len} for clause {clause_idx}",
                    );
                    if pos < 2 || pos >= clause_len {
                        pos = 2;
                    }
                    let normalized_saved_pos = pos;
                    let (bcp_long_scan_bucket, bcp_long_scan_learned) =
                        if COLLECT_BCP_TELEMETRY && MODE == bcp_mode::SEARCH {
                            (
                                self.stats
                                    .record_bcp_long_scan(clause_len, clause_is_learned),
                                clause_is_learned,
                            )
                        } else {
                            (0, false)
                        };
                    let profile_learned_no_replacement_scan_pressure_for_clause =
                        profile_learned_no_replacement_scan_pressure && clause_is_learned;
                    let profile_learned_1963_identity_for_clause = profile_learned_1963_identity
                        && clause_is_learned
                        && (19..=63).contains(&clause_len);
                    let learned_1963_blocker_cert_for_clause = (elide_learned_1963_blocker_cert
                        || shadow_learned_1963_blocker_cert)
                        && clause_is_learned
                        && (19..=63).contains(&clause_len);
                    let learned_1963_blocker_cert_existing_for_clause =
                        learned_1963_blocker_cert_for_clause
                            && self.stats.bcp_learned_1963_blocker_cert(off).is_some();
                    let profile_learned_scan_pressure_or_identity_for_clause =
                        profile_learned_no_replacement_scan_pressure_for_clause
                            || profile_learned_1963_identity_for_clause;
                    let mut learned_no_replacement_scan_pressure_steps = 0u64;
                    let reset_false_start_candidate = pos > 2
                        && ((RESET_LEN18_FALSE_SAVED_POS && clause_len == 18)
                            || (RESET_LEARNED_1963_FALSE_SAVED_POS
                                && clause_is_learned
                                && (19..=63).contains(&clause_len))
                            || (ADVANCE_SAVED_POS_AFTER_UNASSIGNED_MOVE
                                && clause_is_learned
                                && clause_len >= 6));
                    let reset_learned_1963_used5_fsw_saved_pos_candidate =
                        reset_learned_1963_used5_fsw_saved_pos
                            && clause_is_learned
                            && (19..=63).contains(&clause_len)
                            && normalized_saved_pos > 2
                            && self.arena.used(off) >= 5;
                    let reset_learned_1963_fsw_conflict_saved_pos_candidate =
                        reset_learned_1963_fsw_conflict_saved_pos
                            && clause_is_learned
                            && (19..=63).contains(&clause_len)
                            && normalized_saved_pos > 2;
                    let learned_1963_fsw_gent_skip_candidate = learned_1963_fsw_gent_skip
                        && clause_is_learned
                        && (19..=63).contains(&clause_len)
                        && normalized_saved_pos > 2
                        && !reset_false_start_candidate
                        && !learned_1963_blocker_cert_existing_for_clause;
                    let mut saved_start_lit = false_lit;
                    let mut saved_start_val = 1;
                    // The used5 FSW no-replacement reset does not force this
                    // load: with normalized_saved_pos > 2 and no replacement,
                    // the scan has already proved the saved-start tail slot false.
                    if COLLECT_BCP_TELEMETRY
                        || reset_false_start_candidate
                        || reset_learned_1963_fsw_conflict_saved_pos_candidate
                        || learned_1963_fsw_gent_skip_candidate
                        || learned_1963_blocker_cert_for_clause
                    {
                        saved_start_lit = self.arena.bcp_literal(off, pos);
                        saved_start_val = val_at(&self.vals, saved_start_lit.index());
                        if COLLECT_BCP_TELEMETRY {
                            self.stats.bcp_long_saved_pos_scans += 1;
                            if clause_len == 18 {
                                self.stats.bcp_len18_saved_pos_scans += 1;
                            }
                            if saved_start_val < 0 {
                                self.stats.bcp_long_saved_pos_start_false += 1;
                                if clause_len == 18 {
                                    self.stats.bcp_len18_saved_pos_start_false += 1;
                                }
                            }
                        }
                    }
                    let mut known_false_saved_start = clause_len;
                    let mut gent_skip_known_false_saved_start = false;
                    if reset_false_start_candidate && saved_start_val < 0 {
                        // Default-off experiments (#9085/#9124): for the clique
                        // target path, false saved positions often point at stale
                        // tail slots. The learned 19-63 gate applies this only to
                        // the P5g-hot bucket; saved-position advance keeps its
                        // broader learned-long behavior. Coverage is unchanged
                        // because the scan still wraps over every tail literal,
                        // but learned clauses avoid starting on a known-false
                        // stale slot.
                        //
                        // The saved-start literal was just read and proved false,
                        // so the generic scan can skip that slot after resetting to
                        // tail slot 2. This removes one redundant literal/value
                        // load on false-start paths without changing which
                        // non-false replacement is selected.
                        known_false_saved_start = pos;
                        pos = 2;
                    } else if learned_1963_fsw_gent_skip_candidate && saved_start_val < 0 {
                        known_false_saved_start = pos;
                        gent_skip_known_false_saved_start = true;
                    }

                    let mut blocker_cert_elided_scan = false;
                    let mut blocker_cert_shadow_probe: Option<(usize, u32)> = None;
                    let learned_1963_blocker_cert_fsw_candidate =
                        learned_1963_blocker_cert_for_clause
                            && saved_start_val < 0
                            && normalized_saved_pos > 2;
                    if learned_1963_blocker_cert_fsw_candidate {
                        if let Some(cert) = self.stats.bcp_learned_1963_blocker_cert(off) {
                            self.stats.record_bcp_learned_1963_blocker_cert_candidate();
                            let cert_pos = cert.position;
                            let cert_stale = cert.clause_offset != off
                                || off >= self.arena.len()
                                || !bcp_header.is_learned()
                                || !(19..=63).contains(&clause_len)
                                || cert_pos < 2
                                || cert_pos >= clause_len
                                || cert_pos >= normalized_saved_pos;
                            if cert_stale {
                                self.stats
                                    .record_bcp_learned_1963_blocker_cert_stale_reject();
                                self.stats.clear_bcp_learned_1963_blocker_cert(off);
                            } else {
                                let cert_lit = self.arena.bcp_literal(off, cert_pos);
                                if cert_lit.0 != cert.literal_raw {
                                    self.stats
                                        .record_bcp_learned_1963_blocker_cert_stale_reject();
                                    self.stats.clear_bcp_learned_1963_blocker_cert(off);
                                } else if cert.repeat_count
                                    < BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS
                                {
                                    self.stats
                                        .record_bcp_learned_1963_blocker_cert_repeat_reject();
                                } else {
                                    let cert_val = val_at(&self.vals, cert_lit.index());
                                    if cert_val > 0 {
                                        let elided_suffix_slots = if known_false_saved_start
                                            < clause_len
                                        {
                                            (known_false_saved_start - cert_pos - 1 + clause_len
                                                - known_false_saved_start
                                                - 1)
                                                as u64
                                        } else {
                                            (normalized_saved_pos - cert_pos - 1) as u64
                                        };
                                        if shadow_learned_1963_blocker_cert {
                                            blocker_cert_shadow_probe =
                                                Some((cert_pos, cert_lit.0));
                                            self.stats
                                                .record_bcp_learned_1963_blocker_cert_shadow_hit(
                                                    elided_suffix_slots,
                                                    cert.fsw_seed,
                                                );
                                        } else {
                                            macro_rules! record_cert_prefix_scan_step {
                                                () => {{
                                                    if COLLECT_BCP_TELEMETRY {
                                                        self.stats.record_bcp_replacement_scan_step(
                                                            clause_len,
                                                            clause_is_learned,
                                                        );
                                                    }
                                                    if profile_learned_scan_pressure_or_identity_for_clause
                                                    {
                                                        learned_no_replacement_scan_pressure_steps += 1;
                                                    }
                                                }};
                                            }
                                            macro_rules! cert_prefix_slot_is_false {
                                                ($k:expr, $next_limit:expr) => {{
                                                    record_cert_prefix_scan_step!();
                                                    let lit_k = self.arena.bcp_literal(off, $k);
                                                    if $k + 1 < $next_limit {
                                                        let next_lit =
                                                            self.arena.bcp_literal(off, $k + 1);
                                                        ay_prefetch::prefetch_val_l1(
                                                            &self.vals,
                                                            next_lit.index(),
                                                        );
                                                    }
                                                    val_at(&self.vals, lit_k.index()) < 0
                                                }};
                                            }

                                            let mut cert_matches_normal_prefix = true;
                                            if known_false_saved_start < clause_len {
                                                debug_assert_eq!(pos, 2);
                                                for k in 2..cert_pos {
                                                    if !cert_prefix_slot_is_false!(
                                                        k,
                                                        known_false_saved_start
                                                    ) {
                                                        cert_matches_normal_prefix = false;
                                                        break;
                                                    }
                                                }
                                            } else {
                                                record_cert_prefix_scan_step!();
                                                for k in (normalized_saved_pos + 1)..clause_len {
                                                    if !cert_prefix_slot_is_false!(k, clause_len) {
                                                        cert_matches_normal_prefix = false;
                                                        break;
                                                    }
                                                }
                                                if cert_matches_normal_prefix {
                                                    for k in 2..cert_pos {
                                                        if !cert_prefix_slot_is_false!(k, cert_pos)
                                                        {
                                                            cert_matches_normal_prefix = false;
                                                            break;
                                                        }
                                                    }
                                                }
                                            }

                                            if cert_matches_normal_prefix {
                                                record_cert_prefix_scan_step!();
                                                replacement_k = cert_pos;
                                                replacement_val = cert_val;
                                                replacement_lit = cert_lit;
                                                blocker_cert_elided_scan = true;
                                                self.stats
                                                    .record_bcp_learned_1963_blocker_cert_elision(
                                                        elided_suffix_slots,
                                                        cert.fsw_seed,
                                                    );
                                            } else {
                                                self.stats
                                                    .record_bcp_learned_1963_blocker_cert_shadow_mismatch();
                                                if demote_learned_1963_blocker_cert_false_reject {
                                                    self.stats
                                                        .record_bcp_learned_1963_blocker_cert_mismatch_demotion();
                                                    self.stats
                                                        .clear_bcp_learned_1963_blocker_cert(off);
                                                }
                                            }
                                        }
                                    } else {
                                        self.stats
                                            .record_bcp_learned_1963_blocker_cert_false_reject();
                                        if demote_learned_1963_blocker_cert_false_reject {
                                            self.stats.clear_bcp_learned_1963_blocker_cert(off);
                                            self.stats
                                                .record_bcp_learned_1963_blocker_cert_false_reject_demotion();
                                        }
                                    }
                                }
                            }
                        }
                    }

                    if replacement_val < 0 && reset_false_start_candidate && saved_start_val >= 0 {
                        replacement_k = normalized_saved_pos;
                        replacement_val = saved_start_val;
                        replacement_lit = saved_start_lit;
                        if COLLECT_BCP_TELEMETRY {
                            self.stats
                                .record_bcp_replacement_scan_step(clause_len, clause_is_learned);
                        }
                        if profile_learned_scan_pressure_or_identity_for_clause {
                            learned_no_replacement_scan_pressure_steps += 1;
                        }
                    }

                    if replacement_val < 0 && specialize_len68_replacement_scan && clause_len <= 8 {
                        macro_rules! try_replacement_slot {
                            ($k:expr) => {{
                                if COLLECT_BCP_TELEMETRY {
                                    self.stats.record_bcp_replacement_scan_step(
                                        clause_len,
                                        clause_is_learned,
                                    );
                                }
                                if profile_learned_scan_pressure_or_identity_for_clause {
                                    learned_no_replacement_scan_pressure_steps += 1;
                                }
                                let lit_k = self.arena.bcp_literal(off, $k);
                                let v = val_at(&self.vals, lit_k.index());
                                if v >= 0 {
                                    replacement_k = $k;
                                    replacement_val = v;
                                    replacement_lit = lit_k;
                                    true
                                } else {
                                    false
                                }
                            }};
                        }
                        if known_false_saved_start < clause_len {
                            debug_assert_eq!(pos, 2);
                            for k in 2..known_false_saved_start {
                                if try_replacement_slot!(k) {
                                    break;
                                }
                            }
                            if replacement_val < 0 {
                                for k in (known_false_saved_start + 1)..clause_len {
                                    if try_replacement_slot!(k) {
                                        break;
                                    }
                                }
                            }
                        } else {
                            match clause_len {
                                6 => match pos {
                                    2 => {
                                        let _ = try_replacement_slot!(2)
                                            || try_replacement_slot!(3)
                                            || try_replacement_slot!(4)
                                            || try_replacement_slot!(5);
                                    }
                                    3 => {
                                        let _ = try_replacement_slot!(3)
                                            || try_replacement_slot!(4)
                                            || try_replacement_slot!(5)
                                            || try_replacement_slot!(2);
                                    }
                                    4 => {
                                        let _ = try_replacement_slot!(4)
                                            || try_replacement_slot!(5)
                                            || try_replacement_slot!(2)
                                            || try_replacement_slot!(3);
                                    }
                                    _ => {
                                        debug_assert_eq!(pos, 5);
                                        let _ = try_replacement_slot!(5)
                                            || try_replacement_slot!(2)
                                            || try_replacement_slot!(3)
                                            || try_replacement_slot!(4);
                                    }
                                },
                                7 => match pos {
                                    2 => {
                                        let _ = try_replacement_slot!(2)
                                            || try_replacement_slot!(3)
                                            || try_replacement_slot!(4)
                                            || try_replacement_slot!(5)
                                            || try_replacement_slot!(6);
                                    }
                                    3 => {
                                        let _ = try_replacement_slot!(3)
                                            || try_replacement_slot!(4)
                                            || try_replacement_slot!(5)
                                            || try_replacement_slot!(6)
                                            || try_replacement_slot!(2);
                                    }
                                    4 => {
                                        let _ = try_replacement_slot!(4)
                                            || try_replacement_slot!(5)
                                            || try_replacement_slot!(6)
                                            || try_replacement_slot!(2)
                                            || try_replacement_slot!(3);
                                    }
                                    5 => {
                                        let _ = try_replacement_slot!(5)
                                            || try_replacement_slot!(6)
                                            || try_replacement_slot!(2)
                                            || try_replacement_slot!(3)
                                            || try_replacement_slot!(4);
                                    }
                                    _ => {
                                        debug_assert_eq!(pos, 6);
                                        let _ = try_replacement_slot!(6)
                                            || try_replacement_slot!(2)
                                            || try_replacement_slot!(3)
                                            || try_replacement_slot!(4)
                                            || try_replacement_slot!(5);
                                    }
                                },
                                _ => {
                                    debug_assert_eq!(clause_len, 8);
                                    match pos {
                                        2 => {
                                            let _ = try_replacement_slot!(2)
                                                || try_replacement_slot!(3)
                                                || try_replacement_slot!(4)
                                                || try_replacement_slot!(5)
                                                || try_replacement_slot!(6)
                                                || try_replacement_slot!(7);
                                        }
                                        3 => {
                                            let _ = try_replacement_slot!(3)
                                                || try_replacement_slot!(4)
                                                || try_replacement_slot!(5)
                                                || try_replacement_slot!(6)
                                                || try_replacement_slot!(7)
                                                || try_replacement_slot!(2);
                                        }
                                        4 => {
                                            let _ = try_replacement_slot!(4)
                                                || try_replacement_slot!(5)
                                                || try_replacement_slot!(6)
                                                || try_replacement_slot!(7)
                                                || try_replacement_slot!(2)
                                                || try_replacement_slot!(3);
                                        }
                                        5 => {
                                            let _ = try_replacement_slot!(5)
                                                || try_replacement_slot!(6)
                                                || try_replacement_slot!(7)
                                                || try_replacement_slot!(2)
                                                || try_replacement_slot!(3)
                                                || try_replacement_slot!(4);
                                        }
                                        6 => {
                                            let _ = try_replacement_slot!(6)
                                                || try_replacement_slot!(7)
                                                || try_replacement_slot!(2)
                                                || try_replacement_slot!(3)
                                                || try_replacement_slot!(4)
                                                || try_replacement_slot!(5);
                                        }
                                        _ => {
                                            debug_assert_eq!(pos, 7);
                                            let _ = try_replacement_slot!(7)
                                                || try_replacement_slot!(2)
                                                || try_replacement_slot!(3)
                                                || try_replacement_slot!(4)
                                                || try_replacement_slot!(5)
                                                || try_replacement_slot!(6);
                                        }
                                    }
                                }
                            }
                        }
                    } else if replacement_val < 0 {
                        macro_rules! try_generic_replacement_lit {
                            ($k:expr, $lit_k:expr, $next_lit:expr) => {{
                                if COLLECT_BCP_TELEMETRY {
                                    self.stats.record_bcp_replacement_scan_step(
                                        clause_len,
                                        clause_is_learned,
                                    );
                                }
                                if profile_learned_scan_pressure_or_identity_for_clause {
                                    learned_no_replacement_scan_pressure_steps += 1;
                                }
                                // Prefetch val for the NEXT literal while checking this one.
                                if let Some(next_lit) = $next_lit {
                                    ay_prefetch::prefetch_val_l1(&self.vals, next_lit.index());
                                }
                                let lit_k = $lit_k;
                                let v = val_at(&self.vals, lit_k.index());
                                if v >= 0 {
                                    replacement_k = $k;
                                    replacement_val = v;
                                    replacement_lit = lit_k;
                                    true
                                } else {
                                    false
                                }
                            }};
                        }
                        macro_rules! try_generic_replacement_slot {
                            ($k:expr, $next_limit:expr) => {{
                                let lit_k = self.arena.bcp_literal(off, $k);
                                let next_lit = if $k + 1 < $next_limit {
                                    Some(self.arena.bcp_literal(off, $k + 1))
                                } else {
                                    None
                                };
                                try_generic_replacement_lit!($k, lit_k, next_lit)
                            }};
                        }
                        macro_rules! scan_generic_replacement_range {
                            ($start:expr, $end:expr) => {{
                                let start = $start;
                                let end = $end;
                                let mut found = false;
                                if start < end {
                                    let mut k = start;
                                    let mut lit_k = self.arena.bcp_literal(off, k);
                                    loop {
                                        let next_k = k + 1;
                                        let next_lit = if next_k < end {
                                            Some(self.arena.bcp_literal(off, next_k))
                                        } else {
                                            None
                                        };
                                        if try_generic_replacement_lit!(k, lit_k, next_lit) {
                                            found = true;
                                            break;
                                        }
                                        if let Some(next_lit) = next_lit {
                                            k = next_k;
                                            lit_k = next_lit;
                                        } else {
                                            break;
                                        }
                                    }
                                }
                                found
                            }};
                        }

                        // Val prefetch optimization (#8465): on large instances
                        // (50K+ vars), vals[] spans ~100KB+. Each literal indexes
                        // randomly into it. Prefetch vals[lits[k+1]] while checking
                        // vals[lits[k]] to hide L2/L3 latency.
                        if known_false_saved_start < clause_len && gent_skip_known_false_saved_start
                        {
                            self.arena.prefetch_clause_tail(off, clause_len);
                            scan_generic_replacement_range!(
                                known_false_saved_start + 1,
                                clause_len
                            );
                            if replacement_val < 0 {
                                scan_generic_replacement_range!(2, known_false_saved_start);
                            }
                        } else if known_false_saved_start < clause_len {
                            // Second cache-line prefetch (#8000): the split scan is
                            // known to skip one false saved-start slot and continue
                            // through the tail.
                            self.arena.prefetch_clause_tail(off, clause_len);
                            debug_assert_eq!(pos, 2);
                            scan_generic_replacement_range!(2, known_false_saved_start);
                            if replacement_val < 0 {
                                scan_generic_replacement_range!(
                                    known_false_saved_start + 1,
                                    clause_len
                                );
                            }
                        } else {
                            // Check the saved-position slot first. If it is
                            // non-false, avoid the second cache-line prefetch and
                            // the rest of the generic loop setup on the common
                            // saved-position-hit path.
                            if !try_generic_replacement_slot!(pos, clause_len) {
                                self.arena.prefetch_clause_tail(off, clause_len);
                                scan_generic_replacement_range!(pos + 1, clause_len);
                                if replacement_val < 0 && pos > 2 {
                                    scan_generic_replacement_range!(2, pos);
                                }
                            }
                        }
                    }
                    if COLLECT_BCP_TELEMETRY && gent_skip_known_false_saved_start {
                        self.stats.record_bcp_learned_1963_fsw_gent_skip(
                            replacement_val,
                            replacement_k,
                            known_false_saved_start,
                            first_val,
                        );
                    }
                    if let Some((cert_pos, cert_lit_raw)) = blocker_cert_shadow_probe {
                        if replacement_val <= 0
                            || replacement_k != cert_pos
                            || replacement_lit.0 != cert_lit_raw
                        {
                            self.stats
                                .record_bcp_learned_1963_blocker_cert_shadow_mismatch();
                            if demote_learned_1963_blocker_cert_false_reject {
                                self.stats
                                    .record_bcp_learned_1963_blocker_cert_mismatch_demotion();
                                self.stats.clear_bcp_learned_1963_blocker_cert(off);
                            }
                        }
                    }
                    // Update saved position only when a replacement was found
                    // and differs from the cached position (#8569). When no
                    // replacement is found (sentinel), skip the arena write.
                    // The default-off advance experiment only steps past an
                    // unassigned replacement for learned long clauses after
                    // missing the saved start when the next tail slot is not
                    // already false.
                    let off = clause_idx;
                    if replacement_k < clause_len {
                        let learned_1963_true_tail_candidate = RELOCATE_LEARNED_1963_TRUE_TAIL
                            && clause_is_learned
                            && (19..=63).contains(&clause_len);
                        let learned_618_true_tail_candidate = relocate_learned_618_true_tail
                            && clause_is_learned
                            && (6..=18).contains(&clause_len);
                        if COLLECT_BCP_TELEMETRY && learned_1963_true_tail_candidate {
                            self.stats
                                .record_bcp_learned_1963_true_tail_relocation_attempt(
                                    replacement_val,
                                );
                        }
                        if COLLECT_BCP_TELEMETRY && learned_618_true_tail_candidate {
                            self.stats
                                .record_bcp_learned_618_true_tail_relocation_attempt(
                                    replacement_val,
                                );
                        }
                        relocate_true_tail_watch = replacement_val > 0
                            && (learned_1963_true_tail_candidate
                                || learned_618_true_tail_candidate);
                        let saved_pos = if relocate_true_tail_watch {
                            if replacement_k + 1 < clause_len {
                                replacement_k + 1
                            } else {
                                2
                            }
                        } else if ADVANCE_SAVED_POS_AFTER_UNASSIGNED_MOVE
                            && clause_is_learned
                            && clause_len >= 6
                            && replacement_val == 0
                            && replacement_k != pos
                        {
                            let next_k = if replacement_k + 1 < clause_len {
                                replacement_k + 1
                            } else {
                                2
                            };
                            let next_lit = self.arena.bcp_literal(off, next_k);
                            if val_at(&self.vals, next_lit.index()) >= 0 {
                                next_k
                            } else {
                                replacement_k
                            }
                        } else {
                            replacement_k
                        };
                        if saved_pos != cached_saved_pos {
                            self.arena.set_saved_pos(off, saved_pos);
                        }
                    } else if reset_learned_1963_used5_fsw_saved_pos_candidate {
                        let wrote = first_val <= 0 && cached_saved_pos != 2;
                        if wrote {
                            self.arena.set_saved_pos(off, 2);
                        }
                        if COLLECT_BCP_TELEMETRY && MODE == bcp_mode::SEARCH {
                            self.stats
                                .record_bcp_learned_1963_used5_fsw_saved_pos_reset(
                                    first_val, wrote,
                                );
                        }
                    } else if reset_learned_1963_fsw_conflict_saved_pos_candidate
                        && saved_start_val < 0
                        && first_val < 0
                    {
                        let wrote = cached_saved_pos != 2;
                        if wrote {
                            self.arena.set_saved_pos(off, 2);
                        }
                        if COLLECT_BCP_TELEMETRY && MODE == bcp_mode::SEARCH {
                            self.stats
                                .record_bcp_learned_1963_fsw_conflict_saved_pos_reset(wrote);
                        }
                    } else if update_learned_no_replacement_saved_pos
                        && clause_is_learned
                        && (6..=63).contains(&clause_len)
                    {
                        let wrote = cached_saved_pos != 2;
                        if wrote {
                            self.arena.set_saved_pos(off, 2);
                        }
                        if COLLECT_BCP_TELEMETRY && MODE == bcp_mode::SEARCH {
                            self.stats
                                .record_bcp_learned_no_replacement_saved_pos_update(
                                    bcp_long_scan_bucket,
                                    first_val,
                                    wrote,
                                );
                        }
                    }
                    if profile_learned_no_replacement_scan_pressure_for_clause
                        && replacement_val < 0
                    {
                        self.stats.record_bcp_learned_no_replacement_scan_pressure(
                            bcp_long_scan_bucket,
                            learned_no_replacement_scan_pressure_steps,
                            first_val,
                            saved_start_val < 0,
                            normalized_saved_pos > 2,
                            self.arena.lbd(off),
                            self.arena.used(off),
                            off,
                        );
                    }
                    if profile_learned_1963_identity_for_clause {
                        let clause_id = self.cold.clause_ids.get(off).copied().unwrap_or(0);
                        let birth_conflict = self
                            .cold
                            .bcp_learned_clause_birth_conflicts
                            .get(off)
                            .copied()
                            .unwrap_or(self.num_conflicts);
                        self.stats.record_bcp_learned_1963_identity(
                            clause_id,
                            off,
                            clause_len,
                            self.num_conflicts,
                            birth_conflict,
                            learned_no_replacement_scan_pressure_steps,
                            replacement_val,
                            first_val,
                            saved_start_val < 0,
                            normalized_saved_pos > 2,
                            self.arena.lbd(off),
                            self.arena.used(off),
                        );
                    }
                    if learned_1963_blocker_cert_for_clause
                        && !blocker_cert_elided_scan
                        && replacement_val > 0
                        && replacement_k >= 2
                        && replacement_k < clause_len
                    {
                        let fsw_seed = saved_start_val < 0
                            && normalized_saved_pos > 2
                            && replacement_k < normalized_saved_pos;
                        if fsw_seed {
                            self.stats.record_bcp_learned_1963_blocker_cert_populate(
                                off,
                                replacement_k,
                                replacement_lit.0,
                                true,
                            );
                        }
                    }
                    if COLLECT_BCP_TELEMETRY {
                        match replacement_val {
                            v if v > 0 => {
                                self.stats.bcp_long_saved_pos_found_true += 1;
                                if clause_len == 18 {
                                    self.stats.bcp_len18_saved_pos_found_true += 1;
                                }
                            }
                            0 => {
                                self.stats.bcp_long_saved_pos_found_unassigned += 1;
                                if clause_len == 18 {
                                    self.stats.bcp_len18_saved_pos_found_unassigned += 1;
                                }
                            }
                            _ => {
                                self.stats.bcp_long_saved_pos_no_replacement += 1;
                                if clause_len == 18 {
                                    self.stats.bcp_len18_saved_pos_no_replacement += 1;
                                }
                            }
                        }
                    }
                    if COLLECT_BCP_TELEMETRY && MODE == bcp_mode::SEARCH {
                        if replacement_val >= 0 {
                            self.stats.record_bcp_long_found_replacement(
                                bcp_long_scan_bucket,
                                bcp_long_scan_learned,
                                replacement_val,
                            );
                        } else {
                            self.stats.record_bcp_long_no_replacement(
                                bcp_long_scan_bucket,
                                bcp_long_scan_learned,
                                first_val,
                            );
                        }
                    }
                }

                // Note: `off` must be rebound after the saved_pos block since
                // the short-clause path doesn't rebind it.
                let off = clause_idx;

                if replacement_val > 0 {
                    if relocate_true_tail_watch {
                        debug_assert!(
                            replacement_k >= 2 && replacement_k < clause_len,
                            "BUG: replacement index {replacement_k} outside [2, {clause_len}) for clause {clause_idx}"
                        );
                        ticks += 1; // Same watch movement accounting as unassigned replacement.
                        self.arena.swap_literals(off, false_pos, replacement_k);
                        self.deferred_replacement_watches
                            .push((replacement_lit, Watcher::new(clause_ref, first)));
                        continue;
                    }
                    // CaDiCaL propagate.cpp:369-373: replacement satisfied,
                    // just replace blit (blocker). No watch movement needed.
                    //
                    // LSCB (#8442): check for Missed Lower Implication (MLI).
                    // If the replacement literal is TRUE but assigned at a
                    // higher level than the clause's assertion level (max
                    // level among all false literals), this clause could
                    // reimply the replacement literal at a lower level.
                    // Record it in the lambda vector for lazy reimplication
                    // during backtracking and as an alternative reason in
                    // conflict analysis.
                    // LSCB MLI detection DISABLED (#8448): The per-clause
                    // assertion-level scan in the hot BCP replacement path
                    // adds O(clause_len) overhead to every satisfied-replacement
                    // case. On small dense formulas (clique_n2_k10: 180 vars),
                    // this causes 30s+ timeouts. Combined with the lambda reason
                    // substitution disable in conflict analysis, the full LSCB
                    // pipeline is now deactivated pending a correct and efficient
                    // reimplementation.
                    // Reference: Coutelier, Fleury, Kovacs "Lazy Reimplication
                    // in Chronological Backtracking" (SAT 2024), Algorithm 2.
                    bcp_set_kept_blocker(
                        &mut self.deferred_watch_list,
                        j,
                        entry,
                        replacement_lit.0,
                    );
                    j += 1;
                    continue;
                } else if replacement_val == 0 {
                    // CaDiCaL propagate.cpp:375-389: found new unassigned
                    // replacement literal. Move watch from false_lit to lit_k.
                    debug_assert!(
                        replacement_k >= 2 && replacement_k < clause_len,
                        "BUG: replacement index {replacement_k} outside [2, {clause_len}) for clause {clause_idx}"
                    );
                    ticks += 1; // CaDiCaL propagate.cpp:389 — watch replacement
                    self.arena.swap_literals(off, false_pos, replacement_k);
                    // Defer the watch addition to avoid cache pollution from
                    // writing to a different literal's watch list during the
                    // hot BCP scan. Flushed after the current literal's watch
                    // list processing completes. Kissat proplit.h pattern (#8041).
                    self.deferred_replacement_watches
                        .push((replacement_lit, Watcher::new(clause_ref, first)));
                    continue;
                }

                // replacement_val < 0: no replacement found. All non-watched
                // literals are false.
                // CaDiCaL propagate.cpp:393: every tail literal must be false
                // when we reach the unit/conflict branch.
                debug_assert!(
                    (2..clause_len).all(|k| self.lit_val(self.arena.literal(off, k)) < 0),
                    "BUG: no-replacement path reached but a tail literal in clause {clause_idx} is not false"
                );
                if first_val < 0 {
                    // CaDiCaL propagate.cpp:439-448: conflict — both watched
                    // literals false, all tail literals false.
                    self.flush_bcp_ticks::<MODE>(ticks);
                    // SEARCH mode: pass saved binary count to skip recount.
                    // PROBE/VIVIFY: pass u32::MAX to use generic recount.
                    let bc = if MODE == bcp_mode::SEARCH {
                        saved_bc
                    } else {
                        u32::MAX
                    };
                    if MODE == bcp_mode::SEARCH {
                        self.num_search_propagations += (self.qhead - qhead_start) as u64;
                    }
                    return Some(self.conflict_finalize(
                        false_lit,
                        clause_ref,
                        j + 1,
                        i,
                        watch_len,
                        qhead_start,
                        bc,
                    ));
                }

                // Unit propagation
                let mut unit_reason = Some(clause_ref);

                // Probe parent tracking + hyper-binary resolution at level 1.
                //
                // Parent tracking (probe_parent) runs whenever probing_mode is
                // active — CaDiCaL ALWAYS sets parent = dominator for level-1
                // long-clause propagation (probe.cpp:477-478), regardless of
                // whether HBR is enabled or LRAT is on.
                //
                // HBR clause creation additionally requires hbr_enabled and
                // !lrat_enabled (HBR clauses lack LRAT proof steps — #4647).
                if MODE == bcp_mode::PROBE
                    && self.probing_mode
                    && self.decision_level == 1
                    && clause_len > 2
                {
                    self.handle_probe_hbr(
                        false_lit,
                        first,
                        clause_idx,
                        clause_len,
                        &mut unit_reason,
                    );
                }

                // Debug contract: probe assignment coherence (#4753 Step 2).
                if MODE == bcp_mode::PROBE {
                    debug_assert!(
                        !self.probing_mode
                            || self.decision_level != 1
                            || clause_len <= 2
                            || self.probe_parent[first.variable().index()].is_some(),
                        "BUG: probe_parent missing for level-1 implied literal"
                    );
                }

                let skip_unit_blocker_refresh =
                    disable_learned_1963_no_replacement_unit_blocker_refresh
                        && clause_is_learned
                        && (19..=63).contains(&clause_len);
                if !skip_unit_blocker_refresh {
                    bcp_set_kept_blocker(&mut self.deferred_watch_list, j, entry, first.0);
                }
                ticks += 1; // CaDiCaL propagate.cpp:401 — long clause unit
                j += 1;
                // Lightweight enqueue for SEARCH mode (#8042).
                // ChrBT dispatch (#8569): nochrono variant skips the
                // O(clause_len) assignment_level scan.
                if MODE == bcp_mode::SEARCH {
                    let reason = unit_reason.expect("unit propagation always has reason");
                    if chrono {
                        self.enqueue_bcp::<true>(first, reason);
                    } else {
                        self.enqueue_bcp_nochrono(first, reason);
                    }
                } else {
                    self.enqueue(first, unit_reason);
                }
            }

            // Copy remaining unscanned watchers when breaking early due to binary conflict (#8043).
            // When a binary conflict is found, BCP continues through binary watchers but
            // breaks at the first long-clause watcher (CaDiCaL propagate.cpp:301-302).
            // The break skips entries from i..watch_len that must be preserved.
            if binary_conflict.is_some() && i < watch_len {
                self.deferred_watch_list.copy_within(i, watch_len, j);
                j += watch_len - i;
            }

            // ENSURES: compaction preserved all kept watchers
            debug_assert!(
                j <= watch_len,
                "BCP: final j ({j}) > watch_len ({watch_len}) after compaction"
            );

            // Compaction complete: truncate + restore.
            // SEARCH mode (#8465): use restore_from_deferred_with_bc to skip
            // the O(n) count_binary_clauses scan. BCP compaction never drops
            // binary watchers, so the binary count is preserved from the
            // initial copy_to_deferred call.
            // PROBE/VIVIFY modes: use generic restore_from_deferred since HBR
            // can add overflow entries that change the binary count.
            if MODE == bcp_mode::SEARCH {
                self.finalize_watch_list_with_bc(false_lit, j, saved_bc);
            } else {
                self.finalize_watch_list(false_lit, j);
            }

            // Flush deferred replacement watches (#8041). These were collected
            // during the scan above to avoid cache pollution from writing to
            // other literals' watch lists during the hot BCP inner loop.
            // Fast path (#7998): skip the loop setup when no replacements were
            // found (common for short watch lists or mostly-binary formulas).
            if !self.deferred_replacement_watches.is_empty() {
                for &(lit, watcher) in &self.deferred_replacement_watches {
                    self.watches.add_watch(lit, watcher);
                }
                self.deferred_replacement_watches.clear();
            }

            // CaDiCaL propagate.cpp:289-302: if a binary conflict was found
            // during the binary watcher scan, finalize it now (#8043).
            if let Some(conflict_ref) = binary_conflict {
                self.flush_bcp_ticks::<MODE>(ticks);
                if MODE == bcp_mode::SEARCH {
                    self.num_search_propagations += (self.qhead - qhead_start) as u64;
                }
                return Some(self.binary_conflict_finalize(conflict_ref, qhead_start));
            }
        }

        self.num_propagations += (self.qhead - qhead_start) as u64;
        if MODE == bcp_mode::SEARCH {
            self.num_search_propagations += (self.qhead - qhead_start) as u64;
        }
        self.flush_bcp_ticks::<MODE>(ticks);
        // Reason marks maintained incrementally by enqueue_bcp (#8100).
        self.no_conflict_until = self.trail.len();
        // CaDiCaL propagate.cpp:505: post-BCP propagation completeness
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: propagate_bcp completed but qhead ({}) != trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );
        None
    }

    /// Flush accumulated BCP ticks to the per-technique counter.
    ///
    /// Zero-cost: the const-generic MODE is known at monomorphization, so the
    /// match compiles to a single branch. CaDiCaL stats.hpp:36.
    #[inline(always)]
    pub(super) fn flush_bcp_ticks<const MODE: u8>(&mut self, ticks: u64) {
        match MODE {
            bcp_mode::SEARCH => {
                self.search_ticks[usize::from(self.stable_mode)] += ticks;
            }
            bcp_mode::PROBE => {
                self.cold.probe_ticks += ticks;
            }
            bcp_mode::VIVIFY => {
                self.cold.vivify_ticks += ticks;
            }
            _ => {}
        }
    }

    /// Hyper-binary resolution (HBR) helper for PROBE mode.
    ///
    /// Handles probe_parent tracking and optional HBR clause creation
    /// at decision level 1 during probing. Extracted from the BCP loop
    /// to keep the unified function readable (#5037).
    pub(super) fn handle_probe_hbr(
        &mut self,
        false_lit: Literal,
        first: Literal,
        clause_idx: usize,
        clause_len: usize,
        unit_reason: &mut Option<ClauseRef>,
    ) {
        // Guard: after compaction, stale watches may reference literals
        // with variables beyond the current num_vars (#9215).
        if first.variable().index() >= self.num_vars {
            return;
        }
        let off = clause_idx;
        self.hbr_lits.clear();
        self.hbr_lits.push(first);
        for k in 0..clause_len {
            let lit_k = self.arena.literal(off, k);
            if lit_k != first {
                self.hbr_lits.push(lit_k);
            }
        }

        let is_learned = self.arena.is_learned(off);
        let hbr_result = hyper_binary_resolve(
            &self.hbr_lits,
            &self.trail,
            &self.var_data,
            &self.probe_parent,
            &self.arena,
            is_learned,
        );

        // Set probe_parent for the propagated literal (#3419/#4719).
        // CaDiCaL probe.cpp:477-478: parent = dominator ALWAYS,
        // even when no HBR binary clause is created. The dominator
        // is the parent in the binary implication tree at level 1.
        // Guard: after compaction, stale watch entries may reference
        // variables beyond the current num_vars (#9215).
        let var_idx = first.variable().index();
        if var_idx < self.probe_parent.len() {
            self.probe_parent[var_idx] = hbr_result.dominator;
        }

        if self.hbr_enabled && !self.cold.lrat_enabled {
            if let Some((dom_neg, unit)) = hbr_result.binary_clause {
                // Guard: after compaction, stale watches may produce HBR
                // clauses with literals beyond the current num_vars (#9215).
                if dom_neg.variable().index() >= self.num_vars
                    || unit.variable().index() >= self.num_vars
                {
                    return;
                }
                // Emit HBR clause to proof stream (#4966). HBR clauses
                // are derived via resolution from the original clause and
                // binary implication chains — they ARE RUP-derivable.
                let _ =
                    self.proof_emit_add_prechecked(&[dom_neg, unit], &[], ProofAddKind::Derived);
                let hbr_idx = self.add_clause_db_checked(
                    &[dom_neg, unit],
                    hbr_result.is_redundant,
                    true,
                    &[],
                );
                // CaDiCaL propagate.cpp:434-438: mark HBR clause for
                // one-round lifetime in reduce_db (reduce.cpp:116-120).
                self.arena.set_hyper(hbr_idx, true);
                // Notify BVE of new irredundant HBR clause (#8096).
                // Use wrapper to also bump bve_marked and mark JIT dirty vars (#8202).
                if !hbr_result.is_redundant {
                    self.note_irredundant_clause_added_for_bve(hbr_idx, &[dom_neg, unit]);
                }
                self.inproc.prober.record_hbr(
                    clause_len,
                    hbr_result.is_redundant,
                    hbr_result.subsumes_original,
                );

                let hbr_ref = ClauseRef(hbr_idx as u32);
                let dom_watch = Watcher::binary(hbr_ref, unit);
                let unit_watch = Watcher::binary(hbr_ref, dom_neg);
                let mut hbr_dom_targets_false_lit = false;
                let mut hbr_unit_targets_false_lit = false;

                // CaDiCaL probe.cpp:262: probe_reason = c
                // When HBR emits a binary clause, the propagated
                // literal's reason is ALWAYS the new binary clause.
                *unit_reason = Some(hbr_ref);

                if dom_neg == false_lit {
                    hbr_dom_targets_false_lit = true;
                } else {
                    self.watches.add_watch(dom_neg, dom_watch);
                }
                if unit == false_lit {
                    hbr_unit_targets_false_lit = true;
                } else {
                    self.watches.add_watch(unit, unit_watch);
                }

                // CaDiCaL probe.cpp:267-271: subsumed original is marked
                // garbage immediately.
                if hbr_result.subsumes_original {
                    let off = clause_idx;
                    if !self.arena.is_pending_garbage(off) {
                        self.stats.clear_bcp_learned_1963_blocker_cert(off);
                        self.arena.set_pending_garbage(off, true);
                        self.pending_garbage_count += 1;
                    }
                }

                // HBR watchers targeting false_lit go into watches[false_lit],
                // which is marked empty while deferred entries are scanned.
                // They are merged back after the inner loop.
                if hbr_dom_targets_false_lit {
                    self.watches
                        .get_watches_mut(false_lit)
                        .push_watcher(dom_watch);
                }
                if hbr_unit_targets_false_lit {
                    self.watches
                        .get_watches_mut(false_lit)
                        .push_watcher(unit_watch);
                }
            }
        }
    }

    /// Finalize the watch list after processing all watchers for a literal:
    /// truncate to the compacted length, merge any HBR overflow, and restore.
    /// Uses `count_binary_clauses` to recount (PROBE/VIVIFY modes).
    #[inline(always)]
    fn finalize_watch_list(&mut self, false_lit: Literal, j: usize) {
        self.deferred_watch_list.truncate(j);
        self.watches
            .restore_from_deferred(false_lit, &mut self.deferred_watch_list);
    }

    /// Finalize the watch list with a pre-computed binary count (#8465).
    ///
    /// BCP compaction never drops binary watchers, so the binary count from
    /// `copy_to_deferred` is still valid. This skips the O(n) binary count
    /// re-scan that `restore_from_deferred` performs. Used by SEARCH mode BCP.
    #[inline(always)]
    fn finalize_watch_list_with_bc(&mut self, false_lit: Literal, j: usize, binary_count: u32) {
        self.deferred_watch_list.truncate(j);
        self.watches.restore_from_deferred_with_bc(
            false_lit,
            &mut self.deferred_watch_list,
            binary_count,
        );
    }

    /// Finalize a binary conflict after the watch list has been restored.
    #[inline(always)]
    fn binary_conflict_finalize(
        &mut self,
        conflict_ref: ClauseRef,
        qhead_start: usize,
    ) -> ClauseRef {
        self.num_propagations += (self.qhead - qhead_start) as u64;
        // Reason marks maintained incrementally by enqueue_bcp (#8100).
        self.no_conflict_until = if self.decision_level == 0 {
            0
        } else {
            self.trail_lim[self.decision_level as usize - 1]
        };
        let clause_id = self.clause_id(conflict_ref);
        self.last_conflict_clause_ref = Some(conflict_ref);
        self.last_conflict_clause_id = clause_id;
        let trace_clause_id = if clause_id == 0 {
            u64::from(conflict_ref.0) + 1
        } else {
            clause_id
        };
        self.trace_conflict(trace_clause_id);
        conflict_ref
    }

    /// Finalize a conflict in the BCP loop: copy remaining watchers, finalize
    /// the watch list, and update propagation statistics.
    ///
    /// `j_start` is the write position after keeping the current watcher (j+1).
    /// `i` / `watch_len` delimit the unvisited watcher range to copy.
    /// `binary_count` is the pre-computed binary count for the optimized
    /// restore path (pass u32::MAX to use the generic `count_binary_clauses`).
    #[inline(always)]
    fn conflict_finalize(
        &mut self,
        false_lit: Literal,
        clause_ref: ClauseRef,
        j_start: usize,
        i: usize,
        watch_len: usize,
        qhead_start: usize,
        binary_count: u32,
    ) -> ClauseRef {
        let mut j = j_start;
        if i < watch_len {
            self.deferred_watch_list.copy_within(i, watch_len, j);
            j += watch_len - i;
        }
        if binary_count != u32::MAX {
            self.finalize_watch_list_with_bc(false_lit, j, binary_count);
        } else {
            self.finalize_watch_list(false_lit, j);
        }
        // Flush deferred replacement watches on conflict path (#8041).
        if !self.deferred_replacement_watches.is_empty() {
            for &(lit, watcher) in &self.deferred_replacement_watches {
                self.watches.add_watch(lit, watcher);
            }
            self.deferred_replacement_watches.clear();
        }
        self.num_propagations += (self.qhead - qhead_start) as u64;
        // CaDiCaL propagate.cpp:487: trail before current decision level
        // was conflict-free.
        self.no_conflict_until = if self.decision_level == 0 {
            0
        } else {
            self.trail_lim[self.decision_level as usize - 1]
        };
        // CaDiCaL propagate.cpp:441-442: conflict clause has both watched lits false
        debug_assert!(
            {
                let ci = clause_ref.0 as usize;
                let l0 = self.arena.literal(ci, 0);
                let l1 = self.arena.literal(ci, 1);
                self.lit_val(l0) < 0 && self.lit_val(l1) < 0
            },
            "BUG: conflict clause {} does not have both watched lits false",
            clause_ref.0
        );
        let clause_id = self.clause_id(clause_ref);
        self.last_conflict_clause_ref = Some(clause_ref);
        self.last_conflict_clause_id = clause_id;
        let trace_clause_id = if clause_id == 0 {
            u64::from(clause_ref.0) + 1
        } else {
            clause_id
        };
        self.trace_conflict(trace_clause_id);
        solver_log!(
            self,
            "conflict clause {} at level {}",
            clause_ref.0,
            self.decision_level
        );
        clause_ref
    }

    /// Domain-restricted BCP for cone-of-influence queries (#8475),
    /// SEARCH-mode variant.
    ///
    /// Standard two-watched-literal propagation (Een & Sorensson, "An
    /// Extensible SAT-solver", SAT 2003) restricted to a variable subset:
    /// IC3/PDR-style incremental queries are solved inside a
    /// cone-of-influence domain (arXiv:2502.13605 §3), and restricted BCP
    /// never assigns a literal over a non-domain variable — neither by
    /// binary nor by long-clause unit propagation. Callers below the
    /// small-formula breakpoint use full BCP instead (#8802).
    ///
    /// `domain` is a per-variable bitmap built by `set_domain`
    /// (`solver/incremental.rs`) and closed under clause co-occurrence by
    /// `expand_domain_bcp` (COI closure to a fixpoint). Together with
    /// domain-restricted decisions and the level-0-uses-full-BCP rule, the
    /// closure gives the domain invariant: above level 0 every assigned
    /// variable is a domain variable, and every non-domain variable is
    /// unassigned except for root-level units, which full BCP established
    /// before the domain query.
    ///
    /// The delta from base BCP: a watcher whose examined watched literal
    /// (the cached blocker, or the clause's other watched literal) is
    /// UNASSIGNED and over a non-domain variable is trivially satisfiable
    /// for the restricted query — the watcher is kept unmodified, produces
    /// no propagation and no conflict, and `stats.domain_bcp_skips` counts
    /// it. Skipped watchers satisfy the two-watched-literal invariant
    /// vacuously (an unassigned watched literal needs no repair). A FALSE
    /// watched literal over a non-domain variable — a root-level unit, or
    /// a watch re-established between queries by clause-DB maintenance
    /// (#8661) — is processed exactly as in base BCP: skipping it could
    /// miss a forced domain propagation or a conflict. Clauses whose
    /// examined watched literals are all over domain variables take the
    /// unmodified base paths (blocker-satisfied keep, replacement scan,
    /// watch move, unit propagation, conflict).
    ///
    /// Keeps the SEARCH amenities of the base loop: tick accounting
    /// (`flush_bcp_ticks::<SEARCH>`), the deferred-scan blocker fast path,
    /// Gent saved-position replacement scanning, and the CaDiCaL behavior
    /// of continuing through later binary watchers after a binary conflict.
    ///
    /// REQUIRES: decision_level > 0 (level 0 always uses full BCP),
    ///           !has_empty_clause, qhead <= trail.len(), `domain` closed
    ///           under clause co-occurrence
    /// ENSURES: if None, qhead == trail.len(), only domain variables were
    ///          newly assigned, and the trail is exactly what full BCP
    ///          would produce when only domain variables are decided (the
    ///          COI closure precondition is load-bearing here); if
    ///          Some(cref), both watched literals of cref are false, qhead
    ///          is frozen at the conflict point, and the unprocessed watch
    ///          suffix is retained; watch lists stay consistent and
    ///          deferred replacement watches are flushed in both outcomes
    #[inline]
    pub(super) fn propagate_domain_bcp(&mut self, domain: &[bool]) -> Option<ClauseRef> {
        self.propagate_domain_bcp_impl::<false>(domain)
    }

    /// Shared core of domain-restricted BCP (#8475, #8569).
    ///
    /// `IC3 == false`: SEARCH-mode variant (see
    /// [`Solver::propagate_domain_bcp`]) — ticks, saved position, binary
    /// conflicts recorded and scanned past (CaDiCaL style), chrono-aware
    /// enqueues.
    ///
    /// `IC3 == true`: stripped variant for thousands of short IC3/PDR
    /// queries (see the non-`raw-pointer-bcp` [`Solver::propagate_bcp_ic3`]) —
    /// no tick accounting, no saved position, immediate return on any
    /// conflict (including binary), IC3 enqueue helpers (no chronological
    /// backtracking, no phase saving), garbage-bit check retained (#8661).
    ///
    /// Both use ay's deferred copy/restore watch-list iteration and the
    /// shared conflict finalizers, so the entry/exit bookkeeping
    /// (`num_propagations`, `no_conflict_until`,
    /// `last_conflict_clause_ref`/`id`, `trace_conflict`) matches base BCP.
    fn propagate_domain_bcp_impl<const IC3: bool>(&mut self, domain: &[bool]) -> Option<ClauseRef> {
        debug_assert!(
            self.decision_level > 0,
            "BUG: propagate_domain_bcp_impl called at level 0 — level 0 must use full BCP"
        );
        debug_assert!(
            !self.has_empty_clause,
            "BUG: propagate_domain_bcp_impl called with has_empty_clause=true"
        );
        debug_assert!(
            self.qhead <= self.trail.len(),
            "BUG: propagate_domain_bcp_impl entry qhead ({}) > trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );
        if IC3 {
            debug_assert!(
                self.cold.ic3_mode,
                "BUG: propagate_bcp_ic3 called without ic3_mode"
            );
            debug_assert!(
                !self.chrono_enabled,
                "BUG: propagate_bcp_ic3 requires chronological backtracking disabled"
            );
        }
        self.last_conflict_clause_ref = None;
        self.last_conflict_clause_id = 0;
        self.stats.domain_bcp_calls += 1;
        let qhead_start = self.qhead;
        let mut ticks: u64 = 0;
        // Cache ChrBT flag once for the entire propagation loop (#8569).
        let chrono = !IC3 && self.chrono_enabled;

        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            let false_lit = p.negated();

            // Copy watch list into the deferred buffer for iteration;
            // `i` is the read cursor, `j` the compaction write cursor.
            let (watch_len, saved_bc) = self
                .watches
                .copy_to_deferred(false_lit, &mut self.deferred_watch_list);
            let mut i: usize = 0;
            let mut j: usize = 0;
            if !IC3 {
                ticks += 1 + (watch_len as u64).div_ceil(32);
            }

            // CaDiCaL behavior kept by the SEARCH variant (#8043): a binary
            // conflict does not immediately break — the scan continues
            // through the remaining binary watchers (cheap, no arena
            // access) and breaks at the first long watcher. The IC3 variant
            // returns immediately instead (#8569) and never sets this.
            let mut binary_conflict: Option<ClauseRef> = None;

            'watch: loop {
                // #maxsat-domain-bcp-fix: fused domain fast-path scan — the #8475
                // out-of-domain skip is handled IN the tight loop (see helper),
                // not by unwinding to this outer loop per watcher.
                let entries = self.deferred_watch_list.entries_mut();
                let (new_i, new_j, skips, slow_entry) =
                    bcp_scan_blocker_fast_path_domain(entries, &self.vals, domain, i, j);
                i = new_i;
                j = new_j;
                self.stats.domain_bcp_skips += skips;
                let Some((blocker_raw, entry, blocker_val)) = slow_entry else {
                    break 'watch;
                };

                // Binary clause handling: the blocker IS the other literal.
                if watched::entry_is_binary(entry) {
                    let clause_ref = ClauseRef(watched::entry_clause_off(entry));
                    if blocker_val < 0 {
                        if IC3 {
                            // Immediate conflict return (#8569). Keep the
                            // current watcher and the unscanned suffix.
                            return Some(self.conflict_finalize(
                                false_lit,
                                clause_ref,
                                j + 1,
                                i,
                                watch_len,
                                qhead_start,
                                saved_bc,
                            ));
                        }
                        // Record and continue scanning binaries (#8043).
                        binary_conflict = Some(clause_ref);
                        j += 1;
                        continue;
                    }
                    // Unassigned (and in-domain) — propagate, keep watcher.
                    if !IC3 {
                        ticks += 1;
                    }
                    j += 1;
                    if IC3 {
                        self.enqueue_bcp_binary_ic3(Literal(blocker_raw), clause_ref);
                    } else if chrono {
                        self.enqueue_bcp_binary_with_other(
                            Literal(blocker_raw),
                            clause_ref,
                            false_lit,
                        );
                    } else {
                        self.enqueue_bcp_binary_nochrono(Literal(blocker_raw), clause_ref);
                    }
                    continue;
                }

                // SEARCH variant: stop at long clauses if a binary conflict
                // was already found (#8043).
                if !IC3 && binary_conflict.is_some() {
                    j += 1; // keep speculatively-copied watcher
                    break 'watch;
                }

                // Long clause: garbage check after the blocker shortcut.
                // Retained for IC3 (#8661): clause-DB reductions run
                // between IC3 queries, so watch lists can still hold
                // watchers of garbage-marked clauses. Drop the watcher.
                let off = watched::entry_clause_off(entry) as usize;
                let bcp_header = self.arena.bcp_header(off);
                if bcp_header.is_garbage_any() {
                    continue;
                }
                if !IC3 {
                    ticks += 1; // long clause cache-line access
                }
                let clause_ref = ClauseRef(watched::entry_clause_off(entry));
                let clause_len = bcp_header.clause_len();
                let cached_saved_pos = if IC3 { 0 } else { bcp_header.saved_pos() };

                // XOR trick for the other watched literal.
                let lit0 = self.arena.bcp_literal(off, 0);
                let lit1 = self.arena.bcp_literal(off, 1);
                debug_assert!(
                    lit0 == false_lit || lit1 == false_lit,
                    "BUG: watch list for {false_lit:?} contains clause {off} \
                     with watched lits {lit0:?}, {lit1:?} — neither matches"
                );
                let first = Literal(lit0.0 ^ lit1.0 ^ false_lit.0);
                let first_val = val_at(&self.vals, first.index());

                if first_val > 0 {
                    // Satisfied — update blocker to `first`, keep watcher.
                    bcp_set_kept_blocker(&mut self.deferred_watch_list, j, entry, first.0);
                    j += 1;
                    continue;
                }

                // Domain skip (#8475): unassigned out-of-domain other
                // watched literal — trivially satisfiable for the
                // restricted query; keep the watcher unmodified (no watch
                // move, no replacement scan). A FALSE out-of-domain other
                // watch is processed below exactly as in base BCP (#8661).
                if first_val == 0 && !domain_has_lit(domain, first.0) {
                    self.stats.domain_bcp_skips += 1;
                    j += 1;
                    continue;
                }

                let false_pos = usize::from(lit0 != false_lit);
                debug_assert!(clause_len > 2);

                // Replacement scan for a non-false literal. Sentinel
                // (replacement_k == clause_len) means "not found".
                let mut replacement_k: usize = clause_len;
                let mut replacement_val: i8 = -1;
                let mut replacement_lit = false_lit;
                macro_rules! try_replacement_slot {
                    ($k:expr) => {{
                        let lit_k = self.arena.bcp_literal(off, $k);
                        let v = val_at(&self.vals, lit_k.index());
                        if v >= 0 {
                            replacement_k = $k;
                            replacement_val = v;
                            replacement_lit = lit_k;
                            true
                        } else {
                            false
                        }
                    }};
                }
                if IC3 || clause_len <= 5 {
                    // Plain left-to-right scan from the first tail slot:
                    // the IC3 variant skips the saved-position machinery
                    // entirely (#8569); short clauses fit one cache line,
                    // so the base loop also starts them at slot 2.
                    for k in 2..clause_len {
                        if try_replacement_slot!(k) {
                            break;
                        }
                    }
                } else {
                    // Gent saved-position scan: [pos..len), then wrap
                    // around to [2..pos).
                    let mut pos = cached_saved_pos;
                    if pos < 2 || pos >= clause_len {
                        pos = 2;
                    }
                    for k in pos..clause_len {
                        if try_replacement_slot!(k) {
                            break;
                        }
                    }
                    if replacement_val < 0 {
                        for k in 2..pos {
                            if try_replacement_slot!(k) {
                                break;
                            }
                        }
                    }
                    // Update saved position only when a replacement was
                    // found and differs from the cached position (#8569).
                    if replacement_k < clause_len && replacement_k != cached_saved_pos {
                        self.arena.set_saved_pos(off, replacement_k);
                    }
                }

                if replacement_val > 0 {
                    // Replacement satisfied — replace the blocker only, no
                    // watch movement.
                    bcp_set_kept_blocker(
                        &mut self.deferred_watch_list,
                        j,
                        entry,
                        replacement_lit.0,
                    );
                    j += 1;
                    continue;
                } else if replacement_val == 0 {
                    // Unassigned replacement — move the watch from
                    // false_lit to the replacement literal (deferred).
                    debug_assert!(
                        replacement_k >= 2 && replacement_k < clause_len,
                        "BUG: replacement index {replacement_k} outside [2, {clause_len}) for clause {off}"
                    );
                    if !IC3 {
                        ticks += 1;
                    }
                    self.arena.swap_literals(off, false_pos, replacement_k);
                    self.deferred_replacement_watches
                        .push((replacement_lit, Watcher::new(clause_ref, first)));
                    continue; // drop this watcher (j stays)
                }

                // No replacement: every tail literal is false.
                debug_assert!(
                    (2..clause_len).all(|k| self.lit_val(self.arena.literal(off, k)) < 0),
                    "BUG: no-replacement path reached but a tail literal in clause {off} is not false"
                );
                if first_val < 0 {
                    // Conflict — both watched literals false.
                    if !IC3 {
                        self.flush_bcp_ticks::<{ bcp_mode::SEARCH }>(ticks);
                    }
                    return Some(self.conflict_finalize(
                        false_lit,
                        clause_ref,
                        j + 1,
                        i,
                        watch_len,
                        qhead_start,
                        saved_bc,
                    ));
                }

                // Unit propagation on the (in-domain) other watched literal.
                bcp_set_kept_blocker(&mut self.deferred_watch_list, j, entry, first.0);
                if !IC3 {
                    ticks += 1;
                }
                j += 1;
                if IC3 {
                    self.enqueue_bcp_ic3(first, clause_ref);
                } else if chrono {
                    self.enqueue_bcp::<true>(first, clause_ref);
                } else {
                    self.enqueue_bcp_nochrono(first, clause_ref);
                }
            }

            // Copy remaining unscanned watchers when breaking early due to
            // a binary conflict (#8043, SEARCH variant only).
            if !IC3 && binary_conflict.is_some() && i < watch_len {
                self.deferred_watch_list.copy_within(i, watch_len, j);
                j += watch_len - i;
            }

            debug_assert!(
                j <= watch_len,
                "BUG: propagate_domain_bcp_impl final j ({j}) > watch_len ({watch_len}) after compaction"
            );

            // Compaction never drops binary watchers, so the binary count
            // from copy_to_deferred is still valid.
            self.finalize_watch_list_with_bc(false_lit, j, saved_bc);

            // Flush deferred replacement watches (#8041).
            if !self.deferred_replacement_watches.is_empty() {
                for &(lit, watcher) in &self.deferred_replacement_watches {
                    self.watches.add_watch(lit, watcher);
                }
                self.deferred_replacement_watches.clear();
            }

            if !IC3 {
                if let Some(conflict_ref) = binary_conflict {
                    self.flush_bcp_ticks::<{ bcp_mode::SEARCH }>(ticks);
                    return Some(self.binary_conflict_finalize(conflict_ref, qhead_start));
                }
            }
        }

        self.num_propagations += (self.qhead - qhead_start) as u64;
        if !IC3 {
            self.flush_bcp_ticks::<{ bcp_mode::SEARCH }>(ticks);
        }
        self.no_conflict_until = self.trail.len();
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: propagate_domain_bcp_impl completed but qhead ({}) != trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );
        None
    }

    /// Domain-restricted BCP stripped for IC3/PDR incremental queries
    /// (#8569), `raw-pointer-bcp` build: iterates each watch list in place
    /// through raw pointers (no deferred copy/restore).
    ///
    /// Same restricted-propagation semantics as
    /// [`Solver::propagate_domain_bcp`] (two-watched-literal scheme per
    /// Een & Sorensson, SAT 2003, restricted to a cone-of-influence domain
    /// per arXiv:2502.13605 §3; unassigned out-of-domain watched literals
    /// skip their watcher, counted in `stats.domain_bcp_skips`), with the
    /// SEARCH amenities removed for thousands of short queries: no tick
    /// accounting, no saved-position scanning, no prefetch, no telemetry
    /// or logging, immediate return on ANY conflict (including binary),
    /// and the IC3-stripped enqueue helpers (`enqueue_bcp_ic3` /
    /// `enqueue_bcp_binary_ic3` — no chronological backtracking, no phase
    /// saving). The clause garbage-bit check is retained: clause-DB
    /// reductions run between IC3 queries, so watch lists can still hold
    /// watchers of garbage-marked clauses (#8661).
    ///
    /// REQUIRES: cold.ic3_mode, chrono_enabled == false,
    ///           decision_level > 0, !has_empty_clause,
    ///           qhead <= trail.len(), `domain` closed under clause
    ///           co-occurrence (COI closure, see `expand_domain_bcp`)
    /// ENSURES: semantically identical to the non-`raw-pointer-bcp` fallback:
    ///          if None, qhead == trail.len(), only domain variables were
    ///          newly assigned, and the trail matches full BCP restricted
    ///          to domain decisions; if Some(cref), both watched literals
    ///          of cref are false, qhead is frozen, and the unprocessed
    ///          watch suffix is retained; watch lists stay consistent and
    ///          deferred replacement watches are flushed
    #[cfg(feature = "raw-pointer-bcp")]
    #[allow(unsafe_code)]
    pub(super) fn propagate_bcp_ic3(&mut self, domain: &[bool]) -> Option<ClauseRef> {
        debug_assert!(
            self.decision_level > 0,
            "BUG: propagate_bcp_ic3 called at level 0 — level 0 must use full BCP"
        );
        debug_assert!(
            !self.has_empty_clause,
            "BUG: propagate_bcp_ic3 called with has_empty_clause=true"
        );
        debug_assert!(
            self.qhead <= self.trail.len(),
            "BUG: propagate_bcp_ic3 entry qhead ({}) > trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );
        debug_assert!(
            self.cold.ic3_mode,
            "BUG: propagate_bcp_ic3 called without ic3_mode"
        );
        debug_assert!(
            !self.chrono_enabled,
            "BUG: propagate_bcp_ic3 requires chronological backtracking disabled"
        );
        self.last_conflict_clause_ref = None;
        self.last_conflict_clause_id = 0;
        self.stats.domain_bcp_calls += 1;
        let qhead_start = self.qhead;

        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            let false_lit = p.negated();

            // In-place iteration (#8569): raw pointer into the packed-entry
            // region; `i` is the read cursor, `j` the compaction write
            // cursor for the long suffix. The binary-first invariant lets
            // the scan split at `binary_count`.
            let binary_count = self.watches.binary_count_of(false_lit);
            let (entries_ptr, watch_len) =
                self.watches.get_watches_mut(false_lit).entries_raw_mut();
            debug_assert!(
                binary_count <= watch_len,
                "BUG: propagate_bcp_ic3 binary_count ({binary_count}) > watch_len ({watch_len})"
            );
            // SAFETY (pointer scope for the whole watch scan): entries_ptr
            // covers `watch_len` contiguous u64 entries. The loops maintain
            // j <= i <= watch_len, so all reads at .add(i) and writes at
            // .add(j) stay in bounds. Nothing below resizes the watch
            // buffer during iteration: replacement watches are deferred
            // (flushed after the scan, or by the conflict finalizer after
            // the list is truncated) and the IC3 enqueue helpers never
            // touch watch lists.
            let end = watch_len;
            let mut i: usize = 0;

            // Binary prefix [0..binary_count): binary watchers are never
            // dropped or moved, so no compaction happens here and an
            // immediate conflict return leaves the list untouched.
            while i < binary_count {
                // SAFETY: i < binary_count <= watch_len.
                let entry = unsafe { *entries_ptr.add(i) };
                i += 1;
                let blocker_raw = watched::entry_blocker_raw(entry);
                let blocker_val = val_at(&self.vals, blocker_raw as usize);
                if blocker_val > 0 {
                    continue;
                }
                debug_assert!(
                    watched::entry_is_binary(entry),
                    "BUG: binary prefix entry {} is not binary",
                    i - 1
                );
                // Domain skip (#8475): an unassigned watched literal over a
                // non-domain variable cannot be falsified by the restricted
                // query (domain closure invariant) — keep the watcher, no
                // propagation, no conflict. A FALSE out-of-domain literal
                // (root-level unit) takes normal conflict handling (#8661).
                if blocker_val == 0 && !domain_has_lit(domain, blocker_raw) {
                    self.stats.domain_bcp_skips += 1;
                    continue;
                }
                let clause_ref = ClauseRef(watched::entry_clause_off(entry));
                if blocker_val < 0 {
                    // Immediate conflict return (#8569): the prefix is
                    // untouched, so no truncation is needed.
                    return Some(self.unsafe_conflict_finalize(clause_ref, qhead_start));
                }
                self.enqueue_bcp_binary_ic3(Literal(blocker_raw), clause_ref);
            }

            // Long suffix [binary_count..watch_len) with in-place
            // compaction.
            let mut j: usize = binary_count;
            'watch: while i < end {
                // Speculative keep: copy the entry to the compaction slot
                // unconditionally; drop paths simply do not advance j.
                // SAFETY: i < end = watch_len and j <= i.
                let entry = unsafe { *entries_ptr.add(i) };
                unsafe { *entries_ptr.add(j) = entry };
                i += 1;
                debug_assert!(
                    !watched::entry_is_binary(entry),
                    "BUG: long suffix entry {} is binary",
                    i - 1
                );
                let blocker_raw = watched::entry_blocker_raw(entry);
                let blocker_val = val_at(&self.vals, blocker_raw as usize);
                if blocker_val > 0 {
                    j += 1;
                    continue 'watch;
                }
                // Domain skip (#8475): see the binary prefix note — for
                // long clauses this covers the cached blocker without
                // touching the arena.
                if blocker_val == 0 && !domain_has_lit(domain, blocker_raw) {
                    self.stats.domain_bcp_skips += 1;
                    j += 1;
                    continue 'watch;
                }
                // Garbage-bit check retained for IC3 (#8661): clause-DB
                // reductions between queries can leave garbage-marked
                // clauses in watch lists. Drop the watcher.
                let off = watched::entry_clause_off(entry) as usize;
                let bcp_header = self.arena.bcp_header(off);
                if bcp_header.is_garbage_any() {
                    continue 'watch;
                }
                let clause_ref = ClauseRef(watched::entry_clause_off(entry));
                let clause_len = bcp_header.clause_len();

                // XOR trick for the other watched literal.
                let lit0 = self.arena.bcp_literal(off, 0);
                let lit1 = self.arena.bcp_literal(off, 1);
                debug_assert!(
                    lit0 == false_lit || lit1 == false_lit,
                    "BUG: watch list for {false_lit:?} contains clause {off} \
                     with watched lits {lit0:?}, {lit1:?} — neither matches"
                );
                let first = Literal(lit0.0 ^ lit1.0 ^ false_lit.0);
                let first_val = val_at(&self.vals, first.index());
                if first_val > 0 {
                    // Satisfied — refresh the blocker, keep the watcher.
                    // SAFETY: j <= i - 1 < end.
                    unsafe { *entries_ptr.add(j) = watched::entry_with_blocker(entry, first.0) };
                    j += 1;
                    continue 'watch;
                }
                // Domain skip (#8475): unassigned out-of-domain other
                // watched literal — trivially satisfiable for the
                // restricted query; keep the watcher unmodified. A FALSE
                // out-of-domain other watch is processed below exactly as
                // in base BCP (#8661).
                if first_val == 0 && !domain_has_lit(domain, first.0) {
                    self.stats.domain_bcp_skips += 1;
                    j += 1;
                    continue 'watch;
                }
                let false_pos = usize::from(lit0 != false_lit);
                debug_assert!(clause_len > 2);

                // Replacement scan: plain left-to-right, no saved position
                // (#8569).
                let mut replacement_k: usize = clause_len; // sentinel
                let mut replacement_val: i8 = -1;
                let mut replacement_lit = false_lit;
                for k in 2..clause_len {
                    let lit_k = self.arena.bcp_literal(off, k);
                    let v = val_at(&self.vals, lit_k.index());
                    if v >= 0 {
                        replacement_k = k;
                        replacement_val = v;
                        replacement_lit = lit_k;
                        break;
                    }
                }
                if replacement_val > 0 {
                    // Replacement satisfied — blocker refresh only, no
                    // watch movement.
                    // SAFETY: j <= i - 1 < end.
                    unsafe {
                        *entries_ptr.add(j) = watched::entry_with_blocker(entry, replacement_lit.0);
                    }
                    j += 1;
                    continue 'watch;
                } else if replacement_val == 0 {
                    // Unassigned replacement — move the watch (deferred),
                    // drop this watcher (j stays).
                    debug_assert!(
                        replacement_k >= 2 && replacement_k < clause_len,
                        "BUG: replacement index {replacement_k} outside [2, {clause_len}) for clause {off}"
                    );
                    self.arena.swap_literals(off, false_pos, replacement_k);
                    self.deferred_replacement_watches
                        .push((replacement_lit, Watcher::new(clause_ref, first)));
                    continue 'watch;
                }

                // No replacement: every tail literal is false.
                if first_val < 0 {
                    // Conflict — keep the current watcher, retain the
                    // unscanned suffix, truncate, and return immediately.
                    j += 1;
                    if i < end {
                        // SAFETY: source [i..end) and destination
                        // [j..j + (end - i)) both lie inside the entry
                        // region (j <= i); the ranges may overlap, so use
                        // ptr::copy.
                        unsafe {
                            std::ptr::copy(entries_ptr.add(i), entries_ptr.add(j), end - i);
                        }
                        j += end - i;
                    }
                    if j != end {
                        // SAFETY: j <= end and entries [0, j) are the
                        // compacted live watchers.
                        unsafe { self.watches.set_len_after_bcp_compaction(false_lit, j) };
                    }
                    return Some(self.unsafe_conflict_finalize(clause_ref, qhead_start));
                }

                // Unit propagation on the (in-domain) other watched
                // literal.
                // SAFETY: j <= i - 1 < end.
                unsafe { *entries_ptr.add(j) = watched::entry_with_blocker(entry, first.0) };
                j += 1;
                self.enqueue_bcp_ic3(first, clause_ref);
            }

            debug_assert!(
                j <= watch_len,
                "BUG: propagate_bcp_ic3 final j ({j}) > watch_len ({watch_len}) after compaction"
            );
            if j != watch_len {
                // SAFETY: j <= watch_len and entries [0, j) are the
                // compacted live watchers.
                unsafe { self.watches.set_len_after_bcp_compaction(false_lit, j) };
            }

            // Flush deferred replacement watches (#8041).
            if !self.deferred_replacement_watches.is_empty() {
                for &(lit, watcher) in &self.deferred_replacement_watches {
                    self.watches.add_watch(lit, watcher);
                }
                self.deferred_replacement_watches.clear();
            }
        }

        self.num_propagations += (self.qhead - qhead_start) as u64;
        self.no_conflict_until = self.trail.len();
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: propagate_bcp_ic3 completed but qhead ({}) != trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );
        None
    }

    /// Domain-restricted BCP stripped for IC3/PDR incremental queries
    /// (#8569), no-`raw-pointer-bcp` fallback build.
    ///
    /// Semantically identical to the `raw-pointer-bcp` variant above, but
    /// iterates watch lists through the safe deferred copy/restore pattern
    /// instead of raw pointers. See [`Solver::propagate_domain_bcp`] for
    /// the restricted-propagation semantics (Een & Sorensson, SAT 2003;
    /// arXiv:2502.13605 §3) and
    /// [`Solver::propagate_domain_bcp_impl`] for the stripped IC3
    /// instantiation (#8475, #8661).
    ///
    /// REQUIRES / ENSURES: as the `raw-pointer-bcp` variant.
    #[cfg(not(feature = "raw-pointer-bcp"))]
    #[inline]
    pub(super) fn propagate_bcp_ic3(&mut self, domain: &[bool]) -> Option<ClauseRef> {
        self.propagate_domain_bcp_impl::<true>(domain)
    }
}

/// Domain-membership test for a watched literal (#8475).
///
/// `domain` is indexed by variable. A variable at or beyond the bitmap
/// length counts as outside the domain: the bitmap is sized to `num_vars`
/// at `set_domain` time, so variables created afterwards (incremental use)
/// and stale watch entries referencing since-compacted variables are
/// conservatively treated as non-domain.
#[inline(always)]
fn domain_has_lit(domain: &[bool], lit_raw: u32) -> bool {
    let var = Literal(lit_raw).variable().index();
    var < domain.len() && domain[var]
}
