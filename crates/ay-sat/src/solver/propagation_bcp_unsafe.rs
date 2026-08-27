// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CaDiCaL-exact unsafe BCP (Boolean Constraint Propagation) using raw pointers.
//!
//! This module implements the SEARCH and VIVIFY variants of the same BCP
//! algorithm as `propagation_bcp.rs`, but uses raw pointer arithmetic for watch
//! list iteration and literal/val access, matching CaDiCaL's
//! `propagate.cpp:226-498` pattern exactly.
//!
//! Key differences from the safe version:
//! - In-place pointer iteration on the watch list (no deferred swap buffer)
//! - Raw `*const i8` for vals lookups (no bounds checks)
//! - Raw `*const u32` for arena literal access (no bounds checks)
//! - Prefetch after each enqueue
//!
//! Interleaved AoS layout (#9773): watch entries are packed 8-byte words
//! (blocker + binary flag in the low half, clause offset in the high half).
//! ONE load from entries_ptr serves both the blocker fast-path check and,
//! on a blocker miss, the clause reference — no second dependent stream.
//! 8 entries fit per 64-byte cache line.
//!
//! # Safety
//!
//! All unsafe operations rely on the same invariants as the safe BCP:
//! - `Literal::index() < vals.len()` (2 * num_vars)
//! - Watch list entries reference valid clause offsets in the arena
//! - Clause offsets + HEADER_WORDS + literal_index < arena.words.len()
//! - The compaction invariant `j <= i <= end` holds throughout iteration
//!
//! Reference: CaDiCaL `src/propagate.cpp:226-498` (Armin Biere, MIT license).

// Allow unsafe in this module — the entire point is raw pointer BCP.
#![allow(unsafe_code)]
// Same as safe BCP: range loops needed for swap_literals calls.
#![allow(clippy::needless_range_loop)]

use super::*;
use crate::clause_arena::HEADER_WORDS;
use crate::solver::propagation::bcp_mode;
use crate::solver::solver_stats::BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS;
use crate::solver_log::solver_log;
use crate::watched::{entry_blocker_raw, entry_clause_off, entry_is_binary, entry_with_blocker};

#[derive(Default)]
struct Learned1963BlockerCertProbe {
    replacement: Option<(usize, u32, i8)>,
    shadow_probe: Option<(usize, u32)>,
    profile_scan_steps: u64,
    elided_scan: bool,
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
    /// Search-mode CaDiCaL-exact BCP using raw pointer iteration.
    #[inline]
    pub(super) fn propagate_bcp_unsafe_search(&mut self) -> Option<ClauseRef> {
        self.propagate_bcp_unsafe::<{ bcp_mode::SEARCH }>()
    }

    /// Vivification-mode CaDiCaL-exact BCP using raw pointer iteration.
    #[inline]
    pub(super) fn propagate_bcp_unsafe_vivify(&mut self) -> Option<ClauseRef> {
        self.propagate_bcp_unsafe::<{ bcp_mode::VIVIFY }>()
    }

    #[cold]
    #[inline(never)]
    fn probe_learned_1963_blocker_cert_unsafe(
        &mut self,
        off: usize,
        clause_len: usize,
        clause_is_learned: bool,
        normalized_saved_pos: usize,
        known_false_saved_start: usize,
        words_ptr: *const u32,
        vals_ptr: *const i8,
        lits_base: usize,
        collect_bcp_telemetry: bool,
        profile_scan_or_identity: bool,
        shadow: bool,
        demote_false_reject: bool,
    ) -> Learned1963BlockerCertProbe {
        let mut probe = Learned1963BlockerCertProbe::default();
        let Some(cert) = self.stats.bcp_learned_1963_blocker_cert(off) else {
            return probe;
        };

        self.stats.record_bcp_learned_1963_blocker_cert_candidate();
        let cert_pos = cert.position;
        let cert_stale = cert.clause_offset != off
            || off >= self.arena.len()
            || !clause_is_learned
            || !(19..=63).contains(&clause_len)
            || cert_pos < 2
            || cert_pos >= clause_len
            || cert_pos >= normalized_saved_pos;
        if cert_stale {
            self.stats
                .record_bcp_learned_1963_blocker_cert_stale_reject();
            self.stats.clear_bcp_learned_1963_blocker_cert(off);
            return probe;
        }

        // SAFETY: the caller validated the clause extent
        // (off + HEADER_WORDS + clause_len <= words_len) before calling, and
        // the cert_stale check above guarantees 2 <= cert_pos < clause_len,
        // so lits_base + cert_pos is within the clause's literal words.
        let cert_lit_raw = unsafe { *words_ptr.add(lits_base + cert_pos) };
        if cert_lit_raw != cert.literal_raw {
            self.stats
                .record_bcp_learned_1963_blocker_cert_stale_reject();
            self.stats.clear_bcp_learned_1963_blocker_cert(off);
            return probe;
        }
        if cert.repeat_count < BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS {
            self.stats
                .record_bcp_learned_1963_blocker_cert_repeat_reject();
            return probe;
        }

        // SAFETY: cert_lit_raw was just verified to equal the clause literal
        // at cert_pos, and clause literals are valid Literal indices
        // (< 2 * num_vars == vals.len()) by construction.
        let cert_val = unsafe { *vals_ptr.add(cert_lit_raw as usize) };
        if cert_val <= 0 {
            self.stats
                .record_bcp_learned_1963_blocker_cert_false_reject();
            if demote_false_reject {
                self.stats.clear_bcp_learned_1963_blocker_cert(off);
                self.stats
                    .record_bcp_learned_1963_blocker_cert_false_reject_demotion();
            }
            return probe;
        }

        let elided_suffix_slots = if known_false_saved_start < clause_len {
            (known_false_saved_start.saturating_sub(cert_pos + 1)
                + clause_len.saturating_sub(known_false_saved_start + 1)) as u64
        } else {
            normalized_saved_pos.saturating_sub(cert_pos + 1) as u64
        };

        if shadow {
            probe.shadow_probe = Some((cert_pos, cert_lit_raw));
            self.stats.record_bcp_learned_1963_blocker_cert_shadow_hit(
                elided_suffix_slots,
                cert.fsw_seed,
            );
            return probe;
        }

        macro_rules! record_cert_prefix_scan_step {
            () => {{
                if collect_bcp_telemetry {
                    self.stats
                        .record_bcp_replacement_scan_step(clause_len, clause_is_learned);
                }
                if profile_scan_or_identity {
                    probe.profile_scan_steps += 1;
                }
            }};
        }

        macro_rules! cert_prefix_slot_is_false {
            ($k:expr, $next_limit:expr) => {{
                record_cert_prefix_scan_step!();
                // SAFETY: every $k passed here is < $next_limit <= clause_len,
                // and the caller validated the clause extent
                // (off + HEADER_WORDS + clause_len <= words_len), so the read
                // is within the clause's literal words.
                let lit_k_raw = unsafe { *words_ptr.add(lits_base + $k) };
                if $k + 1 < $next_limit {
                    // SAFETY: guarded by $k + 1 < $next_limit <= clause_len,
                    // within the validated clause extent.
                    let next_lit_raw = unsafe { *words_ptr.add(lits_base + $k + 1) };
                    // SAFETY: next_lit_raw is a clause literal, a valid index
                    // < vals.len(); the pointer is only passed to prefetch,
                    // never dereferenced.
                    ay_prefetch::prefetch_read_l1(unsafe { vals_ptr.add(next_lit_raw as usize) });
                }
                // SAFETY: lit_k_raw is a clause literal, hence a valid Literal
                // index < 2 * num_vars == vals.len() by construction.
                (unsafe { *vals_ptr.add(lit_k_raw as usize) }) < 0
            }};
        }

        let mut cert_matches_normal_prefix = true;
        if known_false_saved_start < clause_len {
            for k in 2..cert_pos {
                if !cert_prefix_slot_is_false!(k, known_false_saved_start) {
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
                    if !cert_prefix_slot_is_false!(k, cert_pos) {
                        cert_matches_normal_prefix = false;
                        break;
                    }
                }
            }
        }

        if cert_matches_normal_prefix {
            record_cert_prefix_scan_step!();
            probe.replacement = Some((cert_pos, cert_lit_raw, cert_val));
            probe.elided_scan = true;
            self.stats
                .record_bcp_learned_1963_blocker_cert_elision(elided_suffix_slots, cert.fsw_seed);
        } else {
            self.stats
                .record_bcp_learned_1963_blocker_cert_shadow_mismatch();
            if demote_false_reject {
                self.stats
                    .record_bcp_learned_1963_blocker_cert_mismatch_demotion();
                self.stats.clear_bcp_learned_1963_blocker_cert(off);
            }
        }

        probe
    }

    /// CaDiCaL-exact SEARCH/VIVIFY BCP using raw pointer iteration
    /// (interleaved 8-byte AoS entries, #9773).
    ///
    /// Semantically identical to `propagate_bcp::<MODE>()` but uses unsafe
    /// raw pointer arithmetic for the inner watch scan, val lookups, and
    /// arena literal access. This eliminates bounds checks and enables
    /// the compiler to keep hot pointers in registers throughout the loop.
    ///
    /// With the packed AoS layout, the hot inner loop reads ONE stream
    /// (`entries_ptr`, u64 array; 8 entries per 64-byte cache line). Each
    /// entry load serves both the blocker fast-path check and — on a blocker
    /// miss — the clause reference, removing the second dependent load
    /// stream that made the SoA layout backend-bound.
    ///
    /// REQUIRES: qhead <= trail.len(), watches initialized for all clauses
    /// ENSURES: if None returned, qhead == trail.len() (all propagated);
    ///          if Some(cref), conflicting clause identified, qhead frozen
    #[inline]
    fn propagate_bcp_unsafe<const MODE: u8>(&mut self) -> Option<ClauseRef> {
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

        macro_rules! dispatch_bcp_unsafe_impl {
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
                        .propagate_bcp_unsafe_impl::<MODE, true, true, true, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (true, true, true, false) => self
                        .propagate_bcp_unsafe_impl::<MODE, true, true, false, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (true, true, false, true) => self
                        .propagate_bcp_unsafe_impl::<MODE, true, false, true, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (true, true, false, false) => self
                        .propagate_bcp_unsafe_impl::<MODE, true, false, false, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (true, false, true, true) => self
                        .propagate_bcp_unsafe_impl::<MODE, false, true, true, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (true, false, true, false) => self
                        .propagate_bcp_unsafe_impl::<MODE, false, true, false, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (true, false, false, true) => self
                        .propagate_bcp_unsafe_impl::<MODE, false, false, true, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (true, false, false, false) => self
                        .propagate_bcp_unsafe_impl::<MODE, false, false, false, true, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (false, true, true, true) => self
                        .propagate_bcp_unsafe_impl::<MODE, true, true, true, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (false, true, true, false) => self
                        .propagate_bcp_unsafe_impl::<MODE, true, true, false, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (false, true, false, true) => self
                        .propagate_bcp_unsafe_impl::<MODE, true, false, true, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (false, true, false, false) => self
                        .propagate_bcp_unsafe_impl::<MODE, true, false, false, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (false, false, true, true) => self
                        .propagate_bcp_unsafe_impl::<MODE, false, true, true, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (false, false, true, false) => self
                        .propagate_bcp_unsafe_impl::<MODE, false, true, false, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (false, false, false, true) => self
                        .propagate_bcp_unsafe_impl::<MODE, false, false, true, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                    (false, false, false, false) => self
                        .propagate_bcp_unsafe_impl::<MODE, false, false, false, false, $reset_learned_1963_false_saved_pos, $relocate_learned_1963_true_tail, $learned_1963_fsw_gent_skip, false, false>(),
                }
            };
        }

        // Lean route (#bcp-lean): one dense instantiation with every
        // experiment const false (including the short-clause specialization
        // and jump reasons), env-gated via AY_SAT_BCP_LEAN. Checked before
        // the HOT route so the explicit env override keeps priority.
        if MODE == bcp_mode::SEARCH && self.cold.bcp_lean_route_enabled {
            return self
                .propagate_bcp_unsafe_impl::<MODE, false, false, false, false, false, false, false, true, false>();
        }

        // HOT route (#shave5): production fast path. When every default-off
        // BCP experiment knob is off (the overwhelmingly common case:
        // release builds without BCP telemetry or experiments), dispatch to
        // an instantiation whose HOT const compiles the runtime experiment
        // flags out of the watch scan. Bit-identical to the all-false
        // dispatch arm below: HOT only constant-folds branches whose
        // controlling flags are verified false right here, so the executed
        // path is unchanged. Search-visible runtime features (jump reasons,
        // ChrBT) stay runtime-dispatched inside the impl.
        if !collect_bcp_telemetry
            && !advance_saved_pos
            && !defer_saved_pos_extraction
            && !reset_len18_false_saved_pos
            && !reset_learned_1963_false_saved_pos
            && !relocate_learned_1963_true_tail
            && !learned_1963_fsw_gent_skip
            && !bcp_len68_replacement_scan_enabled()
            && !(MODE == bcp_mode::SEARCH
                && (self.cold.bcp_learned_618_true_tail_relocation
                    || self.cold.bcp_learned_no_replacement_saved_pos_update
                    || self
                        .cold
                        .bcp_disable_learned_1963_no_replacement_unit_blocker_refresh
                    || self.cold.bcp_learned_1963_used5_fsw_saved_pos_reset
                    || self.cold.bcp_learned_1963_fsw_conflict_saved_pos_reset
                    || self.bcp_learned_1963_blocker_cert_elision_enabled_internal()
                    || self.bcp_learned_1963_blocker_cert_shadow_enabled_internal()))
        {
            return self
                .propagate_bcp_unsafe_impl::<MODE, false, false, false, false, false, false, false, false, true>();
        }

        match (
            reset_learned_1963_false_saved_pos,
            relocate_learned_1963_true_tail,
            learned_1963_fsw_gent_skip,
        ) {
            (true, true, true) => dispatch_bcp_unsafe_impl!(true, true, true),
            (true, true, false) => dispatch_bcp_unsafe_impl!(true, true, false),
            (true, false, true) => dispatch_bcp_unsafe_impl!(true, false, true),
            (true, false, false) => dispatch_bcp_unsafe_impl!(true, false, false),
            (false, true, true) => dispatch_bcp_unsafe_impl!(false, true, true),
            (false, true, false) => dispatch_bcp_unsafe_impl!(false, true, false),
            (false, false, true) => dispatch_bcp_unsafe_impl!(false, false, true),
            (false, false, false) => dispatch_bcp_unsafe_impl!(false, false, false),
        }
    }

    #[inline]
    fn propagate_bcp_unsafe_impl<
        const MODE: u8,
        const COLLECT_BCP_TELEMETRY: bool,
        const ADVANCE_SAVED_POS_AFTER_UNASSIGNED_MOVE: bool,
        const DEFER_SAVED_POS_EXTRACTION: bool,
        const RESET_LEN18_FALSE_SAVED_POS: bool,
        const RESET_LEARNED_1963_FALSE_SAVED_POS: bool,
        const RELOCATE_LEARNED_1963_TRUE_TAIL: bool,
        const LEARNED_1963_FSW_GENT_SKIP: bool,
        const LEAN: bool,
        const HOT: bool,
    >(
        &mut self,
    ) -> Option<ClauseRef> {
        debug_assert!(
            !self.has_empty_clause,
            "BUG: propagate_bcp_unsafe called with has_empty_clause=true"
        );
        debug_assert!(
            MODE == bcp_mode::SEARCH || MODE == bcp_mode::VIVIFY,
            "BUG: unsafe BCP only supports SEARCH/VIVIFY modes"
        );
        debug_assert!(
            !self.probing_mode,
            "BUG: propagate_bcp_unsafe called in probing mode"
        );
        self.last_conflict_clause_ref = None;
        self.last_conflict_clause_id = 0;
        let qhead_start = self.qhead;
        // HOT gating (#shave5): every default-off experiment flag below is
        // verified false by the dispatch before selecting the HOT
        // instantiation, so `!HOT &&` constant-folds the flag loads and all
        // downstream per-visit tests out of the hot watch scan without
        // changing the executed path.
        let specialize_len68_replacement_scan =
            !HOT && !LEAN && bcp_len68_replacement_scan_enabled();
        let relocate_learned_618_true_tail = !HOT
            && !LEAN
            && MODE == bcp_mode::SEARCH
            && self.cold.bcp_learned_618_true_tail_relocation;
        let update_learned_no_replacement_saved_pos = !HOT
            && !LEAN
            && MODE == bcp_mode::SEARCH
            && self.cold.bcp_learned_no_replacement_saved_pos_update;
        let disable_learned_1963_no_replacement_unit_blocker_refresh = !HOT
            && !LEAN
            && MODE == bcp_mode::SEARCH
            && self
                .cold
                .bcp_disable_learned_1963_no_replacement_unit_blocker_refresh;
        let profile_learned_no_replacement_scan_pressure = COLLECT_BCP_TELEMETRY
            && MODE == bcp_mode::SEARCH
            && self.cold.bcp_learned_no_replacement_scan_pressure;
        let profile_learned_1963_identity = COLLECT_BCP_TELEMETRY
            && MODE == bcp_mode::SEARCH
            && self.cold.bcp_learned_1963_identity_profile;
        let reset_learned_1963_used5_fsw_saved_pos = !HOT
            && !LEAN
            && MODE == bcp_mode::SEARCH
            && self.cold.bcp_learned_1963_used5_fsw_saved_pos_reset;
        let reset_learned_1963_fsw_conflict_saved_pos = !HOT
            && !LEAN
            && MODE == bcp_mode::SEARCH
            && self.cold.bcp_learned_1963_fsw_conflict_saved_pos_reset;
        let learned_1963_fsw_gent_skip = MODE == bcp_mode::SEARCH && LEARNED_1963_FSW_GENT_SKIP;
        let elide_learned_1963_blocker_cert = !HOT
            && !LEAN
            && MODE == bcp_mode::SEARCH
            && self.bcp_learned_1963_blocker_cert_elision_enabled_internal();
        let shadow_learned_1963_blocker_cert = !HOT
            && !LEAN
            && MODE == bcp_mode::SEARCH
            && !elide_learned_1963_blocker_cert
            && self.bcp_learned_1963_blocker_cert_shadow_enabled_internal();
        // The false-reject demotion flag is only read on cert-elision /
        // cert-shadow paths, which are HOT-gated above, so HOT can force it
        // false without a dispatch-side eligibility check.
        let demote_learned_1963_blocker_cert_false_reject = !HOT
            && !LEAN
            && MODE == bcp_mode::SEARCH
            && self.bcp_learned_1963_blocker_cert_false_reject_demote_enabled_internal();
        let mut ticks: u64 = 0;
        // Cache ChrBT flag once for the entire propagation loop (#8465).
        // This avoids re-reading the field on every enqueue call and lets us
        // dispatch to the stripped-down nochrono enqueue variants which skip
        // the O(clause_len) assignment_level scan + lifecycle checks.
        let chrono = self.chrono_enabled;
        let trail_lookahead_prefetch = self.cold.bcp_trail_lookahead_prefetch;
        // Jump-reasons gate hoist (#shave5): `decision_level` and the cold
        // flag are invariant for the whole propagate call (BCP never opens a
        // decision level), so evaluate the enqueue-route predicate once here
        // instead of re-loading `self.cold.jump_reasons_enabled` and
        // `self.decision_level` on every binary propagation.
        let jump_reasons = !LEAN
            && MODE == bcp_mode::SEARCH
            && self.cold.jump_reasons_enabled
            && self.decision_level > 0;

        debug_assert!(
            self.qhead <= self.trail.len(),
            "BUG: propagate_bcp_unsafe entry qhead ({}) > trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );

        // Verify vals[] is correctly sized for num_vars (#8359). After
        // compaction truncates vals to 2*new_num_vars, any raw pointer
        // dereference of vals_ptr.add(literal_index) with literal_index >=
        // 2*num_vars would be UB. This assertion catches the case where
        // compaction reduced num_vars but vals wasn't properly truncated.
        debug_assert!(
            self.vals.len() >= self.num_vars * 2,
            "BUG: vals[] length {} < 2*num_vars {} — compaction truncation error? (#8359)",
            self.vals.len(),
            self.num_vars * 2,
        );

        // Cache raw pointers for vals and arena words outside the outer loop.
        //
        // SAFETY (pointer stability): vals and arena.words() are Vec-backed
        // slices owned by self. No reallocation occurs during BCP: no new
        // variables are added (vals doesn't grow), no new clauses are
        // allocated (arena doesn't grow), and the deferred_replacement_watches
        // pattern avoids watch list mutation during the inner loop. The
        // pointers remain valid for the entire duration of this function.
        let vals_ptr: *const i8 = self.vals.as_ptr();
        let words_ptr: *const u32 = self.arena.words().as_ptr();
        // Cache arena and vals lengths for bounds validation (#9301).
        // words_len is used in release builds for clause-level bounds checks
        // (header check + clause-extent check). vals_len is used only in
        // debug_assert! but must remain in scope since debug_assert! macro
        // expansion preserves name references even when the assertion body
        // is compiled out. The cost is zero (one usize read at function entry).
        let words_len: usize = self.arena.words().len();
        let vals_len: usize = self.vals.len();

        // Vals-prefetch gate (#shave6): the per-entry lookahead-entry load +
        // L1 prefetch of vals[next blocker] pays only when vals[] is too big
        // to sit in L1. On small-var instances (protein-class MaxSAT parts:
        // 2436 vars = 4.9KB vals) the pair is pure overhead — ~3 instructions
        // on the ~8-instruction dominant blocker-hit path — and neither
        // kissat nor CaDiCaL prefetches vals per watcher. Hoisted bool: one
        // perfectly-predicted test+branch per entry replaces a load + address
        // arithmetic + prefetch. 32KB is conservative for every target L1d.
        const VALS_PREFETCH_L1_RESIDENT_BYTES: usize = 32 * 1024;
        let prefetch_vals = vals_len > VALS_PREFETCH_L1_RESIDENT_BYTES;

        // #shave7: establish trail.capacity() >= num_vars so the enqueue
        // family may use the unchecked trail push (assign_bcp_unchecked).
        self.reserve_trail_for_bcp();

        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            // Verify trail literal is within bounds before raw pointer
            // dereferences in the watch scan loop (#8359).
            debug_assert!(
                p.variable().index() < self.num_vars,
                "BUG: trail[{}] variable index {} >= num_vars {} — stale trail entry \
                 after compaction? (#8359)",
                self.qhead - 1,
                p.variable().index(),
                self.num_vars,
            );
            let false_lit = p.negated();

            // Lookahead prefetch (#8465): prefetch the NEXT trail literal's
            // watch list data while we process the current literal. This hides
            // the latency of the meta[] lookup + buffer base pointer computation
            // that happens at the top of the next outer-loop iteration.
            // CaDiCaL propagate.cpp:160-166 pattern.
            if trail_lookahead_prefetch && self.qhead < self.trail.len() {
                let next_p = self.trail[self.qhead];
                self.watches.prefetch_first(next_p.negated());
            }

            // Interleaved AoS pattern (#9773): get a raw pointer into the
            // packed-entry array for in-place iteration. `i` is the read
            // pointer, `j` is the write pointer (compaction). Both start at
            // the beginning.
            let (entries_ptr, watch_len, binary_count) = self
                .watches
                .get_watches_mut(false_lit)
                .entries_raw_mut_with_bc();
            // SAFETY (pointer scope for entire watch loop): entries_ptr points
            // to `watch_len` contiguous u64 packed entries in the watch list's
            // unified buffer. The compaction loop maintains j <= i < end =
            // watch_len, so all reads at .add(i) and writes at .add(j) are in
            // bounds. The array is not resized during iteration (replacement
            // watches are deferred and flushed after the loop).
            debug_assert!(
                binary_count <= watch_len,
                "BCP unsafe: binary_count ({binary_count}) > watch_len ({watch_len})"
            );
            let end = watch_len;
            let mut i: usize = 0;
            let mut j: usize = 0;

            // CaDiCaL propagate.cpp:249: tick accounting
            ticks += 1 + (watch_len as u64).div_ceil(16);

            // CaDiCaL propagate.cpp:289-302: binary conflicts do NOT
            // immediately break — continue scanning binary watchers (#8043).
            let mut binary_conflict: Option<ClauseRef> = None;
            // Binary prefix: binary watchers are always kept, and the
            // binary-first invariant guarantees [0..binary_count) contains no
            // long watchers. Scan this prefix without BINARY_FLAG branches or
            // compaction stores; j advances in lockstep with i.
            while i < binary_count {
                // SAFETY: i < binary_count <= end = watch_len. One 8-byte load
                // yields blocker AND clause ref (#9773) — no second stream.
                let entry = unsafe { *entries_ptr.add(i) };
                let blocker_raw = entry_blocker_raw(entry);
                i += 1;

                if prefetch_vals && i < binary_count {
                    // SAFETY: guarded by i < binary_count <= watch_len, so the
                    // lookahead read is in bounds.
                    let next_entry = unsafe { *entries_ptr.add(i) };
                    // The blocker is expected to be a live literal index, but
                    // a prefetch hint never dereferences its address. Use
                    // wrapping arithmetic so speculative lookahead does not
                    // depend on that invariant for pointer construction.
                    ay_prefetch::prefetch_read_l1(
                        vals_ptr.wrapping_add(entry_blocker_raw(next_entry) as usize),
                    );
                }

                debug_assert!(
                    (blocker_raw as usize) < vals_len,
                    "BUG: blocker_raw {blocker_raw} >= vals_len {vals_len} — stale watch entry after compaction?",
                );
                // SAFETY: blocker_raw is a Literal index. The invariant
                // Literal::index() < 2 * num_vars == vals.len() is maintained
                // by construction. Stale watch entries after compaction are
                // cleaned up by rebuild_watches, not guarded per-iteration.
                // Removing the per-blocker bounds check (#8547 → #9301)
                // eliminates one cmp+branch from the hottest BCP inner loop,
                // matching CaDiCaL/GipSAT's unchecked `vals[lit]` pattern.
                let blocker_val: i8 = unsafe { *vals_ptr.add(blocker_raw as usize) };

                if blocker_val > 0 {
                    j += 1;
                    if COLLECT_BCP_TELEMETRY {
                        self.stats.bcp_blocker_fastpath_hits += 1;
                    }
                    continue;
                }

                // Binary clause handling. Binary watcher lifecycle (#4924):
                // deletion eagerly unlinks binary watches, so propagation can
                // avoid header liveness checks. The clause ref comes from the
                // SAME 8-byte entry already loaded above (#9773).
                debug_assert!(
                    entry_is_binary(entry),
                    "BUG: binary prefix entry {} is not binary",
                    i - 1
                );
                if COLLECT_BCP_TELEMETRY {
                    self.stats.bcp_binary_path_hits += 1;
                }
                let clause_ref = ClauseRef(entry_clause_off(entry));
                if blocker_val < 0 {
                    // CaDiCaL propagate.cpp:289-290: record binary conflict
                    // but continue scanning binary watchers (#8043).
                    binary_conflict = Some(clause_ref);
                    j += 1;
                    continue;
                }
                // Unassigned — propagate, keep watcher.
                ticks += 1;
                j += 1;
                // Jump reasons (#8034): in SEARCH mode at decision_level > 0
                // with jump reasons enabled. Gate: only when formula has high
                // binary clause ratio (>= 99%, Kissat classify.c bigbigfraction=990)
                // AND LRAT is disabled (LRAT requires clause IDs for hints).
                //
                // ChrBT dispatch (#8465): when chrono is off, use the
                // nochrono variants that skip assignment_level() and
                // lifecycle bookkeeping. Predicate hoisted to `jump_reasons`
                // above (#shave5).
                if jump_reasons {
                    if chrono {
                        self.enqueue_binary_reason(Literal(blocker_raw), false_lit);
                    } else {
                        self.enqueue_binary_reason_nochrono_fast(Literal(blocker_raw), false_lit);
                    }
                } else if MODE == bcp_mode::SEARCH {
                    // Single-call binary enqueue with flag pre-set (#8042).
                    // ChrBT fast path (#8465): pass false_lit as the known
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
                        self.enqueue_bcp_binary_nochrono_fast(Literal(blocker_raw), clause_ref);
                    }
                } else {
                    self.enqueue(Literal(blocker_raw), Some(clause_ref));
                }
            }
            debug_assert_eq!(
                i, binary_count,
                "BCP unsafe: binary scan stopped before binary_count"
            );
            debug_assert_eq!(
                j, binary_count,
                "BCP unsafe: binary scan changed binary prefix length"
            );

            // CaDiCaL propagate.cpp:301-302: stop before long clauses if a
            // binary conflict was found. The long suffix is untouched, so it
            // remains valid and no compaction/truncation is needed.
            if let Some(conflict_ref) = binary_conflict {
                self.flush_bcp_ticks::<MODE>(ticks);
                if MODE == bcp_mode::SEARCH {
                    self.num_search_propagations += (self.qhead - qhead_start) as u64;
                }
                return Some(self.unsafe_conflict_finalize(conflict_ref, qhead_start));
            }

            // Long suffix: entries [binary_count..end) are all non-binary, so
            // the loop uses the existing long-clause logic with no BINARY_FLAG
            // branch. Only this suffix can create compaction gaps.
            'watch: while i < end {
                // CaDiCaL propagate.cpp:253: `const Watch w = *j++ = *i++`.
                // One 8-byte entry load serves blocker AND clause ref (#9773);
                // the unconditional full-entry copy to the compaction slot
                // replaces the old blocker copy + conditional clause copy.
                // SAFETY: i < end = watch_len, so entries_ptr.add(i) is in bounds.
                // j <= i (compaction invariant), so entries_ptr.add(j) is in bounds.
                let entry = unsafe { *entries_ptr.add(i) };
                // SAFETY: j <= i < end = watch_len, and entries_ptr spans all
                // watch_len packed entries, so the compaction write is in bounds.
                unsafe { *entries_ptr.add(j) = entry };
                i += 1;

                // Long suffix: the binary-first invariant guarantees the entry
                // flag (bit 31) is clear, so the low half IS the blocker raw.
                debug_assert!(
                    !entry_is_binary(entry),
                    "BUG: long suffix entry {} is binary",
                    i - 1
                );
                let blocker_raw = entry as u32;

                // Single lookahead-entry load (#shave5): both the vals
                // prefetch here and the clause prefetch on the blocker-miss
                // path below need the NEXT packed entry. Load it once so the
                // blocker-miss path does not repeat the load.
                let next_entry: u64 = if i < end {
                    // SAFETY: guarded by i < end = watch_len, so the lookahead
                    // read is in bounds.
                    unsafe { *entries_ptr.add(i) }
                } else {
                    0
                };
                if prefetch_vals && i < end {
                    // The blocker is expected to be a live literal index, but
                    // a prefetch hint never dereferences its address. Use
                    // wrapping arithmetic so speculative lookahead does not
                    // depend on that invariant for pointer construction.
                    // (#shave6: gated — the next_entry load above stays
                    // unconditional because the clause prefetch on the
                    // blocker-miss path reuses it.)
                    ay_prefetch::prefetch_read_l1(
                        vals_ptr.wrapping_add(entry_blocker_raw(next_entry) as usize),
                    );
                }

                debug_assert!(
                    (blocker_raw as usize) < vals_len,
                    "BUG: blocker_raw {blocker_raw} >= vals_len {vals_len} — stale watch entry after compaction?",
                );
                // SAFETY: blocker_raw is a Literal index. The invariant
                // Literal::index() < 2 * num_vars == vals.len() is maintained
                // by construction (same reasoning as the binary prefix above).
                let blocker_val: i8 = unsafe { *vals_ptr.add(blocker_raw as usize) };

                if blocker_val > 0 {
                    // Blocker satisfied — keep watcher. The full entry
                    // (blocker + clause ref) was already copied to position j
                    // unconditionally above.
                    j += 1;
                    if COLLECT_BCP_TELEMETRY && MODE == bcp_mode::SEARCH {
                        self.stats.bcp_long_blocker_fastpath_hits += 1;
                    }
                    if COLLECT_BCP_TELEMETRY {
                        self.stats.bcp_blocker_fastpath_hits += 1;
                    }
                    continue 'watch;
                }

                // Blocker miss (slow path): the clause offset comes from the
                // SAME entry already in a register — no second stream load
                // (#9773). The entry is already at position j from the
                // unconditional copy above.
                let clause_idx = entry_clause_off(entry) as usize;
                let off = clause_idx;

                // Lookahead prefetch (#8000): prefetch the NEXT watcher's clause
                // arena data while we process the current long clause. Hides
                // ~60-80 cycles of main-memory latency per long clause access.
                // Reuses the `next_entry` loaded above (#shave5).
                if i < end && !entry_is_binary(next_entry) {
                    // `next_entry` is speculative and may carry a stale arena
                    // offset. `wrapping_add` forms the hint address without the
                    // in-allocation requirement of `ptr.add`; the result is
                    // never dereferenced and prefetch instructions do not fault.
                    ay_prefetch::prefetch_read_l2(
                        words_ptr.wrapping_add(entry_clause_off(next_entry) as usize),
                    );
                }

                // Read BCP header via unchecked raw pointer (#8465).
                // Bounds check (#8547): after arena GC, stale watch entries may
                // reference unmapped arena offsets. Verify that the clause header
                // (offset + HEADER_WORDS) fits within the arena before reading.
                // If out of bounds, treat as garbage (skip the watcher).
                if off + HEADER_WORDS + 2 > words_len {
                    // Stale arena offset — skip this watcher (don't increment j).
                    self.stats.stale_bcp_watch_skips += 1;
                    continue 'watch;
                }
                // SAFETY: words_ptr points to arena.words[0], and off is validated
                // above to be within bounds. Every clause has at least
                // HEADER_WORDS (3) words, so off + 2 < arena.words.len().
                let bcp_header = unsafe { self.arena.bcp_header_unchecked(words_ptr, off) };
                if bcp_header.is_garbage_any() {
                    // Garbage — drop watcher (don't increment j).
                    continue 'watch;
                }
                if MODE == bcp_mode::VIVIFY && bcp_header.is_vivify_skipped() {
                    // Keep watcher — clause_ref already at position j from
                    // the speculative copy above.
                    j += 1;
                    continue 'watch;
                }
                ticks += 1;

                // Long-suffix path: entry flag (bit 31) clear, so the high
                // half is exactly the clause word offset (#9670, #9773).
                let clause_ref = ClauseRef(entry_clause_off(entry));
                let mut clause_len = 0usize;
                let mut cached_saved_pos = 0usize;
                if !DEFER_SAVED_POS_EXTRACTION {
                    clause_len = bcp_header.clause_len();
                    cached_saved_pos = bcp_header.saved_pos();
                }

                // XOR trick for the other watched literal.
                // SAFETY: off + HEADER_WORDS + 0 and off + HEADER_WORDS + 1
                // are within arena bounds (clause has >= 2 literals).
                let lit0_raw = unsafe { *words_ptr.add(off + HEADER_WORDS) };
                // SAFETY: the same validated two-literal clause extent covers
                // off + HEADER_WORDS + 1.
                let lit1_raw = unsafe { *words_ptr.add(off + HEADER_WORDS + 1) };
                let lit0 = Literal(lit0_raw);
                let lit1 = Literal(lit1_raw);

                debug_assert!(
                    lit0 == false_lit || lit1 == false_lit,
                    "BUG: watch list for {false_lit:?} contains clause {clause_idx} \
                     with watched lits {lit0:?}, {lit1:?} — neither matches"
                );
                let first = Literal(lit0_raw ^ lit1_raw ^ false_lit.0);
                debug_assert!(
                    first.index() < vals_len,
                    "BUG: first.index() {} >= vals_len {} — stale clause?",
                    first.index(),
                    vals_len,
                );
                // SAFETY: first is derived from XOR of two watched literals
                // which are both valid Literal indices (validated at watch
                // creation). The invariant Literal::index() < 2*num_vars ==
                // vals.len() is maintained by construction. Removing the
                // per-clause bounds check (#8547 → #9301) eliminates one
                // cmp+branch from the long-clause path.
                let first_val: i8 = unsafe { *vals_ptr.add(first.index()) };

                if first_val > 0 {
                    // Other watched literal satisfied — update blocker to `first`
                    // in the packed entry (clause half preserved).
                    // SAFETY: j < i <= end, entries_ptr.add(j) in bounds.
                    unsafe { *entries_ptr.add(j) = entry_with_blocker(entry, first.0) };
                    j += 1;
                    continue 'watch;
                }

                // Position of the false watched literal (0 or 1). Only the
                // replacement-move paths (swap_literals) need it, so it is
                // computed after the satisfied-other-watch fast path (#shave5).
                let false_pos = usize::from(lit0 != false_lit);

                if DEFER_SAVED_POS_EXTRACTION {
                    // Default-off experiment (#9078): avoid saved_pos/header-bit
                    // extraction until replacement scanning actually needs it.
                    // The same-host uf250 smoke was noisy/slower, so production
                    // keeps the original eager extraction unless the env guard is
                    // set.
                    clause_len = bcp_header.clause_len();
                }

                // Replacement search (Gent saved position).
                debug_assert!(clause_len > 2);

                // Clause-level bounds validation (#9301): validate the entire
                // clause extent once, then use unchecked access in the scan.
                // This replaces the per-literal arena_idx and vals bounds checks
                // from #8547, eliminating 2 branches per literal in the hottest
                // inner loop. GipSAT/CaDiCaL use unchecked access throughout.
                //
                // SAFETY: if the clause extent exceeds the arena, skip it as
                // stale. Otherwise, off + HEADER_WORDS + k < words_len for all
                // k < clause_len, so all literal reads are in bounds.
                if off + HEADER_WORDS + clause_len > words_len {
                    // Stale clause length after GC — skip this watcher.
                    continue 'watch;
                }

                // Base pointer for literal access: off + HEADER_WORDS.
                // All literal reads use this base + k, validated by the
                // clause-level bounds check above.
                let lits_base = off + HEADER_WORDS;

                let mut replacement_k: usize = clause_len; // sentinel
                let mut replacement_val: i8 = -1;
                let mut replacement_lit = false_lit;
                let mut relocate_true_tail_watch = false;
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

                // Short clause optimization (#8569): for clauses with <= 5
                // literals, skip saved position (always start at 2), skip
                // val prefetching (clause fits in one cache line), and skip
                // the second cache-line prefetch. Clauses with 6-8 literals
                // keep saved_pos accounting, but use an unrolled bounded scan
                // below instead of the generic long-clause loop.
                if !LEAN && clause_len <= 5 {
                    // Short clause: linear scan from position 2, no saved_pos,
                    // no prefetching. Len-3 and len-4 clauses are specialized
                    // because they dominate the short-clause hot path.
                    match clause_len {
                        3 => {
                            if COLLECT_BCP_TELEMETRY {
                                self.stats.record_bcp_replacement_scan_step(
                                    clause_len,
                                    clause_is_learned,
                                );
                            }
                            // SAFETY: index 2 < clause_len (3..=5 in this
                            // match) and the clause extent was validated
                            // against words_len above; lit2_raw is a clause
                            // literal, a valid index < vals.len().
                            let lit2_raw = unsafe { *words_ptr.add(lits_base + 2) };
                            // SAFETY: lit2_raw came from the validated clause
                            // extent and clause literals are valid vals indices.
                            let v2: i8 = unsafe { *vals_ptr.add(lit2_raw as usize) };
                            if v2 >= 0 {
                                replacement_k = 2;
                                replacement_val = v2;
                                replacement_lit = Literal(lit2_raw);
                            }
                        }
                        4 => {
                            if COLLECT_BCP_TELEMETRY {
                                self.stats.record_bcp_replacement_scan_step(
                                    clause_len,
                                    clause_is_learned,
                                );
                            }
                            // SAFETY: index 2 < clause_len (3..=5 in this
                            // match) and the clause extent was validated
                            // against words_len above; lit2_raw is a clause
                            // literal, a valid index < vals.len().
                            let lit2_raw = unsafe { *words_ptr.add(lits_base + 2) };
                            // SAFETY: lit2_raw came from the validated clause
                            // extent and clause literals are valid vals indices.
                            let v2: i8 = unsafe { *vals_ptr.add(lit2_raw as usize) };
                            if v2 >= 0 {
                                replacement_k = 2;
                                replacement_val = v2;
                                replacement_lit = Literal(lit2_raw);
                            } else {
                                if COLLECT_BCP_TELEMETRY {
                                    self.stats.record_bcp_replacement_scan_step(
                                        clause_len,
                                        clause_is_learned,
                                    );
                                }
                                // SAFETY: index 3 < clause_len (4..=5 in this
                                // match) and the clause extent was validated
                                // against words_len above; lit3_raw is a clause
                                // literal, a valid index < vals.len().
                                let lit3_raw = unsafe { *words_ptr.add(lits_base + 3) };
                                // SAFETY: lit3_raw came from the validated clause
                                // extent and clause literals are valid vals indices.
                                let v3: i8 = unsafe { *vals_ptr.add(lit3_raw as usize) };
                                if v3 >= 0 {
                                    replacement_k = 3;
                                    replacement_val = v3;
                                    replacement_lit = Literal(lit3_raw);
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
                            // SAFETY: index 2 < clause_len (3..=5 in this
                            // match) and the clause extent was validated
                            // against words_len above; lit2_raw is a clause
                            // literal, a valid index < vals.len().
                            let lit2_raw = unsafe { *words_ptr.add(lits_base + 2) };
                            // SAFETY: lit2_raw came from the validated clause
                            // extent and clause literals are valid vals indices.
                            let v2: i8 = unsafe { *vals_ptr.add(lit2_raw as usize) };
                            if v2 >= 0 {
                                replacement_k = 2;
                                replacement_val = v2;
                                replacement_lit = Literal(lit2_raw);
                            } else {
                                if COLLECT_BCP_TELEMETRY {
                                    self.stats.record_bcp_replacement_scan_step(
                                        clause_len,
                                        clause_is_learned,
                                    );
                                }
                                // SAFETY: index 3 < clause_len (4..=5 in this
                                // match) and the clause extent was validated
                                // against words_len above; lit3_raw is a clause
                                // literal, a valid index < vals.len().
                                let lit3_raw = unsafe { *words_ptr.add(lits_base + 3) };
                                // SAFETY: lit3_raw came from the validated clause
                                // extent and clause literals are valid vals indices.
                                let v3: i8 = unsafe { *vals_ptr.add(lit3_raw as usize) };
                                if v3 >= 0 {
                                    replacement_k = 3;
                                    replacement_val = v3;
                                    replacement_lit = Literal(lit3_raw);
                                } else {
                                    if COLLECT_BCP_TELEMETRY {
                                        self.stats.record_bcp_replacement_scan_step(
                                            clause_len,
                                            clause_is_learned,
                                        );
                                    }
                                    // SAFETY: index 4 < clause_len == 5 and
                                    // the clause extent was validated against
                                    // words_len above; lit4_raw is a clause
                                    // literal, a valid index < vals.len().
                                    let lit4_raw = unsafe { *words_ptr.add(lits_base + 4) };
                                    // SAFETY: lit4_raw came from the validated clause
                                    // extent and clause literals are valid vals indices.
                                    let v4: i8 = unsafe { *vals_ptr.add(lit4_raw as usize) };
                                    if v4 >= 0 {
                                        replacement_k = 4;
                                        replacement_val = v4;
                                        replacement_lit = Literal(lit4_raw);
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                } else {
                    // Long clause: use saved position.
                    if DEFER_SAVED_POS_EXTRACTION {
                        cached_saved_pos = bcp_header.saved_pos();
                    }
                    let mut pos = cached_saved_pos;
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
                    let mut saved_start_lit_raw = false_lit.0;
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
                        // SAFETY: pos was normalized to [2, clause_len) above
                        // and the clause extent was validated against
                        // words_len; the loaded literal is a valid index
                        // < vals.len() by construction.
                        saved_start_lit_raw = unsafe { *words_ptr.add(lits_base + pos) };
                        // SAFETY: saved_start_lit_raw came from the validated
                        // clause extent and clause literals are valid vals indices.
                        saved_start_val = unsafe { *vals_ptr.add(saved_start_lit_raw as usize) };
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

                    if reset_false_start_candidate && saved_start_val >= 0 {
                        replacement_k = normalized_saved_pos;
                        replacement_val = saved_start_val;
                        replacement_lit = Literal(saved_start_lit_raw);
                        if COLLECT_BCP_TELEMETRY {
                            self.stats
                                .record_bcp_replacement_scan_step(clause_len, clause_is_learned);
                        }
                        if profile_learned_scan_pressure_or_identity_for_clause {
                            learned_no_replacement_scan_pressure_steps += 1;
                        }
                    }

                    let mut blocker_cert_elided_scan = false;
                    let mut blocker_cert_shadow_probe: Option<(usize, u32)> = None;
                    if learned_1963_blocker_cert_for_clause
                        && saved_start_val < 0
                        && normalized_saved_pos > 2
                    {
                        let probe = self.probe_learned_1963_blocker_cert_unsafe(
                            off,
                            clause_len,
                            clause_is_learned,
                            normalized_saved_pos,
                            known_false_saved_start,
                            words_ptr,
                            vals_ptr,
                            lits_base,
                            COLLECT_BCP_TELEMETRY,
                            profile_learned_scan_pressure_or_identity_for_clause,
                            shadow_learned_1963_blocker_cert,
                            demote_learned_1963_blocker_cert_false_reject,
                        );
                        learned_no_replacement_scan_pressure_steps += probe.profile_scan_steps;
                        if let Some((cert_pos, cert_lit_raw, cert_val)) = probe.replacement {
                            replacement_k = cert_pos;
                            replacement_val = cert_val;
                            replacement_lit = Literal(cert_lit_raw);
                        }
                        blocker_cert_elided_scan = probe.elided_scan;
                        blocker_cert_shadow_probe = probe.shadow_probe;
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
                                // SAFETY: every $k passed here is
                                // < clause_len (<= 8) and the clause extent
                                // was validated against words_len above;
                                // lit_k_raw is a clause literal, a valid
                                // index < vals.len().
                                let lit_k_raw = unsafe { *words_ptr.add(lits_base + $k) };
                                // SAFETY: lit_k_raw came from the validated clause
                                // extent and clause literals are valid vals indices.
                                let v: i8 = unsafe { *vals_ptr.add(lit_k_raw as usize) };
                                if v >= 0 {
                                    replacement_k = $k;
                                    replacement_val = v;
                                    replacement_lit = Literal(lit_k_raw);
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
                            ($k:expr, $lit_k_raw:expr, $next_lit_raw:expr) => {{
                                if COLLECT_BCP_TELEMETRY {
                                    self.stats.record_bcp_replacement_scan_step(
                                        clause_len,
                                        clause_is_learned,
                                    );
                                }
                                if profile_learned_scan_pressure_or_identity_for_clause {
                                    learned_no_replacement_scan_pressure_steps += 1;
                                }
                                if prefetch_vals {
                                    if let Some(next_lit_raw) = $next_lit_raw {
                                        // SAFETY: next_lit_raw is a clause
                                        // literal (valid index < vals.len());
                                        // the pointer is only passed to
                                        // prefetch, never dereferenced.
                                        // (#shave6: gated on vals residency.)
                                        ay_prefetch::prefetch_read_l1(unsafe {
                                            vals_ptr.add(next_lit_raw as usize)
                                        });
                                    }
                                }
                                let lit_k_raw = $lit_k_raw;
                                // SAFETY: lit_k_raw is a clause literal read
                                // from within the validated clause extent,
                                // hence a valid index < vals.len().
                                let v: i8 = unsafe { *vals_ptr.add(lit_k_raw as usize) };
                                if v >= 0 {
                                    replacement_k = $k;
                                    replacement_val = v;
                                    replacement_lit = Literal(lit_k_raw);
                                    true
                                } else {
                                    false
                                }
                            }};
                        }
                        macro_rules! try_generic_replacement_slot {
                            ($k:expr, $next_limit:expr) => {{
                                // SAFETY: $k < $next_limit <= clause_len and
                                // the clause extent was validated against
                                // words_len above, so the read is within the
                                // clause's literal words.
                                let lit_k_raw = unsafe { *words_ptr.add(lits_base + $k) };
                                let next_lit_raw = if $k + 1 < $next_limit {
                                    // SAFETY: guarded by $k + 1 < $next_limit
                                    // <= clause_len, within the validated
                                    // clause extent.
                                    Some(unsafe { *words_ptr.add(lits_base + $k + 1) })
                                } else {
                                    None
                                };
                                try_generic_replacement_lit!($k, lit_k_raw, next_lit_raw)
                            }};
                        }
                        macro_rules! scan_generic_replacement_range {
                            ($start:expr, $end:expr) => {{
                                let start = $start;
                                let end = $end;
                                let mut found = false;
                                if start < end {
                                    let mut k = start;
                                    // SAFETY: k = start < end, and every range
                                    // passed to this macro satisfies
                                    // end <= clause_len, so the read is within
                                    // the clause extent validated against
                                    // words_len above.
                                    let mut lit_k_raw = unsafe { *words_ptr.add(lits_base + k) };
                                    loop {
                                        let next_k = k + 1;
                                        let next_lit_raw = if next_k < end {
                                            // SAFETY: guarded by next_k < end
                                            // <= clause_len, within the
                                            // validated clause extent.
                                            Some(unsafe { *words_ptr.add(lits_base + next_k) })
                                        } else {
                                            None
                                        };
                                        if try_generic_replacement_lit!(k, lit_k_raw, next_lit_raw)
                                        {
                                            found = true;
                                            break;
                                        }
                                        if let Some(next_lit_raw) = next_lit_raw {
                                            k = next_k;
                                            lit_k_raw = next_lit_raw;
                                        } else {
                                            break;
                                        }
                                    }
                                }
                                found
                            }};
                        }

                        // First scan: from saved_pos to end.
                        // SAFETY: k < clause_len, and we validated
                        // off + HEADER_WORDS + clause_len <= words_len above.
                        //
                        // Val prefetch optimization (#8465): prefetch vals[lits[k+1]]
                        // while checking vals[lits[k]], hiding L2/L3 latency.
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
                                // Second scan: from 2 to saved_pos (wrap-around).
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
                    // and differs from the cached position (#8569). Skip the
                    // arena write when no replacement is found (sentinel).
                    // The default-off advance experiment only steps past an
                    // unassigned replacement for learned long clauses after
                    // missing the saved start when the next tail slot is not
                    // already false.
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
                            // SAFETY: next_k is replacement_k + 1 or 2, both
                            // < clause_len (the enclosing branch checked
                            // replacement_k < clause_len, and clause_len > 2),
                            // within the clause extent validated against
                            // words_len; next_lit_raw is a clause literal, a
                            // valid index < vals.len().
                            let next_lit_raw = unsafe { *words_ptr.add(lits_base + next_k) };
                            // SAFETY: next_lit_raw came from the validated clause
                            // extent and clause literals are valid vals indices.
                            let next_val: i8 = unsafe { *vals_ptr.add(next_lit_raw as usize) };
                            if next_val >= 0 {
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

                if replacement_val > 0 {
                    if relocate_true_tail_watch {
                        debug_assert!(
                            replacement_k >= 2 && replacement_k < clause_len,
                            "BUG: replacement index {replacement_k} outside [2, {clause_len})"
                        );
                        ticks += 1;
                        self.arena.swap_literals(off, false_pos, replacement_k);
                        self.deferred_replacement_watches
                            .push((replacement_lit, Watcher::new(clause_ref, first)));
                        continue 'watch;
                    }
                    // Replacement satisfied — update blocker to replacement_lit
                    // in the packed entry (clause half preserved).
                    // SAFETY: j < i <= end, entries_ptr.add(j) in bounds.
                    unsafe {
                        *entries_ptr.add(j) = entry_with_blocker(entry, replacement_lit.0);
                    }
                    j += 1;
                    continue 'watch;
                } else if replacement_val == 0 {
                    // Found unassigned replacement — move watch.
                    debug_assert!(
                        replacement_k >= 2 && replacement_k < clause_len,
                        "BUG: replacement index {replacement_k} outside [2, {clause_len})"
                    );
                    ticks += 1;
                    self.arena.swap_literals(off, false_pos, replacement_k);
                    // Defer watch addition to avoid cache pollution (#8041).
                    self.deferred_replacement_watches
                        .push((replacement_lit, Watcher::new(clause_ref, first)));
                    // Drop this watcher (don't increment j).
                    continue 'watch;
                }

                // No replacement found — all tail literals false.
                debug_assert!(
                    (2..clause_len).all(|k| {
                        let lk = self.arena.literal(off, k);
                        self.lit_val(lk) < 0
                    }),
                    "BUG: no-replacement path but a tail literal is not false"
                );

                if first_val < 0 {
                    // Conflict — both watched literals false.
                    // Keep current watcher — the full entry is already at
                    // position j from the speculative copy above.
                    j += 1;
                    self.unsafe_copy_remaining_entries(entries_ptr, &mut j, i, end);
                    if j != end {
                        // SAFETY: unsafe_copy_remaining_entries preserves
                        // j <= end and initializes every entry in [0, j).
                        unsafe {
                            self.watches
                                .get_watches_mut(false_lit)
                                .set_len_after_bcp_compaction(j);
                        }
                    }
                    self.flush_bcp_ticks::<MODE>(ticks);
                    if MODE == bcp_mode::SEARCH {
                        self.num_search_propagations += (self.qhead - qhead_start) as u64;
                    }
                    return Some(self.unsafe_conflict_finalize(clause_ref, qhead_start));
                }

                // Unit propagation.
                // Keep current watcher — the full entry is already at position
                // j from the speculative copy above; refresh only the blocker
                // half (clause half preserved).
                let skip_unit_blocker_refresh =
                    disable_learned_1963_no_replacement_unit_blocker_refresh
                        && clause_is_learned
                        && (19..=63).contains(&clause_len);
                if !skip_unit_blocker_refresh {
                    // SAFETY: the scan already advanced past this entry, so
                    // j < i <= end and therefore j indexes entries_ptr.
                    unsafe {
                        *entries_ptr.add(j) = entry_with_blocker(entry, first.0);
                    }
                }
                ticks += 1;
                j += 1;
                // Lightweight enqueue for SEARCH mode (#8042).
                // ChrBT dispatch (#8465): nochrono variant skips the
                // O(clause_len) assignment_level scan.
                if MODE == bcp_mode::SEARCH {
                    if chrono {
                        self.enqueue_bcp::<true>(first, clause_ref);
                    } else {
                        self.enqueue_bcp_nochrono_fast(first, clause_ref);
                    }
                } else {
                    self.enqueue(first, Some(clause_ref));
                }
            }

            // Compaction complete: truncate the watch list to j entries.
            // Binary conflicts return before the long suffix, so this point only
            // sees ordinary long-clause compaction.
            debug_assert!(
                j <= watch_len,
                "BCP unsafe: final j ({j}) > watch_len ({watch_len})"
            );
            if j != watch_len {
                // SAFETY: j <= watch_len = original length, and the loop wrote
                // valid packed entries throughout [0, j).
                unsafe {
                    self.watches
                        .get_watches_mut(false_lit)
                        .set_len_after_bcp_compaction(j);
                }
            }

            // Flush deferred replacement watches (#8041). Collected during the
            // scan above to avoid cache pollution from writing to other literals'
            // watch lists during the hot BCP inner loop.
            // Fast path (#7998): skip the loop setup when no replacements were
            // found (common for short watch lists or mostly-binary formulas).
            if !self.deferred_replacement_watches.is_empty() {
                for &(lit, watcher) in &self.deferred_replacement_watches {
                    self.watches.add_watch(lit, watcher);
                }
                self.deferred_replacement_watches.clear();
            }
        }

        self.num_propagations += (self.qhead - qhead_start) as u64;
        if MODE == bcp_mode::SEARCH {
            self.num_search_propagations += (self.qhead - qhead_start) as u64;
        }
        self.flush_bcp_ticks::<MODE>(ticks);
        // Reason marks maintained incrementally by enqueue_bcp (#8100).
        self.no_conflict_until = self.trail.len();
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: propagate_bcp_unsafe completed but qhead ({}) != trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );
        None
    }

    /// Copy remaining unvisited watchers during conflict finalization
    /// (packed AoS entries, #9773).
    ///
    /// # Safety
    /// `entries_ptr` must point to a valid packed-entry array of at least
    /// `end` entries. `j` must be <= `end`, `i` must be <= `end`.
    #[inline(always)]
    fn unsafe_copy_remaining_entries(
        &self,
        entries_ptr: *mut u64,
        j: &mut usize,
        i: usize,
        end: usize,
    ) {
        if i < end {
            // SAFETY: i < end and *j < end (since j <= i before copy).
            // Both source [i..end) and dest [*j..*j+(end-i)) are within
            // the entry buffer. They may overlap, so we use copy.
            unsafe {
                let count = end - i;
                std::ptr::copy(entries_ptr.add(i), entries_ptr.add(*j), count);
                *j += count;
            }
        }
    }

    /// Conflict finalization for the unsafe BCP path.
    ///
    /// Unlike the safe version, the watch list has already been truncated
    /// by the caller (via set_len). This function only updates stats and
    /// records the conflict.
    ///
    /// `pub(super)` visibility: also used by `propagate_bcp_ic3` in
    /// `propagation_bcp.rs` which uses the same in-place iteration pattern.
    #[inline(always)]
    pub(super) fn unsafe_conflict_finalize(
        &mut self,
        clause_ref: ClauseRef,
        qhead_start: usize,
    ) -> ClauseRef {
        // Flush deferred replacement watches on conflict path (#8041).
        if !self.deferred_replacement_watches.is_empty() {
            for &(lit, watcher) in &self.deferred_replacement_watches {
                self.watches.add_watch(lit, watcher);
            }
            self.deferred_replacement_watches.clear();
        }
        self.num_propagations += (self.qhead - qhead_start) as u64;
        self.no_conflict_until = if self.decision_level == 0 {
            0
        } else {
            self.trail_lim[self.decision_level as usize - 1]
        };
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
}

// ---------------------------------------------------------------------------
// #shave7: unchecked hot-path assignment tail (kissat inlineassign.h pattern)
// ---------------------------------------------------------------------------
impl Solver {
    /// Unchecked assignment tail for the unsafe BCP loop: phase store, vals
    /// stores, VarData store, and trail push with the residual bounds/
    /// capacity branches removed (the kissat `*trail_end++` pattern). Ends
    /// with the standard next-watch prefetch. Combined with the safe
    /// enqueues' bounds-checked equivalents this removes ~8-10 dynamic
    /// instructions from EVERY propagation (#shave7).
    ///
    /// SAFETY (callers must guarantee):
    /// - `lit.variable().index() < self.num_vars`: every `_fast` wrapper
    ///   debug_asserts this, and the #8359 stale-literal guards enforce it
    ///   for all BCP-sourced literals. `phase`/`var_data` are sized to
    ///   `num_vars` by `ensure_num_vars`, so the unchecked stores are in
    ///   bounds.
    /// - `reserve_trail_for_bcp()` ran at the BCP loop entry, so
    ///   `trail.capacity() >= num_vars`. Each variable is assigned at most
    ///   once, hence `trail.len() < num_vars` whenever a new assignment is
    ///   enqueued and the raw push is within capacity.
    #[inline(always)]
    unsafe fn assign_bcp_unchecked(
        &mut self,
        lit: Literal,
        level: u32,
        reason: u32,
        extra_flags: u8,
    ) {
        let vi = lit.variable().index();
        // SAFETY: The caller guarantees `vi` indexes phase/var_data/vals and
        // that the trail has spare capacity, as detailed in the contract above.
        unsafe {
            *self.phase.get_unchecked_mut(vi) = lit.sign_i8();
            ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
            ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
            let len = self.trail.len();
            let slot = self.var_data.get_unchecked_mut(vi);
            let preserved = slot.flags & VarData::FLAG_SEEN_PUB;
            *slot = VarData {
                level,
                trail_pos: len as u32,
                reason,
                flags: preserved | extra_flags,
                _pad: [0; 3],
            };
            debug_assert!(
                len < self.trail.capacity(),
                "BUG: assign_bcp_unchecked without reserve_trail_for_bcp (len={} cap={})",
                len,
                self.trail.capacity(),
            );
            self.trail.as_mut_ptr().add(len).write(lit);
            self.trail.set_len(len + 1);
        }
        self.watches.prefetch_first(lit.negated());
    }

    /// Fast-path twin of `enqueue_bcp_nochrono` (#shave7). Unsafe-BCP loop
    /// only; the safe loop keeps the bounds-checked original.
    #[inline(always)]
    pub(super) fn enqueue_bcp_nochrono_fast(&mut self, lit: Literal, reason: ClauseRef) {
        debug_assert!(
            lit.variable().index() < self.num_vars,
            "BUG: enqueue_bcp_nochrono_fast variable index {} >= num_vars {} (lit={lit:?})",
            lit.variable().index(),
            self.num_vars,
        );
        debug_assert!(!self.chrono_enabled);
        let dl = self.decision_level;
        // `OnClauseUse(c)`, BCP half (arXiv:2602.20829): this clause just
        // forced a literal. No-op unless the two-stage arm is armed.
        self.two_stage_note_bcp_use(reason);
        // SAFETY: index bound asserted above (#8359 guards upstream); the
        // unsafe BCP loop entry calls reserve_trail_for_bcp.
        unsafe {
            self.assign_bcp_unchecked(lit, dl, reason.0, 0);
        }
    }

    /// Fast-path twin of `enqueue_bcp_binary_nochrono` (#shave7).
    #[inline(always)]
    pub(super) fn enqueue_bcp_binary_nochrono_fast(&mut self, lit: Literal, reason: ClauseRef) {
        debug_assert!(
            lit.variable().index() < self.num_vars,
            "BUG: enqueue_bcp_binary_nochrono_fast variable index {} >= num_vars {} (lit={lit:?})",
            lit.variable().index(),
            self.num_vars,
        );
        debug_assert!(!self.chrono_enabled);
        let dl = self.decision_level;
        // `OnClauseUse(c)`, BCP half (arXiv:2602.20829): this clause just
        // forced a literal. No-op unless the two-stage arm is armed.
        self.two_stage_note_bcp_use(reason);
        // SAFETY: the only call site passes an unassigned blocker from a live
        // binary watcher. The watch/rebuild invariant keeps that literal below
        // `2 * num_vars`, so its variable indexes phase/VarData. Because each
        // variable has at most one trail entry, this unassigned variable gives
        // `trail.len() < num_vars`; the BCP entry reserved at least `num_vars`
        // slots, so the raw trail push also remains within capacity.
        unsafe {
            self.assign_bcp_unchecked(lit, dl, reason.0, VarData::FLAG_BINARY_REASON_PUB);
        }
    }

    /// Fast-path twin of `enqueue_binary_reason_nochrono` (#shave7), keeping
    /// the jump-reason chain shortening (Kissat fastassign.h:12-19).
    #[inline(always)]
    pub(super) fn enqueue_binary_reason_nochrono_fast(
        &mut self,
        lit: Literal,
        mut reason_lit: Literal,
    ) {
        debug_assert!(
            lit.variable().index() < self.num_vars,
            "BUG: enqueue_binary_reason_nochrono_fast variable index {} >= num_vars {} (lit={lit:?})",
            lit.variable().index(),
            self.num_vars,
        );
        debug_assert!(!self.chrono_enabled);
        debug_assert!(self.decision_level > 0);
        let other_var = reason_lit.variable().index();
        if other_var < self.num_vars {
            let other_vd = self.var_data[other_var];
            if other_vd.is_binary_reason() {
                reason_lit = Literal(binary_reason_lit(other_vd.reason));
                self.stats.jumped_reasons += 1;
            }
        }
        let dl = self.decision_level;
        // SAFETY: the only call site passes an unassigned blocker from a live
        // binary watcher. The watch/rebuild invariant keeps that literal below
        // `2 * num_vars`, so its variable indexes phase/VarData; shortening
        // `reason_lit` changes only encoded reason data. One trail entry per
        // assigned variable gives `trail.len() < num_vars`, and the BCP entry
        // reserved at least `num_vars` slots before this unchecked push.
        unsafe {
            self.assign_bcp_unchecked(
                lit,
                dl,
                make_binary_reason(reason_lit.0),
                VarData::FLAG_BINARY_REASON_PUB,
            );
        }
    }
}
