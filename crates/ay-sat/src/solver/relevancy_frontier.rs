// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental maintenance of the CNF relevancy frontier
//! (#relevancy-frontier-incremental).
//!
//! # Why
//!
//! `relevancy::fill_relevancy_frontier` recomputed the frontier from scratch at
//! EVERY decision: `arena.live_indices()` walks the whole arena by clause
//! headers and then every literal of every live clause, i.e. O(clauses x
//! literals) per decision. On the `inc_some_list` dual-vocabulary obligation
//! (`crates/ay-dpll/tests/fixtures/dt_uf_bridge_congruence_inc_some_list.smt2`,
//! 60 s budget) that walk was **66% of the whole process profile**: 11279
//! samples in `pick_relevancy_frontier_decision` (the fill inlines into it)
//! plus 3665 in `clause_arena::arena_walk_step`, out of 22621 main-thread
//! samples (`/usr/bin/sample`, 10 ms interval, 2026-08-22). The relevancy
//! brancher engages only once the search WANDERS (>= 200 conflicts and
//! decisions/conflicts >= 5 — `relevancy::relevancy_should_engage`), which is
//! precisely the regime with the most decisions to pay that walk on.
//!
//! # What is maintained
//!
//! The frontier is
//!
//! ```text
//! { v : v UNASSIGNED, not lifecycle-removed,
//!       and v occurs in at least one LIVE clause with no TRUE literal }
//! ```
//!
//! so it is a function of two things only: which clauses are currently
//! satisfied, and which variables are currently assigned/removed. This module
//! keeps
//!
//! * `true_count[offset]` — number of currently-TRUE literals in the clause at
//!   `offset`; `== 0` is exactly "unsatisfied".
//! * `var_unsat[v]` — number of (unsatisfied clause, literal occurrence) pairs
//!   for variable `v`. Occurrences count with multiplicity (a tautological
//!   clause holding both `x` and `~x` contributes 2 to `x`); only `> 0` is ever
//!   read and the increments/decrements are symmetric, so multiplicity cannot
//!   change the answer and skipping the dedup keeps the update loops branchless.
//! * `occ[lit]` — offsets of the clauses containing literal `lit`, so assigning
//!   `lit` finds exactly the clauses whose `true_count` changes.
//! * `buf[v]` — the materialised frontier handed to
//!   `pick_domain_restricted_decision`, and `size`, its popcount.
//!
//! A clause moves the frontier only when its `true_count` crosses 0<->1, so the
//! per-event cost is `|occ(lit)|` plus the length of the clauses that flip.
//!
//! # Which events are tracked, and which invalidate
//!
//! * **assignment** — folded LAZILY at the next frontier query, from the trail
//!   suffix `trail[synced_len..]`. Nothing is hooked into `enqueue`/BCP: the
//!   trail IS the assignment, it only ever grows by push, and a decision point
//!   is exactly where the frontier is read. That keeps the twelve hand-tuned
//!   `enqueue*` variants and the raw-pointer/JIT BCP kernels untouched.
//! * **unassignment** — hooked in `backtrack_core` / `backtrack_ic3`, the only
//!   two functions that unassign. Backtracking also COMPACTS the trail (chrono
//!   backtracking keeps out-of-order lower-level literals), so the hook also
//!   recomputes `synced_len` as "how many folded literals survived", which is
//!   well defined because compaction preserves trail order. Both hooks open
//!   the fold through `begin_unassign_fold`, which re-checks the epoch and the
//!   arena watermarks exactly as `sync` does and DROPS the cache rather than
//!   walk offsets the formula has moved out from under: a backtrack is not a
//!   clause-DB event, but an epoch-bumping mutation can sit between the query
//!   that synced the cache and the backtrack that folds out of it.
//! * **clause add** — a pure arena append, detected by the arena word-length
//!   watermark and folded in at the next query.
//! * **every other clause-DB event** — delete, `replace` strengthening, the
//!   garbage / pending-garbage flags, arena compaction, in-place `literals_mut`
//!   writes — bumps `ClauseArena::formula_epoch`, and an epoch change forces a
//!   full rebuild. A rebuild is the same walk the old code did on EVERY
//!   decision, so even a pathological invalidation rate degrades to a small
//!   constant times the old cost, never to anything unsound. Restarts need no
//!   hook of their own: a restart is a `backtrack(0)`.
//! * **solver-level resets** that rewrite the trail or the arena outside
//!   backtrack (`preprocess_reset`, `flip_to_none`, `lucky_scratch`, `warmup`,
//!   variable compaction, the assumption model pokes) call `invalidate()`.
//!
//! Three O(1) staleness guards catch anything a hook misses: `synced_len` may
//! never exceed `trail.len()`, the arena watermarks may never move backwards,
//! and the number of appended clauses folded in must equal the arena's own
//! `num_clauses()` delta. Any mismatch rebuilds. The guards are applied at BOTH
//! entry points into the incremental state — the query (`sync`) and the
//! unassignment fold (`begin_unassign_fold`) — because either can be the first
//! to touch the cache after a mutation.
//!
//! # Exactness
//!
//! `Solver::debug_assert_relevancy_frontier_exact` recomputes the frontier with
//! the original from-scratch walk (`fill_relevancy_frontier`, kept verbatim as
//! the reference) and asserts SET EQUALITY with `buf`, plus agreement on the
//! empty-frontier SAT signal. WHICH decision the picker returns is unchanged by
//! construction: it is still `pick_domain_restricted_decision(&buf)` over the
//! same `buf`.
//!
//! It is asserted at TWO points, not one:
//!
//! * at the query (`pick_relevancy_frontier_decision`), against the synced
//!   `buf`; and
//! * at the END OF EVERY BACKTRACK that folded, against the state the
//!   unassignment fold just produced — via `debug_fold_to_current_strict`,
//!   which completes the fold with every staleness fallback replaced by an
//!   assertion.
//!
//! The second point is what gives the first its weight. `sync` REBUILDS from
//! scratch whenever the epoch moved, so any corruption a fold inflicted after
//! an epoch-bumping mutation is erased before a query-time check can observe
//! it; only a check that runs between the fold and the next rebuild can see
//! that class at all. `fold_unassign` additionally asserts the epoch outright,
//! so the failure is reported at the offending fold rather than as a set
//! difference several events later.
//!
//! Both run on EVERY engaged decision / folding backtrack under
//! `--features relevancy-frontier-invariants` (which, unlike `debug_assert!`,
//! is honoured in a `--release` build too), and on the first
//! `DEFAULT_DEBUG_CHECKS` of each solver in any `debug_assertions` build.

use super::*;

/// Engaged decisions / folding backtracks cross-checked against the
/// from-scratch walk per solver in a plain `debug_assertions` build.
///
/// The check is O(clauses x literals) — it reinstates exactly the cost this
/// module removes — so running it unconditionally would leave every debug build
/// as slow as the code being replaced (66% of the `inc_some_list` profile). A
/// bounded prefix still covers every structural transition that could desync
/// the state (initial rebuild, clause adds, backtracks, restarts, epoch
/// invalidations) on every unit test in the suite, which is well under this
/// budget; `--features relevancy-frontier-invariants` checks EVERY engaged
/// decision for the full-suite proof runs.
#[cfg(all(debug_assertions, not(feature = "relevancy-frontier-invariants")))]
const DEFAULT_DEBUG_CHECKS: u32 = 4096;

/// Incremental CNF relevancy frontier. See the module docs.
#[derive(Default)]
pub(super) struct RelevancyFrontier {
    /// Frontier membership by variable index — the buffer handed to
    /// `pick_domain_restricted_decision`. Empty while `valid` is false.
    buf: Vec<bool>,
    /// Popcount of `buf`. `size == 0` is the empty-frontier SAT signal.
    size: usize,
    /// Per-variable count of unsatisfied-clause literal occurrences.
    var_unsat: Vec<u32>,
    /// Per-clause count of TRUE literals, indexed by arena WORD OFFSET. Sparse
    /// (only clause-header offsets are meaningful); indexing by offset keeps
    /// the update path free of an offset-to-dense-id map.
    true_count: Vec<u32>,
    /// Clause offsets per literal index (`2*var + sign`).
    occ: Vec<Vec<u32>>,
    /// Length of the trail prefix already folded into the counters.
    synced_len: usize,
    /// `arena.len()` at the last fold — the append watermark.
    arena_words: usize,
    /// `arena.num_clauses()` at the last fold — cross-checks the append count.
    arena_clauses: usize,
    /// `arena.formula_epoch()` at the last fold.
    epoch: u64,
    /// `solver.num_vars` at the last rebuild.
    num_vars: usize,
    /// False until the first rebuild, and after any invalidating event.
    valid: bool,
    /// From-scratch cross-checks already spent at the QUERY (plain debug builds
    /// only).
    #[cfg(all(debug_assertions, not(feature = "relevancy-frontier-invariants")))]
    debug_checks_done: u32,
    /// From-scratch cross-checks already spent at the UNASSIGNMENT FOLD (plain
    /// debug builds only). A budget of its own, not a share of
    /// `debug_checks_done`: the two checks cover different failure modes (a
    /// query-time desync vs. a fold over a moved formula) and backtracks
    /// outnumber engaged decisions, so a shared counter would let the fold
    /// checks eat the query coverage the original pin relied on.
    #[cfg(all(debug_assertions, not(feature = "relevancy-frontier-invariants")))]
    debug_fold_checks_done: u32,
}

mod folds;

impl RelevancyFrontier {
    /// Drop all cached state; the next query rebuilds from `live_indices()`.
    ///
    /// Called from every path that rewrites the trail or the arena outside the
    /// two hooked backtracks. Always safe: a rebuild IS the original algorithm.
    pub(super) fn invalidate(&mut self) {
        self.valid = false;
        self.synced_len = 0;
        self.size = 0;
        // Release the per-offset / per-literal tables: an invalidation usually
        // means the arena just shrank or was rebuilt, and a stale `true_count`
        // sized to the OLD arena is pure footprint.
        self.buf.clear();
        self.var_unsat.clear();
        self.true_count.clear();
        for occ in &mut self.occ {
            occ.clear();
        }
    }

    /// Open an unassignment fold, or drop the cache when the live formula
    /// moved under it.
    ///
    /// THE ONLY entry point into `fold_unassign`. `occ` holds arena WORD
    /// OFFSETS and `true_count` is indexed by them, so both are meaningful
    /// only while every existing clause holds still. A backtrack is not a
    /// clause-DB event, but an epoch-bumping mutation — `reduce_db`'s
    /// deletions, a `replace` strengthening, and above all
    /// `compact_arena_locality`, which rewrites the arena into a SHORTER one
    /// where every offset moves — can land between the query that synced this
    /// cache and the backtrack that folds out of it. `sync()` already refuses
    /// to fold across that; the unassign fold must refuse identically, or it
    /// walks offsets that no longer denote the clauses they were recorded for
    /// (measured: `index out of bounds: the len is 37709 but the index is
    /// 48956` inside `ClauseArena::lit_len_raw`, on a 200-variable random
    /// 3-SAT at ratio 4.35 — see `tests/relevancy_frontier.rs`,
    /// `incremental_frontier_survives_arena_compaction_between_sync_and_backtrack`).
    ///
    /// Returns `None` — after dropping the cache, so the next query rebuilds —
    /// when there is nothing cached or the formula moved; otherwise `Some(len)`
    /// where `len` is the folded trail prefix the caller may fold out of.
    /// Scalar arguments (not `&Solver`) so the caller can read them off the
    /// arena while holding `&mut self.relevancy_frontier`.
    #[inline]
    pub(super) fn begin_unassign_fold(
        &mut self,
        arena_epoch: u64,
        arena_words: usize,
        arena_clauses: usize,
    ) -> Option<usize> {
        if !self.valid {
            return None;
        }
        if self.epoch != arena_epoch
            || self.arena_words > arena_words
            || self.arena_clauses > arena_clauses
        {
            self.invalidate();
            return None;
        }
        Some(self.synced_len)
    }

    /// Record the surviving folded prefix length after a trail compaction.
    #[inline]
    pub(super) fn set_synced_len(&mut self, len: usize) {
        if !self.valid {
            return;
        }
        debug_assert!(
            len <= self.synced_len,
            "BUG: backtrack grew the folded trail prefix ({} -> {len})",
            self.synced_len
        );
        self.synced_len = len;
    }

    /// The materialised frontier.
    #[inline]
    pub(super) fn buf(&self) -> &[bool] {
        &self.buf
    }

    /// Bring the cached frontier up to date with `s`; returns whether any
    /// variable is relevant.
    pub(super) fn sync(&mut self, s: &Solver) -> bool {
        if !self.valid
            || self.num_vars != s.num_vars
            || self.epoch != s.arena.formula_epoch()
            || self.arena_words > s.arena.len()
            || self.arena_clauses > s.arena.num_clauses()
            || self.synced_len > s.trail.len()
        {
            self.rebuild(s);
            return self.size > 0;
        }

        // Order matters: fold the assignment delta FIRST, against occurrence
        // lists that do not yet mention the appended clauses, and only then
        // seed those clauses straight from `vals`. The other order would count
        // the new trail literals twice for every appended clause.
        while self.synced_len < s.trail.len() {
            let lit = s.trail[self.synced_len];
            self.synced_len += 1;
            self.fold_assign(s, lit);
        }
        if self.arena_words < s.arena.len() && !self.fold_appended_clauses(s) {
            self.rebuild(s);
        }
        self.size > 0
    }

    /// Advance the cache to the CURRENT solver state exactly as [`Self::sync`]
    /// does, but with EVERY staleness fallback replaced by an assertion.
    ///
    /// This is the exactness pin's entry point (#relevancy-frontier-incremental
    /// blocker 2). `sync` rebuilds from scratch whenever the epoch moved, which
    /// ERASES any corruption an unguarded fold inflicted before the pin could
    /// compare anything — the reason "the suite is green under
    /// `--features relevancy-frontier-invariants`" did not, on its own, cover
    /// the stale-offset fold. Called straight off the backtrack unassignment
    /// fold, before any rebuild can run, it asserts instead of recovering.
    ///
    /// Folding the trail suffix here is not a behaviour change: it is precisely
    /// the work the next `sync` would do, in the same order, so the state and
    /// the frontier it yields are identical either way — only the moment the
    /// work happens moves.
    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    pub(super) fn debug_fold_to_current_strict(&mut self, s: &Solver) -> bool {
        assert!(
            self.valid,
            "BUG: relevancy frontier exactness pin ran on an invalidated cache",
        );
        assert_eq!(
            self.num_vars, s.num_vars,
            "BUG: incremental relevancy frontier survived a num_vars change",
        );
        assert_eq!(
            self.epoch,
            s.arena.formula_epoch(),
            "BUG: incremental relevancy frontier survived a live-formula \
             mutation (cached epoch {} != arena epoch {}); every offset in \
             `occ`/`true_count` may now denote a different clause",
            self.epoch,
            s.arena.formula_epoch(),
        );
        assert!(
            self.arena_words <= s.arena.len(),
            "BUG: incremental relevancy frontier arena watermark moved backwards \
             ({} > {})",
            self.arena_words,
            s.arena.len(),
        );
        assert!(
            self.arena_clauses <= s.arena.num_clauses(),
            "BUG: incremental relevancy frontier clause watermark moved backwards \
             ({} > {})",
            self.arena_clauses,
            s.arena.num_clauses(),
        );
        assert!(
            self.synced_len <= s.trail.len(),
            "BUG: incremental relevancy frontier folded prefix ({}) exceeds the \
             trail ({})",
            self.synced_len,
            s.trail.len(),
        );
        while self.synced_len < s.trail.len() {
            let lit = s.trail[self.synced_len];
            self.synced_len += 1;
            self.fold_assign(s, lit);
        }
        if self.arena_words < s.arena.len() {
            assert!(
                self.fold_appended_clauses(s),
                "BUG: incremental relevancy frontier appended-clause count \
                 disagrees with the arena's own num_clauses() delta",
            );
        }
        self.size > 0
    }

    /// Rebuild every table from `arena.live_indices()` — the original
    /// from-scratch algorithm, now run once per invalidating event instead of
    /// once per decision.
    fn rebuild(&mut self, s: &Solver) {
        let num_vars = s.num_vars;
        self.buf.clear();
        self.buf.resize(num_vars, false);
        self.var_unsat.clear();
        self.var_unsat.resize(num_vars, 0);
        self.true_count.clear();
        self.true_count.resize(s.arena.len(), 0);
        self.occ.resize_with(num_vars * 2, Vec::new);
        for occ in &mut self.occ {
            occ.clear();
        }
        self.size = 0;

        for off in s.arena.live_indices() {
            let lits = s.arena.literals(off);
            let mut true_lits = 0u32;
            for &lit in lits {
                if s.lit_val(lit) > 0 {
                    true_lits += 1;
                }
                let li = lit.index();
                if li < self.occ.len() {
                    self.occ[li].push(off as u32);
                }
            }
            self.true_count[off] = true_lits;
            if true_lits != 0 {
                continue;
            }
            for &lit in lits {
                let v = lit.variable().index();
                if v < num_vars {
                    self.var_unsat[v] += 1;
                }
            }
        }

        for v in 0..num_vars {
            if self.var_unsat[v] > 0
                && ay_prefetch::val_at(&s.vals, v * 2) == 0
                && !s.var_lifecycle.is_removed(v)
            {
                self.buf[v] = true;
                self.size += 1;
            }
        }

        self.synced_len = s.trail.len();
        self.arena_words = s.arena.len();
        self.arena_clauses = s.arena.num_clauses();
        self.epoch = s.arena.formula_epoch();
        self.num_vars = num_vars;
        self.valid = true;
    }

    /// Whether this engaged decision should be cross-checked against the
    /// from-scratch walk. Always, under the invariants feature; otherwise the
    /// first `DEFAULT_DEBUG_CHECKS` engaged decisions of this solver.
    #[cfg(feature = "relevancy-frontier-invariants")]
    #[inline]
    pub(super) fn take_debug_check(&mut self) -> bool {
        true
    }

    #[cfg(all(debug_assertions, not(feature = "relevancy-frontier-invariants")))]
    #[inline]
    pub(super) fn take_debug_check(&mut self) -> bool {
        if self.debug_checks_done >= DEFAULT_DEBUG_CHECKS {
            return false;
        }
        self.debug_checks_done += 1;
        true
    }

    /// Same, for the post-unassignment-fold check. Separate budget — see
    /// `debug_fold_checks_done`.
    #[cfg(feature = "relevancy-frontier-invariants")]
    #[inline]
    pub(super) fn take_debug_fold_check(&mut self) -> bool {
        true
    }

    #[cfg(all(debug_assertions, not(feature = "relevancy-frontier-invariants")))]
    #[inline]
    pub(super) fn take_debug_fold_check(&mut self) -> bool {
        if self.debug_fold_checks_done >= DEFAULT_DEBUG_CHECKS {
            return false;
        }
        self.debug_fold_checks_done += 1;
        true
    }
}
