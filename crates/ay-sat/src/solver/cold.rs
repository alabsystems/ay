// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boxed cold solver state for BCP cache locality (#5090).
//!
//! The hot and warm portions of `Solver` stay inline in `state.rs`. The full
//! cold tail lives here behind a single box so restart/proof/incremental/
//! tracing state no longer inflates the main solver shell.

use super::*;

pub(super) const BCP_LEARNED_1963_BLOCKER_CERT_ELISION_ENV: &str =
    "AY_SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION";
pub(super) const BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ENV: &str =
    "AY_SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW";
pub(super) const BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE_ENV: &str =
    "AY_SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE";

#[inline]
pub(super) fn bcp_learned_1963_blocker_cert_elision_env_enabled() -> bool {
    #[cfg(not(test))]
    {
        static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *ENABLED.get_or_init(|| {
            std::env::var(BCP_LEARNED_1963_BLOCKER_CERT_ELISION_ENV).is_ok_and(|value| value == "1")
        })
    }

    #[cfg(test)]
    {
        std::env::var(BCP_LEARNED_1963_BLOCKER_CERT_ELISION_ENV).is_ok_and(|value| value == "1")
    }
}

#[inline]
pub(super) fn bcp_learned_1963_blocker_cert_shadow_env_enabled() -> bool {
    #[cfg(not(test))]
    {
        static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *ENABLED.get_or_init(|| {
            std::env::var(BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ENV).is_ok_and(|value| value == "1")
        })
    }

    #[cfg(test)]
    {
        std::env::var(BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ENV).is_ok_and(|value| value == "1")
    }
}

#[inline]
pub(super) fn bcp_learned_1963_blocker_cert_false_reject_demote_env_enabled() -> bool {
    #[cfg(not(test))]
    {
        static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *ENABLED.get_or_init(|| {
            std::env::var(BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE_ENV)
                .is_ok_and(|value| value == "1")
        })
    }

    #[cfg(test)]
    {
        std::env::var(BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE_ENV)
            .is_ok_and(|value| value == "1")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ModeLock {
    None,
    Stable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ReduceCandidate {
    pub(super) rank: u64,
    pub(super) clause_idx: usize,
    pub(super) pressure_adjusted: bool,
    pub(super) pressure_retained: bool,
    pub(super) pressure_steps: u64,
}

/// Flat arena for the immutable original-clause ledger.
///
/// Replaces `Vec<Vec<Literal>>` to eliminate N separate heap allocations
/// and N Vec headers (24 bytes each). All literals are stored contiguously
/// with a parallel offset table for O(1) clause access.
///
/// Memory savings for 40K clauses: ~960KB (from ~2.0MB to ~640KB).
#[derive(Clone)]
pub(crate) struct OriginalLedger {
    /// All original clause literals stored contiguously.
    literals: Vec<Literal>,
    /// Start offset (into `literals`) of each clause. Length = num_clauses.
    /// Clause `i` spans `literals[offsets[i] as usize .. end]` where
    /// `end = offsets[i+1]` (or `literals.len()` for the last clause).
    offsets: Vec<u32>,
    /// Stack of (num_clauses, num_literals) snapshots at each push() scope.
    /// On pop(), the ledger is truncated back to the most recent snapshot,
    /// removing clauses that were added inside the scope (#8472).
    scope_starts: Vec<(usize, usize)>,
    /// Global clauses buffered during push scopes (#8546).
    ///
    /// When `push_clause_global` is called inside a scope, the clause is
    /// appended to the main ledger for immediate use AND stored here for
    /// replay after `pop_scope` truncation. On `pop_scope`, the main ledger
    /// is truncated (removing both scoped and global clauses), then the
    /// buffered global clauses are replayed into the main ledger.
    ///
    /// Each scope level maintains its own buffer range. When an inner scope
    /// is popped, its globals are replayed into the main ledger and then
    /// promoted to the parent scope's buffer (so they also survive the
    /// parent's pop).
    pending_global_clauses: Vec<Literal>,
    /// Offsets into `pending_global_clauses` for each buffered clause.
    pending_global_offsets: Vec<u32>,
    /// Stack of buffer-size snapshots: `pending_global_offsets.len()` at each
    /// `push_scope`. On `pop_scope`, only clauses added in the popped scope
    /// (indices >= snapshot) are replayed; earlier entries belong to outer
    /// scopes and are kept for their pop.
    pending_global_scope_starts: Vec<usize>,
}

impl OriginalLedger {
    pub(crate) fn new() -> Self {
        Self {
            literals: Vec::new(),
            offsets: Vec::new(),
            scope_starts: Vec::new(),
            pending_global_clauses: Vec::new(),
            pending_global_offsets: Vec::new(),
            pending_global_scope_starts: Vec::new(),
        }
    }

    /// Append a clause to the ledger.
    #[inline]
    pub(crate) fn push_clause(&mut self, lits: &[Literal]) {
        debug_assert!(
            u32::try_from(self.literals.len()).is_ok(),
            "BUG: OriginalLedger literal count overflows u32"
        );
        self.offsets.push(self.literals.len() as u32);
        self.literals.extend_from_slice(lits);
    }

    /// Append a global clause that survives `pop_scope` (#9378, #8546).
    ///
    /// When inside a push scope, the clause is appended to the main ledger
    /// for immediate use AND buffered in `pending_global_clauses`. On
    /// `pop_scope`, after truncation removes all scoped clauses (including
    /// the global clause's main-ledger copy), the buffered global clauses
    /// are replayed into the main ledger.
    ///
    /// **Bug fix (#8546):** The previous implementation shifted scope
    /// boundaries forward with `max()`, which also protected scoped clauses
    /// from truncation. The buffer-and-replay approach cleanly separates
    /// global clauses from scoped ones.
    ///
    /// When NOT inside a scope, this is equivalent to `push_clause`.
    #[inline]
    pub(crate) fn push_clause_global(&mut self, lits: &[Literal]) {
        if self.scope_starts.is_empty() {
            // No active scope — append directly to the main ledger.
            self.push_clause(lits);
        } else {
            // Inside a scope — add to main ledger for immediate use,
            // AND buffer for replay after pop_scope truncation.
            self.push_clause(lits);
            self.pending_global_offsets
                .push(self.pending_global_clauses.len() as u32);
            self.pending_global_clauses.extend_from_slice(lits);
            // Do NOT shift scope boundaries. The main-ledger copy will be
            // removed by pop_scope truncation, and the buffered copy will
            // be replayed afterward.
        }
    }

    /// Get clause at `index` as a slice.
    #[inline]
    pub(crate) fn clause(&self, index: usize) -> &[Literal] {
        debug_assert!(
            index < self.offsets.len(),
            "BUG: clause index out of bounds"
        );
        let start = self.offsets[index] as usize;
        let end = if index + 1 < self.offsets.len() {
            self.offsets[index + 1] as usize
        } else {
            self.literals.len()
        };
        &self.literals[start..end]
    }

    /// Number of clauses in the ledger.
    #[inline]
    pub(crate) fn num_clauses(&self) -> usize {
        self.offsets.len()
    }

    /// Whether the ledger is empty.
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.offsets.is_empty()
    }

    /// Record the current ledger size as a scope boundary (#8472).
    ///
    /// Called by `Solver::push()`. The snapshot is (num_clauses, num_literals)
    /// at scope entry. `pop_scope()` truncates back to this point.
    #[inline]
    pub(crate) fn push_scope(&mut self) {
        self.scope_starts
            .push((self.offsets.len(), self.literals.len()));
        // Record pending-global buffer size so pop_scope replays only this
        // scope's globals (#8546).
        self.pending_global_scope_starts
            .push(self.pending_global_offsets.len());
    }

    /// Truncate the ledger back to the most recent scope boundary (#8472).
    ///
    /// Called by `Solver::pop()` when scoped clauses are being reclaimed.
    /// Removes all clauses added since the matching `push_scope()`, including
    /// the scope-selector unit clause `[+selector]` added by pop() itself
    /// (which is no longer needed once the scoped clauses are removed).
    ///
    /// Global clauses added via `push_clause_global` during the scope are
    /// buffered in `pending_global_clauses`. After truncation removes all
    /// scoped clauses (and the main-ledger copy of the global clause),
    /// the buffered global clauses from this scope level are replayed into
    /// the main ledger (#8546). If outer scopes remain, the replayed
    /// globals are also kept in the buffer for subsequent pops.
    ///
    /// Returns `true` if the ledger was truncated, `false` if there was no
    /// active scope (should not happen in correct usage).
    #[inline]
    pub(crate) fn pop_scope(&mut self) -> bool {
        let Some((clause_count, literal_count)) = self.scope_starts.pop() else {
            return false;
        };
        // Recover the pending-global buffer snapshot for this scope level.
        // `global_start` is the index into `pending_global_offsets` at the
        // time this scope was pushed. Only globals from index `global_start`
        // onward were added in this scope (or inner scopes). Globals before
        // `global_start` belong to outer scopes and were already in the
        // ledger before our scope boundary — they survive truncation.
        let global_start = self.pending_global_scope_starts.pop().unwrap_or(0);

        self.offsets.truncate(clause_count);
        self.literals.truncate(literal_count);

        // Replay buffered global clauses from THIS scope level and deeper.
        // Only clauses at index >= global_start were added after our push,
        // so only they were removed by truncation. Earlier globals (from
        // outer scopes) are still present in the main ledger.
        //
        // Inline push_clause logic to avoid borrowing conflict (can't borrow
        // self.pending_global_clauses immutably and self.offsets/literals
        // mutably at the same time).
        let num_pending = self.pending_global_offsets.len();
        for i in global_start..num_pending {
            let start = self.pending_global_offsets[i] as usize;
            let end = if i + 1 < num_pending {
                self.pending_global_offsets[i + 1] as usize
            } else {
                self.pending_global_clauses.len()
            };
            // Inline push_clause: append offset + copy literals.
            self.offsets.push(self.literals.len() as u32);
            self.literals
                .extend_from_slice(&self.pending_global_clauses[start..end]);
        }

        // If all scopes are popped, clear the pending buffer entirely.
        // If outer scopes remain, keep the buffer — the globals will be
        // needed again on the next pop.
        if self.scope_starts.is_empty() {
            self.pending_global_clauses.clear();
            self.pending_global_offsets.clear();
            self.pending_global_scope_starts.clear();
        }

        true
    }

    /// Number of active scope boundaries.
    #[inline]
    pub(crate) fn scope_depth(&self) -> usize {
        self.scope_starts.len()
    }

    /// Iterate over all clauses as slices.
    pub(crate) fn iter_clauses(&self) -> OriginalLedgerIter<'_> {
        OriginalLedgerIter {
            ledger: self,
            index: 0,
        }
    }

    /// Iterate over clauses starting from `start` index.
    pub(crate) fn iter_clauses_from(&self, start: usize) -> OriginalLedgerIter<'_> {
        debug_assert!(
            start <= self.offsets.len(),
            "BUG: iter_clauses_from start ({start}) > num_clauses ({})",
            self.offsets.len()
        );
        OriginalLedgerIter {
            ledger: self,
            index: start,
        }
    }

    /// Heap bytes used by this ledger (for memory stats).
    ///
    /// Exposed in production (not `#[cfg(test)]`) so the clause-DB byte-limit
    /// trigger (`Solver::should_reduce_db`) can account for the immutable
    /// original-formula ledger in addition to the arena (#8672).
    pub(crate) fn heap_bytes(&self) -> usize {
        self.literals.capacity() * size_of::<Literal>() + self.offsets.capacity() * size_of::<u32>()
    }

    /// Collect all clauses to Vec<Vec<Literal>> (for tests/debug).
    #[cfg(test)]
    pub(crate) fn to_vec_of_vecs(&self) -> Vec<Vec<Literal>> {
        self.iter_clauses().map(<[Literal]>::to_vec).collect()
    }
}

/// Iterator over clauses in an `OriginalLedger`.
pub(crate) struct OriginalLedgerIter<'a> {
    ledger: &'a OriginalLedger,
    index: usize,
}

impl<'a> Iterator for OriginalLedgerIter<'a> {
    type Item = &'a [Literal];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.ledger.offsets.len() {
            return None;
        }
        let clause = self.ledger.clause(self.index);
        self.index += 1;
        Some(clause)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.ledger.offsets.len().saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for OriginalLedgerIter<'_> {}

/// Cold solver state that is not needed on the BCP fast path.
pub(crate) struct ColdState {
    // Glucose-style EMA restart state (ADAM bias-corrected, CaDiCaL ema.cpp)
    /// Bias-corrected fast EMA of LBD (short window, ~32 conflicts)
    pub(super) lbd_ema_fast: f64,
    /// Bias-corrected slow EMA of LBD (long window, ~100K conflicts)
    pub(super) lbd_ema_slow: f64,
    /// Raw (biased) fast EMA before correction
    pub(super) lbd_ema_fast_biased: f64,
    /// Raw (biased) slow EMA before correction
    pub(super) lbd_ema_slow_biased: f64,
    /// Bias correction exponent: beta_fast^n (decays toward 0)
    pub(super) lbd_ema_fast_exp: f64,
    /// Bias correction exponent: beta_slow^n (decays toward 0)
    pub(super) lbd_ema_slow_exp: f64,
    pub(super) saved_lbd_ema_fast: f64,
    pub(super) saved_lbd_ema_slow: f64,
    pub(super) saved_lbd_ema_fast_biased: f64,
    pub(super) saved_lbd_ema_slow_biased: f64,
    pub(super) saved_lbd_ema_fast_exp: f64,
    pub(super) saved_lbd_ema_slow_exp: f64,
    pub(super) ema_swapped: bool,
    /// Whether to use Glucose-style restarts (true) or Luby restarts (false)
    pub(super) glucose_restarts: bool,
    /// Theory conflict ratio EMA (fraction of conflicts from theory/extension).
    /// Updated by `update_theory_conflict_ratio()` on every conflict. When this
    /// exceeds `THEORY_CONFLICT_RATIO_THRESHOLD` (0.8), the solver switches to
    /// Luby restarts with a longer base interval (`THEORY_LUBY_BASE`), giving
    /// the theory solver more time to propagate before restarting. This matches
    /// Z3's approach of using geometric (slow-growth) restarts for QF_LRA.
    /// (#8452)
    pub(super) theory_conflict_ratio: f64,
    /// Total extension/theory-originated conflicts, tracked for ratio computation.
    /// Incremented by `ext_conflict.rs:handle_ext_conflict` and the extension
    /// callback conflict paths.
    pub(super) ext_conflict_count: u64,
    /// Separate Luby index for theory-aware restarts (#8452).
    /// Uses its own counter (starting at 1) instead of sharing the global
    /// `luby_idx`. The global `luby_idx` is incremented by every restart
    /// (including frequent Glucose EMA restarts in focused mode), so by the
    /// time theory mode activates, `luby_idx` can be 50+, producing large
    /// Luby values that make `THEORY_LUBY_BASE * Luby(luby_idx)` enormous
    /// and effectively disable restarts for theory-dominated problems.
    pub(super) theory_luby_idx: u32,
    /// Trail-length EMA (slow) for restart blocking (Audemard & Simon SAT 2012).
    pub(super) trail_ema_slow: f64,
    /// Number of trail EMA updates (for warmup gating).
    pub(super) trail_ema_count: u64,
    /// Count of consecutive focused-mode EMA restarts (#8360).
    /// When the Glucose EMA fires on every restart for many consecutive
    /// restarts, it is not providing useful quality information (the formula
    /// has uniformly high LBD). After FOCUSED_EMA_CONSEC_THRESHOLD
    /// consecutive fires, the conflict gate is raised from RESTART_INTERVAL
    /// to num_vars/4 (capped at 100), allowing the solver to build deeper
    /// trails. Reset to 0 when the EMA does NOT fire.
    pub(super) consecutive_ema_restarts: u64,
    /// Whether to use geometric restart schedule (overrides glucose/Luby when true).
    /// Z3 uses geometric restarts for QF_LRA: next_restart = initial * factor^n.
    pub(super) geometric_restarts: bool,
    /// Initial restart interval for geometric restarts (conflicts). Z3 default: 100.
    pub(super) geometric_initial: f64,
    /// Growth factor for geometric restarts. Z3 default: 1.1.
    pub(super) geometric_factor: f64,
    /// Minimum conflicts before considering restart (initial stabilization)
    pub(super) restart_min_conflicts: u64,
    /// Minimum conflicts since last restart before stable-mode EMA can fire.
    /// Default: STABLE_EMA_MIN_CONFLICTS (50). Set to u64::MAX to disable
    /// stable-mode EMA entirely (pure reluctant doubling, matching CaDiCaL).
    /// On small dense UNSAT formulas (clique_n2_k10: 180 vars, density 17.5),
    /// the EMA fires pathologically because LBD quality is structurally poor,
    /// causing 93K restarts vs Kissat's 14K (#8466).
    pub(super) stable_ema_gate: u64,
    /// Minimum conflicts since last restart before focused-mode EMA can fire.
    /// Default: RESTART_INTERVAL (2). For small dense formulas where the
    /// Glucose EMA always fires (uniformly bad LBD), a higher gate reduces
    /// restart frequency to match Kissat's ~40 conflicts/restart (#8466).
    pub(super) focused_restart_gate: u64,
    /// Default-off dense-mutex focused restart gate experiment (#9164).
    ///
    /// When enabled by routing/config, the existing small-dense startup tuning
    /// raises the focused gate to `max(40, min(100, active_vars / 4))` only on
    /// dense binary-heavy mutex/clique-shaped formulas.
    pub(super) dense_mutex_focused_restart_gate_experiment: bool,
    /// Current index into the Luby sequence
    pub(super) luby_idx: u32,
    /// Base restart interval (conflicts per Luby unit)
    pub(super) restart_base: u64,
    /// Total number of restarts performed
    pub(super) restarts: u64,
    /// Conflict count when stabilization mode was last switched (first phase only)
    pub(super) stable_mode_start_conflicts: u64,
    /// Configured initial stabilization phase length in conflicts.
    pub(super) stable_phase_init: u64,
    /// Length of current stabilization phase in conflicts (first phase only)
    pub(super) stable_phase_length: u64,
    /// Counter for stable phase number (used to increase phase length)
    pub(super) stable_phase_count: u64,
    /// Total number of stable/focused mode switches.
    /// Kissat uses this to inject deterministic focused-mode polarity cycles.
    pub(super) mode_switch_count: u64,
    /// Search-mode lock for SAT-tuned DIMACS profiles.
    pub(super) mode_lock: ModeLock,
    /// Cumulative ticks charged during probe BCP.
    /// CaDiCaL stats.ticks.probe (stats.hpp:36).
    pub(super) probe_ticks: u64,
    /// Cumulative ticks charged during vivify BCP.
    /// CaDiCaL stats.ticks.vivify.
    pub(super) vivify_ticks: u64,
    /// Tick increment for stabilization phases. 0 = not yet bootstrapped (first phase
    /// uses conflicts). After the first phase switch, bootstrapped from that phase's
    /// tick delta. CaDiCaL restart.cpp:53-54.
    pub(super) stabilize_tick_inc: u64,
    /// Focused-mode search ticks at the moment the current/most recent focused
    /// phase was entered (`AY_AB_MODE_EQUITICKS=1`, opt-in; 2026-07
    /// wf_0370e641 batch-3). Lets the stable-phase budget mirror Kissat
    /// mode.c `update_mode_limit`: each stable phase receives exactly the
    /// ticks the just-ended focused phase consumed, instead of the
    /// bootstrap-frozen `stabilize_tick_inc`.
    pub(super) focused_ticks_at_entry: u64,
    /// Cached equal-ticks band decision (None = not yet computed for this
    /// solve; recomputed after preprocess resets since the band uses the
    /// post-preprocess active clause count). See restart.rs equiticks block.
    pub(super) mode_equiticks_cached: Option<bool>,
    /// Branch heuristic selector mode.
    pub(super) branch_selector_mode: BranchSelectorMode,
    /// Restart-boundary MAB controller state.
    pub(super) branch_mab: MabController,
    /// Tick limit for the current stabilization phase (absolute tick count for the
    /// current mode). CaDiCaL restart.cpp:64.
    pub(super) stabilize_tick_limit: u64,
    /// Equiticks progress-gate (`AY_AB_EQT_PROGRESS`): conflict count at the most
    /// recent stable-mode `target_trail_len` improvement. Used to decide whether
    /// the stable frontier is still deepening when the equal-effort tick budget
    /// (`stabilize_tick_limit`) is reached, so a converging stable phase can be
    /// deferred past that budget (up to `stable_tick_hardcap`) instead of being
    /// starved. 0 = no improvement recorded yet in this phase. Inert unless the
    /// env gate is on AND equiticks is active. See restart.rs switch test.
    pub(super) last_target_improve_conflicts: u64,
    /// Equiticks progress-gate absolute ceiling: the nlogpow4 (default-schedule)
    /// tick budget for the current stable phase. A deferred stable phase never
    /// runs past this cap, so the gate can only ever bridge the equal-effort
    /// budget UP TO the default schedule — never further (bounds unbounded run).
    /// Only written when equiticks is active; 0 otherwise (inert).
    pub(super) stable_tick_hardcap: u64,
    /// Cached `AY_AB_EQT_PROGRESS` env decision (None = not yet read; inner 0 =
    /// disabled, >0 = the progress WINDOW in conflicts). Off by default: the
    /// progress-gated stable-phase extension is opt-in and only has any effect
    /// when `AY_AB_MODE_EQUITICKS` is also active. `AY_AB_EQT_PROGRESS=1` enables
    /// with the default window; `AY_AB_EQT_PROGRESS=<N>` (N>1) sets the window.
    pub(super) eqt_progress_cached: Option<u64>,
    /// Knuth reluctant doubling state u (see reference/cadical/src/reluctant.hpp)
    pub(super) reluctant_u: u64,
    /// Knuth reluctant doubling state v (current Luby sequence value)
    pub(super) reluctant_v: u64,
    /// Countdown: conflicts remaining before next reluctant restart fires
    pub(super) reluctant_countdown: u64,
    /// Conflict count at last reluctant tick (for delta computation)
    pub(super) reluctant_ticked_at: u64,
    /// When to next run clause deletion
    pub(super) next_reduce_db: u64,
    /// Total number of clause DB reductions performed.
    /// CaDiCaL: `stats.reductions` (reduce.cpp:216).
    pub(super) num_reductions: u64,
    /// Arena word-offset boundary: clauses at offsets < this are original (non-learned).
    pub(super) original_clause_boundary: usize,
    /// Reduction count at last inprocessing probe round.
    /// Used to skip redundant probe calls when no new reductions occurred.
    pub(super) last_inprobe_reduction: u64,
    /// Next conflict count at which to run inprocessing probe.
    /// CaDiCaL: `lim.inprobe` (probe.cpp:980-981).
    /// Formula: `conflicts + 10 * INPROBE_INTERVAL * floor_log10(phase + 9)`.
    pub(super) next_inprobe_conflict: u64,
    /// Optional clause-count divisor scaling the *incremental* inprocessing
    /// re-fire interval (#maxsat-inproc-throttle). `Some(n)` sets the interval
    /// to `clamp(500, num_clauses / n, cap)`; `None` keeps the legacy flat
    /// 500-conflict interval. Set by the MaxSAT engine (`Some(100)`) so it
    /// applies only to weighted/unweighted MaxSAT incremental solving, leaving
    /// IC3/SMT/CHC consumers on the legacy cadence. An `AY_SAT_INCR_INPROBE_DIV`
    /// env value, when present, overrides this field. Frequency-only, so it can
    /// never change a verdict.
    pub(super) incremental_inprobe_clause_divisor: Option<u64>,
    /// Number of completed inprocessing probe phases (for logarithmic interval growth).
    /// CaDiCaL: tracks `phases` in probe scheduling (probe.cpp:979-981).
    pub(super) inprobe_phases: u64,
    /// Cached result of `is_uniform_nonbinary_irredundant_formula()`.
    /// `None` = dirty (needs recomputation), `Some(v)` = cached result.
    /// Invalidated when irredundant clauses are added, deleted, or strengthened.
    /// Avoids O(total_clauses) iteration on every inprocessing call (#7905).
    pub(super) uniform_formula_cache: Option<bool>,
    /// Trail of learned clause arena offsets for eager subsumption.
    /// CaDiCaL walks backward through its `clauses` vector; AY uses this
    /// equivalent trail to find the most recently learned clauses.
    pub(super) learned_clause_trail: Vec<usize>,
    /// Number of clauses removed by eager subsumption (CaDiCaL `stats.eagersub`).
    pub(super) num_eager_subsumptions: u64,
    /// Conflict count at which to next run clause flush (CaDiCaL reduce.cpp:26-30).
    /// Flush is more aggressive than reduce -- marks ALL unused learned clauses
    /// as garbage regardless of tier. Grows geometrically by `FLUSH_FACTOR`.
    pub(super) next_flush: u64,
    /// Current flush interval increment (grows by `FLUSH_FACTOR` after each flush).
    pub(super) flush_inc: u64,
    /// Number of flush operations performed.
    pub(super) num_flushes: u64,
    /// Number of arena locality compactions performed (CaDiCaL arenatype=3, #8030).
    /// Incremented by `compact_arena_locality()` in `arena_gc.rs`.
    pub(super) num_arena_compactions: u64,
    /// Number of scoped clauses reclaimed by gc_scoped_clauses() during pop (#1444).
    /// Equivalent to Z3's gc_vars clause removal count.
    pub(super) scoped_clauses_reclaimed: u64,
    /// Number of learned clauses eagerly subsumed per-conflict (#5136).
    /// CaDiCaL: stats.eagersub (analyze.cpp:754).
    pub(super) eager_subsumed: u64,
    /// Maximum number of learned clauses (None = no limit).
    ///
    /// When exceeded, trigger aggressive clause database reduction.
    pub(super) max_learned_clauses: Option<usize>,
    /// Maximum clause database memory in bytes (None = no limit).
    ///
    /// When exceeded, trigger aggressive clause database reduction and arena compaction.
    pub(super) max_clause_db_bytes: Option<usize>,
    /// Absolute conflict budget: stop with `Unknown` once `num_conflicts`
    /// reaches this target (None = no budget). This is the deterministic,
    /// machine-independent analog of the wall-clock interrupt used to back
    /// the SMT-LIB `:rlimit` option (#8749). Unlike a timeout, the same
    /// formula and seed always stops at the same conflict count, so a caller
    /// that sets `:rlimit` gets reproducible termination rather than a result
    /// that depends on how fast the host happens to be.
    pub(super) conflict_budget: Option<u64>,
    /// Absolute decision budget: stop with `Unknown` once `num_decisions`
    /// reaches this target (None = no budget). Deterministic companion of
    /// `conflict_budget` for decision-heavy / conflict-light search regimes
    /// (#ground-determinism): theory-extension churn (e.g. the deductive-checks
    /// calc.rs seq-chain BV<->LIA bridge) makes hundreds of decisions per
    /// conflict, so a conflict budget alone cannot bound such work
    /// deterministically. Checked at the same deterministic checkpoints as
    /// the conflict budget (conflict sites, every 1000th decision, and the
    /// amortized loop-top).
    pub(super) decision_budget: Option<u64>,
    /// Bumpreason rate-limiting: decisions at last conflict (CaDiCaL saved_decisions).
    /// Used to compute per-conflict decision rate for reason bump gating.
    pub(super) bumpreason_saved_decisions: u64,
    /// Bumpreason rate-limiting: EMA of decisions per conflict (CaDiCaL averages.current.decisions).
    /// When this exceeds BUMPREASON_RATE_LIMIT (100), reason bumping is skipped.
    pub(super) bumpreason_decision_rate: f64,
    /// Bumpreason adaptive delay: remaining conflicts to skip before re-enabling.
    /// Per-mode array `[focused, stable]` matching CaDiCaL's `delay[stable].bumpreasons.limit`.
    /// Reason bumping adapts independently in each mode because focused mode has
    /// high decision rates (many bumps wasted) while stable mode has low rates
    /// (bumps are useful). A global counter would carry stale delay from one mode
    /// into the other after a mode switch.
    pub(super) bumpreason_delay_remaining: [u64; 2],
    /// Bumpreason adaptive delay: current interval (doubles on wasted bumps, halves on useful ones).
    /// Per-mode array `[focused, stable]` matching CaDiCaL's `delay[stable].bumpreasons.interval`.
    pub(super) bumpreason_delay_interval: [u64; 2],
    /// `search_ticks` at the last learned vivification round. The delta
    /// `search_ticks - last_vivify_ticks` determines the tick budget.
    pub(super) last_vivify_ticks: u64,
    /// `search_ticks` at the last irredundant vivification round.
    pub(super) last_vivify_irred_ticks: u64,
    /// Adaptive delay multiplier for irredundant vivification interval.
    pub(super) vivify_irred_delay_multiplier: u64,
    // Random decision injection (CaDiCaL-style)
    /// Countdown of remaining random decisions in current burst (0 = inactive)
    pub(super) randomized_deciding: u64,
    /// Number of random decision phases completed
    pub(super) random_decision_phases: u64,
    /// Conflict count at which the next random decision burst starts
    pub(super) next_random_decision: u64,
    /// Per-decision random variable frequency (Z3-style). 0.0 = disabled (default).
    /// Z3 default for SMT: 0.01 (1% of decisions are random).
    pub(super) random_var_freq: f64,
    /// BVE effort as per-mille of cumulative search propagations.
    pub(super) bve_effort_permille: u64,
    /// Subsumption effort as per-mille of cumulative search propagations.
    pub(super) subsume_effort_permille: u64,
    // Bounded Variable Elimination state
    /// Number of completed BVE phases (for CaDiCaL-style growing interval)
    pub(super) bve_phases: u32,
    /// Whether a subsumption pass has run since the last BVE phase (#8502).
    /// CaDiCaL elim.cpp:1043-1044: `last.elim.subsumephases == stats.subsumephases`.
    /// When false, the BVE entry point forces a subsumption round before
    /// elimination to simplify the formula. When true, the forced subsumption
    /// is skipped because subsumption already ran in the front half.
    pub(super) subsume_ran_since_bve: bool,
    /// fixed_count at last BVE run (fixpoint guard: skip if no new units)
    pub(super) last_bve_fixed: i64,
    /// Count of irredundant clause modification events from subsumption/vivification/decompose.
    /// CaDiCaL equivalent: `stats.mark.elim` (internal.hpp:1117-1124).
    /// BVE re-triggers when `last_bve_marked != bve_marked`.
    pub(super) bve_marked: u64,
    /// bve_marked at last BVE run (fixpoint guard).
    /// CaDiCaL equivalent: `last.elim.marked` (elim.cpp:79).
    pub(super) last_bve_marked: u64,
    /// Clause-count resume threshold for BVE.
    /// BVE stays disabled while the current clause count is at or above this
    /// value. After a shrinking phase this is the post-phase clause count;
    /// after a growing phase it remains the stricter pre-phase baseline.
    pub(super) last_bve_clauses: usize,
    /// fixed_count at last level-0 garbage collection (fixpoint guard: skip if no new units).
    /// CaDiCaL equivalent: `last.collect.fixed < stats.all.fixed` in collect.cpp.
    pub(super) last_collect_fixed: i64,
    /// Trail position at last occ-guided GC (#8097).
    pub(super) last_collect_trail_pos: usize,
    /// fixed_count when the FULL level-0 GC last completed (huge-arena batch
    /// deferral, #l0-gc-batch). Distinct from `last_collect_fixed`, which the
    /// lightweight variant also updates: this one moves only when the full
    /// pass actually runs, so the deferral window measures real pending work.
    pub(super) last_full_l0_gc_fixed: i64,
    /// Clause DB mutation counter (incremented by add/delete/replace during inprocessing).
    pub(super) clause_db_changes: u64,
    /// Cumulative BVE resolution count (for effort limiting, CaDiCaL: stats.elimres).
    pub(super) bve_resolutions: u64,
    // Factorization / SBVA extension variable tracking
    /// Index of the first extension variable (from factorization or SBVA).
    /// All variables with index >= this value are extension variables.
    /// Initialized to usize::MAX (meaning no extension variables yet).
    /// Set to the current num_vars before the first extension variable
    /// is created by factoring or SBVA. (#8397)
    pub(super) first_extension_var_index: usize,
    /// Structured proof log for extension-variable definitions.
    pub(super) er_proof_log: crate::er_proof::ErProofLog,

    // Factorization state
    /// Factorization stats: total rounds
    pub(super) factor_rounds: u64,
    /// Factorization stats: total factored groups
    pub(super) factor_factored_total: u64,
    /// Factorization stats: total extension variables introduced
    pub(super) factor_extension_vars_total: u64,
    /// Per-variable signed factor candidate marks (CaDiCaL `Flags::factor`):
    /// bit0 = positive literal marked, bit1 = negative literal marked.
    pub(super) factor_candidate_marks: Vec<u8>,
    /// Monotonic epoch tracking irredundant clause mutations relevant to factoring.
    pub(super) factor_marked_epoch: u64,
    /// Last `factor_marked_epoch` consumed by a completed factor round.
    pub(super) factor_last_completed_epoch: u64,
    /// Search ticks at last factor call. Used to compute tick-proportional effort.
    /// CaDiCaL: `last.factor.ticks` (factor.cpp:962).
    pub(super) last_factor_ticks: u64,

    // SBVA state
    /// SBVA stats: total rounds
    pub(super) sbva_rounds: u64,
    /// SBVA stats: total groups compressed
    pub(super) sbva_groups_total: u64,
    /// SBVA stats: total extension variables introduced
    pub(super) sbva_extension_vars_total: u64,
    /// Search ticks at last SBVA call. Used to compute tick-proportional effort.
    pub(super) last_sbva_ticks: u64,

    /// Search ticks at last sweep call. Used for proportional sweep effort
    /// and tick-threshold scheduling (#7905, #8090).
    pub(super) last_sweep_ticks: u64,
    // sweep_consecutive_unproductive REMOVED (#8450): sweep is no longer
    // permanently disabled. Growing backoff handles unproductive rounds.
    /// Search ticks at last backbone call. Used for tick-threshold scheduling (#8090).
    /// CaDiCaL: `last.backbone.ticks` (backbone.cpp).
    pub(super) last_backbone_ticks: u64,
    /// Search ticks at last probe call. Used for tick-threshold scheduling (#8148).
    pub(super) last_probe_ticks: u64,
    /// Search ticks at last subsume call. Used for tick-threshold scheduling (#8148).
    pub(super) last_subsume_ticks: u64,
    /// Search ticks at last BVE call. Used for tick-threshold scheduling (#8148).
    pub(super) last_bve_ticks: u64,
    /// Consecutive BVE phases with zero eliminations. Used for exponential
    /// backoff scheduling: each unproductive phase doubles the BVE interval.
    /// Reset to 0 when any phase eliminates at least one variable (#8135).
    pub(super) bve_consecutive_unproductive: u32,
    /// Search ticks at last transred call. Used for tick-threshold scheduling (#8148).
    pub(super) last_transred_ticks: u64,
    /// Search ticks at last BCE call. Used for tick-threshold scheduling (#8148).
    pub(super) last_bce_ticks: u64,
    /// Number of completed backbone phases. Used to enforce the round limit
    /// (`BACKBONE_MAX_ROUNDS`). CaDiCaL: `stats.backbone.phases` (backbone.cpp:533).
    pub(super) backbone_phases: u32,
    /// Default-on post-vivify binary-backbone same-round admission gate.
    ///
    /// When enabled, a first binary backbone pass that passed the shared
    /// backbone gate can admit the cheap post-vivify binary pass even if the
    /// bounded-CDCL backbone path grew the shared backoff in between. Disabling
    /// this restores the legacy post-vivify gate of `should_backbone` only.
    pub(super) backbone_post_vivify_binary_admission: bool,
    /// Consecutive backbone invocations that found zero new backbone literals.
    /// When this reaches BACKBONE_STALL_LIMIT, backbone is permanently disabled
    /// for the instance (#8448). On formulas like mp1-klieber (30K vars, 92K
    /// clauses), backbone finds 0 units across all rounds but costs 810ms --
    /// enough to push a 14.4s solve over the 15s SAT-COMP timeout. A
    /// productive round resets the counter.
    ///
    /// Re-added after #8450 removed it: the growing backoff alone is
    /// insufficient because backbone rounds still fire (just less frequently)
    /// and each round costs 200-300ms on medium formulas. On hard SAT formulas
    /// where backbone has no structural leverage, even infrequent rounds are
    /// wasted time.
    pub(super) backbone_consecutive_empty: u32,
    /// Default-off bounded-CDCL-only backbone cooldown conflict target.
    ///
    /// This deliberately does not participate in `should_backbone()`, because
    /// that shared row also admits cheap binary-backbone root-unit discovery.
    pub(super) next_bounded_backbone_conflict: u64,
    /// Consecutive HTR rounds that produced zero resolvents. When this reaches
    /// BACKBONE_STALL_LIMIT, HTR is permanently disabled (#8448). On EDP3
    /// (91K vars, 680K clauses), 3 HTR rounds cost 554ms with 0 resolvents.
    pub(super) htr_consecutive_empty: u32,
    /// Formula component decomposition statistics.
    pub(super) component_stats: crate::component::ComponentStats,
    // Intree probing stats (CMS intree.cpp port, #8169)
    /// Number of completed intree probing rounds.
    pub(super) intree_rounds: u64,
    /// Total failed literals discovered by intree probing.
    pub(super) intree_failed: u64,
    /// Total variables set (units derived) by intree probing.
    pub(super) intree_vars_set: u64,
    /// Wall-clock overhead (milliseconds) of the most recent inprocessing round's
    /// infrastructure work: rebuild_watches, trail re-propagation. Used by
    /// adaptive tick-threshold scaling (#8099).
    /// When incremental state maintenance reduces this overhead, techniques
    /// can fire more frequently.
    pub(super) last_inprocessing_overhead_ms: f64,
    /// Post-rebuild BCP measurement (#8103): propagation count baseline.
    pub(super) post_rebuild_props_baseline: u64,
    /// Post-rebuild BCP measurement (#8103): true if a measurement is pending.
    pub(super) post_rebuild_bcp_pending: bool,
    /// Post-rebuild BCP measurement (#8103): true if the pending measurement
    /// is for a full rebuild, false if for incremental reconnect.
    pub(super) post_rebuild_is_full: bool,
    /// (#8093) Set by instantiate() when it performs a full watch rebuild
    /// during BVE. The elimination phase uses this to advance the arena
    /// baseline (since the rebuild covers all active clauses).
    pub(super) instantiate_rebuilt_watches: bool,
    /// (#8093) Count of clause deletions while watches were disconnected.
    /// When nonzero, reconnect_bve_watches must run the Phase 1 purge to
    /// remove stale binary watch entries. When zero (BVE was a no-op),
    /// the O(total_watch_entries) purge scan can be skipped entirely.
    pub(super) disconnected_deletions: u32,
    /// Simplification count of the most recent inprocessing round.
    /// Used for diminishing-returns detection: when a round makes few
    /// simplifications relative to the active clause count, the next
    /// inprocessing interval is widened more aggressively (#8134).
    pub(super) last_round_simplifications: u64,
    /// Number of consecutive inprocessing rounds with low productivity
    /// (simplifications < 1% of active clauses). When this exceeds a threshold,
    /// the interval scaling is boosted to reduce round frequency (#8134).
    pub(super) consecutive_low_productivity_rounds: u32,
    /// Level-0 assignments for eliminated variables, preserved across
    /// compaction. Indexed by external variable index.
    ///
    /// CaDiCaL preserves eliminated variables' vals across compaction
    /// (extend.cpp:140 reads `internal->val(ilit)` for all variables,
    /// including eliminated ones). AY's compaction truncates the vals
    /// array, discarding eliminated variables' level-0 assignments.
    /// This field bridges the gap: `finalize_sat` reads these values
    /// for UNMAPPED external variables instead of defaulting to `false`.
    ///
    /// Populated during `compact()`. For non-eliminated external
    /// variables, the value is undefined (read from live vals instead).
    /// (#8179)
    pub(super) eliminated_ext_vals: Vec<bool>,

    /// External → internal variable index. Indexed by external var index.
    /// `e2i[ext_var]` = internal var index, or `UNMAPPED` if compacted away.
    /// Length: max external var + 1. Grows monotonically (never shrinks).
    /// Reference: CaDiCaL `external.hpp:64`.
    pub(super) e2i: Vec<u32>,
    /// Internal → external variable index. Indexed by internal var index.
    /// `i2e[int_var]` = external var index.
    /// Length: current `num_vars`. Rebuilt during compaction.
    /// Reference: CaDiCaL `internal.hpp:222`.
    pub(super) i2e: Vec<u32>,
    /// Next conflict count at which compaction is eligible.
    /// CaDiCaL compact.cpp:540-541: `lim.compact = conflicts + compactint * (compacts + 1)`.
    pub(super) compact_next_conflict: u64,
    /// Number of compactions performed so far.
    pub(super) compact_count: u64,
    /// Reference counts for frozen variables (protected from elimination)
    pub(super) freeze_counts: Vec<u32>,
    // LRAT proof support
    /// Clause IDs for LRAT proofs (maps clause index to clause ID)
    /// Original clauses get IDs 1..n, learned clauses get n+1, n+2, etc.
    pub(super) clause_ids: Vec<u64>,
    /// Learned-clause birth conflict count for default-off 19-63 identity profiling.
    pub(super) bcp_learned_clause_birth_conflicts: Vec<u64>,
    /// Per-variable LRAT clause ID fallback for level-0 variables whose reason
    /// clause was deleted via `ReasonPolicy::ClearLevel0`. Without this, chain
    /// collectors skip such variables, producing incomplete LRAT hints (#4617).
    pub(super) level0_proof_id: Vec<u64>,
    /// Signed literal proven by `level0_proof_id`; 0 means no signed provenance.
    pub(super) level0_proof_sign: Vec<i8>,
    /// First root-trail position that still needs level-0 LRAT unit materialization.
    pub(super) lrat_level0_unit_materialize_cursor: usize,
    /// Remaining deterministic work budget for search-time proof bookkeeping
    /// (level-0 LRAT unit materialization rescans; #A2b construction budget).
    /// `None` = unbudgeted (explicit `--proof`/`--strict-proofs`/
    /// `:produce-proofs`). `Some(0)` = exhausted: materialization becomes a
    /// no-op and the clause trace is marked `proof_work_exhausted`, so the
    /// synthesized-default certificate degrades to the honest "no proof
    /// certificate emitted" warning while the verdict is unaffected.
    pub(super) proof_bookkeeping_budget: Option<u64>,
    /// Next clause ID to assign (for derived clauses and id-sync with proof writer)
    pub(super) next_clause_id: u64,
    /// Next original clause ID to assign (1-indexed, increments for each non-derived clause).
    /// Original clauses in LRAT are pre-registered at IDs 1..=num_originals, and this
    /// counter tracks which original ID to assign next. Keeps original clause IDs
    /// consistent with the LRAT proof even when derived clauses/deletions advance
    /// next_clause_id past the original range.
    pub(super) next_original_clause_id: u64,
    /// Whether LRAT proof generation is enabled (track resolution chains)
    pub(super) lrat_enabled: bool,
    /// Whether UNSAT results build a `ProofCertificate` via backward LRAT
    /// reconstruction. Defaults to `true`. Internal consumers that need
    /// clause-ID tracking (e.g. `ClauseTrace`) but never read the returned
    /// certificate can set this to `false` via
    /// `set_unsat_certificate_enabled` to skip the backward reconstruction
    /// pass on every UNSAT (`SatResult::Unsat` then carries
    /// `ProofCertificate::empty()`).
    pub(super) unsat_certificate_enabled: bool,
    /// Default-off internal route for the checker-covered dense
    /// factor->BVE LRAT composition. This only relaxes central LRAT clamps
    /// for factor and BVE when a solver-internal driver explicitly opts in.
    pub(super) dense_factor_bve_lrat_route_enabled: bool,
    /// Default-off internal route for the checker-covered Circuit BVE LRAT
    /// retained-plan mutation candidate. This does not relax the global
    /// Main/LRAT BVE clamp; the route driver opens one bounded BVE slice.
    pub(super) circuit_bve_lrat_route_enabled: bool,
    /// Default-off internal Main/LRAT scout route for a bounded BVE-only
    /// inprocessing slice. The route driver temporarily opens BVE and relies
    /// on `preflight_bve_lrat_transaction`; factor and sweep remain clamped.
    pub(super) bve_lrat_scout_route_enabled: bool,
    /// Default-off internal Main/LRAT Fmla decompose preflight route. This
    /// does not relax global LRAT decompose permissions; the route driver runs
    /// one checker-visible dry-run/materializer preflight and leaves the clause
    /// database unchanged.
    pub(super) fmla_decompose_lrat_preflight_route_enabled: bool,
    /// Whether the Fmla decompose LRAT preflight route has already fired for
    /// this solver. The route is diagnostic/admission-only and must not loop
    /// on every restart inprocessing round.
    pub(super) fmla_decompose_lrat_preflight_route_consumed: bool,
    /// Whether jump reasons optimization is active (#8034).
    ///
    /// Kissat fastassign.h:12-19: when a binary propagation's reason literal
    /// itself has a binary reason, store the transitive reason directly.
    /// This shortens reason chains and reduces clause dereferences during
    /// conflict analysis.
    ///
    /// Gate (Kissat classify.c): only enabled when the formula has a high
    /// binary clause fraction (>= 99.0%, matching Kissat's `bigbigfraction`
    /// default of 990 per mille) AND LRAT is disabled (LRAT requires clause
    /// reasons for forward resolution chain hints).
    ///
    /// Computed once at `init_solve()` based on the original clause database.
    pub(super) jump_reasons_enabled: bool,
    /// Whether the empty clause derivation was already written to proof_manager.
    /// Prevents duplicate empty-clause entries between mark_empty_clause and
    /// finalize_unsat_proof (#4123).
    pub(super) empty_clause_in_proof: bool,
    /// LRAT clause ID assigned to the empty clause derivation, if any.
    /// Used by pop() to emit a deletion step when retracting scoped UNSAT (#4475).
    pub(super) empty_clause_lrat_id: Option<u64>,
    /// Scope depth at which has_empty_clause was first set.
    /// Used by pop() to preserve base-level (depth 0) UNSAT.
    pub(super) empty_clause_scope_depth: usize,
    // In-memory clause trace for SMT proof reconstruction
    /// Optional clause trace (only active when SMT proof production is enabled)
    pub(super) clause_trace: Option<ClauseTrace>,
    /// Stack of active scope selector variables (for push/pop)
    pub(super) scope_selectors: Vec<Variable>,
    /// Snapshot of num_vars at each push(), parallel to scope_selectors (#8369).
    pub(super) scope_var_starts: Vec<usize>,
    /// Snapshot of reconstruction stack length at each push() (#8369).
    /// Used by pop() to drain witness entries added during the scope.
    pub(super) scope_reconstruction_starts: Vec<usize>,
    /// LRAT axiom IDs for scope selector negations, parallel to scope_selectors.
    /// Each entry is the LRAT ID assigned to [¬selector] during push().
    /// Used by finalize_unsat_proof to include axiom IDs in empty clause hints.
    /// Only populated in debug builds (LRAT checker is debug-only).
    #[cfg(debug_assertions)]
    pub(super) scope_selector_axiom_ids: Vec<u64>,
    /// Whether the solver has ever entered incremental mode (push/pop).
    /// Once set, clause-deleting inprocessing techniques (conditioning, BVE,
    /// BCE, sweep, congruence, factor) are permanently disabled because their
    /// reconstruction-based model recovery interacts unsoundly with learned
    /// clauses from scoped solving (#3662).
    pub(super) has_been_incremental: bool,
    /// External variable indices from newly added clauses since last solve (#8369).
    pub(super) tainted_vars: Vec<usize>,
    /// Whether push() has ever been called. Once set, the `original_ledger`
    /// may contain clauses with scope-selector literals that are no
    /// longer asserted after pop(). `verify_against_original` must be skipped
    /// in this case because those clauses may be unsatisfied.
    /// Multi-solve without push/pop (assumption-based incremental, e.g. CHC)
    /// does NOT set this flag — `original_ledger` remains a sound ledger.
    pub(super) has_ever_scoped: bool,
    /// Whether `init_solve()` has been called at least once. Used to detect
    /// multi-solve scenarios (solve→solve without push/pop) where destructive
    /// inprocessing must be disabled to prevent formula corruption (#5031).
    pub(super) has_solved_once: bool,
    // -- CaDiCaL-style temporary constraint clause (#8207) --
    /// Literals of the temporary constraint clause.
    /// Set by [`Solver::constrain()`]. Active for exactly one solve call,
    /// then automatically cleared by [`Solver::reset_constraint()`].
    /// Reference: CaDiCaL `internal.hpp:260`.
    pub(super) constraint: Vec<Literal>,
    /// Whether the constraint was used to prove unsatisfiability.
    /// Set to `true` when all constraint literals are falsified after
    /// assumptions. Reference: CaDiCaL `internal.hpp:261`.
    pub(super) unsat_constraint: bool,
    // Removed BCP/watch JIT cold state in #8517, including tier policy,
    // compilation request queues, backend compiler handles, and related
    // clause-count bookkeeping.
    /// Code cache manager: tracks total executable memory across all JIT
    /// allocations and provides LRU eviction recommendations (#8394).
    /// Retained for conflict processor memory tracking.
    #[cfg(feature = "jit")]
    pub(super) code_cache: ay_jit::CodeCacheManager,
    /// When true, all JIT compilation is disabled. Set by
    /// `disable_technique(SatTechnique::Jit)` via the `--disable jit` CLI flag (#8331).
    pub(super) jit_disabled: bool,
    /// Cumulative conflict count across all incremental solve calls (#8208).
    ///
    /// Each `reset_search_state()` zeroes `num_conflicts` for per-solve
    /// bookkeeping. This field accumulates conflicts from prior solves so
    /// inprocessing scheduling thresholds (which compare against conflict
    /// counts) can progress across the many tiny IC3/PDR solve calls.
    /// Without this, `next_inprobe_conflict` is never reached because each
    /// solve starts at conflict 0 and typically finishes with <100 conflicts.
    pub(super) lifetime_conflicts: u64,
    /// Cumulative decisions across incremental solves (#qfuflia-stats): the
    /// split loop resets `num_decisions` every round, so per-solve reporting
    /// needs `lifetime + current` (same pattern as `lifetime_conflicts`).
    pub(super) lifetime_decisions: u64,
    /// Cumulative propagations across incremental solves (#qfuflia-stats).
    pub(super) lifetime_propagations: u64,
    /// Cumulative restarts across incremental solves (#qfuflia-stats).
    pub(super) lifetime_restarts: u64,
    /// Number of incremental solve calls (assumption-based or push/pop) (#8435).
    ///
    /// Incremented by `reset_search_state()` when `has_solved_once` is true.
    /// Used to schedule between-solve cleanup (learned clause reduction, VSIDS
    /// decay, watch compaction) to prevent accumulated overhead in IC3/PDR
    /// query sequences. The cleanup fires every `INCREMENTAL_REDUCE_INTERVAL`
    /// solves when the learned clause count exceeds a threshold.
    pub(super) incremental_solve_count: u64,
    /// Conflict count at the last between-solve reduction (#8435).
    ///
    /// Tracks when the last `between_solve_reduce` ran (in lifetime_conflicts
    /// units) so the cleanup doesn't fire on every solve call.
    pub(super) last_between_solve_reduce_conflicts: u64,
    /// Lazy theory reason data table (#8467).
    ///
    /// Indexed by the `reason` field of `VarData` when `FLAG_LAZY_THEORY_REASON`
    /// is set. Each entry stores the theory-opaque `reason_data: u64` that can be
    /// passed to `Extension::explain_lazy_reason()` during conflict analysis.
    ///
    /// Entries are appended during `add_lazy_theory_propagation()` and never
    /// removed (indices are stable for the lifetime of a solve call). The table
    /// is cleared at the start of each solve call in `reset_search_state()`.
    pub(super) lazy_theory_reasons: Vec<u64>,
    /// Parallel table to `lazy_theory_reasons`: the propagated literal for each
    /// lazy reason entry. Needed by `explain_lazy_reason()` to reconstruct the
    /// full clause with the propagated literal at position 0.
    pub(super) lazy_theory_propagated: Vec<Literal>,
    /// Sticky flag: set when a lazy theory reason failed to materialize in
    /// `materialize_current_level_lazy_reasons`. When this is true, the
    /// subsequent 1UIP `analyze_conflict` call must bail out (return `None`)
    /// because converting failed lazy reasons to fake decisions corrupts
    /// the `resolvent_size == counter + learned_count` invariant and
    /// produces incorrect learned clauses (#8707).
    ///
    /// Cleared at the start of each `materialize_current_level_lazy_reasons`
    /// invocation and at solve reset via `clear_lazy_reason_tables`.
    pub(crate) lazy_materialization_failed: bool,
    /// When true, theory lemmas from extension callbacks use `TrustedTransform`
    /// proof emission instead of `Axiom` and do NOT block LRAT mode (#7913).
    ///
    /// Set by `prepare_preprocessing_extension` when a preprocessing extension
    /// (e.g., XOR Gauss-Jordan) consumes original clauses and replaces them
    /// with equivalent theory propagations/conflicts. These extension-derived
    /// clauses are logical consequences of the consumed originals and do not
    /// require the full LRAT block that SMT theory lemmas need.
    pub(crate) extension_trusted_lemmas: bool,
    /// Streaming UNSAT core bitmap (#8250).
    /// Tracks which original clause IDs participated in the proof during
    /// conflict analysis. Updated incrementally: when an antecedent clause
    /// used during resolution is an original clause (ID <= num_originals),
    /// its bit is set. Available immediately at UNSAT without needing to
    /// walk the proof DAG post-hoc.
    ///
    /// Indexed by `clause_id - 1` (clause IDs are 1-based).
    /// `None` when streaming core is not active (SAT result or no original
    /// clauses). `Some(bitmap)` when active.
    pub(super) streaming_core: Option<Vec<bool>>,
    /// Number of original clause IDs allocated at solve start.
    /// Used to bound the streaming_core bitmap and determine whether a
    /// clause ID refers to an original (input) clause.
    pub(super) streaming_core_num_originals: u64,
    /// O(1) lookup for scope selectors during UNSAT core filtering
    pub(super) scope_selector_set: Vec<bool>,
    /// Permanent record of variables ever used as scope selectors.
    /// Unlike `scope_selector_set` (cleared on pop), this is never cleared.
    /// Used by `verify_against_original` to skip clauses containing scope
    /// selector literals when `has_ever_scoped` is true (#5522).
    pub(super) was_scope_selector: Vec<bool>,
    /// Clauses removed by conditioning's root-satisfied GC (#5106).
    /// These clauses are satisfied at level 0 and safe to remove within a single
    /// solve, but must be restored by `reset_search_state()` for incremental use
    /// because level-0 assignments are wiped between solves.
    pub(super) root_satisfied_saved: Vec<Vec<Literal>>,
    /// Set by inprocessing (decompose/congruence) when clause_db is permanently
    /// modified (clauses deleted or replaced) without reconstruction entries.
    /// Checked by `reset_search_state()` to trigger clause_db rebuild from
    /// `original_ledger` on the next solve (#5031).
    pub(super) inprocessing_modified_clause_db: bool,
    /// Set by `collect_level0_garbage` when it deletes satisfied clauses or
    /// strengthens clauses by removing false-at-level-0 literals (#8375).
    /// Unlike `inprocessing_modified_clause_db`, L0 GC mutations are safe
    /// for learned clause preservation: learned clauses were derived under
    /// the original (non-BVE-simplified) clause set. The rebuild triggered
    /// by this flag restores original clauses AND re-adds learned clauses.
    pub(super) l0_gc_modified_clause_db: bool,
    // Lookahead scheduling state (#8087, #8322)
    /// Conflict count when the last lookahead round completed.
    /// Used for interval gating (LOOKAHEAD_INTERVAL).
    pub(super) last_lookahead_conflict: u64,
    /// Next conflict threshold for lookahead eligibility.
    /// Grows with each round (2x backoff) to avoid repeated expensive
    /// lookahead on formulas where per-round cost is high (#8322).
    pub(super) next_lookahead_conflict: u64,
    /// Lookahead-chosen decision literal, pending use by the CDCL loop.
    /// Set by `run_lookahead_round()`, consumed by `take_lookahead_decision()`.
    pub(super) lookahead_decision: Option<Literal>,

    // External phase hints (CaDiCaL phases.forced, phases.cpp:31-54)
    /// Per-variable forced phase: 1 = positive, -1 = negative, 0 = no hint.
    /// Set by `set_phase()`, cleared by `clear_phase()` / `clear_phases()`.
    /// Checked first in `pick_phase()` — overrides target/saved phases.
    pub(super) forced_phase: Vec<i8>,

    // Rephasing and phase initialization
    pub(super) rephase_enabled: bool,
    pub(super) rephase_count: u64,
    pub(super) rephase_count_stable: u64,
    pub(super) rephase_count_focused: u64,
    pub(super) next_rephase: u64,
    /// Route-scoped experiment: skip scheduled rephases while in focused mode.
    pub(super) stable_only_rephase_enabled: bool,
    // Flip-based local search state (#8246)
    /// Whether greedy flip-based local search is enabled during rephase.
    /// Disabled by `--disable flip` CLI flag (#8331).
    pub(super) flip_search_enabled: bool,
    /// Search tick watermark used to budget flip search effort.
    pub(super) flip_last_ticks: u64,
    /// Flip search statistics.
    pub(super) flip_stats: crate::flip::FlipStats,
    // Cold restart state (Zhang et al. 2024, arXiv:2404.16387)
    /// Number of cold restarts performed.
    pub(super) cold_restart_count: u64,
    /// Conflict count at the last cold restart.
    pub(super) cold_restart_last_conflict: u64,
    /// Whether cold restart is enabled (disabled by env `AY_NO_COLD_RESTART`).
    pub(super) cold_restart_enabled: bool,
    /// FO (Forget Order): randomize VSIDS scores and VMTF queue.
    pub(super) cold_restart_fo_enabled: bool,
    /// FP (Forget Phases): randomize all variable phases.
    pub(super) cold_restart_fp_enabled: bool,
    // Preprocessing and runtime tracing
    pub(super) preprocess_enabled: bool,
    pub(super) preprocess_watches_valid: bool,
    /// Wall-clock deadline for preprocessing (#8078). When `Some(deadline)`,
    /// preprocessing techniques bail out once `Instant::now() >= deadline`.
    /// Prevents hangs on formulas where aggregate preprocessing cost exceeds
    /// the time budget (e.g., Circuit_multiplier22: XOR detection + gate
    /// extraction + BVE stalls for 30s while CaDiCaL solves in 19s).
    pub(super) preprocess_deadline: Option<ay_core::time::Instant>,
    /// Hard wall-clock deadline for the WHOLE solve call
    /// (#array-deadline-forward). Unlike `preprocess_deadline` (scoped to
    /// `preprocess()`), this covers the phases that the caller's
    /// `should_stop` closure cannot reach: incremental inprocessing and the
    /// level-0 garbage collection sweep, whose per-clause watch-removal loop
    /// was measured running 12+s past the caller's wall budget on a grown
    /// clause DB (QF_AX subset re-solves), and the non-interruptible
    /// `solve_with_assumptions` entry. Polled amortized — never per BCP
    /// step. Fail-closed: an expired deadline can only produce Unknown.
    pub(super) solve_deadline: Option<ay_core::time::Instant>,
    /// When `Some(offset)`, watches from the previous solve are still valid
    /// for all clauses below `offset` in the arena. Only clauses at or after
    /// `offset` need watch attachment. Set by `reset_search_state()` case (b)
    /// (arena preserved, new original clauses appended). `None` means a full
    /// watch rebuild is required (#8374).
    pub(super) incremental_watch_boundary: Option<usize>,
    pub(super) symmetry_enabled: bool,
    pub(super) symmetry_stats: crate::symmetry::SymmetryStats,
    pub(super) tla_trace: Option<TlaTraceWriter>,
    pub(super) diagnostic_trace: Option<SatDiagnosticWriter>,
    pub(super) decision_trace: Option<DecisionTraceWriter>,
    pub(super) replay_trace: Option<ReplayTrace>,
    pub(super) diagnostic_pass: DiagnosticPass,
    pub(super) solution_witness: Option<Vec<Option<bool>>>,
    /// Route SEARCH BCP through the single lean instantiation (#bcp-lean).
    pub(super) bcp_lean_route_enabled: bool,
    pub(super) forward_checker: Option<crate::forward_checker::ForwardChecker>,
    pub(super) last_unknown_reason: Option<SatUnknownReason>,
    /// Detail string explaining WHY the last Unknown was produced (#7917).
    /// Populated when finalization fails (e.g., which original clause was
    /// unsatisfied, reconstruction panic details).
    pub(super) last_unknown_detail: Option<String>,
    /// Number of times finalize_sat_model has failed in the current solve call.
    /// When this exceeds MAX_FINALIZE_SAT_RETRIES, the solver gives up and
    /// returns Unknown. Reset at each solve entry (#7917).
    pub(super) finalize_sat_fail_count: u32,
    /// Sticky poison: a clause with more than `u16::MAX` literals was stored
    /// *truncated* in the arena because oversized-clause splitting was disabled
    /// (`AY_SPLIT_OVERSIZED_CLAUSES=0`). Truncation discards literals, which can
    /// only strengthen the clause, so any later UNSAT is suspect and must be
    /// downgraded to `Unknown` (SAT stays sound). With splitting enabled (the
    /// default) oversized clauses are CNF-split into equisatisfiable chains and
    /// this flag is never set. (#oversized)
    pub(super) oversized_clause_poison: bool,
    pub(super) interrupt: Option<Arc<AtomicBool>>,
    pub(super) process_memory_interrupt: bool,
    /// #sparse-gap Cluster A: one positive memory-gate reading arms this
    /// PENDING flag; only a SECOND consecutive positive poll latches
    /// `process_memory_interrupt`. A transient allocator spike (observed:
    /// parse/realloc of a 63M-clause arena tripping the gate while peak RSS
    /// sat at 65% of the limit) previously latched permanently and poisoned
    /// the whole solve to Unknown at exactly 1024 decisions. Real OOM
    /// pressure persists across polls, so protection is unchanged.
    pub(super) process_memory_interrupt_pending: bool,
    /// #sparse-gap Cluster B: resume cursor for `backbone_binary`'s
    /// per-variable ring scan. The pass previously restarted at var 0 every
    /// call and, unbounded, consumed 45-55s of a 60s budget on large sparse
    /// main-track instances (e.g. 231 units for 13.5s). With the wall cap,
    /// the cursor gives cumulative coverage across rounds — kissat gets its
    /// backbone coverage from many cheap bounded calls, not one unbounded one.
    pub(super) backbone_binary_cursor: usize,
    /// Wall-clock instant when the memory gate first read exceeded (armed).
    /// The interrupt latches only if a poll >= 500ms later STILL reads
    /// exceeded — a genuine runaway sustains pressure; a parse/realloc
    /// transient decays within the window (see
    /// `process_memory_interrupt_pending`).
    pub(super) process_memory_armed_at: Option<ay_core::time::Instant>,
    /// Cached check: `AY_TRACE_EXT_CONFLICT` env var was set at solver creation.
    /// Avoids repeated `std::env::var()` syscalls in the CDCL hot loop (#perf).
    pub(super) trace_ext_conflict: bool,
    /// Cached `AY_BVE_LIMIT` env var. Avoids per-candidate syscalls in BVE loop.
    pub(super) bve_limit: Option<usize>,
    /// Cached `AY_BVE_TRACE` env var. Avoids per-elimination syscalls in BVE loop.
    pub(super) bve_trace: bool,
    /// When true, the quick elimination pre-pass (CaDiCaL elimfast pattern) is
    /// disabled. Set by `--disable elimfast` CLI flag (#8331).
    pub(super) elimfast_disabled: bool,
    /// Sparse-band large-formula preprocess-BVE unlock (scoped, kill-switched).
    ///
    /// Set from the variant sparse-band BVE predicate. When true, the preprocess
    /// BVE/fastelim pass is allowed to run even when
    /// `skip_expensive_preprocessing_passes` is set (num_vars>200K or
    /// num_clauses>3M) — but ONLY on genuinely sparse formulas. The dense-skip
    /// guard is re-checked at BVE entry so this can never run expensive BVE on a
    /// dense formula. Bounded by the existing preprocess deadline and the
    /// fastelim wall-clock guard. Default-driven by AY_AB_BVE_SPARSE +
    /// AY_BVE_SPARSE_MAX_VARS/MAX_DENSITY; large formulas require the operator
    /// to raise AY_BVE_SPARSE_MAX_VARS above the 150K default.
    pub(super) sparse_band_bve_preprocess_unlock: bool,
    /// Giant raw-BVE unlock ROUTE flag (lever 3, 2026-07-11 sparse-prize
    /// completion round; OPT-IN via AY_AB_BVE_GIANT_RAW=1, band + measured
    /// default-OFF rationale in `VariantConfig::bve_giant_raw_route_active`).
    /// Set from the resolved variant config when the PARSED shape sits in
    /// the elimination-giant band (Default DIMACS non-LRAT, 150K < vars <=
    /// 2M, clauses <= 8M, density <= 12). Arming is completed at preprocess
    /// time by `try_qualify_bve_giant_raw` (which latches
    /// `bve_giant_raw_qualified` below) — the route flag alone changes
    /// nothing.
    pub(super) bve_giant_raw_unlock: bool,
    /// Giant raw-BVE unlock QUALIFICATION latch: set once per solve by
    /// `try_qualify_bve_giant_raw` after the preprocess collapse stage
    /// verified `count_removed() == 0` (no substitution structure — collapsed
    /// instances belong to the post-collapse lever) and re-checked the live
    /// dense-skip guard. Latched (rather than re-derived) because BVE itself
    /// flips `count_removed() > 0` as soon as it eliminates its first
    /// variable, which would falsely disqualify the deep budgets mid-phase.
    pub(super) bve_giant_raw_qualified: bool,
    /// Active-clause count captured IMMEDIATELY BEFORE the preprocess factor
    /// step (`config_preprocess.rs`), for the post-factor BVE clause-reopen
    /// (opt-in `AY_AB_BVE_POST_FACTOR`, measured-negative — see
    /// `bve_post_factor_reopens`). Zero until the factor step latches it.
    pub(super) pre_factor_active_clauses: usize,
    /// `num_vars` captured IMMEDIATELY BEFORE the preprocess factor step, paired
    /// with `pre_factor_active_clauses`. Factoring only GROWS num_vars (adds
    /// extension variables), so `num_vars - pre_factor_num_vars` is the count
    /// of factor-created extension vars used by the post-factor reopen predicate.
    pub(super) pre_factor_num_vars: usize,
    /// Post-factor BVE reopen QUALIFICATION latch (opt-in `AY_AB_BVE_POST_FACTOR`):
    /// set once per solve by `try_qualify_bve_post_factor` after the factor step,
    /// when the CLAUSE-axis reopen predicate + live dense-skip re-check pass on
    /// the factored residual. Latched (rather than re-derived) because BVE itself
    /// shrinks the live active-clause count as it eliminates, and the deep budgets
    /// must stay engaged for the whole pass. Mirror of `bve_giant_raw_qualified`.
    pub(super) bve_post_factor_qualified: bool,
    /// Elimination-phase sequence stamp for the instantiate gate (lever 2,
    /// AY_AB_BVE_INST_GATE — see `bve_inst_gate_enabled`). Incremented at
    /// each elimination-phase entry (run_preprocess_bve, the inprocessing
    /// elimination interleave, the incremental elimination path); bve_body
    /// admits at most one instantiate per stamp.
    pub(super) bve_elim_phase_seq: u64,
    /// Phase stamp of the last instantiate run (u64::MAX = never), paired
    /// with `bve_elim_phase_seq` for the once-per-phase gate. Initialized to
    /// MAX so direct `bve()` calls (tests, scoped incremental) that never
    /// stamp a phase still admit their first instantiate.
    pub(super) bve_instantiate_done_seq: u64,
    /// Route-aware substitution-collapse AUTO probe (campaign #15; default ON
    /// since 2026-07-10, wf_55735963 — measured +7 UNSAT flips / 0 hard
    /// losses on main2025, see `VariantConfig::subst_auto_collapse_enabled`).
    ///
    /// Set from the resolved variant config (Default DIMACS variant only;
    /// kill-switch AY_AB_SUBST_AUTO=0). When true, the FIRST preprocess
    /// congruence round doubles as an equivalence-density probe that gates
    /// the expensive decompose+fixpoint collapse (config_preprocess.rs), and
    /// compute_preprocess_policy raises the congruence size caps to the AUTO
    /// bounds. Scoping the flag here (instead of env reads in solver code)
    /// keeps non-Default variants and Custom congruence profiles on their
    /// historical unconditional path.
    pub(super) subst_auto_collapse: bool,
    /// Dense-band guard rails for the DEFAULT-ON AUTO collapse path
    /// (2026-07-11 dense-band regression fix; certified remeasure2 dense
    /// 23→19 attribution at main 0bb876d9). True only when
    /// `subst_auto_collapse` came from the DEFAULT-ON path
    /// (`AY_AB_SUBST_AUTO` unset). Arms two NARROW, instance-scoped guards:
    ///
    ///   1. EARLY formula-density disarm of the whole AUTO arming
    ///      (`compute_preprocess_policy`, predicate `auto_probe_skip_dense`,
    ///      density > PREPROCESS_BVE_SKIP_DENSITY = 20): fires BEFORE the
    ///      policy reads `congruence.enabled` / the AUTO caps, so a dense
    ///      instance's whole pipeline (lightweight L0-GC path included) is
    ///      behaviorally identical to AY_AB_SUBST_AUTO=0. Recovers 43fbacb2
    ///      (48K clauses, formula density 60.3: the probe's 0.05
    ///      EQUIVALENCE-density gate measured 0.50 there — it does not
    ///      correlate with formula density — arming the collapse machinery
    ///      and losing a 4.2s SAT) and 0ec8c5e9 (21.2M clauses, density
    ///      359: armed-but-unprobed flags leaked 2.8s of inprocessing
    ///      decompose + 2 yielding substitution passes, losing a 46s-margin
    ///      SAT; AUTO=0 re-solves SAT@88.7s, model-verified). All 7 sparse
    ///      AUTO flips live at density 2.3–9.3 (>2x below the cap); every
    ///      dense casualty is >= 60.3 — zero flip cost by construction.
    ///
    ///   2. Giant-formula bail on the two probe-path decompose RE-RUN sites
    ///      in inprocessing_schedule.rs (predicate
    ///      `auto_capped_giant_skips_decompose_rerun`, active clauses >
    ///      AUTO_CONGRUENCE_MAX_CLAUSES = 8M): those sites are gated only by
    ///      `should_decompose()` and bypass `skip_congruence_inproc`, so an
    ///      above-cap giant that never probed still paid O(total_literals)
    ///      decompose re-runs. Below-cap instances (ALL 7 flips, <=1.31M
    ///      clauses) keep today's behavior bit-for-bit — including the
    ///      armed-but-unprobed inprocessing leak that the 6f354fbe flip
    ///      depends on (a GLOBAL fail-closed disarm was measured to LOSE
    ///      that flip; do not widen these guards without re-running it).
    ///
    /// Explicit `AY_AB_SUBST_AUTO=1` keeps the historical uncapped
    /// measurement semantics (this stays false).
    pub(super) subst_auto_capped: bool,
    /// Giant-band AUTO probe raise (giant-3M loss fix, 2026-07; target
    /// 5ceb95f5 SAT@62.0s + bonus ac388757 SAT@58.6s, both models
    /// independently validated — see `AUTO_CONGRUENCE_GIANT_MAX_VARS`).
    /// True ONLY on the DEFAULT-ON capped path for NON-PROOF solves with
    /// `AY_AB_SUBST_AUTO_GIANT` not explicitly disabled (see
    /// `VariantConfig::subst_auto_giant_band_active`). When true,
    /// compute_preprocess_policy uses the raised 4M/10M probe caps instead
    /// of 2M/8M, and preprocess() grants the 12s giant-band budget to
    /// in-band non-dense instances. Proof solves, explicit
    /// `AY_AB_SUBST_AUTO=1`, and non-Default variants stay false — their
    /// pipelines are bit-for-bit unchanged.
    pub(super) subst_auto_giant: bool,
    /// Collect BCP attribution counters in optimized builds.
    ///
    /// Kept opt-in because the counters are written from the propagation hot
    /// path. Debug builds collect these counters unconditionally via
    /// `should_collect_bcp_telemetry()`.
    pub(super) bcp_telemetry_enabled: bool,
    /// Outer-loop BCP trail-lookahead watch-list prefetch.
    ///
    /// Current default is enabled. The DIMACS gate can disable only this
    /// propagation-loop lookahead while preserving enqueue-time prefetching, so
    /// benchmark runs can test whether the extra trail load and watch metadata
    /// prefetch pay for themselves.
    pub(super) bcp_trail_lookahead_prefetch: bool,
    /// Experimental SEARCH-only in-place watch scan route.
    ///
    /// When enabled in an `raw-pointer-bcp` build, SEARCH-mode full BCP routes to the
    /// raw-pointer watch-list scan substrate. Default-off so the safe deferred
    /// watch-buffer route remains the standard path for A/B and parity checks.
    pub(super) bcp_search_inplace_watch_scan: bool,
    /// Experimental BCP saved-position policy for long clauses.
    ///
    /// When a long-clause watch moves to an unassigned replacement, the watched
    /// slot receives the just-falsified literal after the later swap. Advancing
    /// `saved_pos` to the next tail slot avoids immediately restarting at that
    /// stale slot on the next scan. Default-off for A/B profiling.
    pub(super) bcp_advance_saved_pos_after_unassigned_move: bool,
    /// Experimental learned 19-63 false saved-position reset.
    ///
    /// When enabled, learned clauses in the P5g-hot 19-63 length bucket whose
    /// saved-position literal is already false restart replacement scanning at
    /// tail slot 2 and skip the known-false saved slot. Default-off for focused
    /// A/B profiling.
    pub(super) bcp_learned_1963_false_saved_pos_reset: bool,
    /// Experimental learned 19-63 true-tail watch relocation.
    ///
    /// When enabled, learned clauses in the P5g-hot 19-63 length bucket move a
    /// watch to a satisfied tail replacement instead of only refreshing the
    /// blocker. Default-off for focused A/B profiling.
    pub(super) bcp_learned_1963_true_tail_relocation: bool,
    /// Experimental learned 19-63 used>=5 FSW saved-position reset.
    ///
    /// When enabled, learned clauses in the 19-63 bucket that hit a
    /// no-replacement false-start-wrap scan with `used >= 5` reset `saved_pos`
    /// to the tail head. Default-off for focused A/B profiling.
    pub(super) bcp_learned_1963_used5_fsw_saved_pos_reset: bool,
    /// Experimental learned 19-63 FSW conflict-only saved-position reset.
    ///
    /// When enabled, learned clauses in the 19-63 bucket that hit a
    /// no-replacement false-start-wrap conflict reset `saved_pos` to the tail
    /// head. Unit outcomes are intentionally left untouched. Default-off for
    /// focused A/B profiling.
    pub(super) bcp_learned_1963_fsw_conflict_saved_pos_reset: bool,
    /// Experimental learned 6-18 true-tail watch relocation.
    ///
    /// Mirrors the 19-63 relocation gate for the shorter learned buckets that
    /// show clique scan pressure: when a replacement scan finds a satisfied tail
    /// literal, move the watch to that tail instead of keeping the falsified
    /// watch and refreshing only the blocker. Default-off for focused A/B
    /// profiling.
    pub(super) bcp_learned_618_true_tail_relocation: bool,
    /// Experimental learned no-replacement saved-position update.
    ///
    /// When enabled, learned long clauses whose replacement scan finds no
    /// non-false tail literal reset `saved_pos` to the normalized tail head.
    /// Default-off for focused A/B profiling because it writes an arena header
    /// on a hot full-scan path.
    pub(super) bcp_learned_no_replacement_saved_pos_update: bool,
    /// Experimental learned 19-63 false-start-wrap Gent-order skip.
    ///
    /// When enabled, learned clauses in the 19-63 bucket whose saved-position
    /// literal is already false keep Gent replacement order, but avoid re-reading
    /// that one known-false tail slot. Default-off for focused A/B profiling.
    pub(super) bcp_learned_1963_fsw_gent_skip: bool,
    /// Default-off learned no-replacement scan-pressure instrumentation.
    ///
    /// When enabled, SEARCH BCP records the scan-step cost of learned long
    /// clauses whose replacement scan finds no non-false tail literal, split by
    /// the same length buckets used by the long-scan telemetry. This is
    /// diagnostic-only and must not change watch movement or saved positions.
    pub(super) bcp_learned_no_replacement_scan_pressure: bool,
    /// Default-off exact learned 19-63 clause identity instrumentation.
    ///
    /// When enabled, SEARCH BCP records exact clause IDs and pressure counters
    /// for learned clauses in the 19-63 length bucket. Diagnostic-only.
    pub(super) bcp_learned_1963_identity_profile: bool,
    /// Default-off learned 19-63 pressure-aware reduce_db rank bias.
    ///
    /// When enabled, normal reduce_db may rank already-deletable learned
    /// 19-63 clauses with exact no-replacement pressure rows slightly worse
    /// within their LBD bucket. It does not add candidates or bypass any
    /// protection/deletion/proof checks.
    pub(super) bcp_learned_1963_pressure_reduction: bool,
    /// Default-off learned 19-63 pressure-aware reduce_db retention rank bias.
    ///
    /// When enabled, normal reduce_db may rank already-deletable learned
    /// 19-63 clauses with exact no-replacement pressure rows slightly better
    /// within their LBD bucket. It does not add candidates or bypass any
    /// protection/deletion/proof checks.
    pub(super) bcp_learned_1963_pressure_retention: bool,
    /// Experimental learned 19-63 no-replacement unit blocker-refresh disable.
    ///
    /// When enabled, learned clauses in the 19-63 bucket that find no tail
    /// replacement and become unit keep their existing blocker instead of
    /// refreshing it to the implied watched literal. Default-off so W58 behavior
    /// remains the normal path while isolating the clique regression surface.
    pub(super) bcp_disable_learned_1963_no_replacement_unit_blocker_refresh: bool,
    /// Experimental learned 6-17 creation-time tail reorder.
    ///
    /// When enabled, conflict-learned clauses in the P5g-hot 6-17 length bucket
    /// keep watched positions 0/1 fixed and reorder only the tail by descending
    /// (decision level, trail position). Default-off for focused A/B profiling.
    pub(super) bcp_learned_617_tail_reorder: bool,
    /// Experimental learned length-18 creation-time tail reorder.
    ///
    /// When enabled, conflict-learned clauses in the P5g-hot length-18 bucket
    /// keep watched positions 0/1 fixed and reorder only the tail by descending
    /// (decision level, trail position). Default-off for focused A/B profiling.
    pub(super) bcp_learned_18_tail_reorder: bool,
    /// Experimental learned 19-63 creation-time tail reorder.
    ///
    /// When enabled, conflict-learned clauses in the P5g-hot 19-63 length
    /// bucket keep watched positions 0/1 fixed and reorder only the tail by
    /// descending (decision level, trail position). Default-off for focused
    /// A/B profiling.
    pub(super) bcp_learned_1963_tail_reorder: bool,
    /// Optional learned 19-63 creation-time tail reorder swap budget.
    ///
    /// When set, conflict-learned 19-63 clauses are tail-reordered only when
    /// the stable adjacent-swap count is no larger than this budget. This keeps
    /// the old full reorder gate available while isolating low-disruption rows.
    pub(super) bcp_learned_1963_tail_reorder_swap_budget: Option<u64>,
    // Progress reporting
    /// Whether periodic progress lines should be emitted to stderr.
    pub(super) progress_enabled: bool,
    /// Programmatic progress observer for AI consumers (#8155).
    /// When `None`, all observer call sites are a single branch that the
    /// branch predictor eliminates (zero-cost). When `Some`, callbacks fire
    /// at conflict, restart, progress, and inprocessing events.
    pub(super) observer: Option<Box<dyn crate::observer::SolveObserver>>,
    /// Parallel-portfolio learned clause export hook.
    ///
    /// Installed only by `PortfolioSolver` worker threads. The hook receives
    /// conflict-learned clauses before the solver consumes the buffer.
    pub(super) portfolio_clause_exporter: Option<Box<dyn FnMut(&[Literal], u32) + Send>>,
    /// Parallel-portfolio learned clause import hook.
    ///
    /// Polled only at decision level 0 so imported clauses can be attached
    /// through the normal watched-clause path without violating CDCL state.
    pub(super) portfolio_clause_importer: Option<Box<dyn FnMut() -> Vec<Vec<Literal>> + Send>>,
    /// Official SAT-COMP Main/default/proof hot path: prune optional
    /// conflict-analysis experiments and stats-only observer hooks.
    pub(super) sat_comp_main_conflict_pruning: bool,
    /// Wall-clock time of the last progress line emission.
    pub(super) last_progress_time: Option<ay_core::time::Instant>,
    /// Wall-clock time when the current solve() call started.
    pub(super) solve_start_time: Option<ay_core::time::Instant>,
    // Immutable original-formula ledger and proof/debug helpers
    #[cfg(ay_logging)]
    pub(super) log_enabled: bool,
    /// Flat arena for the immutable original-clause ledger.
    /// Replaces `Vec<Vec<Literal>>` to eliminate per-clause heap allocations.
    pub(super) original_ledger: OriginalLedger,
    pub(super) incremental_original_boundary: usize,
    #[cfg(debug_assertions)]
    pub(super) pending_forward_check: Option<u64>,
    /// IC3 assumption propagation cache (#8443, GipSAT pattern).
    ///
    /// Stores the previous `solve_with_assumptions` call's assumption list.
    /// When consecutive calls share a prefix, the propagation state from the
    /// common prefix is reused instead of resetting to level 0 and replaying
    /// all assumptions. This avoids redundant BCP in IC3/PDR workloads where
    /// adjacent queries typically differ by 1-2 assumptions out of 5-50.
    ///
    /// Reference: GipSAT `new_round()` (reference/rIC3/src/gipsat/mod.rs:187-223)
    pub(super) prev_assumptions: Vec<Literal>,
    /// Whether the assumption cache is valid for reuse (#8443).
    ///
    /// Invalidated by any structural modification to the clause database:
    /// `add_clause`, `push`, `pop`, `new_var`. When false, the next
    /// `solve_with_assumptions` call performs a full `reset_search_state()`.
    pub(super) assumption_cache_valid: bool,
    /// Number of level-0 trail entries at the time the assumption cache was
    /// populated (#8443). Used to detect whether new level-0 propagations
    /// occurred between solve calls (e.g., from `add_clause` adding a unit).
    /// If the current level-0 trail differs, the cache is invalid.
    pub(super) assumption_cache_trail_len: usize,
    /// IC3 new clauses pending (#8569): set when `add_clause` appends new
    /// original clauses between incremental solves WITHOUT fully invalidating
    /// the assumption cache. The IC3 incremental reset path handles these
    /// by attaching watches and propagating units inline, avoiding the full
    /// O(num_vars) `reset_search_state()`.
    ///
    /// This is the key optimization for IC3 throughput: IC3 adds blocking
    /// clauses (frame lemmas) between every query. Previously each addition
    /// invalidated `assumption_cache_valid`, forcing the expensive full reset.
    /// Now the incremental reset handles them in O(new_clauses) time.
    pub(super) ic3_new_clauses_pending: bool,
    /// IC3 mode (#8569): when true, the solver is configured for IC3/PDR
    /// workloads. This flag enables several optimizations:
    /// - All inprocessing is disabled
    /// - Preprocessing is disabled
    /// - LRAT proof logging is disabled
    /// - Chrono backtracking is disabled
    /// - DIP-ERCL is disabled
    /// - Cold restarts are disabled
    /// - Lucky phases, walk, rephase, flip search are disabled
    /// - Bucket queue stays permanently active for domain queries
    /// - The IC3-optimized CDCL loop is used by `solve_incremental_ic3`
    ///
    /// Set via `Solver::set_ic3_mode()`. Once set, cannot be unset.
    pub(crate) ic3_mode: bool,
    /// #lra-inc-engine (S1): this SAT solver is the incremental QF_LRA engine
    /// lane's session-persistent solver, which FORCES the state-preserving
    /// incremental reset on every check-sat (even after benign var growth that
    /// invalidates `assumption_cache_valid`). Two things must agree on this:
    /// (1) `add_clause_unscoped_inner` must DEFER new-clause arena/watch
    ///     attachment (keep `incremental_original_boundary` put) so the coming
    ///     incremental reset's `attach_new_clauses_incremental` builds their
    ///     watches — otherwise the clauses land in the arena unwatched and BCP
    ///     misses conflicts;
    /// (2) the extension reset paths (`solve_with_assumptions_impl`,
    ///     `init_extension_loop`) re-establish `assumption_cache_valid` and take
    ///     the incremental reset.
    /// Distinct from `ic3_mode` (which CHC/PDR also sets, but WITHOUT forcing the
    /// reset), so gating on this flag leaves the CHC IC3 path untouched. Set via
    /// `Solver::set_inc_engine_reset_mode(true)`.
    pub(crate) inc_engine_reset_mode: bool,
    /// Minimum formula variable count before domain-restricted BCP is used.
    ///
    /// `None` means mode default: IC3 uses `IC3_DOMAIN_BCP_MIN_VARS_DEFAULT`,
    /// non-IC3 keeps the historical always-use-domain-BCP behavior.
    /// `Some(0)` forces domain BCP whenever an active domain is present.
    pub(super) domain_bcp_min_vars: Option<usize>,

    // ── IC3 constraint activation variable (#8662 Gap 3) ────────────────
    //
    // GipSAT pattern: a single reusable activation variable gates temporary
    // constraint clauses across all IC3 queries. Constraint clauses are
    // added as `(!constrain_act | l1 | l2 | ...)`. At query time,
    // `constrain_act = true` is added to assumptions to activate them.
    // Between queries, old constrained clauses remain in the database but
    // are trivially satisfied (constrain_act unassumed → the guard literal
    // is free). This avoids push/pop overhead for temporary constraints.
    //
    /// The activation variable for IC3 constrained clauses.
    /// Set via `Solver::set_constrain_activation()`. When `Some(var)`,
    /// `solve_incremental_ic3` automatically adds `Literal::positive(var)`
    /// to assumptions, and `add_constrained_clause` prepends
    /// `Literal::negative(var)` to each clause.
    pub(crate) ic3_constrain_act: Option<Variable>,

    /// Arena offsets of constrained clauses added via `add_constrained_clause`.
    ///
    /// Tracks every arena clause gated by the `ic3_constrain_act` guard
    /// literal. `cleanup_constrained_clauses` iterates this Vec instead of
    /// scanning the entire arena, achieving O(constraint_count) cleanup.
    /// Cleared on each `cleanup_constrained_clauses` call.
    pub(crate) ic3_constrained_offsets: Vec<usize>,

    // ── Persistent IC3 assumption tracking buffers (#8569 Gap 1) ────────
    //
    // IC3 makes thousands of queries/sec. Previously each query allocated
    // 3 x O(num_vars) vectors for assumption tracking. These persistent
    // buffers are cleared in O(assumptions) by tracking which indices
    // were set and sparse-clearing only those.
    //
    /// Per-variable flag: is this variable an assumption in the current query?
    /// Sized to `num_vars`, lazily grown by `solve_incremental_ic3`.
    pub(super) ic3_is_assumption: Vec<bool>,
    /// Per-variable: the assumption literal for this variable, if any.
    /// Sized to `num_vars`, lazily grown by `solve_incremental_ic3`.
    pub(super) ic3_assumption_lit: Vec<Option<Literal>>,
    /// Track which variable indices were set in `ic3_is_assumption` so we
    /// can clear them in O(assumptions) instead of O(num_vars).
    pub(super) ic3_assumption_indices: Vec<usize>,

    // ── Persistent IC3 domain expansion cache (#8569 Gap 1) ──────────────
    //
    // `set_domain()` is called on every IC3 query with 5-50 domain variables.
    // `expand_domain_bcp()` does a BFS over clauses to compute the transitive
    // cone-of-influence, which is O(arena) in the worst case. The expanded
    // domain result is stable across queries unless new clauses are added.
    // Cache the result and invalidate only when the clause DB changes.
    //
    /// Persistent bitmap buffer for `set_domain()`. Avoids per-query
    /// `vec![false; num_vars]` allocation. Cleared via sparse tracking.
    pub(super) ic3_domain_bitmap_buf: Vec<bool>,
    /// Variable indices that were set in `ic3_domain_bitmap_buf` for
    /// O(prev_domain) sparse clearing.
    pub(super) ic3_domain_set_indices: Vec<usize>,
    /// The original ledger boundary at the time the last domain expansion
    /// was cached. When `incremental_original_boundary` changes, the cache
    /// is invalidated because new clauses may expand the domain.
    pub(super) ic3_domain_cache_boundary: usize,
    /// Cached expanded domain bitmap from the last `expand_domain_bcp` call.
    /// Valid only when `ic3_domain_cache_boundary` matches the current
    /// `incremental_original_boundary` AND the input domain is the same.
    /// Stored as a separate vec because `active_domain` is moved after use.
    pub(super) ic3_domain_cache_expanded: Vec<bool>,
    /// Hash of the input domain variable set for cache invalidation.
    /// If the caller passes different domain variables, the cache is stale.
    pub(super) ic3_domain_cache_hash: u64,

    // ── IC3 memory pressure tracking (#8673) ────────────────────────────
    //
    // Tracks the arena word count at IC3 mode entry to detect when learned
    // clause accumulation has caused disproportionate memory growth. The
    // memory pressure reduce fires when arena.len() exceeds
    // IC3_MEMORY_PRESSURE_ARENA_FACTOR * ic3_baseline_arena_words.
    /// Arena word count when `set_ic3_mode()` was called, or updated after
    /// the first solve populates the arena. Used as the denominator for
    /// memory pressure ratio: `arena.len() / ic3_baseline_arena_words`.
    /// Zero means the baseline has not been captured yet.
    pub(super) ic3_baseline_arena_words: usize,

    // ── Persistent reusable buffers (#8602) ──────────────────────────────
    /// Reusable index buffer for `reduce_db` and related functions.
    /// Avoids per-call `arena.indices().collect::<Vec<usize>>()` allocations
    /// that are arena-proportional (~8 MB for 1M clauses).
    pub(super) reduce_indices_buf: Vec<usize>,
    /// Reusable ranked candidate buffer for normal `reduce_db`.
    /// Retains capacity across reductions and lets candidate metadata be
    /// loaded once before quota selection.
    pub(super) reduce_candidates_buf: Vec<ReduceCandidate>,
    /// Reusable bitmap for arena GC compaction (`compact_arena_locality`).
    /// Avoids per-call `vec![false; arena_len]` allocation.
    pub(super) gc_seen_buf: Vec<bool>,
    /// Reusable buffer for LRAT level-0 variable indices during conflict
    /// analysis (#8603). Previously allocated fresh on every conflict
    /// (`Vec::new()` in analyze_conflict). Conflicts happen thousands of
    /// times per second in LRAT mode — clearing and reusing eliminates the
    /// hottest remaining per-conflict allocation.
    pub(super) lrat_level0_vars_buf: Vec<usize>,
    /// Literal indices already mirrored into the DRAT proof as Derived unit
    /// adds by the certified congruence path (#15 T3). Fixed literals are
    /// flushed off the trail, so the mirror scans `vals` and this bitmap
    /// dedups emissions across passes (lazily sized to 2*num_vars).
    pub(super) proof_mirrored_units: Vec<bool>,
    /// Reusable hint buffer for LRAT unit derivations emitted immediately
    /// before deleting the antecedent clause.
    pub(super) lrat_delete_unit_hints_buf: Vec<u64>,
    /// Reusable hint buffer for level-0 LRAT unit materialization.
    pub(super) lrat_materialize_hints_buf: Vec<u64>,
    /// Reusable scratch buffers for BVE body elimination loop (#8602).
    /// Previously `BveBodyScratch::default()` was allocated fresh on every
    /// BVE round. Making it persistent retains allocated capacity across
    /// rounds, avoiding repeated allocation of the 12+ internal Vecs.
    pub(super) bve_body_scratch: inprocessing::BveBodyScratch,

    // ── Debug-only persistent buffers (#8599) ───────────────────────────
    /// Reusable buffer for JIT cross-validation flag snapshots (debug only).
    /// Previously `Vec::with_capacity(jit_seen_count)` was allocated per
    /// conflict inside `#[cfg(debug_assertions)]`. Conflicts happen thousands
    /// of times per second — clearing and reusing eliminates this per-conflict
    /// allocation in debug builds.
    #[cfg(all(debug_assertions, feature = "jit"))]
    pub(super) debug_jit_flags_buf: Vec<(usize, u8)>,
    /// Reusable interpreter output buffer for JIT cross-validation (debug only).
    /// Previously `ConflictProcessorOutput::new(num_vars)` was allocated per
    /// conflict, creating a `Vec<u32>` of size `4 + 2*num_vars` on every
    /// conflict. For 100K variables that is ~800KB per conflict. Resized
    /// lazily when `num_vars` grows.
    #[cfg(all(debug_assertions, feature = "jit"))]
    pub(super) debug_interp_output: ay_jit::conflict_jit::ConflictProcessorOutput,
}

/// A/B knob (campaign): `AY_AB_STABLE_EMA_GATE` overrides the INITIAL stable-mode
/// Glucose-EMA restart gate (default `STABLE_EMA_MIN_CONFLICTS`). Post-init
/// overrides in solve/mod.rs (small-dense / >1M-clause => u64::MAX) still apply.
/// Cached per process (each solver run is a fresh process).
fn ab_stable_ema_gate() -> u64 {
    use std::sync::OnceLock;
    static V: OnceLock<u64> = OnceLock::new();
    *V.get_or_init(|| {
        std::env::var("AY_AB_STABLE_EMA_GATE")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(STABLE_EMA_MIN_CONFLICTS)
    })
}

impl ColdState {
    /// Create the full cold solver tail for `Solver::build`.
    pub(crate) fn new(num_vars: usize, clauses_capacity: usize, lrat_enabled: bool) -> Self {
        Self {
            lbd_ema_fast: 0.0,
            lbd_ema_slow: 0.0,
            lbd_ema_fast_biased: 0.0,
            lbd_ema_slow_biased: 0.0,
            lbd_ema_fast_exp: 1.0,
            lbd_ema_slow_exp: 1.0,
            saved_lbd_ema_fast: 0.0,
            saved_lbd_ema_slow: 0.0,
            saved_lbd_ema_fast_biased: 0.0,
            saved_lbd_ema_slow_biased: 0.0,
            saved_lbd_ema_fast_exp: 1.0,
            saved_lbd_ema_slow_exp: 1.0,
            ema_swapped: false,
            glucose_restarts: true,
            theory_conflict_ratio: 0.0,
            ext_conflict_count: 0,
            theory_luby_idx: 1,
            trail_ema_slow: 0.0,
            trail_ema_count: 0,
            consecutive_ema_restarts: 0,
            geometric_restarts: false,
            geometric_initial: 100.0,
            geometric_factor: 1.1,
            restart_min_conflicts: RESTART_MIN_CONFLICTS,
            // Stable-mode EMA gate: minimum conflicts before Glucose EMA
            // can trigger a restart in stable mode. Low value (10) enables
            // quality-gated restarts for medium/large UNSAT instances
            // (Dodecahedron, 002, klieber) where pure reluctant doubling
            // runs too deep. Small dense formulas override this to u64::MAX
            // in post-preprocessing tuning (solve/mod.rs) to avoid restart
            // storms (#8135, #8466).
            stable_ema_gate: ab_stable_ema_gate(),
            focused_restart_gate: RESTART_INTERVAL,
            dense_mutex_focused_restart_gate_experiment: false,
            luby_idx: 1,
            restart_base: DEFAULT_RESTART_BASE,
            restarts: 0,
            stable_mode_start_conflicts: 0,
            stable_phase_init: STABLE_PHASE_INIT,
            stable_phase_length: STABLE_PHASE_INIT,
            stable_phase_count: 0,
            mode_switch_count: 0,
            mode_lock: ModeLock::None,
            probe_ticks: 0,
            vivify_ticks: 0,
            stabilize_tick_inc: 0,
            focused_ticks_at_entry: 0,
            mode_equiticks_cached: None,
            branch_selector_mode: BranchSelectorMode::LegacyCoupled,
            branch_mab: MabController::new(),
            stabilize_tick_limit: 0,
            last_target_improve_conflicts: 0,
            stable_tick_hardcap: 0,
            eqt_progress_cached: None,
            reluctant_u: 1,
            reluctant_v: 1,
            reluctant_countdown: RELUCTANT_INIT,
            reluctant_ticked_at: 0,
            next_reduce_db: FIRST_REDUCE_DB,
            num_reductions: 0,
            original_clause_boundary: 0,
            last_inprobe_reduction: 0,
            next_inprobe_conflict: 0,
            incremental_inprobe_clause_divisor: None,
            inprobe_phases: 0,
            uniform_formula_cache: None,
            learned_clause_trail: Vec::new(),
            num_eager_subsumptions: 0,
            next_flush: FLUSH_INIT,
            flush_inc: FLUSH_INIT,
            num_flushes: 0,
            num_arena_compactions: 0,
            scoped_clauses_reclaimed: 0,
            eager_subsumed: 0,
            max_learned_clauses: None,
            max_clause_db_bytes: None,
            conflict_budget: None,
            decision_budget: None,
            bumpreason_saved_decisions: 0,
            bumpreason_decision_rate: 0.0,
            bumpreason_delay_remaining: [0; 2],
            bumpreason_delay_interval: [0; 2],
            last_vivify_ticks: 0,
            last_vivify_irred_ticks: 0,
            vivify_irred_delay_multiplier: 1,
            randomized_deciding: 0,
            random_decision_phases: 0,
            next_random_decision: 1000,
            random_var_freq: 0.0,
            bve_effort_permille: BVE_EFFORT_PER_MILLE,
            subsume_effort_permille: SUBSUME_EFFORT_PER_MILLE,
            bve_phases: 0,
            subsume_ran_since_bve: false,
            last_bve_fixed: -1,
            bve_marked: 0,
            last_bve_marked: 0,
            last_bve_clauses: 0,
            last_collect_fixed: -1,
            last_collect_trail_pos: 0,
            last_full_l0_gc_fixed: -1,
            clause_db_changes: 0,
            bve_resolutions: 0,
            first_extension_var_index: usize::MAX,
            er_proof_log: crate::er_proof::ErProofLog::new(),
            factor_rounds: 0,
            factor_factored_total: 0,
            factor_extension_vars_total: 0,
            factor_candidate_marks: vec![0; num_vars],
            factor_marked_epoch: 1,
            factor_last_completed_epoch: 0,
            last_factor_ticks: 0,
            sbva_rounds: 0,
            sbva_groups_total: 0,
            sbva_extension_vars_total: 0,
            last_sbva_ticks: 0,
            last_sweep_ticks: 0,
            last_backbone_ticks: 0,
            last_probe_ticks: 0,
            last_subsume_ticks: 0,
            last_bve_ticks: 0,
            bve_consecutive_unproductive: 0,
            last_transred_ticks: 0,
            last_bce_ticks: 0,
            backbone_phases: 0,
            backbone_post_vivify_binary_admission: true,
            backbone_consecutive_empty: 0,
            next_bounded_backbone_conflict: 0,
            htr_consecutive_empty: 0,
            component_stats: crate::component::ComponentStats::default(),
            intree_rounds: 0,
            intree_failed: 0,
            intree_vars_set: 0,
            last_inprocessing_overhead_ms: 0.0,
            post_rebuild_props_baseline: 0,
            post_rebuild_bcp_pending: false,
            post_rebuild_is_full: false,
            instantiate_rebuilt_watches: false,
            disconnected_deletions: 0,
            last_round_simplifications: 0,
            consecutive_low_productivity_rounds: 0,
            eliminated_ext_vals: vec![false; num_vars],
            e2i: (0..num_vars as u32).collect(),
            i2e: (0..num_vars as u32).collect(),
            compact_next_conflict: 0,
            compact_count: 0,
            freeze_counts: vec![0; num_vars],
            // Always allocate clause_ids unconditionally (#8069: Phase 2a).
            // Clause IDs are the foundation for deferred backward proof
            // reconstruction and must be tracked even when LRAT mode is not
            // explicitly enabled.
            clause_ids: Vec::with_capacity(clauses_capacity),
            bcp_learned_clause_birth_conflicts: Vec::new(),
            level0_proof_id: vec![0; num_vars],
            level0_proof_sign: vec![0; num_vars],
            lrat_level0_unit_materialize_cursor: 0,
            proof_bookkeeping_budget: None,
            next_clause_id: 1,
            next_original_clause_id: 1,
            lrat_enabled,
            unsat_certificate_enabled: true,
            dense_factor_bve_lrat_route_enabled: false,
            circuit_bve_lrat_route_enabled: false,
            bve_lrat_scout_route_enabled: false,
            fmla_decompose_lrat_preflight_route_enabled: false,
            fmla_decompose_lrat_preflight_route_consumed: false,
            jump_reasons_enabled: false, // computed in init_solve (#8034)
            empty_clause_in_proof: false,
            empty_clause_lrat_id: None,
            empty_clause_scope_depth: 0,
            clause_trace: None,
            scope_selectors: Vec::new(),
            scope_var_starts: Vec::new(),
            scope_reconstruction_starts: Vec::new(),
            #[cfg(debug_assertions)]
            scope_selector_axiom_ids: Vec::new(),
            has_been_incremental: false,
            tainted_vars: Vec::new(),
            has_ever_scoped: false,
            has_solved_once: false,
            constraint: Vec::new(),
            unsat_constraint: false,
            #[cfg(feature = "jit")]
            code_cache: ay_jit::CodeCacheManager::with_default_budget(),
            jit_disabled: false,
            lifetime_conflicts: 0,
            lifetime_decisions: 0,
            lifetime_propagations: 0,
            lifetime_restarts: 0,
            incremental_solve_count: 0,
            last_between_solve_reduce_conflicts: 0,
            lazy_theory_reasons: Vec::new(),
            lazy_theory_propagated: Vec::new(),
            lazy_materialization_failed: false,
            extension_trusted_lemmas: false,
            streaming_core: None,
            streaming_core_num_originals: 0,
            scope_selector_set: vec![false; num_vars],
            was_scope_selector: vec![false; num_vars],
            root_satisfied_saved: Vec::new(),
            inprocessing_modified_clause_db: false,
            l0_gc_modified_clause_db: false,
            last_lookahead_conflict: 0,
            next_lookahead_conflict: 0,
            lookahead_decision: None,
            rephase_enabled: true,
            rephase_count: 0,
            rephase_count_stable: 0,
            rephase_count_focused: 0,
            next_rephase: REPHASE_INITIAL,
            stable_only_rephase_enabled: false,
            flip_search_enabled: true,
            flip_last_ticks: 0,
            flip_stats: crate::flip::FlipStats::default(),
            cold_restart_count: 0,
            cold_restart_last_conflict: 0,
            // #8506: Read cached OnceLock instead of std::env::var().
            cold_restart_enabled: !ay_core::sat_disable_flags().no_cold_restart,
            cold_restart_fo_enabled: true,
            cold_restart_fp_enabled: false,
            forced_phase: vec![0; num_vars],
            preprocess_enabled: true,
            preprocess_watches_valid: false,
            preprocess_deadline: None,
            solve_deadline: None,
            incremental_watch_boundary: None,
            symmetry_enabled: false, // #8190: CaDiCaL has no symmetry detection; adaptive re-enables for small structured formulas
            symmetry_stats: crate::symmetry::SymmetryStats::default(),
            tla_trace: None,
            diagnostic_trace: None,
            decision_trace: None,
            replay_trace: None,
            diagnostic_pass: DiagnosticPass::None,
            solution_witness: None,
            bcp_lean_route_enabled: false,
            forward_checker: None,
            last_unknown_reason: None,
            last_unknown_detail: None,
            finalize_sat_fail_count: 0,
            oversized_clause_poison: false,
            interrupt: None,
            process_memory_interrupt: false,
            process_memory_interrupt_pending: false,
            backbone_binary_cursor: 0,
            process_memory_armed_at: None,
            trace_ext_conflict: ay_core::sat_debug_env_flags().trace_ext_conflict,
            bve_limit: ay_core::sat_debug_env_flags().bve_limit,
            bve_trace: ay_core::sat_debug_env_flags().bve_trace,
            elimfast_disabled: false,
            sparse_band_bve_preprocess_unlock: false,
            bve_giant_raw_unlock: false,
            bve_giant_raw_qualified: false,
            pre_factor_active_clauses: 0,
            pre_factor_num_vars: 0,
            bve_post_factor_qualified: false,
            bve_elim_phase_seq: 0,
            bve_instantiate_done_seq: u64::MAX,
            subst_auto_collapse: false,
            subst_auto_capped: false,
            subst_auto_giant: false,
            bcp_telemetry_enabled: false,
            bcp_trail_lookahead_prefetch: true,
            // CaDiCaL-exact raw-pointer in-place SEARCH BCP (default feature
            // `raw-pointer-bcp`). Same 2WL algorithm as the safe deferred-copy path
            // (verified bit-identical by tests/propagation_bcp_unsafe.rs) but
            // avoids two full watch-list memcpys per propagation of a literal
            // with long watchers — the hottest loop in the solver. Default-on:
            // it is the VIVIFY default and ~2x BCP throughput on real instances.
            bcp_search_inplace_watch_scan: true,
            bcp_advance_saved_pos_after_unassigned_move: false,
            bcp_learned_1963_false_saved_pos_reset: false,
            bcp_learned_1963_true_tail_relocation: false,
            bcp_learned_1963_used5_fsw_saved_pos_reset: false,
            bcp_learned_1963_fsw_conflict_saved_pos_reset: false,
            bcp_learned_618_true_tail_relocation: false,
            bcp_learned_no_replacement_saved_pos_update: false,
            bcp_learned_1963_fsw_gent_skip: false,
            bcp_learned_no_replacement_scan_pressure: false,
            bcp_learned_1963_identity_profile: false,
            bcp_learned_1963_pressure_reduction: false,
            bcp_learned_1963_pressure_retention: false,
            bcp_disable_learned_1963_no_replacement_unit_blocker_refresh: false,
            bcp_learned_617_tail_reorder: false,
            bcp_learned_18_tail_reorder: false,
            bcp_learned_1963_tail_reorder: false,
            bcp_learned_1963_tail_reorder_swap_budget: None,
            progress_enabled: false,
            observer: None,
            portfolio_clause_exporter: None,
            portfolio_clause_importer: None,
            sat_comp_main_conflict_pruning: false,
            last_progress_time: None,
            solve_start_time: None,
            #[cfg(ay_logging)]
            log_enabled: ay_core::sat_debug_env_flags().log_enabled,
            original_ledger: OriginalLedger::new(),
            incremental_original_boundary: 0,
            #[cfg(debug_assertions)]
            pending_forward_check: None,
            prev_assumptions: Vec::new(),
            assumption_cache_valid: false,
            assumption_cache_trail_len: 0,
            ic3_new_clauses_pending: false,
            ic3_mode: false,
            inc_engine_reset_mode: false,
            domain_bcp_min_vars: None,
            ic3_constrain_act: None,
            ic3_constrained_offsets: Vec::new(),
            ic3_is_assumption: Vec::new(),
            ic3_assumption_lit: Vec::new(),
            ic3_assumption_indices: Vec::new(),
            ic3_domain_bitmap_buf: Vec::new(),
            ic3_domain_set_indices: Vec::new(),
            ic3_domain_cache_boundary: 0,
            ic3_domain_cache_expanded: Vec::new(),
            ic3_domain_cache_hash: 0,
            ic3_baseline_arena_words: 0,
            reduce_indices_buf: Vec::new(),
            reduce_candidates_buf: Vec::new(),
            gc_seen_buf: Vec::new(),
            lrat_level0_vars_buf: Vec::new(),
            proof_mirrored_units: Vec::new(),
            lrat_delete_unit_hints_buf: Vec::new(),
            lrat_materialize_hints_buf: Vec::new(),
            bve_body_scratch: Default::default(),
            #[cfg(all(debug_assertions, feature = "jit"))]
            debug_jit_flags_buf: Vec::new(),
            #[cfg(all(debug_assertions, feature = "jit"))]
            debug_interp_output: ay_jit::conflict_jit::ConflictProcessorOutput::new(num_vars),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::OriginalLedger;
    use crate::literal::{Literal, Variable};

    fn lit(v: u32, pos: bool) -> Literal {
        if pos {
            Literal::positive(Variable(v))
        } else {
            Literal::negative(Variable(v))
        }
    }

    /// Basic push_clause_global: global clause survives pop_scope.
    #[test]
    fn test_push_clause_global_survives_pop() {
        let mut ledger = OriginalLedger::new();
        // Base clauses
        ledger.push_clause(&[lit(0, true), lit(1, true)]);
        ledger.push_clause(&[lit(2, true), lit(3, true)]);
        assert_eq!(ledger.num_clauses(), 2);

        ledger.push_scope();
        // Scoped clause
        ledger.push_clause(&[lit(4, true)]);
        assert_eq!(ledger.num_clauses(), 3);
        // Global clause (should survive pop)
        ledger.push_clause_global(&[lit(5, true), lit(6, true)]);
        assert_eq!(ledger.num_clauses(), 4);

        // Pop removes the scoped clause but keeps the global one
        assert!(ledger.pop_scope());
        assert_eq!(
            ledger.num_clauses(),
            3,
            "should have 2 base + 1 global = 3 after pop"
        );

        // Verify the surviving clauses are correct
        let clauses = ledger.to_vec_of_vecs();
        assert_eq!(clauses[0], vec![lit(0, true), lit(1, true)]);
        assert_eq!(clauses[1], vec![lit(2, true), lit(3, true)]);
        assert_eq!(clauses[2], vec![lit(5, true), lit(6, true)]);
    }

    /// Regression #8546: push_clause_global must NOT protect scoped clauses.
    ///
    /// Bug: the old `max()` approach shifted scope boundaries forward past
    /// ALL clauses including scoped ones added before the global clause.
    /// This caused scoped clauses to survive pop_scope.
    #[test]
    fn test_push_clause_global_does_not_protect_scoped_clauses() {
        let mut ledger = OriginalLedger::new();
        // 5 base clauses
        for i in 0..5u32 {
            ledger.push_clause(&[lit(i, true)]);
        }
        assert_eq!(ledger.num_clauses(), 5);

        ledger.push_scope();
        // Add 3 scoped clauses
        ledger.push_clause(&[lit(10, true)]);
        ledger.push_clause(&[lit(11, true)]);
        ledger.push_clause(&[lit(12, true)]);
        assert_eq!(ledger.num_clauses(), 8);

        // Now add a global clause — this is the pattern IC3 uses for frame lemmas
        ledger.push_clause_global(&[lit(20, true), lit(21, true)]);
        assert_eq!(ledger.num_clauses(), 9);

        // Pop should remove the 3 scoped clauses but keep the global one
        assert!(ledger.pop_scope());
        assert_eq!(
            ledger.num_clauses(),
            6,
            "should have 5 base + 1 global = 6 after pop (scoped clauses removed)"
        );

        // Verify no scoped clause survived
        let clauses = ledger.to_vec_of_vecs();
        assert_eq!(clauses.len(), 6);
        // The last clause should be the global one
        assert_eq!(clauses[5], vec![lit(20, true), lit(21, true)]);
        // None of the scoped clauses (lit(10), lit(11), lit(12)) should be present
        for clause in &clauses {
            for l in clause {
                let vi = l.variable().0;
                assert!(
                    vi != 10 && vi != 11 && vi != 12,
                    "scoped clause with var {vi} survived pop_scope — push_clause_global bug"
                );
            }
        }
    }

    /// Nested scopes with push_clause_global at different levels.
    #[test]
    fn test_push_clause_global_nested_scopes() {
        let mut ledger = OriginalLedger::new();
        ledger.push_clause(&[lit(0, true)]); // base

        ledger.push_scope(); // scope 1
        ledger.push_clause(&[lit(10, true)]); // scoped in scope 1
        ledger.push_clause_global(&[lit(20, true)]); // global (survives both pops)

        ledger.push_scope(); // scope 2
        ledger.push_clause(&[lit(30, true)]); // scoped in scope 2
        ledger.push_clause_global(&[lit(40, true)]); // global (survives both pops)

        assert_eq!(ledger.num_clauses(), 5);

        // Pop scope 2: removes scoped-in-2, keeps globals
        assert!(ledger.pop_scope());
        assert_eq!(ledger.num_clauses(), 4); // base + scoped-in-1 + 2 globals
        let clauses = ledger.to_vec_of_vecs();
        // Verify scoped-in-2 (var 30) is gone
        assert!(
            !clauses
                .iter()
                .any(|c| c.iter().any(|l| l.variable().0 == 30)),
            "scope-2 clause should be removed"
        );

        // Pop scope 1: removes scoped-in-1, keeps globals
        assert!(ledger.pop_scope());
        assert_eq!(ledger.num_clauses(), 3); // base + 2 globals
        let clauses = ledger.to_vec_of_vecs();
        assert!(
            !clauses
                .iter()
                .any(|c| c.iter().any(|l| l.variable().0 == 10)),
            "scope-1 clause should be removed"
        );
        // Globals survive
        assert!(clauses
            .iter()
            .any(|c| c.iter().any(|l| l.variable().0 == 20)));
        assert!(clauses
            .iter()
            .any(|c| c.iter().any(|l| l.variable().0 == 40)));
    }

    /// Multiple global clauses within the same scope.
    #[test]
    fn test_push_clause_global_multiple_in_same_scope() {
        let mut ledger = OriginalLedger::new();
        ledger.push_clause(&[lit(0, true)]); // base

        ledger.push_scope();
        ledger.push_clause(&[lit(10, true)]); // scoped
        ledger.push_clause_global(&[lit(20, true)]); // global 1
        ledger.push_clause(&[lit(11, true)]); // scoped (interleaved)
        ledger.push_clause_global(&[lit(21, true)]); // global 2
        ledger.push_clause(&[lit(12, true)]); // scoped
        assert_eq!(ledger.num_clauses(), 6);

        assert!(ledger.pop_scope());
        // 1 base + 2 globals = 3
        assert_eq!(ledger.num_clauses(), 3);
        let clauses = ledger.to_vec_of_vecs();
        assert_eq!(clauses[0], vec![lit(0, true)]);
        assert_eq!(clauses[1], vec![lit(20, true)]);
        assert_eq!(clauses[2], vec![lit(21, true)]);
    }

    /// Repeated push/pop cycles with globals: IC3-like pattern (#8546).
    ///
    /// IC3 repeatedly: push -> add scoped + global -> pop.
    /// Globals must accumulate correctly across many cycles.
    /// Scoped clauses must be fully removed each cycle.
    #[test]
    fn test_push_clause_global_repeated_cycles() {
        let mut ledger = OriginalLedger::new();
        // Base clause
        ledger.push_clause(&[lit(0, true), lit(1, true)]);
        assert_eq!(ledger.num_clauses(), 1);

        for round in 0..50u32 {
            let expected_before_push = 1 + round as usize; // base + round globals

            assert_eq!(
                ledger.num_clauses(),
                expected_before_push,
                "round {round}: wrong clause count before push"
            );

            ledger.push_scope();

            // Add a scoped clause
            ledger.push_clause(&[lit(100 + round, true)]);

            // Add a global clause (frame lemma)
            ledger.push_clause_global(&[lit(200 + round, true), lit(201 + round, false)]);

            assert_eq!(
                ledger.num_clauses(),
                expected_before_push + 2,
                "round {round}: wrong count during scope"
            );

            assert!(ledger.pop_scope());

            // After pop: base + (round+1) globals. Scoped clause removed.
            let expected_after_pop = 1 + (round + 1) as usize;
            assert_eq!(
                ledger.num_clauses(),
                expected_after_pop,
                "round {round}: wrong count after pop"
            );

            // Verify no scoped clause leaked
            let clauses = ledger.to_vec_of_vecs();
            for clause in &clauses {
                for l in clause {
                    let vi = l.variable().0;
                    assert!(
                        !(100..200).contains(&vi),
                        "round {round}: scoped clause with var {vi} survived pop"
                    );
                }
            }
        }

        // Final: 1 base + 50 globals = 51 clauses.
        assert_eq!(ledger.num_clauses(), 51);
    }

    /// Global clause added outside any scope behaves like push_clause.
    #[test]
    fn test_push_clause_global_no_scope() {
        let mut ledger = OriginalLedger::new();
        ledger.push_clause(&[lit(0, true)]);
        ledger.push_clause_global(&[lit(1, true)]);
        ledger.push_clause(&[lit(2, true)]);
        assert_eq!(ledger.num_clauses(), 3);

        // No scope to pop: all clauses remain.
        assert!(!ledger.pop_scope()); // returns false
        assert_eq!(ledger.num_clauses(), 3);
    }

    /// Mixed scoped clauses before AND after global clause in nested scopes.
    ///
    /// Regression scenario: the old max() approach shifted ALL scope boundaries
    /// forward when a global was added, protecting scoped clauses added BEFORE
    /// the global. This test verifies scoped clauses on both sides of a global
    /// are properly removed.
    #[test]
    fn test_push_clause_global_scoped_before_and_after() {
        let mut ledger = OriginalLedger::new();
        ledger.push_clause(&[lit(0, true)]); // base

        ledger.push_scope();
        // Scoped BEFORE global
        ledger.push_clause(&[lit(10, true)]);
        ledger.push_clause(&[lit(11, true)]);

        // Global in the middle
        ledger.push_clause_global(&[lit(50, true)]);

        // Scoped AFTER global
        ledger.push_clause(&[lit(12, true)]);
        ledger.push_clause(&[lit(13, true)]);

        assert_eq!(ledger.num_clauses(), 6); // 1 base + 4 scoped + 1 global

        assert!(ledger.pop_scope());
        // 1 base + 1 global = 2
        assert_eq!(ledger.num_clauses(), 2);
        let clauses = ledger.to_vec_of_vecs();
        assert_eq!(clauses[0], vec![lit(0, true)]);
        assert_eq!(clauses[1], vec![lit(50, true)]);
    }

    /// pop_scope with no globals in scope: pure truncation, no replay.
    #[test]
    fn test_pop_scope_no_globals() {
        let mut ledger = OriginalLedger::new();
        ledger.push_clause(&[lit(0, true)]);
        ledger.push_clause(&[lit(1, true)]);

        ledger.push_scope();
        ledger.push_clause(&[lit(10, true)]);
        ledger.push_clause(&[lit(11, true)]);
        assert_eq!(ledger.num_clauses(), 4);

        assert!(ledger.pop_scope());
        assert_eq!(ledger.num_clauses(), 2);
        let clauses = ledger.to_vec_of_vecs();
        assert_eq!(clauses[0], vec![lit(0, true)]);
        assert_eq!(clauses[1], vec![lit(1, true)]);
    }

    /// Empty scope with a global clause: scope has no scoped clauses,
    /// only a global. Pop should preserve the global.
    #[test]
    fn test_push_clause_global_empty_scope() {
        let mut ledger = OriginalLedger::new();
        ledger.push_clause(&[lit(0, true)]);

        ledger.push_scope();
        // No scoped clauses, only a global
        ledger.push_clause_global(&[lit(50, true), lit(51, true)]);
        assert_eq!(ledger.num_clauses(), 2);

        assert!(ledger.pop_scope());
        assert_eq!(ledger.num_clauses(), 2); // base + global
        let clauses = ledger.to_vec_of_vecs();
        assert_eq!(clauses[0], vec![lit(0, true)]);
        assert_eq!(clauses[1], vec![lit(50, true), lit(51, true)]);
    }

    /// Triple-nested scopes with globals at each level.
    #[test]
    fn test_push_clause_global_triple_nested() {
        let mut ledger = OriginalLedger::new();
        ledger.push_clause(&[lit(0, true)]); // base

        ledger.push_scope(); // scope 1
        ledger.push_clause(&[lit(10, true)]); // scoped-1
        ledger.push_clause_global(&[lit(100, true)]); // global-1

        ledger.push_scope(); // scope 2
        ledger.push_clause(&[lit(20, true)]); // scoped-2
        ledger.push_clause_global(&[lit(200, true)]); // global-2

        ledger.push_scope(); // scope 3
        ledger.push_clause(&[lit(30, true)]); // scoped-3
        ledger.push_clause_global(&[lit(300, true)]); // global-3

        assert_eq!(ledger.num_clauses(), 7); // 1 base + 3 scoped + 3 globals

        // Pop scope 3
        assert!(ledger.pop_scope());
        assert_eq!(ledger.num_clauses(), 6); // base + scoped-1 + scoped-2 + 3 globals
        let clauses = ledger.to_vec_of_vecs();
        assert!(!clauses
            .iter()
            .any(|c| c.iter().any(|l| l.variable().0 == 30)));

        // Pop scope 2
        assert!(ledger.pop_scope());
        assert_eq!(ledger.num_clauses(), 5); // base + scoped-1 + 3 globals
        let clauses = ledger.to_vec_of_vecs();
        assert!(!clauses
            .iter()
            .any(|c| c.iter().any(|l| l.variable().0 == 20)));

        // Pop scope 1
        assert!(ledger.pop_scope());
        assert_eq!(ledger.num_clauses(), 4); // base + 3 globals
        let clauses = ledger.to_vec_of_vecs();
        assert!(!clauses
            .iter()
            .any(|c| c.iter().any(|l| l.variable().0 == 10)));
        // All three globals survive
        assert!(clauses
            .iter()
            .any(|c| c.iter().any(|l| l.variable().0 == 100)));
        assert!(clauses
            .iter()
            .any(|c| c.iter().any(|l| l.variable().0 == 200)));
        assert!(clauses
            .iter()
            .any(|c| c.iter().any(|l| l.variable().0 == 300)));
    }
}
