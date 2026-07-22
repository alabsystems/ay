// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mode-dependent rephasing with CaDiCaL-style schedules.
//!
//! Stable mode uses a conservative schedule (Original/Inverted dominate) because
//! EVSIDS scores are slow-changing and benefit from coherent phase information.
//! Focused mode uses an aggressive schedule (Random/Flipping dominate) because
//! VMTF already provides aggressive diversification.
//!
//! Reference: CaDiCaL `rephase.cpp:113-399`.

use super::*;
use crate::solver::solver_stats::RephaseAttribution;

/// Kissat NLOG3N scaling: `n * (log10(n + 9))^3`.
///
/// Used for rephase interval scheduling. Grows sub-quadratically,
/// keeping rephases more frequent than linear scaling on long runs.
///
/// Reference: Kissat `kimits.c:27-37` (`kissat_nlogpown` with exponent=3).
pub(super) fn nlog3n(n: u64) -> u64 {
    if n == 0 {
        return 1;
    }
    let log = ((n + 9) as f64).log10();
    let factor = log * log * log;
    ((n as f64) * factor).max(1.0) as u64
}

/// Kissat NLOGPOW4 scaling: `n * (log10(n + 9))^4`.
///
/// Used for stabilization phase duration scheduling. Grows much slower
/// than quadratic (`n^2`), matching Kissat's `mode.c:91` which uses
/// `modeint * kissat_nlogpown(count, 4)` for focused phase limits.
///
/// Reference: Kissat `kimits.c:27-37` (`kissat_nlogpown` with exponent=4).
pub(super) fn nlogpow4(n: u64) -> u64 {
    if n == 0 {
        return 1;
    }
    let log = ((n + 9) as f64).log10();
    let factor = log * log * log * log;
    ((n as f64) * factor).max(1.0) as u64
}

impl Solver {
    /// Check if rephasing should be triggered based on conflict count.
    #[inline]
    pub(super) fn should_rephase(&self) -> bool {
        self.cold.rephase_enabled
            && (!self.cold.stable_only_rephase_enabled || self.stable_mode)
            && self.num_conflicts >= self.cold.next_rephase
    }

    /// Perform rephasing: mode-dependent schedule selection.
    ///
    /// Reference: CaDiCaL `rephase.cpp:113-399`.
    pub(super) fn rephase(&mut self) {
        debug_assert_eq!(
            self.target_phase.len(),
            self.num_vars,
            "BUG: target_phase.len() ({}) != num_vars ({})",
            self.target_phase.len(),
            self.num_vars
        );
        debug_assert_eq!(
            self.best_phase.len(),
            self.num_vars,
            "BUG: best_phase.len() ({}) != num_vars ({})",
            self.best_phase.len(),
            self.num_vars
        );

        // Select strategy based on current mode with independent counters.
        // CaDiCaL: `lim.rephased[stable]++` (rephase.cpp:131).
        self.stats.record_rephase_mode(self.stable_mode);
        let is_best_rephase = if self.stable_mode {
            let count = self.cold.rephase_count_stable;
            self.cold.rephase_count_stable += 1;
            self.apply_stable_rephase_schedule(count)
        } else {
            let count = self.cold.rephase_count_focused;
            self.cold.rephase_count_focused += 1;
            self.apply_focused_rephase_schedule(count)
        };

        // Copy current saved phases to target before clearing.
        // CaDiCaL: `copy_phases(phases.target)` (rephase.cpp:373).
        for i in 0..self.num_vars {
            let p = self.phase[i];
            if p != 0 {
                self.target_phase[i] = p;
                self.stats.rephase_target_phase_updates += 1;
            }
        }
        self.target_trail_len = 0;

        // Reset best-phase tracking after Best rephase to allow fresh discovery.
        // CaDiCaL: `best_assigned = 0` (backtrack.cpp:55-56).
        if is_best_rephase {
            self.best_trail_len = 0;
            self.stats.rephase_best_resets += 1;
        }

        self.cold.rephase_count += 1;
        // Kissat rephase.c:119: UPDATE_CONFLICT_LIMIT(rephase, rephased, NLOG3N, false)
        // delta = rephaseint * count * (log10(count + 9))^3
        // NLOG3N grows sub-quadratically, keeping rephases frequent on hard
        // instances requiring 100K+ conflicts (#8085).
        let count = self.cold.rephase_count;
        let delta = REPHASE_INITIAL.saturating_mul(nlog3n(count));
        self.cold.next_rephase = self.num_conflicts.saturating_add(delta);

        // Shuffle decision ordering to diversify search after rephasing.
        // CaDiCaL: `rephase.cpp:396-399`.
        if self.stable_mode {
            self.vsids.shuffle_scores(self.cold.rephase_count);
        } else {
            self.vsids.shuffle_queue(self.cold.rephase_count);
        }
    }

    /// Stable-mode rephase schedule. Returns true if this was a Best rephase.
    ///
    /// Walk enabled (`rephase.cpp:287-316`, `stable && opts.walk`):
    ///   O, I, (B, W, O, B, W, I)^w
    /// Walk disabled (`rephase.cpp:263-286`, `stable && !opts.walk`):
    ///   O, I, (B, O, B, I)^w
    ///
    /// Verified against CaDiCaL commit used in `reference/cadical/`.
    pub(super) fn apply_stable_rephase_schedule(&mut self, count: u64) -> bool {
        if self.phase_init.walk_enabled {
            // O, I, (B, W, O, B, W, I)^w
            match count {
                0 => self.apply_rephase_kind(RephaseAttribution::Original),
                1 => self.apply_rephase_kind(RephaseAttribution::Inverted),
                _ => match (count - 2) % 6 {
                    0 | 3 => self.apply_rephase_kind(RephaseAttribution::Best),
                    1 | 4 => self.apply_rephase_kind(RephaseAttribution::Walk),
                    2 => self.apply_rephase_kind(RephaseAttribution::Original),
                    _ => self.apply_rephase_kind(RephaseAttribution::Inverted),
                },
            }
        } else {
            // O, I, (B, O, B, I)^w
            match count {
                0 => self.apply_rephase_kind(RephaseAttribution::Original),
                1 => self.apply_rephase_kind(RephaseAttribution::Inverted),
                _ => match (count - 2) % 4 {
                    0 | 2 => self.apply_rephase_kind(RephaseAttribution::Best),
                    1 => self.apply_rephase_kind(RephaseAttribution::Original),
                    _ => self.apply_rephase_kind(RephaseAttribution::Inverted),
                },
            }
        }
    }

    /// Focused-mode rephase schedule. Returns true if this was a Best rephase.
    ///
    /// Walk enabled (`rephase.cpp:339-367`, `!stable && opts.walk && opts.walknonstable`):
    ///   O, (#, B, W, F, B, W)^w
    ///   Note: CaDiCaL comment at line 341 says "flipping" for count==0 but
    ///   the code at line 344 calls `rephase_original()`. We follow the code.
    /// Walk disabled (`rephase.cpp:317-338`, `!stable && (!opts.walk || !opts.walknonstable)`):
    ///   F, (#, B, F, B)^w
    ///
    /// Verified against CaDiCaL commit used in `reference/cadical/`.
    pub(super) fn apply_focused_rephase_schedule(&mut self, count: u64) -> bool {
        if self.phase_init.walk_enabled {
            // O, (#, B, W, F, B, W)^w
            match count {
                0 => self.apply_rephase_kind(RephaseAttribution::Original),
                _ => match (count - 1) % 6 {
                    0 => self.apply_rephase_kind(RephaseAttribution::Random),
                    1 | 4 => self.apply_rephase_kind(RephaseAttribution::Best),
                    2 | 5 => self.apply_rephase_kind(RephaseAttribution::Walk),
                    _ => self.apply_rephase_kind(RephaseAttribution::Flip),
                },
            }
        } else {
            // F, (#, B, F, B)^w
            match count {
                0 => self.apply_rephase_kind(RephaseAttribution::Flip),
                _ => match (count - 1) % 4 {
                    0 => self.apply_rephase_kind(RephaseAttribution::Random),
                    1 | 3 => self.apply_rephase_kind(RephaseAttribution::Best),
                    _ => self.apply_rephase_kind(RephaseAttribution::Flip),
                },
            }
        }
    }

    fn apply_rephase_kind(&mut self, kind: RephaseAttribution) -> bool {
        let changed = match kind {
            RephaseAttribution::Original => self.rephase_original(),
            RephaseAttribution::Inverted => self.rephase_inverted(),
            RephaseAttribution::Best => self.rephase_best(),
            RephaseAttribution::Random => self.rephase_random(),
            RephaseAttribution::Flip => self.rephase_flip(),
            RephaseAttribution::Walk => self.rephase_walk(),
        };
        self.stats.record_rephase_attribution(kind, changed);
        matches!(kind, RephaseAttribution::Best)
    }

    /// Set all phases to true (Original).
    fn rephase_original(&mut self) -> u64 {
        let mut changed = 0;
        for p in &mut self.phase {
            if *p != 1 {
                changed += 1;
                *p = 1;
            }
        }
        changed
    }

    /// Set all phases to false (Inverted).
    fn rephase_inverted(&mut self) -> u64 {
        let mut changed = 0;
        for p in &mut self.phase {
            if *p != -1 {
                changed += 1;
                *p = -1;
            }
        }
        changed
    }

    /// Copy best-ever phases into saved phases (Best).
    ///
    /// Variables that have not appeared in a best trail yet fall back to
    /// target phases. This keeps warmup/target guidance available as saved
    /// phase data without weakening the stronger best-phase signal.
    fn rephase_best(&mut self) -> u64 {
        let mut changed = 0;
        for i in 0..self.num_vars {
            let b = if self.best_phase[i] != 0 {
                self.best_phase[i]
            } else {
                self.target_phase[i]
            };
            if b != 0 {
                if self.phase[i] != b {
                    changed += 1;
                }
                self.phase[i] = b;
            }
        }
        changed
    }

    /// Deterministic pseudo-random phase assignment (Random/#).
    /// Also used by cold restart FP variant (Zhang et al. 2024).
    pub(super) fn rephase_random(&mut self) -> u64 {
        let mut seed = self
            .num_conflicts
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1);
        let mut changed = 0;
        for p in &mut self.phase {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            let next = if (seed >> 32) & 1 == 0 { 1 } else { -1 };
            if *p != next {
                changed += 1;
            }
            *p = next;
        }
        changed
    }

    /// Invert all current phases (Flip/F), optionally enhanced with greedy
    /// flip-based local search.
    ///
    /// When flip search is enabled (not disabled via `--disable flip`): runs greedy local
    /// search that evaluates clauses under current phases and flips variables
    /// with positive make-break gain. Falls back to simple negation if flip
    /// search is disabled or the formula is too small to benefit.
    ///
    /// Reference: CaDiCaL `flip.cpp` — flip feasibility. Adapted to AY's
    /// phase-only rephase context as greedy local search.
    fn rephase_flip(&mut self) -> u64 {
        if self.cold.flip_search_enabled && self.num_vars > 0 {
            // Use greedy flip-based local search.
            let total_ticks = self.search_ticks[0] + self.search_ticks[1];
            let delta = total_ticks.saturating_sub(self.cold.flip_last_ticks);
            let tick_limit = crate::flip::compute_flip_effort(delta);
            self.cold.flip_last_ticks = total_ticks;

            let mode_idx = usize::from(self.stable_mode);
            let filter = crate::walk::WalkFilter {
                include_likely_kept: true,
                tier2_lbd: self.tiers.tier2_lbd[mode_idx],
            };

            crate::flip::flip_search(
                &self.arena,
                self.num_vars,
                &mut self.phase,
                &mut self.cold.flip_stats,
                tick_limit,
                filter,
            );
            0
        } else {
            // Simple phase negation fallback.
            let mut changed = 0;
            for p in &mut self.phase {
                // Negate: 1 -> -1, -1 -> 1, 0 stays 0.
                if *p != 0 {
                    changed += 1;
                }
                *p = -*p;
            }
            changed
        }
    }

    /// Run ProbSAT local search to find good phases during rephasing.
    ///
    /// Writes walk-discovered phases into `self.phase[]`. Uses the same walk
    /// implementation as startup phase initialization with Kissat-style effort
    /// scheduling proportional to search ticks since last walk.
    ///
    /// Uses irredundant clauses only, matching Kissat's walk implementation.
    /// CaDiCaL has a `walkredundant` option (default 0) to include learned
    /// clauses, but including them inflates occurrence lists and causes the
    /// walk to waste ticks trying to satisfy clauses that may not reflect
    /// the true problem structure. For hard random/combinatorial instances
    /// (stable-300, battleship), the extra learned clauses degrade walk
    /// quality by over-constraining the local search (#8466).
    ///
    /// Reference: Kissat `walk.c` — only walks irredundant (binary + large)
    /// clauses. CaDiCaL `walk.cpp:walk()` / `walk_full_occs.cpp`.
    fn rephase_walk(&mut self) -> u64 {
        if !self.phase_init.walk_enabled {
            return 0;
        }

        // Size gate (#shave9): walk() setup builds occurrence lists by
        // iterating ALL active clauses twice — an O(clauses) fixed cost the
        // tick budget does not cover, paid on EVERY rephase. The startup walk
        // has long had a size gate (try_walk, 5M cap + density exception);
        // the rephase walk had none, so million-clause incremental MaxSAT
        // parts (protein: 2.5M binary hards) paid a repeated whole-DB scan
        // for phase hints of marginal value on UNSAT-dominated core
        // extraction (~3.4% of steady-state runtime profiled). Kissat/CaDiCaL
        // amortize this differently (persistent occs / strict tick
        // proportionality); until walk setup is incremental, skip the
        // rephase walk on huge DBs. Stricter than the startup 5M cap because
        // this cost repeats.
        const REPHASE_WALK_MAX_ACTIVE_CLAUSES: usize = 2_000_000;
        if self.arena.active_clause_count() > REPHASE_WALK_MAX_ACTIVE_CLAUSES {
            return 0;
        }

        // Kissat-style effort scheduling: walk budget proportional to search
        // ticks since last walk invocation.
        let total_ticks = self.search_ticks[0] + self.search_ticks[1];
        let delta = total_ticks.saturating_sub(self.phase_init.walk_last_ticks);
        let tick_limit = crate::walk::compute_walk_effort(delta);
        self.phase_init.walk_last_ticks = total_ticks;

        let seed = self
            .num_conflicts
            .wrapping_add(self.cold.rephase_count)
            .wrapping_mul(6364136223846793005);

        // Irredundant clauses only, matching Kissat. CaDiCaL's walkredundant
        // defaults to 0 as well. Walking learned clauses inflates occurrence
        // lists and slows each walk step without proportional quality benefit.
        let filter = crate::walk::WalkFilter::irredundant_only();

        crate::walk::walk(
            &self.arena,
            self.num_vars,
            &mut self.phase,
            &mut self.phase_init.walk_prev_phase,
            &mut self.phase_init.walk_stats,
            seed,
            tick_limit,
            filter,
        );
        0
    }
}
