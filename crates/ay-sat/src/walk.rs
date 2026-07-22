// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CaDiCaL-style ProbSAT random walk for phase initialization.
//!
//! Picks random broken clauses, scores literals by break-count, flips with
//! probability proportional to score, saves best phases for CDCL.
//! O(degree) per flip via occurrence lists and incremental satisfaction counts.
//!
//! Reference: CaDiCaL `walk_full_occs.cpp` — full occurrence list walk with
//! per-clause satisfaction counters and lazy best-model tracking.

use crate::clause_arena::ClauseArena;
use crate::literal::Literal;

mod walker;

#[cfg(test)]
mod tests;

use walker::Walker;

/// Filter controlling which clauses the walk considers.
///
/// CaDiCaL's `walkredundant` option includes learned clauses that are
/// "likely to be kept" by the next `reduce_db`: all clauses with
/// `glue <= tier2` (the tier-2 boundary). This matches CaDiCaL's
/// `likely_to_be_kept_clause` in `internal.hpp:1059`.
#[derive(Debug, Clone, Copy)]
pub(crate) struct WalkFilter {
    /// Include learned clauses that are likely to survive reduce_db.
    pub include_likely_kept: bool,
    /// Tier-2 boundary (glue ≤ this → likely kept). Solver's `tier2_lbd`.
    pub tier2_lbd: u32,
}

impl WalkFilter {
    /// Default filter: irredundant clauses only (no learned).
    pub(crate) fn irredundant_only() -> Self {
        Self {
            include_likely_kept: false,
            tier2_lbd: 0,
        }
    }

    /// Whether the walk should include this clause.
    #[inline]
    pub(crate) fn should_include(&self, arena: &ClauseArena, off: usize) -> bool {
        if arena.is_empty_clause(off) || arena.is_garbage_any(off) {
            return false;
        }
        if !arena.is_learned(off) {
            return true;
        }
        // Learned clause: include only if walkredundant is enabled and
        // the clause is likely to be kept by reduce_db.
        if !self.include_likely_kept {
            return false;
        }
        // CaDiCaL likely_to_be_kept_clause: glue <= tier2[false] (no used check).
        // This is more inclusive than reduce's actual keep decision, which
        // additionally checks `used`. The walk intentionally over-approximates
        // to include all potentially useful structural information.
        arena.lbd(off) <= self.tier2_lbd
    }
}

/// CB values for ProbSAT scoring based on average clause size.
/// From Adrian Balint's thesis on ProbSAT.
/// Higher clause sizes need higher CB (more selective scoring).
const CB_VALUES: [(f64, f64); 6] = [
    (0.0, 2.00),
    (3.0, 2.50),
    (4.0, 2.85),
    (5.0, 3.70),
    (6.0, 5.10),
    (7.0, 7.40),
];

/// Interpolate CB value for a given average clause size.
///
/// Clamps to the last table entry for sizes beyond the table range.
/// Without clamping, linear extrapolation produces extreme CB values
/// (e.g., CB=27 for avg size 15.5) that make ProbSAT degenerate into
/// a greedy walk, unable to escape local minima.
///
/// Reference: Kissat `walk.c:fit_cbval()` — clamps to table bounds.
fn fit_cb_value(size: f64) -> f64 {
    // Clamp: sizes beyond the table get the last CB value.
    let (last_x, last_y) = CB_VALUES[CB_VALUES.len() - 1];
    if size >= last_x {
        return last_y;
    }
    // Sizes below the first entry get the first CB value.
    let (first_x, first_y) = CB_VALUES[0];
    if size <= first_x {
        return first_y;
    }
    // Find the segment containing `size` and interpolate.
    let mut i = 0;
    while i + 2 < CB_VALUES.len() && CB_VALUES[i + 1].0 < size {
        i += 1;
    }
    let (x1, y1) = CB_VALUES[i];
    let (x2, y2) = CB_VALUES[i + 1];
    let dx = x2 - x1;
    let dy = y2 - y1;
    dy * (size - x1) / dx + y1
}

/// Simple linear congruential generator for random numbers.
/// Based on CaDiCaL's Random class (Knuth LCG constants).
pub(crate) struct Random {
    state: u64,
}

impl Random {
    pub(crate) fn new(seed: u64) -> Self {
        Self {
            state: seed.wrapping_mul(6364136223846793005).wrapping_add(1),
        }
    }

    pub(crate) fn next(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    pub(crate) fn pick(&mut self, max: usize) -> usize {
        if max == 0 {
            return 0;
        }
        (self.next() % max as u64) as usize
    }

    pub(crate) fn generate_double(&mut self) -> f64 {
        (self.next() as f64) / (u64::MAX as f64)
    }
}

/// Statistics from walk phase
#[derive(Debug, Default, Clone)]
pub(crate) struct WalkStats {
    pub walk_count: u64,     // rounds executed
    pub flips: u64,          // total flips
    pub broken_total: u64,   // total broken clauses encountered
    pub best_minimum: u64,   // best (min) broken count found
    pub initial_broken: u64, // broken at walk start
}

/// Convert literal to occurrence list index: pos=2*v, neg=2*v+1
#[inline]
fn lit_to_occurs_idx(lit: Literal) -> usize {
    let var = lit.variable().index();
    if lit.is_positive() {
        2 * var
    } else {
        2 * var + 1
    }
}

/// Check if a clause should be included in the walk.
///
/// Includes all original (irredundant) clauses plus learned clauses that are
/// "likely to be kept" by the next `reduce_db`: core (LBD ≤ 2) and recently-used
/// tier-1 (LBD ≤ 6, used > 0) clauses.
///
/// Reference: CaDiCaL `walk.cpp` — `walkredundant` option includes likely-to-be-kept
/// learned clauses so the walk sees discovered structural information.
/// ProbSAT random walk: flip variables to minimize unsatisfied clauses,
/// saving best phases for CDCL. O(1) amortized via occurrence lists.
///
/// The `filter` parameter controls which clauses are included. By default,
/// only irredundant clauses are used. With `include_likely_kept`, learned
/// clauses that would survive the next `reduce_db` are also included,
/// giving the walk a more accurate picture of the formula.
/// Reference: CaDiCaL `walk.cpp` — `walkredundant` option.
#[allow(clippy::too_many_arguments)]
pub(crate) fn walk(
    clause_db: &ClauseArena,
    num_vars: usize,
    phases: &mut [i8],
    prev_phases: &mut [bool],
    stats: &mut WalkStats,
    seed: u64,
    tick_limit: u64,
    filter: WalkFilter,
) -> bool {
    debug_assert!(
        phases.len() >= num_vars,
        "BUG: walk phases.len()={} < num_vars={num_vars}",
        phases.len(),
    );
    stats.walk_count += 1;

    let mut walker = Walker::new(
        num_vars,
        clause_db.len(),
        seed.wrapping_add(stats.walk_count),
        tick_limit,
    );

    // CaDiCaL walk.cpp:834: initialize from prev phases (walk continuity).
    // First walk uses current phases; subsequent walks build on prior walk results.
    let use_prev = stats.walk_count > 1 && prev_phases.len() >= num_vars;
    for i in 0..num_vars {
        let val = if use_prev {
            prev_phases[i]
        } else {
            phases[i] >= 0 // 0 (unset) defaults to true
        };
        walker.values[i] = val;
        walker.best_values[i] = val;
    }

    let mut total_lits: usize = 0;
    let mut num_clauses: usize = 0;
    for clause_off in clause_db.indices() {
        if !filter.should_include(clause_db, clause_off) {
            continue;
        }

        let lits = clause_db.literals(clause_off);
        total_lits += lits.len();
        num_clauses += 1;

        let mut sat_count = 0u32;
        for &lit in lits {
            // Add to occurrence list (keyed by clause word offset)
            let occurs_idx = lit_to_occurs_idx(lit);
            if occurs_idx < walker.occurs.len() {
                walker.occurs[occurs_idx].push(clause_off);
            }

            let var_idx = lit.variable().index();
            if var_idx < walker.values.len() {
                let val = walker.values[var_idx];
                let lit_sat = (lit.is_positive() && val) || (!lit.is_positive() && !val);
                if lit_sat {
                    sat_count += 1;
                }
            }
        }

        walker.sat_count[clause_off] = sat_count;
        if sat_count == 0 {
            walker.add_broken(clause_off);
        }

        walker.ticks += lits.len() as u64;
    }

    // Compute average clause size for CB parameter
    let avg_size = if num_clauses > 0 {
        total_lits as f64 / num_clauses as f64
    } else {
        3.0
    };
    walker.populate_table(avg_size, stats.walk_count);

    // Save initial minimum
    walker.minimum = walker.broken.len();
    stats.initial_broken = walker.minimum as u64;
    stats.best_minimum = walker.minimum as u64;

    // Record initial model as best
    walker.save_minimum(num_vars);

    // Main walk loop
    while !walker.broken.is_empty() && walker.ticks < walker.limit {
        walker.ticks += 1;
        stats.flips += 1;
        stats.broken_total += walker.broken.len() as u64;

        // Pick random broken clause
        let broken_idx = walker.random.pick(walker.broken.len());
        let clause_idx = walker.broken[broken_idx];

        // Score literals in the broken clause (clause_idx is a word offset).
        // Reference: CaDiCaL walk_full_occs.cpp:walk_full_occs_pick_lit()
        let lits = clause_db.literals(clause_idx);

        walker.scores_buf.clear();
        let mut sum = 0.0;
        // Track which var each score corresponds to (use indices into lits)
        let mut first_var = 0usize;
        let mut num_scored = 0usize;

        for &lit in lits {
            let var_idx = lit.variable().index();
            if var_idx >= walker.values.len() {
                continue;
            }
            // All literals in broken clause are false, so we want to flip one to true.
            // Break value: how many satisfied clauses would become broken.
            let true_lit_idx = if walker.values[var_idx] {
                2 * var_idx
            } else {
                2 * var_idx + 1
            };
            // Tick for occurrence list scan in break-value computation
            if true_lit_idx < walker.occurs.len() {
                walker.ticks += 1 + (walker.occurs[true_lit_idx].len() as u64 / 8);
            }
            let break_val = walker.compute_break_value(var_idx);
            let s = walker.score(break_val);
            walker.scores_buf.push(s);
            if num_scored == 0 {
                first_var = var_idx;
            }
            num_scored += 1;
            sum += s;
        }

        if sum == 0.0 || num_scored == 0 {
            continue;
        }

        // Sample literal proportional to score
        let threshold = sum * walker.random.generate_double();
        let mut cumsum = 0.0;
        let mut flip_var = first_var;

        let mut score_idx = 0;
        for &lit in lits {
            let var_idx = lit.variable().index();
            if var_idx >= walker.values.len() {
                continue;
            }
            if score_idx < walker.scores_buf.len() {
                cumsum += walker.scores_buf[score_idx];
                flip_var = var_idx;
                score_idx += 1;
                if cumsum > threshold {
                    break;
                }
            }
        }

        // Flip the chosen variable (O(degree) incremental update)
        walker.flip(flip_var);

        // Record on flips trail for lazy best-model tracking
        walker.push_flipped(flip_var);

        // Check for new minimum
        if walker.broken.len() < walker.minimum {
            walker.save_minimum(num_vars);
            stats.best_minimum = walker.minimum as u64;

            // If we found a satisfying assignment, we're done
            if walker.minimum == 0 {
                break;
            }
        }
    }

    // Finalize best model from trail
    walker.save_final_minimum();

    // Copy best phases back to phases array
    for (phase, &best) in phases
        .iter_mut()
        .zip(walker.best_values.iter())
        .take(num_vars)
    {
        *phase = if best { 1 } else { -1 };
    }

    // Save to prev_phases for next walk round continuity (CaDiCaL walk.cpp:228).
    for (prev, &best) in prev_phases
        .iter_mut()
        .zip(walker.best_values.iter())
        .take(num_vars)
    {
        *prev = best;
    }

    // Return true if we found a satisfying assignment
    walker.minimum == 0
}

// CaDiCaL walk effort scheduling constants.
// Reference: CaDiCaL `options.hpp` lines 274-277.

/// Walk effort as per-mille of search tick delta.
/// Kissat: `walkeffort = 50` (options.h:168).
/// CaDiCaL: `walkeffort = 80` (options.hpp:274).
/// AY uses Kissat's value (50). CaDiCaL's higher value (80) was tried but
/// Kissat's schedule is the better match: Kissat only walks irredundant
/// clauses and rephases only in stable mode, so a tighter walk budget
/// prevents over-investment in local search on hard instances (#8466).
pub(crate) const WALK_EFFORT_PER_MILLE: u64 = 50;

/// Minimum walk effort (ticks).
/// CaDiCaL: `walkmineff = 0` (options.hpp:277). Kissat: `mineffort = 10`
/// (10M global floor applied to all effort-limited techniques, options.h:80).
/// AY uses Kissat's global floor: walk needs enough budget for meaningful
/// exploration even when search ticks delta is small (e.g., early rephase
/// cycles or small instances). 10M ticks lets ProbSAT perform thousands
/// of flips on formulas with typical clause densities.
/// Reference: Kissat `kimits.h:143` — `MINEFFORT = 1e6 * GET_OPTION(mineffort)`.
pub(crate) const WALK_MIN_EFFORT: u64 = 10_000_000;

/// Maximum walk effort (in 1e3 ticks; actual max = this * 1000).
/// CaDiCaL: `walkmaxeff = 1e7` (options.hpp:276, so max = 1e10).
pub(crate) const WALK_MAX_EFFORT: u64 = 10_000_000;

/// Compute walk tick limit from search propagation delta.
///
/// Reference: CaDiCaL `walk.cpp:walk()` / `walk_full_occs.cpp:walk_full_occs()`.
/// Formula: `limit = (search_ticks_delta) * walkeffort / 1000`, clamped.
pub(crate) fn compute_walk_effort(propagation_delta: u64) -> u64 {
    let raw = propagation_delta.saturating_mul(WALK_EFFORT_PER_MILLE) / 1000;
    raw.max(WALK_MIN_EFFORT)
        .min(WALK_MAX_EFFORT.saturating_mul(1000))
}
