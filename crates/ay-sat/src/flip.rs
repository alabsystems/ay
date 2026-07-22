// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Flip-based local search for phase initialization during rephasing.
//!
//! A lightweight alternative to ProbSAT walk that evaluates the current phase
//! assignment against all clauses and greedily flips variables that reduce the
//! number of unsatisfied clauses. Cheaper than walk because it operates on
//! phase arrays without building full occurrence lists.
//!
//! Algorithm:
//! 1. Evaluate all clauses under current phases, computing per-variable
//!    make-count (unsatisfied clauses that would become satisfied on flip)
//!    and break-count (satisfied clauses that would become unsatisfied).
//! 2. Greedily flip variables with positive net gain (make > break),
//!    processing in decreasing order of gain.
//! 3. Save the best assignment (minimum unsatisfied count) found during
//!    the greedy pass.
//!
//! Triggered during rephase as a cheaper complement to walk. While walk does
//! sophisticated stochastic search (ProbSAT), flip does deterministic greedy
//! improvement -- fast to compute but may get stuck in local minima. The two
//! techniques complement each other in the rephase schedule.
//!
//! Reference: CaDiCaL `flip.cpp` — flip-feasibility check and trail update.
//! Adapted to AY's phase-only (off-trail) rephase context.

use crate::clause_arena::ClauseArena;
use crate::walk::WalkFilter;

#[cfg(test)]
mod tests;

/// Statistics from flip-based local search.
#[derive(Debug, Default, Clone)]
pub(crate) struct FlipStats {
    /// Number of flip rounds executed.
    pub(crate) rounds: u64,
    /// Total variables flipped across all rounds.
    pub(crate) flips: u64,
    /// Best (minimum) unsatisfied clause count found.
    pub(crate) best_unsat: u64,
}

/// Flip-based local search: greedily flip variables to reduce unsatisfied clauses.
///
/// Operates on the `phases` array (not the solver trail). Modifies `phases` in
/// place with the best assignment found. Returns true if a fully satisfying
/// assignment was found.
///
/// `tick_limit` bounds the computational effort (measured in clause-literal scans).
#[allow(clippy::too_many_arguments)]
pub(crate) fn flip_search(
    clause_db: &ClauseArena,
    num_vars: usize,
    phases: &mut [i8],
    stats: &mut FlipStats,
    tick_limit: u64,
    filter: WalkFilter,
) -> bool {
    debug_assert!(
        phases.len() >= num_vars,
        "BUG: flip phases.len()={} < num_vars={num_vars}",
        phases.len(),
    );
    stats.rounds += 1;

    // Phase 1: Evaluate all clauses under the current phase assignment.
    // Compute per-clause satisfaction count and per-variable make/break scores.

    // make[v]: number of currently-unsatisfied clauses where flipping v would satisfy
    // break_count[v]: number of currently-satisfied clauses where v is the sole satisfier
    let mut make = vec![0i32; num_vars];
    let mut break_count = vec![0i32; num_vars];
    let mut unsat_count: usize = 0;
    let mut ticks: u64 = 0;

    for clause_off in clause_db.indices() {
        if !filter.should_include(clause_db, clause_off) {
            continue;
        }

        let lits = clause_db.literals(clause_off);
        ticks += lits.len() as u64;
        if ticks > tick_limit {
            // Over budget during evaluation -- return without modifying phases.
            return false;
        }

        // Count how many literals are satisfied by current phases, and track
        // the sole satisfier (if exactly one).
        let mut sat = 0u32;
        let mut sole_satisfier: usize = usize::MAX; // var index of sole satisfier

        for &lit in lits {
            let var = lit.variable().index();
            if var >= num_vars {
                continue;
            }
            let phase_val = phases[var];
            let lit_sat =
                (lit.is_positive() && phase_val >= 0) || (!lit.is_positive() && phase_val < 0);
            if lit_sat {
                sat += 1;
                sole_satisfier = var;
            }
        }

        if sat == 0 {
            // Clause is unsatisfied: flipping any literal in it would satisfy it.
            unsat_count += 1;
            for &lit in lits {
                let var = lit.variable().index();
                if var < num_vars {
                    make[var] += 1;
                }
            }
        } else if sat == 1 {
            // Clause has exactly one satisfier: flipping it would break the clause.
            if sole_satisfier < num_vars {
                break_count[sole_satisfier] += 1;
            }
        }
        // sat >= 2: clause is robust, flipping any single variable won't break it.
    }

    stats.best_unsat = unsat_count as u64;

    if unsat_count == 0 {
        // Already satisfying -- nothing to do.
        return true;
    }

    // Phase 2: Compute net gain for each variable and sort by decreasing gain.
    // gain[v] = make[v] - break_count[v]
    // Only consider variables with positive gain.

    let mut candidates: Vec<(usize, i32)> = Vec::new();
    for v in 0..num_vars {
        let gain = make[v] - break_count[v];
        if gain > 0 {
            candidates.push((v, gain));
        }
    }

    // Sort by decreasing gain (higher gain first).
    candidates.sort_unstable_by_key(|b| std::cmp::Reverse(b.1));

    // Phase 3: Greedily apply flips. After each flip, we need to update
    // make/break counts for affected clauses. For efficiency, we do a
    // simplified greedy pass: flip in sorted order without incremental update.
    // Then re-evaluate to find actual improvement.

    // Save current phases as best.
    let mut best_phases: Vec<i8> = phases[..num_vars].to_vec();
    let mut best_unsat = unsat_count;

    // Apply flips greedily.
    for &(var, _gain) in &candidates {
        ticks += 1;
        if ticks > tick_limit {
            break;
        }

        // Flip the variable's phase.
        phases[var] = -phases[var];
        if phases[var] == 0 {
            // Was unset (0): flipping 0 gives 0. Set to 1 instead.
            phases[var] = 1;
        }
        stats.flips += 1;
    }

    // Re-evaluate after greedy pass.
    let mut new_unsat: usize = 0;
    for clause_off in clause_db.indices() {
        if !filter.should_include(clause_db, clause_off) {
            continue;
        }

        let lits = clause_db.literals(clause_off);
        ticks += lits.len() as u64;

        let mut sat = false;
        for &lit in lits {
            let var = lit.variable().index();
            if var >= num_vars {
                continue;
            }
            let phase_val = phases[var];
            let lit_sat =
                (lit.is_positive() && phase_val >= 0) || (!lit.is_positive() && phase_val < 0);
            if lit_sat {
                sat = true;
                break;
            }
        }
        if !sat {
            new_unsat += 1;
        }
    }

    if new_unsat < best_unsat {
        // Greedy pass improved -- keep the flipped phases.
        best_unsat = new_unsat;
        best_phases.clear();
        best_phases.extend_from_slice(&phases[..num_vars]);
    }

    // Phase 4: If still unsatisfied, try a second pass flipping individual
    // variables from the current state to find further local improvements.
    if best_unsat > 0 && ticks < tick_limit {
        // Recompute make/break from current best state.
        phases[..num_vars].copy_from_slice(&best_phases);

        let mut make2 = vec![0i32; num_vars];
        let mut break2 = vec![0i32; num_vars];

        for clause_off in clause_db.indices() {
            if !filter.should_include(clause_db, clause_off) {
                continue;
            }
            let lits = clause_db.literals(clause_off);
            ticks += lits.len() as u64;
            if ticks > tick_limit {
                break;
            }

            let mut sat = 0u32;
            let mut sole: usize = usize::MAX;
            for &lit in lits {
                let var = lit.variable().index();
                if var >= num_vars {
                    continue;
                }
                let phase_val = phases[var];
                let lit_sat =
                    (lit.is_positive() && phase_val >= 0) || (!lit.is_positive() && phase_val < 0);
                if lit_sat {
                    sat += 1;
                    sole = var;
                }
            }

            if sat == 0 {
                for &lit in lits {
                    let var = lit.variable().index();
                    if var < num_vars {
                        make2[var] += 1;
                    }
                }
            } else if sat == 1 && sole < num_vars {
                break2[sole] += 1;
            }
        }

        // Try individual flips with positive gain.
        for v in 0..num_vars {
            if ticks > tick_limit {
                break;
            }
            let gain = make2[v] - break2[v];
            if gain > 0 {
                phases[v] = -phases[v];
                if phases[v] == 0 {
                    phases[v] = 1;
                }
                stats.flips += 1;
                ticks += 1;
            }
        }

        // Re-evaluate after second pass.
        let mut new_unsat2: usize = 0;
        for clause_off in clause_db.indices() {
            if !filter.should_include(clause_db, clause_off) {
                continue;
            }
            let lits = clause_db.literals(clause_off);
            let mut sat = false;
            for &lit in lits {
                let var = lit.variable().index();
                if var >= num_vars {
                    continue;
                }
                let phase_val = phases[var];
                let lit_sat =
                    (lit.is_positive() && phase_val >= 0) || (!lit.is_positive() && phase_val < 0);
                if lit_sat {
                    sat = true;
                    break;
                }
            }
            if !sat {
                new_unsat2 += 1;
            }
        }

        if new_unsat2 < best_unsat {
            best_unsat = new_unsat2;
            best_phases.clear();
            best_phases.extend_from_slice(&phases[..num_vars]);
        }
    }

    // Restore best phases found.
    phases[..num_vars].copy_from_slice(&best_phases);
    stats.best_unsat = best_unsat as u64;

    best_unsat == 0
}

/// Flip effort as per-mille of search tick delta.
/// Lower than walk (80) since flip is a lightweight complement.
pub(crate) const FLIP_EFFORT_PER_MILLE: u64 = 40;

/// Minimum flip effort (ticks).
/// Smaller than walk's 10M since flip is cheaper per round.
pub(crate) const FLIP_MIN_EFFORT: u64 = 1_000_000;

/// Maximum flip effort (in 1e3 ticks; actual max = this * 1000).
pub(crate) const FLIP_MAX_EFFORT: u64 = 5_000_000;

/// Compute flip tick limit from search propagation delta.
pub(crate) fn compute_flip_effort(propagation_delta: u64) -> u64 {
    let raw = propagation_delta.saturating_mul(FLIP_EFFORT_PER_MILLE) / 1000;
    raw.max(FLIP_MIN_EFFORT)
        .min(FLIP_MAX_EFFORT.saturating_mul(1000))
}
