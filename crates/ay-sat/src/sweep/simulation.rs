// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Random simulation-based equivalence candidate finding.
//!
//! Assigns random boolean values to variables incrementally with unit
//! propagation between decisions. Variables that receive the same simulation
//! value across all rounds are equivalence candidates.
//!
//! This is a cheap pre-filter for kitten probing: it reduces the number of
//! expensive SAT-based equivalence checks by quickly eliminating obviously
//! non-equivalent variable pairs.
//!
//! Algorithm:
//! 1. Build per-literal occurrence lists for efficient propagation
//! 2. Sort variables by ascending occurrence count (fewer occs = assign first)
//! 3. For each round, start with all variables unassigned (except level-0 fixed)
//! 4. Iterate variables in occurrence-sorted order (with per-round randomization
//!    within equal-occurrence groups); for each unassigned variable:
//!    - Assign it a random value
//!    - Queue-driven propagation scans only clauses containing the falsified
//!      literal and forces unit implications
//! 5. Record each variable's final value as one bit of its 64-bit signature
//! 6. Group variables by signature (with complement folding for negation-equiv)
//! 7. Return candidate equivalence classes for kitten verification
//!
//! Improvements over naive approach (prior to #6868 audit):
//! - Occurrence-list propagation: O(affected clauses) per decision instead of
//!   O(all clauses). Reference: CaDiCaL sweep_dense_propagate().
//! - Signature-majority polarity: signed literal uses popcount(sig) > 32
//!   instead of last-round sim_vals, eliminating dependence on final round.
//! - Occurrence-count ordering: variables with fewer occurrences are decided
//!   first. They're less likely to be forced by propagation, increasing
//!   simulation diversity.
//!
//! Reference: circuit equivalence checking / SAT sweeping literature.

use std::collections::BTreeMap;

use super::Sweeper;
use crate::clause_arena::ClauseArena;
use crate::literal::Literal;

/// Number of random simulation rounds.
/// Each round produces one bit of the per-variable signature.
/// 64 rounds = 64-bit signature, giving 2^-64 false-positive probability
/// for any single pair.
const MAX_SIMULATION_ROUNDS: u32 = 64;

/// Maximum number of propagation steps per decision.
/// Queue-driven propagation is typically fast; this bounds pathological cases.
const MAX_PROPAGATION_STEPS: u32 = 10_000;

/// Simple XorShift64 PRNG for fast random simulation.
/// No external dependencies; deterministic given a seed.
struct XorShift64 {
    state: u64,
}

impl XorShift64 {
    fn new(seed: u64) -> Self {
        Self {
            state: if seed == 0 {
                0x5A5A_5A5A_5A5A_5A5A
            } else {
                seed
            },
        }
    }

    #[inline]
    fn next(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    #[inline]
    fn next_bool(&mut self) -> bool {
        (self.next() & 1) != 0
    }

    /// Fisher-Yates shuffle of a contiguous sub-slice `[start..end)`.
    fn shuffle_range(&mut self, slice: &mut [usize], start: usize, end: usize) {
        if end <= start + 1 {
            return;
        }
        for i in (start + 1..end).rev() {
            let j = start + (self.next() as usize) % (i - start + 1);
            slice.swap(i, j);
        }
    }
}

/// Assign a literal true in the simulation values buffer.
/// Returns the negated literal index for propagation queue use.
#[inline]
fn sim_assign(sim_vals: &mut [i8], lit: Literal) -> usize {
    let li = lit.index();
    let neg_li = lit.negated().index();
    if li < sim_vals.len() && neg_li < sim_vals.len() {
        sim_vals[li] = 1;
        sim_vals[neg_li] = -1;
    }
    neg_li
}

impl Sweeper {
    /// Find equivalence candidate classes via random simulation.
    ///
    /// Returns equivalence classes as `Vec<Vec<u32>>` where each inner vec
    /// contains signed literal indices that had identical simulation signatures.
    /// The caller should verify these candidates with kitten probing.
    ///
    /// Signed literal convention matches the existing probe code: each class
    /// member is the literal (positive or negative) whose polarity dominated
    /// the simulation signature (popcount > 32).
    pub(super) fn find_candidates_by_simulation(
        &self,
        clauses: &ClauseArena,
        vals: &[i8],
        frozen: &[u32],
    ) -> Vec<Vec<u32>> {
        let num_vars = self.num_vars;
        if num_vars == 0 {
            return Vec::new();
        }

        // Collect clause data once.
        // Skip garbage, empty, and large learned clauses (matching COI filter).
        let clause_data: Vec<Vec<Literal>> = clauses
            .indices()
            .filter(|&idx| {
                !clauses.is_garbage(idx)
                    && !clauses.is_empty_clause(idx)
                    && (!clauses.is_learned(idx) || clauses.len_of(idx) <= 2)
            })
            .map(|idx| clauses.literals(idx).to_vec())
            .collect();

        if clause_data.is_empty() {
            return Vec::new();
        }

        let num_lits = num_vars * 2;

        // ── Build per-literal occurrence lists ──────────────────────────
        // occ_lists[lit_idx] = vec of clause indices in clause_data containing
        // that literal. Used for queue-driven propagation: when a literal is
        // falsified, scan only clauses containing it for unit implications.
        // Reference: CaDiCaL sweep_dense_propagate uses occs(-lit).
        let mut occ_lists: Vec<Vec<usize>> = vec![Vec::new(); num_lits];
        for (ci, lits) in clause_data.iter().enumerate() {
            for &lit in lits {
                let li = lit.index();
                if li < num_lits {
                    occ_lists[li].push(ci);
                }
            }
        }

        // ── Build occurrence-count-sorted variable order ────────────────
        // Sort by ascending total occurrence count (pos + neg). Variables
        // with fewer occurrences are decided first because they're less
        // constrained and thus less likely to be forced by propagation,
        // increasing simulation diversity.
        // Within equal-occurrence groups, we shuffle per-round for variety.
        let mut occ_counts: Vec<u32> = vec![0; num_vars];
        for (var, occ_count) in occ_counts.iter_mut().enumerate().take(num_vars) {
            let pos = var * 2;
            let neg = pos + 1;
            let p = if pos < num_lits {
                occ_lists[pos].len() as u32
            } else {
                0
            };
            let n = if neg < num_lits {
                occ_lists[neg].len() as u32
            } else {
                0
            };
            *occ_count = p + n;
        }

        let mut var_order: Vec<usize> = (0..num_vars).collect();
        var_order.sort_by_key(|&v| occ_counts[v]);

        // Precompute group boundaries for equal-occurrence shuffling.
        let mut group_bounds: Vec<(usize, usize)> = Vec::new();
        {
            let mut i = 0;
            while i < var_order.len() {
                let count = occ_counts[var_order[i]];
                let start = i;
                while i < var_order.len() && occ_counts[var_order[i]] == count {
                    i += 1;
                }
                if i - start > 1 {
                    group_bounds.push((start, i));
                }
            }
        }

        let mut signatures = vec![0u64; num_vars];
        let mut sim_vals = vec![0i8; num_lits];
        let mut prop_queue: Vec<usize> = Vec::new();
        let mut rng = XorShift64::new(0xDEAD_BEEF_CAFE_1234);

        for round in 0..MAX_SIMULATION_ROUNDS {
            // 1. Reset simulation values. Copy level-0 fixed assignments.
            for v in sim_vals.iter_mut() {
                *v = 0;
            }
            for var in 0..num_vars {
                let pos_idx = var * 2;
                let neg_idx = var * 2 + 1;
                if pos_idx < vals.len() && vals[pos_idx] != 0 {
                    sim_vals[pos_idx] = vals[pos_idx];
                    sim_vals[neg_idx] = vals[neg_idx];
                }
            }

            // 2. Shuffle within equal-occurrence groups for this round.
            for &(start, end) in &group_bounds {
                rng.shuffle_range(&mut var_order, start, end);
            }

            // 3. Assign variables in order with queue-driven propagation.
            for &var in &var_order {
                let pos_idx = var * 2;
                if pos_idx >= num_lits {
                    continue;
                }
                // Skip already-assigned variables (fixed or propagated).
                if sim_vals[pos_idx] != 0 {
                    continue;
                }

                // Random decision.
                let decided_lit = if rng.next_bool() {
                    Literal(pos_idx as u32)
                } else {
                    Literal((pos_idx as u32) | 1)
                };
                let neg_idx = sim_assign(&mut sim_vals, decided_lit);

                // Queue-driven propagation from this decision.
                prop_queue.clear();
                prop_queue.push(neg_idx);
                Self::simulate_propagate_queued(
                    &clause_data,
                    &occ_lists,
                    &mut sim_vals,
                    &mut prop_queue,
                    num_lits,
                );
            }

            // 4. Record signature bit.
            let bit = 1u64 << (round & 63);
            for (var, signature) in signatures.iter_mut().enumerate().take(num_vars) {
                let pos_idx = var * 2;
                if pos_idx < num_lits && sim_vals[pos_idx] > 0 {
                    *signature |= bit;
                }
            }
        }

        // 5. Group variables by canonical signature.
        // Complement folding: if sig(A) = !sig(B), then A is equivalent to not-B.
        // Canonical signature = min(sig, !sig). If we use !sig, negate the literal.
        //
        // Signed literal polarity is determined by signature majority:
        // if popcount(sig) > 32, the variable was positive in the majority of
        // rounds, so use the positive literal. This is stable across rounds
        // (unlike using sim_vals from the last round which depends on the
        // random ordering of that particular round).
        let mut classes: BTreeMap<u64, Vec<u32>> = BTreeMap::new();

        for var in 0..num_vars {
            let pos_idx = var * 2;
            // Skip assigned variables.
            if pos_idx < vals.len() && vals[pos_idx] != 0 {
                continue;
            }
            // Skip frozen variables.
            if var < frozen.len() && frozen[var] > 0 {
                continue;
            }

            let sig = signatures[var];
            let majority_positive = sig.count_ones() > 32;

            let (canon_sig, signed_lit) = if sig <= !sig {
                // Use sig directly. Literal polarity follows signature majority.
                let lit = if majority_positive {
                    pos_idx as u32
                } else {
                    (pos_idx as u32) | 1
                };
                (sig, lit)
            } else {
                // Complement fold: use !sig. Negate the literal polarity
                // (if the variable was mostly positive, the complemented class
                // needs the negative literal, and vice versa).
                let lit = if majority_positive {
                    (pos_idx as u32) | 1
                } else {
                    pos_idx as u32
                };
                (!sig, lit)
            };

            classes.entry(canon_sig).or_default().push(signed_lit);
        }

        // 6. Filter: keep only classes with 2+ members.
        classes
            .into_values()
            .filter(|class| class.len() >= 2)
            .collect()
    }

    /// Queue-driven forward propagation using per-literal occurrence lists.
    ///
    /// When a literal is falsified (its negation was assigned true), scan only
    /// the clauses containing that literal for unit implications. Each newly
    /// forced literal enqueues its negation for further propagation.
    ///
    /// This is O(affected clauses) per propagation chain instead of O(all
    /// clauses) per pass, matching CaDiCaL's sweep_dense_propagate pattern.
    fn simulate_propagate_queued(
        clause_data: &[Vec<Literal>],
        occ_lists: &[Vec<usize>],
        sim_vals: &mut [i8],
        queue: &mut Vec<usize>,
        num_lits: usize,
    ) {
        let mut qi = 0;
        let mut steps: u32 = 0;

        while qi < queue.len() && steps < MAX_PROPAGATION_STEPS {
            // The queue contains literal indices that were just falsified.
            // Scan all clauses containing this literal for unit implications.
            let falsified_lit_idx = queue[qi];
            qi += 1;

            if falsified_lit_idx >= num_lits {
                continue;
            }

            for &ci in &occ_lists[falsified_lit_idx] {
                steps += 1;
                let lits = &clause_data[ci];

                let mut satisfied = false;
                let mut unassigned_lit = Literal(0);
                let mut unassigned_count = 0u32;

                for &lit in lits {
                    let li = lit.index();
                    if li >= num_lits {
                        continue;
                    }
                    let v = sim_vals[li];
                    if v > 0 {
                        satisfied = true;
                        break;
                    } else if v == 0 {
                        unassigned_count += 1;
                        if unassigned_count > 1 {
                            break; // Not unit, skip early
                        }
                        unassigned_lit = lit;
                    }
                }

                if satisfied || unassigned_count != 1 {
                    continue;
                }

                // Unit clause: force the remaining literal.
                let li = unassigned_lit.index();
                if li < num_lits && sim_vals[li] == 0 {
                    let neg_idx = sim_assign(sim_vals, unassigned_lit);
                    // Enqueue the negation of the forced literal for further propagation.
                    queue.push(neg_idx);
                }
            }
        }
    }
}
