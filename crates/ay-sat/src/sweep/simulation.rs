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
        self.find_candidates_by_simulation_budgeted(clauses, vals, frozen, None)
            .0
    }

    /// The simulation with its work charged to a tick budget: one tick per
    /// literal of the copied formula, per variable visited in a round and per
    /// clause scanned by the propagation. The round loop stops after the
    /// round in which the budget runs out, so at least one round runs; the
    /// signatures then have `rounds` bits, and the complement fold and the
    /// polarity majority read only those bits. Returns the classes, the
    /// rounds run and the ticks spent. Without a budget it is the 64-round
    /// simulation, whose 64 passes over the formula cost about a second per
    /// in-search sweep on a 263K-clause formula (schooltt-5-3, 2026-09-21)
    /// while the kitten budget it fed was a few million ticks.
    pub(super) fn find_candidates_by_simulation_budgeted(
        &self,
        clauses: &ClauseArena,
        vals: &[i8],
        frozen: &[u32],
        tick_budget: Option<u64>,
    ) -> (Vec<Vec<u32>>, u64, u64) {
        let num_vars = self.num_vars;
        if num_vars == 0 {
            return (Vec::new(), 0, 0);
        }

        // Collect clause data once.
        // Skip garbage, empty, and large learned clauses (matching COI filter).
        let clause_data: Vec<Vec<Literal>> = clauses
            .indices()
            .filter(|&idx| {
                !clauses.is_dead(idx) && (!clauses.is_learned(idx) || clauses.len_of(idx) <= 2)
            })
            .map(|idx| clauses.literals(idx).to_vec())
            .collect();

        if clause_data.is_empty() {
            return (Vec::new(), 0, 0);
        }

        let num_lits = num_vars * 2;
        let mut ticks: u64 = 0;

        // ── Build per-literal occurrence lists ──────────────────────────
        // occ_lists[lit_idx] = vec of clause indices in clause_data containing
        // that literal. Used for queue-driven propagation: when a literal is
        // falsified, scan only clauses containing it for unit implications.
        // Reference: CaDiCaL sweep_dense_propagate uses occs(-lit).
        let mut occ_lists: Vec<Vec<usize>> = vec![Vec::new(); num_lits];
        for (ci, lits) in clause_data.iter().enumerate() {
            ticks += lits.len() as u64;
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

        let mut rounds_run: u64 = 0;
        for round in 0..MAX_SIMULATION_ROUNDS {
            ticks += num_vars as u64;
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
                    &mut ticks,
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
            rounds_run += 1;
            // A stop ends the rounds too; the caller then verifies nothing.
            if tick_budget.is_some_and(|budget| ticks >= budget)
                || self.kitten.terminator().raised()
            {
                break;
            }
        }
        // The bits the rounds wrote; the complement fold and the majority
        // must not read the unwritten ones when the budget cut the rounds.
        let signature_mask = if rounds_run >= 64 {
            u64::MAX
        } else {
            (1u64 << rounds_run) - 1
        };
        let majority_rounds = (rounds_run / 2) as u32;

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
            let complement = !sig & signature_mask;
            let majority_positive = sig.count_ones() > majority_rounds;

            let (canon_sig, signed_lit) = if sig <= complement {
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
                (complement, lit)
            };

            classes.entry(canon_sig).or_default().push(signed_lit);
        }

        // 6. Filter: keep only classes with 2+ members.
        let classes = classes
            .into_values()
            .filter(|class| class.len() >= 2)
            .collect();
        (classes, rounds_run, ticks)
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
        ticks: &mut u64,
    ) {
        let mut qi: usize = 0;
        let mut steps: u32 = 0;

        while qi < queue.len() && steps < MAX_PROPAGATION_STEPS {
            // The queue contains literal indices that were just falsified.
            // Scan all clauses containing this literal for unit implications.
            let Some(&falsified_lit_idx) = queue.get(qi) else {
                break;
            };
            let Some(next_qi) = qi.checked_add(1) else {
                break;
            };
            qi = next_qi;

            if falsified_lit_idx >= num_lits {
                continue;
            }
            let Some(occ) = occ_lists.get(falsified_lit_idx) else {
                continue;
            };

            for &ci in occ {
                steps = steps.saturating_add(1);
                *ticks = ticks.saturating_add(1);
                let Some(lits) = clause_data.get(ci) else {
                    continue;
                };

                let mut satisfied = false;
                let mut unassigned_lit = Literal(0);
                let mut unassigned_count = 0u32;

                for &lit in lits {
                    let li = lit.index();
                    if li >= num_lits {
                        continue;
                    }
                    let Some(&v) = sim_vals.get(li) else {
                        continue;
                    };
                    if v > 0 {
                        satisfied = true;
                        break;
                    } else if v == 0 {
                        unassigned_count = unassigned_count.saturating_add(1);
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
                if li < num_lits && sim_vals.get(li) == Some(&0) {
                    let neg_idx = sim_assign(sim_vals, unassigned_lit);
                    // Enqueue the negation of the forced literal for further propagation.
                    queue.push(neg_idx);
                }
            }
        }
    }
}

#[cfg(test)]
mod budget_tests {
    use super::super::Sweeper;
    use crate::clause_arena::ClauseArena;
    use crate::test_util::lit;

    /// A tick budget cuts the simulation after the round that exhausts it: one
    /// tick is enough for one round (the loop checks after each round), the
    /// signatures then carry one bit, and the propagation-forced pair x0/x1 still
    /// lands in one class. Without a budget all 64 rounds run.
    #[test]
    fn simulation_stops_after_the_round_that_exhausts_the_budget() {
        let mut clauses = ClauseArena::new();
        clauses.add(&[lit(0, true), lit(1, false)], false);
        clauses.add(&[lit(0, false), lit(1, true)], false);
        clauses.add(&[lit(2, true), lit(3, true)], false);
        clauses.add(&[lit(2, false), lit(3, false)], false);
        let vals = vec![0i8; 8];
        let frozen: Vec<u32> = vec![0; 4];
        let sweeper = Sweeper::new(4);

        let (classes, rounds, ticks) =
            sweeper.find_candidates_by_simulation_budgeted(&clauses, &vals, &frozen, Some(1));
        assert_eq!(rounds, 1);
        assert!(
            ticks >= 8,
            "the copied literals alone are 8 ticks, got {ticks}"
        );
        let x0_class = classes.iter().find(|c| c.iter().any(|&l| l >> 1 == 0));
        assert!(
            x0_class.is_some_and(|c| c.iter().any(|&l| l >> 1 == 1)),
            "x0 and x1 are forced equal and must share a class after one round: {classes:?}"
        );

        let (_, rounds, _) =
            sweeper.find_candidates_by_simulation_budgeted(&clauses, &vals, &frozen, None);
        assert_eq!(rounds, 64);
        let (_, rounds, _) = sweeper.find_candidates_by_simulation_budgeted(
            &clauses,
            &vals,
            &frozen,
            Some(u64::MAX),
        );
        assert_eq!(rounds, 64);
    }
}
