// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Failed Literal Probing
//!
//! Failed literal probing is an inprocessing technique that detects literals
//! which lead to conflicts when assumed, determining their forced assignments.
//!
//! ## Algorithm
//!
//! For each candidate probe literal `p`:
//! 1. Temporarily assign `p` at decision level 1
//! 2. Propagate to completion
//! 3. If conflict is found: `p` is a "failed literal" and `¬p` must be true
//! 4. If no conflict: backtrack and try next probe
//!
//! ## Probe Selection
//!
//! We focus on "root" literals in the binary implication graph - literals
//! that appear negated in binary clauses but not positively. These are the
//! most likely to produce useful information through probing.
//!
//! ## Module Structure
//!
//! - `mod.rs`: Prober struct and probe candidate management
//! - `analysis.rs`: UIP extraction, dominator finding, hyper-binary resolution
//!
//! ## References
//!
//! - CaDiCaL probe.cpp
//! - Heule & van Maaren, "Look-Ahead Based SAT Solvers" (2009)

mod analysis;

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;

pub(crate) use analysis::{
    failed_literal_dominator, failed_literal_dominator_forced_only, find_failed_literal_uip,
    hyper_binary_resolve, DominatorFailure, FailedLiteralDominatorResult,
};

use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};

/// Statistics for failed literal probing
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct ProbeStats {
    /// Number of probing rounds
    pub rounds: u64,
    /// Number of literals probed
    pub probed: u64,
    /// Number of failed literals found
    pub failed: u64,
    /// Number of units derived (from failed literals)
    pub units_derived: u64,
    /// Number of hyper-binary resolutions performed
    pub hbrs: u64,
    /// Total size of reason clauses resolved via HBR
    pub hbr_sizes: u64,
    /// Number of redundant HBR clauses added
    pub hbr_redundant: u64,
    /// Number of original clauses subsumed by HBR
    pub hbr_subs: u64,
    /// Number of subsumed original clauses that were actually deleted
    pub hbr_subsumed_deleted: u64,
}

/// Failed literal prober
///
/// Identifies and probes candidate literals to find forced assignments.
pub(crate) struct Prober {
    /// Number of variables
    num_vars: usize,
    /// Probe candidates (literals to probe)
    probes: Vec<Literal>,
    /// Occurrence counts: how many times each literal appears in binary clauses
    /// Index: literal.index()
    bin_occs: Vec<u32>,
    /// Last propagation fixed point for each literal
    /// If `propfixed[lit]` >= current_fixed, no need to reprobe
    propfixed: Vec<i64>,
    /// Reusable scratch for 1UIP extraction during failed literal probing
    uip_seen: Vec<bool>,
    /// Statistics
    stats: ProbeStats,
    /// Search ticks at last probe call (for tick-proportional effort).
    /// CaDiCaL tracks `last.probe.ticks` (probe.cpp:797).
    last_search_ticks: u64,
}

impl Prober {
    /// Create a new prober for the given number of variables
    pub(crate) fn new(num_vars: usize) -> Self {
        let num_lits = num_vars * 2;
        Self {
            num_vars,
            probes: Vec::new(),
            bin_occs: vec![0; num_lits],
            propfixed: vec![-1; num_lits],
            uip_seen: vec![false; num_vars],
            stats: ProbeStats::default(),
            last_search_ticks: 0,
        }
    }

    /// Get search ticks at last probe call.
    pub(crate) fn last_search_ticks(&self) -> u64 {
        self.last_search_ticks
    }

    /// Record current search ticks for next effort computation.
    pub(crate) fn set_last_search_ticks(&mut self, ticks: u64) {
        self.last_search_ticks = ticks;
    }

    /// Ensure internal buffers can handle `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.num_vars >= num_vars {
            return;
        }
        self.num_vars = num_vars;
        let num_lits = num_vars.saturating_mul(2);
        if self.bin_occs.len() < num_lits {
            self.bin_occs.resize(num_lits, 0);
        }
        if self.propfixed.len() < num_lits {
            self.propfixed.resize(num_lits, -1);
        }
        if self.uip_seen.len() < num_vars {
            self.uip_seen.resize(num_vars, false);
        }
    }

    /// Get probing statistics
    pub(crate) fn stats(&self) -> &ProbeStats {
        &self.stats
    }

    /// Restore stats after compaction (compact preserves stats across rebuild).
    pub(crate) fn restore_stats(&mut self, stats: ProbeStats) {
        self.stats = stats;
    }

    /// Reusable 1UIP scratch for failed literal probing.
    pub(crate) fn uip_seen_mut(&mut self) -> &mut Vec<bool> {
        &mut self.uip_seen
    }

    /// Reset occurrence counts
    fn reset_occs(&mut self) {
        self.bin_occs.fill(0);
    }

    /// Count binary clause occurrences
    ///
    /// For each binary clause {a, b}:
    /// - Increment `bin_occs[a]` and `bin_occs[b]`
    fn count_binary_occurrences(&mut self, clauses: &ClauseArena, vals: &[i8]) {
        self.reset_occs();

        for idx in clauses.indices() {
            // Skip empty/deleted clauses
            if clauses.is_empty_clause(idx) {
                continue;
            }

            let lits = clauses.literals(idx);

            // Check if it's effectively binary (ignoring falsified literals at level 0).
            // Use fixed slots instead of Vec to avoid heap allocation per clause.
            let mut unassigned_count: u32 = 0;
            let mut slot_a = Literal::positive(Variable(0)); // placeholder
            let mut slot_b = Literal::positive(Variable(0)); // placeholder
            let mut is_satisfied = false;

            for &lit in lits {
                let li = lit.index();
                // Skip literals with out-of-bounds index
                if li >= vals.len() {
                    continue;
                }
                let v = vals[li];
                if v > 0 {
                    // Literal is satisfied
                    is_satisfied = true;
                    break;
                } else if v == 0 {
                    // Unassigned
                    match unassigned_count {
                        0 => slot_a = lit,
                        1 => slot_b = lit,
                        _ => {} // >2 unassigned: not binary, skip
                    }
                    unassigned_count += 1;
                }
                // else: v < 0, falsified literal, skip
            }

            if is_satisfied {
                continue;
            }

            // Only count actual binary clauses
            if unassigned_count == 2 {
                // Bounds check for bin_occs array
                if slot_a.index() < self.bin_occs.len() && slot_b.index() < self.bin_occs.len() {
                    self.bin_occs[slot_a.index()] += 1;
                    self.bin_occs[slot_b.index()] += 1;
                }
            }
        }
    }

    /// Generate probe candidates
    ///
    /// Probes are "root" literals in the binary implication graph:
    /// - Appear negated in binary clauses
    /// - Do not appear positively in binary clauses
    ///
    /// These are good candidates because probing them exercises the
    /// binary implication chain without immediately satisfying it.
    pub(crate) fn generate_probes(
        &mut self,
        clauses: &ClauseArena,
        vals: &[i8],
        current_fixed: i64,
    ) {
        self.probes.clear();
        self.count_binary_occurrences(clauses, vals);

        // Limit iteration to actual vals length and bin_occs capacity
        let max_lits = self.bin_occs.len();
        let max_vars = self.num_vars.min(vals.len() / 2).min(max_lits / 2);

        for var_idx in 0..max_vars {
            // Skip assigned variables
            if vals[var_idx * 2] != 0 {
                continue;
            }

            let var = Variable(var_idx as u32);
            let pos_lit = Literal::positive(var);
            let neg_lit = Literal::negative(var);

            // Bounds check for bin_occs and propfixed
            if pos_lit.index() >= max_lits || neg_lit.index() >= max_lits {
                continue;
            }
            if pos_lit.index() >= self.propfixed.len() || neg_lit.index() >= self.propfixed.len() {
                continue;
            }

            let pos_occs = self.bin_occs[pos_lit.index()];
            let neg_occs = self.bin_occs[neg_lit.index()];

            // Look for "roots": one polarity has binary clause occurrences,
            // the other doesn't. Probe the NEGATION of the appearing literal
            // so BCP falsifies it and exercises the implication chain.
            //
            // Example: {L, x} encodes !L -> x. If pos_occs > 0 (L appears),
            // probe neg_lit (!L): deciding !L=TRUE falsifies L, triggering
            // propagation x=TRUE via BCP on clauses watching L.
            if pos_occs > 0 && neg_occs == 0 {
                // pos_lit appears in binary clauses like {pos_lit, x}
                // Probe neg_lit to falsify pos_lit and trigger the chain
                if self.propfixed[neg_lit.index()] < current_fixed {
                    self.probes.push(neg_lit);
                }
            } else if neg_occs > 0 && pos_occs == 0 {
                // neg_lit appears in binary clauses like {neg_lit, x}
                // Probe pos_lit to falsify neg_lit and trigger the chain
                if self.propfixed[pos_lit.index()] < current_fixed {
                    self.probes.push(pos_lit);
                }
            }
        }

        // Sort probes by occurrence count (higher first) for better pruning
        let bin_occs_len = self.bin_occs.len();
        self.probes.sort_by(|a, b| {
            let a_idx = a.negated().index();
            let b_idx = b.negated().index();
            let a_occs = if a_idx < bin_occs_len {
                self.bin_occs[a_idx]
            } else {
                0
            };
            let b_occs = if b_idx < bin_occs_len {
                self.bin_occs[b_idx]
            } else {
                0
            };
            b_occs.cmp(&a_occs)
        });
    }

    /// Check if there are leftover probe candidates from a prior round.
    pub(crate) fn has_probes(&self) -> bool {
        !self.probes.is_empty()
    }

    /// Flush stale probe candidates: retain only active root literals.
    /// CaDiCaL probe.cpp:698-747: re-filters and re-sorts leftover probes
    /// from the previous round so they get priority in the next round.
    pub(crate) fn flush_probes(&mut self, clauses: &ClauseArena, vals: &[i8], current_fixed: i64) {
        self.count_binary_occurrences(clauses, vals);
        let max_lits = self.bin_occs.len();

        self.probes.retain(|&lit| {
            let var_idx = lit.variable().index();
            // Drop assigned or out-of-bounds
            if var_idx * 2 >= vals.len() || vals[var_idx * 2] != 0 {
                return false;
            }
            let idx = lit.index();
            if idx >= max_lits || idx >= self.propfixed.len() {
                return false;
            }
            // Drop if propfixed (already probed with no new context)
            if self.propfixed[idx] >= current_fixed {
                return false;
            }
            // Re-verify root property: negated literal has bin_occs, literal does not
            let neg_idx = lit.negated().index();
            if neg_idx >= max_lits {
                return false;
            }
            let self_occs = self.bin_occs[idx];
            let neg_occs = self.bin_occs[neg_idx];
            neg_occs > 0 && self_occs == 0
        });

        // Re-sort by occurrence count (higher first)
        let bin_occs = &self.bin_occs;
        self.probes.sort_by(|a, b| {
            let a_idx = a.negated().index();
            let b_idx = b.negated().index();
            let a_occs = if a_idx < bin_occs.len() {
                bin_occs[a_idx]
            } else {
                0
            };
            let b_occs = if b_idx < bin_occs.len() {
                bin_occs[b_idx]
            } else {
                0
            };
            b_occs.cmp(&a_occs)
        });
    }

    /// Get the next probe candidate, or None if exhausted
    pub(crate) fn next_probe(&mut self) -> Option<Literal> {
        self.probes.pop()
    }

    /// Mark a literal as probed at the current fixed point
    pub(crate) fn mark_probed(&mut self, lit: Literal, current_fixed: i64) {
        let idx = lit.index();
        if idx < self.propfixed.len() {
            self.propfixed[idx] = current_fixed;
        }
    }

    /// Reset all propfixed entries so every literal becomes re-probable.
    /// CaDiCaL probe.cpp:823-824: reset after each probe round because
    /// newly learned clauses may produce fresh propagation chains.
    pub(crate) fn reset_propfixed(&mut self) {
        self.propfixed.fill(-1);
    }

    /// Update statistics after finding a failed literal
    pub(crate) fn record_failed(&mut self) {
        self.stats.failed += 1;
        self.stats.units_derived += 1;
    }

    /// Update statistics after probing a literal
    pub(crate) fn record_probed(&mut self) {
        self.stats.probed += 1;
    }

    /// Update statistics after completing a round
    pub(crate) fn record_round(&mut self) {
        self.stats.rounds += 1;
    }

    /// Update statistics after performing hyper-binary resolution
    pub(crate) fn record_hbr(
        &mut self,
        clause_size: usize,
        is_redundant: bool,
        subsumes_original: bool,
    ) {
        self.stats.hbrs += 1;
        self.stats.hbr_sizes += clause_size as u64;
        if is_redundant {
            self.stats.hbr_redundant += 1;
        }
        if subsumes_original {
            self.stats.hbr_subs += 1;
        }
    }

    /// Update statistics after deleting an HBR-subsumed clause.
    #[cfg(test)]
    pub(crate) fn record_hbr_subsumed_deletion(&mut self) {
        self.stats.hbr_subsumed_deleted += 1;
    }
}
