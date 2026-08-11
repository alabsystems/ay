// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hyper-Ternary Resolution (HTR)
//!
//! Implements hyper-ternary resolution as an inprocessing technique.
//! This technique resolves pairs of ternary (3-literal) clauses to produce
//! new binary or ternary resolvents.
//!
//! The key insight is that resolving two ternary clauses can produce:
//! - A binary clause (2 literals) - highly valuable, can delete both antecedents
//! - A ternary clause (3 literals) - useful for further propagation
//! - A quaternary clause (4 literals) - discarded (not beneficial)
//! - A tautology - discarded
//!
//! Binary resolvents are particularly valuable because they:
//! 1. Strengthen unit propagation
//! 2. Subsume both antecedent clauses (which can be deleted)
//!
//! Reference: Heule, Järvisalo, Lonsing, "Clause Elimination for SAT and QSAT",
//! Journal of Artificial Intelligence Research, 2015.
//! Also: Biere, "Lingeling and Friends at the SAT Competition 2011".

mod resolve;
#[cfg(test)]
mod tests;
#[cfg(kani)]
mod verification;

use crate::clause_arena::ClauseArena;
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};

use crate::kani_compat::DetHashSet;

/// Maximum number of occurrences for a literal to be considered
/// (to avoid combinatorial explosion)
const MAX_OCCURRENCES: usize = 100;
/// Maximum HTR rounds per invocation (CaDiCaL default `ternaryrounds = 2`).
const MAX_HTR_ROUNDS: usize = 2;

/// Statistics for HTR operations

#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct HTRStats {
    /// Number of hyper-ternary resolution rounds
    pub rounds: u64,
    /// Number of ternary resolvents added
    pub ternary_resolvents: u64,
    /// Number of binary resolvents added
    pub binary_resolvents: u64,
    /// Number of clause pairs checked
    pub pairs_checked: u64,
    /// Number of tautological resolvents skipped
    pub tautologies_skipped: u64,
    /// Number of duplicate resolvents skipped
    pub duplicates_skipped: u64,
    /// Number of quaternary (or larger) resolvents skipped
    pub too_large_skipped: u64,
}

/// Result of a single hyper-ternary resolution

#[derive(Debug, Clone)]
pub(crate) struct HTRResult {
    /// New resolvents to add: (literals, antecedent1_idx, antecedent2_idx).
    /// Antecedent indices < `derived_base` are clause DB indices.
    /// Antecedent indices >= `derived_base` are virtual derived ternary clauses
    /// from earlier HTR rounds (index = derived_base + position in derived order).
    pub resolvents: Vec<(Vec<Literal>, usize, usize)>,
    /// Clause indices to delete (antecedents subsumed by binary resolvents)
    pub to_delete: Vec<usize>,
    /// Clause DB length at HTR start. Indices below this are real clauses;
    /// indices at or above are virtual derived ternary resolvents.
    pub derived_base: usize,
}

/// Occurrence list for HTR — reuses shared `OccList` (same as BCE/BVE).
pub(crate) type HTROccList = crate::occ_list::OccList;

/// Hyper-Ternary Resolution engine
#[allow(clippy::upper_case_acronyms)] // -D warnings overrides crate-level #![allow]
pub(crate) struct HTR {
    /// Occurrence lists
    occ: HTROccList,
    /// Statistics
    stats: HTRStats,
    /// Number of variables
    num_vars: usize,
    /// Set of existing binary clauses (for duplicate detection)
    /// Stored as (min_lit_idx, max_lit_idx) pairs
    existing_binary: DetHashSet<(u32, u32)>,
    /// Set of existing ternary clauses (for duplicate detection)
    /// Stored as sorted (lit1, lit2, lit3) triples
    existing_ternary: DetHashSet<(u32, u32, u32)>,
    /// Reusable buffer for positive occurrence indices (avoids per-call allocations)
    pos_occ_buf: Vec<usize>,
    /// Reusable buffer for negative occurrence indices (avoids per-call allocations)
    neg_occ_buf: Vec<usize>,
    /// Ternary resolvents derived in earlier rounds of current `run()`.
    derived_ternary: Vec<[Literal; 3]>,
    /// Virtual clause indices begin at `clause_db.len()`.
    derived_base: usize,
    /// Search ticks at the last completed HTR call.
    last_search_ticks: Option<u64>,
}

impl HTR {
    /// Create a new HTR engine for n variables
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            // Sized on first use by the HTR entry point, which calls
            // `ensure_num_vars` before rebuilding. `OccList::new(n)` commits
            // 128 resident bytes per variable at solver construction whether or
            // not HTR ever runs.
            occ: HTROccList::new(0),
            stats: HTRStats::default(),
            num_vars,
            existing_binary: DetHashSet::default(),
            existing_ternary: DetHashSet::default(),
            pos_occ_buf: Vec::new(),
            neg_occ_buf: Vec::new(),
            derived_ternary: Vec::new(),
            derived_base: 0,
            last_search_ticks: None,
        }
    }

    /// Ensure internal buffers can handle `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.num_vars >= num_vars {
            return;
        }
        self.num_vars = num_vars;
        self.occ.ensure_num_vars(num_vars);
    }

    /// Get statistics
    pub(crate) fn stats(&self) -> &HTRStats {
        &self.stats
    }

    /// Restore previously saved statistics (e.g., after compaction recreates
    /// the engine via `HTR::new()`). Without this, stats are zeroed.
    pub(crate) fn restore_stats(&mut self, stats: HTRStats) {
        self.stats = stats;
    }

    /// Search ticks at the last completed HTR call, if any.
    pub(crate) fn last_search_ticks(&self) -> Option<u64> {
        self.last_search_ticks
    }

    /// Update the last completed HTR search-tick watermark.
    pub(crate) fn set_last_search_ticks(&mut self, ticks: u64) {
        self.last_search_ticks = Some(ticks);
    }

    /// Reset the HTR search-tick watermark to its initial state (`None`).
    ///
    /// `None` means "first call" which uses the INIT budget rather than a
    /// tick-proportional delta. Called by `InprocessingEngines::reset_watermarks()`
    /// when `search_ticks` is reset between incremental solves (#8159).
    pub(crate) fn reset_last_search_ticks(&mut self) {
        self.last_search_ticks = None;
    }

    /// Normalize a binary clause to a canonical form for hashing
    fn normalize_binary(a: Literal, b: Literal) -> (u32, u32) {
        let a_raw = a.0;
        let b_raw = b.0;
        if a_raw <= b_raw {
            (a_raw, b_raw)
        } else {
            (b_raw, a_raw)
        }
    }

    /// Normalize a ternary clause to a canonical form for hashing
    fn normalize_ternary(a: Literal, b: Literal, c: Literal) -> (u32, u32, u32) {
        let mut lits = [a.0, b.0, c.0];
        lits.sort_unstable();
        lits.into()
    }

    /// Initialize/rebuild occurrence lists and existing clause sets
    pub(crate) fn rebuild(&mut self, clauses: &ClauseArena) {
        self.occ.clear();
        self.existing_binary.clear();
        self.existing_ternary.clear();

        for idx in clauses.indices() {
            if clauses.is_empty_clause(idx) {
                continue;
            }

            let len = clauses.len_of(idx);
            let lits = clauses.literals(idx);

            // Only track binary and ternary clauses
            if len == 2 {
                let key = Self::normalize_binary(lits[0], lits[1]);
                self.existing_binary.insert(key);
                self.occ.add_clause(idx, lits);
            } else if len == 3 {
                let key = Self::normalize_ternary(lits[0], lits[1], lits[2]);
                self.existing_ternary.insert(key);
                self.occ.add_clause(idx, lits);
            }
        }

        // Add virtual ternary clauses derived in previous rounds.
        for (i, lits) in self.derived_ternary.iter().enumerate() {
            let virtual_idx = self.derived_base + i;
            let key = Self::normalize_ternary(lits[0], lits[1], lits[2]);
            self.existing_ternary.insert(key);
            self.occ.add_clause(virtual_idx, lits);
        }
    }

    /// Check if a binary clause already exists (or is subsumed)
    fn binary_exists(&self, a: Literal, b: Literal) -> bool {
        let key = Self::normalize_binary(a, b);
        self.existing_binary.contains(&key)
    }

    /// Check if a ternary clause already exists (or is subsumed by a binary)
    fn ternary_exists(&self, a: Literal, b: Literal, c: Literal) -> bool {
        // Check if subsumed by any binary clause
        if self.binary_exists(a, b) || self.binary_exists(a, c) || self.binary_exists(b, c) {
            return true;
        }

        // Check if exact ternary exists
        let key = Self::normalize_ternary(a, b, c);
        self.existing_ternary.contains(&key)
    }

    /// Run hyper-ternary resolution as inprocessing
    ///
    /// Runs up to `MAX_HTR_ROUNDS` rounds. Ternary resolvents from round N are
    /// fed into round N+1 as virtual antecedent clauses (CaDiCaL inter-round
    /// feedback pattern from `ternary.cpp`).
    ///
    /// Returns an HTRResult with new resolvents and clauses to delete.
    #[cfg(test)]
    pub(crate) fn run(
        &mut self,
        clauses: &ClauseArena,
        vals: &[i8],
        max_resolvents: usize,
    ) -> HTRResult {
        let mut marks = LitMarks::new(self.num_vars);
        self.run_with_marks(clauses, vals, max_resolvents, &mut marks)
    }

    pub(crate) fn run_with_marks(
        &mut self,
        clauses: &ClauseArena,
        vals: &[i8],
        max_resolvents: usize,
        marks: &mut LitMarks,
    ) -> HTRResult {
        self.derived_ternary.clear();
        self.derived_base = clauses.len();

        let mut all_resolvents: Vec<(Vec<Literal>, usize, usize)> = Vec::new();
        let mut to_delete = Vec::new();
        let mut deleted_set: DetHashSet<usize> = DetHashSet::default();
        let derived_base = self.derived_base;

        for _ in 0..MAX_HTR_ROUNDS {
            self.stats.rounds += 1;
            self.rebuild(clauses);

            // Keep duplicate detection aware of previously emitted resolvents.
            for (resolvent, _, _) in &all_resolvents {
                match resolvent.len() {
                    2 => {
                        self.existing_binary
                            .insert(Self::normalize_binary(resolvent[0], resolvent[1]));
                    }
                    3 => {
                        self.existing_ternary.insert(Self::normalize_ternary(
                            resolvent[0],
                            resolvent[1],
                            resolvent[2],
                        ));
                    }
                    _ => {}
                }
            }

            let round_start = all_resolvents.len();
            let mut round_ternary = 0usize;

            // Iterate over all variables
            for var_idx in 0..self.num_vars {
                if all_resolvents.len() >= max_resolvents {
                    break;
                }

                let var = Variable(var_idx as u32);

                // Skip if variable is assigned
                if var_idx * 2 < vals.len() && vals[var_idx * 2] != 0 {
                    continue;
                }

                // Check occurrence counts to avoid expensive operations
                let pos_lit = Literal::positive(var);
                let neg_lit = Literal::negative(var);
                let pos_count = self.occ.count(pos_lit);
                let neg_count = self.occ.count(neg_lit);

                if pos_count == 0 || neg_count == 0 {
                    continue;
                }
                if pos_count > MAX_OCCURRENCES || neg_count > MAX_OCCURRENCES {
                    continue;
                }

                // Run resolution on this pivot
                let resolvents = self.resolve_on_pivot_with_marks(var, clauses, vals, marks);

                // Collect resolvents (with antecedent indices for LRAT hints).
                //
                // Antecedent deletion is registered HERE, only for binary
                // resolvents that are actually RETAINED (constraint-loss fix):
                // a binary resolvent subsumes both of its ternary antecedents,
                // so deleting them is sound only when the binary really enters
                // the clause DB. The previous separate antecedent loop deleted
                // both antecedents of every binary-producing pair even when
                // the resolvent itself was dropped by the `max_resolvents`
                // cap, silently weakening the formula. Observed as
                // FINALIZE_SAT_FAIL (model violates the dropped binary) on
                // SAT-COMP main2025 e318e2ac/90bec6dc/e4ac15cf, all XOR-heavy
                // instances whose ternary density blows the resolvent budget.
                for entry in resolvents {
                    if all_resolvents.len() >= max_resolvents {
                        break;
                    }
                    if entry.0.len() == 3 {
                        round_ternary += 1;
                    } else if entry.0.len() == 2 {
                        // Only real clause indices, not virtual derived ones.
                        let (c_idx, d_idx) = (entry.1, entry.2);
                        if c_idx < self.derived_base && deleted_set.insert(c_idx) {
                            to_delete.push(c_idx);
                        }
                        if d_idx < self.derived_base && deleted_set.insert(d_idx) {
                            to_delete.push(d_idx);
                        }
                    }
                    all_resolvents.push(entry);
                }
            }

            if round_ternary == 0 || all_resolvents.len() >= max_resolvents {
                break;
            }

            // Add this round's ternary resolvents as virtual antecedents for next round.
            for (resolvent, _, _) in &all_resolvents[round_start..] {
                if resolvent.len() == 3 {
                    self.derived_ternary
                        .push([resolvent[0], resolvent[1], resolvent[2]]);
                }
            }
        }

        self.derived_ternary.clear();

        HTRResult {
            resolvents: all_resolvents,
            to_delete,
            derived_base,
        }
    }
}
