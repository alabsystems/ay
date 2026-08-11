// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Asymmetric Covered Clause Elimination (ACCE)
//!
//! A clause C is covered-tautological if, after extending it with covered
//! literal addition (CLA), the extended clause is blocked on some literal.
//! CLA computes the intersection of unassigned resolution candidate literals
//! across all clauses containing ~L for some literal L in the extended clause.
//! If the intersection is non-empty, those literals are added to the clause
//! and the process repeats. If all resolution candidates for L are satisfied
//! (blocked), the clause is blocked on L and can be eliminated.
//!
//! ACCE extends CCE with Asymmetric Literal Addition (ALA): for each literal
//! set false, propagate through ALL watched clauses (binary and long). This
//! finds more elimination opportunities than binary-only ALA. CaDiCaL calls
//! this "CCE" but the implementation is actually ACCE (cover.cpp comment).
//!
//! CCE strictly subsumes BCE: every blocked clause is also covered-tautological.
//!
//! Reference: Heule, Järvisalo, Biere, "Covered Clause Elimination", LPAR 2010.
//! Implementation: CaDiCaL `cover.cpp` (704 lines).

use crate::clause_arena::ClauseArena;
use crate::literal::Literal;
use crate::occ_list::OccList;
use crate::watched::WatchedLists;

mod cover;
#[cfg(test)]
mod tests;

/// Maximum clause size for CCE candidates.
/// CaDiCaL: `covermaxclslim = 100000` (options.hpp).
const MAX_CLAUSE_SIZE: usize = 100_000;

/// Statistics for CCE operations.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct CCEStats {
    /// Clauses eliminated by covered blocking (CLA found blocking literal).
    pub blocked: u64,
    /// Total CLA steps (intersection computations).
    pub cla_steps: u64,
    /// Rounds executed.
    pub rounds: u64,
    /// Propagation-equivalent checks (effort tracking).
    pub checks: u64,
}

/// Result of a successful covered clause elimination.
#[derive(Debug, Clone)]
pub(crate) struct CoveredElimination {
    /// Index of the eliminated clause in the clause arena.
    pub clause_idx: usize,
    /// The blocking literal (witness for model reconstruction).
    pub blocking_literal: Literal,
    /// The full covered set (original clause + CLA-added literals).
    /// Used for reconstruction: the blocking literal may be a CLA-added
    /// literal not present in the original clause, so we must save the
    /// covered set for correct model restoration.
    /// CaDiCaL: `cover_push_extension` saves `coveror.covered`.
    pub covered_lits: Vec<Literal>,
}

/// Covered Clause Elimination engine.
///
/// Operates on occurrence lists. Requires all irredundant, non-garbage clauses
/// to be connected before calling `run_round()`.
pub(crate) struct Cce {
    /// Occurrence lists (rebuilt each round from the clause arena).
    occ: OccList,
    /// Combined trail: all literals set false during CCE processing of one clause.
    /// Indexed by variable; stores -1 (false) or 0 (unassigned).
    local_vals: Vec<i8>,
    /// Original clause literals + CLA-added literals.
    covered: Vec<Literal>,
    /// Intersection buffer for CLA computation.
    intersection: Vec<Literal>,
    /// Marks for intersection computation (per-variable: 0 = unmarked, sign = marked).
    cla_marks: Vec<i8>,
    /// Reusable buffer: tracks assigned literals for cleanup in `cover_clause`.
    added_trail: Vec<Literal>,
    /// Reusable buffer: copy of occurrence list indices for borrow-safe iteration.
    occ_cache: Vec<usize>,
    /// Statistics.
    stats: CCEStats,
    /// Effort counter (incremented during clause scanning).
    effort: u64,
}

impl Cce {
    /// Create a new CCE engine for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            // Sized on demand, not here. `OccList::new(n)` commits
            // `vec![Vec::new(); 2n]` plus a per-literal `PosMap` — 128 resident
            // bytes per variable — and CCE's entry point
            // (`solver/inprocessing/cce.rs`) already calls `ensure_num_vars`
            // immediately before `rebuild`, so nothing reads the list until it
            // has been grown. Measured: this is 863 MB on a 6.7 M-variable
            // SAT-COMP 2026 instance, committed before a clause is read on
            // every instance whether or not CCE ever runs.
            occ: OccList::new(0),
            local_vals: vec![0i8; num_vars * 2],
            covered: Vec::new(),
            intersection: Vec::new(),
            cla_marks: vec![0i8; num_vars],
            added_trail: Vec::new(),
            occ_cache: Vec::new(),
            stats: CCEStats::default(),
            effort: 0,
        }
    }

    /// Ensure internal buffers can handle `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        self.occ.ensure_num_vars(num_vars);
        let target_lits = num_vars * 2;
        if self.local_vals.len() < target_lits {
            self.local_vals.resize(target_lits, 0);
        }
        if self.cla_marks.len() < num_vars {
            self.cla_marks.resize(num_vars, 0);
        }
    }

    pub(crate) fn stats(&self) -> &CCEStats {
        &self.stats
    }

    /// Rebuild occurrence lists from the clause arena.
    /// Only includes irredundant, non-empty clauses.
    pub(crate) fn rebuild(&mut self, arena: &ClauseArena) {
        self.occ.clear();
        for idx in arena.indices() {
            if arena.is_empty_clause(idx) || arena.is_learned(idx) {
                continue;
            }
            self.occ.add_clause(idx, arena.literals(idx));
        }
    }

    /// Check if a literal is assigned false in local CCE assignments.
    #[inline]
    fn is_false(&self, lit: Literal) -> bool {
        let li = lit.index();
        li < self.local_vals.len() && self.local_vals[li] < 0
    }

    /// Check if a literal is assigned true in local CCE assignments.
    #[inline]
    fn is_true(&self, lit: Literal) -> bool {
        self.is_false(lit.negated())
    }

    /// Assign a literal false in local CCE vals.
    #[inline]
    fn set_false(&mut self, lit: Literal) {
        let li = lit.index();
        if li < self.local_vals.len() {
            self.local_vals[li] = -1;
        }
        let ni = lit.negated().index();
        if ni < self.local_vals.len() {
            self.local_vals[ni] = 1;
        }
    }

    /// Unassign a literal (reset both polarities to 0).
    #[inline]
    fn unset(&mut self, lit: Literal) {
        let li = lit.index();
        if li < self.local_vals.len() {
            self.local_vals[li] = 0;
        }
        let ni = lit.negated().index();
        if ni < self.local_vals.len() {
            self.local_vals[ni] = 0;
        }
    }

    /// Run one round of Covered Clause Elimination.
    ///
    /// `arena`: clause database.
    /// `vals`: solver level-0 assignments (indexed by literal index).
    /// `freeze_counts`: per-variable freeze counts.
    /// `effort_limit`: maximum effort (clause scans) before stopping.
    ///
    /// Returns eliminated clauses with their blocking literals.
    pub(crate) fn run_round(
        &mut self,
        arena: &ClauseArena,
        vals: &[i8],
        freeze_counts: &[u32],
        watches: &WatchedLists,
        effort_limit: u64,
    ) -> Vec<CoveredElimination> {
        self.stats.rounds += 1;
        self.effort = 0;
        let mut eliminated = Vec::new();

        // Sort occurrence lists by clause size ascending so CLA intersects
        // smaller clauses first. Smaller clauses have fewer literals, making
        // intersection empty sooner (-> move-to-front + early break).
        // CaDiCaL cover.cpp:600-608.
        self.occ.sort_each_by_key(|clause_idx| {
            if clause_idx < arena.len() {
                arena.len_of(clause_idx)
            } else {
                usize::MAX
            }
        });

        // Schedule: collect all irredundant, non-empty clauses within size limit.
        let mut schedule: Vec<(usize, usize)> = Vec::new(); // (size, clause_idx)
        for idx in arena.indices() {
            if arena.is_empty_clause(idx) || arena.is_learned(idx) {
                continue;
            }
            let lits = arena.literals(idx);
            if lits.len() > MAX_CLAUSE_SIZE || lits.len() < 2 {
                continue;
            }

            // Skip clauses with all-frozen literals.
            let all_frozen = lits.iter().all(|&l| {
                let vi = l.variable().index();
                vi < freeze_counts.len() && freeze_counts[vi] > 0
            });
            if all_frozen {
                continue;
            }

            // Skip satisfied clauses.
            let satisfied = lits.iter().any(|&l| {
                let li = l.index();
                li < vals.len() && vals[li] > 0
            });
            if satisfied {
                continue;
            }

            schedule.push((lits.len(), idx));
        }

        // Sort by size descending (larger clauses first — they're more likely
        // to be covered-tautological). CaDiCaL cover.cpp:589-590 processes
        // from the back after sorting smaller-first.
        schedule.sort_unstable_by_key(|b| std::cmp::Reverse(b.0));

        // Process clauses.
        for &(_, clause_idx) in &schedule {
            if self.effort >= effort_limit {
                break;
            }

            // Re-check: clause may have been subsumed by earlier elimination
            // in the same round (via occurrence list updates).
            if arena.is_empty_clause(clause_idx) {
                continue;
            }

            if let Some((blocking_lit, covered_lits)) =
                self.cover_clause(clause_idx, arena, vals, freeze_counts, watches)
            {
                eliminated.push(CoveredElimination {
                    clause_idx,
                    blocking_literal: blocking_lit,
                    covered_lits,
                });
                self.stats.blocked += 1;
            }
        }

        self.stats.checks += self.effort;
        eliminated
    }
}
