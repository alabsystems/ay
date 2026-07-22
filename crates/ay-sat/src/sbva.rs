// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structured Bounded Variable Addition (SBVA) preprocessing.
//!
//! SBVA extends standard BVA (already in `factor.rs`) by identifying groups of
//! clauses sharing a large common literal subset and compressing them using
//! fresh extension variables.
//!
//! Given clauses `{S ∪ D_1, S ∪ D_2, ..., S ∪ D_k}` where S is a shared
//! literal subset and D_i are the per-clause "tails", SBVA introduces a fresh
//! variable `x` and rewrites:
//!
//!   - Definition clause: `{x} ∪ S`     (x implies every literal in S)
//!   - Tail clauses:      `{¬x} ∪ D_i`  for each i
//!
//! The original k clauses (total literal count k·|S| + Σ|D_i|) become 1 + k
//! clauses with total literals |S| + 1 + k + Σ|D_i|. Net literal savings:
//! (k-1)·|S| - k - 1. Profitable when k ≥ 3 and |S| ≥ 2.
//!
//! **DRAT proof**: SBVA's rewrite is a valid RAT extension:
//!   1. Add definition clause `{x} ∪ S` — RAT on fresh var `x`
//!   2. Add blocked clause `{¬x, ¬s_1, ¬s_2, ...}` — RAT on `¬x` (proof only)
//!   3. Add tail clauses `{¬x} ∪ D_i` — RUP (derivable from definition + originals)
//!   4. Delete blocked clause from proof
//!   5. Delete original clauses
//!
//! Reference: Manthey, "Structured BVA" (SAT Competition 2023).
//! Reference: CaDiCaL `factor.cpp` for the basic BVA infrastructure.

#[cfg(test)]
#[path = "sbva_tests.rs"]
mod tests;

use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};
use crate::occ_list::OccList;

/// Maximum clause size eligible for SBVA.
/// Larger clauses rarely compress and waste scanning effort.
pub(crate) const SBVA_SIZE_LIMIT: usize = 12;

/// Minimum shared subset size S for SBVA to be profitable.
/// With |S| = 1, SBVA degenerates to standard BVA (handled by factor.rs).
const MIN_SHARED_SIZE: usize = 2;

/// Minimum group size k for SBVA to be profitable.
/// With k = 2, literal savings = |S| - 3, which is tiny.
const MIN_GROUP_SIZE: usize = 3;

/// Maximum number of clauses to inspect per literal in the grouping phase.
/// Prevents quadratic blowup on high-occurrence literals.
const MAX_OCC_SCAN: usize = 500;

/// One SBVA application with full proof structure.
#[derive(Debug, Clone)]
pub(crate) struct SbvaApplication {
    /// The fresh extension variable introduced.
    pub fresh_var: Variable,
    /// The shared literal subset S.
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub shared_subset: Vec<Literal>,
    /// Definition clause: `{x} ∪ S`.
    pub definition_clause: Vec<Literal>,
    /// Blocked clause: `{¬x, ¬s_1, ¬s_2, ...}` (proof only, RAT on ¬x).
    pub blocked_clause: Vec<Literal>,
    /// Tail clauses: `{¬x} ∪ D_i`.
    pub tail_clauses: Vec<Vec<Literal>>,
    /// Original clause indices to delete.
    pub to_delete: Vec<usize>,
}

/// Result of one SBVA pass.
#[derive(Debug, Default)]
pub(crate) struct SbvaResult {
    /// New clauses to add (definition + tail clauses, flattened).
    pub new_clauses: Vec<Vec<Literal>>,
    /// Clause indices to delete.
    pub to_delete: Vec<usize>,
    /// Number of extension variables introduced.
    pub extension_vars_needed: usize,
    /// Number of SBVA groups applied.
    pub groups_applied: usize,
    /// Per-application structured data for proof emission.
    pub applications: Vec<SbvaApplication>,
    /// Whether the candidate schedule was fully processed.
    pub completed: bool,
}

/// Control parameters for an SBVA run.
pub(crate) struct SbvaConfig {
    /// The next variable index for extension variables.
    pub next_var_id: usize,
    /// Effort limit (clause comparisons budget).
    pub effort_limit: u64,
}

/// SBVA engine state.
#[derive(Debug, Clone)]
pub(crate) struct Sbva {
    num_vars: usize,
    /// Per-literal mark flags for subset identification.
    marks: Vec<bool>,
}

impl Sbva {
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            marks: vec![false; num_vars * 2],
        }
    }

    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if num_vars > self.num_vars {
            self.num_vars = num_vars;
            self.marks.resize(num_vars * 2, false);
        }
    }

    #[inline]
    fn mark(&mut self, lit: Literal) {
        let idx = lit.index();
        if idx < self.marks.len() {
            self.marks[idx] = true;
        }
    }

    #[inline]
    fn unmark(&mut self, lit: Literal) {
        let idx = lit.index();
        if idx < self.marks.len() {
            self.marks[idx] = false;
        }
    }

    #[inline]
    fn is_marked(&self, lit: Literal) -> bool {
        let idx = lit.index();
        idx < self.marks.len() && self.marks[idx]
    }

    /// Check if a literal is assigned true.
    #[inline]
    fn lit_satisfied(lit: Literal, vals: &[i8]) -> bool {
        let idx = lit.index();
        idx < vals.len() && vals[idx] > 0
    }

    #[inline]
    fn clause_satisfied(lits: &[Literal], vals: &[i8]) -> bool {
        lits.iter().any(|&lit| Self::lit_satisfied(lit, vals))
    }

    /// Run SBVA on the clause database.
    ///
    /// Finds groups of clauses sharing large common literal subsets and
    /// compresses them using fresh extension variables.
    pub(crate) fn run(
        &mut self,
        clause_db: &ClauseArena,
        occ: &OccList,
        vals: &[i8],
        var_states: &[crate::solver::lifecycle::VarState],
        config: &SbvaConfig,
    ) -> SbvaResult {
        let mut result = SbvaResult {
            completed: true,
            ..SbvaResult::default()
        };
        let mut effort: u64 = 0;
        let mut next_var = config.next_var_id;
        let mut deleted: Vec<bool> = vec![false; clause_db.len()];

        // Build candidate literal schedule sorted by occurrence count (descending).
        // High-occurrence literals yield more clause grouping opportunities.
        let mut candidates: Vec<(Literal, usize)> = Vec::new();
        for var_idx in 0..self.num_vars {
            if var_idx * 2 < vals.len() && vals[var_idx * 2] != 0 {
                continue; // Variable assigned at level 0.
            }
            if var_idx < var_states.len() && var_states[var_idx].is_removed() {
                continue;
            }
            for positive in [true, false] {
                let lit = if positive {
                    Literal::positive(Variable(var_idx as u32))
                } else {
                    Literal::negative(Variable(var_idx as u32))
                };
                let count = occ.count(lit);
                if count >= MIN_GROUP_SIZE {
                    candidates.push((lit, count));
                }
            }
        }
        candidates.sort_by_key(|b| std::cmp::Reverse(b.1));

        for &(pivot_lit, _) in &candidates {
            if effort > config.effort_limit {
                result.completed = false;
                break;
            }

            // Collect eligible clauses containing pivot_lit.
            let pivot_occs = occ.get(pivot_lit);
            let mut eligible: Vec<usize> = Vec::new();
            for &ci in pivot_occs {
                effort += 1;
                if deleted[ci] {
                    continue;
                }
                if clause_db.is_empty_clause(ci) || clause_db.is_learned(ci) {
                    continue;
                }
                if Self::clause_satisfied(clause_db.literals(ci), vals) {
                    continue;
                }
                let len = clause_db.len_of(ci);
                if !(3..=SBVA_SIZE_LIMIT).contains(&len) {
                    continue; // Need at least 3 lits: pivot + >=1 shared + >=1 tail
                }
                eligible.push(ci);
            }
            if eligible.len() < MIN_GROUP_SIZE {
                continue;
            }

            // Cap scan size to prevent quadratic blowup.
            if eligible.len() > MAX_OCC_SCAN {
                eligible.truncate(MAX_OCC_SCAN);
            }

            // Find groups of clauses sharing large common subsets (excluding pivot_lit).
            // Strategy: for each pair of clauses, compute intersection.
            // Use a signature-based grouping: hash the "non-pivot" literal set,
            // then group by hash to find candidates with identical or near-identical sets.
            //
            // Practical approach: compute a "shared subset" by intersecting all clause
            // pairs and greedily growing groups.
            let groups = self.find_sbva_groups(
                clause_db,
                vals,
                pivot_lit,
                &eligible,
                &mut effort,
                config.effort_limit,
            );

            for group in groups {
                if group.clause_indices.len() < MIN_GROUP_SIZE
                    || group.shared.len() < MIN_SHARED_SIZE
                {
                    continue;
                }

                // Verify all clauses in the group are still alive.
                let alive_indices: Vec<usize> = group
                    .clause_indices
                    .iter()
                    .copied()
                    .filter(|&ci| !deleted[ci])
                    .collect();
                if alive_indices.len() < MIN_GROUP_SIZE {
                    continue;
                }

                // Compute literal savings:
                // Original: k clauses with total lits = sum(clause_len)
                // New: 1 def clause (|S|+1) + k tail clauses (|D_i|+1 each)
                // S includes pivot_lit + shared literals.
                let k = alive_indices.len();
                let shared_set_size = group.shared.len() + 1; // +1 for pivot_lit
                                                              // Each tail has clause_len - shared_set_size literals
                let total_original_lits: usize =
                    alive_indices.iter().map(|&ci| clause_db.len_of(ci)).sum();
                let total_tail_lits: usize = alive_indices
                    .iter()
                    .map(|&ci| clause_db.len_of(ci) - shared_set_size)
                    .sum();
                let new_total_lits = (shared_set_size + 1) + (total_tail_lits + k); // def + tails
                if new_total_lits >= total_original_lits {
                    continue; // Not profitable
                }

                // Apply SBVA: create fresh variable and rewrite.
                let fresh_var = Variable(next_var as u32);
                let fresh_pos = Literal::positive(fresh_var);
                let fresh_neg = Literal::negative(fresh_var);
                next_var += 1;
                result.extension_vars_needed += 1;

                // Mark shared subset for fast membership testing.
                for &lit in &group.shared {
                    self.mark(lit);
                }
                self.mark(pivot_lit);

                // Definition clause: {x} ∪ S (where S = {pivot_lit} ∪ shared).
                let mut def_clause = Vec::with_capacity(shared_set_size + 1);
                def_clause.push(fresh_pos);
                def_clause.push(pivot_lit);
                def_clause.extend_from_slice(&group.shared);
                result.new_clauses.push(def_clause.clone());

                // Blocked clause (proof only): {¬x, ¬pivot, ¬s_1, ...}
                let mut blocked = Vec::with_capacity(shared_set_size + 1);
                blocked.push(fresh_neg);
                blocked.push(pivot_lit.negated());
                for &lit in &group.shared {
                    blocked.push(lit.negated());
                }

                // Tail clauses: {¬x} ∪ D_i for each clause.
                let mut tail_clauses = Vec::with_capacity(alive_indices.len());
                let mut app_to_delete = Vec::with_capacity(alive_indices.len());
                for &ci in &alive_indices {
                    let lits = clause_db.literals(ci);
                    let mut tail = Vec::with_capacity(lits.len() - shared_set_size + 1);
                    tail.push(fresh_neg);
                    for &lit in lits {
                        if !self.is_marked(lit) {
                            tail.push(lit);
                        }
                    }
                    // Skip if tail would be empty (means clause = shared set exactly).
                    // A tail of just {¬x} means the original clause had only the shared
                    // literals. This is valid: ¬x is a unit propagation from x → S.
                    result.new_clauses.push(tail.clone());
                    tail_clauses.push(tail);

                    deleted[ci] = true;
                    result.to_delete.push(ci);
                    app_to_delete.push(ci);
                }

                // Unmark shared subset.
                for &lit in &group.shared {
                    self.unmark(lit);
                }
                self.unmark(pivot_lit);

                result.applications.push(SbvaApplication {
                    fresh_var,
                    shared_subset: {
                        let mut s = vec![pivot_lit];
                        s.extend_from_slice(&group.shared);
                        s
                    },
                    definition_clause: def_clause,
                    blocked_clause: blocked,
                    tail_clauses,
                    to_delete: app_to_delete,
                });
                result.groups_applied += 1;
            }
        }

        result
    }

    /// Find groups of clauses sharing large common literal subsets.
    ///
    /// For a set of clauses all containing `pivot_lit`, computes the "rest"
    /// (clause minus pivot_lit) for each clause and finds groups where the
    /// intersection of rest-sets is large.
    ///
    /// Uses a greedy approach: pick a "seed" clause, intersect with all others,
    /// keep those with intersection >= MIN_SHARED_SIZE, then extract the
    /// maximal common subset.
    fn find_sbva_groups(
        &mut self,
        clause_db: &ClauseArena,
        _vals: &[i8],
        pivot_lit: Literal,
        eligible: &[usize],
        effort: &mut u64,
        effort_limit: u64,
    ) -> Vec<SbvaGroup> {
        let mut groups: Vec<SbvaGroup> = Vec::new();
        let mut used = vec![false; eligible.len()];

        // Pre-compute rest sets (clause literals minus pivot_lit).
        let rest_sets: Vec<Vec<Literal>> = eligible
            .iter()
            .map(|&ci| {
                let lits = clause_db.literals(ci);
                let mut rest: Vec<Literal> =
                    lits.iter().filter(|&&l| l != pivot_lit).copied().collect();
                rest.sort_unstable_by_key(|l| l.0);
                rest
            })
            .collect();

        for seed_idx in 0..eligible.len() {
            if used[seed_idx] || *effort > effort_limit {
                continue;
            }

            let seed_rest = &rest_sets[seed_idx];
            if seed_rest.len() < MIN_SHARED_SIZE {
                continue;
            }

            // Mark seed rest literals for intersection.
            for &lit in seed_rest {
                self.mark(lit);
            }

            // Find all clauses whose rest-set intersects with seed by >= MIN_SHARED_SIZE.
            let mut group_members: Vec<usize> = vec![seed_idx];
            let mut intersection: Vec<Literal> = seed_rest.clone();

            for other_idx in (seed_idx + 1)..eligible.len() {
                *effort += 1;
                if used[other_idx] || *effort > effort_limit {
                    continue;
                }

                let other_rest = &rest_sets[other_idx];
                // Quick check: if other_rest is much smaller than current intersection,
                // the intersection can only shrink.
                if other_rest.len() < MIN_SHARED_SIZE {
                    continue;
                }

                // Compute intersection of current group intersection with other_rest.
                let new_intersection: Vec<Literal> = intersection
                    .iter()
                    .filter(|&&lit| {
                        // Check if lit is in other_rest (sorted, use binary search).
                        other_rest.binary_search_by_key(&lit.0, |l| l.0).is_ok()
                    })
                    .copied()
                    .collect();

                if new_intersection.len() >= MIN_SHARED_SIZE {
                    intersection = new_intersection;
                    group_members.push(other_idx);
                }
            }

            // Unmark seed rest literals.
            for &lit in seed_rest {
                self.unmark(lit);
            }

            if group_members.len() >= MIN_GROUP_SIZE && intersection.len() >= MIN_SHARED_SIZE {
                // Mark all members as used to avoid overlapping groups.
                for &member_idx in &group_members {
                    used[member_idx] = true;
                }

                groups.push(SbvaGroup {
                    clause_indices: group_members.iter().map(|&i| eligible[i]).collect(),
                    shared: intersection,
                });
            }
        }

        groups
    }
}

/// A group of clauses identified for SBVA compression.
#[derive(Debug)]
struct SbvaGroup {
    /// Clause indices in the group.
    clause_indices: Vec<usize>,
    /// The shared literal subset (excluding the pivot literal).
    shared: Vec<Literal>,
}
