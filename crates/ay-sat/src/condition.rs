// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Globally Blocked Clause Elimination (GBCE / "Conditioning").
//!
//! A clause C is globally blocked if there exists a total assignment
//! partitioned into a "conditional" part (literals whose negations touch
//! unsatisfied clauses) and an "autarky" part (the rest) such that at
//! least one autarky literal appears positively in C.
//!
//! Conditioning can remove ~49% of clauses on structured BMC formulas.
//!
//! Reference: CaDiCaL `condition.cpp`; PhD thesis of Benjamin Kiesl (2019);
//! Kiesl, Heule, Biere – ATVA 2019.
//!
//! ## Implementation
//!
//! Implements CaDiCaL's per-candidate refinement (condition.cpp:565-705).
//! For each candidate clause, the initial conditional/autarky partition is
//! refined: conditional literals not appearing negated in the candidate are
//! "unassigned", and when a watched clause loses all true literals, its
//! false autarky literals are promoted to conditional. A candidate is
//! globally blocked if an autarky literal survives after refinement.
//!
//! For model reconstruction, the full autarky witness set (all autarky
//! literals) is stored with each eliminated clause, matching CaDiCaL's
//! `condition.cpp:787-790` approach. Reconstruction flips all autarky
//! witnesses as a group to preserve the global invariant.

#[cfg(test)]
mod tests;

use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};

/// Statistics for conditioning operations.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct ConditioningStats {
    /// Number of globally blocked clauses eliminated
    pub clauses_eliminated: u64,
    /// Number of candidate clauses checked
    pub candidates_checked: u64,
    /// Number of conditioning rounds
    pub rounds: u64,
}

/// Result of a conditioning pass: clause indices to eliminate, with witnesses.
#[derive(Debug, Clone)]
pub(crate) struct ConditionedClause {
    /// Index of the eliminated clause in the clause database
    pub clause_idx: usize,
    /// The full autarky witness set for model reconstruction. During
    /// reconstruction, if the removed clause is not satisfied, all witness
    /// literals that are currently false are flipped to true. CaDiCaL
    /// `condition.cpp:787-790` stores all autarky literals as the witness.
    pub witnesses: Vec<Literal>,
}

/// Result of a conditioning round: both globally blocked clauses and
/// root-satisfied clauses that should be garbage-collected.
#[derive(Debug, Clone, Default)]
pub(crate) struct ConditionResult {
    /// Globally blocked clauses to eliminate (with reconstruction witnesses).
    pub eliminated: Vec<ConditionedClause>,
    /// Clause indices that are root-level satisfied and should be deleted.
    /// CaDiCaL `condition.cpp:321-322`: `mark_garbage(c)` for root-satisfied clauses.
    /// Root-level assignments are permanent in CDCL, so these clauses can
    /// never become unsatisfied. Failing to delete them causes unsound
    /// reconstruction: autarky witness flipping can break clauses that were
    /// only satisfied by root-assigned variables (#5052).
    pub root_satisfied: Vec<usize>,
}

/// Conditioning engine for Globally Blocked Clause Elimination.
///
/// Computes an initial conditional/autarky partition from the total assignment
/// and clause database, then eliminates candidate clauses that contain at
/// least one autarky literal.
pub(crate) struct Conditioning {
    /// Per-variable marks. Bit 0 = conditional (1) vs autarky (0).
    marks: Vec<u8>,

    /// Per-literal candidate membership. Indexed by literal index.
    /// CaDiCaL condition.cpp:126-141 uses mark67 (polarity-aware marks)
    /// so `is_in_candidate_clause(-lit)` returns false when `lit` (not `-lit`)
    /// was marked. AY previously used a per-variable CANDIDATE_BIT which
    /// conflated `lit` and `~lit`, causing unsound GBCE eliminations.
    candidate_lits: Vec<bool>,

    /// Stack of conditional literals (for tracking).
    conditional: Vec<Literal>,

    /// Reusable occurrence list buffer (avoids per-round allocation).
    occs: Vec<Vec<usize>>,

    /// Reusable candidate clause index buffer.
    candidates: Vec<usize>,

    /// Reusable unassigned literal buffer (per-candidate refinement).
    unassigned: Vec<Literal>,

    /// Statistics
    stats: ConditioningStats,
}

const CONDITIONAL_BIT: u8 = 0x01;
const UNASSIGNED_BIT: u8 = 0x04;

/// Minimum propagation steps per conditioning round.
/// CaDiCaL condition.cpp:912: `conditionmineff`.
const CONDITION_MIN_EFFORT: usize = 1_000;

/// Maximum propagation steps per conditioning round.
/// CaDiCaL condition.cpp:914: `conditionmaxeff`.
const CONDITION_MAX_EFFORT: usize = 10_000_000;

impl Conditioning {
    /// Compute the dynamic propagation limit for conditioning.
    ///
    /// CaDiCaL condition.cpp:908-920.
    pub(crate) fn compute_prop_limit(
        search_propagations: u64,
        active_vars: usize,
        irredundant_clauses: usize,
    ) -> usize {
        let base = (search_propagations / 10) as usize;
        let clamped = base.clamp(CONDITION_MIN_EFFORT, CONDITION_MAX_EFFORT);
        if irredundant_clauses > 0 && active_vars > 0 {
            let scaled = (clamped as u128 * 2 * active_vars as u128) / irredundant_clauses as u128;
            (scaled as usize)
                .max(2 * active_vars)
                .min(CONDITION_MAX_EFFORT)
        } else {
            clamped
        }
    }

    /// CaDiCaL condition.cpp:59-61: skip if irredundant/active > 100.
    pub(crate) fn should_skip_ratio(irredundant_clauses: usize, active_vars: usize) -> bool {
        if active_vars == 0 {
            return true;
        }
        irredundant_clauses / active_vars > 100
    }

    /// Create a new conditioning engine.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            marks: vec![0; num_vars],
            candidate_lits: vec![false; num_vars * 2],
            conditional: Vec::new(),
            occs: Vec::new(),
            candidates: Vec::new(),
            unassigned: Vec::new(),
            stats: ConditioningStats::default(),
        }
    }

    /// Access conditioning statistics.
    pub(crate) fn stats(&self) -> &ConditioningStats {
        &self.stats
    }

    /// Restore previously saved statistics after compaction recreates the engine.
    pub(crate) fn restore_stats(&mut self, stats: ConditioningStats) {
        self.stats = stats;
    }

    /// Ensure buffers can handle `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.marks.len() < num_vars {
            self.marks.resize(num_vars, 0);
        }
        let num_lits = num_vars * 2;
        if self.candidate_lits.len() < num_lits {
            self.candidate_lits.resize(num_lits, false);
        }
    }

    /// Run a conditioning round.
    ///
    /// # Arguments
    /// * `clauses` - The clause database
    /// * `vals` - Value array indexed by literal index: 1=true, -1=false, 0=unassigned.
    ///   Root-level (level 0) assigned literals should have value 0 (unassigned)
    ///   to match CaDiCaL's `condition_unassign` pattern (condition.cpp:425-436).
    /// * `root_vals` - Value array WITH root-level assignments, used to detect
    ///   and skip root-level satisfied clauses (CaDiCaL condition.cpp:304-324).
    /// * `frozen` - Frozen variable counts (variables with count > 0 are frozen)
    /// * `reason_clause_marks` - Clause-indexed reason markers (epoch-stamped)
    /// * `reason_clause_epoch` - Active epoch in `reason_clause_marks`
    /// * `max_eliminations` - Maximum number of clauses to eliminate
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn condition_round(
        &mut self,
        clauses: &mut ClauseArena,
        vals: &[i8],
        root_vals: &[i8],
        frozen: &[u32],
        reason_clause_marks: &[u32],
        reason_clause_epoch: u32,
        max_eliminations: usize,
        prop_limit: usize,
    ) -> ConditionResult {
        // CaDiCaL condition.cpp: vals must have entries for all literals
        debug_assert!(
            !vals.is_empty(),
            "BUG: condition_round called with empty vals array",
        );
        // Marks must be consistent with num_vars
        debug_assert!(
            self.marks.len() * 2 <= vals.len() + 2,
            "BUG: condition marks array (len={}) inconsistent with vals (len={})",
            self.marks.len(),
            vals.len(),
        );
        self.stats.rounds += 1;
        let mut eliminated = Vec::new();
        let mut root_satisfied_indices = Vec::new();

        // Clear state from previous round.
        for m in self.marks.iter_mut() {
            *m = 0;
        }
        for c in self.candidate_lits.iter_mut() {
            *c = false;
        }
        self.conditional.clear();

        // Phase 1: Classify all irredundant clauses.
        // Build the initial conditional/autarky partition AND occurrence lists.
        // CaDiCaL condition.cpp:287-396.
        //
        // A literal is "conditional" if its negation appears in an
        // all-negative (unsatisfied-under-the-total-assignment) clause.
        // All other assigned literals are "autarky".
        self.candidates.clear();
        // Occurrence lists: for each literal index, the clause indices watched
        // by that literal. CaDiCaL condition.cpp:351-362.
        let num_lits = vals.len();
        if self.occs.len() < num_lits {
            self.occs.resize_with(num_lits, Vec::new);
        }
        for v in self.occs[..num_lits].iter_mut() {
            v.clear();
        }

        for idx in clauses.indices() {
            let off_header = idx;
            if clauses.is_empty_clause(off_header) || clauses.is_learned(off_header) {
                continue;
            }

            let lits = clauses.literals(idx);

            // CaDiCaL condition.cpp:304-324: garbage-collect root-level satisfied
            // clauses. Root-level (level 0) assignments are permanent in CDCL,
            // so these clauses can never become unsatisfied. CaDiCaL deletes
            // them with `mark_garbage(c)`. Merely skipping them (without
            // deletion) causes unsound reconstruction: autarky witness flipping
            // can break clauses that remain in clause_db but were only satisfied
            // by root-assigned variables whose model value may differ from the
            // phase-based total_vals used during conditioning (#5052).
            let is_root_satisfied = lits.iter().any(|&lit| {
                let li = lit.index();
                li < root_vals.len() && root_vals[li] > 0 && (li >= vals.len() || vals[li] == 0)
            });
            if is_root_satisfied {
                // CaDiCaL condition.cpp:321-322: mark_garbage(c).
                root_satisfied_indices.push(idx);
                continue;
            }

            let mut has_positive = false;
            let mut has_negative = false;
            let mut best_watch = None;
            let mut best_occ_count = usize::MAX;

            for &lit in lits {
                let li = lit.index();
                let val = if li < vals.len() { vals[li] } else { 0 };
                if val > 0 {
                    has_positive = true;
                    // Pick the positive literal with fewest occurrences.
                    // CaDiCaL condition.cpp:315-318.
                    let count = if li < self.occs.len() {
                        self.occs[li].len()
                    } else {
                        0
                    };
                    if count < best_occ_count {
                        best_occ_count = count;
                        best_watch = Some(lit);
                    }
                } else if val < 0 {
                    has_negative = true;
                }
            }

            if has_positive {
                self.candidates.push(idx);
            }

            // Watch one positive literal in mixed clauses for refinement.
            // CaDiCaL condition.cpp:351-362.
            if has_positive && has_negative {
                if let Some(w) = best_watch {
                    let wi = w.index();
                    if wi < self.occs.len() {
                        self.occs[wi].push(idx);
                    }
                }
            }

            if !has_positive && has_negative {
                // All-negative clause: mark negations of false literals as
                // conditional. CaDiCaL condition.cpp:369-394.
                for &lit in lits {
                    let neg = lit.negated();
                    let nli = neg.index();
                    let var = neg.variable().index();
                    if nli < vals.len()
                        && vals[nli] > 0
                        && var < self.marks.len()
                        && (self.marks[var] & CONDITIONAL_BIT) == 0
                    {
                        self.marks[var] |= CONDITIONAL_BIT;
                        self.conditional.push(neg);
                    }
                }
            }
        }

        let initial_conditional_len = self.conditional.len();

        // Round-robin scheduling (CaDiCaL condition.cpp:443-468).
        let mut num_conditioned: usize = 0;
        let mut num_unconditioned: usize = 0;
        for &idx in &self.candidates {
            if clauses.is_conditioned(idx) {
                num_conditioned += 1;
            } else {
                num_unconditioned += 1;
            }
        }
        if num_conditioned > 0 && num_unconditioned > 0 {
            self.candidates
                .sort_unstable_by_key(|&idx| clauses.is_conditioned(idx));
        } else if num_conditioned > 0 && num_unconditioned == 0 {
            for &idx in &self.candidates {
                clauses.set_conditioned(idx, false);
            }
        }

        // Phase 2: Per-candidate refinement (CaDiCaL condition.cpp:484-834).
        // For each candidate, refine the partition and check if an autarky
        // literal survives in the candidate.
        let mut props: usize = 0;
        self.unassigned.clear();

        for ci in 0..self.candidates.len() {
            let clause_idx = self.candidates[ci];
            if eliminated.len() >= max_eliminations || props >= prop_limit {
                break;
            }

            let off_header = clause_idx;
            if clauses.is_empty_clause(off_header) {
                continue;
            }

            // Skip reason clauses.
            if clause_idx < reason_clause_marks.len()
                && reason_clause_marks[clause_idx] == reason_clause_epoch
            {
                continue;
            }

            // Mark as tried (CaDiCaL condition.cpp:513) before borrowing lits.
            clauses.set_conditioned(clause_idx, true);

            // Skip clauses containing frozen variables.
            let lits = clauses.literals(clause_idx);
            let has_frozen = lits.iter().any(|&lit| {
                let var = lit.variable().index();
                var < frozen.len() && frozen[var] > 0
            });
            if has_frozen {
                continue;
            }

            self.stats.candidates_checked += 1;

            // Mark candidate clause literals and find initial watched autarky
            // literal. CaDiCaL condition.cpp:527-538.
            //
            // CRITICAL: Mark at the LITERAL level, not variable level.
            // CaDiCaL mark67 stores polarity so is_in_candidate_clause(-lit)
            // returns false when lit (not -lit) was marked. The refinement
            // check (condition.cpp:574) tests the NEGATION of the conditional
            // literal: skip only if ~conditional_lit is in the candidate.
            // Using per-variable marks conflates lit and ~lit, causing unsound
            // GBCE eliminations.
            let mut watched_autarky: Option<Literal> = None;
            for &lit in lits {
                let li = lit.index();
                if li < self.candidate_lits.len() {
                    self.candidate_lits[li] = true;
                }
                if watched_autarky.is_none() {
                    let var = lit.variable().index();
                    let val = if li < vals.len() { vals[li] } else { 0 };
                    if val > 0 && var < self.marks.len() && (self.marks[var] & CONDITIONAL_BIT) == 0
                    {
                        watched_autarky = Some(lit);
                    }
                }
            }

            if watched_autarky.is_none() {
                // No autarky literal in this candidate — cannot be blocked.
                for &lit in lits {
                    let li = lit.index();
                    if li < self.candidate_lits.len() {
                        self.candidate_lits[li] = false;
                    }
                }
                continue;
            }

            // Per-candidate refinement loop (CaDiCaL condition.cpp:565-705).
            // Process conditional literals: if a conditional literal's negation
            // is NOT in the candidate clause, "unassign" it. When unassignment
            // causes a watched clause to lose all true literals, promote the
            // false autarky literals in that clause to conditional.
            debug_assert!(self.unassigned.is_empty());
            let mut cond_cursor: usize = 0;

            'refine: while watched_autarky.is_some()
                && props < prop_limit
                && cond_cursor < self.conditional.len()
            {
                let cond_lit = self.conditional[cond_cursor];
                cond_cursor += 1;

                // If the negation of the conditional literal is in the
                // candidate clause, skip (CaDiCaL condition.cpp:574-577).
                // CRITICAL: Check the NEGATION at the literal level, not the
                // variable level. CaDiCaL: is_in_candidate_clause(-conditional_lit).
                let neg_cond = cond_lit.negated();
                let neg_li = neg_cond.index();
                if neg_li < self.candidate_lits.len() && self.candidate_lits[neg_li] {
                    continue;
                }

                // Skip already-unassigned (from a previous iteration).
                let cond_var = cond_lit.variable().index();
                if cond_var < self.marks.len() && (self.marks[cond_var] & UNASSIGNED_BIT) != 0 {
                    continue;
                }

                // "Unassign" this conditional literal.
                // CaDiCaL condition.cpp:582-584.
                self.marks[cond_var] |= UNASSIGNED_BIT;
                self.unassigned.push(cond_lit);

                // Process unassigned literals: check their occurrence lists.
                // CaDiCaL condition.cpp:591-704.
                let mut ua_cursor = self.unassigned.len() - 1;
                while watched_autarky.is_some()
                    && props < prop_limit
                    && ua_cursor < self.unassigned.len()
                {
                    let ua_lit = self.unassigned[ua_cursor];
                    ua_cursor += 1;
                    props += 1;

                    let ua_li = ua_lit.index();
                    if ua_li >= self.occs.len() {
                        continue;
                    }

                    // Process each watched clause.
                    let mut occ_idx = 0;
                    while occ_idx < self.occs[ua_li].len() {
                        let d_idx = self.occs[ua_li][occ_idx];
                        let d_lits = clauses.literals(d_idx);

                        // Find a replacement watch: an assigned true literal
                        // that hasn't been unassigned.
                        // CaDiCaL condition.cpp:621-629.
                        let replacement = d_lits.iter().find(|&&l| {
                            let li = l.index();
                            let val = if li < vals.len() { vals[li] } else { 0 };
                            let var = l.variable().index();
                            val > 0
                                && var < self.marks.len()
                                && (self.marks[var] & UNASSIGNED_BIT) == 0
                        });

                        if let Some(&rep) = replacement {
                            // Move this clause to the replacement's occ list.
                            let rep_li = rep.index();
                            if rep_li < self.occs.len() {
                                self.occs[rep_li].push(d_idx);
                            }
                            self.occs[ua_li].swap_remove(occ_idx);
                            continue; // Don't increment (swapped element).
                        }

                        occ_idx += 1;

                        // No replacement: promote false autarky literals to
                        // conditional. CaDiCaL condition.cpp:655-691.
                        for &l in d_lits {
                            if watched_autarky.is_none() {
                                break;
                            }
                            let li = l.index();
                            let val = if li < vals.len() { vals[li] } else { 0 };
                            if val >= 0 {
                                continue;
                            }
                            let neg = l.negated();
                            let nvar = neg.variable().index();
                            if nvar >= self.marks.len() {
                                continue;
                            }
                            // Must be autarky (assigned, not conditional, not
                            // unassigned) for promotion.
                            if (self.marks[nvar] & (CONDITIONAL_BIT | UNASSIGNED_BIT)) != 0 {
                                continue;
                            }
                            // Promote to conditional.
                            self.marks[nvar] |= CONDITIONAL_BIT;
                            self.conditional.push(neg);

                            // If the promoted literal is the watched autarky
                            // literal in the candidate, find a replacement.
                            // CaDiCaL condition.cpp:667-690.
                            if Some(neg) == watched_autarky {
                                let rep = lits.iter().find(|&&cl| {
                                    let cv = cl.variable().index();
                                    let cli = cl.index();
                                    let cval = if cli < vals.len() { vals[cli] } else { 0 };
                                    cval > 0
                                        && cv < self.marks.len()
                                        && (self.marks[cv] & (CONDITIONAL_BIT | UNASSIGNED_BIT))
                                            == 0
                                });
                                watched_autarky = rep.copied();
                                if watched_autarky.is_none() {
                                    break 'refine;
                                }
                            }
                        }
                    }
                }
            }

            // Success: an autarky literal survived refinement.
            // CaDiCaL condition.cpp:756-800.
            if watched_autarky.is_some() && props < prop_limit {
                // Collect autarky witnesses: all assigned literals that are
                // still autarky (not conditional, not unassigned).
                let witnesses: Vec<Literal> = (0..self.marks.len())
                    .filter(|&var| (self.marks[var] & (CONDITIONAL_BIT | UNASSIGNED_BIT)) == 0)
                    .filter_map(|var| {
                        let pos = Literal::positive(Variable(var as u32));
                        let neg = pos.negated();
                        let pv = if pos.index() < vals.len() {
                            vals[pos.index()]
                        } else {
                            0
                        };
                        if pv > 0 {
                            Some(pos)
                        } else if pv < 0 || (neg.index() < vals.len() && vals[neg.index()] > 0) {
                            Some(neg)
                        } else {
                            None
                        }
                    })
                    .collect();
                debug_assert!(
                    !witnesses.is_empty(),
                    "BUG: conditioning eliminated clause {clause_idx} with empty witness set",
                );
                // Skip elimination if any witness literal is a frozen
                // variable (#5549). Reconstruction flips witness literals
                // to satisfy removed clauses, which would override the
                // CDCL-assigned value of frozen variables (assumptions,
                // theory vars), causing SAT models to violate assumptions.
                let has_frozen_witness = witnesses.iter().any(|lit| {
                    let var = lit.variable().index();
                    var < frozen.len() && frozen[var] > 0
                });
                if has_frozen_witness {
                    // Cleanup before continuing to next candidate
                    for i in 0..self.unassigned.len() {
                        let var = self.unassigned[i].variable().index();
                        if var < self.marks.len() {
                            self.marks[var] &= !UNASSIGNED_BIT;
                        }
                    }
                    self.unassigned.clear();
                    while self.conditional.len() > initial_conditional_len {
                        let lit = self
                            .conditional
                            .pop()
                            .expect("invariant: len > initial_conditional_len");
                        let var = lit.variable().index();
                        if var < self.marks.len() {
                            self.marks[var] &= !CONDITIONAL_BIT;
                        }
                    }
                    for &lit in lits {
                        let li = lit.index();
                        if li < self.candidate_lits.len() {
                            self.candidate_lits[li] = false;
                        }
                    }
                    continue;
                }
                eliminated.push(ConditionedClause {
                    clause_idx,
                    witnesses,
                });
                self.stats.clauses_eliminated += 1;
            }

            // Cleanup: restore to initial state.
            // Reassign all unassigned literals (CaDiCaL condition.cpp:807-813).
            for i in 0..self.unassigned.len() {
                let var = self.unassigned[i].variable().index();
                if var < self.marks.len() {
                    self.marks[var] &= !UNASSIGNED_BIT;
                }
            }
            self.unassigned.clear();

            // Remove newly-added conditional entries and clear their marks
            // (CaDiCaL condition.cpp:819-827).
            while self.conditional.len() > initial_conditional_len {
                let lit = self
                    .conditional
                    .pop()
                    .expect("invariant: len > initial_conditional_len");
                let var = lit.variable().index();
                if var < self.marks.len() {
                    self.marks[var] &= !CONDITIONAL_BIT;
                }
            }

            // Unmark candidate literal bits.
            for &lit in lits {
                let li = lit.index();
                if li < self.candidate_lits.len() {
                    self.candidate_lits[li] = false;
                }
            }
        }

        // Postcondition: all eliminated clauses must be active.
        debug_assert!(
            eliminated
                .iter()
                .all(|e| !clauses.is_empty_clause(e.clause_idx)),
            "BUG: conditioning eliminated a deleted clause",
        );

        ConditionResult {
            eliminated,
            root_satisfied: root_satisfied_indices,
        }
    }
}
