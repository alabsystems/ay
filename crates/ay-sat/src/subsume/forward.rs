// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One-watch forward subsumption round (CaDiCaL subsume.cpp:335-602).

use super::types::{Bin, KeptThresholds, SubsumeResult, SUBSUME_CLS_LIM, SUBSUME_OCC_LIM};
use super::Subsumer;
use crate::clause::{clause_signature_vars_subset, compute_clause_signature};
use crate::clause_arena::ClauseArena;
use crate::kani_compat::DetHashSet as HashSet;
use crate::literal::Literal;

fn clause_touches_unit_subsumer_var(lits: &[Literal], unit_subsumer_vars: &[bool]) -> bool {
    lits.iter().any(|lit| {
        unit_subsumer_vars
            .get(lit.variable().index())
            .copied()
            .unwrap_or(false)
    })
}

fn is_unit_subsumer_candidate(lits: &[Literal], unit_subsumer_vars: &[bool]) -> bool {
    lits.len() <= 2 && clause_touches_unit_subsumer_var(lits, unit_subsumer_vars)
}

impl Subsumer {
    /// Check whether `new_lits` is already subsumed by an active clause.
    ///
    /// REQUIRES: `rebuild()` was called after the last clause-database mutation.
    /// Uses the rarest literal in `new_lits` to probe only clauses that could
    /// subsume the new clause.
    #[allow(dead_code)]
    pub(crate) fn clause_subsumed_by_existing(
        &mut self,
        new_lits: &[Literal],
        clauses: &ClauseArena,
    ) -> Option<usize> {
        if new_lits.is_empty() {
            return None;
        }

        // Find the literal with the fewest (but nonzero) occurrences to use
        // as a probe. Literals with 0 occurrences are skipped -- they simply
        // mean no existing clause contains that literal, but a smaller clause
        // that omits it can still subsume `new_lits`.
        let mut best_lit = new_lits[0];
        let mut best_count: usize = 0;
        for &lit in new_lits {
            let count = self.full_occs.count(lit);
            if count > 0 && (best_count == 0 || count < best_count) {
                best_lit = lit;
                best_count = count;
            }
        }
        if best_count == 0 {
            return None; // no literal in new_lits appears in any clause
        }

        let candidate_indices: Vec<usize> = self.full_occs.get(best_lit).to_vec();
        // 64-bit signature of the new clause for bloom-style pre-filtering (#7922).
        // For D to subsume new_lits, D's variables must be a subset of new_lits's
        // variables. This O(1) check avoids the O(|D|) subsume_check for most
        // non-matching candidates.
        let new_sig = compute_clause_signature(new_lits);
        self.mark_clause(new_lits);
        let mut subsumer_idx = None;
        for idx in candidate_indices {
            if idx >= clauses.len() || !clauses.is_active(idx) || clauses.is_dead(idx) {
                continue;
            }
            let lits = clauses.literals(idx);
            if lits.len() > new_lits.len() {
                continue;
            }
            // Signature pre-filter: D's variables must be a subset of new_lits's
            // variables for subsumption to be possible (#7922).
            let d_sig = clauses.signature(idx);
            if !clause_signature_vars_subset(d_sig, new_sig) {
                continue;
            }
            if self.subsume_check(lits) == i32::MIN {
                subsumer_idx = Some(idx);
                break;
            }
        }
        self.unmark_clause(new_lits);
        subsumer_idx
    }

    /// Run CaDiCaL-style one-watch forward subsumption.
    ///
    /// `subsume_dirty`: per-variable flags. True = variable was added/modified
    ///   since the last subsumption round. Only clauses with >= 2 dirty variables
    ///   are scheduled as candidates.
    /// `vals`: literal value array indexed by `lit.index()`. Non-zero = fixed at level 0.
    ///   Clauses containing fixed literals are skipped.
    pub(crate) fn run_forward_subsumption(
        &mut self,
        clauses: &mut ClauseArena,
        freeze_counts: &[u32],
        subsume_dirty: &[bool],
        vals: &[i8],
        kept: KeptThresholds,
    ) -> SubsumeResult {
        let _ = freeze_counts; // reserved for future frozen-variable skip
        let mut result = SubsumeResult::new();
        self.stats.rounds += 1;
        self.round_checks = 0;

        // Phase 1: Schedule candidate clauses (CaDiCaL subsume.cpp:382-422)
        self.schedule.clear();

        // CaDiCaL skips clauses with fewer than two dirty variables because
        // ordinary subsumers need at least two recently-added literals. A dirty
        // unit clause is the exception: {a} can subsume clauses containing a and
        // can strengthen clauses containing ~a, including binary clauses to
        // units and opposing unit clauses to empty.
        let mut unit_subsumer_vars = vec![false; self.marks.len()];
        for idx in clauses.indices() {
            let off = idx;
            if clauses.is_empty_clause(off) || clauses.is_dead(off) {
                continue;
            }
            let lits = clauses.literals(off);
            if lits.len() != 1 {
                continue;
            }
            if clauses.is_learned(off)
                && clauses.lbd(off) > kept.tier2_lbd
                && (clauses.lbd(off) > kept.kept_glue || (lits.len() as u32) > kept.kept_size)
            {
                continue;
            }
            let lit = lits[0];
            let li = lit.index();
            if li < vals.len() && vals[li] != 0 {
                continue;
            }
            let v = lit.variable().index();
            if v < subsume_dirty.len() && subsume_dirty[v] && v < unit_subsumer_vars.len() {
                unit_subsumer_vars[v] = true;
            }
        }

        for idx in clauses.indices() {
            let off = idx;
            if clauses.is_empty_clause(off) || clauses.is_dead(off) {
                continue;
            }
            let lits = clauses.literals(off);
            if lits.len() > SUBSUME_CLS_LIM {
                continue;
            }

            // CaDiCaL likely_to_be_kept_clause (internal.hpp:1053-1069):
            // Skip learned clauses unlikely to survive the next reduce_db.
            // Irredundant → always kept. Tier1/tier2 (glue <= tier2_lbd) → always kept.
            // Tier3: kept only if glue <= keptglue AND size <= keptsize.
            if clauses.is_learned(off)
                && clauses.lbd(off) > kept.tier2_lbd
                && (clauses.lbd(off) > kept.kept_glue || (lits.len() as u32) > kept.kept_size)
            {
                continue;
            }

            // Skip clauses with fixed (level-0 assigned) literals
            let mut has_fixed = false;
            let mut dirty_count = 0u32;
            for &lit in lits {
                let li = lit.index();
                if li < vals.len() && vals[li] != 0 {
                    has_fixed = true;
                    break;
                }
                let v = lit.variable().index();
                if v < subsume_dirty.len() && subsume_dirty[v] {
                    dirty_count += 1;
                }
            }
            if has_fixed {
                continue;
            }
            // CaDiCaL subsume.cpp:409-415: skip clauses with fewer than 2 dirty
            // variables. Unit and binary clauses are the soundness exception:
            // one dirty unit subsumer is enough for {a} to shrink {~a, b} to a
            // unit or {~a} to empty.
            let unit_subsumer_candidate =
                dirty_count > 0 && is_unit_subsumer_candidate(lits, &unit_subsumer_vars);
            if dirty_count < 2 && !unit_subsumer_candidate {
                continue;
            }

            self.schedule.push((lits.len(), idx));
        }

        // Sort by size ascending (CaDiCaL subsume.cpp:427)
        self.schedule.sort_unstable_by_key(|&(size, _)| size);
        result.candidates_scheduled = self.schedule.len() as u64;
        self.stats.candidates_scheduled += result.candidates_scheduled;

        // CaDiCaL subsume.cpp:417-432: per-clause `c->subsume` flag.
        // Count left-overs from a previous incomplete round (clauses that
        // still have the flag set because they were scheduled but never
        // reached before the effort limit hit). If no left-overs, this is a
        // fresh round: mark ALL scheduled size>2 clauses for subsumption
        // attempt. If left-overs exist, only those carry the flag — newly-
        // dirty clauses are connected as potential subsumers but not tried,
        // except for unit-subsumer candidates which must be tried to avoid
        // leaving derived unit/empty clauses latent.
        let mut left_over = 0u64;
        for &(_, c_idx) in &self.schedule {
            if clauses.is_subsume_candidate(c_idx) {
                left_over += 1;
            }
        }
        for &(size, c_idx) in &self.schedule {
            let unit_subsumer_candidate =
                is_unit_subsumer_candidate(clauses.literals(c_idx), &unit_subsumer_vars);
            if unit_subsumer_candidate || (left_over == 0 && size > 2) {
                clauses.set_subsume_candidate(c_idx, true);
            }
        }

        // Count per-literal occurrences in scheduled clauses (CaDiCaL subsume.cpp:420-421).
        // Used to sort connected clause literals by ascending frequency so subsumption
        // checks fail faster on rare literals (subsume.cpp:542).
        let num_lits = self.marks.len() * 2;
        self.noccs.resize(num_lits, 0);
        for v in self.noccs[..num_lits].iter_mut() {
            *v = 0;
        }
        for &(_, c_idx) in &self.schedule {
            for &lit in clauses.literals(c_idx) {
                let li = lit.index();
                if li < num_lits {
                    self.noccs[li] += 1;
                }
            }
        }

        // Phase 2: Forward subsumption pass with incremental one-watch connection
        if self.occs.len() < num_lits {
            self.occs.resize_with(num_lits, Vec::new);
        }
        for v in self.occs[..num_lits].iter_mut() {
            v.clear();
        }
        if self.bins.len() < num_lits {
            self.bins.resize_with(num_lits, Vec::new);
        }
        for v in self.bins[..num_lits].iter_mut() {
            v.clear();
        }

        let mut completed = true;
        for si in 0..self.schedule.len() {
            let c_idx = self.schedule[si].1;
            if self.check_limit_reached() {
                completed = false;
                break;
            }

            if clauses.is_empty_clause(c_idx) || clauses.is_dead(c_idx) {
                continue;
            }

            // CaDiCaL subsume.cpp:475-476: only attempt subsumption on clauses
            // with the per-clause `c->subsume` flag set (size > 2). Clear the
            // flag before borrowing literals to satisfy the borrow checker.
            // This prevents redundant re-checking of clauses already tried in
            // a previous round (#7393).
            let is_candidate = clauses.is_subsume_candidate(c_idx);
            if is_candidate {
                clauses.set_subsume_candidate(c_idx, false);
            }

            let c_lits = clauses.literals(c_idx);
            let unit_subsumer_candidate = is_unit_subsumer_candidate(c_lits, &unit_subsumer_vars);

            if (c_lits.len() > 2 || unit_subsumer_candidate) && is_candidate {
                let (d_opt, flipped) =
                    self.try_to_subsume_clause(c_idx, c_lits, subsume_dirty, clauses);

                if let Some(d_idx) = d_opt {
                    if flipped == i32::MIN {
                        // C is subsumed by D — record both indices for
                        // irredundant promotion logic in the solver layer.
                        result.subsumed.push((c_idx, d_idx));
                        self.stats.forward_subsumed += 1;
                        continue; // don't connect subsumed clause
                    } else if flipped != 0 {
                        // Strengthened: decode +1-offset literal and remove its negation from C
                        let remove_lit = Literal((flipped - 1) as u32).negated();
                        let new_lits: Vec<Literal> = c_lits
                            .iter()
                            .filter(|&&l| l != remove_lit)
                            .copied()
                            .collect();
                        debug_assert_eq!(
                            new_lits.len(),
                            c_lits.len() - 1,
                            "BUG: strengthening removed wrong count"
                        );
                        self.stats.strengthened_clauses += 1;
                        self.stats.strengthened_literals += 1;
                        result.strengthened.push((c_idx, new_lits, d_idx));
                        // Strengthened clauses still get connected below
                    }
                }
            }

            // Connect on minimum-occurrence literal (one-watch scheme).
            // Only connect if ALL variables are dirty (can serve as new subsumer).
            let all_dirty = c_lits.iter().all(|&lit| {
                let v = lit.variable().index();
                v < subsume_dirty.len() && subsume_dirty[v]
            });
            if !all_dirty {
                continue;
            }

            let is_binary_irred = c_lits.len() == 2 && !clauses.is_learned(c_idx);

            // CaDiCaL breaks ties on current connection-list size with higher
            // total noccs (subsume.cpp:505-513). This keeps rarer literals in
            // the clause body where they are more useful for fail-fast checks.
            let min_lit = self.pick_connection_literal(c_lits, is_binary_irred);
            let min_size = self.connection_size(min_lit, is_binary_irred);

            let li = min_lit.index();
            if is_binary_irred {
                let other = if c_lits[0] == min_lit {
                    c_lits[1]
                } else {
                    c_lits[0]
                };
                if li < self.bins.len() {
                    self.bins[li].push(Bin {
                        other,
                        clause_idx: c_idx,
                    });
                }
            } else if min_size <= SUBSUME_OCC_LIM && li < self.occs.len() {
                self.occs[li].push(c_idx);

                // Sort non-watched clause literals by ascending noccs (CaDiCaL
                // subsume.cpp:542). Rare literals first → subsume_check fails
                // faster because rare literals are unlikely to appear in the
                // candidate clause's mark set.
                //
                // CaDiCaL sorts ALL literals because it disconnects watches
                // before subsumption (subsume.cpp:628 reset_watches). AY
                // maintains watches incrementally, so positions [0] and [1]
                // (watched pair) must stay fixed. Sorting [2..] still gets
                // most of the benefit for clauses of size >= 4.
                let lits = clauses.literals_mut(c_idx);
                if lits.len() > 3 {
                    let noccs = &self.noccs;
                    lits[2..].sort_unstable_by(|a, b| {
                        let na = noccs.get(a.index()).copied().unwrap_or(0);
                        let nb = noccs.get(b.index()).copied().unwrap_or(0);
                        na.cmp(&nb)
                            .then_with(|| a.variable().index().cmp(&b.variable().index()))
                    });
                }
            }
        }

        // CaDiCaL subsume.cpp:590: only mark the round as completed if all
        // scheduled candidates were processed. Incomplete rounds preserve
        // dirty bits for the next round (the solver layer checks this).
        result.completed = completed;
        if completed {
            self.stats.completed_rounds += 1;
        }
        result.checks_performed = self.round_checks;

        // Cleanup: remove strengthened entries for clauses also subsumed
        result
            .subsumed
            .sort_unstable_by_key(|&(sub_idx, _)| sub_idx);
        result.subsumed.dedup_by_key(|entry| entry.0);
        if !result.subsumed.is_empty() && !result.strengthened.is_empty() {
            let subsumed_set: HashSet<usize> = result
                .subsumed
                .iter()
                .map(|&(sub_idx, _)| sub_idx)
                .collect();
            result
                .strengthened
                .retain(|(idx, _, _)| !subsumed_set.contains(idx));
        }

        result
    }
}
