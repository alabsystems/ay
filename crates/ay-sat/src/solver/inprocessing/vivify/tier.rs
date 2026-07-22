// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-tier vivification processing loop.

use super::super::super::mutate::{DeleteResult, ReasonPolicy, ReplaceResult};
use super::super::super::*;
use super::super::VivifyTierRun;
use crate::kani_compat::DetHashSet as HashSet;

#[cfg(feature = "jit")]
const SIMD_VIVIFY_SUBSUME_THRESHOLD: usize = 64;
#[cfg(feature = "jit")]
const SIMD_VIVIFY_SUBSUME_MAX_LEN: usize = 32;
#[cfg(feature = "jit")]
const SIMD_VIVIFY_SUBSUME_MAX_PAIRS: usize = 200_000;

fn retain_best_candidates(candidates: &mut Vec<(usize, i64)>, limit: usize) {
    if limit < candidates.len() {
        candidates.select_nth_unstable_by_key(limit, |b| std::cmp::Reverse(b.1));
        candidates.truncate(limit);
    }
    candidates.sort_unstable_by_key(|b| std::cmp::Reverse(b.1));
}

#[cfg(feature = "jit")]
fn simd_vivify_subsumed_candidates(sorted_lits: &[Vec<Literal>], eligible: &[bool]) -> Vec<bool> {
    simd_vivify_subsumed_candidates_with_threshold(
        sorted_lits,
        eligible,
        SIMD_VIVIFY_SUBSUME_THRESHOLD,
    )
}

#[cfg(feature = "jit")]
fn simd_vivify_subsumed_candidates_with_threshold(
    sorted_lits: &[Vec<Literal>],
    eligible: &[bool],
    min_candidates: usize,
) -> Vec<bool> {
    let mut candidate_data: Vec<(usize, usize)> = Vec::new();
    for (ci, lits) in sorted_lits.iter().enumerate() {
        if !eligible.get(ci).copied().unwrap_or(false) {
            continue;
        }
        if lits.len() < 2 || lits.len() > SIMD_VIVIFY_SUBSUME_MAX_LEN {
            continue;
        }
        candidate_data.push((ci, lits.len()));
    }

    let mut subsumed = vec![false; sorted_lits.len()];
    if candidate_data.len() < min_candidates {
        return subsumed;
    }

    candidate_data.sort_unstable_by_key(|&(ci, len)| (len, ci));

    let total_lits: usize = candidate_data.iter().map(|&(_, len)| len).sum();
    let mut scanner =
        ay_jit::simd_inprocess::SimdClauseScanner::with_capacity(candidate_data.len(), total_lits);
    let mut candidate_indices = Vec::with_capacity(candidate_data.len());

    for &(ci, _) in &candidate_data {
        let raw_lits: Vec<i32> = sorted_lits[ci].iter().map(|lit| lit.raw() as i32).collect();
        scanner.push(&raw_lits);
        candidate_indices.push(ci);
    }

    let mut pairs = Vec::new();
    'pair_gen: for a in 0..candidate_data.len() {
        let a_len = candidate_data[a].1;
        for (b, &(_, b_len)) in candidate_data.iter().enumerate().skip(a + 1) {
            if a_len > b_len {
                continue;
            }
            pairs.push((a, b));
            if pairs.len() >= SIMD_VIVIFY_SUBSUME_MAX_PAIRS {
                break 'pair_gen;
            }
        }
    }

    for (_, b, is_subsumed) in scanner.batch_subsumption_check(&pairs) {
        if is_subsumed {
            subsumed[candidate_indices[b]] = true;
        }
    }

    subsumed
}

impl Solver {
    pub(super) fn vivify_tier(
        &mut self,
        tier: VivifyTier,
        noccs: &[i64],
        tick_budget: u64,
    ) -> VivifyTierRun {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: vivify_tier at decision level {}",
            self.decision_level
        );
        // CaDiCaL: vivification decisions are artificial — suppress phase saving
        // in enqueue() to avoid corrupting the phase heuristic.
        self.suppress_phase_saving = true;
        if tick_budget == 0 {
            self.suppress_phase_saving = false;
            return VivifyTierRun::default();
        }

        let mut candidates: Vec<(usize, i64)> = Vec::new();
        for idx in self.arena.active_indices() {
            // Garbage-kept husks (mark_garbage_keep_data, e.g. congruence
            // forward subsumption / eager subsumption) still have
            // lit_len_raw != 0, so active_indices() yields them even though
            // BCP and the proof stream treat them as deleted. They must not
            // become vivify candidates: a husk acting as a prefix-subsumption
            // flusher deletes the LIVE twin clause it shadows — observed
            // constraint loss on cmu-bmc-barrel6 (decompose-substituted twin
            // flushed by its own dead husk → bogus internal SAT, caught
            // fail-closed by the finalize original-ledger gate as
            // FINALIZE_SAT_FAIL; wf_ff5991a1 Defect 2).
            if self.arena.is_garbage_any(idx) {
                continue;
            }
            let clen = self.arena.len_of(idx);
            if clen < 3 {
                continue;
            }

            let clause_tier = self.clause_tier(idx);
            let in_tier = match tier {
                VivifyTier::LearnedCore => {
                    self.arena.is_learned(idx) && clause_tier == ClauseTier::Core
                }
                VivifyTier::LearnedTier2 => {
                    self.arena.is_learned(idx) && clause_tier == ClauseTier::Tier1
                }
                VivifyTier::LearnedOther => {
                    self.arena.is_learned(idx) && clause_tier == ClauseTier::Tier2
                }
                VivifyTier::Irredundant => !self.arena.is_learned(idx),
            };
            if !in_tier {
                continue;
            }

            let base_score = Self::vivify_clause_score(self.arena.literals(idx), noccs);
            // For irredundant tier, add a clause-length bonus (#8655).
            // Longer irredundant clauses have more vivification opportunities.
            // On BMC-style structured formulas, these are prime candidates for
            // strengthening.
            let score = if tier == VivifyTier::Irredundant {
                base_score.saturating_add((clen as i64).saturating_mul(1024))
            } else {
                base_score
            };
            candidates.push((idx, score));
        }

        // Every attempted candidate is charged at least one synthetic tick
        // below, so no run can inspect more than `tick_budget` candidates.
        // Select only that many here before building per-candidate literal
        // copies and visit-order state. A full sort used to make a small
        // vivification budget cost O(N log N) time and O(N) extra storage on
        // the entire learned database.
        let candidate_limit = usize::try_from(tick_budget)
            .unwrap_or(usize::MAX)
            .min(candidates.len());
        retain_best_candidates(&mut candidates, candidate_limit);
        // Tick-proportional budgeting: process selected candidates in score
        // order until the tier budget is exhausted. `vivify_ticks` meters
        // propagation work, while the main loop also charges one synthetic
        // tick per candidate attempt.

        // Sort each candidate's literals by nocc score (descending) and store the
        // literal order alongside the clause index.
        //
        // Level-0 simplification: track whether the clause is satisfied at level 0
        // (any literal true at level 0) vs merely having false literals that can
        // be removed.
        let mut sorted_lits: Vec<Vec<Literal>> = Vec::with_capacity(candidates.len());
        let mut level0_satisfied: Vec<bool> = Vec::with_capacity(candidates.len());
        let mut contains_removed_literal: Vec<bool> = Vec::with_capacity(candidates.len());
        for &(clause_idx, _) in &candidates {
            let lits = self.arena.literals(clause_idx);
            let mut sat = false;
            let mut has_removed_literal = false;
            let mut sorted: Vec<Literal> = Vec::with_capacity(lits.len());
            for &lit in lits {
                // Defense-in-depth (#4719): clauses still carrying removed
                // variables are not safe vivification candidates.
                if self.var_lifecycle.is_removed(lit.variable().index()) {
                    has_removed_literal = true;
                    break;
                }
                let val = self.lit_val(lit);
                if val > 0 && self.var_data[lit.variable().index()].level == 0 {
                    sat = true;
                    break;
                }
                if val < 0 && self.var_data[lit.variable().index()].level == 0 {
                    continue; // false at level 0 — drop
                }
                sorted.push(lit);
            }
            if !sat {
                sorted.sort_unstable_by(|a, b| {
                    let sa = noccs.get(a.index()).copied().unwrap_or(0);
                    let sb = noccs.get(b.index()).copied().unwrap_or(0);
                    sb.cmp(&sa) // descending by nocc
                });
            }
            // CaDiCaL vivify.cpp:907: no duplicate variables in sorted list.
            debug_assert!(
                has_removed_literal || {
                    let mut vars: Vec<u32> = sorted.iter().map(|l| l.variable().0).collect();
                    vars.sort_unstable();
                    vars.windows(2).all(|w| w[0] != w[1])
                },
                "BUG: vivify sorted literals contain duplicate variables for clause {clause_idx}",
            );
            sorted_lits.push(sorted);
            level0_satisfied.push(sat);
            contains_removed_literal.push(has_removed_literal);
        }

        // Sort candidate visit order to maximize decision reuse prefix sharing
        // (CaDiCaL vivify.cpp:1543-1551). Lexicographic sort on negated sorted
        // literals groups clauses that share the same initial decisions together.
        // This is a post-truncation reorder: WHICH candidates are selected is
        // unchanged (determined by score), only the processing ORDER changes.
        let mut visit_order: Vec<usize> = (0..candidates.len()).collect();
        visit_order.sort_by(|&a, &b| {
            let sa = &sorted_lits[a];
            let sb = &sorted_lits[b];
            for (la, lb) in sa.iter().zip(sb.iter()) {
                let na = la.negated().0;
                let nb = lb.negated().0;
                match na.cmp(&nb) {
                    std::cmp::Ordering::Equal => continue,
                    other => return other,
                }
            }
            sa.len().cmp(&sb.len())
        });

        // Prefix subsumption flushing (CaDiCaL vivify.cpp:372-419).
        // After sorting by negated-literal lexicographic order, adjacent clauses
        // that share a common prefix can be checked cheaply. If clause A's sorted
        // literals are a prefix of clause B's sorted literals, then A subsumes B
        // and B can be deleted without any propagation work.
        let mut flushed = vec![false; candidates.len()];
        #[cfg(feature = "jit")]
        {
            let simd_eligible: Vec<bool> = candidates
                .iter()
                .enumerate()
                .map(|(ci, &(clause_idx, _))| {
                    !level0_satisfied[ci]
                        && !contains_removed_literal[ci]
                        && sorted_lits[ci].len() == self.arena.len_of(clause_idx)
                })
                .collect();
            let simd_flushed = simd_vivify_subsumed_candidates(&sorted_lits, &simd_eligible);
            let mut simd_count = 0usize;
            for (dst, src) in flushed.iter_mut().zip(simd_flushed) {
                if src {
                    *dst = true;
                    simd_count += 1;
                }
            }
            if simd_count > 0 {
                tracing::debug!(
                    tier = ?tier,
                    simd_subsumed = simd_count,
                    "SIMD vivification candidate subsumption pre-pass"
                );
            }
        }
        {
            let mut prev_ci: Option<usize> = None;
            for &ci in &visit_order {
                if level0_satisfied[ci]
                    || contains_removed_literal[ci]
                    || sorted_lits[ci].is_empty()
                {
                    continue;
                }
                if let Some(pi) = prev_ci {
                    let prev_lits = &sorted_lits[pi];
                    let curr_lits = &sorted_lits[ci];
                    // Check if prev is a prefix of curr (prev subsumes curr).
                    // Guard: prev must be non-empty to avoid vacuous prefix match.
                    if !prev_lits.is_empty()
                        && prev_lits.len() <= curr_lits.len()
                        && prev_lits
                            .iter()
                            .zip(curr_lits.iter())
                            .all(|(a, b)| a.0 == b.0)
                    {
                        flushed[ci] = true;
                    }
                }
                if !flushed[ci] {
                    prev_ci = Some(ci);
                }
            }
        }
        // Delete flushed clauses. Must be at level 0 for clause mutation.
        for &ci in &visit_order {
            if flushed[ci] {
                let clause_idx = candidates[ci].0;
                if !self.arena.is_empty_clause(clause_idx) && self.arena.len_of(clause_idx) >= 2 {
                    // CaDiCaL vivify.cpp mark_removed: mark variables dirty
                    // for subsumption before deleting (#7393).
                    self.mark_subsume_dirty_if_kept(clause_idx);
                    // Snapshot literals before delete for BVE dirty-candidate marking (#7905).
                    let is_irredundant = !self.arena.is_learned(clause_idx);
                    let old_lits = if is_irredundant {
                        Some(self.arena.literals(clause_idx).to_vec())
                    } else {
                        None
                    };
                    if matches!(
                        self.delete_clause_checked(clause_idx, ReasonPolicy::Skip),
                        DeleteResult::Deleted
                    ) && is_irredundant
                    {
                        self.note_irredundant_clause_removed_for_bve(
                            clause_idx,
                            old_lits
                                .as_deref()
                                .expect("irredundant vivify flushed clause snapshot"),
                        );
                    }
                    self.inproc.vivifier.stats.clauses_satisfied += 1;
                }
            }
        }

        let mut run = VivifyTierRun::default();
        // Track effort consumption via vivify_ticks, which increments
        // in VIVIFY-mode BCP with the same cache-line granularity as
        // search_ticks. Budget and consumption in the same unit (#3758).
        let ticks_at_start = self.cold.vivify_ticks;
        let mut candidate_scan_ticks = 0u64;

        // CaDiCaL vivify.cpp:1598-1608: retry counter for cascading
        // simplifications. When a clause is successfully strengthened and
        // still has >2 literals, re-process it immediately (up to
        // VIVIFY_RETRY_LIMIT times).
        let mut retry_count: u32 = 0;
        let mut visit_idx: usize = 0;
        while visit_idx < visit_order.len() {
            // Wall-clock / cooperative-interrupt check. The tick budget below bounds
            // propagation EFFORT, not wall time; on a large formula a single vivify
            // tier can still run far past the solve deadline because the
            // closure-based `should_stop` is only threaded into the CDCL main loop,
            // not inprocessing. Poll the interrupt handle every 64 candidates so a
            // tripped deadline/interrupt aborts the tier promptly. Cutting a tier
            // short is always sound: vivification only strengthens or removes
            // redundant clauses and never changes the formula's satisfiability.
            if visit_idx & 63 == 0 && self.is_interrupted() {
                break;
            }
            let ci = visit_order[visit_idx];
            // Skip flushed (prefix-subsumed) clauses.
            if flushed[ci] {
                visit_idx += 1;
                retry_count = 0;
                continue;
            }
            // Tick budget exhaustion check.
            if self
                .cold
                .vivify_ticks
                .saturating_sub(ticks_at_start)
                .saturating_add(candidate_scan_ticks)
                >= tick_budget
            {
                break;
            }
            candidate_scan_ticks = candidate_scan_ticks.saturating_add(1);

            let clause_idx = candidates[ci].0;
            let clause_ref = ClauseRef(clause_idx as u32);

            // Re-check validity (clause may have been deleted by a prior iteration)
            let clause_len = self.arena.len_of(clause_idx);
            if clause_len < 3 {
                visit_idx += 1;
                retry_count = 0;
                continue;
            }

            let sorted = &sorted_lits[ci];
            if contains_removed_literal[ci] {
                visit_idx += 1;
                retry_count = 0;
                continue;
            }

            // --- Level-0 simplification ---
            // Decision reuse may leave the solver at a non-zero decision level
            // from a previous candidate. Clause mutation (delete/replace) requires
            // level 0 — backtrack before entering the simplification paths (#5025).
            let needs_l0_simplification = level0_satisfied[ci] || sorted.len() < clause_len;
            if needs_l0_simplification && self.decision_level > 0 {
                self.backtrack_without_phase_saving(0);
            }

            if level0_satisfied[ci] {
                // Clause satisfied at level 0: delete it.
                run.processed += 1;
                self.inproc.vivifier.stats.clauses_examined += 1;
                self.inproc.vivifier.stats.clauses_satisfied += 1;
                // CaDiCaL vivify.cpp mark_removed: mark dirty before delete (#7393).
                self.mark_subsume_dirty_if_kept(clause_idx);
                // Snapshot literals before delete for BVE dirty-candidate marking (#7905).
                let is_irredundant = !self.arena.is_learned(clause_idx);
                let old_lits = if is_irredundant {
                    Some(self.arena.literals(clause_idx).to_vec())
                } else {
                    None
                };
                if self.delete_clause_checked(clause_idx, ReasonPolicy::Skip)
                    == DeleteResult::Deleted
                {
                    run.strengthened += 1;
                    if is_irredundant {
                        self.note_irredundant_clause_removed_for_bve(
                            clause_idx,
                            old_lits
                                .as_deref()
                                .expect("irredundant vivify level-0 clause snapshot"),
                        );
                    }
                }
                visit_idx += 1;
                retry_count = 0;
                continue;
            }

            if sorted.len() < clause_len {
                // Some literals are false at level 0 — apply immediate strengthening.
                if sorted.is_empty() {
                    self.suppress_phase_saving = false;
                    run.conflict = true;
                    return run;
                }

                run.processed += 1;
                self.inproc.vivifier.stats.clauses_examined += 1;
                // Read irredundant status before replace (header may be invalidated for Unit).
                let is_irredundant = !self.arena.is_learned(clause_idx);
                // Snapshot literals before replace for BVE dirty-candidate marking (#7905).
                let old_lits = if is_irredundant {
                    Some(self.arena.literals(clause_idx).to_vec())
                } else {
                    None
                };

                match self.replace_clause_checked(clause_idx, sorted) {
                    ReplaceResult::Replaced => {
                        self.inproc.vivifier.stats.clauses_strengthened += 1;
                        self.inproc.vivifier.stats.literals_removed +=
                            (clause_len - sorted.len()) as u64;
                        run.strengthened += 1;
                        // CaDiCaL mark_added: shorter clause may subsume others (#7393).
                        self.mark_subsume_dirty_if_kept(clause_idx);
                        if is_irredundant {
                            self.note_irredundant_clause_replaced_for_bve(
                                clause_idx,
                                old_lits
                                    .as_deref()
                                    .expect("irredundant vivify strengthened clause snapshot"),
                                sorted,
                            );
                        }
                    }
                    ReplaceResult::Unit => {
                        self.inproc.vivifier.stats.clauses_strengthened += 1;
                        self.inproc.vivifier.stats.literals_removed +=
                            (clause_len - sorted.len()) as u64;
                        run.strengthened += 1;
                        run.enqueued_units = true;
                        if is_irredundant {
                            self.note_irredundant_clause_replaced_for_bve(
                                clause_idx,
                                old_lits
                                    .as_deref()
                                    .expect("irredundant vivify strengthened clause snapshot"),
                                sorted,
                            );
                        }
                    }
                    ReplaceResult::Empty => {
                        self.suppress_phase_saving = false;
                        run.conflict = true;
                        return run;
                    }
                    ReplaceResult::Skipped => {}
                }
                visit_idx += 1;
                retry_count = 0;
                continue;
            }

            // Need at least 2 non-level-0 literals for propagation-based vivification.
            if sorted.len() < 2 {
                visit_idx += 1;
                retry_count = 0;
                continue;
            }

            // Decision reuse prefix matching (CaDiCaL vivify.cpp:970-988).
            // If the trail has reused decisions from the previous candidate,
            // compare the current candidate's sorted literals against them.
            // Backtrack only to the first divergence point, keeping matching
            // prefix decisions and their propagations on the trail.
            if self.decision_level > 0 {
                let mut l: u32 = 1;
                let mut diverged = false;
                for &lit in sorted.iter() {
                    if l > self.decision_level {
                        break;
                    }
                    let decision_trail_idx = self.trail_lim[(l - 1) as usize];
                    let decision_lit = self.trail[decision_trail_idx];
                    if lit.negated() == decision_lit {
                        // Reuse: this decision matches the current candidate
                        self.inproc.vivifier.stats.decisions_reused += 1;
                        l += 1;
                    } else {
                        // Mismatch: backtrack to just before this level
                        self.backtrack_without_phase_saving(l - 1);
                        diverged = true;
                        break;
                    }
                }
                // If all sorted lits matched but trail has extra levels from the
                // previous candidate, backtrack those extra levels.
                if !diverged && l <= self.decision_level {
                    self.backtrack_without_phase_saving(l - 1);
                }
            }

            // Mark clause header to skip during propagation (CaDiCaL: ignore = c).
            self.arena.set_vivify_skip(clause_idx, true);

            // Check if the clause is already the reason for forcing one of its
            // literals true. If so, we must backtrack below that level first
            // to avoid incorrectly concluding the clause is redundant.
            // (CaDiCaL: lines 943-965 in vivify.cpp)
            let clause_lits_snapshot: Vec<Literal> = self.arena.literals(clause_idx).to_vec();
            for &lit in &clause_lits_snapshot {
                let val = self.lit_val(lit);
                if val <= 0 {
                    continue; // false or unassigned
                }
                // lit is true — check if this clause is its reason
                let var_idx = lit.variable().index();
                if self.var_data[var_idx].reason == clause_ref.0 {
                    // Must backtrack below this level
                    let forced_level = self.var_data[var_idx].level;
                    if forced_level > 0 {
                        self.backtrack_without_phase_saving(forced_level - 1);
                    }
                }
                break; // only check the first non-false literal (watch invariant)
            }

            // Vivify: decide -lit for each literal in sorted order
            let mut strengthened: Option<Vec<Literal>> = None;
            let mut is_subsumed = false;
            let mut conflict_found = false;
            let mut probe_lrat_hints: Vec<u64> = Vec::new();
            let mut captured_removed_reasons: Vec<u64> = Vec::new();
            // LRAT hint infrastructure (#4360): track trail position for
            // complete BCP reason chain capture (CaDiCaL vivify.cpp:1094-1098).
            let trail_start_pos = self.trail.len();
            let mut is_instantiation_path = false;
            let mut trail_pos_before_inst: usize = 0;
            let mut used_inline_subsumption = false;
            let mut used_analysis_subsumption = false;
            let mut subsuming_clause: Option<ClauseRef> = None;
            // CaDiCaL vivify.cpp:586: track whether any reason clause in the
            // resolution chain is redundant (learned). Phase 3 (#3310) will
            // use this to gate irredundant clause subsumption decisions.
            let mut _vivify_uses_redundant = false;

            let start_level = self.decision_level;
            let _probe_trail_start = self.trail.len();
            for &lit in sorted.iter() {
                // Tick accounting: 1 vivify tick per literal tested (#8188).
                // CaDiCaL charges ticks per literal in vivify_clause
                // (vivify.cpp:886,1020). Without this, vivification budget
                // consumption is undercounted and runs too long.
                self.cold.vivify_ticks += 1;

                let val = self.lit_val(lit);
                if val > 0 {
                    // Literal is already true (from propagation or reused decision).
                    // If implied (has a reason), the clause may be subsumed.
                    // CaDiCaL vivify.cpp:1051-1054, 1117-1133.
                    let var_idx = lit.variable().index();
                    if self.var_data[var_idx].reason != NO_REASON {
                        let implied_lit = self.pick_vivify_implied_literal(lit, sorted);
                        let (necessary_decisions, lrat_chain, uses_redundant, subsuming) =
                            self.vivify_analyze_implied_literal(implied_lit, sorted);
                        _vivify_uses_redundant = uses_redundant;
                        if let Some(subsuming) = subsuming {
                            is_subsumed = true;
                            used_analysis_subsumption = true;
                            subsuming_clause = Some(subsuming);
                        } else {
                            let mut kept =
                                Vec::with_capacity(necessary_decisions.len().saturating_add(1));
                            for &slit in sorted.iter() {
                                let keep_implied = slit == implied_lit;
                                let keep_decision =
                                    necessary_decisions.contains(&slit.variable().index());
                                if keep_implied || keep_decision {
                                    kept.push(slit);
                                }
                            }
                            if kept.len() < clause_len {
                                probe_lrat_hints = lrat_chain;
                                strengthened = Some(kept);
                            } else {
                                if tier == VivifyTier::Irredundant && uses_redundant {
                                    // Keep the old conservative fallback when the
                                    // learned reason chain proves redundancy but
                                    // does not produce a concrete subsumer or a
                                    // shorter clause.
                                    continue;
                                }
                                is_subsumed = true;
                            }
                        }
                        break;
                    }
                    // Keep already-satisfied literals in the candidate clause.
                    continue;
                }
                if val < 0 {
                    // Literal is already false — it can be removed from the clause
                    continue;
                }

                // CaDiCaL vivify.cpp: literal must be unassigned before probe decision
                debug_assert_eq!(
                    val, 0,
                    "BUG: vivify probe deciding non-unassigned literal {lit:?} (val={val})",
                );
                if self.var_lifecycle.is_removed(lit.variable().index()) {
                    continue;
                }
                // Drain pending propagations from chrono-BT compaction
                // (#7249). Partial backtrack (decision reuse or forced-level
                // backtrack) can leave qhead < trail.len(). decide() asserts
                // qhead == trail.len().
                if self.qhead < self.trail.len() {
                    if let Some(drain_conflict) = self.vivify_propagate() {
                        // BCP conflict during drain: the current partial
                        // assignment is inconsistent. Treat as a vivify
                        // conflict for this candidate (same as the
                        // post-decide conflict path below).
                        conflict_found = true;
                        if self.vivify_conflict_clause_subsumes_candidate(
                            clause_idx,
                            sorted,
                            drain_conflict,
                        ) {
                            is_subsumed = true;
                            used_inline_subsumption = true;
                            subsuming_clause = Some(drain_conflict);
                            let conflict_idx = drain_conflict.0 as usize;
                            if conflict_idx < self.arena.len() {
                                _vivify_uses_redundant |= self.arena.is_learned(conflict_idx);
                            }
                        } else {
                            let (necessary_decisions, _lrat_chain, uses_redundant, subsuming) =
                                self.vivify_analyze_conflict(drain_conflict, sorted);
                            _vivify_uses_redundant = uses_redundant;
                            if subsuming.is_some() {
                                is_subsumed = true;
                                used_analysis_subsumption = true;
                                subsuming_clause = subsuming;
                            } else {
                                let mut kept = Vec::with_capacity(necessary_decisions.len());
                                for &slit in sorted.iter() {
                                    if necessary_decisions.contains(&slit.variable().index()) {
                                        kept.push(slit);
                                    }
                                }
                                if kept.len() < clause_len {
                                    strengthened = Some(kept);
                                }
                            }
                        }
                        break;
                    }
                    // Re-check literal value after drain.
                    let new_val = self.lit_val(lit);
                    if new_val != 0 {
                        continue;
                    }
                }
                // Literal is unassigned: decide its negation
                self.decide(lit.negated());
                let conflict = self.vivify_propagate();
                if let Some(conflict_ref) = conflict {
                    conflict_found = true;
                    if self.vivify_conflict_clause_subsumes_candidate(
                        clause_idx,
                        sorted,
                        conflict_ref,
                    ) {
                        // CaDiCaL vivify_deduce short-circuits when the conflict
                        // clause is already a subset of the candidate. Deleting
                        // the candidate is stronger and avoids unnecessary
                        // backward analysis on a clause we are about to remove.
                        is_subsumed = true;
                        used_inline_subsumption = true;
                        subsuming_clause = Some(conflict_ref);
                        let conflict_idx = conflict_ref.0 as usize;
                        if conflict_idx < self.arena.len() {
                            _vivify_uses_redundant |= self.arena.is_learned(conflict_idx);
                        }
                    } else {
                        // Full backward trail analysis (CaDiCaL vivify_analyze):
                        // identifies only decisions causally needed for the conflict,
                        // producing shorter vivified clauses than keeping all decisions.
                        // Also checks each reason clause for subsumption against the
                        // candidate (CaDiCaL vivify_analyze vivify.cpp:587-635).
                        let (necessary_decisions, lrat_chain, uses_redundant, subsuming) =
                            self.vivify_analyze_conflict(conflict_ref, sorted);
                        _vivify_uses_redundant = uses_redundant;
                        if subsuming.is_some() {
                            // A reason clause during backward analysis subsumes the
                            // candidate (CaDiCaL vivifysubs path). Delete candidate.
                            is_subsumed = true;
                            used_analysis_subsumption = true;
                            subsuming_clause = subsuming;
                        } else {
                            probe_lrat_hints = lrat_chain;
                            // Conflict clause at position 0 → after global reversal in
                            // replace_clause_impl, it appears LAST (after all unit
                            // propagations) producing the final contradiction.
                            if self.cold.lrat_enabled {
                                let cid = self.clause_id(conflict_ref);
                                if cid != 0 {
                                    probe_lrat_hints.insert(0, cid);
                                }
                            }
                            // Build strengthened clause: ONLY causally-needed decisions
                            // from backward analysis (CaDiCaL vivify_analyze pattern).
                            // Undecided literals after the conflict point are dropped:
                            // they played no role in the conflict derivation, so the
                            // resolution proof of the shorter clause is valid without
                            // them. This produces strictly shorter clauses than the
                            // previous conservative approach (#3292 Bug D) which kept
                            // all undecided literals.
                            let mut kept = Vec::with_capacity(necessary_decisions.len());
                            for &slit in sorted.iter() {
                                let var_idx = slit.variable().index();
                                if necessary_decisions.contains(&var_idx) {
                                    kept.push(slit);
                                }
                            }
                            if kept.len() < clause_len {
                                strengthened = Some(kept);
                            }
                        }
                    }
                    break;
                }
            }

            // If no conflict and no subsumption: try instantiation fallback.
            // Assume the last literal positively (not negated). If conflict,
            // that literal can be removed from the clause.
            if !conflict_found
                && !is_subsumed
                && strengthened.is_none()
                && self.decision_level > start_level
            {
                // Backtrack one level (undo the last decision)
                self.backtrack_without_phase_saving(self.decision_level - 1);
                // Record trail position after partial backtrack for LRAT hint
                // chain boundary (#4360). Probe reasons occupy
                // trail[trail_start_pos..here]; instantiation reasons occupy
                // trail[here..end]. CaDiCaL vivify.cpp:1145 discards the
                // analysis chain here and rebuilds via vivify_build_lrat.
                trail_pos_before_inst = self.trail.len();
                if let Some(&last_lit) = sorted.last() {
                    // Drain pending propagations from chrono-BT compaction
                    // (#7249). backtrack_without_phase_saving() above can
                    // leave qhead < trail.len(). decide() asserts equality.
                    if self.qhead < self.trail.len() && self.vivify_propagate().is_some() {
                        // Conflict during drain — the partial assignment
                        // from decision reuse is inconsistent. Skip the
                        // instantiation attempt; the outer loop will
                        // backtrack to level 0 and handle the candidate.
                    }
                    if self.qhead == self.trail.len()
                        && self.lit_val(last_lit) == 0
                        && !self.var_lifecycle.is_removed(last_lit.variable().index())
                    {
                        // Decide the literal positively
                        self.decide(last_lit);
                        let conflict = self.vivify_propagate();
                        if let Some(conflict_ref) = conflict {
                            let (_decisions, lrat_chain, uses_redundant, _) =
                                self.vivify_analyze_conflict(conflict_ref, &[]);
                            _vivify_uses_redundant = uses_redundant;
                            probe_lrat_hints = lrat_chain;
                            if self.cold.lrat_enabled {
                                let cid = self.clause_id(conflict_ref);
                                if cid != 0 {
                                    probe_lrat_hints.insert(0, cid);
                                }
                            }
                            is_instantiation_path = true;
                            // Instantiation succeeded: the last literal is redundant
                            let kept: Vec<Literal> = sorted[..sorted.len() - 1].to_vec();
                            if kept.len() < clause_len {
                                strengthened = Some(kept);
                            }
                        }
                    }
                }
            }

            // Capture LRAT hints by walking the trail in forward (propagation)
            // order (#4360). This captures the FULL BCP reason chain including
            // intermediate/auxiliary variable reasons needed by the LRAT checker
            // for RUP verification.
            //
            // Previous approach (W7 iter 1281) only captured direct reasons for
            // removed clause literals, missing chain dependencies through
            // auxiliary variables. CaDiCaL vivify.cpp:572-661 (vivify_analyze)
            // walks the trail backward then reverses; we walk forward directly.
            //
            // For the instantiation path, we build a two-phase chain with the
            // original clause ID as a bridge (CaDiCaL vivify.cpp:827-867).
            if self.cold.lrat_enabled && strengthened.is_some() {
                if is_instantiation_path {
                    // Instantiation path: three phases in REVERSE order for
                    // the global reversal in replace_clause_impl (#4398).
                    //
                    // Checker needs: [phase1_forward, bridge, phase3_forward]
                    // Pre-reversal:  [phase3_reverse, bridge, phase1_reverse]
                    //
                    // Phase 3 (first in pre-reversal): instantiation BCP
                    // reasons from deciding the removed literal positively.
                    for i in (trail_pos_before_inst..self.trail.len()).rev() {
                        let var_idx = self.trail[i].variable().index();
                        if let Some(reason_ref) = self.var_reason(var_idx) {
                            let reason_id = self.clause_id(reason_ref);
                            if reason_id != 0 {
                                captured_removed_reasons.push(reason_id);
                            }
                        }
                    }
                    // Phase 2 (bridge): original clause ID. After the RUP
                    // checker processes probe reasons + sets kept literals
                    // false, the original clause becomes unit.
                    let original_cid = self.clause_id(clause_ref);
                    if original_cid != 0 {
                        captured_removed_reasons.push(original_cid);
                    }
                    // Phase 1 (last in pre-reversal → first after reversal):
                    // probe BCP reasons before instantiation backtrack.
                    for i in (trail_start_pos..trail_pos_before_inst).rev() {
                        let var_idx = self.trail[i].variable().index();
                        if let Some(reason_ref) = self.var_reason(var_idx) {
                            let reason_id = self.clause_id(reason_ref);
                            if reason_id != 0 {
                                captured_removed_reasons.push(reason_id);
                            }
                        }
                    }
                } else {
                    // Conflict path: single-phase capture. Walk the trail in
                    // REVERSE order to match `vivify_analyze_conflict`
                    // ordering. Both sources must use reverse trail order so that
                    // the global reversal in `replace_clause_impl` produces
                    // forward trail order for the LRAT checker (#4398).
                    for i in (trail_start_pos..self.trail.len()).rev() {
                        let var_idx = self.trail[i].variable().index();
                        if let Some(reason_ref) = self.var_reason(var_idx) {
                            let reason_id = self.clause_id(reason_ref);
                            if reason_id != 0 {
                                captured_removed_reasons.push(reason_id);
                            }
                        }
                    }
                }
            }

            // Clear vivify-skip header bit (safe at any level — the clause was
            // excluded from propagation, so no trail entry references it).
            self.arena.set_vivify_skip(clause_idx, false);

            run.processed += 1;
            self.inproc.vivifier.stats.clauses_examined += 1;

            // Decision reuse: only backtrack to level 0 when the candidate has a
            // result that requires clause database modification. "No change"
            // candidates keep the trail for prefix sharing with the next candidate
            // (CaDiCaL vivify.cpp:970-988 decision reuse optimization).
            let has_result = conflict_found || is_subsumed || strengthened.is_some();
            if has_result {
                self.backtrack_without_phase_saving(0);
            }

            // Handle subsumption (clause is satisfied/redundant)
            if is_subsumed {
                if tier == VivifyTier::Irredundant && _vivify_uses_redundant {
                    // CaDiCaL vivify_subsume_clause promotes a concrete learned
                    // subsumer to irredundant before deleting the irredundant
                    // candidate. Keep the old conservative skip only when we do
                    // not know which clause actually subsumed the candidate
                    // (for example the implied-literal shortcut path).
                    let Some(subsuming_ref) = subsuming_clause else {
                        visit_idx += 1;
                        retry_count = 0;
                        continue;
                    };
                    let subsuming_idx = subsuming_ref.0 as usize;
                    // Reject garbage-kept husks as subsumers: they pass
                    // is_active() (lit_len_raw != 0) but are deleted from the
                    // live formula (wf_ff5991a1 Defect 2 hardening).
                    if subsuming_idx >= self.arena.len()
                        || !self.arena.is_active(subsuming_idx)
                        || self.arena.is_garbage_any(subsuming_idx)
                    {
                        visit_idx += 1;
                        retry_count = 0;
                        continue;
                    }
                    if self.arena.is_learned(subsuming_idx) {
                        self.arena.set_learned(subsuming_idx, false);
                        // BVE occ lists only track irredundant clauses. Notify
                        // BVE about the promotion so occ lists stay consistent (#8135).
                        let promoted_lits: Vec<Literal> =
                            self.arena.literals(subsuming_idx).to_vec();
                        self.note_clause_promoted_to_irredundant(subsuming_idx, &promoted_lits);
                        self.mark_subsume_dirty_if_kept(subsuming_idx);
                    }
                }
                if used_inline_subsumption {
                    self.inproc.vivifier.stats.inline_subsumed += 1;
                } else if used_analysis_subsumption {
                    self.inproc.vivifier.stats.analysis_subsumed += 1;
                }
                self.inproc.vivifier.stats.clauses_satisfied += 1;
                // CaDiCaL vivify.cpp mark_removed: mark dirty before delete (#7393).
                self.mark_subsume_dirty_if_kept(clause_idx);
                // Snapshot literals before delete for BVE dirty-candidate marking (#7905).
                let is_irredundant = !self.arena.is_learned(clause_idx);
                let old_lits = if is_irredundant {
                    Some(self.arena.literals(clause_idx).to_vec())
                } else {
                    None
                };
                if matches!(
                    self.delete_clause_checked(clause_idx, ReasonPolicy::Skip),
                    DeleteResult::Deleted
                ) && is_irredundant
                {
                    self.note_irredundant_clause_removed_for_bve(
                        clause_idx,
                        old_lits
                            .as_deref()
                            .expect("irredundant vivify subsumed clause snapshot"),
                    );
                }
                visit_idx += 1;
                retry_count = 0;
                continue;
            }

            // Handle strengthening
            let was_strengthened = strengthened.is_some();
            let Some(new_lits) = strengthened else {
                visit_idx += 1;
                retry_count = 0;
                continue;
            };
            if new_lits.len() >= clause_len || new_lits.is_empty() {
                visit_idx += 1;
                retry_count = 0;
                continue;
            }

            // Check frozen literals: if any literal in the clause is frozen,
            // ensure it's preserved in the strengthened clause
            let has_frozen = clause_lits_snapshot.iter().any(|lit| {
                self.cold
                    .freeze_counts
                    .get(lit.variable().index())
                    .copied()
                    .unwrap_or(0)
                    > 0
            });
            let final_lits = if has_frozen {
                let mut merged = Vec::with_capacity(clause_len);
                let kept_set: HashSet<Literal> = new_lits.iter().copied().collect();
                for &lit in &clause_lits_snapshot {
                    let frozen = self
                        .cold
                        .freeze_counts
                        .get(lit.variable().index())
                        .copied()
                        .unwrap_or(0)
                        > 0;
                    if frozen || kept_set.contains(&lit) {
                        merged.push(lit);
                    }
                }
                if merged.len() >= clause_len {
                    visit_idx += 1;
                    retry_count = 0;
                    continue; // no actual improvement after preserving frozen lits
                }
                merged
            } else {
                new_lits
            };

            // No duplicate variables in vivify final_lits
            debug_assert!(
                {
                    let mut vars: Vec<u32> = final_lits.iter().map(|l| l.variable().0).collect();
                    vars.sort_unstable();
                    vars.windows(2).all(|w| w[0] != w[1])
                },
                "BUG: vivify final_lits has duplicate variables for clause {clause_idx}",
            );
            debug_assert!(
                !final_lits.is_empty(),
                "BUG: vivify final_lits empty for clause {clause_idx}",
            );

            // Use backward analysis as the primary LRAT hint source.
            // The captured trail reasons are in the correct reverse-trail order
            // but may introduce hints the checker can't process in sequence.
            // Use captured hints ONLY when backward analysis produced nothing
            // (defense against empty backward chains) (#4398).
            let vivify_lrat_hints = if probe_lrat_hints.is_empty() && self.cold.lrat_enabled {
                captured_removed_reasons.clone()
            } else {
                probe_lrat_hints.clone()
            };
            // Read irredundant status before replace (header may be invalidated for Unit).
            let is_irredundant = !self.arena.is_learned(clause_idx);
            // Snapshot literals before replace for BVE dirty-candidate marking (#7905).
            let old_lits = if is_irredundant {
                Some(self.arena.literals(clause_idx).to_vec())
            } else {
                None
            };

            match self.replace_clause_checked_with_lrat_hints(
                clause_idx,
                &final_lits,
                &vivify_lrat_hints,
            ) {
                ReplaceResult::Replaced => {
                    run.strengthened += 1;
                    self.inproc.vivifier.stats.clauses_strengthened += 1;
                    self.inproc.vivifier.stats.literals_removed +=
                        (clause_len - final_lits.len()) as u64;
                    // CaDiCaL mark_added: shorter clause may subsume others (#7393).
                    self.mark_subsume_dirty_if_kept(clause_idx);
                    if is_irredundant {
                        self.note_irredundant_clause_replaced_for_bve(
                            clause_idx,
                            old_lits
                                .as_deref()
                                .expect("irredundant vivify strengthened clause snapshot"),
                            &final_lits,
                        );
                    }
                }
                ReplaceResult::Unit => {
                    run.strengthened += 1;
                    self.inproc.vivifier.stats.clauses_strengthened += 1;
                    self.inproc.vivifier.stats.literals_removed +=
                        (clause_len - final_lits.len()) as u64;
                    run.enqueued_units = true;
                    if is_irredundant {
                        self.note_irredundant_clause_replaced_for_bve(
                            clause_idx,
                            old_lits
                                .as_deref()
                                .expect("irredundant vivify strengthened clause snapshot"),
                            &final_lits,
                        );
                    }
                }
                ReplaceResult::Empty => {
                    self.suppress_phase_saving = false;
                    run.conflict = true;
                    return run;
                }
                ReplaceResult::Skipped => {}
            }

            // CaDiCaL vivify.cpp:1598-1608: retry successfully vivified
            // clauses. When strengthened and still >2 literals, re-snapshot
            // the clause from the arena and retry without advancing visit_idx.
            let did_strengthen = has_result && !is_subsumed && was_strengthened;
            let should_retry = did_strengthen
                && retry_count < VIVIFY_RETRY_LIMIT
                && !self.arena.is_empty_clause(clause_idx)
                && self.arena.len_of(clause_idx) > 2;

            if should_retry {
                retry_count += 1;
                // Re-snapshot the clause from the arena for the next pass.
                let new_lits_from_arena = self.arena.literals(clause_idx);
                let mut resorted: Vec<Literal> = Vec::with_capacity(new_lits_from_arena.len());
                let mut re_sat = false;
                let mut has_removed = false;
                for &lit in new_lits_from_arena {
                    if self.var_lifecycle.is_removed(lit.variable().index()) {
                        has_removed = true;
                        break;
                    }
                    let val = self.lit_val(lit);
                    if val > 0 && self.var_data[lit.variable().index()].level == 0 {
                        re_sat = true;
                        break;
                    }
                    if val < 0 && self.var_data[lit.variable().index()].level == 0 {
                        continue;
                    }
                    resorted.push(lit);
                }
                if re_sat || has_removed || resorted.len() < 3 {
                    visit_idx += 1;
                    retry_count = 0;
                } else {
                    resorted.sort_unstable_by(|a, b| {
                        let sa = noccs.get(a.index()).copied().unwrap_or(0);
                        let sb = noccs.get(b.index()).copied().unwrap_or(0);
                        sb.cmp(&sa)
                    });
                    sorted_lits[ci] = resorted;
                    level0_satisfied[ci] = false;
                    contains_removed_literal[ci] = false;
                    // Do not advance visit_idx -- re-process same candidate.
                }
            } else {
                visit_idx += 1;
                if !did_strengthen {
                    retry_count = 0;
                }
            }
        }

        // Ensure we're back at level 0 after vivification
        if self.decision_level > 0 {
            self.backtrack_without_phase_saving(0);
        }
        self.suppress_phase_saving = false;

        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: vivify_tier did not restore decision level to 0"
        );

        run
    }
}

#[cfg(test)]
mod candidate_selection_tests {
    use super::retain_best_candidates;

    #[test]
    fn candidate_selection_keeps_only_highest_scores() {
        let mut candidates = vec![(0, 2), (1, 9), (2, -1), (3, 7), (4, 4)];

        retain_best_candidates(&mut candidates, 3);

        assert_eq!(candidates, vec![(1, 9), (3, 7), (4, 4)]);
    }

    #[test]
    fn candidate_selection_accepts_limit_larger_than_input() {
        let mut candidates = vec![(0, 2), (1, 9)];

        retain_best_candidates(&mut candidates, 10);

        assert_eq!(candidates, vec![(1, 9), (0, 2)]);
    }
}

#[cfg(all(test, feature = "jit"))]
mod tests {
    use super::*;
    use crate::test_util::lit;

    #[test]
    fn simd_vivify_candidate_subsumption_finds_non_prefix_subset() {
        let sorted_lits = vec![
            vec![lit(0, true), lit(2, true)],
            vec![lit(2, true), lit(1, true), lit(0, true)],
            vec![lit(3, true), lit(4, true)],
        ];
        let eligible = vec![true; sorted_lits.len()];

        let subsumed = simd_vivify_subsumed_candidates_with_threshold(&sorted_lits, &eligible, 1);

        assert_eq!(subsumed, vec![false, true, false]);
    }

    #[test]
    fn simd_vivify_candidate_subsumption_keeps_one_duplicate() {
        let sorted_lits = vec![
            vec![lit(0, true), lit(1, true)],
            vec![lit(1, true), lit(0, true)],
        ];
        let eligible = vec![true; sorted_lits.len()];

        let subsumed = simd_vivify_subsumed_candidates_with_threshold(&sorted_lits, &eligible, 1);

        assert_eq!(subsumed, vec![false, true]);
    }

    #[test]
    fn simd_vivify_candidate_subsumption_respects_eligibility() {
        let sorted_lits = vec![
            vec![lit(0, true), lit(1, true)],
            vec![lit(0, true), lit(1, true), lit(2, true)],
        ];
        let eligible = vec![true, false];

        let subsumed = simd_vivify_subsumed_candidates_with_threshold(&sorted_lits, &eligible, 1);

        assert_eq!(subsumed, vec![false, false]);
    }
}
