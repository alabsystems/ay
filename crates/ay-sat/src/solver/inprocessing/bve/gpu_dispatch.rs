// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GPU-accelerated BVE resolvent generation dispatch.
//!
//! When the GPU feature is enabled and the number of resolution pairs
//! exceeds `GpuBvePipeline::should_use_gpu`, the BVE elimination check
//! dispatches resolvent generation to the GPU. The GPU computes raw
//! resolvents and tautology flags in parallel. The CPU then post-processes
//! them for OTFS (on-the-fly strengthening), budget tracking, and proof
//! management.
//!
//! CPU-path parity: before dispatch, occurrence lists are filtered and
//! classified exactly like `check_bounded_elimination_with_marks` +
//! `try_resolve_pair` on the CPU path:
//! - stale (dead / out-of-range) occurrence entries are dropped;
//! - the `ELIM_OCC_LIMIT` occurrence cap rejects the elimination;
//! - tautological parents produce no resolvents;
//! - root-satisfied parents produce no resolvents and are reported in
//!   `satisfied_parents` so they are NOT pushed as reconstruction
//!   witnesses (#8356/#8397);
//! - the global resolution-effort budget is honored.
//!
//! Fallback: if GPU initialization fails, the dispatch exceeds device
//! limits, or the pair count is below threshold, the standard CPU
//! resolution path is used unchanged.

use super::super::super::*;
use crate::bve::{ELIM_CLAUSE_SIZE_LIMIT, ELIM_OCC_LIMIT};
use crate::clause::{clause_signature_bit, clause_signature_may_subsume};
use crate::kani_compat::DetHashMap;
use crate::literal::{Literal, Variable};

impl Solver {
    /// Check whether GPU-accelerated BVE resolution should be used for
    /// the given positive/negative occurrence pair counts.
    ///
    /// Returns true when:
    /// 1. The `gpu` feature is enabled
    /// 2. The pair count exceeds the GPU dispatch threshold (2048)
    /// 3. The GPU BVE pipeline is available (adapter probe succeeded)
    pub(in crate::solver) fn should_use_gpu_bve(&mut self, num_pos: usize, num_neg: usize) -> bool {
        if !crate::gpu::bve::GpuBvePipeline::should_use_gpu(num_pos, num_neg) {
            return false;
        }
        // Lazily initialize the GPU context + BVE pipeline.
        self.inproc.gpu_bve().is_some()
    }

    /// Dispatch GPU-accelerated BVE resolvent generation for a variable.
    ///
    /// Generates all resolvents between positive and negative occurrence
    /// clauses on the GPU, then applies CPU-side post-processing:
    /// - Tautology filtering (handled by GPU)
    /// - Clause size limit enforcement
    /// - Self-subsuming resolution (OTFS) detection
    /// - Budget/bound checking
    ///
    /// `remaining_budget` is the number of resolution attempts left in the
    /// global BVE effort budget (CPU parity: incremental effort charging,
    /// #8195). If the filtered pair count exceeds it, the elimination is
    /// rejected with the budget reported as consumed, matching the CPU
    /// path's mid-variable abort.
    ///
    /// Returns `None` if the GPU dispatch fails (caller falls back to CPU).
    /// Returns `Some((can_eliminate, resolvents, strengthened, satisfied_parents, attempts))`
    /// in the same format as `check_bounded_elimination_with_marks`.
    pub(in crate::solver) fn gpu_bve_resolve_and_check(
        &mut self,
        pivot_var: Variable,
        pos_clause_indices: &[usize],
        neg_clause_indices: &[usize],
        remaining_budget: u64,
    ) -> Option<(
        bool,
        Vec<(Vec<Literal>, usize, usize, Vec<usize>)>,
        Vec<crate::bve::ClauseStrengthening>,
        Vec<usize>,
        u64,
    )> {
        // Filter and classify occurrence lists (CPU parity: resolve.rs
        // filters stale entries; profiles mark tautological parents;
        // resolution reports root-satisfied parents).
        let mut satisfied_parents: Vec<usize> = Vec::new();
        let mut pos_resolve: Vec<usize> = Vec::new();
        let mut neg_resolve: Vec<usize> = Vec::new();
        let mut live_pos = 0usize;
        let mut live_neg = 0usize;
        let pos_pivot = Literal::positive(pivot_var);
        let neg_pivot = Literal::negative(pivot_var);
        for (occs, live, resolve_list) in [
            (pos_clause_indices, &mut live_pos, &mut pos_resolve),
            (neg_clause_indices, &mut live_neg, &mut neg_resolve),
        ] {
            for &idx in occs {
                // Occurrence lists can hold stale (garbage) entries from
                // lazy removal; resolving against a dead clause's stale
                // literals is unsound (its constraint may no longer be
                // implied by the current formula).
                if idx >= self.arena.len() || self.arena.is_dead(idx) {
                    continue;
                }
                *live += 1;
                let lits = self.arena.literals(idx);
                let mut has_pos_pivot = false;
                let mut has_neg_pivot = false;
                let mut satisfied = false;
                for &l in lits {
                    if l == pos_pivot {
                        has_pos_pivot = true;
                    } else if l == neg_pivot {
                        has_neg_pivot = true;
                    } else if self.vals.get(l.index()).copied().unwrap_or(0) > 0 {
                        satisfied = true;
                    }
                }
                // A clause with both pivot polarities is tautological in
                // the pivot: it is trivially true and contributes no
                // resolvents. Resolving it (the shader drops BOTH pivot
                // literals) would yield a stronger-than-justified clause —
                // the self-pair case even yields a spurious EMPTY resolvent
                // (false UNSAT). The CPU path guards the self-pair in
                // try_resolve_pair; excluding the clause entirely covers
                // cross-pairs as well. It is still deleted and witnessed
                // by finalize (an always-true clause never flips a
                // reconstruction witness).
                if has_pos_pivot && has_neg_pivot {
                    continue;
                }
                // Non-pivot tautologies skip every pair (CPU parity:
                // ResolveClauseProfile::tautological).
                let (_, tautological) =
                    BVE::resolve_clause_profile(lits, pivot_var, &self.vals, &mut self.lit_marks);
                if tautological {
                    continue;
                }
                // Root-satisfied parents produce no resolvents and must
                // NOT be pushed as reconstruction witnesses (#8356/#8397).
                if satisfied {
                    satisfied_parents.push(idx);
                    continue;
                }
                resolve_list.push(idx);
            }
        }

        // Pure variable after stale-entry filtering: trivially eliminable
        // (CPU parity: pos_count == 0 || neg_count == 0 early return).
        if live_pos == 0 || live_neg == 0 {
            return Some((true, Vec::new(), Vec::new(), Vec::new(), 0));
        }

        // Occurrence cap (CPU parity: kissat eliminateocclim on the sum).
        if live_pos + live_neg > ELIM_OCC_LIMIT {
            return Some((false, Vec::new(), Vec::new(), Vec::new(), 0));
        }

        let clauses_removed = live_pos + live_neg;
        let num_pairs = pos_resolve.len() * neg_resolve.len();

        // Global resolution-effort budget (CPU parity: the CPU path aborts
        // mid-variable once `remaining_budget` attempts are consumed and
        // reports the elimination as not-bounded).
        if num_pairs as u64 > remaining_budget {
            return Some((false, Vec::new(), Vec::new(), Vec::new(), remaining_budget));
        }

        // All pairs pre-filtered away (every parent tautological or
        // satisfied): no resolvents, trivially bounded.
        if num_pairs == 0 {
            return Some((true, Vec::new(), Vec::new(), satisfied_parents, 0));
        }

        let gpu_results = {
            let arena = &self.arena;
            let vals = &self.vals;
            let (context, pipeline) = self.inproc.gpu_bve()?;
            pipeline
                .dispatch_resolve(context, pivot_var, &pos_resolve, &neg_resolve, arena, vals)
                .ok()?
        };

        let num_attempts = gpu_results.len() as u64;
        let mut resolvents: Vec<(Vec<Literal>, usize, usize, Vec<usize>)> = Vec::new();
        let mut strengthened: Vec<crate::bve::ClauseStrengthening> = Vec::new();
        let mut strengthened_idx: DetHashMap<usize, usize> = DetHashMap::default();
        let mut tautologies_skipped: u64 = 0;
        let budget = self.inproc.bve.resolvent_budget(clauses_removed);

        for gpu_resolvent in gpu_results {
            if gpu_resolvent.is_tautology {
                tautologies_skipped += 1;
                continue;
            }

            let pos_arena_idx = pos_resolve[gpu_resolvent.pos_idx];
            let neg_arena_idx = neg_resolve[gpu_resolvent.neg_idx];
            // Self-resolution pairs are excluded by the pivot-tautology
            // filter above (a clause in both lists contains both pivot
            // polarities); skip defensively like the CPU path.
            debug_assert_ne!(
                pos_arena_idx, neg_arena_idx,
                "BUG: GPU BVE self-resolution pair survived filtering",
            );
            if pos_arena_idx == neg_arena_idx {
                continue;
            }
            let resolvent = gpu_resolvent.literals;

            // Compute pruned_vars: root-level-false variables from both
            // parents that were pruned by the GPU shader (needed for LRAT
            // hints, including the empty-resolvent chain).
            let pruned_vars = if self.cold.lrat_enabled {
                let mut pruned = Vec::new();
                for &lit in self
                    .arena
                    .literals(pos_arena_idx)
                    .iter()
                    .chain(self.arena.literals(neg_arena_idx).iter())
                {
                    if lit.variable() == pivot_var {
                        continue;
                    }
                    let v = self.vals.get(lit.index()).copied().unwrap_or(0);
                    if v < 0 && !pruned.contains(&lit.variable().index()) {
                        pruned.push(lit.variable().index());
                    }
                }
                pruned
            } else {
                Vec::new()
            };

            // Empty resolvent signals UNSAT.
            if resolvent.is_empty() {
                resolvents.push((resolvent, pos_arena_idx, neg_arena_idx, pruned_vars));
                // Update stats and return immediately.
                self.stats.gpu_bve_dispatches += 1;
                self.stats.gpu_bve_pairs += num_attempts;
                self.stats.gpu_bve_tautologies += tautologies_skipped;
                return Some((
                    true,
                    resolvents,
                    strengthened,
                    satisfied_parents,
                    num_attempts,
                ));
            }

            // Enforce per-resolvent clause size limit (CaDiCaL elimclslim).
            // This check is also what makes the shader's silent truncation
            // at GPU_MAX_RESOLVENT_LEN (128 > limit) sound: a truncated
            // resolvent always reports a saturated length above the limit.
            if resolvent.len() > ELIM_CLAUSE_SIZE_LIMIT {
                // A resolvent exceeds the size limit: reject elimination.
                self.stats.gpu_bve_dispatches += 1;
                self.stats.gpu_bve_pairs += num_attempts;
                self.stats.gpu_bve_tautologies += tautologies_skipped;
                return Some((false, Vec::new(), Vec::new(), Vec::new(), num_attempts));
            }

            // CPU-side OTFS (on-the-fly self-subsuming resolution):
            // Check if the resolvent subsumes either parent clause.
            // This is the same logic as eliminate.rs:try_resolve_pair.
            let pos_lits = self.arena.literals(pos_arena_idx);
            let neg_lits = self.arena.literals(neg_arena_idx);

            // Build resolvent signature and mark for subset checking.
            let mut resolvent_signature = 0u64;
            for &lit in &resolvent {
                self.lit_marks.mark(lit);
                resolvent_signature |= clause_signature_bit(lit);
            }

            // Compute parent signatures (excluding pivot).
            let mut pos_signature = 0u64;
            for &lit in pos_lits {
                if lit.variable() != pivot_var {
                    pos_signature |= clause_signature_bit(lit);
                }
            }
            let mut neg_signature = 0u64;
            for &lit in neg_lits {
                if lit.variable() != pivot_var {
                    neg_signature |= clause_signature_bit(lit);
                }
            }

            let subsumes_pos = resolvent.len() < pos_lits.len()
                && clause_signature_may_subsume(resolvent_signature, pos_signature)
                && pos_lits.iter().all(|lit| {
                    lit.variable() == pivot_var || self.lit_marks.get(lit.variable()) != 0
                });
            let subsumes_neg = resolvent.len() < neg_lits.len()
                && clause_signature_may_subsume(resolvent_signature, neg_signature)
                && neg_lits.iter().all(|lit| {
                    lit.variable() == pivot_var || self.lit_marks.get(lit.variable()) != 0
                });

            self.lit_marks.clear_clause(&resolvent);

            if subsumes_pos || subsumes_neg {
                // Self-subsuming resolution: strengthen the subsumed parent
                // (double OTFS strengthens the positive parent, matching the
                // CPU path). The resolvent itself is NOT added.
                let (target_idx, target_lits) = if subsumes_pos {
                    (pos_arena_idx, pos_lits)
                } else {
                    (neg_arena_idx, neg_lits)
                };
                let (new_lits, _) =
                    BVE::parent_without_pivot_and_false(target_lits, pivot_var, &self.vals);
                if !new_lits.is_empty() {
                    // Dedup per parent clause, keeping the shortest
                    // strengthening (CPU parity: record_strengthening).
                    if let Some(&slot) = strengthened_idx.get(&target_idx) {
                        if new_lits.len() < strengthened[slot].new_lits.len() {
                            strengthened[slot].new_lits = new_lits;
                            strengthened[slot].pos_ante = pos_arena_idx;
                            strengthened[slot].neg_ante = neg_arena_idx;
                            strengthened[slot].pruned_vars = pruned_vars;
                        }
                    } else {
                        strengthened_idx.insert(target_idx, strengthened.len());
                        strengthened.push(crate::bve::ClauseStrengthening {
                            clause_idx: target_idx,
                            new_lits,
                            pos_ante: pos_arena_idx,
                            neg_ante: neg_arena_idx,
                            pruned_vars,
                        });
                    }
                }
            } else {
                // No self-subsumption: add resolvent normally.
                let is_unit = resolvent.len() == 1;
                resolvents.push((resolvent, pos_arena_idx, neg_arena_idx, pruned_vars));

                // Unit resolvents skip the in-loop bound check (CPU parity:
                // try_resolve_pair returns before the clause-count check).
                if is_unit {
                    continue;
                }

                // Budget check: reject if resolvents exceed the bound.
                if resolvents.len() > budget {
                    self.stats.gpu_bve_dispatches += 1;
                    self.stats.gpu_bve_pairs += num_attempts;
                    self.stats.gpu_bve_tautologies += tautologies_skipped;
                    return Some((false, Vec::new(), Vec::new(), Vec::new(), num_attempts));
                }
            }
        }

        // Final clause-count bound check.
        let bounded = resolvents.len() <= budget;

        self.stats.gpu_bve_dispatches += 1;
        self.stats.gpu_bve_pairs += num_attempts;
        self.stats.gpu_bve_tautologies += tautologies_skipped;

        if bounded {
            Some((
                true,
                resolvents,
                strengthened,
                satisfied_parents,
                num_attempts,
            ))
        } else {
            Some((false, Vec::new(), Vec::new(), Vec::new(), num_attempts))
        }
    }
}
