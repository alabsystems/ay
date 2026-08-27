// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backward subsumption for BVE resolvents.
//!
//! After variable elimination produces new resolvents, check if any of them
//! subsume or self-subsume existing (longer or equal-size) clauses. This is
//! CaDiCaL's "eager backward subsumption" from `backward.cpp`.
//!
//! Three outcomes per resolvent R vs candidate C:
//! 1. **Subsumption**: R ⊆ C → delete C
//! 2. **Self-subsumption**: R \ {l} ⊆ C and ¬l ∈ C → strengthen C by removing ¬l
//! 3. **Hyper-unary resolution**: complementary pair (a ∨ b) and (a ∨ ¬b) → derive unit a
//!
//! Reference: `reference/cadical/src/backward.cpp` (253 lines)

use super::BVE;
use crate::clause::{clause_signature_vars_subset, compute_clause_signature};
use crate::clause_arena::ClauseArena;
use crate::kani_compat::DetHashSet as HashSet;
use crate::lit_marks::LitMarks;
use crate::literal::Literal;

/// Maximum occurrence list size for the "best" literal. This uses AY's
/// Kissat-style 2000 occurrence guard from `ELIM_OCC_LIMIT`; CaDiCaL's
/// `elimocclim` default is 100 per polarity.
const BACKWARD_OCC_LIMIT: usize = 2_000;

/// Maximum occurrence list size for the removed literal in backward
/// self-subsumption strengthening. CaDiCaL backward.cpp:196 checks
/// `occs(negated).size() <= opts.elimocclim` (default 100) before applying
/// strengthening. Without this guard, strengthening can remove a literal
/// from a clause, taking it out of a not-yet-eliminated variable's occ list.
/// When that variable is later eliminated, the clause is missing from the
/// extension stack, and reconstruction produces an invalid model (#8482).
const BACKWARD_STRENGTHEN_OCC_LIMIT: usize = 100;

/// Result of backward subsumption over a batch of new resolvents.
#[derive(Debug, Clone, Default)]
pub(crate) struct BackwardSubsumptionResult {
    /// Clause indices that are subsumed and should be deleted.
    pub subsumed: Vec<usize>,
    /// (clause_idx, literal_to_remove): clauses to be strengthened via
    /// self-subsumption. The caller removes the negated literal from the clause.
    pub strengthened: Vec<(usize, Literal)>,
    /// Unit literals derived from hyper-unary resolution.
    pub units: Vec<Literal>,
    /// Clause indices discovered to be satisfied at root level during backward
    /// subsumption scanning. CaDiCaL backward.cpp:107-110 marks these as garbage
    /// immediately. Collecting them separately avoids mixing subsumption results
    /// with satisfied-clause cleanup (#8007).
    pub satisfied: Vec<usize>,
    /// Number of candidate clauses checked (for diagnostics).
    pub checks: u64,
}

impl BVE {
    /// Run backward subsumption and strengthening for a batch of newly-added
    /// resolvent clause indices.
    ///
    /// CaDiCaL `elim_backward_clauses` (backward.cpp:215-227): dequeue each
    /// new resolvent and attempt backward subsumption/strengthening against
    /// existing clauses via occurrence lists.
    ///
    /// REQUIRES: occurrence lists are up-to-date (resolvents already added)
    /// REQUIRES: `marks` is clean (all zeros) on entry
    /// ENSURES: `marks` is clean on return
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn backward_subsume_resolvents(
        &mut self,
        clauses: &ClauseArena,
        new_resolvent_indices: &[usize],
        marks: &mut LitMarks,
        vals: &[i8],
    ) -> BackwardSubsumptionResult {
        let mut result = BackwardSubsumptionResult::default();

        // Build a set of source resolvent indices so backward_subsume_one
        // can skip candidates that are themselves sources. Without this,
        // two identical resolvents (produced by redundant resolution paths)
        // subsume each other in the batched scan, and BOTH get deleted,
        // removing the constraint entirely. CaDiCaL avoids this by
        // processing sequentially with immediate mark_garbage, so a
        // subsumed clause is invisible to later scans. AY's batched
        // approach requires explicit source-set filtering.
        let source_set: HashSet<usize> = new_resolvent_indices.iter().copied().collect();

        // Track clauses already subsumed/satisfied in prior iterations of
        // this batch (#8382, #8448). CaDiCaL processes resolvents
        // sequentially and immediately marks subsumed clauses as garbage,
        // making them invisible to subsequent resolvent scans. AY's batched
        // approach must explicitly track these to prevent ordering bugs:
        //   R1 subsumes clause C → C added to `already_dead`
        //   R2 attempts hyper-unary resolution using C → C is in
        //   `already_dead`, so R2 skips it
        // Without this, R2 could derive a unit from a clause that no longer
        // exists, causing an unsound deduction (false UNSAT on ecarev-110).
        let mut already_dead: HashSet<usize> = HashSet::default();

        for &r_idx in new_resolvent_indices {
            if r_idx >= clauses.len() || clauses.is_dead(r_idx) {
                continue;
            }
            if already_dead.contains(&r_idx) {
                continue;
            }
            let prev_subsumed = result.subsumed.len();
            let prev_satisfied = result.satisfied.len();
            self.backward_subsume_one(
                clauses,
                r_idx,
                marks,
                vals,
                &mut result,
                &source_set,
                &already_dead,
            );

            // Register newly subsumed/satisfied clauses as dead so
            // subsequent resolvents skip them.
            for &idx in &result.subsumed[prev_subsumed..] {
                already_dead.insert(idx);
            }
            for &idx in &result.satisfied[prev_satisfied..] {
                already_dead.insert(idx);
            }

            // If a unit was derived, stop processing (CaDiCaL backward.cpp:194-195).
            if !result.units.is_empty() {
                break;
            }
        }

        result
    }

    /// Process backward subsumption for a single resolvent, returning a fresh
    /// result. This is the sequential per-resolvent entry point used by the
    /// corrected backward subsumption loop (#8448).
    ///
    /// Unlike `backward_subsume_resolvents` (batched), this returns results for
    /// one resolvent only. The caller applies mutations immediately before
    /// processing the next resolvent, ensuring correct proof ordering:
    /// - Deletions are visible in the proof stream before dependent derivations
    /// - Strengthened clauses can be re-enqueued for cascade processing
    /// - Units reference clauses that are still alive in the proof
    ///
    /// CaDiCaL `elim_backward_clause` (backward.cpp:40-211).
    pub(crate) fn backward_subsume_one_sequential(
        &mut self,
        clauses: &ClauseArena,
        r_idx: usize,
        marks: &mut LitMarks,
        vals: &[i8],
        source_set: &HashSet<usize>,
    ) -> BackwardSubsumptionResult {
        let mut result = BackwardSubsumptionResult::default();
        let empty_dead = HashSet::default();
        self.backward_subsume_one(
            clauses,
            r_idx,
            marks,
            vals,
            &mut result,
            source_set,
            &empty_dead,
        );
        result
    }

    /// Attempt backward subsumption and strengthening with one resolvent.
    ///
    /// CaDiCaL `elim_backward_clause` (backward.cpp:40-211).
    ///
    /// `already_dead` contains clause indices subsumed or satisfied by
    /// earlier resolvents in the same batch. These clauses are logically
    /// deleted even though the arena hasn't been mutated yet. Skipping them
    /// prevents ordering-dependent unsoundness (#8382, #8448).
    fn backward_subsume_one(
        &mut self,
        clauses: &ClauseArena,
        r_idx: usize,
        marks: &mut LitMarks,
        vals: &[i8],
        result: &mut BackwardSubsumptionResult,
        source_set: &HashSet<usize>,
        already_dead: &HashSet<usize>,
    ) {
        let r_lits = clauses.literals(r_idx);

        // Find the literal in R with the smallest occurrence count.
        // Skip root-level-assigned literals (CaDiCaL backward.cpp:57-58).
        // Also compute a 64-bit signature for R's active literals to use as
        // a bloom-style pre-filter against candidate clauses (#7922).
        let mut best_lit: Option<Literal> = None;
        let mut best_occ_count = usize::MAX;
        let mut active_size: u32 = 0;
        let mut r_active_lits: Vec<Literal> = Vec::with_capacity(r_lits.len());

        for &lit in r_lits {
            let v = vals.get(lit.index()).copied().unwrap_or(0);
            if v > 0 {
                // CaDiCaL backward.cpp:67-69: clause is satisfied at root
                // level. Mark it for deletion — it contributes to clause DB
                // bloat if left alive. Clean up any marks already set.
                self.unmark_clause(r_lits, marks);
                result.satisfied.push(r_idx);
                return;
            }
            if v < 0 {
                // Root-level-false literal: skip it.
                continue;
            }
            marks.mark(lit);
            active_size += 1;
            r_active_lits.push(lit);

            let occ_count = self.occ.count(lit);
            if occ_count < best_occ_count {
                best_occ_count = occ_count;
                best_lit = Some(lit);
            }
        }
        // 64-bit signature of R's active (non-root-false) literals.
        // For D to be subsumed or strengthened by R, all of R's variables must
        // appear in D (possibly with one opposite polarity for strengthening).
        // clause_signature_vars_subset provides a sound negative filter (#7922).
        let r_sig = compute_clause_signature(&r_active_lits);

        if active_size == 0 {
            // All literals are root-level-false; this is effectively an empty clause.
            self.unmark_clause(r_lits, marks);
            return;
        }

        // CaDiCaL backward.cpp:70: skip if too many occurrences.
        if best_occ_count > BACKWARD_OCC_LIMIT {
            self.unmark_clause(r_lits, marks);
            return;
        }

        let best = match best_lit {
            Some(l) => l,
            None => {
                self.unmark_clause(r_lits, marks);
                return;
            }
        };

        // Scan the occurrence list of the literal with the fewest occurrences.
        // Copy to avoid borrow conflict with self.occ.
        let occ_snapshot: Vec<usize> = self.occ.get(best).to_vec();

        for &d_idx in &occ_snapshot {
            if d_idx == r_idx {
                continue;
            }
            // Skip candidates that are also source resolvents. In
            // CaDiCaL's sequential processing, a source resolvent that
            // was subsumed by an earlier source is immediately marked
            // garbage and invisible to later scans. In AY's batched
            // approach, two identical resolvents can subsume each other,
            // causing both to be deleted and removing the constraint.
            // Skipping source resolvents as candidates prevents this
            // mutual-subsumption bug while preserving the ability for
            // resolvents to subsume non-source (existing) clauses.
            if source_set.contains(&d_idx) {
                continue;
            }
            if d_idx >= clauses.len() || clauses.is_dead(d_idx) {
                continue;
            }
            // Skip clauses subsumed or satisfied by earlier resolvents
            // in this batch (#8382, #8448). Prevents hyper-unary
            // resolution from deriving units that depend on logically
            // deleted clauses.
            if already_dead.contains(&d_idx) {
                continue;
            }
            // C must be at least as large as R's active literals to be subsumable.
            let d_lits = clauses.literals(d_idx);
            if (d_lits.len() as u32) < active_size {
                continue;
            }

            // 64-bit signature pre-filter (#7922): R's variables must be a
            // subset of D's variables (ignoring polarity) for subsumption or
            // self-subsumption. Recomputed from D's literals now that the
            // always-on arena signature side table is retired: the recompute
            // is a branch-free OR sweep over the contiguous literal words of
            // `d_lits` (already resident from the length check above), where
            // the old path was a guaranteed-cold probe into a table spanning
            // hundreds of MB. It still pays for itself against the
            // mark-array scan below (random access into a num_vars-sized
            // array per literal), and the filter decision — hence
            // `checks`/`backward_sig_filtered` — is identical: the side
            // table was maintained on every add/replace, so it too always
            // reflected D's current literals.
            let d_sig = compute_clause_signature(d_lits);
            if !clause_signature_vars_subset(r_sig, d_sig) {
                self.stats.backward_sig_filtered += 1;
                continue;
            }

            result.checks += 1;

            // Count how many of R's active literals appear in C, tracking
            // whether exactly one appears negated (self-subsumption case).
            let mut found: u32 = 0;
            let mut negated_lit: Option<Literal> = None;
            let mut satisfied = false;
            let mut double_negated = false;

            for &lit in d_lits {
                let v = vals.get(lit.index()).copied().unwrap_or(0);
                if v > 0 {
                    // Candidate clause is satisfied at root level.
                    satisfied = true;
                    break;
                }
                if v < 0 {
                    // Root-level-false literal: not an active literal in C.
                    continue;
                }

                let mark = marks.get(lit.variable());
                if mark == 0 {
                    // Not in R — irrelevant.
                    continue;
                }
                if mark == lit.sign_i8() {
                    // Same polarity match.
                    found += 1;
                } else {
                    // Opposite polarity: potential self-subsumption.
                    if negated_lit.is_some() {
                        // Two negated literals: can't be subsumption or
                        // self-subsumption. CaDiCaL backward.cpp:98-99.
                        double_negated = true;
                        break;
                    }
                    negated_lit = Some(lit);
                    found += 1;
                }

                if found == active_size {
                    break;
                }
            }

            if satisfied {
                // CaDiCaL backward.cpp:107-110: candidate clause is satisfied
                // at root level. Collect it for deletion to prevent clause DB
                // bloat (#8007).
                result.satisfied.push(d_idx);
                continue;
            }
            if double_negated {
                continue;
            }

            if found < active_size {
                continue;
            }

            // All active_size literals of R matched in C.
            if let Some(neg_lit) = negated_lit {
                // Self-subsumption: R \ {l} ⊆ C and ¬l ∈ C.
                // Re-scan D to: (a) detect if D is satisfied (any literal
                // true at root), and (b) count active (unassigned) literals.
                // The outer scan loop above may have exited early at
                // `found == active_size` without visiting all of D's
                // literals. CaDiCaL backward.cpp:124-148 does this re-scan
                // explicitly, checking `val(lit) > 0 => satisfied` for every
                // literal before deciding unit vs strengthen (#8477).
                let mut d_satisfied = false;
                let mut d_active: u32 = 0;
                for &lit in d_lits {
                    let v = vals.get(lit.index()).copied().unwrap_or(0);
                    if v > 0 {
                        // Literal is true -> D is satisfied at root level.
                        // CaDiCaL backward.cpp:137-139.
                        d_satisfied = true;
                        break;
                    }
                    if v == 0 {
                        d_active += 1;
                    }
                }

                if d_satisfied {
                    // D is root-satisfied. CaDiCaL backward.cpp:107-110
                    // marks it as garbage immediately. Collect it for the
                    // caller to delete (#8007).
                    result.satisfied.push(d_idx);
                    continue;
                }

                if d_active == active_size {
                    // C has exactly the same number of active literals as R.
                    // CaDiCaL backward.cpp:119-148: figure out whether we
                    // strengthen C or derive a new unit. Count unassigned
                    // literals in C excluding the negated literal.
                    let mut unit_lit: Option<Literal> = None;
                    let mut non_neg_active_count = 0u32;
                    for &lit in d_lits {
                        let v = vals.get(lit.index()).copied().unwrap_or(0);
                        if v != 0 {
                            continue;
                        }
                        if lit == neg_lit {
                            continue;
                        }
                        non_neg_active_count += 1;
                        unit_lit = Some(lit);
                    }

                    if non_neg_active_count == 1 {
                        // Hyper-unary resolution: derive the unit.
                        if let Some(u) = unit_lit {
                            result.units.push(u);
                            self.stats.backward_units += 1;
                            break; // CaDiCaL: stop after first unit
                        }
                    } else {
                        // Strengthen: remove the negated literal from C.
                        // Guard: CaDiCaL backward.cpp:196 — skip if the
                        // negated literal's occurrence list is too large.
                        // Without this, strengthening can remove a literal
                        // from a clause that hasn't been added to a
                        // not-yet-eliminated variable's extension stack,
                        // corrupting BVE reconstruction (#8482).
                        if self.occ.count(neg_lit) <= BACKWARD_STRENGTHEN_OCC_LIMIT {
                            result.strengthened.push((d_idx, neg_lit));
                            self.stats.backward_strengthened += 1;
                        }
                    }
                } else {
                    // C has more active literals than R. Strengthen C.
                    // Same occ-limit guard as above (#8482).
                    if self.occ.count(neg_lit) <= BACKWARD_STRENGTHEN_OCC_LIMIT {
                        result.strengthened.push((d_idx, neg_lit));
                        self.stats.backward_strengthened += 1;
                    }
                }
            } else {
                // Pure subsumption: R ⊆ C. Delete C.
                debug_assert!(
                    active_size <= d_lits.len() as u32,
                    "BUG: backward subsumption: R has more active literals than C"
                );
                result.subsumed.push(d_idx);
                self.stats.backward_subsumed += 1;
            }
        }

        // Clean up marks.
        self.unmark_clause(r_lits, marks);
    }

    /// Clear marks set for a clause's literals.
    #[inline]
    fn unmark_clause(&self, lits: &[Literal], marks: &mut LitMarks) {
        marks.clear_clause(lits);
    }
}
