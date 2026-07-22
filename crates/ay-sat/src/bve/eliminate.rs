// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BVE elimination: resolution, gate-aware elimination, and candidate filtering.

use super::{
    EliminationResult, ResolveAcc, ResolveClauseProfile, ResolveOutcome, WitnessEntry, BVE,
    ELIM_CLAUSE_SIZE_LIMIT,
};
use crate::clause::{
    clause_signature_bit, clause_signature_may_subsume,
    clause_signatures_may_resolve_tautologically,
};
use crate::clause_arena::ClauseArena;
#[cfg(test)]
use crate::elim_heap::ElimHeap;
use crate::kani_compat::DetHashSet as HashSet;
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};

impl BVE {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn try_resolve_pair(
        &mut self,
        var: Variable,
        clauses: &ClauseArena,
        pos: ResolveClauseProfile,
        neg: ResolveClauseProfile,
        marks: &mut LitMarks,
        vals: &[i8],
        acc: &mut ResolveAcc<'_>,
    ) -> bool {
        let pos_idx = pos.clause_idx;
        let neg_idx = neg.clause_idx;
        // CaDiCaL elim.cpp: variable must not already be eliminated
        debug_assert!(
            !self.eliminated[var.index()],
            "BUG: try_resolve_pair on eliminated variable {var:?}",
        );
        // Skip self-resolution: a tautological clause like (x ∨ ¬x) appears
        // in both positive and negative occurrence lists, so resolving it with
        // itself would remove the pivot pair and produce a spurious empty
        // resolvent, falsely signaling UNSAT.
        if pos_idx == neg_idx {
            return true;
        }
        if pos_idx >= clauses.len() || clauses.is_dead(pos_idx) {
            return true;
        }
        if neg_idx >= clauses.len() || clauses.is_dead(neg_idx) {
            return true;
        }

        let pos_lits = clauses.literals(pos_idx);
        let neg_lits = clauses.literals(neg_idx);
        let pos_pivot = Literal::positive(var);
        let neg_pivot = Literal::negative(var);

        debug_assert!(
            pos_lits.contains(&pos_pivot),
            "BUG: clause {pos_idx} from positive occurrence list for {var:?} is missing {pos_pivot:?}"
        );
        debug_assert!(
            neg_lits.contains(&neg_pivot),
            "BUG: clause {neg_idx} from negative occurrence list for {var:?} is missing {neg_pivot:?}"
        );

        if pos.tautological || neg.tautological {
            self.stats.tautologies_skipped += 1;
            return true;
        }

        // Signature-based resolvent size pre-filter (#7922): the union of two
        // clause signatures (pivot excluded during profile computation) gives a
        // lower bound on distinct resolvent variables. If this lower bound
        // exceeds ELIM_CLAUSE_SIZE_LIMIT, the resolvent is guaranteed too large.
        let combined_sig = pos.signature | neg.signature;
        if combined_sig.count_ones() as usize > ELIM_CLAUSE_SIZE_LIMIT {
            return true;
        }

        let outcome = if clause_signatures_may_resolve_tautologically(pos.signature, neg.signature)
        {
            self.resolve_with_marks(pos_lits, neg_lits, var, marks, vals)
        } else {
            self.stats.sig_fast_path += 1;
            self.resolve_without_tautology_checks(pos_lits, neg_lits, var, marks, vals)
        };

        match outcome {
            ResolveOutcome::Tautology => {
                return true;
            }
            ResolveOutcome::ParentSatisfied(first_parent) => {
                // CaDiCaL elim.cpp:316-325: mark satisfied parent as garbage.
                let satisfied_idx = if first_parent { pos_idx } else { neg_idx };
                acc.satisfied_parents.push(satisfied_idx);
                return true;
            }
            ResolveOutcome::Resolvent(resolvent, pruned_vars) => {
                if resolvent.is_empty() {
                    acc.resolvents
                        .push((resolvent, pos_idx, neg_idx, pruned_vars));
                    *acc.found_empty_resolvent = true;
                    return true;
                }

                // NOTE: CaDiCaL does NOT forward-subsume resolvents during
                // BVE resolution (elim.cpp:264-460). A subsuming clause D
                // may be deleted in a later variable elimination within the
                // same BVE round, making the dropped resolvent needed. The
                // resolvent must be kept unconditionally. Forward subsumption
                // is a separate inprocessing pass that runs between BVE rounds,
                // where it is safe because no concurrent deletions occur.

                // CaDiCaL elim.cpp:396-403: unit resolvents are assigned
                // immediately and not counted toward the elimination bound.
                // The solver propagates them after the elimination round,
                // allowing subsequent variables to see a cleaner formula.
                if resolvent.len() == 1 {
                    acc.resolvents
                        .push((resolvent, pos_idx, neg_idx, pruned_vars));
                    return true;
                }

                // CaDiCaL elim.cpp:509: reject if any resolvent exceeds elimclslim.
                if resolvent.len() > ELIM_CLAUSE_SIZE_LIMIT {
                    return false;
                }

                // CaDiCaL elim.cpp:409-447: self-subsuming resolution.
                // Check if the resolvent subsumes either (or both) parent clauses.
                // Use the 64-bit signature as a sound negative filter before the
                // O(r+p) mark scan to avoid work on obviously impossible cases.
                // Marks still replace the old O(r×p) Vec::contains path (#5075).
                let mut resolvent_signature = 0;
                for &lit in &resolvent {
                    marks.mark(lit);
                    resolvent_signature |= clause_signature_bit(lit);
                }
                let subsumes_pos = resolvent.len() < pos_lits.len()
                    && clause_signature_may_subsume(resolvent_signature, pos.signature)
                    && pos_lits
                        .iter()
                        .all(|lit| lit.variable() == var || marks.get(lit.variable()) != 0);
                let subsumes_neg = resolvent.len() < neg_lits.len()
                    && clause_signature_may_subsume(resolvent_signature, neg.signature)
                    && neg_lits
                        .iter()
                        .all(|lit| lit.variable() == var || marks.get(lit.variable()) != 0);
                marks.clear_clause(&resolvent);

                if subsumes_pos && subsumes_neg {
                    // CaDiCaL elim.cpp:413-424: Double self-subsuming resolution.
                    // The two antecedents are identical except for the pivot polarity.
                    // Strengthen one parent (remove pivot + root-level-false lits),
                    // garbage-collect the other. The resolvent is NOT added.
                    // CaDiCaL elim.cpp:215-223: also prune root-level-false lits.
                    let (new_lits, otfs_pruned) =
                        Self::parent_without_pivot_and_false(pos_lits, var, vals);
                    // Merge root-level-false vars from both antecedents (resolution)
                    // with those from the parent itself for complete LRAT hints.
                    let mut all_pruned = pruned_vars;
                    for vi in otfs_pruned {
                        if !all_pruned.contains(&vi) {
                            all_pruned.push(vi);
                        }
                    }
                    if !new_lits.is_empty() {
                        Self::record_strengthening(
                            acc, pos_idx, new_lits, pos_idx, neg_idx, all_pruned,
                        );
                    }
                    self.stats.double_otfs += 1;
                    // neg_idx is NOT strengthened — it stays in to_delete and the
                    // driver garbage-collects it. This removes one redundant clause.
                } else if subsumes_pos {
                    // CaDiCaL elim.cpp:431-437: Single self-subsuming resolution
                    // on the positive parent. Remove pivot + root-level-false lits.
                    let (new_lits, otfs_pruned) =
                        Self::parent_without_pivot_and_false(pos_lits, var, vals);
                    let mut all_pruned = pruned_vars;
                    for vi in otfs_pruned {
                        if !all_pruned.contains(&vi) {
                            all_pruned.push(vi);
                        }
                    }
                    if !new_lits.is_empty() {
                        Self::record_strengthening(
                            acc, pos_idx, new_lits, pos_idx, neg_idx, all_pruned,
                        );
                    }
                    self.stats.single_otfs += 1;
                    // Resolvent NOT added.
                } else if subsumes_neg {
                    // CaDiCaL elim.cpp:441-447: Single self-subsuming resolution
                    // on the negative parent. Remove pivot + root-level-false lits.
                    let (new_lits, otfs_pruned) =
                        Self::parent_without_pivot_and_false(neg_lits, var, vals);
                    let mut all_pruned = pruned_vars;
                    for vi in otfs_pruned {
                        if !all_pruned.contains(&vi) {
                            all_pruned.push(vi);
                        }
                    }
                    if !new_lits.is_empty() {
                        Self::record_strengthening(
                            acc, neg_idx, new_lits, pos_idx, neg_idx, all_pruned,
                        );
                    }
                    self.stats.single_otfs += 1;
                    // Resolvent NOT added.
                } else {
                    // No self-subsumption: add resolvent normally.
                    let rlen = resolvent.len() as u64;
                    self.stats.total_resolvent_literals += rlen;
                    self.stats.non_unit_resolvents += 1;
                    if rlen > self.stats.max_resolvent_len {
                        self.stats.max_resolvent_len = rlen;
                    }
                    acc.resolvents
                        .push((resolvent, pos_idx, neg_idx, pruned_vars));
                }

                // CaDiCaL fastelim product shortcut: skip clause-count check when
                // the product of occurrence counts guarantees we're within budget.
                if !acc.clause_count_guaranteed
                    && acc.resolvents.len() > self.resolvent_budget(acc.clauses_removed)
                {
                    return false;
                }
            }
        }

        true
    }

    /// Find the best variable to eliminate (linear scan).
    ///
    /// Returns None if no suitable variable is found.
    /// The `frozen` slice contains reference counts - a variable is frozen if its count > 0.
    ///
    /// Note: production uses `next_candidate()` (priority queue) for better
    /// ordering. This linear scan is used by unit tests for simpler setup.
    #[cfg(test)]
    pub(super) fn find_elimination_candidate(
        &self,
        vals: &[i8],
        frozen: &[u32],
    ) -> Option<Variable> {
        let mut best_var: Option<Variable> = None;
        let mut best_score = u64::MAX;

        for var_idx in 0..self.num_vars {
            let Some((var, _, _)) = self.candidate_occurrence_counts(var_idx, vals, frozen) else {
                continue;
            };

            // Gate-defined variables receive a credit that approximates the
            // gate×gate pairs skipped by restricted resolution.
            let score = ElimHeap::elim_score(var, &self.occ, &self.schedule_gate_pair_credit);

            if score < best_score {
                best_score = score;
                best_var = Some(var);
            }
        }

        best_var
    }

    /// Try to eliminate a specific variable.
    ///
    /// Convenience wrapper around `try_eliminate_with_gate_with_marks` that
    /// allocates fresh temporaries. Production code reuses marks/vals buffers
    /// via `try_eliminate_with_gate_with_marks` directly.
    #[cfg(test)]
    pub(crate) fn try_eliminate(
        &mut self,
        var: Variable,
        clauses: &ClauseArena,
    ) -> EliminationResult {
        self.try_eliminate_with_gate(var, clauses, None, false)
    }

    /// Try to eliminate a specific variable, optionally using restricted
    /// resolution if `gate_defining_clauses` is provided.
    ///
    /// Convenience wrapper that allocates fresh `LitMarks` and empty `vals`.
    /// Production code reuses shared buffers via `try_eliminate_with_gate_with_marks`.
    #[cfg(test)]
    pub(crate) fn try_eliminate_with_gate(
        &mut self,
        var: Variable,
        clauses: &ClauseArena,
        gate_defining_clauses: Option<&[usize]>,
        resolve_gate_pairs: bool,
    ) -> EliminationResult {
        let mut marks = LitMarks::new(self.num_vars);
        let empty_vals: Vec<i8> = vec![0; self.num_vars * 2];
        self.try_eliminate_with_gate_with_marks(
            var,
            clauses,
            gate_defining_clauses,
            resolve_gate_pairs,
            &mut marks,
            &empty_vals,
            u64::MAX, // unlimited budget for tests
        )
    }

    /// Try to eliminate a specific variable using shared marks, optionally with
    /// restricted resolution if `gate_defining_clauses` is provided.
    ///
    /// `vals` is the literal-indexed value array from the solver. At level 0,
    /// `vals[lit.index()] > 0` means the literal is root-level-true.
    ///
    /// `remaining_budget` is the number of resolution attempts remaining in the
    /// global BVE effort budget. Resolution exits early if this is exceeded,
    /// implementing CaDiCaL's incremental effort charging (#8195).
    pub(crate) fn try_eliminate_with_gate_with_marks(
        &mut self,
        var: Variable,
        clauses: &ClauseArena,
        gate_defining_clauses: Option<&[usize]>,
        resolve_gate_pairs: bool,
        marks: &mut LitMarks,
        vals: &[i8],
        remaining_budget: u64,
    ) -> EliminationResult {
        let var_idx = var.index();

        // CaDiCaL elim.cpp:698: variable index must be within bounds
        debug_assert!(
            var_idx < self.num_vars,
            "BUG: try_eliminate_with_gate var {var:?} index {var_idx} >= num_vars {}",
            self.num_vars,
        );
        // CaDiCaL elim.cpp:700: gate defining clauses must reference valid indices
        debug_assert!(
            gate_defining_clauses
                .map(|g| g.iter().all(|&idx| idx < clauses.len()))
                .unwrap_or(true),
            "BUG: gate_defining_clauses contains index >= clauses.len() {}",
            clauses.len(),
        );
        debug_assert!(
            gate_defining_clauses.is_some() || !resolve_gate_pairs,
            "BUG: resolve_gate_pairs requires gate_defining_clauses"
        );

        // Check if already eliminated
        if var_idx < self.eliminated.len() && self.eliminated[var_idx] {
            return EliminationResult::not_eliminated(var);
        }

        // SOUNDNESS GUARD (pure-gate clamp, inc1). Gate-restricted elimination
        // both (a) skips non-gate × non-gate resolvent pairs and (b) pushes ONLY
        // the gate-defining clauses as reconstruction witnesses (#8482). Both are
        // unsound when the gate does not COMPLETELY define `x`: a deleted,
        // non-witnessed non-gate clause `(¬x ∨ C)` can be falsified when model
        // reconstruction flips the pivot per the gate, even though the simplified
        // DB stayed equisatisfiable (the braun/barrel FINALIZE_SAT_FAIL). AY
        // extracts gates without `elim_propagate`, so structural completeness
        // checks are unreliable. Conservative, provably-correct rule
        // (`gate_restriction_is_sound`): use gate restriction ONLY for pure-gate
        // variables (every live clause with the pivot IS a gate clause);
        // otherwise nullify the gate and fall back to FULL resolution + full
        // witnessing, which is unconditionally equisat- and reconstruction-
        // preserving.
        let gate_defining_clauses = match gate_defining_clauses {
            Some(defining) if !self.gate_restriction_is_sound(var, clauses, defining) => None,
            other => other,
        };
        // `resolve_gate_pairs` only has meaning when a gate is present; once the
        // gate is nullified above it must be cleared too (debug_assert invariant).
        let resolve_gate_pairs = resolve_gate_pairs && gate_defining_clauses.is_some();

        // Check if elimination is bounded
        let (can_eliminate, resolvents, strengthened, satisfied_parents, resolution_attempts) =
            self.check_bounded_elimination_with_marks(
                var,
                clauses,
                gate_defining_clauses,
                resolve_gate_pairs,
                marks,
                vals,
                remaining_budget,
            );

        if !can_eliminate {
            let mut result = EliminationResult::not_eliminated(var);
            result.resolution_attempts = resolution_attempts;
            return result;
        }

        // Collect clauses to delete
        let pos_lit = Literal::positive(var);
        let neg_lit = Literal::negative(var);

        let mut to_delete = Vec::new();
        let mut witness_entries = Vec::new();
        let mut seen = HashSet::default();
        // CaDiCaL elim.cpp:611-671 (mark_eliminated_clauses_as_garbage):
        // ALL clauses are deleted, but only a SUBSET are pushed onto the
        // extension stack (witness entries for reconstruction).
        //
        // Gate-restricted elimination (elim.cpp:628): `if (!substitute || c->gate)`
        // means only gate-defining clauses get witness entries when a gate
        // exists. Non-gate clauses are deleted but NOT pushed. This is correct
        // because the gate definition alone suffices for reconstruction: the
        // reconstruction algorithm (extend.cpp:121-204) can determine the
        // eliminated variable's value from the gate clauses alone.
        //
        // Without this filter (#8356), pushing ALL clauses as witness entries
        // when gate-restricted resolution skips non-gate x non-gate pairs
        // causes reconstruction corruption: the non-gate clauses on the
        // extension stack reference resolvents that were never generated,
        // breaking the reconstruction invariant and causing cascading model
        // corruption.

        // #8397: Build set of satisfied parent indices for fast lookup, but
        // avoid the allocation on the common path where no parent was root-
        // satisfied during resolution.
        // CaDiCaL marks satisfied parents as garbage during resolution
        // (elim.cpp:319), then skips garbage clauses when building the
        // extension stack (elim.cpp:625). Satisfied parents are root-level-
        // satisfied clauses whose resolvents were NOT generated; pushing them
        // to the reconstruction stack is unsound because their root-true
        // literals may be flipped by reconstruction of later-eliminated
        // variables, causing spurious piviot flips that break other clauses.
        let satisfied_set: Option<HashSet<usize>> = if satisfied_parents.is_empty() {
            None
        } else {
            Some(satisfied_parents.iter().copied().collect())
        };

        for &(witness, occs) in &[
            (pos_lit, self.occ.get(pos_lit)),
            (neg_lit, self.occ.get(neg_lit)),
        ] {
            for &c_idx in occs {
                if c_idx >= clauses.len() || clauses.is_dead(c_idx) || !seen.insert(c_idx) {
                    continue;
                }
                to_delete.push(c_idx);
                // #8397: Skip satisfied parents — their resolvents were not
                // generated, so pushing them to the reconstruction stack would
                // allow reconstruction to flip the pivot based on a clause
                // whose non-pivot literal satisfaction is not guaranteed after
                // multi-variable reconstruction. CaDiCaL skips these via
                // garbage check (elim.cpp:625).
                if satisfied_set
                    .as_ref()
                    .is_some_and(|set| set.contains(&c_idx))
                {
                    continue;
                }
                // #8482: CaDiCaL elim.cpp:628: `if (!substitute || c->gate)`
                // When a gate exists, only push gate-defining clauses to the
                // extension stack. Non-gate clauses are deleted but NOT pushed.
                // The gate definition alone suffices for reconstruction.
                // Pushing non-gate clauses causes reconstruction corruption on
                // gate-structured formulas (braun circuit equivalence).
                //
                // When no gate exists (gate_defining_clauses is None), push all
                // non-satisfied clauses (full substitution mode).
                if let Some(defining) = gate_defining_clauses {
                    if !defining.contains(&c_idx) {
                        continue;
                    }
                }
                witness_entries.push(WitnessEntry {
                    clause_idx: c_idx,
                    witness,
                });
            }
        }

        // #8179: Reconstruction completeness guard. Witness entries MUST
        // contain BOTH polarities (positive and negative pivot) for the
        // reconstruction algorithm to work correctly, UNLESS the missing
        // side's clauses are all root-satisfied (#8397).
        //
        // Root cause: within a single BVE round, a prior variable's
        // elimination can delete clauses (via backward subsumption or
        // elim_propagate) that belong to a later variable's occurrence
        // lists. By the time the later variable is processed, its
        // occurrence lists are depleted on one side, producing one-sided
        // witness entries regardless of gate filtering.
        //
        // Exception (#8397): when all clauses on one side are root-
        // satisfied (and thus excluded from witness entries), the
        // variable is effectively pure on the other side. CaDiCaL handles
        // this correctly by skipping garbage (root-satisfied) clauses in
        // mark_eliminated_clauses_as_garbage (elim.cpp:625), producing
        // single-polarity extension stack entries for pure-after-satisfied
        // variables. Reconstruction works correctly with single-polarity
        // entries: it either flips the variable to satisfy the remaining
        // clauses or leaves it as-is if they're already satisfied.
        {
            let has_pos = witness_entries.iter().any(|e| e.witness == pos_lit);
            let has_neg = witness_entries.iter().any(|e| e.witness == neg_lit);
            if !has_pos || !has_neg {
                // Check if the missing polarity is accounted for by
                // root-satisfied parents. If all missing-polarity clauses
                // are in satisfied_parents, the elimination is still valid.
                // The missing side must also have at least one clause
                // (otherwise it's a pure literal, which is rejected).
                let missing_lit = if !has_pos { pos_lit } else { neg_lit };
                let missing_count = to_delete
                    .iter()
                    .filter(|&&idx| clauses.literals(idx).contains(&missing_lit))
                    .count();
                let missing_satisfied_count = to_delete
                    .iter()
                    .filter(|&&idx| {
                        clauses.literals(idx).contains(&missing_lit)
                            && satisfied_set.as_ref().is_some_and(|set| set.contains(&idx))
                    })
                    .count();
                // Must have at least one clause on the missing side, and
                // all of them must be root-satisfied. Pure literals
                // (missing_count == 0) are rejected.
                let missing_all_satisfied =
                    missing_count > 0 && missing_count == missing_satisfied_count;
                if !missing_all_satisfied {
                    let mut result = EliminationResult::not_eliminated(var);
                    result.resolution_attempts = resolution_attempts;
                    return result;
                }
            }
        }

        let active_before = clauses.active_clause_count();
        // Only apply the 10% backstop on formulas large enough for the
        // percentage to be meaningful. On tiny formulas, additive
        // growth_bound is the intended sole budget control.
        if active_before >= 100 && resolvents.len() > to_delete.len() {
            let growth = resolvents.len() - to_delete.len();
            if growth.saturating_mul(10) > active_before {
                let mut result = EliminationResult::not_eliminated(var);
                result.resolution_attempts = resolution_attempts;
                return result;
            }
        }

        debug_assert!(
            to_delete.iter().all(|&idx| {
                idx < clauses.len()
                    && !clauses.is_dead(idx)
                    && clauses
                        .literals(idx)
                        .iter()
                        .any(|lit| lit.variable() == var)
            }),
            "BUG: deleted clause missing eliminated variable {var:?}"
        );
        debug_assert!(
            witness_entries.iter().all(|entry| {
                entry.clause_idx < clauses.len()
                    && !clauses.is_dead(entry.clause_idx)
                    && entry.witness.variable() == var
                    && clauses.literals(entry.clause_idx).contains(&entry.witness)
            }),
            "BUG: invalid witness entries for eliminated variable {var:?}"
        );
        #[cfg(debug_assertions)]
        {
            let to_delete_set: HashSet<usize> = to_delete.iter().copied().collect();
            assert!(
                self.occ
                    .get(pos_lit)
                    .iter()
                    .chain(self.occ.get(neg_lit).iter())
                    .all(|&idx| {
                        if idx >= clauses.len() || clauses.is_dead(idx) {
                            return true;
                        }
                        if !clauses
                            .literals(idx)
                            .iter()
                            .any(|lit| lit.variable() == var)
                        {
                            return true;
                        }
                        to_delete_set.contains(&idx)
                    }),
                "BUG: active clause containing {var:?} is missing from deletion/witness set"
            );
        }
        // #8397/#8483: Deleted clauses = witness entries + satisfied parents
        // + gate-filtered non-gate clauses. Three categories of deleted-but-
        // not-witnessed clauses:
        // 1. Satisfied parents (CaDiCaL elim.cpp:625 garbage check)
        // 2. Gate-filtered clauses (#8482, CaDiCaL elim.cpp:628)
        // NOTE: Use satisfied_set.len() (deduplicated) because the same
        // clause can be a satisfied parent in multiple resolution pairs,
        // but to_delete is deduplicated via `seen` (#8477).
        debug_assert!(
            {
                let gate_filtered = if let Some(defining) = gate_defining_clauses {
                    to_delete.iter()
                        .filter(|&&idx| {
                            !satisfied_set
                                .as_ref()
                                .is_some_and(|set| set.contains(&idx))
                                && !defining.contains(&idx)
                        })
                        .count()
                } else {
                    0
                };
                let satisfied_count = satisfied_set.as_ref().map_or(0, |s| s.len());
                to_delete.len() == witness_entries.len() + satisfied_count + gate_filtered
            },
            "BUG: BVE: {} clauses deleted but {} witness + {} satisfied (dedup) + {} gate-filtered for var {var:?}",
            to_delete.len(),
            witness_entries.len(),
            satisfied_set.as_ref().map_or(0, |s| s.len()),
            if let Some(defining) = gate_defining_clauses {
                to_delete.iter()
                    .filter(|&&idx| {
                        !satisfied_set
                            .as_ref()
                            .is_some_and(|set| set.contains(&idx))
                            && !defining.contains(&idx)
                    })
                    .count()
            } else { 0 },
        );
        // Invariant: no resolvent should contain the eliminated variable.
        debug_assert!(
            resolvents
                .iter()
                .all(|(r, _, _, _)| r.iter().all(|l| l.variable() != var)),
            "BUG: resolvent contains eliminated variable {var:?}"
        );

        // Mark variable as eliminated
        if var_idx < self.eliminated.len() {
            self.eliminated[var_idx] = true;
        }

        // Update statistics
        self.stats.vars_eliminated += 1;
        self.stats.clauses_removed += to_delete.len() as u64;
        self.stats.resolvents_added += resolvents.len() as u64;
        // NOTE: non_unit_resolvents, total_resolvent_literals, and
        // max_resolvent_len are already counted in try_resolve_pair
        // (called during check_bounded_elimination_with_marks). Do NOT
        // re-count here — that would double-count resolvents for
        // successfully eliminated variables while leaving resolvents
        // from failed elimination attempts counted once. The try_resolve_pair
        // counter captures ALL resolution work (including for variables
        // that end up not being eliminated), which is the correct metric
        // for measuring BVE effort.

        EliminationResult {
            variable: var,
            to_delete,
            witness_entries,
            resolvents,
            strengthened,
            satisfied_parents,
            eliminated: true,
            resolution_attempts,
        }
    }

    /// Decide whether gate-restricted resolution + gate-only witnessing is sound
    /// (equisatisfiability- AND reconstruction-preserving) for `var` (inc1).
    ///
    /// Gate-restricted elimination skips non-gate × non-gate resolvent pairs and
    /// witnesses ONLY the gate-defining clauses (#8482). Reconstruction flips the
    /// pivot to satisfy its gate-only witnesses; a deleted, non-witnessed non-gate
    /// clause `(¬x ∨ C)` can then be falsified even though the simplified DB was
    /// equisatisfiable (braun-9/13 + barrel6 FINALIZE_SAT_FAIL). AY's
    /// `vals`-based gate extraction can return a structurally-complete "gate" that
    /// still fails to subsume an extra non-gate constraint, so structural checks
    /// are insufficient.
    ///
    /// Conservative, provably-correct rule: only use gate restriction when EVERY
    /// live clause containing the pivot is a gate-defining clause (a "pure-gate"
    /// variable). Then there are no non-gate clauses to drop, gate-only witnessing
    /// equals full witnessing, and restricted resolution equals full resolution —
    /// all trivially sound. Otherwise the caller nullifies the gate and falls back
    /// to full resolution + full witnessing (unconditionally equisat-preserving),
    /// sacrificing gate aggressiveness on mixed variables for guaranteed soundness.
    fn gate_restriction_is_sound(
        &self,
        var: Variable,
        clauses: &ClauseArena,
        defining: &[usize],
    ) -> bool {
        let live = |idx: usize| idx < clauses.len() && !clauses.is_dead(idx);
        // Pure-gate test: every live clause containing the pivot (either polarity)
        // must be a gate-defining clause. A single non-gate clause makes gate-only
        // witnessing unsound for reconstruction → fall back to full resolution.
        for &lit in &[Literal::positive(var), Literal::negative(var)] {
            for &idx in self.occ.get(lit) {
                if live(idx) && !defining.contains(&idx) {
                    return false;
                }
            }
        }
        true
    }

    /// Finalize a variable elimination using pre-computed resolution results.
    ///
    /// This is the GPU-accelerated path (#8349): the resolution phase was
    /// performed on the GPU, producing `resolvents`, `strengthened`, and
    /// `satisfied_parents`. This method performs the remaining steps:
    /// witness entry collection, reconstruction completeness guard, 10%
    /// growth backstop, and variable elimination marking.
    ///
    /// The logic mirrors `try_eliminate_with_gate_with_marks` lines 374-548,
    /// factored out to avoid duplication between CPU and GPU paths.
    #[cfg(feature = "gpu")]
    pub(crate) fn finalize_elimination_from_resolution(
        &mut self,
        var: Variable,
        clauses: &ClauseArena,
        can_eliminate: bool,
        resolvents: Vec<(Vec<Literal>, usize, usize, Vec<usize>)>,
        strengthened: Vec<super::ClauseStrengthening>,
        satisfied_parents: Vec<usize>,
        resolution_attempts: u64,
    ) -> EliminationResult {
        let var_idx = var.index();

        if var_idx < self.eliminated.len() && self.eliminated[var_idx] {
            return EliminationResult::not_eliminated(var);
        }

        if !can_eliminate {
            let mut result = EliminationResult::not_eliminated(var);
            result.resolution_attempts = resolution_attempts;
            return result;
        }

        let pos_lit = Literal::positive(var);
        let neg_lit = Literal::negative(var);

        let mut to_delete = Vec::new();
        let mut witness_entries = Vec::new();
        let mut seen = HashSet::default();

        // #8397 (CPU parity with try_eliminate_with_gate_with_marks):
        // root-satisfied parents are deleted but must NOT be pushed as
        // reconstruction witnesses. Their resolvents were never generated,
        // so a witness entry could flip the pivot based on a clause whose
        // satisfaction is not guaranteed after multi-variable
        // reconstruction (#8356).
        let satisfied_set: Option<HashSet<usize>> = if satisfied_parents.is_empty() {
            None
        } else {
            Some(satisfied_parents.iter().copied().collect())
        };

        for &(witness, occs) in &[
            (pos_lit, self.occ.get(pos_lit)),
            (neg_lit, self.occ.get(neg_lit)),
        ] {
            for &c_idx in occs {
                if c_idx >= clauses.len() || clauses.is_dead(c_idx) || !seen.insert(c_idx) {
                    continue;
                }
                to_delete.push(c_idx);
                if satisfied_set
                    .as_ref()
                    .is_some_and(|set| set.contains(&c_idx))
                {
                    continue;
                }
                witness_entries.push(WitnessEntry {
                    clause_idx: c_idx,
                    witness,
                });
            }
        }

        // Reconstruction completeness guard (#8179), with the #8397
        // exception: a polarity whose clauses are ALL root-satisfied is
        // effectively pure on the other side and remains eliminable
        // (CPU parity with try_eliminate_with_gate_with_marks).
        {
            let has_pos = witness_entries.iter().any(|e| e.witness == pos_lit);
            let has_neg = witness_entries.iter().any(|e| e.witness == neg_lit);
            if !has_pos || !has_neg {
                let missing_lit = if !has_pos { pos_lit } else { neg_lit };
                let missing_count = to_delete
                    .iter()
                    .filter(|&&idx| clauses.literals(idx).contains(&missing_lit))
                    .count();
                let missing_satisfied_count = to_delete
                    .iter()
                    .filter(|&&idx| {
                        clauses.literals(idx).contains(&missing_lit)
                            && satisfied_set.as_ref().is_some_and(|set| set.contains(&idx))
                    })
                    .count();
                let missing_all_satisfied =
                    missing_count > 0 && missing_count == missing_satisfied_count;
                if !missing_all_satisfied {
                    let mut result = EliminationResult::not_eliminated(var);
                    result.resolution_attempts = resolution_attempts;
                    return result;
                }
            }
        }

        // 10% growth backstop.
        let active_before = clauses.active_clause_count();
        if active_before >= 100 && resolvents.len() > to_delete.len() {
            let growth = resolvents.len() - to_delete.len();
            if growth.saturating_mul(10) > active_before {
                let mut result = EliminationResult::not_eliminated(var);
                result.resolution_attempts = resolution_attempts;
                return result;
            }
        }

        // Mark variable as eliminated.
        if var_idx < self.eliminated.len() {
            self.eliminated[var_idx] = true;
        }

        self.stats.vars_eliminated += 1;
        self.stats.clauses_removed += to_delete.len() as u64;
        self.stats.resolvents_added += resolvents.len() as u64;

        EliminationResult {
            variable: var,
            to_delete,
            witness_entries,
            resolvents,
            strengthened,
            satisfied_parents,
            eliminated: true,
            resolution_attempts,
        }
    }
}
