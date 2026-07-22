// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BVE resolution core and bounded elimination check.

use super::{
    BoundedElimCheck, ClauseStrengthening, ResolveAcc, ResolveClauseProfile, ResolveOutcome, BVE,
    ELIM_OCC_LIMIT,
};
use crate::clause::{clause_signature_bit, ClauseSignature};
use crate::clause_arena::ClauseArena;
use crate::kani_compat::DetHashMap;
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};

impl BVE {
    #[inline]
    pub(crate) fn resolve_clause_profile(
        clause: &[Literal],
        var: Variable,
        vals: &[i8],
        marks: &mut LitMarks,
    ) -> (ClauseSignature, bool) {
        let mut signature = 0;
        let mut tautological = false;

        marks.clear_clause(clause);
        for &lit in clause {
            if lit.variable() == var {
                continue;
            }
            // CaDiCaL elim.cpp:298-314: skip root-level assigned literals.
            // Root-true → parent is satisfied (handled at resolve level).
            // Root-false → literal is dead, prune from resolvent.
            if vals.get(lit.index()).copied().unwrap_or(0) != 0 {
                continue;
            }

            let sign = lit.sign_i8();
            if marks.get(lit.variable()) == -sign {
                tautological = true;
                break;
            }
            if marks.get(lit.variable()) == 0 {
                marks.mark(lit);
            }
            signature |= clause_signature_bit(lit);
        }
        marks.clear_clause(clause);

        (signature, tautological)
    }

    pub(crate) fn resolve_without_tautology_checks(
        &mut self,
        pos_clause: &[Literal],
        neg_clause: &[Literal],
        var: Variable,
        marks: &mut LitMarks,
        vals: &[i8],
    ) -> ResolveOutcome {
        self.resolvent_buf.clear();
        self.pruned_root_vars_buf.clear();
        let pos_pivot = Literal::positive(var);
        let neg_pivot = Literal::negative(var);

        debug_assert!(
            pos_clause
                .iter()
                .all(|l| { l.variable() == var || !self.eliminated[l.variable().index()] }),
            "BUG: pos_clause contains eliminated variable (other than pivot {var:?})",
        );
        debug_assert!(
            neg_clause
                .iter()
                .all(|l| { l.variable() == var || !self.eliminated[l.variable().index()] }),
            "BUG: neg_clause contains eliminated variable (other than pivot {var:?})",
        );
        debug_assert!(
            !pos_clause.is_empty() && !neg_clause.is_empty(),
            "BUG: resolve called with empty clause",
        );
        debug_assert!(
            pos_clause.contains(&pos_pivot),
            "BUG: positive parent clause missing pivot literal {pos_pivot:?}"
        );
        debug_assert!(
            neg_clause.contains(&neg_pivot),
            "BUG: negative parent clause missing pivot literal {neg_pivot:?}"
        );

        marks.clear_clause(pos_clause);
        marks.clear_clause(neg_clause);

        // Positive clause: tautology check SKIPPED (signatures guarantee it).
        for &lit in pos_clause {
            if lit.variable() == var {
                continue;
            }

            let v = vals.get(lit.index()).copied().unwrap_or(0);
            if v > 0 {
                self.stats.root_satisfied_parents += 1;
                marks.clear_clause(&self.resolvent_buf);
                return ResolveOutcome::ParentSatisfied(true);
            }
            if v < 0 {
                // Root-level-false: literal is dead, prune from resolvent.
                self.stats.root_literals_pruned += 1;
                self.pruned_root_vars_buf.push(lit.variable().index());
                continue;
            }

            if marks.get(lit.variable()) == 0 {
                marks.mark(lit);
                self.resolvent_buf.push(lit);
            }
        }

        // Negative clause: tautology check SKIPPED (signatures guarantee it).
        for &lit in neg_clause {
            if lit.variable() == var {
                continue;
            }

            let v = vals.get(lit.index()).copied().unwrap_or(0);
            if v > 0 {
                self.stats.root_satisfied_parents += 1;
                marks.clear_clause(&self.resolvent_buf);
                return ResolveOutcome::ParentSatisfied(false);
            }
            if v < 0 {
                // Root-level-false: literal is dead, prune from resolvent.
                self.stats.root_literals_pruned += 1;
                self.pruned_root_vars_buf.push(lit.variable().index());
                continue;
            }

            if marks.get(lit.variable()) == 0 {
                marks.mark(lit);
                self.resolvent_buf.push(lit);
            }
        }

        marks.clear_clause(&self.resolvent_buf);

        let resolvent = self.resolvent_buf.clone();
        self.resolvent_buf.clear();
        debug_assert!(
            resolvent.iter().all(|l| l.variable() != var),
            "BUG: resolvent contains pivot variable {var:?}"
        );
        debug_assert!(
            resolvent.iter().enumerate().all(|(idx, lit)| {
                resolvent[..idx]
                    .iter()
                    .all(|prev| prev.variable() != lit.variable())
            }),
            "BUG: resolvent contains duplicate variables: {resolvent:?}"
        );
        let pruned = self.pruned_root_vars_buf.clone();
        ResolveOutcome::Resolvent(resolvent, pruned)
    }

    /// Compute the resolvent of two clauses on a variable using shared marks.
    ///
    /// CaDiCaL `elim.cpp:292-359`: for each literal, checks `val(lit)`:
    /// - Root-level-true -> parent clause is satisfied -> `ParentSatisfied`
    /// - Root-level-false -> literal is dead -> skip (prune from resolvent)
    /// - Unassigned -> include in resolvent (mark for tautology detection)
    ///
    /// The `vals` array uses literal-indexed encoding: `vals[lit.index()]` is
    /// 1 (true), -1 (false), or 0 (unassigned). Since BVE runs at level 0,
    /// all non-zero entries are root-level assignments.
    pub(super) fn resolve_with_marks(
        &mut self,
        pos_clause: &[Literal],
        neg_clause: &[Literal],
        var: Variable,
        marks: &mut LitMarks,
        vals: &[i8],
    ) -> ResolveOutcome {
        self.resolvent_buf.clear();
        self.pruned_root_vars_buf.clear();
        let pos_pivot = Literal::positive(var);
        let neg_pivot = Literal::negative(var);

        // CaDiCaL elim.cpp: input clauses must contain only non-eliminated
        // variables (except the pivot being eliminated in this call).
        debug_assert!(
            pos_clause
                .iter()
                .all(|l| { l.variable() == var || !self.eliminated[l.variable().index()] }),
            "BUG: pos_clause contains eliminated variable (other than pivot {var:?})",
        );
        debug_assert!(
            neg_clause
                .iter()
                .all(|l| { l.variable() == var || !self.eliminated[l.variable().index()] }),
            "BUG: neg_clause contains eliminated variable (other than pivot {var:?})",
        );
        // CaDiCaL elim.cpp: clauses must be non-empty (at least the pivot)
        debug_assert!(
            !pos_clause.is_empty() && !neg_clause.is_empty(),
            "BUG: resolve called with empty clause",
        );

        debug_assert!(
            pos_clause.contains(&pos_pivot),
            "BUG: positive parent clause missing pivot literal {pos_pivot:?}"
        );
        debug_assert!(
            neg_clause.contains(&neg_pivot),
            "BUG: negative parent clause missing pivot literal {neg_pivot:?}"
        );

        // Clear marks before building the resolvent.
        marks.clear_clause(pos_clause);
        marks.clear_clause(neg_clause);

        // Add literals from positive clause (except the pivot).
        // CaDiCaL elim.cpp:292-315: check val(lit) for root-level pruning.
        for &lit in pos_clause {
            if lit.variable() == var {
                continue;
            }

            // Root-level value check (CaDiCaL elim.cpp:298-314).
            let v = vals.get(lit.index()).copied().unwrap_or(0);
            if v > 0 {
                // Literal is true at root level → parent clause is satisfied.
                // CaDiCaL: mark_garbage(c), return false.
                self.stats.root_satisfied_parents += 1;
                marks.clear_clause(&self.resolvent_buf);
                return ResolveOutcome::ParentSatisfied(true);
            }
            if v < 0 {
                // Root-level-false: literal is dead, prune from resolvent.
                // CaDiCaL elim.cpp:302-303: `continue` to skip.
                self.stats.root_literals_pruned += 1;
                self.pruned_root_vars_buf.push(lit.variable().index());
                continue;
            }

            let sign: i8 = lit.sign_i8();
            if marks.get(lit.variable()) == -sign {
                // Tautology: both L and ~L present
                self.stats.tautologies_skipped += 1;
                marks.clear_clause(&self.resolvent_buf);
                return ResolveOutcome::Tautology;
            }
            if marks.get(lit.variable()) == 0 {
                marks.mark(lit);
                self.resolvent_buf.push(lit);
            }
            // If marked with same sign, literal is duplicate, skip.
        }

        // Add literals from negative clause (except the pivot).
        // CaDiCaL elim.cpp:331-358: same root-level checks + tautology detection.
        for &lit in neg_clause {
            if lit.variable() == var {
                continue;
            }

            // Root-level value check.
            let v = vals.get(lit.index()).copied().unwrap_or(0);
            if v > 0 {
                // Literal is true at root level → parent clause is satisfied.
                self.stats.root_satisfied_parents += 1;
                marks.clear_clause(&self.resolvent_buf);
                return ResolveOutcome::ParentSatisfied(false);
            }
            if v < 0 {
                // Root-level-false: literal is dead, prune from resolvent.
                self.stats.root_literals_pruned += 1;
                self.pruned_root_vars_buf.push(lit.variable().index());
                continue;
            }

            let sign: i8 = lit.sign_i8();
            if marks.get(lit.variable()) == -sign {
                // Tautology: both L and ~L present
                self.stats.tautologies_skipped += 1;
                marks.clear_clause(&self.resolvent_buf);
                return ResolveOutcome::Tautology;
            }
            if marks.get(lit.variable()) == 0 {
                marks.mark(lit);
                self.resolvent_buf.push(lit);
            }
            // If marked with same sign, literal is duplicate, skip.
        }

        // Clear marks set during this call. With shared LitMarks, stale marks
        // from one resolution corrupt the next if only the input-clause clearing
        // covers overlapping variables.
        marks.clear_clause(&self.resolvent_buf);

        // Clone to preserve buffer allocation across calls (CaDiCaL elim.cpp:281).
        let resolvent = self.resolvent_buf.clone();
        self.resolvent_buf.clear();
        // Invariant: resolvent must not contain the pivot variable.
        // If the pivot appears, the resolution is unsound.
        debug_assert!(
            resolvent.iter().all(|l| l.variable() != var),
            "BUG: resolvent contains pivot variable {var:?}"
        );
        // Invariant: resolvent must not contain duplicate variables.
        // Duplicates (same or opposite polarity) indicate mark handling bugs.
        debug_assert!(
            resolvent.iter().enumerate().all(|(idx, lit)| {
                resolvent[..idx]
                    .iter()
                    .all(|prev| prev.variable() != lit.variable())
            }),
            "BUG: resolvent contains duplicate variables: {resolvent:?}"
        );
        let pruned = self.pruned_root_vars_buf.clone();
        ResolveOutcome::Resolvent(resolvent, pruned)
    }

    /// CaDiCaL elim.cpp:215-223: build OTFS strengthened clause by removing
    /// the pivot and root-level-false literals from the parent clause.
    ///
    /// Returns (new_lits, pruned_var_indices) where pruned_var_indices
    /// tracks root-level-false variables removed (for LRAT hint generation).
    #[inline]
    pub(crate) fn parent_without_pivot_and_false(
        parent: &[Literal],
        var: Variable,
        vals: &[i8],
    ) -> (Vec<Literal>, Vec<usize>) {
        let mut new_lits = Vec::with_capacity(parent.len());
        let mut pruned = Vec::new();
        for &lit in parent {
            if lit.variable() == var {
                continue;
            }
            let v = vals.get(lit.index()).copied().unwrap_or(0);
            if v < 0 {
                // Root-level-false: prune from strengthened clause,
                // record for LRAT hints.
                pruned.push(lit.variable().index());
                continue;
            }
            // v > 0 shouldn't happen (parent clause should not be satisfied),
            // but include the literal to be safe.
            new_lits.push(lit);
        }
        (new_lits, pruned)
    }

    #[inline]
    pub(super) fn record_strengthening(
        acc: &mut ResolveAcc<'_>,
        clause_idx: usize,
        new_lits: Vec<Literal>,
        pos_ante: usize,
        neg_ante: usize,
        pruned_vars: Vec<usize>,
    ) {
        if let Some(&idx) = acc.strengthened_idx.get(&clause_idx) {
            if new_lits.len() < acc.strengthened[idx].new_lits.len() {
                acc.strengthened[idx].new_lits = new_lits;
                acc.strengthened[idx].pos_ante = pos_ante;
                acc.strengthened[idx].neg_ante = neg_ante;
                acc.strengthened[idx].pruned_vars = pruned_vars;
            }
            return;
        }
        let pos = acc.strengthened.len();
        acc.strengthened.push(ClauseStrengthening {
            clause_idx,
            new_lits,
            pos_ante,
            neg_ante,
            pruned_vars,
        });
        acc.strengthened_idx.insert(clause_idx, pos);
    }

    /// Test helper wrapper using a temporary mark array and empty vals.
    #[cfg(test)]
    pub(super) fn resolve(
        &mut self,
        pos_clause: &[Literal],
        neg_clause: &[Literal],
        var: Variable,
    ) -> Option<Vec<Literal>> {
        let mut marks = LitMarks::new(self.num_vars);
        let empty_vals: Vec<i8> = vec![0; self.num_vars * 2];
        match self.resolve_with_marks(pos_clause, neg_clause, var, &mut marks, &empty_vals) {
            ResolveOutcome::Resolvent(r, _pruned) => Some(r),
            ResolveOutcome::Tautology | ResolveOutcome::ParentSatisfied(_) => None,
        }
    }

    /// Check if eliminating a variable would increase the formula size too much
    ///
    /// Returns (can_eliminate, resolvents) where:
    /// - can_eliminate: true if the elimination is bounded
    /// - resolvents: the computed resolvents (only if can_eliminate is true)
    ///
    /// `remaining_budget` is the number of resolution attempts remaining in
    /// the global BVE effort budget. The function exits early (returning
    /// not-eliminable) if this many attempts are exhausted before resolution
    /// completes. This implements CaDiCaL's incremental effort charging
    /// (elim.cpp:888): the budget is checked per-resolution-attempt, not
    /// charged upfront as pos*neg (#8195).
    ///
    /// REQUIRES: var is not already eliminated
    pub(super) fn check_bounded_elimination_with_marks(
        &mut self,
        var: Variable,
        clauses: &ClauseArena,
        gate_defining_clauses: Option<&[usize]>,
        resolve_gate_pairs: bool,
        marks: &mut LitMarks,
        vals: &[i8],
        remaining_budget: u64,
    ) -> BoundedElimCheck {
        debug_assert!(
            !self.eliminated[var.index()],
            "BUG: check_bounded_elimination called on eliminated variable {var:?}"
        );
        debug_assert!(
            gate_defining_clauses.is_some() || !resolve_gate_pairs,
            "BUG: resolve_gate_pairs requires gate_defining_clauses"
        );

        let pos_lit = Literal::positive(var);
        let neg_lit = Literal::negative(var);

        // Copy occ lists to buffers, filtering stale (garbage) entries from lazy
        // removal. Same O(occ_len) cost; ensures accurate heuristic counts.
        self.pos_occ_buf.clear();
        self.pos_occ_buf.extend(
            self.occ
                .get(pos_lit)
                .iter()
                .copied()
                .filter(|&idx| idx < clauses.len() && !clauses.is_dead(idx)),
        );
        self.neg_occ_buf.clear();
        self.neg_occ_buf.extend(
            self.occ
                .get(neg_lit)
                .iter()
                .copied()
                .filter(|&idx| idx < clauses.len() && !clauses.is_dead(idx)),
        );

        let pos_count = self.pos_occ_buf.len();
        let neg_count = self.neg_occ_buf.len();

        debug_assert!(
            self.pos_occ_buf
                .iter()
                .all(|&idx| clauses.literals(idx).contains(&pos_lit)),
            "BUG: positive occurrence list for {var:?} contains invalid entries"
        );
        debug_assert!(
            self.neg_occ_buf
                .iter()
                .all(|&idx| clauses.literals(idx).contains(&neg_lit)),
            "BUG: negative occurrence list for {var:?} contains invalid entries"
        );
        // CaDiCaL elim.cpp:268-269: resolution inputs must be irredundant (#5019).
        debug_assert!(
            self.pos_occ_buf.iter().all(|&idx| !clauses.is_learned(idx)),
            "BUG: positive occ list for {var:?} contains learned clause"
        );
        debug_assert!(
            self.neg_occ_buf.iter().all(|&idx| !clauses.is_learned(idx)),
            "BUG: negative occ list for {var:?} contains learned clause"
        );

        // CaDiCaL elimfast.cpp:234-236: sort occ lists by clause size (shortest
        // first). Shorter clauses produce shorter resolvents that are more likely
        // to trigger OTFS and tautology detection, improving resolvent quality.
        self.pos_occ_buf
            .sort_unstable_by_key(|&idx| clauses.len_of(idx));
        self.neg_occ_buf
            .sort_unstable_by_key(|&idx| clauses.len_of(idx));

        if pos_count == 0 || neg_count == 0 {
            // Variable is pure - can be eliminated trivially
            // All clauses containing the variable can be removed
            return (true, Vec::new(), Vec::new(), Vec::new(), 0);
        }

        // Kissat resolve.c:282-289: reject if total occurrences exceed limit.
        // Checking the sum (not per-polarity) allows elimination of variables
        // with lopsided occurrence distributions (e.g., 20 pos + 300 neg).
        if pos_count + neg_count > ELIM_OCC_LIMIT {
            return (false, Vec::new(), Vec::new(), Vec::new(), 0);
        }

        // Reuse profile buffers across elimination attempts (#8134).
        // clear() retains backing allocation; only the first call allocates.
        self.pos_profile_buf.clear();
        for &idx in &self.pos_occ_buf {
            let (signature, tautological) =
                Self::resolve_clause_profile(clauses.literals(idx), var, vals, marks);
            self.pos_profile_buf.push(ResolveClauseProfile {
                clause_idx: idx,
                signature,
                tautological,
            });
        }
        self.neg_profile_buf.clear();
        for &idx in &self.neg_occ_buf {
            let (signature, tautological) =
                Self::resolve_clause_profile(clauses.literals(idx), var, vals, marks);
            self.neg_profile_buf.push(ResolveClauseProfile {
                clause_idx: idx,
                signature,
                tautological,
            });
        }
        // Move profiles out of self to avoid borrow conflict during resolution.
        // std::mem::take replaces with an empty Vec (no allocation) and gives
        // ownership to the local variable. The buffers are restored after the
        // resolution loop so they retain their capacity for the next call.
        let pos_candidates = std::mem::take(&mut self.pos_profile_buf);
        let neg_candidates = std::mem::take(&mut self.neg_profile_buf);

        // Number of clauses that would be removed
        let clauses_removed = pos_count + neg_count;

        // CaDiCaL fastelim product shortcut (elimfast.cpp:85-88, :239):
        // If pos * neg <= budget, even in the worst case (ALL resolvents are
        // non-tautological), the count can't exceed the clause-count budget.
        // The resolution loop still runs (to compute resolvents and check the
        // per-resolvent size limit), but per-pair count-check early-abort
        // is skipped.
        let initial_budget = self.resolvent_budget(clauses_removed);
        let clause_count_guaranteed = pos_count
            .checked_mul(neg_count)
            .is_some_and(|product| product <= initial_budget);

        // Compute all resolvents and count
        let mut resolvents = Vec::new();
        let mut strengthened = Vec::new();

        let mut pos_gate = Vec::new();
        let mut pos_non_gate = Vec::new();
        let mut neg_gate = Vec::new();
        let mut neg_non_gate = Vec::new();

        if let Some(defining) = gate_defining_clauses {
            for cand in pos_candidates {
                if defining.contains(&cand.clause_idx) {
                    pos_gate.push(cand);
                } else {
                    pos_non_gate.push(cand);
                }
            }
            for cand in neg_candidates {
                if defining.contains(&cand.clause_idx) {
                    neg_gate.push(cand);
                } else {
                    neg_non_gate.push(cand);
                }
            }
        } else {
            // No gate - all clauses are non-gate.
            pos_non_gate = pos_candidates;
            neg_non_gate = neg_candidates;
        }

        // Restricted resolution (Een & Biere SAT'05): if a functional gate
        // definition for `var` is known, only resolve between gate clauses and
        // non-gate clauses, skipping gate/gate and non-gate/non-gate pairs.
        let mut found_empty_resolvent = false;
        let mut satisfied_parents = Vec::new();
        let mut strengthened_idx = DetHashMap::default();
        // CaDiCaL elim.cpp:271,888: count actual resolve_clauses() calls and
        // check against the remaining global budget. CaDiCaL checks
        // `stats.elimres <= resolution_limit` at the outer loop, but the
        // counter increments per resolve_clauses() call. This means a
        // variable with 500*500=250K pairs can't burn the entire budget
        // when only 100 attempts remain -- it exits early (#8195).
        let mut resolution_attempts: u64 = 0;
        let mut resolution_failed = false;
        let mut budget_exhausted = false;
        {
            let mut acc = ResolveAcc {
                clauses_removed,
                resolvents: &mut resolvents,
                strengthened: &mut strengthened,
                strengthened_idx: &mut strengthened_idx,
                found_empty_resolvent: &mut found_empty_resolvent,
                clause_count_guaranteed,
                satisfied_parents: &mut satisfied_parents,
            };

            // BUG FIX (#ay/1): The prior code had
            //   `let force_full = env("AY_FORCE_FULL_RESOLVE") || resolve_gate_pairs;`
            // When resolve_gate_pairs was true (kitten-based semantic definitions),
            // force_full caused the else branch to run, which only resolves
            // pos_non_gate × neg_non_gate — completely dropping gate clauses
            // from resolution. The restricted path already correctly handles
            // resolve_gate_pairs by including the gate×gate loop.
            if gate_defining_clauses.is_some() {
                'gate_outer: {
                    for &pos in &pos_gate {
                        for &neg in &neg_non_gate {
                            // Incremental budget check (#8195): bail out when
                            // the global resolution budget is exhausted mid-
                            // variable, matching CaDiCaL's per-attempt charging.
                            if resolution_attempts >= remaining_budget {
                                budget_exhausted = true;
                                break 'gate_outer;
                            }
                            resolution_attempts += 1;
                            if !self.try_resolve_pair(var, clauses, pos, neg, marks, vals, &mut acc)
                            {
                                resolution_failed = true;
                                break 'gate_outer;
                            }
                        }
                    }
                    for &pos in &pos_non_gate {
                        for &neg in &neg_gate {
                            if resolution_attempts >= remaining_budget {
                                budget_exhausted = true;
                                break 'gate_outer;
                            }
                            resolution_attempts += 1;
                            if !self.try_resolve_pair(var, clauses, pos, neg, marks, vals, &mut acc)
                            {
                                resolution_failed = true;
                                break 'gate_outer;
                            }
                        }
                    }
                    // CaDiCaL elim.cpp:501: `definition_unit` disables the
                    // same-gate skip for kitten-based semantic definitions.
                    // Structural gates keep skipping gate×gate pairs because
                    // those resolvents are tautological; semantic definitions
                    // can require them for soundness.
                    if resolve_gate_pairs {
                        for &pos in &pos_gate {
                            for &neg in &neg_gate {
                                if resolution_attempts >= remaining_budget {
                                    budget_exhausted = true;
                                    break 'gate_outer;
                                }
                                resolution_attempts += 1;
                                if !self
                                    .try_resolve_pair(var, clauses, pos, neg, marks, vals, &mut acc)
                                {
                                    resolution_failed = true;
                                    break 'gate_outer;
                                }
                            }
                        }
                    }
                }
                // CaDiCaL elim.cpp:501: non_gate × non_gate pairs are NEVER
                // resolved when a gate exists. The gate + gate×non_gate
                // resolvents are equisatisfiable with the original formula.
                // The previous "incomplete gate" heuristic that resolved
                // non_gate × non_gate was incorrect — it produced extra
                // resolvents not needed for equisatisfiability and caused
                // reconstruction to push all clauses (defeating gate-only
                // filtering).
            } else {
                // Full variable elimination resolution.
                'full_outer: for &pos in &pos_non_gate {
                    for &neg in &neg_non_gate {
                        if resolution_attempts >= remaining_budget {
                            budget_exhausted = true;
                            break 'full_outer;
                        }
                        resolution_attempts += 1;
                        if !self.try_resolve_pair(var, clauses, pos, neg, marks, vals, &mut acc) {
                            resolution_failed = true;
                            break 'full_outer;
                        }
                    }
                }
            }
        }

        // Restore profile buffers to preserve capacity for the next call (#8134).
        // In the no-gate path, pos_non_gate/neg_non_gate ARE pos/neg_candidates.
        // In the gate path, candidates were split into separate locals.
        // We restore the larger of the two (candidates, if they weren't consumed).
        if gate_defining_clauses.is_none() {
            self.pos_profile_buf = pos_non_gate;
            self.neg_profile_buf = neg_non_gate;
        } else {
            // Gate path: pos_candidates/neg_candidates were consumed by split.
            // Restore with the larger of the two sub-vectors.
            if pos_gate.capacity() >= pos_non_gate.capacity() {
                self.pos_profile_buf = pos_gate;
            } else {
                self.pos_profile_buf = pos_non_gate;
            }
            if neg_gate.capacity() >= neg_non_gate.capacity() {
                self.neg_profile_buf = neg_gate;
            } else {
                self.neg_profile_buf = neg_non_gate;
            }
        }

        if resolution_failed || budget_exhausted {
            return (
                false,
                Vec::new(),
                Vec::new(),
                Vec::new(),
                resolution_attempts,
            );
        }

        if found_empty_resolvent {
            return (
                true,
                resolvents,
                strengthened,
                satisfied_parents,
                resolution_attempts,
            );
        }

        // Clause-count bound (CaDiCaL elim.cpp:480,517; elimfast.cpp:118).
        // CaDiCaL uses the original occ count (pos+neg) as the budget base,
        // NOT adjusted for OTFS strengthening. OTFS results are never counted
        // as resolvents (they don't push to `resolvents`), so the budget
        // naturally stays accurate.
        //
        // Individual resolvent size is bounded by ELIM_CLAUSE_SIZE_LIMIT
        // (CaDiCaL elimclslim=100) at try_resolve_pair:1174. CaDiCaL has
        // no total-literal-count bound — clause count + per-resolvent size
        // are sufficient. The old AY-only literal-count bound (#4940) was
        // removed because: (a) CaDiCaL doesn't have it, (b) the P0
        // reconstruction bug (#6892) that motivated it is now fixed, and
        // (c) it was over-restrictive, rejecting ~50% of eliminations
        // CaDiCaL accepts (13 vs 25 eliminated vars on crn_11_99_u).
        let bounded = resolvents.len() <= self.resolvent_budget(clauses_removed);

        if bounded {
            // Postcondition: no resolvent should contain the eliminated variable.
            debug_assert!(
                resolvents
                    .iter()
                    .all(|(r, _, _, _)| r.iter().all(|l| l.variable() != var)),
                "BUG: bounded resolvents contain eliminated variable {var:?}",
            );
            (
                true,
                resolvents,
                strengthened,
                satisfied_parents,
                resolution_attempts,
            )
        } else {
            (
                false,
                Vec::new(),
                Vec::new(),
                Vec::new(),
                resolution_attempts,
            )
        }
    }
}
