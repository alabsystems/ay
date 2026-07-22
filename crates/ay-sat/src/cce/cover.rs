// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Cce {
    /// ACCE: propagate asymmetric implications for one literal.
    ///
    /// `lit` was just set false. Check ALL clauses watching `~lit`:
    /// - Binary clauses: if blocker is true, skip. If false, CONFLICT.
    ///   If unassigned, set false (ALA).
    /// - Long clauses: scan all literals. If clause satisfied (any true
    ///   literal), skip. If all but one are false, force the remaining
    ///   literal false (ALA). If all are false, CONFLICT.
    ///
    /// `ignore_clause`: the clause being covered (must be skipped).
    ///
    /// Returns `true` if a conflict was found (clause is tautological).
    ///
    /// Port of CaDiCaL `Internal::cover_propagate_asymmetric` (cover.cpp:100-176).
    fn ala_propagate_one(
        &mut self,
        lit: Literal,
        watches: &WatchedLists,
        arena: &ClauseArena,
        ignore_clause: usize,
    ) -> bool {
        // `lit` is false, so clauses watching `lit` may become unit or
        // conflicting. This matches the solver BCP convention: a true trail
        // literal `p` scans watches for `p.negated()`.
        let wl = watches.get_watches(lit);
        for i in 0..wl.len() {
            let clause_idx = wl.clause_ref(i).0 as usize;
            if clause_idx == ignore_clause {
                continue;
            }

            if wl.is_binary(i) {
                // Binary clause fast path.
                let other = wl.blocker(i);
                if self.is_true(other) {
                    continue;
                }
                if self.is_false(other) {
                    return true; // conflict
                }
                self.set_false(other);
                self.added_trail.push(other);
                self.effort += 1;
            } else {
                // Long clause: full scan.
                if arena.is_garbage_any(clause_idx) || arena.is_empty_clause(clause_idx) {
                    continue;
                }

                let c_lits = arena.literals(clause_idx);
                self.effort += 1;

                // Single-pass scan: count unassigned literals.
                let mut unassigned_lit = None;
                let mut n_unassigned = 0u32;
                let mut satisfied = false;
                for &c_lit in c_lits {
                    if self.is_true(c_lit) {
                        satisfied = true;
                        break;
                    }
                    if !self.is_false(c_lit) {
                        n_unassigned += 1;
                        unassigned_lit = Some(c_lit);
                        if n_unassigned >= 2 {
                            break; // 2+ unassigned: no unit propagation
                        }
                    }
                }

                if satisfied {
                    continue;
                }

                if n_unassigned == 0 {
                    // All literals false => conflict (subsuming resolvent).
                    return true;
                }

                if n_unassigned == 1 {
                    // Exactly one unassigned: ALA forces it false.
                    let unit = unassigned_lit
                        .expect("invariant: exactly one unassigned when n_unassigned == 1");
                    self.set_false(unit);
                    self.added_trail.push(unit);
                    self.effort += 1;
                }
            }
        }
        false
    }

    /// Test hook for a single ALA propagation step.
    #[cfg(test)]
    pub(super) fn test_ala_propagate_one(
        &mut self,
        lit: Literal,
        watches: &WatchedLists,
        arena: &ClauseArena,
        ignore_clause: usize,
    ) -> bool {
        self.ala_propagate_one(lit, watches, arena, ignore_clause)
    }

    /// Test hook for setting up local CCE assumptions before ALA.
    #[cfg(test)]
    pub(super) fn test_assume_false(&mut self, lit: Literal) {
        self.set_false(lit);
        self.added_trail.push(lit);
    }

    /// Run ALA/ACCE propagation to completion for all pending literals on the trail.
    ///
    /// `ala_next`: index into `added_trail` of the next literal to propagate.
    /// `ignore_clause`: the clause being covered (skipped during propagation).
    /// Returns `true` if a conflict was found.
    fn ala_drain(
        &mut self,
        ala_next: &mut usize,
        watches: &WatchedLists,
        arena: &ClauseArena,
        ignore_clause: usize,
    ) -> bool {
        while *ala_next < self.added_trail.len() {
            let lit = self.added_trail[*ala_next];
            *ala_next += 1;
            if self.ala_propagate_one(lit, watches, arena, ignore_clause) {
                return true;
            }
        }
        false
    }

    /// Try to eliminate a single clause using ACCE (ALA + CLA).
    ///
    /// Returns `Some((blocking_literal, covered_lits))` if the clause is
    /// covered-tautological, `None` otherwise. `covered_lits` is the full
    /// covered set (original + CLA-added) needed for reconstruction.
    ///
    /// ACCE (Asymmetric Covered Clause Elimination) combines:
    /// - ALA: propagates implications through ALL watched clauses (binary + long)
    /// - CLA: extends the clause using occurrence-list intersection
    ///
    /// The two alternate until a blocking literal is found, a conflict is
    /// detected, or no progress is possible.
    ///
    /// Port of CaDiCaL `Internal::cover_clause` (cover.cpp:323-475).
    ///
    /// `vals`: solver's level-0 assignments (indexed by literal index).
    /// `freeze_counts`: per-variable freeze counts (>0 = frozen, skip CLA).
    /// `watches`: watch lists for ALA propagation (binary + long clauses).
    pub(super) fn cover_clause(
        &mut self,
        clause_idx: usize,
        arena: &ClauseArena,
        vals: &[i8],
        freeze_counts: &[u32],
        watches: &WatchedLists,
    ) -> Option<(Literal, Vec<Literal>)> {
        let lits = arena.literals(clause_idx);

        // Skip clauses with level-0 satisfied literals (already garbage).
        for &lit in lits {
            let li = lit.index();
            if li < vals.len() && vals[li] > 0 {
                return None;
            }
        }

        // Initialize: assign all clause literals false, build covered set.
        self.covered.clear();
        self.added_trail.clear();

        for &lit in lits {
            // Skip level-0 false literals (they don't participate).
            let li = lit.index();
            if li < vals.len() && vals[li] < 0 {
                continue;
            }
            self.set_false(lit);
            self.added_trail.push(lit);
            self.covered.push(lit);
        }

        // ALA/CLA alternating loop (CaDiCaL cover.cpp:337-470).
        // Phase 1: ACCE drains all pending asymmetric implications (binary + long).
        // Phase 2: CLA tries one covered literal.
        // If CLA extends, ACCE runs again for the new additions.
        let mut ala_next: usize = 0;
        let mut next_covered = 0;
        let mut result = None;

        loop {
            // Phase 1: ACCE — propagate all pending asymmetric implications.
            if self.ala_drain(&mut ala_next, watches, arena, clause_idx) {
                // Conflict: subsuming resolvent found. The clause is
                // tautological after ALA extension. Return the first
                // covered literal as the "blocking" witness.
                result = self.covered.first().copied();
                break;
            }

            // Phase 2: CLA — try one covered literal.
            if next_covered >= self.covered.len() {
                break;
            }

            let lit = self.covered[next_covered];
            next_covered += 1;

            // Skip frozen literals for CLA.
            let vi = lit.variable().index();
            if vi < freeze_counts.len() && freeze_counts[vi] > 0 {
                continue;
            }

            match self.cover_propagate_covered(lit, clause_idx, arena) {
                CoverResult::Blocked(blocking_lit) => {
                    result = Some(blocking_lit);
                    break;
                }
                CoverResult::Extended => {
                    // Add CLA literals from intersection to covered and assign them false.
                    // intersection is populated by cover_propagate_covered and is valid
                    // until the next call.
                    let ext_start = self.intersection.len();
                    for i in 0..ext_start {
                        let new_lit = self.intersection[i];
                        if !self.is_false(new_lit) {
                            self.set_false(new_lit);
                            self.added_trail.push(new_lit);
                            self.covered.push(new_lit);
                        }
                    }
                    // CLA restart: re-examine all covered literals from the
                    // beginning with the enlarged clause. CaDiCaL cover.cpp:76.
                    next_covered = 0;
                    self.stats.cla_steps += 1;
                }
                CoverResult::NoProgress => {
                    // Intersection was empty — CLA failed for this literal.
                }
            }
        }

        // Snapshot covered set BEFORE cleanup (needed for reconstruction).
        // CaDiCaL: cover_push_extension saves coveror.covered (cover.cpp:49-60).
        let covered_snapshot = if result.is_some() {
            self.covered.clone()
        } else {
            Vec::new()
        };

        // Cleanup: unassign all literals. Index-based to avoid holding
        // an immutable borrow on added_trail while calling &mut self.unset().
        for i in 0..self.added_trail.len() {
            let lit = self.added_trail[i];
            self.unset(lit);
        }

        result.map(|blocking_lit| (blocking_lit, covered_snapshot))
    }

    /// CLA propagation for one literal using occurrence lists.
    ///
    /// For literal `lit` in the covered clause, examines all clauses containing
    /// `~lit` (the resolution candidates). Computes the intersection of unassigned
    /// literals across those clauses.
    ///
    /// Returns:
    /// - `Blocked(lit)` if all resolution candidates are satisfied (blocked on `lit`)
    /// - `Extended` if intersection is non-empty (caller reads `self.intersection`)
    /// - `NoProgress` if intersection is empty
    ///
    /// Port of CaDiCaL `Internal::cover_propagate_covered` (cover.cpp:181-319).
    fn cover_propagate_covered(
        &mut self,
        lit: Literal,
        ignore_clause: usize,
        arena: &ClauseArena,
    ) -> CoverResult {
        let neg_lit = lit.negated();

        // Copy occurrence list indices into reusable buffer to avoid holding
        // an immutable borrow on self.occ while mutating other self fields.
        self.occ_cache.clear();
        self.occ_cache.extend_from_slice(self.occ.get(neg_lit));

        let mut first = true;
        self.intersection.clear();

        for oi in 0..self.occ_cache.len() {
            let d_idx = self.occ_cache[oi];
            if d_idx == ignore_clause {
                continue;
            }
            if d_idx >= arena.len() || arena.is_empty_clause(d_idx) {
                continue;
            }

            self.effort += 1;
            let d_lits = arena.literals(d_idx);

            // Check if clause d is "blocked" (has a true literal besides ~lit).
            // If it has a true literal under the current CCE assignment,
            // it's already satisfied and doesn't constrain the resolution.
            let mut d_blocked = false;
            for &d_lit in d_lits {
                if d_lit != neg_lit && self.is_true(d_lit) {
                    d_blocked = true;
                    break;
                }
            }
            if d_blocked {
                continue;
            }

            // Collect unassigned literals from d (excluding ~lit and false literals).
            if first {
                // First non-blocked clause: initialize intersection.
                for &d_lit in d_lits {
                    if d_lit == neg_lit {
                        continue;
                    }
                    if self.is_false(d_lit) || self.is_true(d_lit) {
                        continue;
                    }
                    self.intersection.push(d_lit);
                    let vi = d_lit.variable().index();
                    if vi < self.cla_marks.len() {
                        self.cla_marks[vi] = d_lit.sign_i8();
                    }
                }
                first = false;
            } else {
                // Subsequent clauses: intersect with current intersection.
                // Unmark all literals from this clause that appear in current
                // intersection (mark becomes 0 for "seen in this clause").
                for &d_lit in d_lits {
                    if d_lit == neg_lit {
                        continue;
                    }
                    if self.is_false(d_lit) || self.is_true(d_lit) {
                        continue;
                    }
                    let vi = d_lit.variable().index();
                    if vi < self.cla_marks.len() && self.cla_marks[vi] == d_lit.sign_i8() {
                        // Mark as "confirmed in this clause" by negating.
                        self.cla_marks[vi] = -self.cla_marks[vi];
                    }
                }

                // Sweep intersection: keep only literals that were confirmed.
                let marks = &mut self.cla_marks;
                self.intersection.retain(|&int_lit| {
                    let vi = int_lit.variable().index();
                    if vi >= marks.len() {
                        return false;
                    }
                    let mark = marks[vi];
                    if mark == -int_lit.sign_i8() {
                        // Was negated = confirmed in this clause. Restore mark.
                        marks[vi] = int_lit.sign_i8();
                        true
                    } else {
                        // Not seen in this clause. Remove from intersection.
                        marks[vi] = 0;
                        false
                    }
                });

                if self.intersection.is_empty() {
                    // Move-to-front heuristic: move the "killing" clause to
                    // front of occ list so future CLA iterations abort faster.
                    // CaDiCaL cover.cpp:286-292: shifts preceding elements
                    // right and inserts killer at front. We use swap(0, oi)
                    // which is O(1) and achieves the same effect.
                    self.occ.swap_to_front(neg_lit, oi);
                    break;
                }
            }
        }

        // Clear marks.
        for &int_lit in &self.intersection {
            let vi = int_lit.variable().index();
            if vi < self.cla_marks.len() {
                self.cla_marks[vi] = 0;
            }
        }

        if first {
            // ALL resolution candidates were blocked (satisfied).
            // The covered clause is blocked on `lit`.
            return CoverResult::Blocked(lit);
        }

        if self.intersection.is_empty() {
            return CoverResult::NoProgress;
        }

        // Intersection is non-empty: caller reads from self.intersection.
        CoverResult::Extended
    }
}

/// Result of CLA propagation for one literal.
enum CoverResult {
    /// All resolution candidates are satisfied — clause is blocked on this literal.
    Blocked(Literal),
    /// Intersection is non-empty — caller reads from `self.intersection`.
    Extended,
    /// Intersection is empty — no progress possible for this literal.
    NoProgress,
}
