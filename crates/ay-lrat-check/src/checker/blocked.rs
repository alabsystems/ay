// Copyright 2026 Andrew Yates
// Blocked clause (extended resolution) check for the LRAT checker.
//
// Verifies extended resolution proofs where the hint chain contains negative
// IDs. A clause is "blocked" if there exists a literal such that every
// non-exempt clause containing the negation of that literal resolves
// tautologically with the imported clause.
//
// Optimization (#5330): Uses occ_lists for the elimination pass instead of
// scanning the entire clause database. Proof-chain clauses (neg_ids) are
// looked up directly by ID.
//
// Reference: CaDiCaL lratchecker.cpp:384-444 (check_blocked).

use crate::dimacs::Literal;
use ay_core::kani_compat::DetHashSet as HashSet;

use super::LratChecker;

impl LratChecker {
    /// Verify an extended resolution (ER) blocked clause.
    ///
    /// Called when RUP+resolution fails. Handles proof chains with negative
    /// hint IDs (ER definitions).
    ///
    /// Algorithm (CaDiCaL lratchecker.cpp:384-444):
    /// 1. Mark imported clause negation in `checked_lits` and `marks`.
    ///    2a. Process proof-chain clauses (neg_ids) by direct ID lookup.
    ///    2b. Use occurrence lists to find non-proof-chain clauses that overlap
    ///    with negated imported clause literals — eliminates O(n) full scan.
    /// 3. If any RAT candidate survives, the clause is blocked → PASS.
    ///
    /// Reference: CaDiCaL lratchecker.cpp:384-444.
    pub(super) fn check_blocked(&mut self, clause: &[Literal], hints: &[i64]) -> bool {
        // Build set of negated hint IDs for O(1) lookup.
        let neg_ids: HashSet<u64> = hints
            .iter()
            .filter(|&&h| h < 0)
            .map(|&h| {
                debug_assert!(h != i64::MIN, "hint i64::MIN would overflow on negation");
                (-h) as u64
            })
            .collect();

        // Phase 1: Mark imported clause negation.
        for &lit in clause {
            let neg = lit.negated();
            self.ensure_mark_capacity(neg);
            self.checked_lits[neg.index()] = true;
            self.marks[neg.index()] = true;
        }

        // Verify all negative-ID clauses exist. If any witness clause is missing,
        // the blocked check cannot succeed (no clause to resolve against).
        for &neg_id in &neg_ids {
            if !self.clause_index.contains_key(&neg_id) {
                self.cleanup_blocked_marks(clause);
                return false;
            }
        }

        // Phase 2a: Process proof-chain clauses by direct ID lookup (#5330).
        // Each neg_id clause must be blocked (count >= 2 overlapping literals).
        let mut ok = true;
        for &neg_id in &neg_ids {
            let entry = match self.clause_index.get(&neg_id) {
                Some(&e) => e,
                None => {
                    ok = false;
                    break;
                }
            };
            let start = entry.start as usize;
            let end = start + entry.len as usize;

            debug_assert!(self.checked_stack.is_empty());
            for i in start..end {
                let lit = self.clause_arena[i];
                if lit.index() < self.checked_lits.len() && self.checked_lits[lit.index()] {
                    // Toggle each overlap only once. The dirty stack records
                    // the distinct indices and lets us restore checked_lits
                    // without allocating a set for every witness clause.
                    self.checked_lits[lit.index()] = false;
                    self.checked_stack.push(lit.index());
                }
            }
            // A tautological resolvent needs two *distinct* complementary
            // literals.  Repeated occurrences of the same literal in a
            // malformed or non-normalized input clause must not be counted as
            // separate overlaps: D = (~p v ~p) does not make the resolvent of
            // C = (p) tautological.
            if self.checked_stack.len() < 2 {
                self.restore_blocked_overlaps();
                ok = false;
                break;
            }
            // Narrow candidates: remove marks for imported literals whose
            // negation is NOT in the candidate set.
            for &lit in clause {
                let neg = lit.negated();
                if neg.index() < self.marks.len()
                    && self.marks[neg.index()]
                    && self.checked_lits[neg.index()]
                {
                    self.marks[neg.index()] = false;
                }
            }
            self.restore_blocked_overlaps();
        }

        // Phase 2b: Elimination pass using occurrence lists (#5330).
        // For each negated imported literal, check if any non-proof-chain clause
        // in the occurrence list contains it. If so, that literal is not a valid
        // RAT candidate. This replaces the O(|clause_index|) full database scan
        // with O(|clause| * avg_occ) occurrence list iteration.
        if ok {
            for &lit in clause {
                let neg = lit.negated();
                let neg_idx = neg.index();
                if neg_idx >= self.marks.len() || !self.marks[neg_idx] {
                    continue; // Already eliminated or out of range
                }
                if neg_idx < self.occ_lists.len() {
                    // Collect clause IDs from occ_list to avoid borrowing self
                    // during the check (occ_lists is not mutated here but we
                    // need clause_index access).
                    let occ = &self.occ_lists[neg_idx];
                    let mut found_eliminator = false;
                    for &cid in occ {
                        if neg_ids.contains(&cid) {
                            continue; // Proof-chain clause, already handled
                        }
                        if self.clause_index.contains_key(&cid) {
                            // Active non-proof-chain clause contains this literal.
                            // This eliminates `neg` as a RAT candidate.
                            found_eliminator = true;
                            break;
                        }
                        // Lazy deletion: clause was deleted, skip
                    }
                    if found_eliminator {
                        self.marks[neg_idx] = false;
                    }
                }
            }
        }

        // Phase 3: Check if any RAT candidate survives.
        let success = ok
            && clause.iter().any(|&lit| {
                let neg = lit.negated();
                neg.index() < self.marks.len() && self.marks[neg.index()]
            });

        self.cleanup_blocked_marks(clause);
        success
    }

    /// Clear `checked_lits` and `marks` for all negated imported clause literals.
    fn cleanup_blocked_marks(&mut self, clause: &[Literal]) {
        for &lit in clause {
            let neg = lit.negated();
            if neg.index() < self.checked_lits.len() {
                self.checked_lits[neg.index()] = false;
            }
            if neg.index() < self.marks.len() {
                self.marks[neg.index()] = false;
            }
        }
    }

    /// Restore imported-clause marks toggled while scanning one witness.
    #[inline]
    fn restore_blocked_overlaps(&mut self) {
        while let Some(idx) = self.checked_stack.pop() {
            self.checked_lits[idx] = true;
        }
    }
}
