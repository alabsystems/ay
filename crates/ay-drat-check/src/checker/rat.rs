// Copyright 2026 Andrew Yates
// RAT (Resolution Asymmetric Tautology) checking for the DRAT proof checker.
// Matches drat-trim's pivot fallback behavior (drat-trim.c:662-683).

use super::DratChecker;
use crate::literal::Literal;

/// Result of a RAT check with dependency tracking.
pub(super) struct RatDepsResult {
    pub(super) success: bool,
    /// Clause indices of resolution candidates (clauses containing ¬pivot).
    pub(super) candidate_indices: Vec<usize>,
    /// Clause indices from RUP proof chains of each resolvent.
    pub(super) rup_deps: Vec<usize>,
}

impl DratChecker {
    /// Check if `clause` is RAT. Tries the first literal as pivot (standard),
    /// then falls back to all other literals if that fails (drat-trim parity).
    pub(super) fn check_rat_for_clause(&mut self, clause: &[Literal]) -> bool {
        if clause.is_empty() {
            return false;
        }
        self.stats.rat_checks += 1;
        // Try the first literal (the default pivot for most solvers).
        if self.check_rat_with_pivot(clause, clause[0], None) {
            return true;
        }
        // Pivot fallback: try remaining literals (drat-trim.c:662-683).
        for &alt_pivot in &clause[1..] {
            if self.check_rat_with_pivot(clause, alt_pivot, None) {
                return true;
            }
        }
        false
    }

    /// Collect resolution candidate indices for a given pivot, optionally
    /// filtering by ACTIVE status.
    fn collect_rat_candidates(&self, pivot: Literal, active_filter: Option<&[bool]>) -> Vec<usize> {
        let neg_pivot = pivot.negated();
        self.occ_lists
            .get(neg_pivot.index())
            .into_iter()
            .flatten()
            .copied()
            .filter(|&cidx| {
                if let Some(active) = active_filter {
                    if cidx >= active.len() || !active[cidx] {
                        return false;
                    }
                }
                self.clauses[cidx]
                    .as_ref()
                    .is_some_and(|c| c.contains(&neg_pivot))
            })
            .collect()
    }

    /// Build the resolvent of `clause` and `db_clause` on `pivot` into the
    /// provided buffer. Returns whether it is tautological.
    ///
    /// Literal marks provide linear-time duplicate removal and tautology
    /// detection, avoiding a sort of every RAT resolvent.
    fn build_resolvent_into(
        marks: &mut [bool],
        buf: &mut Vec<Literal>,
        clause: &[Literal],
        db_clause: &[Literal],
        pivot: Literal,
    ) -> bool {
        let neg_pivot = pivot.negated();
        buf.clear();
        let mut tautological = false;
        for lit in clause
            .iter()
            .copied()
            .filter(|&lit| lit != pivot)
            .chain(db_clause.iter().copied().filter(|&lit| lit != neg_pivot))
        {
            if marks[lit.negated().index()] {
                tautological = true;
                break;
            }
            if !marks[lit.index()] {
                marks[lit.index()] = true;
                buf.push(lit);
            }
        }
        for &lit in buf.iter() {
            marks[lit.index()] = false;
        }
        tautological
    }

    /// Check if `clause` is RAT with the given pivot, optionally filtering
    /// resolution candidates by ACTIVE status.
    ///
    /// For each clause in the database containing `¬pivot`, the resolvent
    /// (clause ∪ db_clause \ {pivot, ¬pivot}) must be RUP.
    ///
    /// When `active_filter` is provided (backward mode), clauses where
    /// `!active[cidx]` are skipped (drat-trim.c:565-567).
    pub(super) fn check_rat_with_pivot(
        &mut self,
        clause: &[Literal],
        pivot: Literal,
        active_filter: Option<&[bool]>,
    ) -> bool {
        let candidate_indices = self.collect_rat_candidates(pivot, active_filter);

        for cidx in candidate_indices {
            let db_clause = match &self.clauses[cidx] {
                Some(c) => c,
                None => continue,
            };

            // Build resolvent into scratch buffer. We take the buffer out of
            // self to avoid holding a borrow on self.clauses while mutating.
            let mut scratch = std::mem::take(&mut self.scratch_resolvent);
            let tautological =
                Self::build_resolvent_into(&mut self.marks, &mut scratch, clause, db_clause, pivot);

            if tautological {
                self.scratch_resolvent = scratch;
                continue;
            }

            let rup_ok = self.check_rup(&scratch);
            self.scratch_resolvent = scratch;

            if !rup_ok {
                return false;
            }
        }
        true
    }

    /// Like `check_rat_with_pivot`, but also collects dependency information:
    /// the resolution candidate clause indices and RUP proof chain clause
    /// indices. Used by the backward checker to mark these clauses ACTIVE.
    ///
    /// Mirrors drat-trim's backward RAT behavior:
    /// - `addDependency(S, -id, 1)` for each candidate (drat-trim.c:605)
    /// - `propagate(S, 0, mark)` → `analyze()` → `markClause()` for RUP
    ///   deps (drat-trim.c:604)
    pub(super) fn check_rat_with_pivot_deps(
        &mut self,
        clause: &[Literal],
        pivot: Literal,
        active_filter: Option<&[bool]>,
    ) -> RatDepsResult {
        let candidate_indices = self.collect_rat_candidates(pivot, active_filter);
        let mut all_rup_deps = Vec::new();
        let mut used_candidates = Vec::new();

        for cidx in candidate_indices {
            let db_clause = match &self.clauses[cidx] {
                Some(c) => c,
                None => continue,
            };

            let mut scratch = std::mem::take(&mut self.scratch_resolvent);
            let tautological =
                Self::build_resolvent_into(&mut self.marks, &mut scratch, clause, db_clause, pivot);

            if tautological {
                self.scratch_resolvent = scratch;
                continue;
            }

            let rup_result = self.check_rup_with_deps(&scratch);
            self.scratch_resolvent = scratch;

            if !rup_result.is_rup {
                return RatDepsResult {
                    success: false,
                    candidate_indices: Vec::new(),
                    rup_deps: Vec::new(),
                };
            }
            used_candidates.push(cidx);
            all_rup_deps.extend(rup_result.deps);
        }

        RatDepsResult {
            success: true,
            candidate_indices: used_candidates,
            rup_deps: all_rup_deps,
        }
    }
}
