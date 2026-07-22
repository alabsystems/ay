// Copyright 2026 Andrew Yates
// Backward DRAT checking: verify only clauses needed for the empty clause
// derivation. Typically 10-100x faster than forward checking on industrial
// proofs. Algorithm from drat-trim (Heule & Wetzler 2014).
//
// Two-pass: (1) forward replay building clause DB + watches + trail, mark
// ACTIVE from empty clause; (2) backward walk verifying only ACTIVE steps,
// marking more clauses via MARK-based conflict analysis (drat-trim parity).

use crate::drat_parser::ProofStep;
use crate::error::DratCheckError;
use crate::literal::Literal;

use super::{ConcludeResult, DratChecker, Stats};

mod mark_active;
/// Record of a proof step with its clause index in the arena.
#[derive(Clone, Copy)]
struct StepRecord {
    cidx: usize,
    is_delete: bool,
    /// Trail length before this step was applied. Used to unwind
    /// transitive propagations when undoing additions in the backward pass.
    trail_len_before: usize,
}

/// Backward DRAT checker.
///
/// Wraps a `DratChecker` for the BCP engine and adds ACTIVE marking
/// and the two-pass backward algorithm. Reason tracking is handled by
/// `DratChecker.reasons` (set during BCP via `assign_with_reason`).
pub struct BackwardChecker {
    inner: DratChecker,
    /// ACTIVE flag per clause index. Only ACTIVE clauses are verified
    /// in the backward pass.
    active: Vec<bool>,
    /// Records of proof steps mapped to clause indices.
    step_records: Vec<StepRecord>,
    /// Number of original clauses (before proof steps).
    num_original: usize,
    /// Clause index where the empty clause was derived (or conflict detected).
    conflict_cidx: Option<usize>,
    /// Step index (into step_records/steps) where the conflict was found.
    conflict_step: Option<usize>,
}

impl BackwardChecker {
    pub fn new(num_vars: usize, check_rat: bool) -> Self {
        Self {
            inner: DratChecker::new(num_vars, check_rat),
            active: Vec::new(),
            step_records: Vec::new(),
            num_original: 0,
            conflict_cidx: None,
            conflict_step: None,
        }
    }

    pub fn stats(&self) -> &Stats {
        &self.inner.stats
    }

    /// Returns true if a clause at `cidx` was marked ACTIVE during
    /// backward verification. Used for testing dependency tracking.
    #[cfg(test)]
    pub(crate) fn is_active(&self, cidx: usize) -> bool {
        cidx < self.active.len() && self.active[cidx]
    }

    /// Returns true if `step_idx` is the conflict step.
    fn is_conflict_step(&self, step_idx: usize) -> bool {
        self.conflict_step == Some(step_idx)
    }

    /// Forward pass: add an original clause without verification.
    fn add_original_tracking(&mut self, clause: &[Literal]) {
        if self.inner.inconsistent {
            return;
        }
        self.inner.stats.original += 1;
        for &lit in clause {
            self.inner.ensure_capacity(lit.variable().index());
        }
        self.inner.add_clause_internal(clause);
        // Sync active array
        while self.active.len() < self.inner.clauses.len() {
            self.active.push(false);
        }
    }

    /// Forward pass: add a derived clause (no RUP/RAT check in forward replay).
    ///
    /// Returns the clause index if a clause was inserted, or `usize::MAX` if
    /// the clause was discarded (tautology, satisfied, or simplified to empty).
    fn add_derived_forward(&mut self, clause: &[Literal]) -> usize {
        self.inner.stats.additions += 1;
        for &lit in clause {
            self.inner.ensure_capacity(lit.variable().index());
        }
        let clauses_before = self.inner.clauses.len();
        self.inner.add_clause_internal(clause);
        while self.active.len() < self.inner.clauses.len() {
            self.active.push(false);
        }
        if self.inner.clauses.len() > clauses_before {
            self.inner.clauses.len() - 1
        } else {
            // Clause was discarded — no arena entry to reference.
            usize::MAX
        }
    }

    /// Forward pass: delete a clause. Removes watches and hash table entry
    /// but preserves clause data in the arena (unlike DratChecker::delete_clause
    /// which nulls it). The backward pass needs the clause data intact to
    /// restore watches when undoing deletions. Returns the clause index.
    fn delete_forward(&mut self, clause: &[Literal]) -> Option<usize> {
        self.inner.stats.deletions += 1;
        if let Some(cidx) = self.inner.find_clause_idx(clause) {
            // Pseudo-unit check: skip deletion if this clause is the reason
            // for its first literal's assignment (drat-trim.c:807).
            if self.inner.is_reason_for_first_lit(cidx) {
                self.inner.stats.pseudo_unit_skips += 1;
                return None;
            }
            // Remove watches only (clause stays in arena for backward pass).
            self.remove_watches(cidx);
            // Remove from hash table so duplicate deletions don't find it.
            let hash = DratChecker::hash_clause(clause);
            let bucket = self.inner.bucket_idx(hash);
            if let Some(bi) = self.inner.hash_buckets[bucket]
                .iter()
                .position(|&c| c == cidx)
            {
                self.inner.hash_buckets[bucket].swap_remove(bi);
            }
            self.inner.remove_clause_occurrences(cidx);
            self.inner.live_clauses -= 1;
            Some(cidx)
        } else {
            self.inner.stats.missed_deletes += 1;
            None
        }
    }

    /// Verify a complete proof using backward checking.
    ///
    /// Pass 1: Forward replay of all proof steps (no verification).
    /// Pass 2: Backward walk verifying only ACTIVE clauses.
    pub fn verify(
        &mut self,
        clauses: &[Vec<Literal>],
        steps: &[ProofStep],
    ) -> Result<(), DratCheckError> {
        // ── Pass 1: Forward replay ───────────────────────────────────
        for clause in clauses {
            self.add_original_tracking(clause);
        }
        self.num_original = self.inner.clauses.len();

        if self.inner.inconsistent {
            // Formula already UNSAT from original clauses
            return Ok(());
        }

        for (step_i, step) in steps.iter().enumerate() {
            match step {
                ProofStep::Add(lits) => {
                    let trail_before = self.inner.trail.len();
                    let cidx = self.add_derived_forward(lits);
                    self.step_records.push(StepRecord {
                        cidx,
                        is_delete: false,
                        trail_len_before: trail_before,
                    });
                    if (lits.is_empty() || self.inner.inconsistent) && self.conflict_cidx.is_none()
                    {
                        self.conflict_cidx = Some(cidx);
                        self.conflict_step = Some(step_i);
                        // Mark conflict clause + full dependency chain (drat-trim analyze()).
                        if cidx != usize::MAX {
                            self.mark_active(cidx);
                        }
                        // Mark the BCP conflict clause (if different from cidx)
                        // and all trail reason clauses. This mirrors drat-trim's
                        // analyze() which walks the trail from the conflict
                        // backward through all reason clauses (#5258 bug 2).
                        if let Some(bcp_cidx) = self.inner.bcp_conflict_cidx {
                            self.mark_active(bcp_cidx);
                        }
                        self.mark_trail_reasons_active();
                    }
                }
                ProofStep::Delete(lits) => {
                    let cidx = self.delete_forward(lits);
                    self.step_records.push(StepRecord {
                        cidx: cidx.unwrap_or(usize::MAX),
                        is_delete: true,
                        trail_len_before: self.inner.trail.len(),
                    });
                }
                ProofStep::AddPr { clause, .. } => {
                    // PR/DPR additions are outside the RUP/RAT trusted fragment;
                    // fail closed (see forward checker + DratCheckError::UnsupportedPr).
                    return Err(DratCheckError::UnsupportedPr {
                        clause: format!("{clause:?}"),
                    });
                }
            }
        }

        if let ConcludeResult::Failed(reason) = self.inner.conclude_unsat() {
            return Err(DratCheckError::from(reason));
        }

        // ── Pass 2: Backward verification ────────────────────────────
        // Reset inconsistent so check_rup doesn't short-circuit (#5258).
        self.inner.inconsistent = false;
        // Core-first BCP (drat-trim.c:196 `mode = !S->prep`).
        self.inner.prep = false;
        self.inner.core_first = true;

        for step_idx in (0..self.step_records.len()).rev() {
            let record = self.step_records[step_idx];

            if record.is_delete {
                // Undo deletion: restore watches + hash entry (arena data intact).
                if record.cidx != usize::MAX {
                    self.restore_clause(record.cidx);
                }
                continue;
            }

            // Undoing an addition: remove from clause DB
            let cidx = record.cidx;

            if cidx == usize::MAX {
                // Discarded clause (tautology/satisfied/empty). No arena entry,
                // but ACTIVE ones still need verification.
                self.inner.backtrack(record.trail_len_before);
                if self.conflict_cidx == Some(usize::MAX) && self.is_conflict_step(step_idx) {
                    // ACTIVE empty clause — reset inconsistent for RUP check.
                    self.inner.inconsistent = false;
                    let clause = match &steps[step_idx] {
                        ProofStep::Add(lits) => lits,
                        _ => continue,
                    };
                    let result = self.inner.check_rup_with_deps(clause);
                    if !result.is_rup {
                        self.inner.stats.failures += 1;
                        let lits: Vec<_> = clause.iter().map(ToString::to_string).collect();
                        return Err(DratCheckError::NotImplied {
                            clause: format!("backward: ACTIVE discarded {lits:?}"),
                            step: (step_idx + 1) as u64,
                            kind: "RUP ",
                        });
                    }
                    self.mark_deps_active(&result.deps);
                    // No clause reduction for discarded clauses (no arena entry).
                }
                continue;
            }

            self.remove_watches(cidx);
            self.inner.backtrack(record.trail_len_before);

            if cidx >= self.active.len() || !self.active[cidx] {
                // Not ACTIVE — skip verification
                // Remove from clause DB
                self.inner.clauses[cidx] = None;
                continue;
            }

            // ACTIVE clause — must verify via RUP/RAT.
            // Remove the arena clause (it shouldn't be used to prove itself).
            self.inner.clauses[cidx] = None;

            // Use the ORIGINAL proof step literals for the RUP check, not the
            // arena clause. add_clause_internal simplifies clauses during the
            // forward pass (removes falsified literals), but drat-trim stores
            // unsimplified clauses and reduces them during the backward pass.
            let clause = match &steps[step_idx] {
                ProofStep::Add(lits) => lits.clone(),
                _ => continue, // should not happen for additions
            };
            let clause = self.reduce_clause(clause);

            // Check RUP with precise dependency tracking (MARK-based,
            // mirrors drat-trim analyze()). Collects the exact set of
            // clause indices in the resolution proof chain BEFORE
            // backtracking the trail. Also identifies ASSUMED literals
            // that were unused in the conflict derivation (clause reduction,
            // drat-trim.c:174-179).
            let result = self.inner.check_rup_with_deps(&clause);
            if result.is_rup {
                // Adaptive prep toggle (drat-trim.c:647-652).
                let indegree = result.deps.len();
                if indegree <= 2 && !self.inner.prep {
                    self.inner.prep = true;
                    self.inner.core_first = false;
                } else if indegree > 2 && self.inner.prep {
                    self.inner.prep = false;
                    self.inner.core_first = true;
                }
                self.mark_deps_active(&result.deps);
                // Clause reduction: remove ASSUMED literals that were not
                // needed for the conflict derivation (drat-trim.c:174-179).
                if !result.reducible_positions.is_empty() {
                    let reduced = reduce_clause(&clause, &result.reducible_positions);
                    self.inner.stats.reduced_literals += result.reducible_positions.len() as u64;
                    self.inner.clauses[cidx] = Some(reduced);
                }
                continue;
            }

            // Check RAT with ACTIVE filtering (drat-trim.c:565-567).
            // In backward mode, non-ACTIVE clauses are skipped as resolution
            // candidates — they're not part of the proof core.
            // No clause reduction for RAT (drat-trim.c:175: `!S->RATmode`).
            if self.inner.check_rat && !clause.is_empty() && self.check_rat_backward(&clause) {
                continue;
            }

            self.inner.stats.failures += 1;
            let lits: Vec<_> = clause.iter().map(ToString::to_string).collect();
            return Err(DratCheckError::NotImplied {
                clause: format!("backward: ACTIVE {lits:?}"),
                step: (step_idx + 1) as u64,
                kind: "RUP/RAT ",
            });
        }

        Ok(())
    }
}

/// Remove literals at the given positions from a clause.
/// Positions must be sorted ascending. drat-trim.c:174-179.
fn reduce_clause(clause: &[Literal], positions: &[usize]) -> Vec<Literal> {
    let mut reduced = Vec::with_capacity(clause.len() - positions.len());
    let mut remove_iter = positions.iter().peekable();
    for (i, &lit) in clause.iter().enumerate() {
        if remove_iter.peek() == Some(&&i) {
            remove_iter.next();
        } else {
            reduced.push(lit);
        }
    }
    reduced
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_backward_rejection;
#[cfg(test)]
mod tests_boundary;
#[cfg(test)]
mod tests_clause_reduction;
#[cfg(test)]
mod tests_core_first;
#[cfg(test)]
mod tests_exhaustive;
#[cfg(test)]
mod tests_proptest;
#[cfg(test)]
mod tests_rat;
#[cfg(test)]
mod tests_regression;
