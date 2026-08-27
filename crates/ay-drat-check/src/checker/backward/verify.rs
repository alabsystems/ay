// Copyright 2026 Andrew Yates
// Backward DRAT proof replay and ACTIVE-clause verification.

use crate::drat_parser::ProofStep;
use crate::error::DratCheckError;
use crate::literal::Literal;

use super::super::{ConcludeResult, DratChecker};
use super::{reduce_clause, BackwardChecker, StepRecord};

enum ForwardReplay {
    AlreadyVerified,
    NeedsBackwardPass,
}

impl BackwardChecker {
    /// Verify a complete proof using backward checking on a fresh checker.
    ///
    /// Pass 1 replays all proof steps without verification. Pass 2 walks the
    /// proof backward and verifies only ACTIVE clauses. This bulk API is
    /// one-shot: a repeated call fails with [`DratCheckError::CheckerNotFresh`]
    /// rather than reusing clauses or a contradiction from an earlier formula.
    pub fn verify(
        &mut self,
        clauses: &[Vec<Literal>],
        steps: &[ProofStep],
    ) -> Result<(), DratCheckError> {
        self.inner.begin_bulk_verify()?;
        match self.replay_forward(clauses, steps)? {
            ForwardReplay::AlreadyVerified => Ok(()),
            ForwardReplay::NeedsBackwardPass => {
                self.prepare_backward_pass();
                self.verify_backward_steps(steps)
            }
        }
    }

    fn replay_forward(
        &mut self,
        clauses: &[Vec<Literal>],
        steps: &[ProofStep],
    ) -> Result<ForwardReplay, DratCheckError> {
        for clause in clauses {
            self.add_original_tracking(clause);
        }
        self.num_original = self.inner.clauses.len();

        if self.inner.inconsistent {
            return match self.inner.conclude_unsat() {
                ConcludeResult::Verified => Ok(ForwardReplay::AlreadyVerified),
                ConcludeResult::Failed(reason) => Err(DratCheckError::from(reason)),
            };
        }

        for (step_idx, step) in steps.iter().enumerate() {
            self.replay_forward_step(step_idx, step)?;
        }

        if let ConcludeResult::Failed(reason) = self.inner.conclude_unsat() {
            return Err(DratCheckError::from(reason));
        }
        Ok(ForwardReplay::NeedsBackwardPass)
    }

    fn replay_forward_step(
        &mut self,
        step_idx: usize,
        step: &ProofStep,
    ) -> Result<(), DratCheckError> {
        match step {
            ProofStep::Add(lits) => self.replay_forward_addition(step_idx, lits),
            ProofStep::Delete(lits) => {
                let cidx = self.delete_forward(lits).unwrap_or(usize::MAX);
                self.step_records.push(StepRecord {
                    cidx,
                    is_delete: true,
                    trail_len_before: self.inner.trail.len(),
                });
            }
            ProofStep::AddPr { clause, .. } => {
                // PR/DPR additions are outside the RUP/RAT trusted fragment.
                return Err(DratCheckError::UnsupportedPr {
                    clause: format!("{clause:?}"),
                });
            }
        }
        Ok(())
    }

    fn replay_forward_addition(&mut self, step_idx: usize, lits: &[Literal]) {
        let trail_len_before = self.inner.trail.len();
        let cidx = self.add_derived_forward(lits);
        self.step_records.push(StepRecord {
            cidx,
            is_delete: false,
            trail_len_before,
        });

        if (lits.is_empty() || self.inner.inconsistent) && self.conflict_cidx.is_none() {
            self.record_forward_conflict(step_idx, cidx);
        }
    }

    fn record_forward_conflict(&mut self, step_idx: usize, cidx: usize) {
        self.conflict_cidx = Some(cidx);
        self.conflict_step = Some(step_idx);
        if cidx != usize::MAX {
            self.mark_active(cidx);
        }
        // Mirror drat-trim's analyze(): mark the BCP conflict and all trail
        // reason clauses, including when the added clause was simplified away.
        if let Some(bcp_cidx) = self.inner.bcp_conflict_cidx {
            self.mark_active(bcp_cidx);
        }
        self.mark_trail_reasons_active();
    }

    /// Forward pass: add an original clause without verification.
    pub(super) fn add_original_tracking(&mut self, clause: &[Literal]) {
        if self.inner.inconsistent {
            return;
        }
        self.inner.stats.original += 1;
        for &lit in clause {
            self.inner.ensure_capacity(lit.variable().index());
        }
        self.inner.add_clause_internal(clause);
        while self.active.len() < self.inner.clauses.len() {
            self.active.push(false);
        }
    }

    /// Forward pass: add a derived clause without a RUP/RAT check.
    pub(super) fn add_derived_forward(&mut self, clause: &[Literal]) -> usize {
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
            usize::MAX
        }
    }

    /// Forward pass: soft-delete a clause while retaining its arena entry.
    pub(super) fn delete_forward(&mut self, clause: &[Literal]) -> Option<usize> {
        self.inner.stats.deletions += 1;
        let Some(cidx) = self.inner.find_clause_idx(clause) else {
            self.inner.stats.missed_deletes += 1;
            return None;
        };
        if self.inner.is_reason_for_first_lit(cidx) {
            self.inner.stats.pseudo_unit_skips += 1;
            return None;
        }

        self.remove_watches(cidx);
        let hash = DratChecker::hash_clause(clause);
        let bucket = self.inner.bucket_idx(hash);
        if let Some(position) = self.inner.hash_buckets[bucket]
            .iter()
            .position(|&candidate| candidate == cidx)
        {
            self.inner.hash_buckets[bucket].swap_remove(position);
        }
        self.inner.remove_clause_occurrences(cidx);
        self.inner.live_clauses -= 1;
        Some(cidx)
    }

    fn prepare_backward_pass(&mut self) {
        // Do not let the forward conflict short-circuit subsequent RUP checks.
        self.inner.inconsistent = false;
        // Core-first BCP (drat-trim.c:196 `mode = !S->prep`).
        self.inner.prep = false;
        self.inner.core_first = true;
    }

    fn verify_backward_steps(&mut self, steps: &[ProofStep]) -> Result<(), DratCheckError> {
        for step_idx in (0..self.step_records.len()).rev() {
            self.verify_backward_step(step_idx, steps)?;
        }
        Ok(())
    }

    fn verify_backward_step(
        &mut self,
        step_idx: usize,
        steps: &[ProofStep],
    ) -> Result<(), DratCheckError> {
        let record = self.step_records[step_idx];
        if record.is_delete {
            if record.cidx != usize::MAX {
                self.restore_clause(record.cidx);
            }
            return Ok(());
        }
        if record.cidx == usize::MAX {
            return self.verify_discarded_step(step_idx, record.trail_len_before, steps);
        }

        self.remove_watches(record.cidx);
        self.inner.backtrack(record.trail_len_before);
        if record.cidx >= self.active.len() || !self.active[record.cidx] {
            self.inner.clauses[record.cidx] = None;
            return Ok(());
        }
        self.verify_active_addition(step_idx, record.cidx, &steps[step_idx])
    }

    fn verify_discarded_step(
        &mut self,
        step_idx: usize,
        trail_len_before: usize,
        steps: &[ProofStep],
    ) -> Result<(), DratCheckError> {
        self.inner.backtrack(trail_len_before);
        if self.conflict_cidx != Some(usize::MAX) || !self.is_conflict_step(step_idx) {
            return Ok(());
        }

        self.inner.inconsistent = false;
        let ProofStep::Add(clause) = &steps[step_idx] else {
            return Ok(());
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
        Ok(())
    }

    fn verify_active_addition(
        &mut self,
        step_idx: usize,
        cidx: usize,
        step: &ProofStep,
    ) -> Result<(), DratCheckError> {
        // The ACTIVE clause cannot be used to prove itself.
        self.inner.clauses[cidx] = None;
        let ProofStep::Add(clause) = step else {
            return Ok(());
        };
        // Forward insertion simplifies clauses. Backward checking starts from
        // the original proof literals, as drat-trim does.
        let clause = self.reduce_clause(clause.clone());
        let result = self.inner.check_rup_with_deps(&clause);
        if result.is_rup {
            self.accept_active_rup(cidx, &clause, &result.deps, &result.reducible_positions);
            return Ok(());
        }
        if self.inner.check_rat && !clause.is_empty() && self.check_rat_backward(&clause) {
            return Ok(());
        }

        self.inner.stats.failures += 1;
        let lits: Vec<_> = clause.iter().map(ToString::to_string).collect();
        Err(DratCheckError::NotImplied {
            clause: format!("backward: ACTIVE {lits:?}"),
            step: (step_idx + 1) as u64,
            kind: "RUP/RAT ",
        })
    }

    fn accept_active_rup(
        &mut self,
        cidx: usize,
        clause: &[Literal],
        deps: &[usize],
        reducible_positions: &[usize],
    ) {
        let indegree = deps.len();
        if indegree <= 2 && !self.inner.prep {
            self.inner.prep = true;
            self.inner.core_first = false;
        } else if indegree > 2 && self.inner.prep {
            self.inner.prep = false;
            self.inner.core_first = true;
        }
        self.mark_deps_active(deps);

        if !reducible_positions.is_empty() {
            let reduced = reduce_clause(clause, reducible_positions);
            self.inner.stats.reduced_literals += reducible_positions.len() as u64;
            self.inner.clauses[cidx] = Some(reduced);
        }
    }

    fn is_conflict_step(&self, step_idx: usize) -> bool {
        self.conflict_step == Some(step_idx)
    }
}
