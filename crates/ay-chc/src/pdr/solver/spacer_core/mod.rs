// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Spacer-faithful lemma side of the PDR blocking loop (Workstream B,
//! the development design notes at `9598c4206`, §4.2).
//!
//! Owner: **WP-B1-L** (lemma core). This module tree was declared in the
//! skeleton commit by WP-B1-S with the frozen §3 signatures; bodies marked
//! `todo!()` are L's to fill. S dispatches into [`PdrSolver::block_linear`]
//! from `blocking/mod.rs` after the syntactic checks (contract C4) only when
//! `self.spacer_core && self.linear_pred(pob.predicate)`; nothing here runs
//! with the lane OFF.
//!
//! Sub-modules:
//! - [`oracle`]  — `ClauseQuery`, `Hyp`, `Verdict`, `Budget`, the one oracle
//!   (`oracle_check_clause`, `oracle_check_all_clauses`) and C3's
//!   `q1_core_for_clause`.
//! - [`derive`]  — `lemma_from_cores`: Phases 0/A/B/C/D, budgets, within-run CTP.
//! - [`ddmin`]   — QuickXplain over a monotone predicate.
//! - [`stats`]   — `SpacerCoreStats` counters (C7), wired by S into
//!   `SolverStats`, the trace telemetry block and the verbose line.
//!
//! Soundness invariants S1–S11 (`DESIGN` §6) apply to every body here; in
//! particular every inserted lemma must be backed by an OBSERVED UNSAT at its
//! level (S2) and an exclusion-dependent block returns `Unknown` (S3).

#![allow(dead_code, unused)]

pub(in crate::pdr::solver) mod ddmin;
pub(in crate::pdr::solver) mod derive;
pub(in crate::pdr::solver) mod oracle;
pub(in crate::pdr::solver) mod stats;

#[cfg(test)]
mod tests;

#[cfg(test)]
#[path = "nonlinear_tests.rs"]
mod nonlinear_tests;

pub(in crate::pdr::solver) use derive::DeriveError;
pub(in crate::pdr::solver) use oracle::{Budget, ClauseQuery, Hyp, OracleBackend, Verdict};
pub(in crate::pdr::solver) use stats::SpacerCoreStats;

use super::{blocking, BlockResult, ChcExpr, PdrSolver, PredicateId, ProofObligation};

impl PdrSolver {
    /// Every defining clause of `pred` is a fact or has exactly one body
    /// predicate (cached at construction in `linear_pred_cache`, C5).
    pub(in crate::pdr::solver) fn linear_pred(&self, pred: PredicateId) -> bool {
        self.linear_pred_cache
            .get(pred.index())
            .copied()
            .unwrap_or(false)
    }

    /// Replacement of `blocking/mod.rs` steps 1–2 for spacer_core linear
    /// predicates (contract C4; `DESIGN` §4.2.1).
    ///
    /// 1. NO already-blocked pre-check unless `spacer.already_blocked_fastpath`
    ///    (Q1 subsumes it; a fast-path hit still yields a lemma through
    ///    `lemma_from_cores` on an uncovered seed — Phase A/B do the work).
    /// 2. `level ≥ 1`: `check_predecessor_reachability(pob, unknown_predecessors)`
    ///    → `Err(Reachable | Unknown)` returned as is.
    ///    `level 0`: the per-fact loop `level0_fact_reachability` (S keeps it;
    ///    it fills `cores` per fact through C3).
    /// 3. `Ok(data)` ⇒ `lemma_from_cores(pob, &data.cores, unknown_predecessors)`:
    ///    `Ok(lemma) ⇒ Blocked(lemma)`, `Err(ExclusionDependent) ⇒ Unknown` (INV-L3, D4),
    ///    `Err(SeedRefuted) ⇒ Unknown` (the oracle has a model of the full cube: the
    ///    Q1 UNSAT is no sound justification; expected 0, fail-closed).
    ///
    /// A lemma is ALWAYS produced for a blocked POB; `Unknown` from here
    /// arises only from cancellation / SMT `Unknown` on the reachability side,
    /// INV-L3 or a refuted seed (lock L2; `pending_unknown_class` names the class).
    pub(in crate::pdr::solver) fn block_linear(
        &mut self,
        pob: &mut ProofObligation,
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
    ) -> BlockResult {
        use stats::UnknownClass;
        let mut fastpath_blocked = false;
        if self.config.spacer.already_blocked_fastpath && pob.level >= 1 {
            if let Some(frame) = self.frame_hyp(pob.level, pob.predicate) {
                let query = self.bound_int_vars(ChcExpr::and(frame, pob.state.clone()));
                self.spacer_stats.smt_solves_total += 1;
                if matches!(
                    self.check_sat_via_executor_backend(&query),
                    crate::smt::SmtResult::Unsat
                        | crate::smt::SmtResult::UnsatWithCore(_)
                        | crate::smt::SmtResult::UnsatWithFarkas(_)
                ) {
                    self.spacer_stats.already_blocked_smt += 1;
                    fastpath_blocked = true;
                }
            }
        }
        let cores: Vec<blocking::ClauseCore> = if fastpath_blocked {
            Vec::new()
        } else {
            let reach = if pob.level == 0 {
                self.level0_fact_reachability(pob)
            } else {
                self.check_predecessor_reachability(pob, unknown_predecessors)
            };
            match reach {
                Ok(data) => data.cores,
                Err(result) => {
                    if matches!(result, BlockResult::Unknown)
                        && self.pending_unknown_class.is_none()
                    {
                        self.pending_unknown_class = Some(if self.is_cancelled() {
                            UnknownClass::Cancelled
                        } else {
                            UnknownClass::SmtUnknown
                        });
                    }
                    return result;
                }
            }
        };
        if self.is_cancelled() {
            self.pending_unknown_class = Some(UnknownClass::Cancelled);
            return BlockResult::Unknown;
        }
        match self.lemma_from_cores(pob, &cores, unknown_predecessors) {
            Ok(lemma) => BlockResult::Blocked(lemma),
            Err(DeriveError::ExclusionDependent) => {
                self.spacer_stats.q1_exclusion_dependent += 1;
                self.pending_unknown_class = Some(UnknownClass::ExclusionDependent);
                BlockResult::Unknown
            }
            Err(DeriveError::SeedRefuted) => {
                self.pending_unknown_class = Some(UnknownClass::SeedRefuted);
                BlockResult::Unknown
            }
        }
    }
}
