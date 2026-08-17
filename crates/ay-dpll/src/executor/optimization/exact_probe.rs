// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact disposable decisions for quantified optimization obligations.

use ay_core::term::{TermEntryStamp, TermStoreSnapshotStamp};
use ay_core::TermId;
use ay_frontend::{Command, SourceContextStamp};

use super::{
    CheckedOptimizationDecision, Executor, QueryAuthorityEpoch,
    OPTIMIZATION_AUTHORITY_PROBE_BUDGET_MS,
};
use crate::ematching::contains_quantifier;
use crate::executor_types::SolveResult;

/// Outer identity of one disposable optimization obligation.
///
/// The nested executor authenticates its cloned context. This scope separately
/// proves that the clone and returned decision still name the same immutable
/// outer query and term universe.
struct OptimizationProbeScope {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[Option<TermEntryStamp>]>,
    term_snapshot: TermStoreSnapshotStamp,
}

impl OptimizationProbeScope {
    fn capture(executor: &Executor, roots: &[TermId]) -> Self {
        Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            roots: roots.into(),
            root_entries: roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root))
                .collect(),
            term_snapshot: executor.ctx.terms.snapshot_stamp(),
        }
    }

    fn is_current_for(&self, executor: &Executor, roots: &[TermId]) -> bool {
        self.query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.roots.as_ref() == roots
            && self.root_entries.iter().copied().eq(roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
            && self.term_snapshot == executor.ctx.terms.snapshot_stamp()
    }
}

impl Executor {
    /// Decide a quantified optimization subproblem without importing its model.
    ///
    /// SAT crosses the clone boundary only after the ordinary public emission
    /// funnel minted a complete certificate. UNSAT likewise requires strict,
    /// independent, or exact-semantic publication authority.
    pub(super) fn checked_optimization_quantified_decision(
        &mut self,
        roots: &[TermId],
    ) -> CheckedOptimizationDecision {
        if !self.optimization_probe_preflight() {
            return CheckedOptimizationDecision::Unknown;
        }
        let scope = OptimizationProbeScope::capture(self, roots);
        let Some(mut probe) = self.optimization_probe_executor(roots) else {
            return CheckedOptimizationDecision::Unknown;
        };
        let decision = match probe.check_sat() {
            Ok(SolveResult::Sat) => probe
                .take_sat_certificate()
                .is_some_and(|certificate| certificate.confirms_sat_emission())
                .then_some(CheckedOptimizationDecision::Sat),
            Ok(result @ SolveResult::Unsat(_)) => {
                let published = probe.certify_unsat_for_publication(result, &[]);
                let certified = probe.take_unsat_certificate().is_some_and(|certificate| {
                    certificate.strict_proof_verified()
                        || certificate.independently_verified()
                        || certificate.exact_semantic_verified()
                });
                (published.is_unsat() && certified).then_some(CheckedOptimizationDecision::Unsat)
            }
            Ok(SolveResult::Unknown) | Err(_) => None,
        };
        drop(probe);
        if !self.optimization_probe_preflight() || !scope.is_current_for(self, roots) {
            return CheckedOptimizationDecision::Unknown;
        }
        decision.unwrap_or(CheckedOptimizationDecision::Unknown)
    }

    /// Clone only when predictive resource checks say a disposable solver fits.
    fn optimization_probe_preflight(&mut self) -> bool {
        if self.should_abort_theory_loop()
            || ay_core::TermStore::global_memory_exceeded()
            || ay_sys::process_memory_exceeded_at_percent(50)
            || crate::memory::memory_exceeded(self.memory_limit())
        {
            return false;
        }
        if let Some(limit) = self.memory_limit() {
            let current = crate::memory::current_memory_bytes();
            if current > 0 && current > limit / 2 {
                return false;
            }
        }
        self.ctx.terms.true_memory_bytes() <= ay_core::TermStore::per_engine_budget() / 2
    }

    /// Build a public-query transaction over exactly `roots`, without carrying
    /// objectives, soft constraints, named-core state, or assertion scopes.
    fn optimization_probe_executor(&self, roots: &[TermId]) -> Option<Executor> {
        let mut probe_ctx = self.ctx.clone();
        probe_ctx.process_command(&Command::ResetAssertions).ok()?;
        probe_ctx.assertions = roots.to_vec();

        let mut probe = Executor::new();
        probe.ctx = probe_ctx;
        probe.set_verification_level(self.verification_level());
        probe.set_self_check(self.self_check());
        probe.set_learned_clause_limit(self.learned_clause_limit());
        probe.set_clause_db_bytes_limit(self.clause_db_bytes_limit());
        probe.set_resource_limit(self.resource_limit());
        probe.set_decision_limit(self.decision_limit());
        probe.set_ground_budget_enabled(self.ground_budget_enabled());
        probe.set_memory_limit(self.memory_limit());
        let tight = ay_core::time::Instant::now()
            + std::time::Duration::from_millis(OPTIMIZATION_AUTHORITY_PROBE_BUDGET_MS);
        let deadline = match self.solve_deadline.get() {
            Some(existing) if existing < tight => Some(existing),
            _ => Some(tight),
        };
        probe.set_solve_controls(self.solve_interrupt.clone(), deadline);
        probe.original_problem_had_quantifiers = roots
            .iter()
            .any(|&root| contains_quantifier(&probe.ctx.terms, root));
        probe.incremental_mode = false;
        probe.in_alternation_validation = true;
        probe.in_nested_array_residue_probe = true;
        probe.begin_public_solve(false);
        probe.bind_unsat_query_assumptions(&[]);
        Some(probe)
    }
}
