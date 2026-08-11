// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Verification level, counterexample style, timeout/memory/clause limits,
//! interrupt, unknown reason, and statistics accessors.

use ay_core::time::Instant;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use crate::api::types::{
    AssumptionSolveDetails, LimitKind, ResourceUsage, SolveDetails, Term, UnknownDiagnostic,
    VerificationLevel, VerificationSummary, VerifiedSolveResult,
};
use crate::api::Solver;
use crate::UnknownReason;

impl Solver {
    // =========================================================================
    // Verification and diagnostics (#4444)
    // =========================================================================

    /// Set the verification level controlling runtime correctness checks.
    ///
    /// Higher levels provide stronger guarantees at the cost of performance.
    /// The default is `DebugAssert` (checks active only in debug builds).
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Solver, Logic};
    /// use ay_dpll::VerificationLevel;
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// solver.set_verification_level(VerificationLevel::ProofChecked);
    /// ```
    pub fn set_verification_level(&mut self, level: VerificationLevel) {
        self.executor.set_verification_level(level);
    }

    /// Get the current verification level.
    #[must_use]
    pub fn verification_level(&self) -> VerificationLevel {
        self.executor.verification_level()
    }

    // =========================================================================
    // Counterexample style (#4522)
    // =========================================================================

    /// Set the counterexample style for model minimization.
    ///
    /// - `Minimal` (default): Prefer small values (0, ±1, powers of 2).
    /// - `Any`: Return whatever the solver finds, no minimization.
    /// - `Readable`: Prefer human-friendly values (round numbers).
    ///
    /// When the SMT-LIB option `:minimize-counterexamples` is explicitly set,
    /// it takes precedence over this setting.
    pub fn set_counterexample_style(&mut self, style: crate::CounterexampleStyle) {
        self.executor.set_counterexample_style(style);
    }

    /// Get the current counterexample style.
    #[must_use]
    pub fn counterexample_style(&self) -> crate::CounterexampleStyle {
        self.executor.counterexample_style()
    }

    // =========================================================================
    // Timeout and interrupt control
    // =========================================================================

    /// Set a timeout for check_sat calls.
    ///
    /// GROUND (quantifier-free) solves treat this as the nominal wall-clock
    /// deadline. QUANTIFIED solves (#quantifier-determinism) terminate
    /// primarily on the engine's DETERMINISTIC instantiation budgets
    /// (E-matching round/instance caps, interleaved/CEGQI/MBQI round caps) so
    /// that identical inputs produce identical verdicts regardless of machine
    /// speed or CPU load; for those solves the timeout acts as a far-out
    /// hang-protection BACKSTOP (remaining budget scaled by a small factor,
    /// capped — see `Executor::install_quantifier_deadline_backstop`), so a
    /// quantified check-sat may run moderately past the nominal timeout before
    /// failing closed to `Unknown`. A zero or already-expired timeout still
    /// stops immediately on both paths.
    pub fn set_timeout(&mut self, timeout: Option<Duration>) {
        self.timeout = timeout;
    }

    /// Get the current timeout setting
    #[must_use]
    pub fn timeout(&self) -> Option<Duration> {
        self.timeout
    }

    /// Set a memory limit for check_sat calls
    ///
    /// When the process memory exceeds this limit during solving, the solver
    /// will return `Unknown` with `MemoryLimit` reason.
    ///
    /// # Arguments
    ///
    /// * `limit` - Memory limit in bytes, or `None` to disable the limit
    ///
    /// # Platform Support
    ///
    /// Memory measurement is supported on macOS and Linux. On other platforms,
    /// the limit will have no effect.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Solver, Logic};
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// // Set 1GB memory limit
    /// solver.set_memory_limit(Some(1024 * 1024 * 1024));
    /// ```
    pub fn set_memory_limit(&mut self, limit: Option<usize>) {
        self.memory_limit = limit;
    }

    /// Get the current memory limit setting
    ///
    /// Returns the memory limit in bytes, or `None` if no limit is set.
    #[must_use]
    pub fn memory_limit(&self) -> Option<usize> {
        self.memory_limit
    }

    /// Set a per-instance term memory limit in bytes (#6563).
    ///
    /// Unlike `set_memory_limit` (process RSS), this caps the total bytes of
    /// term allocation for THIS solver instance only. Multiple solver instances
    /// in the same process each track their own budget independently, preventing
    /// cross-instance interference that causes non-deterministic `Unknown` results.
    ///
    /// Set to `None` for no limit (default, backward compatible).
    pub fn set_term_memory_limit(&mut self, limit: Option<usize>) {
        self.term_memory_limit = limit;
    }

    /// Get the current per-instance term memory limit.
    #[must_use]
    pub fn term_memory_limit(&self) -> Option<usize> {
        self.term_memory_limit
    }

    /// Get the approximate term memory usage for this solver instance in bytes.
    ///
    /// This counts only terms interned by THIS solver's `TermStore`, not terms
    /// from other solver instances in the same process (#6563).
    #[must_use]
    pub fn instance_term_bytes(&self) -> usize {
        self.terms().instance_term_bytes()
    }

    /// Set a limit on learned clauses for the SAT solver (#1609)
    ///
    /// When the number of learned clauses exceeds this limit, the SAT solver
    /// triggers more aggressive clause database reduction to prevent memory
    /// exhaustion. Set to `None` for no limit (default).
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Solver, Logic};
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// // Limit to 100,000 learned clauses
    /// solver.set_learned_clause_limit(Some(100_000));
    /// ```
    pub fn set_learned_clause_limit(&mut self, limit: Option<usize>) {
        self.learned_clause_limit = limit;
    }

    /// Get the current learned clause limit setting
    ///
    /// Returns the learned clause limit, or `None` if no limit is set.
    #[must_use]
    pub fn learned_clause_limit(&self) -> Option<usize> {
        self.learned_clause_limit
    }

    /// Set a limit on the SAT clause database size (bytes) (#1609)
    ///
    /// The limit applies to the SAT solver clause arena allocation estimate
    /// (`ClauseDB::memory_bytes()`, headers + literal arena). When exceeded,
    /// the SAT solver will compact the arena and may delete learned clauses.
    ///
    /// Set to `None` for no limit (default).
    pub fn set_clause_db_bytes_limit(&mut self, limit: Option<usize>) {
        self.clause_db_bytes_limit = limit;
    }

    /// Get the current clause DB bytes limit setting
    ///
    /// Returns the limit in bytes, or `None` if no limit is set.
    #[must_use]
    pub fn clause_db_bytes_limit(&self) -> Option<usize> {
        self.clause_db_bytes_limit
    }

    /// Set the random seed for SAT solver VSIDS tie-breaking (#6961).
    ///
    /// Different seeds produce different variable selection orders when
    /// activity scores are tied, leading to different search paths. This is
    /// useful for catching non-deterministic solver bugs via seed perturbation:
    /// run the same formula with N different seeds and compare results.
    ///
    /// The seed is forwarded to every SAT solver instance created during
    /// subsequent `check_sat` calls.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Solver, Logic};
    ///
    /// let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    /// solver.set_random_seed(42);
    /// ```
    pub fn set_random_seed(&mut self, seed: u64) {
        self.executor.set_random_seed(seed);
    }

    /// Set the maximum E-matching rounds per check-sat (#7893).
    ///
    /// Overrides the default of 8 rounds. Clamped to [1, 64].
    /// Lower values speed up proofs that converge quickly; higher
    /// values allow deeper instantiation chains for complex quantifier
    /// reasoning.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Solver, Logic};
    ///
    /// let mut solver = Solver::try_new(Logic::Uf).unwrap();
    /// solver.set_ematching_round_limit(16);
    /// assert_eq!(solver.ematching_round_limit(), 16);
    /// ```
    pub fn set_ematching_round_limit(&mut self, n: usize) {
        self.executor.set_ematching_round_limit(n);
    }

    /// Get the effective E-matching round limit (default: 8).
    #[must_use]
    pub fn ematching_round_limit(&self) -> usize {
        self.executor.ematching_round_limit()
    }

    // =========================================================================
    // Lemma persistence for incremental binary path analysis (#8304)
    // =========================================================================

    /// Enable or disable theory lemma persistence across push/pop scopes.
    ///
    /// When enabled, theory lemmas learned during solving are cached and
    /// replayed into subsequent check-sat calls after pop. This is useful
    /// for binary path analysis where the same program is analyzed path-by-path:
    /// each path shares most constraints but differs in branch conditions.
    /// Persistent lemmas avoid re-deriving theory knowledge that applies to
    /// multiple paths.
    ///
    /// Off by default. Has no effect without push/pop (non-incremental mode).
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Solver, Logic};
    ///
    /// let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    /// solver.set_lemma_persistence(true);
    /// assert!(solver.lemma_persistence());
    /// ```
    pub fn set_lemma_persistence(&mut self, enabled: bool) {
        self.executor.lemma_persistence = enabled;
    }

    /// Check whether theory lemma persistence is enabled.
    #[must_use]
    pub fn lemma_persistence(&self) -> bool {
        self.executor.lemma_persistence
    }

    /// Number of theory lemmas currently in the persistence cache.
    ///
    /// Returns 0 when lemma persistence is disabled.
    #[must_use]
    pub fn cached_lemma_count(&self) -> usize {
        if self.executor.lemma_persistence {
            self.executor.lemma_cache.len()
        } else {
            0
        }
    }

    /// Interrupt a running check_sat from another thread
    pub fn interrupt(&self) {
        self.interrupt.store(true, Ordering::Relaxed);
    }

    /// Get a handle that can be used to interrupt the solver from another thread
    #[must_use]
    pub fn interrupt_handle(&self) -> Arc<AtomicBool> {
        self.interrupt.clone()
    }

    /// Clear the interrupt flag
    pub fn clear_interrupt(&self) {
        self.interrupt.store(false, Ordering::Relaxed);
    }

    /// Check if the solver is currently interrupted
    #[must_use]
    pub fn is_interrupted(&self) -> bool {
        self.interrupt.load(Ordering::Relaxed)
    }

    /// Structured reason for the last Unknown result.
    ///
    /// Returns a structured enum indicating why the solver returned Unknown.
    /// For SMT-LIB compatible string output, use [`reason_unknown_smtlib`].
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Solver, Logic};
    /// use ay_dpll::UnknownReason;
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// solver.interrupt();
    /// let _ = solver.check_sat();
    /// assert_eq!(solver.unknown_reason(), Some(UnknownReason::Interrupted));
    /// ```
    ///
    /// [`reason_unknown_smtlib`]: Solver::reason_unknown_smtlib
    #[must_use]
    pub fn unknown_reason(&self) -> Option<UnknownReason> {
        self.last_unknown_reason
    }

    /// Reason for the last Unknown result as an SMT-LIB string.
    ///
    /// Returns the reason as a lowercase string matching SMT-LIB conventions
    /// (e.g., "timeout", "interrupted", "incomplete").
    ///
    /// For structured access, use [`unknown_reason`].
    ///
    /// [`unknown_reason`]: Solver::unknown_reason
    #[must_use]
    pub fn reason_unknown_smtlib(&self) -> Option<String> {
        self.unknown_reason().map(|r| r.to_string())
    }

    /// Deprecated compatibility wrapper for
    /// [`reason_unknown_smtlib`](Self::reason_unknown_smtlib).
    #[must_use]
    pub fn get_reason_unknown(&self) -> Option<String> {
        self.reason_unknown_smtlib()
    }

    /// Detail message from the last executor error.
    ///
    /// When `unknown_reason()` returns `Some(UnknownReason::InternalError)`,
    /// this method provides the underlying error message (e.g., model validation
    /// failure details). Returns `None` when the last result was not caused by
    /// an executor error.
    #[must_use]
    pub fn executor_error(&self) -> Option<&str> {
        self.last_executor_error.as_deref()
    }

    /// Statistics from the last check-sat call.
    ///
    /// Returns solver performance metrics for debugging and analysis.
    /// Statistics include conflicts, decisions, propagations, restarts, etc.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Solver, Sort, Logic};
    ///
    /// let mut solver = Solver::new(Logic::QfUf);
    /// let a = solver.declare_const("a", Sort::Bool);
    /// let b = solver.declare_const("b", Sort::Bool);
    /// let clause = solver.or(a, b);
    /// solver.assert_term(clause);
    /// solver.check_sat();
    ///
    /// let stats = solver.statistics();
    /// println!("Conflicts: {}", stats.conflicts);
    /// println!("Decisions: {}", stats.decisions);
    /// ```
    #[must_use]
    pub fn statistics(&self) -> &crate::Statistics {
        self.executor.statistics()
    }

    /// Deprecated: use [`statistics`](Self::statistics) instead.
    #[must_use]
    pub fn get_statistics(&self) -> &crate::Statistics {
        self.statistics()
    }

    /// Check satisfiability and return structured statistics from the same solve call.
    ///
    /// This is an ergonomic helper for callers that need both the SAT result and
    /// solver telemetry without a follow-up `statistics()` call.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
    ///
    /// let mut solver = Solver::new(Logic::QfUf);
    /// let a = solver.declare_const("a", Sort::Bool);
    /// let b = solver.declare_const("b", Sort::Bool);
    /// let clause = solver.or(a, b);
    /// solver.assert_term(clause);
    ///
    /// let (result, stats) = solver.check_sat_with_statistics();
    /// assert_eq!(result, SolveResult::Sat);
    /// assert!(stats.propagations > 0 || stats.decisions > 0);
    /// ```
    pub fn check_sat_with_statistics(&mut self) -> (VerifiedSolveResult, crate::Statistics) {
        let details = self.check_sat_with_details();
        (details.result, details.statistics)
    }

    /// Check satisfiability and return atomic result details from the same solve call.
    ///
    /// This includes:
    /// - SAT/UNSAT/UNKNOWN result
    /// - statistics snapshot
    /// - structured Unknown reason (if any)
    /// - verification provenance summary
    pub fn check_sat_with_details(&mut self) -> SolveDetails {
        let start = Instant::now();
        let verified = self.check_sat();
        let mut details = self.build_solve_details(verified);
        details.resource_usage.wall_time = start.elapsed();
        details
    }

    /// Check satisfiability under temporary assumptions and return atomic result
    /// details including unsat assumptions from the same solve call.
    ///
    /// This is the assumption-parity equivalent of `check_sat_with_details`,
    /// capturing the unsat-assumption subset in the same envelope instead of
    /// requiring a follow-up `unsat_assumptions()` call.
    pub fn check_sat_assuming_with_details(
        &mut self,
        assumptions: &[Term],
    ) -> AssumptionSolveDetails {
        let start = Instant::now();
        let verified = self.check_sat_assuming(assumptions);
        let mut solve = self.build_solve_details(verified);
        solve.resource_usage.wall_time = start.elapsed();
        let unsat_assumptions = self.unsat_assumptions();
        AssumptionSolveDetails {
            solve,
            unsat_assumptions,
        }
    }

    /// Build a `SolveDetails` envelope from a completed solve result.
    ///
    /// Shared implementation behind all `*_with_details` entrypoints.
    fn build_solve_details(&self, verified: VerifiedSolveResult) -> SolveDetails {
        let raw = verified.result();
        let statistics = self.statistics().clone();
        let (independent, delegated, incomplete) =
            if let Some(ref stats) = self.executor.last_validation_stats {
                stats.verification_evidence_counts()
            } else {
                (0, 0, 0)
            };
        let verification = VerificationSummary {
            sat_model_validated: verified.was_model_validated(),
            unsat_proof_available: raw.is_unsat() && self.last_proof().is_some(),
            unsat_proof_strictly_verified: verified.was_unsat_strictly_verified(),
            unsat_independently_verified: verified.was_unsat_independently_verified(),
            unsat_exact_semantically_verified: verified.was_unsat_exact_semantically_verified(),
            unsat_proof_checker_failures: statistics.get_int("proof_checker_failures").unwrap_or(0),
            sat_independent_checks: independent,
            sat_delegated_checks: delegated,
            sat_incomplete_checks: incomplete,
        };
        let proof_checking_requested =
            self.is_producing_proofs() || self.executor.verification_level().has_proof_checking();
        let verification_level = VerificationLevel::from_state(proof_checking_requested);
        let limit_hit = self.last_unknown_reason.and_then(|r| match r {
            UnknownReason::Timeout => Some(LimitKind::Timeout),
            UnknownReason::MemoryLimit => Some(LimitKind::MemoryLimit),
            UnknownReason::ResourceLimit => Some(LimitKind::MemoryLimit),
            UnknownReason::Interrupted => Some(LimitKind::Interrupted),
            _ => None,
        });
        let unknown_diagnostic = self
            .last_unknown_reason
            .map(|reason| self.build_unknown_diagnostic(reason, limit_hit));
        let resource_usage = ResourceUsage {
            rss_bytes: crate::memory::current_memory_bytes(),
            term_bytes: self.terms().instance_term_bytes(),
            term_count: self.terms().len(),
            learned_clause_count: statistics.learned_clauses as usize,
            wall_time: Duration::ZERO, // filled by caller if timing is tracked
            limit_hit,
        };
        SolveDetails {
            result: verified,
            statistics,
            unknown_reason: self.last_unknown_reason,
            unknown_diagnostic,
            executor_error: self.last_executor_error.clone(),
            verification,
            verification_level,
            resource_usage,
        }
    }

    fn build_unknown_diagnostic(
        &self,
        reason: UnknownReason,
        limit_hit: Option<LimitKind>,
    ) -> UnknownDiagnostic {
        let statistics = self.statistics();
        let phase = statistics
            .get_string("unknown.phase")
            .map(ToOwned::to_owned)
            .or_else(|| Some(default_unknown_phase(reason, limit_hit).to_string()));
        let cost_center = statistics
            .get_string("unknown.cost_center")
            .map(ToOwned::to_owned)
            .or_else(|| Some(default_unknown_cost_center(reason, limit_hit).to_string()));
        let detail = statistics
            .get_string("unknown.detail")
            .map(ToOwned::to_owned)
            .or_else(|| Some(default_unknown_detail(reason).to_string()));

        UnknownDiagnostic {
            reason,
            phase,
            cost_center,
            detail,
        }
    }
}

fn default_unknown_phase(reason: UnknownReason, limit_hit: Option<LimitKind>) -> &'static str {
    match limit_hit {
        Some(LimitKind::Timeout | LimitKind::Interrupted) => "search-control",
        Some(
            LimitKind::MemoryLimit
            | LimitKind::TermMemoryLimit
            | LimitKind::LearnedClauseLimit
            | LimitKind::ClauseDbBytesLimit,
        ) => "resource-control",
        None => match reason {
            UnknownReason::Timeout | UnknownReason::Interrupted => "search-control",
            UnknownReason::MemoryLimit | UnknownReason::ResourceLimit => "resource-control",
            reason if reason.is_quantifier() => "quantifier-instantiation",
            UnknownReason::UnsupportedArithmetic => "theory-preprocessing",
            UnknownReason::UnsupportedMixedCollection => "theory-combination",
            UnknownReason::Unsupported => "theory-combination",
            UnknownReason::InternalError => "executor",
            _ => "theory-search",
        },
    }
}

fn default_unknown_cost_center(
    reason: UnknownReason,
    limit_hit: Option<LimitKind>,
) -> &'static str {
    match limit_hit {
        Some(LimitKind::Timeout) => "deadline",
        Some(LimitKind::Interrupted) => "interrupt",
        Some(LimitKind::MemoryLimit) => "memory",
        Some(LimitKind::TermMemoryLimit) => "term-memory",
        Some(LimitKind::LearnedClauseLimit) => "learned-clause-limit",
        Some(LimitKind::ClauseDbBytesLimit) => "clause-db-bytes-limit",
        None => match reason {
            UnknownReason::QuantifierRoundLimit => "ematching",
            UnknownReason::QuantifierDeferred => "deferred-instantiation",
            UnknownReason::QuantifierUnhandled => "unhandled",
            UnknownReason::QuantifierCegqiIncomplete => "cegqi",
            UnknownReason::QuantifierEmatchingExistsIncomplete => "ematching-exists",
            UnknownReason::UnsupportedArithmetic => "arithmetic-div-mod",
            UnknownReason::UnsupportedMixedCollection => "mixed-collection",
            UnknownReason::Unsupported => "unsupported-fragment",
            UnknownReason::SplitLimit => "split-loop",
            UnknownReason::ExpressionSplit => "expression-split",
            UnknownReason::Timeout => "deadline",
            UnknownReason::Interrupted => "interrupt",
            UnknownReason::MemoryLimit | UnknownReason::ResourceLimit => "memory",
            UnknownReason::InternalError => "internal-error",
            UnknownReason::SelfCheckRejected => "self-check-rejected",
            UnknownReason::ProofTrusted => "proof-trusted",
            UnknownReason::Incomplete | UnknownReason::Unknown => "unknown",
        },
    }
}

fn default_unknown_detail(reason: UnknownReason) -> &'static str {
    match reason {
        UnknownReason::Timeout => "deadline expired before a definitive result",
        UnknownReason::Interrupted => "interrupt requested before a definitive result",
        UnknownReason::QuantifierRoundLimit => "E-matching budget was exhausted",
        UnknownReason::QuantifierDeferred => "deferred quantifier instantiations remained",
        UnknownReason::QuantifierUnhandled => "one or more quantifiers were unhandled",
        UnknownReason::QuantifierCegqiIncomplete => "CEGQI did not complete",
        UnknownReason::QuantifierEmatchingExistsIncomplete => {
            "existential E-matching mode is incomplete"
        }
        UnknownReason::UnsupportedArithmetic => "arithmetic div/mod fragment is unsupported",
        UnknownReason::UnsupportedMixedCollection => {
            "mixed collection/datatype fragment is unsupported"
        }
        UnknownReason::Unsupported => "theory fragment is unsupported",
        UnknownReason::SplitLimit => "theory split-loop budget was exhausted",
        UnknownReason::ExpressionSplit => "expression split was required",
        UnknownReason::MemoryLimit | UnknownReason::ResourceLimit => {
            "resource budget was exhausted"
        }
        UnknownReason::InternalError => "executor returned an internal error",
        UnknownReason::SelfCheckRejected => "AY COMPUTED A VERDICT AND ITS OWN FAIL-CLOSED CHECKER REFUTED IT -- this is a caught wrong answer, not a missing capability",
        UnknownReason::ProofTrusted => "AY COMPUTED AN UNSAT AND WITHHELD IT -- the terminal derivation chain is not trust-free, so no checker can confirm the refutation; this is a soundness gate firing, not a missing capability",
        UnknownReason::Incomplete | UnknownReason::Unknown => "solver returned Unknown",
    }
}
