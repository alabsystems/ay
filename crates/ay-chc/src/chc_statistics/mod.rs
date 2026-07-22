// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public CHC solver statistics.
//!
//! Exposes PDR/IC3 counters for external consumers (ay binary `--stats` flag)
//! without leaking internal `SolverStats` or failure-analysis details.
//!
//! Part of #4710 — CHC/portfolio mode observability.

use crate::algebraic_invariant::AlgebraicValidationStats;
use crate::failure_analysis::SolverStats;
#[cfg(test)]
use crate::trp::AcceleratedSummaryTrpFamilySummaryStatistics;

/// Native-code helper counters collected from CHC profile-only paths.
///
/// These counters are observability only. They report where the existing
/// Bool/Int expression helper was compiled, applied, or conservatively
/// bypassed; they do not enable solver-program dispatch.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct NativeCodeHelperStatistics {
    /// Attempts to compile a CHC expression helper.
    pub(crate) compile_attempts: u64,
    /// Successful native helper compilations.
    pub(crate) compile_successes: u64,
    /// Failed or unsupported native helper compilations.
    pub(crate) compile_failures: u64,
    /// Calls that reached the native helper path.
    pub(crate) evaluations: u64,
    /// Native helper results that conservatively deoptimized.
    pub(crate) deopts: u64,
    /// Fallbacks to the interpreter/SmallModel evaluator.
    pub(crate) fallbacks: u64,
    /// Fallbacks caused by a model missing a compiled variable binding.
    pub(crate) missing_var_fallbacks: u64,
    /// Native-true results checked by the interpreter oracle.
    pub(crate) interpreter_confirmations: u64,
    /// Native-true results accepted by the conservative trusted grammar.
    pub(crate) trusted_true_results: u64,
    /// Accepted native true helper applications.
    pub(crate) applications: u64,
}

/// Statistics collected during a CHC solve attempt.
///
/// Returned by `PdrSolver::solve_problem_with_statistics` and
/// `AdaptivePortfolio::solve_with_statistics`. All fields are counters
/// accumulated during the solve; none are rates or derived metrics.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct ChcStatistics {
    /// Total PDR iterations (blocking + propagation rounds).
    pub iterations: u64,
    /// Number of inductive lemmas learned across all frames.
    pub lemmas_learned: u64,
    /// Maximum PDR frame depth reached.
    pub max_frame: u64,
    /// Number of PDR restarts triggered.
    pub restarts: u64,
    /// Number of SMT queries that returned Unknown.
    pub smt_unknowns: u64,
    /// Implication-cache hits (exact result reused, no solver call).
    pub cache_hits: u64,
    /// Implication-cache model rejections (fast rejection via cached model).
    pub cache_model_rejections: u64,
    /// Total SMT solver calls recorded by the implication cache.
    pub cache_solver_calls: u64,
    /// Number of trust-proof fallback events (#8555).
    ///
    /// Counts code paths that accepted a result without full independent
    /// proof verification. Non-zero indicates potential soundness gaps
    /// that `--strict-proofs` would have caught.
    pub trust_proof_fallbacks: u64,
    /// Attempts to compile CHC native-code helper expressions.
    pub native_code_helper_compile_attempts: u64,
    /// Successful CHC native-code helper compilations.
    pub native_code_helper_compile_successes: u64,
    /// Failed or unsupported CHC native-code helper compilations.
    pub native_code_helper_compile_failures: u64,
    /// Calls that reached the CHC native-code helper path.
    pub native_code_helper_evaluations: u64,
    /// CHC native-code helper deopts back to conservative evaluation.
    pub native_code_helper_deopts: u64,
    /// CHC native-code helper fallbacks to the interpreter path.
    pub native_code_helper_fallbacks: u64,
    /// CHC native-code helper fallbacks due to missing model bindings.
    pub native_code_helper_missing_var_fallbacks: u64,
    /// CHC native-code helper true results checked by the interpreter oracle.
    pub native_code_helper_interpreter_confirmations: u64,
    /// CHC native-code helper true results accepted by the trusted grammar.
    pub native_code_helper_trusted_true_results: u64,
    /// CHC native-code helper applications that accepted a native true result.
    pub native_code_helper_applications: u64,
    /// Profile-only TLA transition-cluster metadata applications.
    pub tla_transition_cluster_applications: u64,
    /// Distinct symbolic array-scalarization projected cells.
    pub symbolic_scalarization_projected_cells: u64,
    /// Original predicate array args with more than one distinct symbolic projected cell.
    pub symbolic_scalarization_multi_cell_args: u64,
    /// LRA affine/algebraic candidates checked against original CHC clauses.
    pub lra_affine_original_clause_validation_attempts: u64,
    /// SMT queries issued by LRA affine/algebraic original-clause validation.
    pub lra_affine_original_clause_validation_queries: u64,
    /// LRA affine/algebraic candidates accepted by original-clause validation.
    pub lra_affine_original_clause_validation_successes: u64,
    /// LRA affine/algebraic candidates rejected with a SAT witness.
    pub lra_affine_original_clause_validation_failures: u64,
    /// LRA affine/algebraic candidates rejected after validation returned UNKNOWN.
    pub lra_affine_original_clause_validation_unknowns: u64,
    /// Deterministic Bool/BV transition route gate attempts.
    pub deterministic_bv_bool_transition_attempts: u64,
    /// Deterministic Bool/BV transition systems recognized after syntactic gating.
    pub deterministic_bv_bool_transition_recognized: u64,
    /// Validated UNSAFE results produced by the deterministic Bool/BV BMC leg.
    pub deterministic_bv_bool_transition_bmc_unsafe_validated: u64,
    /// Validated SAFE results produced by the deterministic Bool/BV Kind leg.
    pub deterministic_bv_bool_transition_kind_safe_validated: u64,
    /// Validated UNSAFE results produced by the deterministic Bool/BV Kind leg.
    pub deterministic_bv_bool_transition_kind_unsafe_validated: u64,
    /// Validated SAFE results produced by the Bool-control reachability shortcut.
    pub deterministic_bv_bool_transition_bool_control_safe_validated: u64,
    /// Deterministic Bool/BV route candidates rejected by original validation.
    pub deterministic_bv_bool_transition_validation_rejections: u64,
    /// Profile-only accelerated-summary modular predicate-chain summary candidates.
    pub accelerated_summary_modular_chain_summary_candidates: u64,
    /// Profile-only accelerated-summary modular predicate-chain candidates counted as family summaries.
    pub accelerated_summary_modular_chain_family_summary_candidates: u64,
    /// Profile-only TRP accelerated-summary family-summary candidates.
    pub accelerated_summary_trp_family_summary_candidates: u64,
    /// Profile-only TRP affine constant-delta family summaries.
    pub accelerated_summary_trp_affine_constant_delta_family_summaries: u64,
    /// Profile-only TRP polynomial closed-form family summaries.
    pub accelerated_summary_trp_polynomial_closed_form_family_summaries: u64,
    /// Profile-only TRP affine preserved-difference family summaries.
    pub accelerated_summary_trp_affine_preserved_difference_family_summaries: u64,
}

impl From<SolverStats> for ChcStatistics {
    fn from(s: SolverStats) -> Self {
        Self {
            iterations: s.iterations as u64,
            lemmas_learned: s.lemmas_learned as u64,
            max_frame: s.max_frame as u64,
            restarts: s.restart_count as u64,
            smt_unknowns: s.smt_unknowns as u64,
            cache_hits: s.implication_cache_hits as u64,
            cache_model_rejections: s.implication_model_rejections as u64,
            cache_solver_calls: s.implication_solver_calls as u64,
            trust_proof_fallbacks: 0,
            native_code_helper_compile_attempts: s.chc_native_code_helper_compile_attempts as u64,
            native_code_helper_compile_successes: s.chc_native_code_helper_compile_successes as u64,
            native_code_helper_compile_failures: s.chc_native_code_helper_compile_failures as u64,
            native_code_helper_evaluations: s.chc_native_code_helper_evaluations as u64,
            native_code_helper_deopts: s.chc_native_code_helper_deopts as u64,
            native_code_helper_fallbacks: s.chc_native_code_helper_fallbacks as u64,
            native_code_helper_missing_var_fallbacks: s.chc_native_code_helper_missing_var_fallbacks
                as u64,
            native_code_helper_interpreter_confirmations: s
                .chc_native_code_helper_interpreter_confirmations
                as u64,
            native_code_helper_trusted_true_results: s.chc_native_code_helper_trusted_true_results
                as u64,
            native_code_helper_applications: s.chc_native_code_helper_applications as u64,
            tla_transition_cluster_applications: s.chc_tla_transition_cluster_applications as u64,
            symbolic_scalarization_projected_cells: s.symbolic_scalarization_projected_cells as u64,
            symbolic_scalarization_multi_cell_args: s.symbolic_scalarization_multi_cell_args as u64,
            lra_affine_original_clause_validation_attempts: 0,
            lra_affine_original_clause_validation_queries: 0,
            lra_affine_original_clause_validation_successes: 0,
            lra_affine_original_clause_validation_failures: 0,
            lra_affine_original_clause_validation_unknowns: 0,
            deterministic_bv_bool_transition_attempts: 0,
            deterministic_bv_bool_transition_recognized: 0,
            deterministic_bv_bool_transition_bmc_unsafe_validated: 0,
            deterministic_bv_bool_transition_kind_safe_validated: 0,
            deterministic_bv_bool_transition_kind_unsafe_validated: 0,
            deterministic_bv_bool_transition_bool_control_safe_validated: 0,
            deterministic_bv_bool_transition_validation_rejections: 0,
            accelerated_summary_modular_chain_summary_candidates: 0,
            accelerated_summary_modular_chain_family_summary_candidates: 0,
            accelerated_summary_trp_family_summary_candidates: 0,
            accelerated_summary_trp_affine_constant_delta_family_summaries: 0,
            accelerated_summary_trp_polynomial_closed_form_family_summaries: 0,
            accelerated_summary_trp_affine_preserved_difference_family_summaries: 0,
        }
    }
}

impl ChcStatistics {
    /// Merge another `ChcStatistics` into this one (additive).
    ///
    /// Used by portfolio mode to aggregate stats across multiple engine runs.
    /// Uses saturating arithmetic to avoid overflow panics/wraparound on long runs.
    pub fn merge(&mut self, other: &Self) {
        self.iterations = self.iterations.saturating_add(other.iterations);
        self.lemmas_learned = self.lemmas_learned.saturating_add(other.lemmas_learned);
        self.max_frame = self.max_frame.max(other.max_frame);
        self.restarts = self.restarts.saturating_add(other.restarts);
        self.smt_unknowns = self.smt_unknowns.saturating_add(other.smt_unknowns);
        self.cache_hits = self.cache_hits.saturating_add(other.cache_hits);
        self.cache_model_rejections = self
            .cache_model_rejections
            .saturating_add(other.cache_model_rejections);
        self.cache_solver_calls = self
            .cache_solver_calls
            .saturating_add(other.cache_solver_calls);
        self.trust_proof_fallbacks = self
            .trust_proof_fallbacks
            .saturating_add(other.trust_proof_fallbacks);
        self.native_code_helper_compile_attempts = self
            .native_code_helper_compile_attempts
            .saturating_add(other.native_code_helper_compile_attempts);
        self.native_code_helper_compile_successes = self
            .native_code_helper_compile_successes
            .saturating_add(other.native_code_helper_compile_successes);
        self.native_code_helper_compile_failures = self
            .native_code_helper_compile_failures
            .saturating_add(other.native_code_helper_compile_failures);
        self.native_code_helper_evaluations = self
            .native_code_helper_evaluations
            .saturating_add(other.native_code_helper_evaluations);
        self.native_code_helper_deopts = self
            .native_code_helper_deopts
            .saturating_add(other.native_code_helper_deopts);
        self.native_code_helper_fallbacks = self
            .native_code_helper_fallbacks
            .saturating_add(other.native_code_helper_fallbacks);
        self.native_code_helper_missing_var_fallbacks = self
            .native_code_helper_missing_var_fallbacks
            .saturating_add(other.native_code_helper_missing_var_fallbacks);
        self.native_code_helper_interpreter_confirmations = self
            .native_code_helper_interpreter_confirmations
            .saturating_add(other.native_code_helper_interpreter_confirmations);
        self.native_code_helper_trusted_true_results = self
            .native_code_helper_trusted_true_results
            .saturating_add(other.native_code_helper_trusted_true_results);
        self.native_code_helper_applications = self
            .native_code_helper_applications
            .saturating_add(other.native_code_helper_applications);
        self.tla_transition_cluster_applications = self
            .tla_transition_cluster_applications
            .saturating_add(other.tla_transition_cluster_applications);
        self.symbolic_scalarization_projected_cells = self
            .symbolic_scalarization_projected_cells
            .saturating_add(other.symbolic_scalarization_projected_cells);
        self.symbolic_scalarization_multi_cell_args = self
            .symbolic_scalarization_multi_cell_args
            .saturating_add(other.symbolic_scalarization_multi_cell_args);
        self.lra_affine_original_clause_validation_attempts = self
            .lra_affine_original_clause_validation_attempts
            .saturating_add(other.lra_affine_original_clause_validation_attempts);
        self.lra_affine_original_clause_validation_queries = self
            .lra_affine_original_clause_validation_queries
            .saturating_add(other.lra_affine_original_clause_validation_queries);
        self.lra_affine_original_clause_validation_successes = self
            .lra_affine_original_clause_validation_successes
            .saturating_add(other.lra_affine_original_clause_validation_successes);
        self.lra_affine_original_clause_validation_failures = self
            .lra_affine_original_clause_validation_failures
            .saturating_add(other.lra_affine_original_clause_validation_failures);
        self.lra_affine_original_clause_validation_unknowns = self
            .lra_affine_original_clause_validation_unknowns
            .saturating_add(other.lra_affine_original_clause_validation_unknowns);
        self.deterministic_bv_bool_transition_attempts = self
            .deterministic_bv_bool_transition_attempts
            .saturating_add(other.deterministic_bv_bool_transition_attempts);
        self.deterministic_bv_bool_transition_recognized = self
            .deterministic_bv_bool_transition_recognized
            .saturating_add(other.deterministic_bv_bool_transition_recognized);
        self.deterministic_bv_bool_transition_bmc_unsafe_validated = self
            .deterministic_bv_bool_transition_bmc_unsafe_validated
            .saturating_add(other.deterministic_bv_bool_transition_bmc_unsafe_validated);
        self.deterministic_bv_bool_transition_kind_safe_validated = self
            .deterministic_bv_bool_transition_kind_safe_validated
            .saturating_add(other.deterministic_bv_bool_transition_kind_safe_validated);
        self.deterministic_bv_bool_transition_kind_unsafe_validated = self
            .deterministic_bv_bool_transition_kind_unsafe_validated
            .saturating_add(other.deterministic_bv_bool_transition_kind_unsafe_validated);
        self.deterministic_bv_bool_transition_bool_control_safe_validated = self
            .deterministic_bv_bool_transition_bool_control_safe_validated
            .saturating_add(other.deterministic_bv_bool_transition_bool_control_safe_validated);
        self.deterministic_bv_bool_transition_validation_rejections = self
            .deterministic_bv_bool_transition_validation_rejections
            .saturating_add(other.deterministic_bv_bool_transition_validation_rejections);
        self.accelerated_summary_modular_chain_summary_candidates = self
            .accelerated_summary_modular_chain_summary_candidates
            .saturating_add(other.accelerated_summary_modular_chain_summary_candidates);
        self.accelerated_summary_modular_chain_family_summary_candidates = self
            .accelerated_summary_modular_chain_family_summary_candidates
            .saturating_add(other.accelerated_summary_modular_chain_family_summary_candidates);
        self.accelerated_summary_trp_family_summary_candidates = self
            .accelerated_summary_trp_family_summary_candidates
            .saturating_add(other.accelerated_summary_trp_family_summary_candidates);
        self.accelerated_summary_trp_affine_constant_delta_family_summaries = self
            .accelerated_summary_trp_affine_constant_delta_family_summaries
            .saturating_add(other.accelerated_summary_trp_affine_constant_delta_family_summaries);
        self.accelerated_summary_trp_polynomial_closed_form_family_summaries = self
            .accelerated_summary_trp_polynomial_closed_form_family_summaries
            .saturating_add(other.accelerated_summary_trp_polynomial_closed_form_family_summaries);
        self.accelerated_summary_trp_affine_preserved_difference_family_summaries = self
            .accelerated_summary_trp_affine_preserved_difference_family_summaries
            .saturating_add(
                other.accelerated_summary_trp_affine_preserved_difference_family_summaries,
            );
    }

    /// Record profile-only TLA transition-cluster metadata applications.
    pub(crate) fn record_tla_transition_cluster_applications(&mut self, count: u64) {
        self.tla_transition_cluster_applications = self
            .tla_transition_cluster_applications
            .saturating_add(count);
    }

    pub(crate) fn record_lra_affine_original_clause_validation_stats(
        &mut self,
        stats: &AlgebraicValidationStats,
    ) {
        self.lra_affine_original_clause_validation_attempts = self
            .lra_affine_original_clause_validation_attempts
            .saturating_add(stats.lra_affine_original_clause_validation_attempts);
        self.lra_affine_original_clause_validation_queries = self
            .lra_affine_original_clause_validation_queries
            .saturating_add(stats.lra_affine_original_clause_validation_queries);
        self.lra_affine_original_clause_validation_successes = self
            .lra_affine_original_clause_validation_successes
            .saturating_add(stats.lra_affine_original_clause_validation_successes);
        self.lra_affine_original_clause_validation_failures = self
            .lra_affine_original_clause_validation_failures
            .saturating_add(stats.lra_affine_original_clause_validation_failures);
        self.lra_affine_original_clause_validation_unknowns = self
            .lra_affine_original_clause_validation_unknowns
            .saturating_add(stats.lra_affine_original_clause_validation_unknowns);
        self.accelerated_summary_modular_chain_summary_candidates = self
            .accelerated_summary_modular_chain_summary_candidates
            .saturating_add(stats.accelerated_summary_modular_chain_summary_candidates);
        self.accelerated_summary_modular_chain_family_summary_candidates = self
            .accelerated_summary_modular_chain_family_summary_candidates
            .saturating_add(stats.accelerated_summary_modular_chain_family_summary_candidates);
    }

    pub(crate) fn record_deterministic_bv_bool_transition_attempt(&mut self) {
        self.deterministic_bv_bool_transition_attempts = self
            .deterministic_bv_bool_transition_attempts
            .saturating_add(1);
    }

    pub(crate) fn record_deterministic_bv_bool_transition_recognized(&mut self) {
        self.deterministic_bv_bool_transition_recognized = self
            .deterministic_bv_bool_transition_recognized
            .saturating_add(1);
    }

    pub(crate) fn record_deterministic_bv_bool_transition_bmc_unsafe_validated(&mut self) {
        self.deterministic_bv_bool_transition_bmc_unsafe_validated = self
            .deterministic_bv_bool_transition_bmc_unsafe_validated
            .saturating_add(1);
    }

    pub(crate) fn record_deterministic_bv_bool_transition_kind_safe_validated(&mut self) {
        self.deterministic_bv_bool_transition_kind_safe_validated = self
            .deterministic_bv_bool_transition_kind_safe_validated
            .saturating_add(1);
    }

    pub(crate) fn record_deterministic_bv_bool_transition_kind_unsafe_validated(&mut self) {
        self.deterministic_bv_bool_transition_kind_unsafe_validated = self
            .deterministic_bv_bool_transition_kind_unsafe_validated
            .saturating_add(1);
    }

    pub(crate) fn record_deterministic_bv_bool_transition_bool_control_safe_validated(&mut self) {
        self.deterministic_bv_bool_transition_bool_control_safe_validated = self
            .deterministic_bv_bool_transition_bool_control_safe_validated
            .saturating_add(1);
    }

    pub(crate) fn record_deterministic_bv_bool_transition_validation_rejection(&mut self) {
        self.deterministic_bv_bool_transition_validation_rejections = self
            .deterministic_bv_bool_transition_validation_rejections
            .saturating_add(1);
    }

    #[cfg(test)]
    pub(crate) fn record_trp_family_summary_stats(
        &mut self,
        stats: &AcceleratedSummaryTrpFamilySummaryStatistics,
    ) {
        self.accelerated_summary_trp_family_summary_candidates = self
            .accelerated_summary_trp_family_summary_candidates
            .saturating_add(stats.family_summary_candidates);
        self.accelerated_summary_trp_affine_constant_delta_family_summaries = self
            .accelerated_summary_trp_affine_constant_delta_family_summaries
            .saturating_add(stats.affine_constant_delta_family_summaries);
        self.accelerated_summary_trp_polynomial_closed_form_family_summaries = self
            .accelerated_summary_trp_polynomial_closed_form_family_summaries
            .saturating_add(stats.polynomial_closed_form_family_summaries);
        self.accelerated_summary_trp_affine_preserved_difference_family_summaries = self
            .accelerated_summary_trp_affine_preserved_difference_family_summaries
            .saturating_add(stats.affine_preserved_difference_family_summaries);
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
