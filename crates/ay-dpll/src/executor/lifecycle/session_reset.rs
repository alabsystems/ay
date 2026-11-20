// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `(reset)` returns the executor to exactly what [`Executor::new`] builds,
//! keeping only the host's configuration.
//!
//! The frontend implements `(reset)` by replacing its `Context`, and with it
//! the append-only term store, wholesale: term ids restart at zero. The
//! executor used to clear an ALLOW-list of its own fields on the same command.
//! Every field added after that list was written survived the reset holding
//! the previous problem's state:
//!
//! * `TermId`s into the discarded store, which the next problem reads back as
//!   ids of unrelated terms or past the end of the new store. Measured in one
//!   `ay --incremental` process on
//!   `storecomm_invalid_t1_pp_sf_ni_00030_008.cvc.smt2` then
//!   `sat_nested_function.smt2`: the first query's rejected array assertion
//!   (`last_rejected_array_assertion`, `TermId(247)`) was dereferenced by the
//!   second query's read-pin repair, `index out of bounds: the len is 7 but the
//!   index is 247` in `ay-core/src/term/mod.rs`, and the second query answered
//!   `unknown` where a fresh process answers `sat`;
//! * per-session budgets and memos that only ever grow
//!   (`residue_probe_failures`, `eqdv_retention_off_declined_at_steps`), so a
//!   later problem is refused work a fresh process would do;
//! * retry latches and routing flags of a query that never finished (a panic
//!   unwinds past the code that would have cleared them).
//!
//! The list is therefore inverted. Everything is rebuilt by the constructor,
//! and only the fields of [`HostConfiguration`] are carried over. Each of them
//! is set by the embedding host (API setters, CLI flags, SMT-LIB options the
//! executor mirrors into its own fields) and none of them names a term. A field
//! added later is reset by default; keeping one across `(reset)` requires
//! adding it to that struct, where it has to be justified.

use super::*;

/// The host configuration `(reset)` carries over. Every other executor field
/// is rebuilt by the constructor. None of these fields names a term.
struct HostConfiguration {
    // Host configuration: API setters and CLI flags.
    debug_ufbv: bool,
    lia_incremental_eager_override: Option<bool>,
    lra_incremental_eager_override: Option<bool>,
    lra_inc_engine_override: Option<bool>,
    no_lra_theory_propagation: bool,
    counterexample_style: crate::CounterexampleStyle,
    proof_tracker: crate::proof_tracker::ProofTracker,
    proof_output_requested: bool,
    proof_artifact_required: bool,
    interpolation_proof: bool,
    proof_reconstruction_step_budget: Option<u64>,
    alethe_dialect: ay_proof::AletheDialect,
    learned_clause_limit: Option<usize>,
    clause_db_bytes_limit: Option<usize>,
    verification_level: VerificationLevel,
    self_check: bool,
    competition_mode: bool,
    ematching_round_limit: Option<usize>,
    progress_enabled: bool,
    progress_json_path: Option<String>,
    aggressive_model_minimize: bool,
    model_output_shed: bool,
    lemma_persistence: bool,
    measured_negative_quantifier_routes: qe_route::MeasuredNegativeRoutes,
    // Host resource controls. `timeout`, `resource_limit`,
    // `ground_budget_enabled`, `memory_limit` and `random_seed` are also
    // reachable through `:timeout`, `:rlimit`, `:max-memory` and
    // `:random-seed`. Those option paths record the host value they replace
    // (`ScriptOverriddenResourceOptions`), and `reset_to_fresh_session` writes
    // it back BEFORE this struct is taken, so what is carried over here is
    // the host's value, never a script's.
    solve_interrupt: Option<Arc<AtomicBool>>,
    certification_parent: ay_core::resource::WeakGuard,
    solve_deadline: SolveDeadlineCell,
    certification_deadline: SolveDeadlineCell,
    command_deadline: CommandDeadlineState,
    quantifier_deadline_policy: QuantifierDeadlinePolicy,
    quantifier_deadline_backstop_opt_in: bool,
    timeout: Option<Duration>,
    resource_limit: Option<u64>,
    decision_limit: Option<u64>,
    ground_budget_enabled: bool,
    memory_limit: Option<usize>,
    term_memory_limit: Option<usize>,
    random_seed: Option<u64>,
    // The caller's position on the call stack; the caller restores it.
    query_publication_role: Cell<QueryPublicationRole>,
    decision_command_depth: Cell<u32>,
    // Lifetime diagnostic counters. They name no term.
    prepass_reachability: PrepassReachability,
    // Test and debug instrumentation hooks.
    #[cfg(test)]
    test_force_non_bv_congruence_bail: Option<theories::TestCongruenceBail>,
    #[cfg(test)]
    test_euf_bv_congruence_clause_cap: Option<usize>,
    #[cfg(test)]
    last_applied_sat_random_seed: Cell<Option<u64>>,
    #[cfg(test)]
    last_applied_dpll_random_seed: Cell<Option<u64>>,
    #[cfg(test)]
    last_oll_core_rounds: Cell<u64>,
    #[cfg(test)]
    forced_maxsmt_exact_cost: Cell<Option<u64>>,
    #[cfg(test)]
    forced_maxsmt_oll_core_anomaly: Cell<bool>,
    #[cfg(test)]
    forced_maxsmt_post_emit_soft_flip: Cell<bool>,
    #[cfg(test)]
    forced_optimization_post_emit_objective_flip: Cell<bool>,
    #[cfg(debug_assertions)]
    auflia_persistent_shadow: bool,
    #[cfg(debug_assertions)]
    demand_force_eager: bool,
}

impl HostConfiguration {
    /// Move the host configuration out of an executor that is being discarded.
    fn take(previous: Executor) -> Self {
        Self {
            debug_ufbv: previous.debug_ufbv,
            lia_incremental_eager_override: previous.lia_incremental_eager_override,
            lra_incremental_eager_override: previous.lra_incremental_eager_override,
            lra_inc_engine_override: previous.lra_inc_engine_override,
            no_lra_theory_propagation: previous.no_lra_theory_propagation,
            counterexample_style: previous.counterexample_style,
            proof_tracker: previous.proof_tracker,
            proof_output_requested: previous.proof_output_requested,
            proof_artifact_required: previous.proof_artifact_required,
            interpolation_proof: previous.interpolation.enabled,
            proof_reconstruction_step_budget: previous.proof_reconstruction_step_budget,
            alethe_dialect: previous.alethe_dialect,
            learned_clause_limit: previous.learned_clause_limit,
            clause_db_bytes_limit: previous.clause_db_bytes_limit,
            verification_level: previous.verification_level,
            self_check: previous.self_check,
            competition_mode: previous.competition_mode,
            ematching_round_limit: previous.ematching_round_limit,
            progress_enabled: previous.progress_enabled,
            progress_json_path: previous.progress_json_path,
            aggressive_model_minimize: previous.aggressive_model_minimize,
            model_output_shed: previous.model_output_shed,
            lemma_persistence: previous.lemma_persistence,
            measured_negative_quantifier_routes: previous.measured_negative_quantifier_routes,
            solve_interrupt: previous.solve_interrupt,
            certification_parent: previous.certification_parent,
            solve_deadline: previous.solve_deadline,
            certification_deadline: previous.certification_deadline,
            command_deadline: previous.command_deadline,
            quantifier_deadline_policy: previous.quantifier_deadline_policy,
            quantifier_deadline_backstop_opt_in: previous.quantifier_deadline_backstop_opt_in,
            timeout: previous.timeout,
            resource_limit: previous.resource_limit,
            decision_limit: previous.decision_limit,
            ground_budget_enabled: previous.ground_budget_enabled,
            memory_limit: previous.memory_limit,
            term_memory_limit: previous.term_memory_limit,
            random_seed: previous.random_seed,
            query_publication_role: previous.query_publication_role,
            decision_command_depth: previous.decision_command_depth,
            prepass_reachability: previous.prepass_reachability,
            #[cfg(test)]
            test_force_non_bv_congruence_bail: previous.test_force_non_bv_congruence_bail,
            #[cfg(test)]
            test_euf_bv_congruence_clause_cap: previous.test_euf_bv_congruence_clause_cap,
            #[cfg(test)]
            last_applied_sat_random_seed: previous.last_applied_sat_random_seed,
            #[cfg(test)]
            last_applied_dpll_random_seed: previous.last_applied_dpll_random_seed,
            #[cfg(test)]
            last_oll_core_rounds: previous.last_oll_core_rounds,
            #[cfg(test)]
            forced_maxsmt_exact_cost: previous.forced_maxsmt_exact_cost,
            #[cfg(test)]
            forced_maxsmt_oll_core_anomaly: previous.forced_maxsmt_oll_core_anomaly,
            #[cfg(test)]
            forced_maxsmt_post_emit_soft_flip: previous.forced_maxsmt_post_emit_soft_flip,
            #[cfg(test)]
            forced_optimization_post_emit_objective_flip: previous
                .forced_optimization_post_emit_objective_flip,
            #[cfg(debug_assertions)]
            auflia_persistent_shadow: previous.auflia_persistent_shadow,
            #[cfg(debug_assertions)]
            demand_force_eager: previous.demand_force_eager,
        }
    }

    /// Install the carried-over configuration into a freshly built executor.
    fn install(self, executor: &mut Executor) {
        executor.debug_ufbv = self.debug_ufbv;
        executor.lia_incremental_eager_override = self.lia_incremental_eager_override;
        executor.lra_incremental_eager_override = self.lra_incremental_eager_override;
        executor.lra_inc_engine_override = self.lra_inc_engine_override;
        executor.no_lra_theory_propagation = self.no_lra_theory_propagation;
        executor.counterexample_style = self.counterexample_style;
        executor.proof_tracker = self.proof_tracker;
        executor.proof_output_requested = self.proof_output_requested;
        executor.proof_artifact_required = self.proof_artifact_required;
        executor.interpolation.enabled = self.interpolation_proof;
        executor.proof_reconstruction_step_budget = self.proof_reconstruction_step_budget;
        executor.alethe_dialect = self.alethe_dialect;
        executor.learned_clause_limit = self.learned_clause_limit;
        executor.clause_db_bytes_limit = self.clause_db_bytes_limit;
        executor.verification_level = self.verification_level;
        executor.self_check = self.self_check;
        executor.competition_mode = self.competition_mode;
        executor.ematching_round_limit = self.ematching_round_limit;
        executor.progress_enabled = self.progress_enabled;
        executor.progress_json_path = self.progress_json_path;
        executor.aggressive_model_minimize = self.aggressive_model_minimize;
        executor.model_output_shed = self.model_output_shed;
        executor.lemma_persistence = self.lemma_persistence;
        executor.measured_negative_quantifier_routes = self.measured_negative_quantifier_routes;
        executor.solve_interrupt = self.solve_interrupt;
        executor.certification_parent = self.certification_parent;
        executor.solve_deadline = self.solve_deadline;
        executor.certification_deadline = self.certification_deadline;
        executor.command_deadline = self.command_deadline;
        executor.quantifier_deadline_policy = self.quantifier_deadline_policy;
        executor.quantifier_deadline_backstop_opt_in = self.quantifier_deadline_backstop_opt_in;
        executor.timeout = self.timeout;
        executor.resource_limit = self.resource_limit;
        executor.decision_limit = self.decision_limit;
        executor.ground_budget_enabled = self.ground_budget_enabled;
        executor.memory_limit = self.memory_limit;
        executor.term_memory_limit = self.term_memory_limit;
        executor.random_seed = self.random_seed;
        executor.query_publication_role = self.query_publication_role;
        executor.decision_command_depth = self.decision_command_depth;
        executor.prepass_reachability = self.prepass_reachability;
        #[cfg(test)]
        {
            executor.test_force_non_bv_congruence_bail = self.test_force_non_bv_congruence_bail;
            executor.test_euf_bv_congruence_clause_cap = self.test_euf_bv_congruence_clause_cap;
            executor.last_applied_sat_random_seed = self.last_applied_sat_random_seed;
            executor.last_applied_dpll_random_seed = self.last_applied_dpll_random_seed;
            executor.last_oll_core_rounds = self.last_oll_core_rounds;
            executor.forced_maxsmt_exact_cost = self.forced_maxsmt_exact_cost;
            executor.forced_maxsmt_oll_core_anomaly = self.forced_maxsmt_oll_core_anomaly;
            executor.forced_maxsmt_post_emit_soft_flip = self.forced_maxsmt_post_emit_soft_flip;
            executor.forced_optimization_post_emit_objective_flip =
                self.forced_optimization_post_emit_objective_flip;
        }
        #[cfg(debug_assertions)]
        {
            executor.auflia_persistent_shadow = self.auflia_persistent_shadow;
            executor.demand_force_eager = self.demand_force_eager;
        }
    }
}

impl Executor {
    /// Replace every piece of problem, query and session-history state with a
    /// freshly constructed executor's, install `ctx` as the frontend context,
    /// and carry over the [`HostConfiguration`].
    ///
    /// `ctx` is the context the reset produced: for SMT-LIB `(reset)` the
    /// frontend's own reset (which keeps its host-configured retention policy
    /// and definitional budget), for [`Executor::reset`] a new context.
    pub(in crate::executor) fn reset_to_fresh_session(&mut self, ctx: Context) {
        // Revoke the old problem's artifacts through the ordinary funnel first,
        // so its diagnostics fire exactly as for any other invalidation.
        self.invalidate_last_check_result();
        // SMT-LIB `(reset)` restores options to their initial values: undo
        // every resource option the script set, back to the host's value.
        let script_options = std::mem::take(&mut self.script_resource_options);
        script_options.restore_host_values(self);
        let previous = std::mem::take(self);
        let mut configuration = HostConfiguration::take(previous);
        // The recorder's enabled state is host configuration; its ledger is
        // not. `reset` empties the ledger and replaces its identity.
        IncrementalSubsystem::reset(&mut configuration.proof_tracker);
        configuration.install(self);
        self.ctx = ctx;
    }
}
