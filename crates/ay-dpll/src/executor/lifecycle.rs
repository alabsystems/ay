// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Default for Executor {
    fn default() -> Self {
        Self::new()
    }
}

impl Executor {
    /// Commands that mutate the assertion/objective stack invalidate
    /// any cached check-sat artefacts (model/proof/unsat-assumptions).
    pub(super) fn command_invalidates_last_check_result(cmd: &Command) -> bool {
        matches!(
            cmd,
            Command::Assert(_)
                | Command::AssertSoft { .. }
                | Command::Push(_)
                | Command::Pop(_)
                | Command::Reset
                | Command::ResetAssertions
                | Command::Maximize(_)
                | Command::Minimize(_)
        )
    }

    /// Clear all query artefacts produced by the last check-sat call.
    ///
    /// This mirrors SMT-LIB solver behavior: after assertion-stack mutations,
    /// `get-model`, `get-proof`, and unsat-core/assumption queries are no
    /// longer valid until the next check-sat.
    pub(super) fn invalidate_last_check_result(&mut self) {
        self.last_result = None;
        self.last_model = None;
        self.last_sat_certificate = None;
        self.last_assumptions = None;
        self.last_assumption_core = None;
        self.last_core_term_to_name = None;
        self.last_proof = None;
        self.last_proof_term_overrides = None;
        self.proof_problem_assertion_provenance = None;
        self.quant_expansion_records.clear();
        self.last_proof_rebuild_originals.clear();
        self.last_proof_quality = None;
        self.last_unknown_reason = None;
        self.last_clause_trace = None;
        self.last_lrat_certificate = None;
        self.last_var_to_term = None;
        self.last_trail_provenance = None;
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
        self.proof_check_result = None;
        self.pending_sat_unknown_reason = None;
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.model_validation_delegated_assertions.clear();
        self.dt_solver_added_axiom_terms.clear();
        self.last_soft_cost = None;
        self.last_soft_cost_optimal = true;
        self.last_soft_violations = None;
        self.finite_objective_values.clear();
        self.unbounded_objectives.clear();
        self.infinitesimal_objectives.clear();
        self.unavailable_objectives.clear();
        self.objective_certificates.clear();
        // Pareto enumeration is stateful across consecutive `(check-sat)` calls
        // but MUST reset when the problem changes (a new assert / push / pop /
        // objective addition / reset all route through here). Dropping the state
        // forces the next pareto `(check-sat)` to start a fresh front, so a stale
        // front can never contaminate a different problem or corrupt lex / box /
        // single-objective / plain check-sat (none of which read this field).
        self.pareto_state = None;
    }

    /// Revoke every user-visible artefact at the start of a public decision
    /// query, before preflight or elaboration can fail. Consecutive Pareto
    /// queries are the sole case that may retain algorithmic enumeration state;
    /// the previously emitted result/model/certificate are still always cleared.
    pub(crate) fn begin_public_solve(&mut self, preserve_pareto_enumeration: bool) {
        let pareto_state = if preserve_pareto_enumeration {
            self.pareto_state.take()
        } else {
            None
        };
        self.invalidate_last_check_result();
        if preserve_pareto_enumeration {
            self.pareto_state = pareto_state;
        }
    }

    /// Native API assertions bypass `Command::Assert`, so they must manually
    /// invalidate stale solve artifacts.
    ///
    /// If a new assertion is added after any prior `check-sat` result, treat
    /// the session as incremental even without explicit push/pop. This keeps
    /// follow-up solves on the persistent-safe lanes used for accumulating
    /// blocking clauses and other post-solve refinement patterns.
    pub(crate) fn note_api_assertion_mutation(&mut self) {
        let had_prior_result = self.last_result.is_some();
        self.invalidate_last_check_result();
        if had_prior_result {
            self.incremental_mode = true;
        }
    }

    /// Native objective/soft registration changes the optimization problem and
    /// invalidates every result/model/optimum from the preceding query.
    ///
    /// Unlike an assertion mutation, adding an objective does not change the
    /// hard formula and therefore must not force the executor into incremental
    /// assertion mode. It still resets Pareto enumeration through the common
    /// invalidator, so a front can never survive an optimization-input change.
    pub(crate) fn note_api_optimization_mutation(&mut self) {
        self.invalidate_last_check_result();
    }

    /// Create a new executor
    #[must_use]
    pub fn new() -> Self {
        // Guard against small embedder/test thread stacks: constructing an
        // `Executor` builds a large (~56 KB) struct plus the frontend
        // `Context` through several by-value frames, which in low-opt builds
        // needs hundreds of KiB of stack (2026-07-18 deductive-checks embedder
        // overflow on libtest's default 2 MiB threads). Grow once so
        // construction succeeds regardless of the caller's remaining stack.
        stacker::maybe_grow(
            EXECUTOR_STACK_RED_ZONE,
            EXECUTOR_STACK_SIZE,
            Self::new_stack_guarded,
        )
    }

    /// Body of [`Executor::new`] — only called through the stack guard above
    /// so the struct-literal frames land on the grown segment.
    fn new_stack_guarded() -> Self {
        // Arm the process-wide memory ceiling for EVERY in-process embedder,
        // exactly once, only if the embedder has not chosen one. Previously
        // only the ay-bindings `execute_direct` entry armed it, so embedders
        // that drive `Executor` directly (e.g. proof-replay-consumer's AyProofBackend
        // inside compiler_consumer) ran with NO memory gate at all — the certify-lane
        // divergence that grew a rustc past 300 GB. Uses the EMBEDDED default
        // (~phys/8, 2–16 GB — see `default_embedded_memory_limit`): a
        // verification pass shares its host process, and an abandoned PDR
        // bit-blast was observed transiently holding ~28 GB under the
        // standalone phys/2 default. The gate only ever degrades a solve to
        // Unknown; standalone `ay` keeps its own explicit/auto limit.
        //
        // NOT under cfg(test): the auto-armed ceiling is PROCESS-GLOBAL state,
        // and the unit-test harness is one long-lived process running thousands
        // of solver tests whose aggregate allocator-retained footprint has
        // nothing to do with the CURRENT solve. On a 24 GiB host the embedded
        // default is 3 GiB; partway through the full `ay-dpll --lib` suite the
        // harness's cumulative footprint legitimately crosses 95% of that, and
        // from then on EVERY solve in the process — however tiny — degraded to
        // Unknown(MemoryLimit): ~1200+ load-dependent failures that vanish when
        // any test runs alone. Same principle as ay-sys's thread-local
        // `force_process_memory_exceeded_for_testing` hook: tests must never
        // couple through the process-global memory gate. Tests that exercise
        // the memory-exit paths use that thread-local force hook (honored even
        // with no limit armed); production embedders are unaffected — this arm
        // is compiled into every non-test build exactly as before.
        #[cfg(not(test))]
        {
            use std::sync::Once;
            static ARM: Once = Once::new();
            ARM.call_once(|| {
                if ay_sys::get_process_memory_limit() == 0 {
                    ay_sys::set_process_memory_limit(ay_sys::default_embedded_memory_limit());
                }
            });
        }
        Self {
            ctx: Context::new(),
            qfax_budget_multiplier: 1,
            qfax_refinement_clause: None,
            last_rejected_array_assertion: None,
            qfax_retry_done: false,
            arm_uflia_congruence_repair: false,
            split_eager_wander_abort: false,
            split_eager_relevancy_hard: false,
            split_lazy_relevancy_hard: false,
            split_lazy_detour_conflict_budget: None,
            uflia_congruence_lane: false,
            uflia_congruence_gate_rejected: false,
            uflia_congruence_retry_done: false,
            uflia_repair_candidates: Vec::new(),
            uflia_repair_conflict_tables: Vec::new(),
            uflia_model_repair_done: false,
            uflia_repair_detour_direct: false,
            uflia_repair_eager_direct: false,
            dt_lazy_auflia_eager_arm: false,
            bv_subst_lane: false,
            bv_subst_model_rejected: false,
            bv_subst_retry_done: false,
            bv_subst_retry_disable_preprocess: false,
            corroborating_nonstring_seq_unsat: false,
            last_result: None,
            last_model: None,
            active_support_axioms: Vec::new(),
            conflict_semantic_verify_memo: Default::default(),
            last_assumptions: None,
            last_assumption_core: None,
            last_core_term_to_name: None,
            last_proof: None,
            last_lrat_certificate: None,
            last_proof_term_overrides: None,
            proof_problem_assertion_provenance: None,
            quant_expansion_records: Vec::new(),
            last_proof_rebuild_originals: Vec::new(),
            last_proof_quality: None,
            last_unknown_reason: None,
            last_statistics: Statistics::default(),
            debug_ufbv: false,
            incremental_mode: false,
            lia_incremental_eager_override: None,
            lra_incremental_eager_override: None,
            lra_inc_engine_override: None,
            lra_persist_sat_active: false,
            no_lra_theory_propagation: false,
            incr_bv_state: None,
            incr_theory_state: None,
            counterexample_style: crate::CounterexampleStyle::default(),
            proof_tracker: crate::proof_tracker::ProofTracker::new(),
            proof_reconstruction_step_budget: None,
            last_clause_trace: None,
            last_var_to_term: None,
            last_trail_provenance: None,
            last_clausification_proofs: None,
            last_original_clause_theory_proofs: None,
            quantifier_manager: None,
            learned_clause_limit: None,
            clause_db_bytes_limit: None,
            resource_limit: None,
            decision_limit: None,
            ground_budget_enabled: true,
            memory_limit: None,
            solve_interrupt: None,
            #[cfg(test)]
            test_force_non_bv_congruence_bail: false,
            in_alternation_validation: false,
            in_closed_universal_precheck: false,
            in_quantified_model_gate: false,
            dt_cert_grant_active: false,
            solve_deadline: SolveDeadlineCell::new(),
            quantifier_deadline_backstop_installed: false,
            quantifier_pipeline_engaged: false,
            active_solve_phase: None,
            active_solve_cost_center: None,
            timeout: None,
            pivot_enum_depth: 0,
            mod_div_or_branch_rescue_depth: 0,
            post_split_verify_depth: 0,
            lra_in_assignment_recheck: false,
            final_lia_resolve_disabled: false,
            proof_check_result: None,
            proof_check_ok: false,
            pending_sat_unknown_reason: None,
            verification_level: VerificationLevel::from_state(false),
            self_check: false,
            dt_array_injectivity_gate_bypass: false,
            last_degrade_was_datatype_array: false,
            dt_pre_lift_assertions: Vec::new(),
            dt_lazy_splits: None,
            defer_model_validation: false,
            defer_counterexample_minimization: false,
            last_model_validated: false,
            last_sat_certificate: None,
            cegar_pending_lemma: None,
            cegar_rounds_remaining: 0,
            cegar_emitted_lemmas: HashSet::default(),
            last_validation_stats: None,
            model_validation_delegated_assertions: HashSet::default(),
            dt_solver_added_axiom_terms: HashSet::default(),
            skip_model_eval: false,
            read_pin_repair_done: false,
            nra_algebraic_model: HashMap::default(),
            dt_theory_model: None,
            dt_validation_wants_egraph: false,
            dt_egraph_assignment: std::cell::RefCell::new(None),
            dt_egraph_building: std::cell::Cell::new(false),
            recorded_var_substitutions: HashMap::default(),
            original_problem_had_quantifiers: false,
            sat_validated_by_mod_div_or_branch: false,
            bypass_string_tautology_guard: false,
            slia_accepted_unknown: false,
            self_check_authored_assertions: None,
            array_axiom_scope: None,
            row_seeded_terms: HashSet::default(),
            cached_store_eqs: Vec::new(),
            store_eq_scan_hwm: 0,
            cached_select_indices_by_array: HashMap::default(),
            select_index_scan_hwm: 0,
            last_negations: None,
            random_seed: None,
            ematching_round_limit: None,
            progress_enabled: false,
            progress_json_path: None,
            aggressive_model_minimize: false,
            #[cfg(test)]
            last_applied_sat_random_seed: Cell::new(None),
            #[cfg(test)]
            last_applied_dpll_random_seed: Cell::new(None),
            #[cfg(test)]
            last_oll_core_rounds: Cell::new(0),
            #[cfg(test)]
            forced_maxsmt_exact_cost: Cell::new(None),
            #[cfg(test)]
            forced_maxsmt_oll_core_anomaly: Cell::new(false),
            #[cfg(test)]
            forced_maxsmt_post_emit_soft_flip: Cell::new(false),
            #[cfg(test)]
            forced_optimization_post_emit_objective_flip: Cell::new(false),
            #[cfg(test)]
            last_diff_logic_decided: Cell::new(false),
            lemma_persistence: false,
            lemma_cache: lemma_cache::LemmaCache::new(),
            unbounded_objectives: HashMap::default(),
            infinitesimal_objectives: HashMap::default(),
            unavailable_objectives: HashSet::default(),
            objective_certificates: HashMap::default(),
            last_soft_cost: None,
            last_soft_cost_optimal: true,
            last_soft_violations: None,
            finite_objective_values: HashMap::default(),
            pareto_state: None,
            independent_gate_disabled: false,
            array_ext_shadow: ArrayExtShadow::default(),
            // M-A2 lazy-persistent-combiner shadow: OFF by default (§5 A2).
            #[cfg(debug_assertions)]
            auflia_persistent_shadow: false,
            // M5 demand-lane: PRODUCTION-authoritative for classified families;
            // the debug-only force-eager differential override is OFF by default.
            #[cfg(debug_assertions)]
            demand_force_eager: false,
        }
    }

    /// Enable/disable the M-A2 lazy-persistent-combiner SHADOW arm
    /// (ARRAY-PROCEDURE-CLOSER-BLUEPRINT §5 A2 / LAZY-M3 §M3.2).
    ///
    /// DEBUG-ONLY, test/diagnostic use only. When enabled, the lazy AUFLIA loop
    /// runs a create-once + warm-reset persistent `TheoryCombiner` in SHADOW
    /// alongside the authoritative fresh-per-round combiner, comparing per-round
    /// verdicts + lemma/conflict reason-sets. The persistent path is purely
    /// observational — it NEVER overrides the fresh verdict and it borrows a
    /// private term-store snapshot, so it cannot change solving behavior. The
    /// per-round engage count and DISAGREE count are surfaced on the stats
    /// channel (`auflia.shadow.*`). NOT a shipping mode: there is deliberately no
    /// env-var or CLI switch, and no production path enables it. Compiled out in
    /// release (this setter does not exist there), so the default (fresh-only)
    /// behavior is byte-identical.
    #[cfg(debug_assertions)]
    pub fn set_auflia_persistent_shadow(&mut self, enabled: bool) {
        self.auflia_persistent_shadow = enabled;
    }

    /// Whether the M-A2 lazy-persistent-combiner shadow arm is active for this
    /// solve. Compile-time absent in release. Test-only introspection.
    #[cfg(debug_assertions)]
    pub(crate) fn auflia_persistent_shadow_active(&self) -> bool {
        self.auflia_persistent_shadow
    }

    /// Force the OLD eager geometric level-0 minting instead of the M5 production
    /// demand lane, for THIS solve (`demand-driven-instantiation-campaign` memory,
    /// M5 differential).
    ///
    /// DEBUG-ONLY, test/diagnostic use only. Since the M5 flip the demand-driven
    /// frontier-gated lane is the PRODUCTION path for M1-classified self-chaining /
    /// bridge-cycle families; this override reinstates the pre-flip eager path so
    /// the differential harness can compare production-demand against forced-eager
    /// on the same problem. NOT a shipping mode: no env-var or CLI switch, and the
    /// setter is compiled out in release (where the lane is unconditionally the
    /// production path).
    #[cfg(debug_assertions)]
    pub fn set_demand_force_eager(&mut self, enabled: bool) {
        self.demand_force_eager = enabled;
    }

    /// M5 FLIP — whether the demand-driven-instantiation lane is ELIGIBLE to arm
    /// for this solve. This is the PRODUCTION gate: the lane is the authoritative
    /// path for the M1 self-chaining / bridge-cycle families, always-on in release
    /// AND debug. Eligibility does NOT by itself arm the lane — the lane arms
    /// (per-solve, on the `QuantifierManager` via `demand_arm`) ONLY if the family
    /// classifier finds >=1 classified family (`gated` non-empty). A solve with no
    /// classified family never arms, so [`Self::demand_lane_armed`] stays `false`
    /// and every downstream gate is inert — byte-identical to the pre-flip eager
    /// path. The debug-only `demand_force_eager` override is the ONLY way to make
    /// this `false`; it is compiled out in release, so production is always
    /// eligible.
    pub(crate) fn demand_lane_eligible(&self) -> bool {
        #[cfg(debug_assertions)]
        {
            !self.demand_force_eager
        }
        #[cfg(not(debug_assertions))]
        {
            true
        }
    }

    /// M5 FLIP — whether the demand lane is ACTUALLY armed for this solve, i.e. the
    /// classifier found >=1 self-chaining / bridge-cycle family and
    /// `run_ematching_rounds` armed the per-solve `DemandLaneState`. This is the
    /// FAMILY-SCOPED gate consulted by every downstream site (DT resume/ceiling,
    /// `demand_refine`, the certificate discipline): when no classified family is
    /// present it is `false`, so those sites run the eager path byte-identically.
    /// Independent of build profile — it reflects real per-solve state, not the
    /// debug override.
    pub(crate) fn demand_lane_armed(&self) -> bool {
        self.quantifier_manager
            .as_ref()
            .is_some_and(QuantifierManager::demand_active)
    }

    /// Enable or disable the independent fail-closed model-check gate.
    ///
    /// The gate is ON by default. When ON, every `Sat` result is re-checked by
    /// [`ay_model_check::confirm_model`] against the assertions; a `Sat` whose
    /// model the gate ground-refutes (`ModelViolates`) is unconditionally
    /// downgraded to `Unknown` (a coverage gap the gate cannot evaluate is
    /// recorded but keeps the verdict). Disabling the gate is a DEBUGGING-ONLY
    /// escape hatch; no production path calls this with `false`.
    pub fn set_independent_model_gate(&mut self, enabled: bool) {
        self.independent_gate_disabled = !enabled;
    }

    /// Whether the independent model-check gate is currently enabled.
    #[must_use]
    pub fn independent_model_gate_enabled(&self) -> bool {
        !self.independent_gate_disabled
    }

    /// Create a new executor with a specific verification level (#4444).
    #[must_use]
    pub fn with_verification_level(level: VerificationLevel) -> Self {
        let mut exec = Self::new();
        exec.verification_level = level;
        exec
    }

    /// Get the current verification level.
    #[must_use]
    pub fn verification_level(&self) -> VerificationLevel {
        self.verification_level
    }

    /// Set the verification level.
    pub fn set_verification_level(&mut self, level: VerificationLevel) {
        self.verification_level = level;
    }

    /// Enable or disable fail-closed self-check mode (`--self-check`).
    ///
    /// In self-check mode AY only emits a `sat`/`unsat` it can verify itself:
    /// SAT requires the independent model evaluator to confirm every assertion
    /// (else the result degrades to `Unknown`), and UNSAT requires a checked
    /// refutation proof. This trades completeness for self-certified soundness.
    pub fn set_self_check(&mut self, enabled: bool) {
        self.self_check = enabled;
    }

    /// Whether fail-closed self-check mode is active.
    #[must_use]
    pub fn self_check(&self) -> bool {
        self.self_check
    }

    /// Access the internal context (for API module)
    pub fn context(&self) -> &Context {
        &self.ctx
    }

    /// Access the internal context mutably (for API module)
    pub fn context_mut(&mut self) -> &mut Context {
        &mut self.ctx
    }

    /// Result from the last internal proof validation (#4393).
    ///
    /// Returns `None` if no proof validation has been performed (e.g., last
    /// result was SAT, or proofs are not enabled). Returns `Some` with the
    /// partial check result after any UNSAT proof generation.
    pub fn proof_check_result(&self) -> Option<&PartialProofCheck> {
        self.proof_check_result.as_ref()
    }

    /// Enable debug output for QF_UFBV solving
    pub fn set_debug_ufbv(&mut self, enabled: bool) {
        self.debug_ufbv = enabled;
    }

    /// Set the counterexample style for model generation
    ///
    /// This affects how `get-model` generates values:
    /// - `Any`: Return any satisfying value (fast, current behavior)
    /// - `Minimal`: Prefer 0, ±1, powers of 2, MIN/MAX (default)
    /// - `Readable`: Prefer round numbers and simple values
    pub fn set_counterexample_style(&mut self, style: crate::CounterexampleStyle) {
        self.counterexample_style = style;
    }

    /// Get the current counterexample style.
    #[must_use]
    pub fn counterexample_style(&self) -> crate::CounterexampleStyle {
        self.counterexample_style
    }

    /// Enable or disable proof production
    ///
    /// When enabled, the solver collects proof steps during solving.
    /// After an UNSAT result, call `get_proof()` to retrieve the proof.
    ///
    /// This is required for VerifierConsumer integration (proof certificates).
    pub fn set_produce_proofs(&mut self, enabled: bool) {
        if enabled {
            self.proof_tracker.enable();
            // Proof export aligns Assume steps with the ORIGINAL parsed
            // surface syntax, so retention must be on whenever proofs are.
            self.ctx.set_retain_parsed_assertions(true);
        } else {
            self.proof_tracker.disable();
        }
    }

    /// Configure whether the frontend context retains the original parsed AST
    /// of every assertion (`assertions_parsed`).
    ///
    /// The parsed stack exists ONLY to align exported proofs with surface
    /// syntax; retaining it is a large peak-RSS cost on parse-heavy inputs
    /// (#rss-vs-z3 campaign). The CLI turns retention OFF when the session can
    /// never emit a proof (`--no-proof`, `--z3-mode`, competition mode). A
    /// later `set_produce_proofs(true)` or in-script
    /// `(set-option :produce-proofs true)` turns it back on. Verdicts are
    /// unaffected — every consumer degrades gracefully on an empty prefix.
    pub fn set_retain_parsed_assertions(&mut self, retain: bool) {
        self.ctx.set_retain_parsed_assertions(retain);
    }

    /// Check if proof production is enabled
    #[must_use]
    pub fn is_producing_proofs(&self) -> bool {
        self.proof_tracker.is_enabled()
    }

    /// Bound post-UNSAT SAT-proof reconstruction with a deterministic step
    /// budget (RUP-replay clause scans). Intended ONLY for the
    /// synthesized-default proof-carrying certificate: when the budget runs
    /// out, no proof is reconstructed (the caller degrades to the existing
    /// "no proof certificate emitted" warning) and the verdict — already
    /// decided before reconstruction starts — is unchanged. Explicit proof
    /// requests (`--proof`, `--strict-proofs`, `:produce-proofs` /
    /// `(get-proof)`) must NOT set a budget. Deterministic by construction:
    /// a step count, never wall time (#A2b).
    pub fn set_proof_reconstruction_step_budget(&mut self, budget: Option<u64>) {
        self.proof_reconstruction_step_budget = budget;
    }

    /// Search-time proof bookkeeping work budget for SAT solvers created by
    /// this executor (#A2b construction budget).
    ///
    /// Derived from `proof_reconstruction_step_budget` (only set for
    /// synthesized-default certificates) scaled by
    /// `SEARCH_PROOF_BOOKKEEPING_WORK_DIVISOR`: the search-time meter is
    /// byte-denominated — clause-trace bytes recorded, LRAT
    /// clause-replacement bytes, and root-trail entries rescanned by level-0
    /// LRAT unit materialization. An in-script
    /// `(set-option :produce-proofs true)` is an explicit SMT-LIB demand for
    /// a proof and disables the budget, mirroring
    /// `try_derive_empty_via_sat_resolution`.
    pub(crate) fn search_proof_bookkeeping_budget(&self) -> Option<u64> {
        Self::search_proof_bookkeeping_budget_for(&self.ctx, self.proof_reconstruction_step_budget)
    }

    /// Associated-function form of [`Self::search_proof_bookkeeping_budget`]
    /// for call sites where `self` is already partially borrowed (persistent
    /// SAT state setup): takes the two disjoint fields directly.
    pub(crate) fn search_proof_bookkeeping_budget_for(
        ctx: &Context,
        reconstruction_budget: Option<u64>,
    ) -> Option<u64> {
        /// Calibrated so every currently carcara-valid synthesized-default
        /// certificate (eq_diamond / SEQ / CAV_2009 / read2 families) still
        /// materializes fully, while pathological proof-bookkeeping-heavy
        /// runs (QF_ALIA pointer-safe-5: unknown at 127s with unbounded
        /// bookkeeping) exhaust and degrade to no-proof search EARLY —
        /// before the proof-clamped inprocessing rounds diverge the search
        /// beyond recovery. Recalibrated 2026-07-12 when the search-time
        /// meter switched from root-trail-entry counts to byte-denominated
        /// units (clause-trace bytes recorded + LRAT clause-replacement
        /// bytes): measured consumption on the protected certificate
        /// families is ~28 units (eq_diamond10 / SEQ015_size2) to ~150K
        /// (read2), while pointer-safe-5 burns 2M within its first six
        /// incremental-inprocessing rounds and must degrade within its
        /// first two to converge. reconstruction_budget / DIVISOR = 250K
        /// sits between with margin on both sides.
        const SEARCH_PROOF_BOOKKEEPING_WORK_DIVISOR: u64 = 4;
        let script_demands_proof = matches!(
            ctx.get_option("produce-proofs"),
            Some(OptionValue::Bool(true))
        );
        if script_demands_proof {
            return None;
        }
        reconstruction_budget.map(|b| (b / SEARCH_PROOF_BOOKKEEPING_WORK_DIVISOR).max(1))
    }

    /// Set the maximum learned clauses limit for SAT solving (#1609)
    pub fn set_learned_clause_limit(&mut self, limit: Option<usize>) {
        self.learned_clause_limit = limit;
    }

    /// Get the current learned clause limit
    pub fn learned_clause_limit(&self) -> Option<usize> {
        self.learned_clause_limit
    }

    /// Set the maximum clause DB size (bytes) limit for SAT solving (#1609)
    pub fn set_clause_db_bytes_limit(&mut self, limit: Option<usize>) {
        self.clause_db_bytes_limit = limit;
    }

    /// Get the current clause DB size (bytes) limit
    pub fn clause_db_bytes_limit(&self) -> Option<usize> {
        self.clause_db_bytes_limit
    }

    /// Set the deterministic resource limit (`:rlimit`, #8749).
    ///
    /// Measured in SAT conflicts — a machine-independent proxy for solver
    /// effort, unlike wall-clock `:timeout`. `None` means no budget. When the
    /// budget is hit, solving stops with [`UnknownReason::ResourceLimit`].
    pub fn set_resource_limit(&mut self, limit: Option<u64>) {
        self.resource_limit = limit;
    }

    /// Get the current deterministic resource limit (conflicts).
    pub fn resource_limit(&self) -> Option<u64> {
        self.resource_limit
    }

    /// Set the deterministic per-SAT-solve DECISION budget
    /// (#ground-determinism), the decision-count companion of
    /// [`Self::set_resource_limit`]. Measured in SAT decisions — the effort
    /// axis that bounds decision-heavy / conflict-light theory-extension
    /// churn a conflict budget cannot see. `None` means "use the default
    /// ground allowance when the ground budget is enabled". When the budget
    /// is hit, solving stops with [`UnknownReason::ResourceLimit`].
    pub fn set_decision_limit(&mut self, limit: Option<u64>) {
        self.decision_limit = limit;
    }

    /// Get the current explicit deterministic decision limit.
    pub fn decision_limit(&self) -> Option<u64> {
        self.decision_limit
    }

    /// Enable/disable the DEFAULT deterministic ground-phase budget
    /// (#ground-determinism). Enabled by default; `(set-option :rlimit 0)`
    /// disables it (true opt-out to unbounded solving). See
    /// `crate::pipeline_fns::effective_conflict_allowance` for the semantics.
    pub fn set_ground_budget_enabled(&mut self, enabled: bool) {
        self.ground_budget_enabled = enabled;
    }

    /// Whether the default deterministic ground-phase budget is in force.
    pub fn ground_budget_enabled(&self) -> bool {
        self.ground_budget_enabled
    }

    /// Per-SAT-solve conflict allowance for the current configuration
    /// (#ground-determinism).
    ///
    /// An explicit `:rlimit` (see [`Self::set_resource_limit`]) always wins;
    /// otherwise the DEFAULT ground budget supplies
    /// [`Self::DEFAULT_GROUND_CONFLICT_ALLOWANCE`] unless disabled
    /// (`set_ground_budget_enabled(false)`, `:rlimit 0`, or the
    /// `AY_NO_GROUND_BUDGET` env knob). `None` = no conflict budget.
    ///
    /// Field-only free-function core lives in `pipeline_fns` so the pipeline
    /// macros can call it while holding disjoint `&mut` borrows of other
    /// executor fields. Production goes through that core directly; this
    /// method wrapper is exercised by the executor tests.
    #[cfg(test)]
    pub(crate) fn effective_conflict_allowance(&self) -> Option<u64> {
        crate::pipeline_fns::effective_conflict_allowance(
            self.resource_limit,
            self.ground_budget_enabled,
        )
    }

    /// Per-SAT-solve decision allowance for the current configuration
    /// (#ground-determinism). An explicit [`Self::set_decision_limit`] wins;
    /// otherwise the default ground allowance applies while the ground
    /// budget is in force (an explicit `:rlimit` keeps it active —
    /// `:rlimit` is a CONFLICT budget and does not replace the decision
    /// bound). `None` = no decision budget.
    ///
    /// Test-only wrapper over `crate::pipeline_fns::effective_decision_allowance`
    /// (production calls the free-function core directly).
    #[cfg(test)]
    pub(crate) fn effective_decision_allowance(&self) -> Option<u64> {
        crate::pipeline_fns::effective_decision_allowance(
            self.decision_limit,
            self.ground_budget_enabled,
        )
    }

    /// Set the process-RSS ceiling (bytes) backing `:max-memory`.
    ///
    /// `None` means no limit. When a solve crosses this bound the active
    /// check-sat stops with [`UnknownReason::MemoryLimit`].
    pub fn set_memory_limit(&mut self, limit: Option<usize>) {
        self.memory_limit = limit;
    }

    /// Get the current process-RSS ceiling (bytes).
    pub fn memory_limit(&self) -> Option<usize> {
        self.memory_limit
    }

    /// Disable (or re-enable) LRA theory propagation inside LIA theory
    /// solvers created by this executor.
    ///
    /// Per-executor counterpart of the process-global
    /// `AY_NO_THEORY_PROPAGATION` debug flag, applied via
    /// `LraSolver::set_no_theory_propagation` on the LRA solver embedded in
    /// every `LiaSolver` this executor constructs. Default off.
    ///
    /// Intended caller: the CHC BMC transition-system lane (sat-type
    /// counterexample search). On DRAGON-class QF_LIA model searches,
    /// BCP-time LRA implied-bounds propagation causes a CDCL search livelock
    /// — long interval-reconstructed reasons produce weak learned clauses,
    /// suppressed early conflicts trip the adaptive theory-decision mode
    /// (#9505), and LP-model phase hints override phase saving — turning
    /// 9ms-class queries (z3) into >300s timeouts. With propagation off the
    /// same queries solve in ~1s with identical verdicts
    /// (the development design notes).
    pub fn set_no_lra_theory_propagation(&mut self, disabled: bool) {
        self.no_lra_theory_propagation = disabled;
    }

    /// Whether LIA theory solvers created by this executor disable LRA
    /// theory propagation (see [`Self::set_no_lra_theory_propagation`]).
    #[must_use]
    pub fn no_lra_theory_propagation(&self) -> bool {
        self.no_lra_theory_propagation
    }

    /// Set the random seed for SAT solver VSIDS tie-breaking (#6961).
    ///
    /// Different seeds produce different variable selection orders for
    /// tied activities, leading to different search paths. Useful for
    /// catching non-deterministic solver bugs via seed perturbation.
    pub fn set_random_seed(&mut self, seed: u64) {
        self.random_seed = Some(seed);
    }

    /// Enable periodic progress line emission on SAT solvers used during solving.
    ///
    /// When enabled, all SAT solver instances created by this executor emit
    /// a compact one-line status summary to stderr approximately every 5
    /// seconds during CDCL solving. Forwarded to DpllT and raw SAT solvers.
    pub fn set_progress_enabled(&mut self, enabled: bool) {
        self.progress_enabled = enabled;
    }

    /// Set the JSONL progress file path (#8155 subtask 7b).
    ///
    /// When `Some`, every SAT solver instance created by this executor
    /// attaches a [`ay_sat::json_observer::JsonProgressObserver`] that
    /// writes versioned JSONL events to the given path (append mode).
    pub fn set_progress_json(&mut self, path: Option<String>) {
        self.progress_json_path = path;
    }

    /// Enable aggressive model minimization (#8297).
    ///
    /// When enabled, an additional minimization pass runs after each SAT result
    /// that aggressively targets BV variables with 0/1 candidates beyond the
    /// standard `minimize_model_sat_preserving()` pipeline. This produces
    /// minimal counterexamples suitable for vulnerability analysis.
    pub fn set_aggressive_model_minimize(&mut self, enabled: bool) {
        self.aggressive_model_minimize = enabled;
    }

    /// Check whether aggressive model minimization is enabled.
    #[must_use]
    pub fn aggressive_model_minimize(&self) -> bool {
        self.aggressive_model_minimize
    }

    /// Get the current random seed, if set.
    #[must_use]
    pub fn random_seed(&self) -> Option<u64> {
        self.random_seed
    }

    /// Proof from the last UNSAT result.
    ///
    /// Returns None if the last result was not UNSAT or if proof production was disabled.
    #[must_use]
    pub fn last_proof(&self) -> Option<&Proof> {
        self.last_proof.as_ref()
    }

    /// Get access to the term store
    #[must_use]
    pub fn terms(&self) -> &TermStore {
        &self.ctx.terms
    }

    #[cfg(test)]
    #[must_use]
    pub(crate) fn has_proof_problem_assertion_provenance(&self) -> bool {
        self.proof_problem_assertion_provenance.is_some()
    }

    pub(super) fn produce_models_enabled(&self) -> bool {
        matches!(
            self.ctx.get_option("produce-models"),
            Some(OptionValue::Bool(true))
        )
    }

    /// Resolve the effective counterexample style from the typed API field and
    /// the SMT-LIB option. The SMT-LIB option takes precedence when explicitly set.
    pub(crate) fn effective_counterexample_style(&self) -> crate::CounterexampleStyle {
        match self.ctx.get_option("minimize-counterexamples") {
            Some(OptionValue::Bool(true)) => crate::CounterexampleStyle::Minimal,
            Some(OptionValue::Bool(false)) => crate::CounterexampleStyle::Any,
            _ => self.counterexample_style,
        }
    }

    pub(super) fn minimize_counterexamples_enabled(&self) -> bool {
        !matches!(
            self.effective_counterexample_style(),
            crate::CounterexampleStyle::Any
        )
    }

    /// Reset the executor to initial state.
    ///
    /// Aligns with the SMT-LIB `(reset)` command handler: resets all solving
    /// state, incremental state, quantifier manager, proof tracking, and
    /// interrupt/deadline. Configuration settings (debug_ufbv,
    /// counterexample_style, learned clause limits, verification_level)
    /// are preserved.
    pub fn reset(&mut self) {
        self.ctx = Context::new();
        self.last_result = None;
        self.last_model = None;
        self.last_assumptions = None;
        self.last_assumption_core = None;
        self.last_core_term_to_name = None;
        self.last_proof = None;
        self.last_proof_term_overrides = None;
        self.last_proof_quality = None;
        self.last_unknown_reason = None;
        self.pending_sat_unknown_reason = None;
        self.last_statistics = Statistics::default();
        self.last_clause_trace = None;
        self.last_var_to_term = None;
        self.last_trail_provenance = None;
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
        self.proof_problem_assertion_provenance = None;
        self.quant_expansion_records.clear();
        self.last_negations = None;
        self.incremental_mode = false;
        self.pivot_enum_depth = 0;
        self.proof_check_result = None;
        self.defer_model_validation = false;
        self.defer_counterexample_minimization = false;
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.model_validation_delegated_assertions.clear();
        self.dt_solver_added_axiom_terms.clear();
        self.skip_model_eval = false;
        self.read_pin_repair_done = false;
        self.nra_algebraic_model.clear();
        self.clear_dt_theory_model();
        self.recorded_var_substitutions.clear();
        self.bypass_string_tautology_guard = false;
        self.slia_accepted_unknown = false;
        self.array_axiom_scope = None;
        self.row_seeded_terms.clear();
        self.cached_store_eqs.clear();
        self.store_eq_scan_hwm = 0;
        self.cached_select_indices_by_array.clear();
        self.select_index_scan_hwm = 0;
        self.solve_interrupt = None;
        self.solve_deadline.set(None);
        self.quantifier_deadline_backstop_installed = false;
        self.quantifier_pipeline_engaged = false;
        self.last_soft_cost = None;
        self.last_soft_cost_optimal = true;
        self.last_soft_violations = None;
        self.finite_objective_values.clear();
        self.unbounded_objectives.clear();
        self.infinitesimal_objectives.clear();
        self.unavailable_objectives.clear();
        self.objective_certificates.clear();
        self.lemma_cache.clear();
        for_each_incremental_subsystem!(reset self);
    }
}
