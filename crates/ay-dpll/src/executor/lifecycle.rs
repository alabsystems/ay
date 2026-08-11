// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;

impl Default for Executor {
    fn default() -> Self {
        Self::new()
    }
}

impl Executor {
    /// Execute a native-API declaration outside SMT-LIB assertion scoping.
    ///
    /// Native declaration handles belong to the solver context rather than an
    /// assertion frame. The frontend helper updates existing scope snapshots
    /// without changing either spelling of the public global-declarations
    /// option; the executor then retires artifacts from the preceding decision
    /// just as [`Executor::execute`] does for an ordinary declaration command.
    pub(crate) fn execute_native_global_declaration(&mut self, cmd: &Command) -> Result<()> {
        self.ctx.execute_native_global_declaration(cmd)?;
        self.invalidate_last_check_result();
        Ok(())
    }

    /// Register a native constant globally and retire the preceding decision.
    pub(crate) fn register_native_global_symbol(&mut self, name: String, term: TermId, sort: Sort) {
        self.ctx.register_native_global_symbol(name, term, sort);
        self.invalidate_last_check_result();
    }

    /// Register a native function's surface alias globally and retire the
    /// preceding decision if the registration succeeds.
    pub(crate) fn register_native_global_function_alias(
        &mut self,
        surface_name: String,
        internal_name: String,
        arg_sorts: Vec<Sort>,
        ret_sort: Sort,
    ) -> Result<()> {
        let changed = self.ctx.register_native_global_function_alias(
            surface_name,
            internal_name,
            arg_sorts,
            ret_sort,
        )?;
        if changed {
            self.invalidate_last_check_result();
        }
        Ok(())
    }

    /// Register a native function alias with an exact public signature.
    pub(crate) fn register_native_global_public_function_alias(
        &mut self,
        surface_name: String,
        internal_name: String,
        public_arg_sorts: Vec<ay_frontend::PublicSort>,
        public_sort: ay_frontend::PublicSort,
    ) -> Result<()> {
        let changed = self.ctx.register_native_global_public_function_alias(
            surface_name,
            internal_name,
            public_arg_sorts,
            public_sort,
        )?;
        if changed {
            self.invalidate_last_check_result();
        }
        Ok(())
    }

    /// Retire a completed decision after a native API mutation that is held in
    /// the API layer rather than represented by a frontend command.
    pub(crate) fn invalidate_for_native_api_mutation(&mut self) {
        self.invalidate_last_check_result();
    }

    /// Every command that changes the problem signature, semantics, assertion
    /// stack, Horn/SyGuS problem, or objectives invalidates cached check-sat
    /// artefacts (model/proof/core/unsat-assumptions). Pure options and queries
    /// deliberately do not: changing presentation settings or asking for an
    /// artefact cannot make the preceding decision stale.
    pub(super) fn command_invalidates_last_check_result(cmd: &Command) -> bool {
        matches!(
            cmd,
            Command::SetLogic(_)
                | Command::DeclareSort(..)
                | Command::DeclareSortParameter(..)
                | Command::DefineSort(..)
                | Command::DeclareDatatype(..)
                | Command::DeclareDatatypes(..)
                | Command::DeclareFun(..)
                | Command::DeclareConst(..)
                | Command::DeclareVar(..)
                | Command::DeclareRel(..)
                | Command::Rule(..)
                | Command::Query(..)
                | Command::DefineFun(..)
                | Command::DefineFunRec(..)
                | Command::DefineFunsRec(..)
                | Command::SynthFun(..)
                | Command::SynthInv(..)
                | Command::SygusConstraint(..)
                | Command::InvConstraint(..)
                | Command::Assert(_)
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
        self.last_unsat_certificate = None;
        self.last_assumptions = None;
        self.last_assumption_core = None;
        self.last_core_term_to_name = None;
        self.last_proof = None;
        self.last_proof_term_overrides = None;
        self.proof_problem_assertion_provenance = None;
        self.quant_expansion_records.clear();
        self.ematching_proof_records.clear();
        self.last_proof_rebuild_originals.clear();
        self.last_proof_quality = None;
        self.last_unknown_reason = None;
        self.last_unknown_origin = None;
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

    /// Close every decision-trace writer retained by an incremental SAT lane.
    ///
    /// Persistent solvers keep their buffered writer across `check-sat` calls.
    /// A CLI-level fail-closed result must detach those file descriptors before
    /// removing the now-non-authoritative trace; reopening or truncating the
    /// path while an old writer remains live can corrupt or re-expose it.
    fn detach_persistent_decision_trace_writers(&mut self) {
        if let Some(state) = self.incr_bv_state.as_mut() {
            if let Some(sat) = state.persistent_sat.as_mut() {
                sat.disable_decision_trace();
            }
        }
        if let Some(state) = self.incr_theory_state.as_mut() {
            if let Some(sat) = state.persistent_sat.as_mut() {
                sat.disable_decision_trace();
            }
            if let Some(sat) = state.lia_persistent_sat.as_mut() {
                sat.disable_decision_trace();
            }
        }
        if ay_core::trace_config().decision_trace_path.is_some() {
            // Once a public/raw mismatch occurs, a later partial trace cannot
            // replay the full session honestly. Leave tracing disabled for the
            // rest of this process instead of silently starting a forged stream.
            ay_sat::suppress_decision_trace_after_public_mismatch();
        }
    }

    /// Publish `Unknown` from an authoritative production origin and revoke
    /// every artifact belonging to an older or partially completed decision.
    ///
    /// CLI preflight rejection and panic containment can decide to fail closed
    /// without receiving a normal `Unknown` from the solver. This canonical
    /// transition prevents subsequent model/proof/core queries from observing
    /// a stale result. Decision tracing is also detached and permanently
    /// suppressed when configured, because replay would reproduce the solver's
    /// raw result rather than the external boundary's synthesized result.
    pub(crate) fn publish_unknown_from_origin(&mut self, origin: UnknownOrigin) {
        self.detach_persistent_decision_trace_writers();
        self.invalidate_last_check_result();
        self.last_result = Some(SolveResult::Unknown);
        self.last_unknown_reason = Some(origin.reason());
        self.last_unknown_origin = Some(origin);
    }

    /// Compatibility entrypoint for existing external fail-closed callers.
    ///
    /// The reason is immediately converted to its unique registered origin;
    /// callers cannot create a mismatched reason/origin pair.
    pub fn replace_last_result_with_unknown(&mut self, reason: UnknownReason) {
        self.publish_unknown_from_origin(reason.origin());
    }

    /// Classify a provisional internal Unknown through the typed origin
    /// registry. The public solve boundary subsequently calls
    /// [`Self::finalize_unknown_publication`] to revoke artifacts and publish
    /// the result. Production origin sites use this instead of independently
    /// pairing a reason with a code string.
    pub(crate) fn record_unknown_from_origin(&mut self, origin: UnknownOrigin) {
        self.last_unknown_reason = Some(origin.reason());
        self.last_unknown_origin = Some(origin);
    }

    /// Inject an exact registered production origin for the authenticated
    /// conformance executable's negative/coverage campaign.
    ///
    /// This is not a solver option and ordinary solving never calls it. The
    /// hidden probe reports the injection honestly and pairs it with the
    /// audited production chokepoint from [`UnknownOrigin::production_chokepoint`].
    #[doc(hidden)]
    pub fn conformance_inject_unknown_origin(&mut self, origin: UnknownOrigin) {
        self.record_unknown_from_origin(origin);
        let _ = self.finalize_unknown_publication(SolveResult::Unknown);
    }

    /// Apply the mandatory public Unknown boundary to a provisional result.
    ///
    /// This is intentionally idempotent. Every public solve route calls it
    /// after the internal lane chooses a result, so direct internal writes to
    /// `last_unknown_reason` cannot bypass result-artifact revocation.
    pub(crate) fn finalize_unknown_publication(&mut self, proposed: SolveResult) -> SolveResult {
        if proposed.is_unknown() {
            let reason = self.last_unknown_reason.unwrap_or(UnknownReason::Unknown);
            self.publish_unknown_from_origin(reason.origin());
            SolveResult::Unknown
        } else {
            self.last_unknown_origin = None;
            proposed
        }
    }

    /// Exact production origin for the last public Unknown result.
    #[must_use]
    pub fn unknown_origin(&self) -> Option<UnknownOrigin> {
        self.last_result
            .as_ref()
            .is_some_and(SolveResult::is_unknown)
            .then_some(self.last_unknown_origin)
            .flatten()
    }

    /// Reject the current internal UNSAT at a mandatory certification boundary.
    ///
    /// This is the canonical fail-closed transition used after a post-solve
    /// checker refuses an UNSAT result. It clears every UNSAT-derived model,
    /// proof, core, assumption, optimization, and certificate cache before
    /// installing `Unknown`, so all later SMT-LIB queries and EOF consumers see
    /// the public verdict rather than the rejected internal one.
    ///
    /// Returns `false` without changing state unless the current result is
    /// UNSAT. That precondition keeps result gates from accidentally upgrading
    /// a missing, SAT, or already-unknown result.
    pub fn reject_last_unsat_as_unknown(&mut self) -> bool {
        if !self.last_result_is_unsat() {
            return false;
        }
        self.replace_last_result_with_unknown(UnknownReason::Incomplete);
        true
    }

    /// Revoke every user-visible artefact at the start of a public decision
    /// query, before preflight or elaboration can fail. Consecutive Pareto
    /// queries are the sole case that may retain algorithmic enumeration state;
    /// the previously emitted result/model/certificate are still always cleared.
    pub(crate) fn begin_public_solve(&mut self, preserve_pareto_enumeration: bool) {
        self.array_ext_witness_cache
            .begin_public_solve(&self.ctx.terms);
        // Proof output is optional; proof-backed UNSAT correctness is not.
        // Enable internal proof tracking for every public decision before the
        // authored scope is finalized. `--no-proof` and `:produce-proofs false`
        // still suppress user-facing artifacts, but cannot disable the soundness
        // certificate required to publish `unsat`.
        self.proof_tracker.enable();
        self.ctx.set_retain_parsed_assertions(true);
        let authored_assertions = self.ctx.assertions.clone();
        let pareto_state = if preserve_pareto_enumeration {
            self.pareto_state.take()
        } else {
            None
        };
        self.invalidate_last_check_result();
        if preserve_pareto_enumeration {
            self.pareto_state = pareto_state;
        }
        self.begin_unsat_query_epoch(&authored_assertions);
        // Install the pre-elaboration proof authority at the public-query
        // boundary. SMT-LIB command dispatch may replace it exactly once with
        // authenticated schematic instances; recursive retries and
        // optimization/probe solves then inherit those roots rather than
        // recapturing their generated working set as authored input.
        self.install_proof_source_provenance(&authored_assertions);
    }

    /// Bind public UNSAT/proof authority to the frontend's final query roots.
    ///
    /// `begin_public_solve` runs before command elaboration so even a malformed
    /// query revokes stale artifacts. SMT-LIB 2.7 schematic assertions are
    /// materialized during that elaboration, however, and must be included in
    /// the exact epoch before any solver lane runs. This is the sole permitted
    /// pre-solve rebind; the epoch method refuses it once assumptions are bound.
    pub(crate) fn bind_materialized_public_query(&mut self) {
        let assertions = self.ctx.assertions.clone();
        self.proof_problem_assertion_provenance = None;
        if self.rebind_unsat_query_epoch_assertions(&assertions) {
            self.install_proof_source_provenance(&assertions);
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
        // Process memory policy belongs to the host executable. In particular,
        // constructing this library type must not mutate ay-sys's process-global
        // ceiling: an AY dependency is compiled without cfg(test) inside another
        // crate's libtest, and a constructor-side default then couples thousands
        // of otherwise independent tests through the harness's retained RSS.
        // The standalone AY binaries and the direct-bindings host arm their
        // explicit defaults; compiler/server embedders must do likewise at their
        // process entry point.
        Self {
            ctx: Context::new(),
            // No string lemma lowered yet — vacuously all-valid.
            string_lemma_kinds_all_valid: true,
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
            prop_semantic_verify_memo: Default::default(),
            last_assumptions: None,
            last_assumption_core: None,
            last_core_term_to_name: None,
            named_assert_rewrites: Default::default(),
            last_proof: None,
            last_lrat_certificate: None,
            last_proof_term_overrides: None,
            proof_problem_assertion_provenance: None,
            quant_expansion_records: Vec::new(),
            ematching_proof_records: Vec::new(),
            last_proof_rebuild_originals: Vec::new(),
            last_proof_quality: None,
            last_unknown_reason: None,
            last_unknown_origin: None,
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
            proof_output_requested: false,
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
            finite_table_cert_grant_active: false,
            const_interp_cert_grant_active: false,
            mbqi_sat_cert_grant_active: false,
            mbqi_sat_cert_pins: HashMap::default(),
            finite_table_cert_pending_witness: None,
            const_interp_cert_witness: Vec::new(),
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
            last_bv_drat_self_cert: false,
            dt_array_injectivity_gate_bypass: false,
            last_degrade_was_datatype_array: false,
            dt_pre_lift_assertions: Vec::new(),
            dt_lazy_splits: None,
            defer_model_validation: false,
            bv_quantifier_full_domain_proof: false,
            defer_counterexample_minimization: false,
            last_model_validated: false,
            last_sat_certificate: None,
            last_unsat_certificate: None,
            unsat_query_epoch: None,
            next_unsat_query_epoch: 0,
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
            dt_egraph_building: Cell::new(false),
            array_def_index: std::cell::RefCell::new(None),
            select_by_array_index: std::cell::RefCell::new((0, Default::default())),
            required_terms_index: std::cell::RefCell::new(None),
            recorded_var_substitutions: HashMap::default(),
            original_problem_had_quantifiers: false,
            sat_validated_by_mod_div_or_branch: false,
            nested_array_row_reduction_unsat: false,
            ho_seq_unfold_array_free_unsat: false,
            in_nested_array_residue_probe: false,
            residue_probe_failures: 0,
            bypass_string_tautology_guard: false,
            slia_accepted_unknown: false,
            w7_defs: None,
            w7_int_defs: HashMap::default(),
            w4_work_deadline: Cell::new(None),
            self_check_authored_assertions: None,
            array_axiom_scope: None,
            row_seeded_terms: HashSet::default(),
            array_default_epsilon_by_sort: HashMap::default(),
            array_default_diag_by_sort: HashMap::default(),
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
            array_ext_shadow: ArrayExtShadow::default(),
            array_ext_witness_cache: ArrayExtWitnessCache::default(),
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

    /// Compatibility shim retained for callers that previously toggled model
    /// checking. Independent SAT validation is now a mandatory publication
    /// boundary and cannot be disabled.
    #[deprecated(note = "the independent model gate is mandatory and cannot be disabled")]
    pub fn set_independent_model_gate(&mut self, _enabled: bool) {}

    /// Whether the independent model-check gate is currently enabled.
    #[must_use]
    pub const fn independent_model_gate_enabled(&self) -> bool {
        true
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

    /// Whether the last `check_sat` produced a pure-QF_BV UNSAT under
    /// `--self-check` that emitted a native-checkable bit-blast DRAT to the
    /// self-cert temp files and whose finalized (CNF, DRAT) pair the executor
    /// verified with AY's native checker before returning `Unsat`. The CLI uses
    /// this only to print the certification diagnostic. Fail-closed: `false`
    /// unless both emission and verification succeeded for this solve.
    #[must_use]
    pub fn bv_drat_self_cert_pending(&self) -> bool {
        self.last_bv_drat_self_cert
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
        self.proof_output_requested = enabled;
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
        self.proof_output_requested
            || matches!(
                self.ctx.get_option("produce-proofs"),
                Some(OptionValue::Bool(true))
            )
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
        if self.is_producing_proofs() {
            self.last_proof.as_ref()
        } else {
            None
        }
    }

    /// Get access to the term store
    #[must_use]
    pub fn terms(&self) -> &TermStore {
        &self.ctx.terms
    }

    /// Describe why caller-authored roots cannot be registered safely.
    ///
    /// This immediate API gate covers both the current query's active
    /// extensionality witnesses and identities retired by earlier queries.
    pub(crate) fn array_ext_witness_registration_error(&self, roots: &[TermId]) -> Option<String> {
        match self
            .array_ext_witness_cache
            .registration_violation(&self.ctx.terms, roots)?
        {
            theories::ArrayExtWitnessRootViolation::InvalidTerm(term) => Some(format!(
                "caller-authored input contains out-of-range raw term id {}",
                term.0
            )),
            theories::ArrayExtWitnessRootViolation::CapturedWitness(term) => Some(format!(
                "caller-authored input captures solver-generated array-extensionality witness term {}",
                term.0
            )),
        }
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
        self.array_ext_witness_cache.clear();
        // ctx (and its append-only TermStore) is replaced wholesale: term ids
        // restart, so the prefix-extended select index MUST restart with them.
        *self.select_by_array_index.borrow_mut() = (0, Default::default());
        *self.array_def_index.borrow_mut() = None;
        *self.required_terms_index.borrow_mut() = None;
        self.last_result = None;
        self.last_model = None;
        self.last_sat_certificate = None;
        self.last_unsat_certificate = None;
        self.unsat_query_epoch = None;
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
        self.ematching_proof_records.clear();
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
        self.array_default_epsilon_by_sort.clear();
        self.array_default_diag_by_sort.clear();
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

#[cfg(test)]
mod result_rejection_tests {
    use super::*;
    use crate::incremental_state::IncrementalTheoryState;
    use ay_sat::Solver as SatSolver;

    #[test]
    fn rejecting_unsat_clears_certificates_and_canonicalizes_followup_queries() {
        let mut executor = Executor::new();
        executor
            .execute(&Command::SetOption(
                ":produce-proofs".to_string(),
                ay_frontend::SExpr::True,
            ))
            .expect("enable proof production");
        executor.last_result = Some(SolveResult::unsat());
        executor.last_proof = Some(Proof::new());
        executor.last_assumptions = Some(Vec::new());
        executor.last_assumption_core = Some(Vec::new());

        assert!(executor.reject_last_unsat_as_unknown());
        assert!(executor.last_result_is_unknown());
        assert_eq!(
            executor.get_reason_unknown(),
            Some(UnknownReason::Incomplete)
        );
        assert!(executor.last_proof().is_none());
        assert!(executor.last_assumptions.is_none());
        assert!(executor.last_assumption_core.is_none());

        let proof = executor
            .execute(&Command::GetProof)
            .expect("get-proof remains a recoverable query")
            .expect("get-proof has an error response");
        assert_eq!(
            proof,
            "(error \"proof is not available, last result was unknown\")"
        );
        let reason = executor
            .execute(&Command::GetInfo(":reason-unknown".to_string()))
            .expect("get-info remains available")
            .expect("get-info has a response");
        assert_eq!(reason, "(:reason-unknown incomplete)");

        // A later decision replaces the rejected result normally; rejection is
        // scoped to exactly the failed certification, not the whole session.
        assert_eq!(
            executor
                .execute(&Command::CheckSat)
                .expect("next check-sat"),
            Some("sat".to_string())
        );
        assert!(executor.last_result_is_sat());
    }

    #[test]
    fn rejecting_unsat_is_a_narrow_noop_for_other_states() {
        let mut executor = Executor::new();
        assert!(!executor.reject_last_unsat_as_unknown());
        executor.last_result = Some(SolveResult::Sat);
        assert!(!executor.reject_last_unsat_as_unknown());
        assert!(executor.last_result_is_sat());
    }

    #[test]
    fn externally_synthesized_unknown_revokes_every_prior_result() {
        let mut executor = Executor::new();
        executor
            .execute(&Command::SetOption(
                ":produce-proofs".to_string(),
                ay_frontend::SExpr::True,
            ))
            .expect("enable proof production");
        executor.last_result = Some(SolveResult::Sat);
        executor.replace_last_result_with_unknown(UnknownReason::InternalError);
        assert!(executor.last_result_is_unknown());
        assert_eq!(
            executor.get_reason_unknown(),
            Some(UnknownReason::InternalError)
        );
        let model = executor
            .execute(&Command::GetModel)
            .expect("get-model remains recoverable")
            .expect("get-model has an error response");
        assert_eq!(model, "(error \"model is not available\")");

        executor.last_result = Some(SolveResult::unsat());
        executor.last_proof = Some(Proof::new());
        executor.replace_last_result_with_unknown(UnknownReason::Incomplete);
        assert!(executor.last_proof().is_none());
        let proof = executor
            .execute(&Command::GetProof)
            .expect("get-proof remains recoverable")
            .expect("get-proof has an error response");
        assert_eq!(
            proof,
            "(error \"proof is not available, last result was unknown\")"
        );

        assert_eq!(
            executor
                .execute(&Command::CheckSat)
                .expect("later decision remains usable"),
            Some("sat".to_string())
        );
    }

    #[test]
    fn every_registered_unknown_reason_uses_the_shared_artifact_revocation_policy() {
        for reason in UnknownReason::ALL {
            let mut executor = Executor::new();
            executor.last_result = Some(SolveResult::Sat);
            executor.last_model = Some(Model::empty());
            executor.last_model_validated = true;
            executor.last_assumptions = Some(Vec::new());
            executor.last_assumption_core = Some(Vec::new());
            executor.last_core_term_to_name = Some(HashMap::default());
            executor.last_proof = Some(Proof::new());
            executor.last_lrat_certificate = Some(vec![1]);
            executor.last_proof_term_overrides = Some(HashMap::default());
            executor.last_clause_trace = Some(ClauseTrace::new());
            executor.last_var_to_term = Some(HashMap::default());
            executor.last_trail_provenance = Some(HashMap::default());
            executor.last_clausification_proofs = Some(Vec::new());
            executor.last_original_clause_theory_proofs = Some(Vec::new());
            executor.last_soft_cost = Some(1);
            executor.last_soft_cost_optimal = false;
            executor.last_soft_violations = Some(vec![0]);

            executor.replace_last_result_with_unknown(reason);

            assert!(
                executor.last_result_is_unknown(),
                "reason={}",
                reason.code()
            );
            assert_eq!(executor.get_reason_unknown(), Some(reason));
            assert!(executor.last_model.is_none(), "reason={}", reason.code());
            assert!(!executor.last_model_validated, "reason={}", reason.code());
            assert!(
                executor.last_assumptions.is_none(),
                "reason={}",
                reason.code()
            );
            assert!(
                executor.last_assumption_core.is_none(),
                "reason={}",
                reason.code()
            );
            assert!(
                executor.last_core_term_to_name.is_none(),
                "reason={}",
                reason.code()
            );
            assert!(executor.last_proof.is_none(), "reason={}", reason.code());
            assert!(
                executor.last_lrat_certificate.is_none(),
                "reason={}",
                reason.code()
            );
            assert!(
                executor.last_proof_term_overrides.is_none(),
                "reason={}",
                reason.code()
            );
            assert!(
                executor.last_clause_trace.is_none(),
                "reason={}",
                reason.code()
            );
            assert!(
                executor.last_var_to_term.is_none(),
                "reason={}",
                reason.code()
            );
            assert!(
                executor.last_trail_provenance.is_none(),
                "reason={}",
                reason.code()
            );
            assert!(
                executor.last_clausification_proofs.is_none(),
                "reason={}",
                reason.code()
            );
            assert!(
                executor.last_original_clause_theory_proofs.is_none(),
                "reason={}",
                reason.code()
            );
            assert!(
                executor.last_soft_cost.is_none(),
                "reason={}",
                reason.code()
            );
            assert!(executor.last_soft_cost_optimal, "reason={}", reason.code());
            assert!(
                executor.last_soft_violations.is_none(),
                "reason={}",
                reason.code()
            );
        }
    }

    #[test]
    fn public_unknown_boundary_revokes_artifacts_from_direct_internal_classification() {
        let mut executor = Executor::new();
        executor.last_result = Some(SolveResult::Sat);
        executor.last_model = Some(Model::empty());
        executor.last_unknown_reason = Some(UnknownReason::QuantifierDeferred);

        let published = executor.finalize_unknown_publication(SolveResult::Unknown);

        assert_eq!(published, SolveResult::Unknown);
        assert_eq!(
            executor.unknown_origin(),
            Some(UnknownOrigin::DeferredInstantiation)
        );
        assert!(executor.last_model.is_none());

        // External-stop attribution runs after the first public publication.
        // Reclassification must update the public pair atomically rather than
        // leave the original origin attached to a new reason.
        executor.record_unknown_from_origin(UnknownOrigin::SolveDeadline);
        assert_eq!(executor.unknown_reason(), Some(UnknownReason::Timeout));
        assert_eq!(
            executor.unknown_origin(),
            Some(UnknownOrigin::SolveDeadline)
        );
    }

    #[test]
    fn synthesized_unknown_detaches_persistent_trace_writer() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let trace = temp.path().join("decision.trace");
        let trace_text = trace.to_str().expect("UTF-8 trace path");

        let mut sat = SatSolver::new(0);
        sat.enable_decision_trace(trace_text)
            .expect("enable decision trace");
        let mut state = IncrementalTheoryState::new();
        state.persistent_sat = Some(sat);

        let mut executor = Executor::new();
        executor.incr_theory_state = Some(state);
        executor.last_result = Some(SolveResult::unsat());
        executor.replace_last_result_with_unknown(UnknownReason::Incomplete);

        let retained = executor
            .incr_theory_state
            .as_mut()
            .and_then(|state| state.persistent_sat.as_mut())
            .expect("persistent SAT state remains reusable");
        assert!(
            !retained.disable_decision_trace(),
            "the stale buffered writer must already be detached"
        );
        assert!(retained.solve().into_inner().is_sat());
    }

    #[test]
    fn signature_mutation_retires_a_direct_executor_result() {
        let mut executor = Executor::new();
        assert_eq!(
            executor.execute(&Command::CheckSat).expect("initial check"),
            Some("sat".to_string())
        );
        assert!(executor.last_result_is_sat());

        executor
            .execute(&Command::DeclareConst(
                "after_check".to_string(),
                ay_frontend::Sort::Simple("Int".to_string()),
            ))
            .expect("declaration after check");
        assert!(executor.last_result.is_none());

        let model = executor
            .execute(&Command::GetModel)
            .expect("get-model stays recoverable")
            .expect("get-model emits an error");
        assert_eq!(model, "(error \"model is not available\")");
    }

    #[test]
    fn every_parsed_problem_mutation_is_classified_for_invalidation() {
        let commands = ay_frontend::parse(
            r#"
            (set-logic ALL)
            (declare-sort S 0)
            (declare-const x Int)
            (declare-fun f (Int) Int)
            (define-fun g ((x Int)) Int x)
            (declare-var v Int)
            (declare-rel p (Int))
            (rule (p v))
            (query (p 0))
            (synth-fun sf ((x Int)) Int)
            (constraint (= (sf 0) 0))
            (push 1)
            (pop 1)
            (reset-assertions)
            "#,
        )
        .expect("representative mutation commands parse");
        assert!(
            commands
                .iter()
                .all(Executor::command_invalidates_last_check_result),
            "every semantics/signature mutation must revoke stale results: {commands:?}"
        );

        let queries = ay_frontend::parse(
            "(set-option :print-success true)\n(get-info :name)\n(echo \"ok\")\n",
        )
        .expect("non-mutating commands parse");
        assert!(queries
            .iter()
            .all(|cmd| !Executor::command_invalidates_last_check_result(cmd)));
    }
}
