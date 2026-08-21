// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager-persistent arm of the incremental split-loop pipeline.
//!
//! Extracted from `pipeline_incremental_split_macros.rs` (#6680).
//! Contains the persistent-theory lifecycle: theory is created once before
//! the loop and warm-reset each iteration instead of recreated.
//! Preserves simplex basis and variable values across iterations,
//! matching Z3's persistent lar_solver architecture.

/// Eager-persistent arm implementation for `solve_incremental_split_loop_pipeline!`.
///
/// Key differences from @eager:
/// 1. Theory created once before the loop, soft_reset_warm() each iteration
/// 2. set_terms()/unset_terms() bracket each iteration's term access
/// 3. No structural snapshot needed (theory persists)
/// 4. Theory is NOT dropped before split atom creation — only unset_terms()
macro_rules! pipeline_incremental_split_eager_persistent_arm {
    ($self:ident,
        tag: $tag:expr,
        persistent_sat_field: $sat_field:ident,
        tseitin_field: $tseitin_field:ident,
        encoded_field: $encoded_field:ident,
        activation_scope_field: $activation_scope_field:ident,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        max_splits: $max_splits:expr,
        pre_theory_import: |$import_theory:ident, $import_lc:ident, $import_hc:ident, $import_ds:ident| $import_expr:expr,
        post_theory_export: |$export_theory:ident| $export_expr:expr
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
    ) => {{
#[cfg(not(kani))]
        // #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
#[cfg(kani)]
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
        use ay_core::{TermId, Tseitin, TseitinEncodedAssertion};
        use ay_sat::{Literal as SatLiteral, SatResult, Variable as SatVariable};
        use $crate::executor_types::{SolveResult, UnknownReason};
        use $crate::incremental_state::{collect_active_theory_atoms_cached, IncrementalTheoryState};
        use $crate::executor::theories::freeze_var_if_needed;

        let proof_enabled = $self.produce_proofs_enabled();
        let _islp_problem_assertions = if proof_enabled {
            $self.proof_problem_assertions()
        } else {
            Vec::new()
        };
        let random_seed = $self.current_random_seed();
        let should_record_random_seed = match $self.incr_theory_state.as_ref() {
            Some(state) => state.$sat_field.is_none(),
            None => true,
        };
        if should_record_random_seed {
            $self.record_applied_sat_random_seed_for_test(random_seed);
        }

        // #8064: Capture should_stop closure BEFORE taking mutable borrows on
        // self.incr_theory_state. make_should_stop() only borrows &self and
        // returns an owned closure that captures Arc-cloned interrupt flag +
        // copied deadline, freeing self for mutable use below.
        let _islp_base_should_stop = $self.make_should_stop();

        // #8256: Per-iteration wall-clock budget for the persistent split-loop.
        // The SAT solver polls should_stop every 100 conflicts and every 1000
        // decisions. We use a wall-clock timer to limit each iteration's runtime,
        // preventing the SAT solver from getting stuck indefinitely on iteration 0
        // for complex QF_LRA formulas (e.g., simple_startup, labyrinth).
        //
        // Wall-clock approach is necessary because theory-heavy formulas have
        // very low conflict rates (expensive simplex calls dominate), making
        // conflict-based budgets ineffective.
        //
        // Grace period: iteration 0 gets a 5s grace period before the budget
        // kicks in. This allows benchmarks that AY can solve within 5s (like
        // sc-8.induction2/3) to finish without interruption. After the grace
        // period, iterations get 500ms + 200ms * iter, capped at 30s.
        let _islp_iter_deadline = std::cell::Cell::new(ay_core::time::Instant::now());
        let _islp_budget_exhausted = std::cell::Cell::new(false);
        let _islp_should_stop = || {
            if _islp_base_should_stop() {
                return true;
            }
            if ay_core::time::Instant::now() >= _islp_iter_deadline.get() {
                _islp_budget_exhausted.set(true);
                return true;
            }
            false
        };

        // #8256: Track whether the previous iteration was budget-exhausted.
        // When true, the next SAT solve uses continue_solving_with_extension()
        // or resume_solving_with_extension() to preserve state. Reset to false
        // when splits or refinements are added (which change the clause set).
        let mut _islp_use_continue_solving = false;
        // #8256: Track whether to use the zero-overhead resume path.
        // resume_solving re-enters the CDCL loop without trail reset, learned
        // clause flush, or VSIDS rebuild — O(1) per budget-exhausted iteration
        // vs O(trail + learned) for continue_solving. Used for the first
        // budget-exhausted continuation; falls back to continue_solving when
        // stall detection triggers (preserving the sc-8 non-convergence fix).
        let mut _islp_use_resume_solving = false;

        // #8373: Cap on model-validation blocking clauses to prevent
        // infinite retry loops on benchmarks where every Boolean assignment
        // fails validation. After this many retries, accept Unknown.
        // With targeted decision-only blocking clauses (<=64 lits), more
        // retries are feasible and useful for convergence to UNSAT.
        const _ISLP_MAX_BLOCKING_RETRIES: u32 = 200;
        let mut _islp_blocking_retry_count: u32 = 0;

        // #8399: Stall detection for continue_solving recovery.
        // When continue_solving_with_extension makes no progress (measured by
        // SAT conflict count delta) for MAX_CONTINUE_STALLS consecutive
        // budget-exhausted iterations, fall back to continue_solving (with
        // trail reset) to break out of stuck search regions. This prevents
        // the sc-8 non-convergence pattern where stale learned clauses lock
        // the solver into revisiting the same search region.
        //
        // #8399 escalation: after MAX_CONTINUE_FALLBACKS consecutive times
        // that continue_solving itself stalls and resets, escalate to full
        // solve (neither continue nor resume) to completely rebuild search
        // state. This handles the case where flushing non-core learned
        // clauses + resetting restart counters is insufficient.
        const _ISLP_MAX_CONTINUE_STALLS: u32 = 3;
        const _ISLP_MIN_CONFLICT_PROGRESS: u64 = 50;
        const _ISLP_MAX_CONTINUE_FALLBACKS: u32 = 2;
        let mut _islp_continue_stall_count: u32 = 0;
        let mut _islp_continue_fallback_count: u32 = 0;

        // Initialize or get incremental state.
        //
        // #8373: We take() the state out of $self rather than borrowing it
        // in-place. This decouples `state` and `solver` (which borrows
        // state.$sat_field) from `$self`, allowing $self method calls
        // (e.g., solve_and_store_model_with_theories) during the split loop
        // without borrow conflicts. The state is put back into $self after
        // the split loop exits.
        let mut _islp_owned_state = $self
            .incr_theory_state
            .take()
            .unwrap_or_else(IncrementalTheoryState::new);
        let state = &mut _islp_owned_state;
        collect_theory_stats!(incremental: $self, state);

        pipeline_incremental_setup!(
            $self, state, proof_enabled, random_seed, $tag,
            sat_field: $sat_field,
            tseitin_field: $tseitin_field,
            encoded_field: $encoded_field,
            activation_scope_field: $activation_scope_field,
            solver_init: {
                if let Some(ref mut sat) = state.$sat_field {
                    for _ in 0..state.scope_depth {
                        sat.push();
                    }
                }
            },
            out: (new_assertion_set, solver, tseitin, base_var_to_term, base_term_to_var, pending_activations)
        );
        state.$sat_field = Some(solver);

        // Save Tseitin state back
        state.$tseitin_field = tseitin.into_state();

        // Collect theory atoms in active assertions only. The global
        // Bool-UF-arg scan reuses the persistent high-water-mark cache (#N).
        let base_active_atoms = collect_active_theory_atoms_cached(
            &$self.ctx.terms,
            &$self.ctx.assertions,
            Some(&mut state.bool_uf_arg_cache),
        );
        let solver = state
            .$sat_field
            .as_mut()
            .expect(concat!("incremental ", $tag, " should initialize persistent SAT solver"));
        for &term in &base_active_atoms {
            if let Some(&var) = base_term_to_var.get(&term) {
                freeze_var_if_needed(solver, SatVariable::new(var));
            }
        }
        // ITE-condition guard variables are decided by `suggest_decision`
        // (#8003) and gate branch-atom deferral (#8125); they are frequently
        // plain Tseitin variables, so they need their own freeze pass or
        // BVE/SCC inprocessing can remove them (decide-removed-variable panic).
        $crate::executor::theories::freeze_ite_condition_vars(
            solver,
            &$self.ctx.terms,
            &base_term_to_var,
        );
        // #6853: Apply deferred activations immediately (no private push in eager-persistent arm).
        pipeline_apply_pending_activations_immediate!(
            solver, pending_activations, proof_enabled, state
        );

        // #lra-inc-engine: the incremental QF_LRA engine lane runs this arm on
        // the SESSION-persistent state whose scope_depth mirrors the SMT push/pop
        // stack (SAT scope selectors keep the clause DB aligned), so nonzero depth
        // IS supported when lra_persist_sat_active is set. Every other caller must
        // still be at isolated scope depth 0.
        let _islp_scope_depth_unsupported =
            state.scope_depth != 0 && !$self.lra_persist_sat_active;
        // #lra-inc-engine INV-3: while scope selectors are active, the
        // budget-exhausted continue/resume fast paths are forbidden — they
        // re-enter the CDCL loop directly WITHOUT re-composing the scope-selector
        // assumptions, so a pushed activation clause `(root OR +selector)` could
        // be satisfied through the unassumed selector and the pushed assertion
        // silently dropped. Force full scope-composed solves instead.
        let _islp_persist_scoped =
            $self.lra_persist_sat_active && solver.scope_depth() > 0;
        // Reuse scratch allocation from previous check-sat call (#8573).
        state.scratch_var_to_term.clone_from(&base_var_to_term);
        let mut local_var_to_term: HashMap<u32, TermId> =
            std::mem::take(&mut state.scratch_var_to_term);

        // Local variable maps grow as splits are added
        let mut local_term_to_var: HashMap<TermId, u32> = base_term_to_var;
        let mut local_next_var: u32 = u32::try_from(solver.user_num_vars() + solver.scope_depth())
            .expect("SAT solver variable count does not fit in u32");
        let base_active_atom_set: HashSet<TermId> = base_active_atoms.iter().copied().collect();
        let mut _islp_added_split_clauses: HashSet<
            $crate::executor::theories::split_incremental::SplitClauseKey,
        > = HashSet::default();
        let mut _islp_added_refinement_clauses: HashSet<
            $crate::executor::theories::split_incremental::BoundRefinementReplayKey,
        > = HashSet::default();
        let mut _islp_added_axioms: HashSet<$crate::extension::TheoryAxiomKey> = HashSet::default();

        // Learned state persisted across theory instances
        let mut _islp_learned_cuts: Vec<ay_lia::StoredCut> = Vec::new();
        let mut _islp_seen_hnf_cuts: HashSet<ay_lia::HnfCutKey> = HashSet::default();
        let mut _islp_dioph_state = ay_lia::DiophState::default();

        // Split value trends for unbounded oscillation detection
        let mut _islp_last_split_values: $crate::executor::theories::solve_harness::SplitOscillationMap = HashMap::default();
        // #6851: Centralized model-equality tracker. The persistent arm uses
        // should_add_triangle() to avoid re-adding identical triangle clauses
        // across repeated requests for the same equality atom.
        let mut _islp_model_eq_tracker = $crate::executor::theories::split_incremental::ModelEqualityTracker::new(
            $crate::executor::theories::split_incremental::model_equality::MODEL_EQ_MAX_ROUNDS_EAGER_PERSISTENT,
        );

        // Per-theory statistics saved from the most recent theory instance (#6579).
        let mut _islp_last_theory_stats: Vec<(&'static str, u64)> = Vec::new();

        // Split-loop timing (#6503).
        let mut _islp_timing = $crate::SplitLoopTimingStats::default();
        let _islp_total_start = ay_core::time::Instant::now();
        let mut _islp_eager_stats = $crate::DpllEagerStats::default();

        // #8256: Cached extension data to avoid O(|terms|) ITE scan and
        // O(|vars|) bitset construction on every split-loop iteration.
        // Populated on iteration 0 by the full TheoryExtension::new() path,
        // then reused via TheoryExtension::new_with_cached_data() on
        // subsequent iterations. Incrementally extended when new split
        // variables are added.
        let mut _islp_cached_ext_data = $crate::extension::CachedExtensionData {
            theory_var_bitset: Vec::new(),
            ite_branch_guards: Vec::new(),
            ite_guarded_bitset: Vec::new(),
            ite_condition_bitset: Vec::new(),
            ite_condition_var_to_term: HashMap::default(),
            last_full_rebuild_num_vars: 0,
            prev_registered_atom_count: 0,
            disable_theory_check: crate::theory_debug_flags::disable_theory_check(),
        };

        // #8256: Cache active_theory_atoms and active_theory_atom_set across
        // iterations. Only rebuild when new variables are added (split encoding).
        let mut _islp_cached_active_atoms: Vec<TermId> = Vec::new();
        let mut _islp_cached_active_atom_set: HashSet<TermId> = HashSet::default();
        let mut _islp_cached_var_count: usize = 0;

        // #6590 Packet 3: Create persistent theory ONCE before the loop.
        // The theory's terms_ptr is null initially; set_terms() is called
        // at the start of each iteration.
        //
        // #lra-inc-engine S3 (warm theory across check-sats): when the warm lane
        // is on (inc-engine lane, `--dpll-no-lra-inc-warm` opts out), REUSE a theory solver
        // persisted across check-sats instead of rebuilding from scratch — the
        // accumulated base bounds + implied_bounds cache carry over, so
        // re-asserting an already-set bound is a non-tightening no-op and
        // compute_implied_bounds' #inc-cib-nodelta guard makes the dominant
        // deep-check cost O(delta). soft_reset_warm is already skipped at
        // iteration 0 (`_iteration > 0` guard below), so the reused theory's
        // state is preserved on entry; set_terms refreshes its dangling terms
        // pointer. A None / type-mismatch falls back to a fresh solver.
        // SOUNDNESS: warm theory is default ON (opt out with
        // --dpll-no-lra-inc-warm). Scoped pops and monotone selector units preserve
        // the live constraint set, while a scope/type mismatch discards the
        // cached solver. --lra-inc-engine-reverify remains an opt-in
        // from-scratch disagreement backstop.
        let _islp_inc_warm = $crate::warm_theory_flag::get();
        let (mut theory, _islp_theory_reused) = if _islp_inc_warm {
            match state.persist_theory.take() {
                Some(_islp_boxed) => match _islp_boxed.downcast() {
                    Ok(_islp_t) => (*_islp_t, true),
                    Err(_) => ($create_theory, false),
                },
                None => ($create_theory, false),
            }
        } else {
            ($create_theory, false)
        };
        if _islp_theory_reused {
            theory.set_terms(&$self.ctx.terms);
        }
        // #lra-inc-engine S3 (warm theory): tell the theory whether it is a
        // reused warm solver, so it can cap the implied-bounds cascade that a
        // stale warm cache would otherwise blow up on a region shift (making warm
        // slower than from-scratch). No-op for non-LRA theories.
        <_ as ay_core::TheorySolver>::set_warm_reuse_hint(&mut theory, _islp_theory_reused);

        // Proof ledger clone + context registration (#5814 Packet A)
        // Reordered: proof labels -> negation cache (parity with lazy/assume arms).
        let (mut _islp_local_clausification_proofs, mut _islp_local_original_clause_theory_proofs) =
            pipeline_clone_local_proof_ledgers!(state, proof_enabled);
        pipeline_register_proof_context!(
            $self,
            proof_enabled,
            $tag,
            problem_assertions: _islp_problem_assertions
        );
        // Negation cache seeding (#6660, #6735): build negation map once and
        // sync only newly encoded terms before proof consumers run.
        let mut _islp_negations = $crate::incremental_proof_cache::IncrementalNegationCache::seed(
            &mut $self.ctx.terms,
            local_var_to_term.values().copied(),
            proof_enabled,
        );

        // #8008: Bound axiom injection for the eager-persistent arm.
        // Generates transitivity binary clauses (e.g., x >= 5 => x >= 3)
        // from bound atom pairs on the same variable. Z3 generates 6,885
        // such clauses on simple_startup_6nodes, producing 18,712 binary
        // propagations (80% of total). Without these, the SAT solver
        // must discover every implication through the theory solver.
        // Previously only present in lazy/assume arms (#6579).
        pipeline_inject_bound_axioms!(
            $self, solver, base_active_atoms, local_term_to_var,
            $create_theory, proof_enabled, $tag,
            _islp_local_clausification_proofs, _islp_local_original_clause_theory_proofs,
            state
        );

        // #8256: Track that bound axioms were pre-injected by
        // pipeline_inject_bound_axioms!() above. This tells iteration 0's
        // TheoryExtension construction to skip the expensive per-axiom
        // LraSolver validation (33K fresh solver instances on labyrinth
        // benchmarks). The axioms are already in the SAT solver; the
        // extension only needs to build bitsets and register atoms.
        let _islp_bound_axioms_pre_injected = true;

        let _islp_result: $crate::executor_types::Result<SolveResult> = 'split_loop: {
            if _islp_scope_depth_unsupported {
                tracing::warn!(
                    scope_depth = state.scope_depth,
                    concat!(
                        "Incremental eager persistent ",
                        $tag,
                        " split-loop requires isolated scope depth 0; returning Unknown"
                    )
                );
                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                $self.last_result = Some(SolveResult::Unknown);
                break 'split_loop Ok(SolveResult::Unknown);
            }

            for _iteration in 0..$max_splits {
                // Pre-iteration check (interrupt/deadline)
                $(
                    {
                        let $pic_self = &();
                        if $pic_expr {
                            // #lra-inc-engine: in persist mode this arm opens no
                            // private SAT scope, so at isolated depth 0 this pop
                            // was a harmless no-op; under real SMT scopes it would
                            // pop a live scope selector and misalign the selector
                            // stack — skip it there.
                            if !$self.lra_persist_sat_active {
                                let _ = solver.pop();
                            }
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                    }
                )?

                state.round_trips += 1;
                _islp_timing.dpll.round_trips += 1;

                // #8256: Consume the continue/resume flags BEFORE setting the
                // budget, since the budget depends on the mode. Flags were set
                // by the previous iteration if budget was exhausted. Reset AFTER
                // consuming so that iterations with splits/refinements use full solve.
                // #lra-inc-engine INV-3: under active scope selectors the
                // continue/resume entrypoints are assumptionless — force full
                // scope-composed solves (see _islp_persist_scoped above).
                let _islp_use_continue_this_iter =
                    _islp_use_continue_solving && !_islp_persist_scoped;
                let _islp_use_resume_this_iter =
                    _islp_use_resume_solving && !_islp_persist_scoped;
                _islp_use_continue_solving = false;
                _islp_use_resume_solving = false;

                // #8256: Set per-iteration wall-clock deadline.
                //
                // The budget system exists to let the split loop add
                // splits/refinements when the SAT solver returns Unknown.
                // However, for pure QF_LRA benchmarks without ITEs or
                // disequalities, there are NO splits to add — the solver
                // must converge in a single continuous run.
                //
                // Budget strategy:
                //   Iteration 0: long budget (120s or global timeout).
                //     This allows the solver to converge without interruption
                //     on pure QF_LRA benchmarks. Z3 solves simple_startup_10nodes
                //     in 1.3s and labyrinth-18 in 11.3s. AY needs ~10-20x more
                //     decisions due to lower propagation quality, so 120s covers
                //     the gap with margin. The global timeout (if set) still
                //     applies via should_stop.
                //   Resume iterations (budget-exhausted, no splits): 30s.
                //     After iter 0's budget expires, subsequent budget-exhausted
                //     continuations use resume_solving (O(1) overhead) and get
                //     a generous 30s budget. The split loop overhead per resume
                //     iteration is near-zero.
                //   Split/refinement iterations: 500ms + 200ms * iter, capped at 30s.
                //     After new clauses are added, the solver needs to re-explore
                //     with the new constraints. Shorter budgets are appropriate.
                _islp_budget_exhausted.set(false);
                let _iter_budget_ms = if _iteration == 0 {
                    // Long budget for initial solve. The global timeout
                    // (via should_stop) still provides the hard cap.
                    120_000u64
                } else if _islp_use_resume_this_iter {
                    // Resume after budget exhaustion with no new clauses:
                    // give the solver a long continuation window.
                    30_000u64
                } else if _islp_use_continue_this_iter {
                    // Continue with trail reset (stall fallback):
                    // moderate budget for the fresh search.
                    15_000u64
                } else {
                    // After splits/refinements: incremental budget.
                    std::cmp::min(500u64 + (_iteration as u64) * 200, 30_000u64)
                };
                _islp_iter_deadline.set(
                    ay_core::time::Instant::now() + std::time::Duration::from_millis(_iter_budget_ms)
                );

                // #6590: Set terms pointer for this iteration.
                theory.set_terms(&$self.ctx.terms);
                // #8256: Skip soft_reset_warm() when continuing after a
                // budget-exhausted iteration. The theory solver already has
                // all assertions from the previous iteration, and the SAT
                // solver is resuming from its interrupted state. Warm-resetting
                // would force the entire trail to be replayed through the theory,
                // imposing O(trail * per-atom-cost) overhead per continuation.
                // On simple_startup_10nodes, this reduces per-iteration overhead
                // from ~50ms (warm-reset + trail replay) to <1ms (no-op).
                if _iteration > 0 && !_islp_use_continue_this_iter {
                    theory.soft_reset_warm();
                }

                if _iteration < 5 || _iteration % 1000 == 0 {
                    tracing::debug!(
                        iter = _iteration,
                        vars = local_var_to_term.len(),
                        splits = _islp_added_split_clauses.len(),
                        continue_solving = _islp_use_continue_this_iter,
                        budget_ms = _iter_budget_ms,
                        stall_count = _islp_continue_stall_count,
                        "#8256/#8399 persistent loop state"
                    );
                }

                // #8256: Only rebuild active_theory_atoms when var count changed
                // (new split atoms added). On large formulas this saves O(n*log(n))
                // sort + O(n) filter per iteration.
                let _islp_current_var_count = local_var_to_term.len();
                if _islp_current_var_count != _islp_cached_var_count {
                    _islp_cached_active_atoms =
                        $crate::iter_var_to_term_sorted(&local_var_to_term)
                            .map(|(_, term)| term)
                            .filter(|term| {
                                base_active_atom_set.contains(term)
                                    || $crate::is_theory_atom(&$self.ctx.terms, *term)
                            })
                            .collect();
                    _islp_cached_active_atom_set =
                        _islp_cached_active_atoms.iter().copied().collect();
                    _islp_cached_var_count = _islp_current_var_count;
                }
                let active_theory_atoms = &_islp_cached_active_atoms;
                let active_theory_atom_set = &_islp_cached_active_atom_set;

                // Import learned state (no-op for LRA, used by LIA).
                {
                    let $import_theory = &mut theory;
                    let $import_lc = &mut _islp_learned_cuts;
                    let $import_hc = &mut _islp_seen_hnf_cuts;
                    let $import_ds = &mut _islp_dioph_state;
                    $import_expr;
                }
                theory.replay_learned_cuts();
                // #qf-auflia-fc-diseq-sync: see the eager arm — assert
                // preprocessor-eliminated top-level arithmetic disequality
                // facts each iteration (idempotent for the warm-reset theory).
                let _islp_synced_diseq_facts =
                    $crate::pipeline_fns::assert_top_level_arith_diseq_facts(
                        &$self.ctx.terms,
                        &$self.ctx.assertions,
                        &mut theory,
                    );

                // Sync only the fresh atoms introduced by prior iterations (#6735).
                _islp_negations.sync_pending(&mut $self.ctx.terms);

                // #8399: Record conflict count before SAT solve for stall detection.
                let _islp_pre_solve_conflicts = solver.num_conflicts();

                let (sat_result, _ext_conflicts, _ext_propagations,
                     _ext_partial, pending_split, pending_refinements) =
                    pipeline_build_eager_extension!(
                        $self, solver, theory,
                        local_var_to_term, local_term_to_var,
                        *active_theory_atoms, *active_theory_atom_set,
                        proof_enabled, _islp_negations,
                        _islp_added_refinement_clauses, _islp_added_axioms,
                        _islp_eager_stats, _islp_timing, state,
                        should_stop: _islp_should_stop,
                        cached_ext_data: _islp_cached_ext_data,
                        use_continue_solving: _islp_use_continue_this_iter,
                        use_resume_solving: _islp_use_resume_this_iter,
                        bound_axioms_pre_injected: _islp_bound_axioms_pre_injected
                    );

                // #8727: Reset the model-equality round counter whenever the
                // SAT solver learned at least one theory-conflict clause in
                // this iteration. The budget exists to prevent infinite
                // model-equality loops on pure no-progress cycling, not to
                // cap genuine theory conflicts (e.g., iterative Dioph UNSAT
                // on modular-cascade benchmarks). Each learned conflict is
                // real progress and refreshes the budget.
                _islp_model_eq_tracker.note_theory_progress(_ext_conflicts);

                // Save per-theory statistics (#6579).
                _islp_last_theory_stats = ay_core::TheorySolver::collect_statistics(&theory);

                let pending_split = match pending_split {
                    Some(ay_core::TheoryResult::NeedModelEquality(eq)) => {
                        theory.unset_terms();
                        // #6851: Centralized round budget via ModelEqualityTracker.
                        if _islp_model_eq_tracker.increment_round() {
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                        pipeline_encode_model_equality!(
                            $self, solver, local_term_to_var, local_var_to_term,
                            local_next_var, _islp_negations, eq,
                            added_model_eqs: _islp_model_eq_tracker.triangle_atoms_mut()
                        );
                        continue;
                    }
                    Some(ay_core::TheoryResult::NeedModelEqualities(eqs)) => {
                        theory.unset_terms();
                        // #6851: Centralized round budget via ModelEqualityTracker.
                        if _islp_model_eq_tracker.increment_round() {
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                        for eq in eqs {
                            pipeline_encode_model_equality!(
                                $self, solver, local_term_to_var, local_var_to_term,
                                local_next_var, _islp_negations, eq,
                                added_model_eqs: _islp_model_eq_tracker.triangle_atoms_mut()
                            );
                        }
                        continue;
                    }
                    Some(ay_core::TheoryResult::NeedLemmas(lemmas)) => {
                        theory.unset_terms();
                        let mut _islp_lemma_original_ids = Vec::with_capacity(lemmas.len());
                        for lemma in &lemmas {
                            _islp_lemma_original_ids.push($crate::executor::theories::split_incremental::apply_theory_lemma_incremental(
                                &$self.ctx.terms,
                                solver,
                                &mut local_term_to_var,
                                &mut local_var_to_term,
                                &mut local_next_var,
                                &mut _islp_negations,
                                &lemma.clause,
                            ));
                        }
                        if proof_enabled {
                            _islp_negations.sync_pending(&mut $self.ctx.terms);
                            // #trust->0 C3: DT registries, once per batch.
                            let _c3_dt = $crate::theory_inference::dt_funnel_registry_data(&$self.ctx);
                            for (lemma, _islp_original_id) in
                                lemmas.iter().zip(_islp_lemma_original_ids)
                            {
                                let terms: Vec<ay_core::TermId> = lemma
                                    .clause
                                    .iter()
                                    .map(|lit| {
                                        if lit.value {
                                            lit.term
                                        } else {
                                            *_islp_negations
                                                .as_map()
                                                .get(&lit.term)
                                                .expect("persistent eager theory-lemma negation cache should be synced")
                                        }
                                    })
                                    .collect();
                                // #trust->0 C3: funnel classifies + records;
                                // adopt its validator-ordered clause.
                                let (kind, terms) =
                                    $crate::theory_inference::record_funnel_classified_lemma(
                                        &mut $self.proof_tracker,
                                        &$self.ctx.terms,
                                        terms,
                                        _c3_dt.as_ref(),
                                    );
                                if let Some(_islp_original_id) = _islp_original_id {
                                    $crate::pipeline_fns::place_original_clause_authority_at_id(
                                        &solver,
                                        _islp_original_id,
                                        None,
                                        Some(ay_core::TheoryLemmaProof {
                                            clause: terms,
                                            kind,
                                            farkas: None,
                                            lia: None,
                                        }),
                                        &mut _islp_local_clausification_proofs,
                                        &mut _islp_local_original_clause_theory_proofs,
                                    );
                                }
                            }
                        }
                        continue;
                    }
                    other => other,
                };

                match sat_result {
                    SatResult::Sat(model) => {
                        if _iteration < 5 || _iteration % 1000 == 0 {
                            tracing::debug!(
                                iter = _iteration,
                                conflicts = _ext_conflicts,
                                propagations = _ext_propagations,
                                partial = _ext_partial,
                                split = pending_split.is_some(),
                                refine = !pending_refinements.is_empty(),
                                "#6590 persistent SAT result"
                            );
                        }
                        // Soundness guard: escalate SAT→Unknown when theory
                        // conflicts were dropped (parity with solve_eager_step).
                        if _ext_partial > 0 {
                            tracing::warn!(
                                partial_clauses = _ext_partial,
                                concat!("Eager persistent ", $tag, " produced SAT with dropped theory conflicts; escalating to Unknown")
                            );
                            theory.unset_terms();
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }

                        // Final full-check for combined/persistent theories (#5462).
                        // The eager extension only runs the lightweight
                        // BCP-time check; theories that opt into a final SAT
                        // fixpoint must be rechecked here before accepting SAT.
                        if ay_core::TheorySolver::needs_final_check_after_sat(&theory)
                            && pending_split.is_none()
                        {
                            let _fc_result = ay_core::TheorySolver::check(&mut theory);
                            match _fc_result {
                                ay_core::TheoryResult::Sat => {
                                    // Final check passed.
                                }
                                ay_core::TheoryResult::NeedSplit(_)
                                | ay_core::TheoryResult::NeedDisequalitySplit(_)
                                | ay_core::TheoryResult::NeedExpressionSplit(_)
                                | ay_core::TheoryResult::NeedExpressionSplits(_) => {
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    // #8762: drain batched disequality splits BEFORE
                                    // releasing the theory's term borrow.
                                    let _drained_diseq_extras =
                                        <_ as ay_core::TheorySolver>::drain_pending_diseq_splits(&mut theory);
                                    theory.unset_terms();

                                    pipeline_incremental_split_eager_dispatch_split!(
                                        'split_loop, $self, solver,
                                        tag: $tag, suffix: "-INC-EAGER-PERSIST-FC",
                                        local_term_to_var, local_var_to_term, local_next_var, _islp_negations,
                                        _islp_added_split_clauses, _islp_last_split_values,
                                        split_result: _fc_result,
                                        drained_diseq_extras: _drained_diseq_extras,
                                        fallthrough: {
                                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                            $self.last_result = Some(SolveResult::Unknown);
                                            break 'split_loop Ok(SolveResult::Unknown);
                                        }
                                    );
                                }
                                ay_core::TheoryResult::NeedModelEquality(eq) => {
                                    // #7966: Suppress stale model equalities whose
                                    // atoms are already encoded in the SAT solver,
                                    // matching the extension-level filter in check.rs.
                                    let _fc_eq_stale = $self.ctx.terms.find_eq(eq.lhs, eq.rhs)
                                        .is_some_and(|ea| local_term_to_var.contains_key(&ea));
                                    if _fc_eq_stale {
                                        tracing::debug!(
                                            lhs = ?eq.lhs, rhs = ?eq.rhs,
                                            "#7966 persistent final-check suppressed stale NeedModelEquality"
                                        );
                                        // Treat as Sat — the equality is already encoded.
                                    } else {
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        theory.unset_terms();
                                        // #6851: Centralized round budget via ModelEqualityTracker.
                                        if _islp_model_eq_tracker.increment_round() {
                                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                            $self.last_result = Some(SolveResult::Unknown);
                                            break 'split_loop Ok(SolveResult::Unknown);
                                        }
                                        pipeline_encode_model_equality!(
                                            $self, solver, local_term_to_var, local_var_to_term,
                                            local_next_var, _islp_negations, eq,
                                            added_model_eqs: _islp_model_eq_tracker.triangle_atoms_mut()
                                        );
                                        continue;
                                    }
                                }
                                ay_core::TheoryResult::NeedModelEqualities(eqs) => {
                                    // #7966: Filter out already-encoded model equalities
                                    // before consuming a round budget slot.
                                    let _fc_fresh_eqs: Vec<ay_core::ModelEqualityRequest> = eqs
                                        .into_iter()
                                        .filter(|eq| {
                                            !$self.ctx.terms.find_eq(eq.lhs, eq.rhs)
                                                .is_some_and(|ea| local_term_to_var.contains_key(&ea))
                                        })
                                        .collect();
                                    if _fc_fresh_eqs.is_empty() {
                                        tracing::debug!(
                                            "#7966 persistent final-check suppressed all stale NeedModelEqualities"
                                        );
                                        // Treat as Sat — all equalities already encoded.
                                    } else {
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        theory.unset_terms();
                                        // #6851: Centralized round budget via ModelEqualityTracker.
                                        if _islp_model_eq_tracker.increment_round() {
                                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                            $self.last_result = Some(SolveResult::Unknown);
                                            break 'split_loop Ok(SolveResult::Unknown);
                                        }
                                        for eq in _fc_fresh_eqs {
                                            pipeline_encode_model_equality!(
                                                $self, solver, local_term_to_var, local_var_to_term,
                                                local_next_var, _islp_negations, eq,
                                                added_model_eqs: _islp_model_eq_tracker.triangle_atoms_mut()
                                            );
                                        }
                                        continue;
                                    }
                                }
                                ay_core::TheoryResult::NeedLemmas(lemmas) => {
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    theory.unset_terms();
                                    let mut _fc_lemma_original_ids = Vec::with_capacity(lemmas.len());
                                    for lemma in &lemmas {
                                        _fc_lemma_original_ids.push($crate::executor::theories::split_incremental::apply_theory_lemma_incremental(
                                            &$self.ctx.terms,
                                            solver,
                                            &mut local_term_to_var,
                                            &mut local_var_to_term,
                                            &mut local_next_var,
                                            &mut _islp_negations,
                                            &lemma.clause,
                                        ));
                                    }
                                    if proof_enabled {
                                        _islp_negations.sync_pending(&mut $self.ctx.terms);
                                        // #trust->0 C3: DT registries, once per batch.
                                        let _c3_dt = $crate::theory_inference::dt_funnel_registry_data(&$self.ctx);
                                        for (lemma, _fc_original_id) in
                                            lemmas.iter().zip(_fc_lemma_original_ids)
                                        {
                                            let terms: Vec<ay_core::TermId> = lemma
                                                .clause
                                                .iter()
                                                .map(|lit| {
                                                    if lit.value {
                                                        lit.term
                                                    } else {
                                                        *_islp_negations
                                                            .as_map()
                                                            .get(&lit.term)
                                                            .expect("persistent final-check theory-lemma negation cache should be synced")
                                                    }
                                                })
                                                .collect();
                                            // #trust->0 C3: funnel classifies +
                                            // records; adopt its validator-ordered
                                            // clause.
                                            let (kind, terms) =
                                                $crate::theory_inference::record_funnel_classified_lemma(
                                                    &mut $self.proof_tracker,
                                                    &$self.ctx.terms,
                                                    terms,
                                                    _c3_dt.as_ref(),
                                                );
                                            if let Some(_fc_original_id) = _fc_original_id {
                                                $crate::pipeline_fns::place_original_clause_authority_at_id(
                                                    &solver,
                                                    _fc_original_id,
                                                    None,
                                                    Some(ay_core::TheoryLemmaProof {
                                                        clause: terms,
                                                        kind,
                                                        farkas: None,
                                                        lia: None,
                                                    }),
                                                    &mut _islp_local_clausification_proofs,
                                                    &mut _islp_local_original_clause_theory_proofs,
                                                );
                                            }
                                        }
                                    }
                                    continue;
                                }
                                // #9224: Handle Unsat/UnsatWithFarkas from post-SAT final
                                // check. Previously fell through to catch-all returning
                                // Unknown(Incomplete), causing sc-6/sc-8/simple_startup/
                                // uart/clocksynchro benchmarks to return unknown.
                                ay_core::TheoryResult::Unsat(mut conflict_lits) => {
                                    tracing::debug!(
                                        iter = _iteration,
                                        conflict_len = conflict_lits.len(),
                                        "#9224 post-SAT final check Unsat, adding conflict clause"
                                    );
                                    $crate::verification::dedup_conflict_literals(&mut conflict_lits);
                                    if $crate::verification::verify_conflict_semantic_memoized(
                                        &mut $self.conflict_semantic_verify_memo,
                                        &conflict_lits,
                                        &$self.ctx.terms,
                                        &$self.active_support_axioms,
                                    )
                                    .is_err()
                                    {
                                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                        $self.last_result = Some(SolveResult::Unknown);
                                        break 'split_loop Ok(SolveResult::Unknown);
                                    }
                                    let _fc_conflict_annotation = if proof_enabled {
                                        dt_conflict_proof!(
                                            $self,
                                            _islp_negations,
                                            &conflict_lits,
                                            $crate::theory_inference::dt_funnel_registry_data(&$self.ctx)
                                        )
                                    } else { None };
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    theory.unset_terms();
                                    let mut sat_clause = Vec::with_capacity(conflict_lits.len());
                                    let mut all_mapped = true;
                                    for tlit in &conflict_lits {
                                        if let Some(&var) = local_term_to_var.get(&tlit.term) {
                                            let lit = if tlit.value {
                                                ay_sat::Literal::negative(ay_sat::Variable::new(var))
                                            } else {
                                                ay_sat::Literal::positive(ay_sat::Variable::new(var))
                                            };
                                            sat_clause.push(lit);
                                        } else {
                                            all_mapped = false;
                                            break;
                                        }
                                    }
                                    if all_mapped && !sat_clause.is_empty() {
                                        let _fc_before = solver.issued_original_clause_id_max();
                                        solver.add_clause(sat_clause);
                                        if let (Some(_fc_id), Some(_fc_proof)) = (
                                            $crate::executor::theories::split_incremental::single_issued_original_id_since(solver, _fc_before),
                                            _fc_conflict_annotation,
                                        ) {
                                            if !matches!(_fc_proof.kind, ay_core::TheoryLemmaKind::Generic) {
                                                $crate::pipeline_fns::place_original_clause_authority_at_id(
                                                    &solver,
                                                    _fc_id,
                                                    None,
                                                    Some(_fc_proof),
                                                    &mut _islp_local_clausification_proofs,
                                                    &mut _islp_local_original_clause_theory_proofs,
                                                );
                                            }
                                        }
                                        continue;
                                    }
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                                ay_core::TheoryResult::UnsatWithFarkas(mut conflict) => {
                                    tracing::debug!(
                                        iter = _iteration,
                                        conflict_len = conflict.literals.len(),
                                        "#9224 post-SAT final check UnsatWithFarkas, adding conflict clause"
                                    );
                                    $crate::verification::dedup_conflict_with_farkas(&mut conflict);
                                    let _fc_farkas_valid = conflict.farkas.is_some()
                                        && $crate::verification::verify_theory_conflict_with_farkas(&conflict).is_ok()
                                        && $crate::verification::verify_theory_conflict_with_farkas_full(
                                            &conflict,
                                            &$self.ctx.terms,
                                        ).is_ok();
                                    if !_fc_farkas_valid
                                        && $crate::verification::verify_conflict_semantic_memoized(
                                            &mut $self.conflict_semantic_verify_memo,
                                            &conflict.literals,
                                            &$self.ctx.terms,
                                            &$self.active_support_axioms,
                                        ).is_err()
                                    {
                                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                        $self.last_result = Some(SolveResult::Unknown);
                                        break 'split_loop Ok(SolveResult::Unknown);
                                    }
                                    let _fc_conflict_annotation = if proof_enabled && _fc_farkas_valid {
                                        dt_farkas_proof!(
                                            $self,
                                            _islp_negations,
                                            &conflict,
                                            $crate::theory_inference::dt_funnel_registry_data(&$self.ctx)
                                        )
                                    } else if proof_enabled {
                                        dt_conflict_proof!(
                                            $self,
                                            _islp_negations,
                                            &conflict.literals,
                                            $crate::theory_inference::dt_funnel_registry_data(&$self.ctx)
                                        )
                                    } else { None };
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    theory.unset_terms();
                                    let mut sat_clause = Vec::with_capacity(conflict.literals.len());
                                    let mut all_mapped = true;
                                    for tlit in &conflict.literals {
                                        if let Some(&var) = local_term_to_var.get(&tlit.term) {
                                            let lit = if tlit.value {
                                                ay_sat::Literal::negative(ay_sat::Variable::new(var))
                                            } else {
                                                ay_sat::Literal::positive(ay_sat::Variable::new(var))
                                            };
                                            sat_clause.push(lit);
                                        } else {
                                            all_mapped = false;
                                            break;
                                        }
                                    }
                                    if all_mapped && !sat_clause.is_empty() {
                                        let _fc_before = solver.issued_original_clause_id_max();
                                        solver.add_clause(sat_clause);
                                        if let (Some(_fc_id), Some(_fc_proof)) = (
                                            $crate::executor::theories::split_incremental::single_issued_original_id_since(solver, _fc_before),
                                            _fc_conflict_annotation,
                                        ) {
                                            if !matches!(_fc_proof.kind, ay_core::TheoryLemmaKind::Generic) {
                                                $crate::pipeline_fns::place_original_clause_authority_at_id(
                                                    &solver,
                                                    _fc_id,
                                                    None,
                                                    Some(_fc_proof),
                                                    &mut _islp_local_clausification_proofs,
                                                    &mut _islp_local_original_clause_theory_proofs,
                                                );
                                            }
                                        }
                                        continue;
                                    }
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                                ay_core::TheoryResult::Unknown => {
                                    tracing::debug!(
                                        iter = _iteration,
                                        "#9224 post-SAT final check returned Unknown, continuing"
                                    );
                                    continue;
                                }
                                _ => {
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                            }
                        }

                        if let Some(split_result) = pending_split {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            // #8762: drain batched disequality splits BEFORE releasing
                            // the theory's term borrow so we can encode all pairwise
                            // disequalities in one SAT-resolve round.
                            let _drained_diseq_extras =
                                <_ as ay_core::TheorySolver>::drain_pending_diseq_splits(&mut theory);
                            // #6590: unset terms before mutating self.ctx.terms
                            // for split atom creation. Theory persists.
                            theory.unset_terms();

                            pipeline_incremental_split_eager_dispatch_split!(
                                'split_loop, $self, solver,
                                tag: $tag, suffix: "-INC-EAGER-PERSIST",
                                local_term_to_var, local_var_to_term, local_next_var, _islp_negations,
                                _islp_added_split_clauses, _islp_last_split_values,
                                split_result: split_result,
                                drained_diseq_extras: _drained_diseq_extras,
                                fallthrough: {
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                            );
                        }

                        // Check if there are genuinely NEW refinements that the SAT
                        // solver hasn't seen.  With a persistent theory, soft_reset()
                        // can re-derive the same bound refinements the SAT solver
                        // already contains.  Re-running the loop in that case leads
                        // to an infinite refinement cycle (#6590).
                        let has_new_refinements = pending_refinements.iter().any(|r| {
                            let key = $crate::executor::theories::split_incremental::BoundRefinementReplayKey::new(r);
                            !_islp_added_refinement_clauses.contains(&key)
                        });

                        if has_new_refinements {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            theory.unset_terms();

                            if !$crate::executor::theories::split_incremental::replay_incremental_bound_refinements(
                                &mut $self.ctx.terms,
                                solver,
                                &mut local_term_to_var,
                                &mut local_var_to_term,
                                &mut local_next_var,
                                &mut _islp_negations,
                                &pending_refinements,
                                &mut _islp_added_refinement_clauses,
                            ) {
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                break 'split_loop Ok(SolveResult::Unknown);
                            }

                            continue;
                        }

                        // No pending split — theory is SAT. Extract model.
                        //
                        // #8373 completeness fix: instead of unconditionally
                        // breaking out of the split loop (via pipeline_store_sat_model!),
                        // check the model validation result. When validation fails
                        // (Violated → Unknown), add a blocking clause to prevent
                        // the SAT solver from finding the same assignment again,
                        // then continue the split loop. This allows the solver to
                        // explore other Boolean assignments and potentially find
                        // UNSAT, instead of immediately giving up with Unknown.
                        //
                        // On QF_LRA benchmarks with ITE-heavy structure (tgc_io-safe,
                        // clocksynchro, 1.smt2, 5.smt2), the LRA theory can produce
                        // arithmetically-consistent models that violate the original
                        // assertions' Boolean structure. Blocking the spurious SAT
                        // and retrying is the standard DPLL(T) completeness mechanism
                        // for handling theory incompleteness.
                        {
                            let _psm_extract_start = ay_core::time::Instant::now();
                            let $theory_var = &mut theory;
                            let _psm_models = $extract;
                            _islp_timing.model_extract += _psm_extract_start.elapsed();

                            let _psm_fake_result = ay_core::TseitinResult::new(
                                vec![],
                                local_term_to_var.iter().map(|(&t, &v)| (t, v + 1)).collect(),
                                local_var_to_term.iter().map(|(&v, &t)| (v + 1, t)).collect(),
                                1,
                                local_next_var,
                            );
                            theory.unset_terms();

                            // #8373: With the take() pattern for incr_theory_state,
                            // $self is no longer borrowed through state/solver, so we
                            // can freely call $self methods here.
                            let _psm_store_start = ay_core::time::Instant::now();
                            let _psm_store_result = $self.solve_and_store_model_with_theories(
                                ay_sat::SatResult::Sat(model.clone()), &_psm_fake_result, _psm_models,
                            );
                            _islp_timing.store_model += _psm_store_start.elapsed();

                            // Check if model validation failed (SatResult::Sat converted
                            // to SolveResult::Unknown). This happens when the model is
                            // arithmetically consistent but violates the original formula's
                            // Boolean structure. Add a blocking clause to prevent the same
                            // Boolean assignment from recurring.
                            if let Ok(SolveResult::Unknown) = &_psm_store_result {
                                if _islp_blocking_retry_count < _ISLP_MAX_BLOCKING_RETRIES {
                                    // Build targeted blocking clause: negate only DECISION
                                    // variables among the term-backed variables (#8373).
                                    //
                                    // Rationale: propagated variables' values are fully
                                    // determined by decisions + clause database (BCP is
                                    // deterministic). Blocking just the decision cube is
                                    // sound and sufficient to prevent the same complete
                                    // assignment from recurring.
                                    //
                                    // To further limit clause size, sort decisions by
                                    // decision level (descending) and take at most
                                    // MAX_BLOCKING_LITS. Higher-level decisions are
                                    // more specific to the current search region and
                                    // more effective at pruning.
                                    //
                                    // Fallback: if no decision variables are found among
                                    // term-backed vars (e.g., all are level-0 propagations),
                                    // fall back to blocking all term-backed variables.
                                    const MAX_BLOCKING_LITS: usize = 64;
                                    let mut decision_lits: Vec<(u32, ay_sat::Literal)> = Vec::new();
                                    let mut all_clause = Vec::new();
                                    // #8515: Optimization blocking constraints may introduce
                                    // variables beyond the persistent SAT solver's variable
                                    // count. Guard against out-of-bounds access in
                                    // var_assignment_kind/var_level by checking bounds first.
                                    let _solver_num_vars = solver.total_num_vars();
                                    for (&var_id, &_term) in local_var_to_term.iter() {
                                        if let Some(&val) = model.get(var_id as usize) {
                                            let var = ay_sat::Variable::new(var_id);
                                            let lit = if val {
                                                ay_sat::Literal::negative(var)
                                            } else {
                                                ay_sat::Literal::positive(var)
                                            };
                                            all_clause.push(lit);
                                            // Skip solver queries for vars beyond the
                                            // solver's internal array size (#8515).
                                            if (var_id as usize) < _solver_num_vars
                                                && solver.var_assignment_kind(var)
                                                    == ay_sat::VarAssignmentKind::Decision
                                            {
                                                let level = solver.var_level(var).unwrap_or(0);
                                                decision_lits.push((level, lit));
                                            }
                                        }
                                    }
                                    let blocking_clause = if decision_lits.is_empty() {
                                        // No decisions found; use all variables as fallback.
                                        all_clause
                                    } else if decision_lits.len() <= MAX_BLOCKING_LITS {
                                        decision_lits.into_iter().map(|(_, lit)| lit).collect()
                                    } else {
                                        // Too many decisions; keep only the highest-level
                                        // ones (most specific to current search region).
                                        decision_lits.sort_unstable_by(|a, b| b.0.cmp(&a.0));
                                        decision_lits.truncate(MAX_BLOCKING_LITS);
                                        decision_lits.into_iter().map(|(_, lit)| lit).collect()
                                    };
                                    // SOUNDNESS (#9604 unsound-blocking guard): the
                                    // blocking clause negates the current complete
                                    // Boolean assignment. That is a sound refutation
                                    // step ONLY when the blocked assignment is
                                    // genuinely theory-UNSAT. Model validation,
                                    // however, can fail on a Boolean assignment that
                                    // is theory-SATISFIABLE — when the theory's
                                    // check() accepted it but extract_model() emitted
                                    // an arithmetic witness that violates the original
                                    // constraints (e.g. a strict bound realized at its
                                    // delta/epsilon boundary). Permanently blocking
                                    // such an assignment removes a satisfiable region
                                    // and a later propositional UNSAT becomes a
                                    // false-UNSAT (C5 / split-loop r7519 class).
                                    //
                                    // ROOT-CAUSE FIX (split-loop false-UNSAT, AY=unsat
                                    // where z3=sat): the soundness of blocking hinges on
                                    // whether the blocked Boolean assignment is genuinely
                                    // theory-UNSAT. The prior guard only suppressed the
                                    // block when a single `LraSolver::check()` returned
                                    // `Sat`, treating EVERY other status as "UNSAT → safe
                                    // to block". That is wrong: over the reals a single
                                    // `check()` of a linear-feasible atom set containing
                                    // `distinct`/`(not (= ..))` returns
                                    // `NeedDisequalitySplit`/`NeedExpressionSplit`
                                    // (a "must case-split to decide" status, NOT a proof
                                    // of unsatisfiability) whenever the chosen vertex
                                    // lands on a disequality hyperplane that still has
                                    // slack — i.e. for a SATISFIABLE assignment. Blocking
                                    // it removes a satisfiable region → false UNSAT.
                                    //
                                    // Block ONLY when a single `check()` proves the
                                    // assignment theory-UNSAT (`Unsat`/`UnsatWithFarkas`:
                                    // linear infeasibility, or a genuinely *pinned*
                                    // disequality). Otherwise the assignment is NOT proven
                                    // UNSAT; rather than fail closed (losing a real SAT
                                    // answer), recover a sound verdict by re-solving the
                                    // assignment's atom conjunction with the COMPLETE
                                    // split-loop, which drives the disequality splits to a
                                    // valid, validation-passing model. A `Sat` recovery is
                                    // published directly; a recovered `Unsat` makes
                                    // blocking sound; anything else fails closed.
                                    //
                                    // The guard is UNCONDITIONAL: the former
                                    // AY_NO_MODELVALFAIL_BLOCK_UNSAT_GUARD=1 kill
                                    // switch (skip the re-check and block
                                    // unconditionally — the prior, false-UNSAT-prone
                                    // behavior) is removed; no environment variable
                                    // may turn off a soundness guard.
                                    if !blocking_clause.is_empty() {
                                        let mut _islp_assignment_lits: Vec<ay_core::TheoryLit> =
                                            Vec::new();
                                        for (&var_id, &term) in local_var_to_term.iter() {
                                            if !ay_core::is_theory_atom(&$self.ctx.terms, term) {
                                                continue;
                                            }
                                            if let Some(&val) = model.get(var_id as usize) {
                                                _islp_assignment_lits
                                                    .push(ay_core::TheoryLit::new(term, val));
                                            }
                                        }
                                        if !_islp_assignment_lits.is_empty()
                                            && !$self.lra_assignment_recheck_proves_unsat(
                                                &_islp_assignment_lits,
                                            )
                                        {
                                            // The blocked assignment is NOT proven
                                            // theory-UNSAT, so blocking it would be
                                            // unsound.
                                            theory.unset_terms();
                                            if $self.lra_in_assignment_recheck {
                                                // Already inside a recovery re-solve:
                                                // do not recurse further. Fail closed.
                                                tracing::warn!(
                                                    iter = _iteration,
                                                    concat!("Eager persistent ", $tag, " model-validation failure on a not-provably-UNSAT assignment during nested recovery; failing closed to Unknown (#split-loop-false-unsat)")
                                                );
                                                $self.last_unknown_reason =
                                                    Some(UnknownReason::Incomplete);
                                                $self.last_result =
                                                    Some(SolveResult::Unknown);
                                                break 'split_loop Ok(SolveResult::Unknown);
                                            }
                                            // Recover a sound verdict via a complete,
                                            // disequality-split-aware re-solve of the
                                            // assignment's atom conjunction.
                                            match $self.lra_recover_assignment_verdict(
                                                &_islp_assignment_lits,
                                            ) {
                                                Ok(SolveResult::Sat) => {
                                                    tracing::warn!(
                                                        iter = _iteration,
                                                        concat!("Eager persistent ", $tag, " model-validation failure recovered to SAT via complete disequality-aware re-solve (#split-loop-false-unsat)")
                                                    );
                                                    // last_result / last_model are set
                                                    // by the recovery re-solve to a
                                                    // validation-passing SAT model.
                                                    break 'split_loop Ok(SolveResult::Sat);
                                                }
                                                Ok(ref r) if r.is_unsat() => {
                                                    // The assignment IS genuinely
                                                    // theory-UNSAT (the complete solve
                                                    // proved it once splits were driven);
                                                    // blocking it is sound. Fall through
                                                    // to add the blocking clause.
                                                }
                                                _ => {
                                                    tracing::warn!(
                                                        iter = _iteration,
                                                        concat!("Eager persistent ", $tag, " model-validation failure: recovery re-solve indeterminate; failing closed to Unknown (#split-loop-false-unsat)")
                                                    );
                                                    $self.last_unknown_reason =
                                                        Some(UnknownReason::Incomplete);
                                                    $self.last_result =
                                                        Some(SolveResult::Unknown);
                                                    break 'split_loop Ok(SolveResult::Unknown);
                                                }
                                            }
                                        }
                                    }
                                    // #lra-inc-engine: a model-validation blocking
                                    // clause is clause-DB-relative and unsafe to
                                    // persist across check-sats (it could smuggle a
                                    // false-UNSAT into a later check). In persist
                                    // mode fail closed to Unknown; the lane's caller
                                    // falls back to the isolated from-scratch
                                    // standalone path, which recovers a definite
                                    // verdict with the full blocking/recovery
                                    // machinery on a throwaway solver.
                                    if $self.lra_persist_sat_active {
                                        tracing::debug!(
                                            iter = _iteration,
                                            "#lra-inc-engine model validation failed in persist mode; failing closed for standalone fallback"
                                        );
                                        break 'split_loop Ok(SolveResult::Unknown);
                                    }
                                    if !blocking_clause.is_empty() {
                                        tracing::warn!(
                                            clause_len = blocking_clause.len(),
                                            iter = _iteration,
                                            retries = _islp_blocking_retry_count,
                                            "#8373 adding blocking clause after model validation failure"
                                        );
                                        solver.add_clause(blocking_clause);
                                        $self.last_model = None;
                                        _islp_blocking_retry_count += 1;
                                        continue;
                                    } else {
                                        tracing::warn!(
                                            iter = _iteration,
                                            local_vars = local_var_to_term.len(),
                                            model_len = model.len(),
                                            "#8373 blocking clause is EMPTY, cannot retry"
                                        );
                                    }
                                }
                            }
                            // Success, retry limit reached, or error.
                            break 'split_loop _psm_store_result;
                        }
                    }
                    SatResult::Unsat(_) => {
                        // #6812: Soundness guard — when theory conflicts had terms
                        // that couldn't map to SAT literals (partial clauses), the
                        // learned clauses are stronger than what the theory proved.
                        // A propositional UNSAT derived from such clauses is unsound.
                        if _ext_partial > 0 {
                            tracing::warn!(
                                partial_clauses = _ext_partial,
                                concat!("Eager persistent ", $tag, " produced UNSAT with dropped theory conflicts; escalating to Unknown")
                            );
                            theory.unset_terms();
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                        // SOUNDNESS (#9604-class false-UNSAT): the #8373 model-
                        // validation-failure blocking clauses are guarded at their
                        // emission site below (see "#9604 unsound-blocking guard"):
                        // a blocking clause is only emitted when the blocked Boolean
                        // assignment is genuinely theory-UNSAT. When it is instead
                        // theory-SAT (validation failed on a good assignment because
                        // `extract_model()` produced a bad arithmetic witness), the
                        // solve fails closed to Unknown there rather than poisoning
                        // the clause DB. So any UNSAT that reaches here was derived
                        // only from sound blocking clauses (plus tautological split
                        // clauses), and is itself sound.
                        // #6846: Expression split clauses (NeedSplit: x ≤ k ∨ x ≥ k+1)
                        // are tautological over integers and cannot make a
                        // satisfiable formula UNSAT. Model equalities are only
                        // SAT decision hints (`try_true_first`), not permanent
                        // clauses. In the persistent eager arm, the theory
                        // solver also persists across iterations, so learned
                        // clauses remain sound. UNSAT accepted.
                        if !_islp_added_split_clauses.is_empty() {
                            tracing::debug!(
                                split_clauses = _islp_added_split_clauses.len(),
                                concat!("Eager persistent ", $tag, " UNSAT after expression splits (tautological, accepted)")
                            );
                        }
                        theory.unset_terms();
                        _islp_negations.sync_pending(&mut $self.ctx.terms);
                        pipeline_incremental_split_eager_build_unsat_proof!(
                            'split_loop, $self, solver, state,
                            local_var_to_term, _islp_negations, proof_enabled,
                            _islp_local_clausification_proofs, _islp_local_original_clause_theory_proofs
                        );
                    }
                    SatResult::Unknown => {
                        if let Some(split_result) = pending_split {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            // #8762: drain batched disequality splits BEFORE
                            // releasing the theory's term borrow.
                            let _drained_diseq_extras =
                                <_ as ay_core::TheorySolver>::drain_pending_diseq_splits(&mut theory);
                            theory.unset_terms();

                            pipeline_incremental_split_eager_dispatch_split!(
                                'split_loop, $self, solver,
                                tag: $tag, suffix: "-INC-EAGER-PERSIST",
                                local_term_to_var, local_var_to_term, local_next_var, _islp_negations,
                                _islp_added_split_clauses, _islp_last_split_values,
                                split_result: split_result,
                                drained_diseq_extras: _drained_diseq_extras,
                                fallthrough: {}
                            );
                        }

                        // Same duplicate-refinement guard as the SAT path (#6590).
                        let has_new_refinements_unk = pending_refinements.iter().any(|r| {
                            let key = $crate::executor::theories::split_incremental::BoundRefinementReplayKey::new(r);
                            !_islp_added_refinement_clauses.contains(&key)
                        });

                        if has_new_refinements_unk {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            theory.unset_terms();

                            if !$crate::executor::theories::split_incremental::replay_incremental_bound_refinements(
                                &mut $self.ctx.terms,
                                solver,
                                &mut local_term_to_var,
                                &mut local_var_to_term,
                                &mut local_next_var,
                                &mut _islp_negations,
                                &pending_refinements,
                                &mut _islp_added_refinement_clauses,
                            ) {
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                break 'split_loop Ok(SolveResult::Unknown);
                            }

                            continue;
                        }

                        // #8256/#8399: If the Unknown was caused by conflict budget
                        // exhaustion (not a real global interrupt), continue the
                        // split-loop. The next iteration will use
                        // continue_solving_with_extension() to preserve VSIDS
                        // scores and learned clauses, giving the SAT solver a
                        // chance to converge with fresh theory guidance from the
                        // soft_reset_warm() cycle.
                        //
                        // #8399: Stall detection — if continue_solving made no
                        // progress (< MIN_CONFLICT_PROGRESS conflicts) for
                        // MAX_CONTINUE_STALLS consecutive budget-exhausted
                        // iterations, fall back to full solve. This prevents
                        // the sc-8 non-convergence pattern where stale learned
                        // clauses lock the solver into revisiting the same
                        // search region indefinitely.
                        if _islp_budget_exhausted.get() && !_islp_base_should_stop() {
                            let _post_conflicts = solver.num_conflicts();
                            let _conflict_progress = _post_conflicts
                                .saturating_sub(_islp_pre_solve_conflicts);

                            // Track stalls only when resume/continue was used.
                            // Full solve iterations always reset the counter.
                            if (_islp_use_continue_this_iter || _islp_use_resume_this_iter)
                                && _conflict_progress < _ISLP_MIN_CONFLICT_PROGRESS
                            {
                                _islp_continue_stall_count += 1;
                            } else {
                                _islp_continue_stall_count = 0;
                            }

                            // If stalled for too many consecutive iterations,
                            // escalate the solve strategy to break out of stuck
                            // search regions. Two-level escalation (#8399):
                            //
                            //   Level 0: resume_solving stalls -> continue_solving
                            //     (trail reset + learned clause flush + restart reset)
                            //   Level 1: continue_solving stalls repeatedly ->
                            //     full solve (complete reinit + theory warm reset)
                            //
                            // This prevents the sc-8 non-convergence pattern while
                            // allowing the solver to escalate through increasingly
                            // aggressive state resets when lighter resets fail.
                            if _islp_continue_stall_count >= _ISLP_MAX_CONTINUE_STALLS {
                                _islp_continue_stall_count = 0;
                                _islp_continue_fallback_count += 1;

                                if _islp_continue_fallback_count >= _ISLP_MAX_CONTINUE_FALLBACKS {
                                    // Level 1: continue_solving has stalled repeatedly.
                                    // Escalate to full solve with complete state rebuild.
                                    tracing::debug!(
                                        iter = _iteration,
                                        fallbacks = _islp_continue_fallback_count,
                                        progress = _conflict_progress,
                                        "#8399 continue_solving stalled repeatedly, escalating to full solve"
                                    );
                                    _islp_continue_fallback_count = 0;
                                    // Full solve: neither continue nor resume
                                    _islp_use_continue_solving = false;
                                    _islp_use_resume_solving = false;
                                } else {
                                    // Level 0: resume stalled, fall back to continue
                                    tracing::debug!(
                                        iter = _iteration,
                                        stalls = _ISLP_MAX_CONTINUE_STALLS,
                                        fallbacks = _islp_continue_fallback_count,
                                        progress = _conflict_progress,
                                        "#8399 resume stalled, falling back to continue_solving"
                                    );
                                    _islp_use_continue_solving = true;
                                    _islp_use_resume_solving = false;
                                }
                            } else {
                                tracing::debug!(
                                    iter = _iteration,
                                    resume = _islp_use_resume_this_iter,
                                    continue_solving = _islp_use_continue_this_iter,
                                    progress = _conflict_progress,
                                    stalls = _islp_continue_stall_count,
                                    "#8256 budget exhausted, resuming split-loop"
                                );
                                // Prefer resume (zero overhead) over continue
                                _islp_use_continue_solving = true;
                                _islp_use_resume_solving = true;
                            }

                            theory.unset_terms();
                            continue;
                        }
                        theory.unset_terms();
                        $self.last_model = None;
                        if $self.last_unknown_reason.is_none() {
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        }
                        $self.last_result = Some(SolveResult::Unknown);
                        break 'split_loop Ok(SolveResult::Unknown);
                    }
                    #[allow(unreachable_patterns)]
                    _ => unreachable!(),
                }
            }

            // Too many splits - return unknown
            theory.unset_terms();
            if $self.last_unknown_reason.is_none() {
                $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
            }
            $self.last_result = Some(SolveResult::Unknown);
            Ok(SolveResult::Unknown)
        };

        // #8373: Restore the owned state back into $self now that all borrows
        // (state, solver) from the split loop have ended.
        _islp_owned_state.scratch_var_to_term = local_var_to_term;
        // #lra-inc-engine S3 (warm theory): persist the theory solver across
        // check-sats so its base bounds + implied_bounds cache carry over (see
        // the take at theory creation). terms_ptr is left dangling here (the
        // exit paths unset_terms); set_terms refreshes it on the next reuse.
        // Only in warm mode; the from-scratch re-verify lane uses a throwaway
        // temp state, so this never persists there.
        if _islp_inc_warm {
            _islp_owned_state.persist_theory = Some(Box::new(theory));
        }
        $self.incr_theory_state = Some(_islp_owned_state);

        pipeline_split_epilogue!(
            $self, _islp_timing, _islp_total_start,
            _islp_last_theory_stats, _islp_result,
            eager: { pipeline_export_split_loop_eager_stats!($self, _islp_eager_stats); },
            restore: {}
        )
    }};
    // Default-fields rule: when tseitin_field/encoded_field/activation_scope_field
    // are not provided, use the standard IncrementalTheoryState field names (#6853).
    ($self:ident,
        tag: $tag:expr,
        persistent_sat_field: $sat_field:ident,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        max_splits: $max_splits:expr,
        pre_theory_import: |$import_theory:ident, $import_lc:ident, $import_hc:ident, $import_ds:ident| $import_expr:expr,
        post_theory_export: |$export_theory:ident| $export_expr:expr
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
    ) => {{
        pipeline_incremental_split_eager_persistent_arm!($self,
            tag: $tag,
            persistent_sat_field: $sat_field,
            tseitin_field: tseitin_state,
            encoded_field: encoded_assertions,
            activation_scope_field: assertion_activation_scope,
            create_theory: $create_theory,
            extract_models: |$theory_var| $extract,
            max_splits: $max_splits,
            pre_theory_import: |$import_theory, $import_lc, $import_hc, $import_ds| $import_expr,
            post_theory_export: |$export_theory| $export_expr
            $(, pre_iter_check: |$pic_self| $pic_expr)?
        )
    }};
}
