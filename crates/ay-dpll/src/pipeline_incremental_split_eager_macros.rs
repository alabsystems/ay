// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager arm of the incremental split-loop pipeline.
//!
//! Extracted from `pipeline_incremental_split_macros.rs` (#6680).
//! Contains the eager theory-SAT interleaving path via TheoryExtension.
//! Each iteration creates a fresh theory for borrow safety. SAT solver
//! runs with TheoryExtension for inline BCP propagation.

#![allow(unused_macros)]

/// Eager arm implementation for `solve_incremental_split_loop_pipeline!`.
///
/// Key differences from the lazy arm:
/// 1. Each iteration creates a fresh theory (same as lazy) for borrow safety
/// 2. SAT solver runs with TheoryExtension for inline BCP propagation
/// 3. Theory conflicts are learned during search (not after full model)
/// 4. TheoryExtension handles push/pop for backtracking within one solve
/// 5. Theory is dropped before split atom creation (needs &mut TermStore)
// Live call sites: AUFLIA (combined.rs), UF+LRA (combined.rs), UF+LIA (combined.rs).
// The eager-persistent arm (with persistent_theory: true) is used by lra.rs.
macro_rules! pipeline_incremental_split_eager_arm {
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
        $(, disable_preprocess: $disable_preprocess:expr)?
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
        $(, accept_unsat_after_splits: $accept_unsat:expr)?
        $(, verify_unsat_after_splits: $verify_unsat:expr)?
        $(, skip_arith_triangle: $skip_arith_tri:expr)?
        $(, max_string_lemma_requests: $max_slr:expr,
           handle_string_lemma: |$sl_lemma:ident, $sl_negations:ident| $sl_handler:expr)?
    ) => {{
#[cfg(not(kani))]
        // #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
#[cfg(kani)]
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
        use ay_core::{TermId, Tseitin, TseitinEncodedAssertion};
        use ay_sat::{Literal as SatLiteral, SatResult, Solver as SatSolver, Variable as SatVariable};
        use $crate::executor_types::{SolveResult, UnknownReason};
        use $crate::incremental_state::{collect_active_theory_atoms_cached, IncrementalTheoryState};
        use $crate::executor::theories::freeze_var_if_needed;

        let proof_enabled = $self.produce_proofs_enabled();

        // Take ownership so NeedStringLemma handlers can borrow $self.
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
        let _islp_should_stop = $self.make_should_stop();

        let _ = $self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);
        let mut state = $self
            .incr_theory_state
            .take()
            .expect("invariant: incr_theory_state initialized by get_or_insert_with above");
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
        $(
            solver.set_preprocess_enabled(!$disable_preprocess);
        )?
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
        // #6853: Apply deferred activations immediately (no private push in eager arm).
        pipeline_apply_pending_activations_immediate!(
            solver, pending_activations, proof_enabled, state
        );

        let _islp_scope_depth_unsupported = state.scope_depth != 0;
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
        // #6851: Centralized model-equality tracker replaces per-path
        // HashMap + counter duplication that caused #6846.
        let mut _islp_model_eq_tracker = $crate::executor::theories::split_incremental::ModelEqualityTracker::new(
            $crate::executor::theories::split_incremental::model_equality::MODEL_EQ_MAX_ROUNDS_EAGER,
        );
        // #6846: Total non-convergence iteration counter. The non-persistent
        // eager arm recreates the theory each iteration, losing convergence
        // state. When the solver alternates between NeedExpressionSplit and
        // NeedModelEqualities without making progress, this cap ensures
        // termination with Unknown within reasonable time.
        //
        // #ssl-residue D1: the counter RESETS whenever an iteration made
        // genuine progress — a NEW split clause, bound refinement, theory
        // axiom, or encoded atom strictly grew the solver's knowledge (see
        // the watermark below). Without the reset this was a hard 100-round
        // cap on branch-and-bound (any LIA instance needing >100 split
        // rounds bailed to Unknown), not a no-progress detector. True
        // oscillation (iterations whose dedup sets admit nothing new) still
        // hits the cap, preserving the #6846 termination guarantee; overall
        // termination stays bounded by `$max_splits`, the pre-iteration
        // deadline/interrupt check, and the per-solve conflict/decision
        // budgets. Verdict-safe: a longer search can only convert
        // unknown -> validated-sat or -> unsat, never fabricate.
        let mut _islp_no_progress_iters: usize = 0;
        const _ISLP_MAX_NO_PROGRESS_ITERS: usize = 100;
        let mut _islp_progress_watermark: (usize, usize, usize, usize) =
            (usize::MAX, usize::MAX, usize::MAX, usize::MAX);
        // #8594: Pipeline-level dedup for model equality requests. The
        // non-persistent eager arm recreates the theory each iteration,
        // losing ArraySolver::requested_interface_eqs. Without this
        // dedup, the fresh theory regenerates the same NeedModelEquality
        // requests each iteration, cycling until the no-progress cap.
        // Keys are (lhs, rhs) TermId pairs from the requests — these are
        // stable TermStore IDs, unlike equivalence class roots.
        let mut _islp_seen_model_eq_requests: HashSet<(TermId, TermId)> = HashSet::default();

        // #8596: Whether to skip arithmetic triangle axioms in model equality
        // encoding. Pure ArrayEUF (no LIA/LRA) must skip them because the
        // (x <= y) atoms have no theory interpretation, causing spurious
        // EUF bool-congruence conflicts and false UNSAT.
        let _islp_skip_arith_triangle: bool = false;
        $(let _islp_skip_arith_triangle: bool = $skip_arith_tri;)?

        // Inc5 #fused-detour: capture the executor's eager relevancy-HARD flag
        // ONCE at attempt entry. Non-fused attempts (the default: eager1, the
        // hybrid's isolated resume, the AUFLIA/UF+LRA lanes) carry `false` and
        // keep their byte-identical relevancy configuration below. The FUSED
        // detour arm (`--uflia-fused-detour=1`, combined/mod.rs #fused-detour
        // slot) sets the flag around this expansion so relevancy-hard rides
        // the live TheoryExtension on the SHARED persistent solver
        // (the development design notes §2 Inc5).
        // Captured as a local so a re-entrant inner solve
        // (`verify_post_split_unsat_via_fresh_solve` re-enters check-sat,
        // whose UFLIA entry defensively resets the executor flags) can never
        // flip this attempt's per-round relevancy configuration or its
        // cross-arm UNSAT guard mid-attempt.
        let _islp_eager_relevancy_hard: bool = $self.split_eager_relevancy_hard;

        // Per-theory statistics saved from the most recent theory instance (#6579).
        let mut _islp_last_theory_stats: Vec<(&'static str, u64)> = Vec::new();
        let mut _islp_string_lemma_clauses: Vec<Vec<TermId>> = Vec::new();
        let mut _islp_string_lemma_requests = 0usize;

        // Split-loop timing (#6503).
        let mut _islp_timing = $crate::SplitLoopTimingStats::default();
        let _islp_total_start = ay_core::time::Instant::now();
        let mut _islp_eager_stats = $crate::DpllEagerStats::default();

        // Proof ledger clone + context registration (#5814 Packet A)
        // Reordered: proof labels -> negation cache (parity with lazy/assume arms).
        let (mut _islp_local_clausification_proofs, mut _islp_local_original_clause_theory_proofs) =
            pipeline_clone_local_proof_ledgers!(state, proof_enabled);
        pipeline_register_proof_context!($self, proof_enabled, $tag);
        // Negation cache seeding (#6660, #6735): build negation map once and
        // sync only newly encoded terms before proof consumers run.
        let mut _islp_negations = $crate::incremental_proof_cache::IncrementalNegationCache::seed(
            &mut $self.ctx.terms,
            local_var_to_term.values().copied(),
            proof_enabled,
        );

        // Fix 3 Layer A (#8857): per-Executor bound-axiom cache for the eager
        // arm. Compute the key over the iteration-0 active theory atom set —
        // exactly the set iteration 0's TheoryExtension would register and
        // generate bound axioms from. On a VALIDATED cache hit, replay the
        // pairs as SAT clauses up front (mirroring the eager-persistent arm's
        // pipeline_inject_bound_axioms! pre-injection) and construct the
        // extension with new_skip_bound_axioms, skipping generation and
        // per-pair validation entirely.
        let _islp_ba_iter0_atoms: Vec<TermId> =
            $crate::iter_var_to_term_sorted(&local_var_to_term)
                .map(|(_, term)| term)
                .filter(|term| {
                    base_active_atom_set.contains(term)
                        || $crate::is_theory_atom(&$self.ctx.terms, *term)
                })
                .collect();
        let _islp_ba_key = $crate::incremental_state::bound_axiom_atom_set_key(
            _islp_ba_iter0_atoms.iter().copied(),
        );
        let mut _islp_ba_pre_injected = false;
        {
            let mut _ba_cached: Option<(
                Vec<(TermId, bool, TermId, bool)>,
                Vec<Option<ay_core::FarkasAnnotation>>,
            )> = None;
            if let Some(_ba_c) = state.bound_axiom_cache.as_ref() {
                if _ba_c.atom_set_key == _islp_ba_key
                    && _ba_c.atom_count == _islp_ba_iter0_atoms.len()
                    && _ba_c.validated
                    && (!proof_enabled || _ba_c.proof_validated)
                {
                    _ba_cached = Some((_ba_c.pairs.clone(), _ba_c.farkas.clone()));
                }
            }
            if let Some((_ba_pairs, _ba_farkas)) = _ba_cached {
                tracing::debug!(
                    registered_atoms = _islp_ba_iter0_atoms.len(),
                    axiom_pairs = _ba_pairs.len(),
                    concat!("Bound axiom cache hit (#8857) for eager ", $tag)
                );
                let mut _ba_farkas_store = _ba_farkas;
                let (_ba_added, _ba_dropped) = pipeline_add_bound_axiom_clauses!(
                    $self, solver, local_term_to_var, proof_enabled,
                    _ba_pairs, _ba_farkas_store, true,
                    _islp_local_clausification_proofs,
                    _islp_local_original_clause_theory_proofs
                );
                let _ = (_ba_added, _ba_dropped);
                _islp_ba_pre_injected = true;
            }
        }

        // #bool-arg-congruence: Encode + freeze clauseless Bool-sorted UF
        // arguments so DPLL(T) DECIDES them. Without a SAT variable, a Bool arg
        // that appears only inside UF applications (e.g. `(bool (and ...))`)
        // never gets a truth value, the EUF model stays partial, and the model
        // validator degrades the result to `unknown`. EUF's Bool-argument
        // congruence completeness (which rejects every non-congruent assignment)
        // makes deciding these atoms SOUND: the SAT solver backtracks through
        // non-congruent assignments until it finds a congruent model or proves
        // UNSAT. Gated by AY_EUF_BOOL_ARG_CONGRUENCE (default ON).
        {
            let _islp_bool_arg_encoded =
                $crate::executor::theories::split_incremental::encode_bool_uf_arg_atoms(
                    &$self.ctx.terms,
                    solver,
                    &mut local_term_to_var,
                    &mut local_var_to_term,
                    &mut local_next_var,
                    &mut _islp_negations,
                    &base_active_atom_set,
                    $self.incremental_mode,
                );
            if _islp_bool_arg_encoded > 0 {
                tracing::debug!(
                    encoded = _islp_bool_arg_encoded,
                    concat!("Eager ", $tag, ": encoded clauseless Bool UF-arg atoms for decision (#bool-arg-congruence)")
                );
            }
        }

        let _islp_result: $crate::executor_types::Result<SolveResult> = 'split_loop: {
            if _islp_scope_depth_unsupported {
                tracing::warn!(
                    scope_depth = state.scope_depth,
                    concat!(
                        "Incremental eager ",
                        $tag,
                        " split-loop requires isolated scope depth 0; returning Unknown"
                    )
                );
                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                $self.last_result = Some(SolveResult::Unknown);
                $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L296"));
                break 'split_loop Ok(SolveResult::Unknown);
            }

            // #qfuflia-diseq-preencode: eagerly encode every syntactic Int/Real
            // disequality's case split up front (budgeted, guarded tautologies)
            // so LIA/LRA eager propagation refutes bad candidate models during
            // search instead of surfacing ~2 pairs per full SAT re-solve round.
            {
                let _islp_pre_encoded =
                    $crate::executor::theories::split_incremental::pre_encode_int_disequality_splits(
                        &mut $self.ctx.terms,
                        &$self.ctx.assertions.clone(),
                        solver,
                        &mut local_term_to_var,
                        &mut local_var_to_term,
                        &mut local_next_var,
                        &mut _islp_negations,
                        &mut _islp_added_split_clauses,
                    );
                if _islp_pre_encoded > 0 {
                    tracing::debug!(
                        pre_encoded = _islp_pre_encoded,
                        concat!("Incremental eager ", $tag, ": pre-encoded disequality splits")
                    );
                }
            }

            for _iteration in 0..$max_splits {
                // Pre-iteration check (interrupt/deadline)
                $(
                    {
                        let $pic_self = &();
                        if $pic_expr {
                            let _ = solver.pop();
                            $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L330"));
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                    }
                )?

                state.round_trips += 1;
                _islp_timing.dpll.round_trips += 1;

                // #6846: non-convergence guard for non-persistent eager arm.
                // #ssl-residue D1: reset the counter when the previous
                // iteration added ANYTHING new (split clause, bound
                // refinement, theory axiom, or encoded atom) — the dedup
                // sets below are append-only, so growth == genuine progress.
                // Only true oscillation accumulates toward the cap.
                {
                    let _islp_progress_now = (
                        _islp_added_split_clauses.len(),
                        _islp_added_refinement_clauses.len(),
                        _islp_added_axioms.len(),
                        local_term_to_var.len(),
                    );
                    if _islp_progress_now != _islp_progress_watermark {
                        _islp_progress_watermark = _islp_progress_now;
                        _islp_no_progress_iters = 0;
                    }
                }
                _islp_no_progress_iters += 1;
                if _islp_no_progress_iters > _ISLP_MAX_NO_PROGRESS_ITERS {
                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    $self.last_result = Some(SolveResult::Unknown);
                    $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L346"));
                    break 'split_loop Ok(SolveResult::Unknown);
                }

                let active_theory_atoms: Vec<TermId> =
                    $crate::iter_var_to_term_sorted(&local_var_to_term)
                        .map(|(_, term)| term)
                        .filter(|term| {
                            base_active_atom_set.contains(term)
                                || $crate::is_theory_atom(&$self.ctx.terms, *term)
                        })
                        .collect();
                let active_theory_atom_set: HashSet<TermId> =
                    active_theory_atoms.iter().copied().collect();
                // Sync only the fresh atoms introduced by prior iterations (#6735).
                _islp_negations.sync_pending(&mut $self.ctx.terms);
                let mut theory = $create_theory;
                ay_core::TheorySolver::set_sat_atom_terms(&mut theory, &local_term_to_var);
                {
                    let $import_theory = &mut theory;
                    let $import_lc = &mut _islp_learned_cuts;
                    let $import_hc = &mut _islp_seen_hnf_cuts;
                    let $import_ds = &mut _islp_dioph_state;
                    $import_expr;
                }
                theory.replay_learned_cuts();
                // #qf-auflia-fc-diseq-sync: top-level arithmetic disequality
                // FACTS are invisible to the extension when preprocessing
                // eliminated their SAT variables — assert them at theory
                // creation so every BCP/final check sees them (see
                // pipeline_fns::assert_top_level_arith_diseq_facts).
                let _islp_synced_diseq_facts =
                    $crate::pipeline_fns::assert_top_level_arith_diseq_facts(
                        &$self.ctx.terms,
                        &$self.ctx.assertions,
                        &mut theory,
                    );

                // #array-deadline-forward: forward the executor's live
                // per-solve deadline so inprocessing/L0-GC phases honor the
                // caller's wall budget (see the assume arm).
                solver.set_solve_deadline($self.solve_deadline.get());
                // Deterministic resource budgets (#8749 `:rlimit` +
                // #ground-determinism defaults). Bound this refinement's SAT
                // solve; with the `$max_splits` cap this guarantees
                // machine-independent termination on otherwise-diverging
                // theory loops (e.g. NIA). The decision-budget companion is
                // what bounds decision-heavy / conflict-light theory-
                // extension churn (the deductive-checks calc.rs seq-chain bridge
                // profile: ~240 decisions per conflict).
                solver.set_conflict_budget(
                    $crate::pipeline_fns::effective_conflict_allowance(
                        $self.resource_limit,
                        $self.ground_budget_enabled,
                    )
                    .map(|n| solver.num_conflicts().saturating_add(n)),
                );
                solver.set_decision_budget(
                    $crate::pipeline_fns::effective_decision_allowance(
                        $self.decision_limit,
                        $self.ground_budget_enabled,
                    )
                    .map(|n| solver.num_decisions().saturating_add(n)),
                );

                // Relevancy brancher (Increment 1): env-gated, hybrid Scheme-A
                // CNF-frontier decision restriction. Wired into the split-loop
                // theory lanes (UFLIA/AUFLIA/LIA). The hybrid trip-wire inside
                // ay-sat governs whether it actually engages per decision, and it
                // restricts DECISIONS only (BCP + model gate untouched), so it
                // can never cause a wrong verdict. See
                // the development design notes
                //
                // Inc5 #fused-detour seam (flag-respecting; mirrors the lazy
                // arm's seam verbatim): `--sat-relevancy` still kills the
                // brancher (env override wins); `--sat-relevancy|2` forces it
                // on. With the fused flag unset this computes exactly the
                // historical values (branching = env default-off, hard =
                // false — eager solves never ran relevancy HARD, and the
                // persistent solver may carry the hard flag from a prior
                // lazy-arm fallback, so it is re-stamped every round either
                // way). Relevancy-hard is inert without the branching enable
                // (`relevancy_should_engage` checks `relevancy_branching`
                // first), so the hard flag forces branching on.
                let _islp_relevancy_on = SatSolver::relevancy_env_override()
                    .unwrap_or(_islp_eager_relevancy_hard);
                solver.set_relevancy_branching(_islp_relevancy_on);
                solver.set_relevancy_hard(_islp_relevancy_on && _islp_eager_relevancy_hard);
                // #relevancy-lazy-routing: arm the wander-abort trip-wire for
                // hybrid arm routing (UFLIA). Re-armed each round so the
                // conflict/decision baselines snapshot the round start. A no-op
                // (disarm) for every lane that doesn't set the executor flag.
                solver.arm_wander_abort($self.split_eager_wander_abort);

                // Search-phase hint: defer expensive completeness passes (full
                // Dioph) to the post-SAT final check (TheorySolver::set_search_phase).
                ay_core::TheorySolver::set_search_phase(&mut theory, true);
                let (sat_result, _ext_conflicts, _, _ext_partial, pending_split, pending_refinements) =
                    pipeline_build_eager_extension!(
                        $self, solver, theory,
                        local_var_to_term, local_term_to_var,
                        active_theory_atoms, active_theory_atom_set,
                        proof_enabled, _islp_negations,
                        _islp_added_refinement_clauses, _islp_added_axioms,
                        _islp_eager_stats, _islp_timing, state,
                        should_stop: _islp_should_stop,
                        bound_axioms_pre_injected: _islp_ba_pre_injected,
                        bound_axiom_cache_key:
                            (_iteration == 0).then_some(_islp_ba_key)
                    );
                ay_core::TheorySolver::set_search_phase(&mut theory, false);
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
                    Some(ay_core::TheoryResult::NeedStringLemma(_islp_sl)) => {
                        $(
                            _islp_string_lemma_requests += 1;
                            if _islp_string_lemma_requests >= $max_slr {
                                $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                                $self.last_result = Some(SolveResult::Unknown);
                                $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L440"));
                                break 'split_loop Ok(SolveResult::Unknown);
                            }
                            // Strings NF-engine closure 3 (`AY_STR_NF=1`):
                            // drain any ADDITIONAL lemmas the theory queued
                            // behind this one and lower the whole batch in
                            // THIS iteration instead of one CEGAR round-trip
                            // per lemma. Always empty with the closure off, so
                            // the loop below runs exactly once — byte-identical.
                            let _islp_sl_extra =
                                ay_core::TheorySolver::take_pending_string_lemmas(&mut theory);
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            drop(theory);
                            let mut _islp_new_sl_clauses: Vec<Vec<TermId>> = Vec::new();
                            let mut _islp_sl_stall = false;
                            for _islp_sl_one in
                                std::iter::once(_islp_sl).chain(_islp_sl_extra.into_iter())
                            {
                                let $sl_lemma = _islp_sl_one;
                                let $sl_negations = &mut _islp_negations;
                                let (_islp_one_clauses, _islp_one_stall): (Vec<Vec<TermId>>, bool) =
                                    $sl_handler;
                                _islp_new_sl_clauses.extend(_islp_one_clauses);
                                if _islp_one_stall {
                                    _islp_sl_stall = true;
                                    break;
                                }
                            }
                            if _islp_sl_stall {
                                $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                                $self.last_result = Some(SolveResult::Unknown);
                                $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L454"));
                                break 'split_loop Ok(SolveResult::Unknown);
                            }
                            for _sl_clause in &_islp_new_sl_clauses {
                                let (_islp_lowered_sl_clause, _islp_sl_original_id) = $crate::executor::theories::split_incremental::apply_string_lemma_incremental(
                                    &$self.ctx.terms,
                                    solver,
                                    &mut local_term_to_var,
                                    &mut local_var_to_term,
                                    &mut local_next_var,
                                    &mut _islp_negations,
                                    _sl_clause,
                                );
                                if proof_enabled {
                                    // #8106: String lemma clauses from NeedStringLemma
                                    // are content axioms (decomposition, contains, substr).
                                    // Use StringContentAxiom instead of Generic/trust.
                                    let _ = $self.proof_tracker.add_theory_lemma_with_kind(
                                        _islp_lowered_sl_clause.clone(),
                                        ay_core::TheoryLemmaKind::StringContentAxiom,
                                    );
                                    if let Some(_islp_sl_original_id) = _islp_sl_original_id {
                                        $crate::pipeline_fns::place_original_clause_authority_at_id(
                                            &solver,
                                            _islp_sl_original_id,
                                            None,
                                            Some(ay_core::TheoryLemmaProof {
                                                clause: _islp_lowered_sl_clause,
                                                kind: ay_core::TheoryLemmaKind::StringContentAxiom,
                                                farkas: None,
                                                lia: None,
                                            }),
                                            &mut _islp_local_clausification_proofs,
                                            &mut _islp_local_original_clause_theory_proofs,
                                        );
                                    }
                                }
                            }
                            _islp_negations.sync_pending(&mut $self.ctx.terms);
                            _islp_string_lemma_clauses.extend(_islp_new_sl_clauses);
                            continue;
                        )?
                        #[allow(unreachable_code)]
                        {
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L491"));
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                    }
                    Some(ay_core::TheoryResult::NeedLemmas(lemmas)) => {
                        // #8594: Check if all lemma atoms are already encoded.
                        // In the non-persistent eager arm, a fresh theory each
                        // iteration may regenerate the same NeedLemmas that
                        // were already added in prior iterations. When all
                        // atoms are already mapped to SAT variables, the
                        // clauses are redundant and re-solving will produce
                        // the same model — continuing would loop until the
                        // no-progress cap. Instead, fall through to accept
                        $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager fallthrough-accept L508"));
                        // the SAT model.
                        let _nlm_all_known = lemmas.iter().all(|lemma| {
                            lemma.clause.iter().all(|lit| {
                                local_term_to_var.contains_key(&lit.term)
                            })
                        });
                        if _nlm_all_known {
                            // All atoms already encoded — skip redundant
                            // re-add and fall through. Theory stays alive
                            // for the SAT model handler's final check.
                            None
                        } else {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            drop(theory);
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
                                                    .expect("eager theory-lemma negation cache should be synced")
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
                    }
                    Some(ay_core::TheoryResult::NeedModelEquality(ref eq)) => {
                        // #8594: Pipeline-level dedup for model equality requests.
                        // The non-persistent eager arm recreates the theory each
                        // iteration, losing ArraySolver::requested_interface_eqs.
                        // Without this dedup, a fresh theory regenerates the same
                        // NeedModelEquality requests, cycling until no-progress cap.
                        let _meq_req_key = if eq.lhs.0 <= eq.rhs.0 {
                            (eq.lhs, eq.rhs)
                        } else {
                            (eq.rhs, eq.lhs)
                        };
                        if !_islp_seen_model_eq_requests.insert(_meq_req_key) {
                            // Already requested in a prior iteration — fall
                            // through to accept the SAT model.
                            None
                        } else {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            drop(theory);

                            // #8594: Only count a round if this equality atom is new.
                            let _meq_atom = $self.ctx.terms.mk_eq_coerce(eq.lhs, eq.rhs);
                            let _meq_is_new = !local_term_to_var.contains_key(&_meq_atom);
                            if _meq_is_new {
                                if _islp_model_eq_tracker.increment_round() {
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L604"));
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                            }

                            // #8596: Skip triangle axioms for pure ArrayEUF.
                            if _islp_skip_arith_triangle {
                                pipeline_encode_model_equality!(
                                    $self, solver, local_term_to_var, local_var_to_term,
                                    local_next_var, _islp_negations, eq, skip_arith_triangle: true
                                );
                            } else {
                                pipeline_encode_model_equality!(
                                    $self, solver, local_term_to_var, local_var_to_term,
                                    local_next_var, _islp_negations, eq
                                );
                            }
                            continue;
                        }
                    }
                    Some(ay_core::TheoryResult::NeedModelEqualities(eqs)) => {
                        // #8594: Pipeline-level dedup for batch model equalities.
                        let _meq_batch_has_new = eqs.iter().any(|eq| {
                            let key = if eq.lhs.0 <= eq.rhs.0 {
                                (eq.lhs, eq.rhs)
                            } else {
                                (eq.rhs, eq.lhs)
                            };
                            !_islp_seen_model_eq_requests.contains(&key)
                        });
                        if !_meq_batch_has_new {
                            // All already requested — fall through to accept model.
                            $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager fallthrough-accept L641"));
                            None
                        } else {
                            for eq in &eqs {
                                let key = if eq.lhs.0 <= eq.rhs.0 {
                                    (eq.lhs, eq.rhs)
                                } else {
                                    (eq.rhs, eq.lhs)
                                };
                                _islp_seen_model_eq_requests.insert(key);
                            }
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            drop(theory);

                            // #8594: Only count a round if at least one atom is new.
                            let _meq_has_new = eqs.iter().any(|eq| {
                                let atom = $self.ctx.terms.mk_eq_coerce(eq.lhs, eq.rhs);
                                !local_term_to_var.contains_key(&atom)
                            });
                            if _meq_has_new {
                                if _islp_model_eq_tracker.increment_round() {
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L660"));
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                            }

                            for eq in eqs {
                                // #8596: Skip triangle axioms for pure ArrayEUF.
                                if _islp_skip_arith_triangle {
                                    pipeline_encode_model_equality!(
                                        $self, solver, local_term_to_var, local_var_to_term,
                                        local_next_var, _islp_negations, eq, skip_arith_triangle: true
                                    );
                                } else {
                                    pipeline_encode_model_equality!(
                                        $self, solver, local_term_to_var, local_var_to_term,
                                        local_next_var, _islp_negations, eq
                                    );
                                }
                            }
                            continue;
                        }
                    }
                    other => other,
                };

                match sat_result {
                    SatResult::Sat(model) => {
                        // Diagnostic-only (--debug-no-terms): dump the SAT view of
                        // listed atoms at every SAT-accept: var mapping + model value
                        // + whether the var was ASSIGNED on the trail (vs defaulted).
                        if let Some(list) = ay_core::misc_cli_flags().debug_no_terms.as_deref() {
                            for raw in list.split(',') {
                                let Ok(id) = raw.trim().parse::<u32>() else { continue };
                                let t = ay_core::TermId(id);
                                let var = local_term_to_var.get(&t).copied();
                                let mv = var.and_then(|v| model.get(v as usize)).copied();
                                safe_eprintln!(
                                    "[sat-accept] T{} var={:?} model={:?}",
                                    id, var, mv,
                                );
                            }
                        }
                        // Soundness guard: escalate SAT→Unknown when theory
                        // conflicts were dropped (parity with solve_eager_step).
                        if _ext_partial > 0 {
                            tracing::warn!(
                                partial_clauses = _ext_partial,
                                concat!("Eager ", $tag, " produced SAT with dropped theory conflicts; escalating to Unknown")
                            );
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L695"));
                            break 'split_loop Ok(SolveResult::Unknown);
                        }

                        // Final full-check for combined theories (#5462 Packet 3).
                        // BCP-time check was local-only; run the full fixpoint
                        // once on the candidate model before accepting SAT.
                        //
                        // Skip when the extension already ran the full check and
                        // captured a pending split — the extension's check() already
                        // invoked theory.check() and the result is in pending_split.
                        // Running check() again would operate on modified state.
                        //
                        // Inc5 #fused-detour Q2 (brief open question 2:
                        // frontier-empty exit × extension final check): under
                        // relevancy-HARD the extension lane suppresses
                        // `suggest_decision` (theory_backend.rs USE_CALLBACK
                        // decide branch) and decisions route through
                        // `pick_relevancy_frontier_decision`; an EMPTY CNF
                        // frontier returns no decision, which lands in the
                        // CDCL loop's complete-assignment branch and routes
                        // through the extension's `check_model` →
                        // `TheoryExtension::check` — the SAME full theory
                        // final check as any complete-assignment SAT, over the
                        // TRAIL-asserted atoms only. Don't-care atoms were
                        // never asserted to the theory (a strictly weaker
                        // obligation set), so there is no spurious-escalation
                        // path: split-type results are parked in
                        // `pending_split` with Sat returned (the normal
                        // protocol, handled below), and this gate's
                        // pending_split-aware skip behaves identically at a
                        // frontier-empty accept. Completion-model source
                        // (brief's confirm item): the SAT-level accept
                        // completes don't-cares via `get_model` (vals;
                        // unassigned ⇒ false) — `relevancy_completed_model`'s
                        // phase completion is wired only into the lazy arm's
                        // assumption path (finalize_sat.rs) — and a
                        // false-completed don't-care theory atom is re-checked
                        // by the unchanged model-validation gates: worst case
                        // `unknown`, never wrong-sat.
                        if ay_core::TheorySolver::needs_final_check_after_sat(&theory)
                            && pending_split.is_none()
                        {
                            let _fc_result = ay_core::TheorySolver::check(&mut theory);
                            match _fc_result {
                                ay_core::TheoryResult::Sat => {
                                    // Full check passed — fall through to existing
                                    // pending_split / refinements / model extraction.
                                }
                                ay_core::TheoryResult::NeedSplit(_)
                                | ay_core::TheoryResult::NeedDisequalitySplit(_)
                                | ay_core::TheoryResult::NeedExpressionSplit(_)
                                | ay_core::TheoryResult::NeedExpressionSplits(_) => {
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    // #8762: drain batched disequality splits while
                                    // theory is still accessible.
                                    let _drained_diseq_extras =
                                        <_ as ay_core::TheorySolver>::drain_pending_diseq_splits(&mut theory);
                                    pipeline_incremental_split_eager_dispatch_split!(
                                        'split_loop, $self, solver,
                                        tag: $tag, suffix: "-INC-EAGER-FC",
                                        local_term_to_var, local_var_to_term, local_next_var, _islp_negations,
                                        _islp_added_split_clauses, _islp_last_split_values,
                                        split_result: _fc_result,
                                        drained_diseq_extras: _drained_diseq_extras,
                                        fallthrough: {
                                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                            $self.last_result = Some(SolveResult::Unknown);
                                            $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L737"));
                                            break 'split_loop Ok(SolveResult::Unknown);
                                        }
                                    );
                                }
                                ay_core::TheoryResult::NeedModelEquality(eq) => {
                                    // #8594: Pipeline-level dedup using raw TermId
                                    // pairs. The fresh theory loses its internal
                                    // requested_interface_eqs set; this pipeline-
                                    // level set persists across iterations.
                                    let _fc_meq_key = if eq.lhs.0 <= eq.rhs.0 {
                                        (eq.lhs, eq.rhs)
                                    } else {
                                        (eq.rhs, eq.lhs)
                                    };
                                    if _islp_seen_model_eq_requests.insert(_fc_meq_key) {
                                        // New request — encode and continue.
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        drop(theory);
                                        // #8594: Only count round if atom is new.
                                        let _meq_atom = $self.ctx.terms.mk_eq_coerce(eq.lhs, eq.rhs);
                                        let _meq_is_new = !local_term_to_var.contains_key(&_meq_atom);
                                        if _meq_is_new {
                                            if _islp_model_eq_tracker.increment_round() {
                                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                                $self.last_result = Some(SolveResult::Unknown);
                                                $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L765"));
                                                break 'split_loop Ok(SolveResult::Unknown);
                                            }
                                        }
                                        // #8596: Skip triangle axioms for pure ArrayEUF.
                                        if _islp_skip_arith_triangle {
                                            pipeline_encode_model_equality!(
                                                $self, solver, local_term_to_var, local_var_to_term,
                                                local_next_var, _islp_negations, eq, skip_arith_triangle: true
                                            );
                                        } else {
                                            pipeline_encode_model_equality!(
                                                $self, solver, local_term_to_var, local_var_to_term,
                                                local_next_var, _islp_negations, eq
                                            );
                                        }
                                        continue;
                                    }
                                    // Already requested — fall through to accept model.
                                    $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager fallthrough-accept L793"));
                                }
                                ay_core::TheoryResult::NeedModelEqualities(eqs) => {
                                    // #8594: Pipeline-level dedup.
                                    let _fc_meqs_has_new = eqs.iter().any(|eq| {
                                        let key = if eq.lhs.0 <= eq.rhs.0 {
                                            (eq.lhs, eq.rhs)
                                        } else {
                                            (eq.rhs, eq.lhs)
                                        };
                                        !_islp_seen_model_eq_requests.contains(&key)
                                    });
                                    if _fc_meqs_has_new {
                                        // At least one new request — encode all and continue.
                                        for eq in &eqs {
                                            let key = if eq.lhs.0 <= eq.rhs.0 {
                                                (eq.lhs, eq.rhs)
                                            } else {
                                                (eq.rhs, eq.lhs)
                                            };
                                            _islp_seen_model_eq_requests.insert(key);
                                        }
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        drop(theory);
                                        // #8594: Only count round if at least one atom is new.
                                        let _meq_has_new = eqs.iter().any(|eq| {
                                            let atom = $self.ctx.terms.mk_eq_coerce(eq.lhs, eq.rhs);
                                            !local_term_to_var.contains_key(&atom)
                                        });
                                        if _meq_has_new {
                                            if _islp_model_eq_tracker.increment_round() {
                                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                                $self.last_result = Some(SolveResult::Unknown);
                                                $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L818"));
                                                break 'split_loop Ok(SolveResult::Unknown);
                                            }
                                        }
                                        for eq in eqs {
                                            // #8596: Skip triangle axioms for pure ArrayEUF.
                                            if _islp_skip_arith_triangle {
                                                pipeline_encode_model_equality!(
                                                    $self, solver, local_term_to_var, local_var_to_term,
                                                    local_next_var, _islp_negations, eq, skip_arith_triangle: true
                                                );
                                            } else {
                                                pipeline_encode_model_equality!(
                                                    $self, solver, local_term_to_var, local_var_to_term,
                                                    local_next_var, _islp_negations, eq
                                                );
                                            }
                                        }
                                        continue;
                                    }
                                    // All already requested — fall through to accept model.
                                    $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager fallthrough-accept L849"));
                                }
                                ay_core::TheoryResult::NeedLemmas(lemmas) => {
                                    // #8594: Check if all lemma atoms are already
                                    // encoded. If so, the clauses are redundant
                                    // duplicates from a fresh theory.
                                    let _fc_nlm_all_known = lemmas.iter().all(|lemma| {
                                        lemma.clause.iter().all(|lit| {
                                            local_term_to_var.contains_key(&lit.term)
                                        })
                                    });
                                    if !_fc_nlm_all_known {
                                        // New atoms — replay into SAT solver and continue.
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        drop(theory);
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
                                                                .expect("final-check theory-lemma negation cache should be synced")
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
                                    // All atoms already known — fall through to
                                    // accept model.
                                }
                                _ => {
                                    // Unsat/UnsatWithFarkas/Unknown/NeedStringLemma:
                                    // conservative escalation to Unknown.
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L916"));
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                            }
                        }

                        if let Some(split_result) = pending_split {
                            // #8596: The extension's check() may return NeedModelEquality,
                            // NeedModelEqualities, or NeedLemmas which are stored in
                            // pending_split. These are NOT handled by the dispatch_split
                            // macro (which only handles NeedSplit/NeedDisequalitySplit/
                            // NeedExpressionSplit). Handle them here, mirroring the
                            // final-check path above.
                            match split_result {
                                ay_core::TheoryResult::NeedModelEquality(eq) => {
                                    let _ps_meq_key = if eq.lhs.0 <= eq.rhs.0 {
                                        (eq.lhs, eq.rhs)
                                    } else {
                                        (eq.rhs, eq.lhs)
                                    };
                                    if _islp_seen_model_eq_requests.insert(_ps_meq_key) {
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        drop(theory);
                                        let _meq_atom = $self.ctx.terms.mk_eq_coerce(eq.lhs, eq.rhs);
                                        let _meq_is_new = !local_term_to_var.contains_key(&_meq_atom);
                                        if _meq_is_new {
                                            if _islp_model_eq_tracker.increment_round() {
                                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                                $self.last_result = Some(SolveResult::Unknown);
                                                $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L947"));
                                                break 'split_loop Ok(SolveResult::Unknown);
                                            }
                                        }
                                        if _islp_skip_arith_triangle {
                                            pipeline_encode_model_equality!(
                                                $self, solver, local_term_to_var, local_var_to_term,
                                                local_next_var, _islp_negations, eq, skip_arith_triangle: true
                                            );
                                        } else {
                                            pipeline_encode_model_equality!(
                                                $self, solver, local_term_to_var, local_var_to_term,
                                                local_next_var, _islp_negations, eq
                                            );
                                        }
                                        continue;
                                    }
                                    // Already requested — fall through to accept model.
                                    $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager fallthrough-accept L977"));
                                }
                                ay_core::TheoryResult::NeedModelEqualities(eqs) => {
                                    let _ps_meqs_has_new = eqs.iter().any(|eq| {
                                        let key = if eq.lhs.0 <= eq.rhs.0 {
                                            (eq.lhs, eq.rhs)
                                        } else {
                                            (eq.rhs, eq.lhs)
                                        };
                                        !_islp_seen_model_eq_requests.contains(&key)
                                    });
                                    if _ps_meqs_has_new {
                                        for eq in &eqs {
                                            let key = if eq.lhs.0 <= eq.rhs.0 {
                                                (eq.lhs, eq.rhs)
                                            } else {
                                                (eq.rhs, eq.lhs)
                                            };
                                            _islp_seen_model_eq_requests.insert(key);
                                        }
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        drop(theory);
                                        let _meq_has_new = eqs.iter().any(|eq| {
                                            let atom = $self.ctx.terms.mk_eq_coerce(eq.lhs, eq.rhs);
                                            !local_term_to_var.contains_key(&atom)
                                        });
                                        if _meq_has_new {
                                            if _islp_model_eq_tracker.increment_round() {
                                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                                $self.last_result = Some(SolveResult::Unknown);
                                                $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L996"));
                                                break 'split_loop Ok(SolveResult::Unknown);
                                            }
                                        }
                                        for eq in eqs {
                                            if _islp_skip_arith_triangle {
                                                pipeline_encode_model_equality!(
                                                    $self, solver, local_term_to_var, local_var_to_term,
                                                    local_next_var, _islp_negations, eq, skip_arith_triangle: true
                                                );
                                            } else {
                                                pipeline_encode_model_equality!(
                                                    $self, solver, local_term_to_var, local_var_to_term,
                                                    local_next_var, _islp_negations, eq
                                                );
                                            }
                                        }
                                        continue;
                                    }
                                    // All already requested — fall through to accept model.
                                    $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager fallthrough-accept L1029"));
                                }
                                ay_core::TheoryResult::NeedLemmas(lemmas) => {
                                    let _ps_nlm_all_known = lemmas.iter().all(|lemma| {
                                        lemma.clause.iter().all(|lit| {
                                            local_term_to_var.contains_key(&lit.term)
                                        })
                                    });
                                    if !_ps_nlm_all_known {
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        drop(theory);
                                        let mut _ps_lemma_original_ids = Vec::with_capacity(lemmas.len());
                                        for lemma in &lemmas {
                                            _ps_lemma_original_ids.push($crate::executor::theories::split_incremental::apply_theory_lemma_incremental(
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
                                            for (lemma, _ps_original_id) in
                                                lemmas.iter().zip(_ps_lemma_original_ids)
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
                                                                .expect("pending-split theory-lemma negation cache should be synced")
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
                                                if let Some(_ps_original_id) = _ps_original_id {
                                                    $crate::pipeline_fns::place_original_clause_authority_at_id(
                                                        &solver,
                                                        _ps_original_id,
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
                                    // All atoms already known — fall through to accept model.
                                    $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager fallthrough-accept L1096"));
                                }
                                _ => {
                                    // NeedSplit/NeedDisequalitySplit/NeedExpressionSplit:
                                    // handled by the dispatch_split macro.
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    // #8762: drain batched disequality splits while
                                    // theory is still accessible.
                                    let _drained_diseq_extras =
                                        <_ as ay_core::TheorySolver>::drain_pending_diseq_splits(&mut theory);

                                    pipeline_incremental_split_eager_dispatch_split!(
                                        'split_loop, $self, solver,
                                        tag: $tag, suffix: "-INC-EAGER",
                                        local_term_to_var, local_var_to_term, local_next_var, _islp_negations,
                                        _islp_added_split_clauses, _islp_last_split_values,
                                        split_result: split_result,
                                        drained_diseq_extras: _drained_diseq_extras,
                                        fallthrough: {
                                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                            $self.last_result = Some(SolveResult::Unknown);
                                            $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L1105"));
                                            break 'split_loop Ok(SolveResult::Unknown);
                                        }
                                    );
                                }
                            }
                        }

                        if !pending_refinements.is_empty() {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );

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
                                $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L1130"));
                                break 'split_loop Ok(SolveResult::Unknown);
                            }

                            continue;
                        }

                        // No pending split — theory is SAT. Extract model.
                        pipeline_store_sat_model!(
                            'split_loop, $self, solver, model,
                            local_term_to_var, local_var_to_term, local_next_var,
                            _islp_timing, theory, $theory_var, $extract,
                            pre_store: {}
                        );
                    }
                    SatResult::Unsat(_) => {
                        // Strings NF-engine closure 5 (`AY_STR_NF=1`): a
                        // propositional UNSAT reached after string lemma
                        // clauses were added is a PROOF when every such clause
                        // is universally valid (exact reduction axioms over
                        // fresh skolems + tautological splits — classified at
                        // the single lowering chokepoint) and no distrusted
                        // NF-dependent string conflict was ever turned into a
                        // clause (`check_during_propagate` gate, plus the
                        // adapter's `check()` gate). Under those two
                        // conditions every clause in the solver is a
                        // consequence of the original formula, so UNSAT of the
                        // augmented set is UNSAT of the original. The
                        // remaining guards below (`_ext_partial`, the
                        // split-clause / verify-before-accept backstop) still
                        // apply — this only removes the blanket downgrade.
                        let _islp_sl_unsat_trustworthy =
                            ay_strings::str_nf_closure_enabled(5)
                                && $self.string_lemma_kinds_all_valid;
                        if !_islp_string_lemma_clauses.is_empty() && !_islp_sl_unsat_trustworthy {
                            $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                            $self.last_result = Some(SolveResult::Unknown);
                            $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L1148"));
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                        // #6812: Soundness guard — when theory conflicts had terms
                        // that couldn't map to SAT literals (partial clauses), the
                        // learned clauses are stronger than what the theory proved.
                        // A propositional UNSAT derived from such clauses is unsound.
                        if _ext_partial > 0 {
                            tracing::warn!(
                                partial_clauses = _ext_partial,
                                concat!("Eager ", $tag, " produced UNSAT with dropped theory conflicts; escalating to Unknown")
                            );
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L1161"));
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                        // #6812: Soundness guard — in the non-persistent eager
                        // arm, theory conflicts from the extension persist as
                        // learned SAT clauses. A fresh theory in a later iteration
                        // may be inconsistent with these stale learned conflicts,
                        // causing false-UNSAT. By default, escalate to Unknown
                        // when split clauses exist to prevent this.
                        //
                        // #6846: Callers that use tautological expression splits
                        // (e.g., AUFLIA with model equalities) can opt into
                        // accepting UNSAT after splits via accept_unsat_after_splits.
                        // In those logics, the split clauses are tautological and
                        // cannot cause false-UNSAT.
                        //
                        // Inc5 #fused-detour Q4 (brief open question 4:
                        // cross-arm stale-clause false-UNSAT vector): the fused
                        // arm runs this macro on a SHARED persistent solver
                        // PRE-LOADED by eager1 and the lazy detour. Their split
                        // clauses are invisible to THIS expansion's fresh
                        // `_islp_added_split_clauses` dedup set, so a
                        // propositional UNSAT with an empty LOCAL set could
                        // still lean on prior-arm split clauses. The fused arm
                        // therefore ALWAYS routes UNSAT through the
                        // verify-before-accept backstop below
                        // (`verify_unsat_after_splits`: fresh isolated
                        // re-derivation from the ORIGINAL assertions, accept
                        // only on an explicit fresh Unsat — the stale-clause
                        // backstop; do NOT weaken it). Non-fused attempts
                        // (`_islp_eager_relevancy_hard == false`) keep the
                        // exact historical guard — byte-identical flags-off.
                        if !_islp_added_split_clauses.is_empty() || _islp_eager_relevancy_hard {
                            // #6846: tautological-split opt-in (unverified). Accepts
                            // the post-split UNSAT directly because the split clauses
                            // are integer tautologies (plain-LIA, #8727).
                            let mut _accept = false;
                            $(_accept = $accept_unsat;)?
                            // #6812 sound relaxation: verify-before-accept opt-in.
                            // Strictly stronger than `accept_unsat_after_splits`: on a
                            // post-split UNSAT, re-derive UNSAT of the ORIGINAL
                            // assertions (invariant (a): no learned/split clauses) on a
                            // FRESH, isolated solve (invariant (b)) and accept ONLY on
                            // an explicit fresh Unsat. Non-optimistic: anything else
                            // (Sat / Unknown / verifier failure) => escalate.
                            let _verify = false;
                            $(let _verify = $verify_unsat;)?
                            // #6812: when this solve IS the fresh re-derivation of a
                            // post-split UNSAT core (post_split_verify_depth > 0), the
                            // incremental state is brand-new — no stale learned theory
                            // conflicts. The only remaining clauses are tautological
                            // split clauses (§2), so accept the post-split UNSAT
                            // directly instead of recursing into another verify pass.
                            if $self.post_split_verify_depth > 0 {
                                _accept = true;
                            }
                            let mut _accept_via_verify = false;
                            if !_accept && _verify {
                                // Guard (design §4d V4): disable verify-accept under a
                                // non-zero incremental scope (push/pop). The fresh
                                // re-derivation solves the core flat at scope depth 0;
                                // under genuine incremental we cannot guarantee the
                                // core reflects only currently-active assertions, so
                                // keep the conservative escalate (matches today).
                                let _islp_scope_depth = $self
                                    .incr_theory_state
                                    .as_ref()
                                    .map_or(0, |st| st.scope_depth);
                                if _islp_scope_depth == 0 {
                                    // Invariant (a): the verification core is built ONLY
                                    // from the ORIGINAL assertion terms
                                    // ($self.ctx.assertions == the preprocessed
                                    // assertions inside with_deferred_postprocessing;
                                    // learned and split clauses are NOT in this set).
                                    // The fresh isolated solve re-clausifies and
                                    // re-derives UNSAT with no shared learned state.
                                    let _islp_core: Vec<TermId> =
                                        $self.ctx.assertions.clone();
                                    _accept_via_verify = $self
                                        .verify_post_split_unsat_via_fresh_solve(&_islp_core);
                                }
                            }
                            if !_accept && !_accept_via_verify {
                                tracing::warn!(
                                    split_clauses = _islp_added_split_clauses.len(),
                                    verify_attempted = _verify,
                                    concat!("Eager ", $tag, " UNSAT after expression splits; escalating to Unknown")
                                );
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L1233"));
                                break 'split_loop Ok(SolveResult::Unknown);
                            }
                            tracing::debug!(
                                split_clauses = _islp_added_split_clauses.len(),
                                verified = _accept_via_verify,
                                concat!("Eager ", $tag, " UNSAT after expression splits (accepted via opt-in)")
                            );
                        }
                        // NOTE: The rescued #8596 patch had a soundness guard here
                        // that escalated UNSAT to Unknown after model equality encoding.
                        // This is removed because the root cause was in row2_down_clause_terms
                        // not accepting EUF-equivalent array/store pairs, causing missing
                        // ROW2 lemmas. With that fix, UNSAT after model equality encoding
                        // is genuine and should be accepted.
                        _islp_negations.sync_pending(&mut $self.ctx.terms);
                        pipeline_incremental_split_eager_build_unsat_proof!(
                            'split_loop, $self, solver, state,
                            local_var_to_term, _islp_negations, proof_enabled,
                            _islp_local_clausification_proofs, _islp_local_original_clause_theory_proofs
                        );
                    }
                    SatResult::Unknown => {
                        // #relevancy-lazy-routing: the wander-abort trip-wire
                        // fired — this eager attempt is WANDERING. Break out
                        // immediately (skipping pending-split refinement rounds,
                        // which would keep re-tripping) so the executor can
                        // re-route this check-sat to the lazy arm with relevancy.
                        // Sound: an aborted attempt only ever yields `unknown`.
                        if solver.wander_abort_tripped() {
                            $self.last_model = None;
                            if $self.last_unknown_reason.is_none() {
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            }
                            $self.last_result = Some(SolveResult::Unknown);
                            $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager wander-abort"));
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                        if ay_core::misc_cli_flags().debug_split_exit {
                            safe_eprintln!(
                                "[split-exit-probe] sat_unknown_reason={:?}",
                                solver.last_unknown_reason()
                            );
                            match &pending_split {
                                Some(ay_core::TheoryResult::NeedModelEquality(eq)) => {
                                    safe_eprintln!("[split-exit-probe] Unknown w/ NeedModelEquality {:?}={:?}", eq.lhs, eq.rhs);
                                }
                                Some(ay_core::TheoryResult::NeedModelEqualities(eqs)) => {
                                    for eq in eqs {
                                        safe_eprintln!("[split-exit-probe] Unknown w/ NeedModelEqualities {:?}={:?}", eq.lhs, eq.rhs);
                                    }
                                }
                                other => {
                                    safe_eprintln!("[split-exit-probe] Unknown w/ pending_split={:?}", other.as_ref().map(std::mem::discriminant));
                                }
                            }
                        }
                        if let Some(split_result) = pending_split {
                            // #8596: Handle NeedModelEquality/NeedModelEqualities/
                            // NeedLemmas from extension pending_split (same as Sat path).
                            match split_result {
                                ay_core::TheoryResult::NeedModelEquality(eq) => {
                                    let _unk_meq_key = if eq.lhs.0 <= eq.rhs.0 {
                                        (eq.lhs, eq.rhs)
                                    } else {
                                        (eq.rhs, eq.lhs)
                                    };
                                    if _islp_seen_model_eq_requests.insert(_unk_meq_key) {
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        drop(theory);
                                        let _meq_atom = $self.ctx.terms.mk_eq_coerce(eq.lhs, eq.rhs);
                                        let _meq_is_new = !local_term_to_var.contains_key(&_meq_atom);
                                        if _meq_is_new {
                                            if _islp_model_eq_tracker.increment_round() {
                                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                                $self.last_result = Some(SolveResult::Unknown);
                                                $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L1277"));
                                                break 'split_loop Ok(SolveResult::Unknown);
                                            }
                                        }
                                        if _islp_skip_arith_triangle {
                                            pipeline_encode_model_equality!(
                                                $self, solver, local_term_to_var, local_var_to_term,
                                                local_next_var, _islp_negations, eq, skip_arith_triangle: true
                                            );
                                        } else {
                                            pipeline_encode_model_equality!(
                                                $self, solver, local_term_to_var, local_var_to_term,
                                                local_next_var, _islp_negations, eq
                                            );
                                        }
                                        continue;
                                    }
                                    // Already requested — fall through to Unknown.
                                }
                                ay_core::TheoryResult::NeedModelEqualities(eqs) => {
                                    let _unk_meqs_has_new = eqs.iter().any(|eq| {
                                        let key = if eq.lhs.0 <= eq.rhs.0 {
                                            (eq.lhs, eq.rhs)
                                        } else {
                                            (eq.rhs, eq.lhs)
                                        };
                                        !_islp_seen_model_eq_requests.contains(&key)
                                    });
                                    if _unk_meqs_has_new {
                                        for eq in &eqs {
                                            let key = if eq.lhs.0 <= eq.rhs.0 {
                                                (eq.lhs, eq.rhs)
                                            } else {
                                                (eq.rhs, eq.lhs)
                                            };
                                            _islp_seen_model_eq_requests.insert(key);
                                        }
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        drop(theory);
                                        let _meq_has_new = eqs.iter().any(|eq| {
                                            let atom = $self.ctx.terms.mk_eq_coerce(eq.lhs, eq.rhs);
                                            !local_term_to_var.contains_key(&atom)
                                        });
                                        if _meq_has_new {
                                            if _islp_model_eq_tracker.increment_round() {
                                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                                $self.last_result = Some(SolveResult::Unknown);
                                                $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L1326"));
                                                break 'split_loop Ok(SolveResult::Unknown);
                                            }
                                        }
                                        for eq in eqs {
                                            if _islp_skip_arith_triangle {
                                                pipeline_encode_model_equality!(
                                                    $self, solver, local_term_to_var, local_var_to_term,
                                                    local_next_var, _islp_negations, eq, skip_arith_triangle: true
                                                );
                                            } else {
                                                pipeline_encode_model_equality!(
                                                    $self, solver, local_term_to_var, local_var_to_term,
                                                    local_next_var, _islp_negations, eq
                                                );
                                            }
                                        }
                                        continue;
                                    }
                                    // All already requested — fall through to Unknown.
                                }
                                ay_core::TheoryResult::NeedLemmas(lemmas) => {
                                    let _unk_nlm_all_known = lemmas.iter().all(|lemma| {
                                        lemma.clause.iter().all(|lit| {
                                            local_term_to_var.contains_key(&lit.term)
                                        })
                                    });
                                    if !_unk_nlm_all_known {
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        drop(theory);
                                        let mut _unk_lemma_original_ids = Vec::with_capacity(lemmas.len());
                                        for lemma in &lemmas {
                                            _unk_lemma_original_ids.push($crate::executor::theories::split_incremental::apply_theory_lemma_incremental(
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
                                            let _c3_dt = $crate::theory_inference::dt_funnel_registry_data(&$self.ctx);
                                            for (lemma, _unk_original_id) in
                                                lemmas.iter().zip(_unk_lemma_original_ids)
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
                                                                .expect("unknown-recovery theory-lemma negation cache should be synced")
                                                        }
                                                    })
                                                    .collect();
                                                let (kind, terms) =
                                                    $crate::theory_inference::record_funnel_classified_lemma(
                                                        &mut $self.proof_tracker,
                                                        &$self.ctx.terms,
                                                        terms,
                                                        _c3_dt.as_ref(),
                                                    );
                                                if let Some(_unk_original_id) = _unk_original_id {
                                                    if !matches!(kind, ay_core::TheoryLemmaKind::Generic) {
                                                        $crate::pipeline_fns::place_original_clause_authority_at_id(
                                                            &solver,
                                                            _unk_original_id,
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
                                        }
                                        continue;
                                    }
                                    // All atoms already known — fall through to Unknown.
                                }
                                _ => {
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    // #8762: drain batched disequality splits while
                                    // theory is still accessible.
                                    let _drained_diseq_extras =
                                        <_ as ay_core::TheorySolver>::drain_pending_diseq_splits(&mut theory);

                                    pipeline_incremental_split_eager_dispatch_split!(
                                        'split_loop, $self, solver,
                                        tag: $tag, suffix: "-INC-EAGER",
                                        local_term_to_var, local_var_to_term, local_next_var, _islp_negations,
                                        _islp_added_split_clauses, _islp_last_split_values,
                                        split_result: split_result,
                                        drained_diseq_extras: _drained_diseq_extras,
                                        fallthrough: {}
                                    );
                                }
                            }
                        }

                        if !pending_refinements.is_empty() {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );

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
                                $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L1414"));
                                break 'split_loop Ok(SolveResult::Unknown);
                            }

                            continue;
                        }

                        $self.last_model = None;
                        if $self.last_unknown_reason.is_none() {
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        }
                        $self.last_result = Some(SolveResult::Unknown);
                        $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager L1425"));
                        break 'split_loop Ok(SolveResult::Unknown);
                    }
                    #[allow(unreachable_patterns)]
                    _ => unreachable!(),
                }
            }

            // Too many splits - return unknown
            if $self.last_unknown_reason.is_none() {
                $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
            }
            $self.last_result = Some(SolveResult::Unknown);
            $crate::pipeline_fns::debug_split_exit(concat!($tag, "-eager split-limit"));
            Ok(SolveResult::Unknown)
        };

        state.scratch_var_to_term = local_var_to_term;
        pipeline_split_epilogue!(
            $self, _islp_timing, _islp_total_start,
            _islp_last_theory_stats, _islp_result,
            eager: { pipeline_export_split_loop_eager_stats!($self, _islp_eager_stats); },
            restore: { $self.incr_theory_state = Some(state); }
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
        $(, disable_preprocess: $disable_preprocess:expr)?
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
        $(, accept_unsat_after_splits: $accept_unsat:expr)?
        $(, max_string_lemma_requests: $max_slr:expr,
           handle_string_lemma: |$sl_lemma:ident, $sl_negations:ident| $sl_handler:expr)?
    ) => {{
        pipeline_incremental_split_eager_arm!($self,
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
            $(, disable_preprocess: $disable_preprocess)?
            $(, pre_iter_check: |$pic_self| $pic_expr)?
            $(, accept_unsat_after_splits: $accept_unsat)?
            $(, max_string_lemma_requests: $max_slr,
               handle_string_lemma: |$sl_lemma, $sl_negations| $sl_handler)?
        )
    }};
}
