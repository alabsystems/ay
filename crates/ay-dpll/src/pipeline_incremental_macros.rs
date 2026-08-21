// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental theory pipeline macro (without splits).
//!
//! Split from `pipeline_macros.rs` (#6321). Contains
//! [`solve_incremental_theory_pipeline`] for incremental theory solving
//! that maintains a persistent SAT solver across check-sat calls.
//!
//! The split-loop variant is in [`pipeline_incremental_split_macros`].

/// Incremental theory solving pipeline macro.
///
/// Extracts the common incremental DPLL(T) loop pattern shared by
/// `solve_euf`, `solve_lra_incremental`, and similar methods.
/// The incremental path maintains a persistent SAT solver and TseitinState
/// across check-sat calls, using SAT scope selectors for correct scoping.
///
/// # Parameters
/// - `$self`: the Executor instance
/// - `tag`: string label for debug messages (e.g., "EUF", "LRA")
/// - `create_theory`: expression producing a fresh theory solver each DPLL(T) iteration
/// - `extract_models`: closure `|theory: &mut T| -> TheoryModels`
/// - `track_theory_stats`: bool — track round_trips/theory_conflicts and call
///   `collect_theory_stats!(incremental: ...)`
/// - `set_unknown_on_error`: bool — set `UnknownReason::Incomplete` on verification failures
macro_rules! solve_incremental_theory_pipeline {
    ($self:ident,
        tag: $tag:expr,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        track_theory_stats: $track_stats:expr,
        set_unknown_on_error: $set_unknown:expr
        $(, pre_sat_solve: |$sat_solver:ident, $ttv_ref:ident| $pre_sat_solve:expr)?
        $(, extra_active_atoms: $extra_atoms:expr)?
    ) => {{
#[cfg(not(kani))]
        // #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
#[cfg(kani)]
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
        use ay_core::{TermId, Tseitin, TseitinEncodedAssertion, TseitinResult};
        use ay_sat::{Literal as SatLiteral, SatResult, Variable as SatVariable};
        use $crate::executor_types::{SolveResult, UnknownReason};
        use $crate::incremental_state::{collect_active_theory_atoms_cached, IncrementalTheoryState};
        use $crate::verification::{
            log_conflict_debug, verify_theory_conflict, verify_theory_conflict_with_farkas,
            verify_theory_conflict_with_farkas_full,
        };
        use $crate::executor::theories::freeze_var_if_needed;
        use $crate::executor::theories::solve_harness::TheoryModels;

        let proof_enabled = $self.produce_proofs_enabled();
        // #dt-ground-conflict: datatype registries for the conflict-path
        // classifier, built once per pipeline run (None when the problem
        // declares no datatypes — zero cost outside DT logics).
        // Reuse the owned registry data across plain and Farkas conflict arms.
        // Recorder calls borrow a short-lived view of this owned data.
        let _itp_dt_registry_data = if proof_enabled {
            $crate::theory_inference::dt_funnel_registry_data(&$self.ctx)
        } else {
            None
        };
        let _itp_problem_assertions = if proof_enabled {
            $self.proof_problem_assertions()
        } else {
            Vec::new()
        };
        let random_seed = $self.current_random_seed();
        let should_record_random_seed = match $self.incr_theory_state.as_ref() {
            Some(state) => state.persistent_sat.is_none(),
            None => true,
        };
        if should_record_random_seed {
            $self.record_applied_sat_random_seed_for_test(random_seed);
        }

        // #8634: Build should_stop closure before borrowing incr_theory_state
        // so the SAT solver respects caller-set interrupt flags and deadlines.
        let _itp_should_stop = $self.make_should_stop();

        // Initialize or get incremental state
        let state = $self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);

        // #8304: Replay cached persistent lemmas back into theory_lemmas
        // after pop. The lemma cache retains lemmas across scope transitions
        // that the theory state may have lost (e.g., due to theory_lemma_keys
        // clear on pop). Only active when lemma_persistence is enabled.
        if $self.lemma_persistence && !$self.lemma_cache.is_empty() {
            for (lemma, scope) in $self.lemma_cache.replay_lemmas() {
                if *scope <= state.scope_depth
                    && !state.theory_lemma_keys.contains(&lemma.clause)
                {
                    state.theory_lemma_keys.insert(lemma.clause.clone());
                    state.theory_lemmas.push((lemma.clone(), *scope));
                }
            }
        }

        if $track_stats {
            collect_theory_stats!(incremental: $self, state);
        }

        pipeline_incremental_setup!(
            $self, state, proof_enabled, random_seed, $tag,
            sat_field: persistent_sat,
            tseitin_field: tseitin_state,
            encoded_field: encoded_assertions,
            activation_scope_field: assertion_activation_scope,
            solver_init: { state.apply_pending_pushes(); },
            out: (new_assertion_set, solver, tseitin, var_to_term, term_to_var, pending_activations)
        );

        // Save tseitin num_vars before consuming, then release &TermStore borrow
        let _itp_tseitin_num_vars = tseitin.num_vars();
        state.tseitin_state = tseitin.into_state();

        // Proof tracking setup: tracker, assumptions, negation map (#6705, #6735, #5814 Packet A)
        pipeline_register_proof_context!(
            $self,
            proof_enabled,
            $tag,
            problem_assertions: _itp_problem_assertions
        );
        let mut _itp_negations = $crate::incremental_proof_cache::IncrementalNegationCache::seed(
            &mut $self.ctx.terms,
            var_to_term.values().copied(),
            proof_enabled,
        );

        // Make maps mutable so NeedLemmas/NeedModelEquality can allocate new SAT variables
        let mut var_to_term = var_to_term;
        let mut term_to_var = term_to_var;
        // FAIL-CLOSED proof backfill (#verification-route), PROOF-CAPTURE ONLY: when this
        // incremental round re-activates a previously-encoded assertion ROOT
        // without encoding any new term-mapping, the per-round tseitin var_to_term
        // is empty, so SAT-proof reconstruction can't name the assertion root var
        // (its complementary unit clauses [+v]/[-v] are dropped) and falls back to
        // an unverified Trust step. `encoded_assertions` maps each assertion term ->
        // its root DIMACS lit; it is the SAME datum that emits the root activation
        // unit clause `[cnf_lit_to_sat(root_lit)]`, so mapping var->term from it is
        // the genuine encoder binding, never invented. Key 0-indexed via
        // `cnf_lit_to_sat(..).variable().index()` to match the local map (v-1 at
        // setup) and the SatProofManager consume side.
        // CRITICAL: this is a READ-ONLY list applied ONLY to the captured proof map
        // at the UNSAT stash below. It must NOT mutate the live var_to_term/
        // term_to_var, which are consumed DURING solving (NeedLemmas / conflict
        // mapping) — mutating them changes the SAT verdict.
        let _itp_proof_backfill: Vec<(u32, TermId)> = if proof_enabled {
            state
                .encoded_assertions
                .iter()
                .map(|(&_itp_assn_term, &_itp_root_lit)| {
                    (
                        crate::cnf_lit_to_sat(_itp_root_lit).variable().index() as u32,
                        _itp_assn_term,
                    )
                })
                .collect()
        } else {
            Vec::new()
        };
        // SOUNDNESS (push/pop var-collision): newly-allocated split / model-equality
        // atom variables must start past EVERY SAT variable already present —
        // including scope-selector variables allocated by `push()` in a non-base
        // scope, which `tseitin.num_vars()` does NOT count. If `_itp_next_var`
        // started at `_itp_tseitin_num_vars` while a selector occupied that
        // index, the freshly-encoded le/ge triangle atoms (or model-eq vars)
        // would ALIAS the scope selector. The triangle clause `(¬eq ∨ le)` then
        // becomes `(¬eq ∨ +selector)`; with the selector assumed false (scope
        // active) it forces `¬eq`, producing a spurious in-scope conflict (a
        // false UNSAT on a satisfiable conjunction).
        let mut _itp_next_var = _itp_tseitin_num_vars
            .max(u32::try_from(solver.total_num_vars()).expect("SAT solver vars fit u32"));
        let mut _itp_model_eq_tracker = $crate::executor::theories::split_incremental::ModelEqualityTracker::new(
            $crate::executor::theories::split_incremental::model_equality::MODEL_EQ_MAX_ROUNDS_NO_SPLIT,
        );

        state.persistent_sat = Some(solver);
        let solver = state
            .persistent_sat
            .as_mut()
            .expect(concat!("incremental ", $tag, " must store persistent SAT solver before solve"));
        $(
            let $sat_solver = &mut *solver;
            let $ttv_ref = &term_to_var;
            $pre_sat_solve;
        )?

        // Collect theory atoms in active assertions only. The global
        // Bool-UF-arg scan reuses the persistent high-water-mark cache so it
        // only examines terms appended since the previous check-sat (avoids the
        // O(N^2) incremental blowup). `solver` and `bool_uf_arg_cache` are
        // disjoint fields of `state`, so both can be borrowed here.
        let active_atoms = collect_active_theory_atoms_cached(
            &$self.ctx.terms,
            &$self.ctx.assertions,
            Some(&mut state.bool_uf_arg_cache),
        );
        // Extend with caller-supplied extra atoms (e.g., derived or_eq_lemma eq_terms)
        $(
            let active_atoms = {
                let mut _aa = active_atoms;
                for _ea_term in $extra_atoms {
                    _aa.insert(_ea_term);
                }
                _aa
            };
        )?
        for &term in &active_atoms {
            if let Some(&var) = term_to_var.get(&term) {
                freeze_var_if_needed(solver, SatVariable::new(var));
            }
        }
        // #6853: Apply deferred activations immediately (no private push in non-split path).
        pipeline_apply_pending_activations_immediate!(
            solver, pending_activations, proof_enabled, state
        );

        // Stash proof data for post-loop finalization (#6705).
        // We can't assign to $self fields inside the loop because solver/state
        // hold mutable borrows into $self.incr_theory_state.
        let mut _itp_proof_stash: Option<(
            Option<ay_sat::ClauseTrace>,
            HashMap<u32, TermId>,
            HashMap<TermId, TermId>,
            Vec<Option<ay_core::ClausificationProof>>,
            Vec<Option<ay_core::TheoryLemmaProof>>,
        )> = None;

        let mut _itp_refinement_count: u32 = 0;
        const _ITP_MAX_REFINEMENTS: u32 = 1_000_000;

        // Theory-guided phase hints (#8067): saved across refinement iterations
        // so the SAT solver uses LP-model-consistent polarity on each `solve()`.
        let mut _itp_saved_phase_hints: Vec<(u32, bool)> = Vec::new();

        // In incremental mode, compute reachable terms to filter dead-scope
        // theory responses (#6726). After pop, the TermStore still contains
        // terms from popped scopes. The theory combiner scans all terms and
        // may produce NeedLemmas/NeedModelEquality for dead terms.
        let _itp_reachable: Option<HashSet<TermId>> = if $self.incremental_mode {
            Some($crate::executor::theories::reachable_term_set(
                &$self.ctx.terms,
                &$self.ctx.assertions,
            ))
        } else {
            None
        };

        // Lazy DPLL(T) loop
        let _itp_result: $crate::executor_types::Result<SolveResult> = loop {
            _itp_refinement_count += 1;
            if _itp_refinement_count > _ITP_MAX_REFINEMENTS {
                tracing::warn!(
                    tag = $tag,
                    refinements = _itp_refinement_count,
                    "incremental pipeline: max theory refinements exceeded; returning Unknown"
                );
                $self.last_result = Some(SolveResult::Unknown);
                break Ok(SolveResult::Unknown);
            }
            // #8634: Check interrupt/deadline at top of each refinement iteration.
            if _itp_should_stop() {
                $self.last_unknown_reason = Some($crate::executor_types::UnknownReason::Interrupted);
                $self.last_result = Some(SolveResult::Unknown);
                break Ok(SolveResult::Unknown);
            }
            if $track_stats {
                state.round_trips += 1;
            }

            // #8067: Apply saved theory phase hints before SAT solve.
            for &(var_idx, phase) in &_itp_saved_phase_hints {
                solver.set_var_phase(SatVariable::new(var_idx), phase);
            }
            // #array-deadline-forward: forward the executor's live per-solve
            // deadline so inprocessing/L0-GC phases honor the caller's wall
            // budget (see the assume arm).
            solver.set_solve_deadline($self.solve_deadline.get());
            // Deterministic resource budgets: `:rlimit` conflict budget
            // (#8749) with the default ground-phase conflict + decision
            // allowances (#ground-determinism) when no explicit `:rlimit`
            // is set. Bound this refinement's SAT solve so ground CDCL work
            // terminates on a machine-independent count, not the wall clock.
            solver.set_conflict_budget(
                $crate::pipeline_fns::effective_conflict_allowance(
                    $self.resource_limit,
                    $self.ground_budget_enabled,
                )
                .map(|n| solver.num_conflicts().saturating_add(n)),
            );
            solver.set_decision_budget(
                $crate::pipeline_fns::effective_decision_allowance($self.decision_limit, $self.ground_budget_enabled)
                    .map(|n| solver.num_decisions().saturating_add(n)),
            );
            let sat_result = solver.solve_interruptible(&_itp_should_stop).into_inner();
            if let Some(r) = solver.last_unknown_reason() {
                $self.last_unknown_reason = Some($crate::executor::Executor::map_sat_unknown_reason(r));
            }

            collect_sat_stats!($self, solver);

            if $track_stats {
                collect_theory_stats!(incremental: $self, state);
            }

                match sat_result {
                    SatResult::Sat(model) => {
                        _itp_negations.sync_pending(&mut $self.ctx.terms);
                        let mut theory = $create_theory;
                        ay_core::TheorySolver::reset(&mut theory);

                    for (lemma, _scope) in &state.theory_lemmas {
                        ay_core::TheorySolver::note_applied_theory_lemma(
                            &mut theory,
                            &lemma.clause,
                        );
                    }

                    // Sync model to theory
                    for (var, term) in $crate::iter_var_to_term_sorted(&var_to_term) {
                        if $crate::is_theory_atom(&$self.ctx.terms, term)
                            && active_atoms.contains(&term)
                        {
                            let value = match model.get(var as usize).copied() {
                                Some(v) => v,
                                None => match solver.value(SatVariable::new(var)) {
                                    Some(v) => v,
                                    // Unassigned theory atom — skip rather than
                                    // defaulting to false (#6188).
                                    None => continue,
                                },
                            };
                            ay_core::TheorySolver::assert_literal(&mut theory, term, value);
                        }
                    }

                    let _itp_theory_result = ay_core::TheorySolver::check(&mut theory);

                    // #8067: Collect theory phase hints for the next SAT solve iteration.
                    _itp_saved_phase_hints.clear();
                    for (&term, &var_idx) in term_to_var.iter() {
                        if let Some(phase) = ay_core::TheorySolver::suggest_phase(&theory, term) {
                            _itp_saved_phase_hints.push((var_idx, phase));
                        }
                    }

                    // In incremental mode, filter dead-term NeedModelEquality responses
                    // (#6726). After pop(), the TermStore still has terms from popped
                    // scopes. The theory combiner (ArraySolver::populate_caches) scans
                    // all terms and may produce NeedModelEquality for dead terms.
                    // Treat these as SAT since the model is consistent for live terms.
                    let _itp_theory_result = match _itp_theory_result {
                        ay_core::TheoryResult::NeedModelEquality(ref eq)
                            if _itp_reachable
                                .as_ref()
                                .is_some_and(|r| !r.contains(&eq.lhs) || !r.contains(&eq.rhs)) =>
                        {
                            ay_core::TheoryResult::Sat
                        }
                        ay_core::TheoryResult::NeedModelEqualities(ref eqs)
                            if _itp_reachable.as_ref().is_some_and(|r| {
                                eqs.iter()
                                    .all(|eq| !r.contains(&eq.lhs) || !r.contains(&eq.rhs))
                            }) =>
                        {
                            ay_core::TheoryResult::Sat
                        }
                        other => other,
                    };
                    match _itp_theory_result {
                        ay_core::TheoryResult::Sat => {
                            let $theory_var = &mut theory;
                            let _itp_models = $extract;

                            let fake_result = TseitinResult::new(
                                vec![],
                                term_to_var
                                    .iter()
                                    .map(|(&t, &v)| (t, v + 1))
                                    .collect(),
                                var_to_term
                                    .iter()
                                    .map(|(&v, &t)| (v + 1, t))
                                    .collect(),
                                1,
                                _itp_tseitin_num_vars,
                            );
                            break $self.solve_and_store_model_with_theories(
                                SatResult::Sat(model),
                                &fake_result,
                                _itp_models,
                            );
                        }
                        ay_core::TheoryResult::Unsat(mut conflict_terms) => {
                            // #4666: exact-duplicate literals are a logical
                            // identity in a conflict (X ∨ X ≡ X in the learned
                            // clause) but structurally fail verification, forcing
                            // the slow semantic gate on every re-derivation of
                            // the identical conflict. Dedupe before verifying.
                            $crate::verification::dedup_conflict_literals(&mut conflict_terms);
                            log_conflict_debug(&conflict_terms, concat!("incremental ", $tag, " UNSAT"));
                            if let Err(e) = verify_theory_conflict(&conflict_terms) {
                                // Structural failure is diagnostic only: the
                                // fail-closed semantic gate below is the
                                // authoritative check.
                                tracing::warn!(
                                    error = %e,
                                    conflict_len = conflict_terms.len(),
                                    concat!("BUG(#4666): ", $tag, " conflict structural verification failed; deferring to fail-closed semantic gate")
                                );
                            }

                            // Fail-closed: a conflict that cannot be semantically
                            // verified must NOT be learned as a global clause. The
                            // former #8595 "using conflict anyway" arm laundered
                            // unverifiable theory conflicts into learned clauses,
                            // converting theory bugs into wrong UNSAT verdicts on
                            // satisfiable formulas. Verifiable-domain skips inside
                            // `verify_conflict_semantic` return Ok, so only genuine
                            // verification failures reach this bail (mirrors the
                            // lazy split loop in
                            // pipeline_incremental_split_lazy_shared_macros.rs).
                            if let Err(e) = $crate::verification::verify_conflict_semantic_memoized(
                                &mut $self.conflict_semantic_verify_memo,
                                &conflict_terms,
                                &$self.ctx.terms,
                                &$self.active_support_axioms,
                            ) {
                                tracing::error!(
                                    error = %e,
                                    conflict_len = conflict_terms.len(),
                                    conflict = ?conflict_terms,
                                    concat!("BUG(#6853): ", $tag, " conflict semantic verification failed; returning Unknown instead of learning unverified clause")
                                );
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                break Ok(SolveResult::Unknown);
                            }

                            let _itp_conflict_annotation = if proof_enabled {
                                // Record single theory lemma; proof-time
                                // decomposition in decompose_combined_real_conflict_lemmas
                                // handles EUF+LRA split (#6756 Packet 2).
                                dt_conflict_proof!(
                                    $self,
                                    _itp_negations,
                                    &conflict_terms,
                                    _itp_dt_registry_data
                                )
                            } else { None };

                            if $track_stats {
                                state.theory_conflicts = state.theory_conflicts.saturating_add(1);
                                collect_theory_stats!(incremental: $self, state);
                            }

                            pipeline_add_incremental_conflict_clause!(
                                $self,
                                state: state,
                                solver: solver,
                                term_to_var: term_to_var,
                                conflict_terms: conflict_terms,
                                tag: $tag,
                                set_unknown_on_error: $set_unknown,
                                unmapped_message: "incremental pipeline: theory conflict terms all failed to map; returning Unknown",
                                proof_enabled: proof_enabled,
                                theory_proof: _itp_conflict_annotation
                            );
                        }
                        ay_core::TheoryResult::UnsatWithFarkas(mut conflict) => {
                            // #4666: dedupe exact-duplicate literals, merging
                            // positional Farkas coefficients by sum (λ₁·c + λ₂·c
                            // = (λ₁+λ₂)·c) — logical identity, keeps the
                            // certificate aligned and verifiable.
                            $crate::verification::dedup_conflict_with_farkas(&mut conflict);
                            log_conflict_debug(
                                &conflict.literals,
                                concat!("incremental ", $tag, " UnsatWithFarkas"),
                            );
                            let mut _itp_farkas_proof_valid = conflict.farkas.is_some();
                            if let Err(e) = verify_theory_conflict_with_farkas(&conflict) {
                                if e.is_missing_annotation() {
                                    // Missing Farkas annotation (#6535): no certificate to
                                    // check. The conflict itself is still gated by the
                                    // fail-closed semantic backstop below.
                                    _itp_farkas_proof_valid = false;
                                    tracing::debug!(
                                        conflict_len = conflict.literals.len(),
                                        concat!($tag, " Farkas annotation missing; skipping proof cert, deferring to semantic backstop")
                                    );
                                } else {
                                    // Certificate downgrade: the Farkas certificate is
                                    // unusable, so drop it. The conflict itself is then
                                    // re-verified by the fail-closed semantic backstop
                                    // below — it is only learned if that verification
                                    // succeeds (no more fail-open "use anyway" path).
                                    _itp_farkas_proof_valid = false;
                                    tracing::warn!(
                                        error = %e,
                                        conflict_len = conflict.literals.len(),
                                        concat!("BUG(#4666): ", $tag, " Farkas structural verification failed; dropping certificate, deferring to semantic backstop")
                                    );
                                }
                            }
                            // Semantic Farkas verification. Runs in ALL builds
                            // (adversarial-review followup on #rank-4 increment 2;
                            // was debug-only per W16-5): a semantically verified
                            // certificate proves the conflict, covering this arm's
                            // UNSAT verdict.
                            let mut _itp_farkas_semantically_verified = false;
                            if _itp_farkas_proof_valid && conflict.farkas.is_some() {
                                match verify_theory_conflict_with_farkas_full(&conflict, &$self.ctx.terms)
                                {
                                    Ok(()) => _itp_farkas_semantically_verified = true,
                                    Err(e) => {
                                        // Certificate downgrade: semantically invalid
                                        // certificate. Drop it and defer to the
                                        // fail-closed semantic backstop below, which
                                        // only learns the conflict if it verifies.
                                        _itp_farkas_proof_valid = false;
                                        tracing::warn!(
                                            error = %e,
                                            conflict_len = conflict.literals.len(),
                                            concat!("BUG(#4666): ", $tag, " Farkas semantic verification failed; dropping certificate, deferring to semantic backstop")
                                        );
                                    }
                                }
                            }
                            // Release backstop: when the UNSAT verdict is NOT covered
                            // by a semantically verified certificate, run the same
                            // domain-aware semantic re-check the Unsat arm runs.
                            //
                            // Fail-closed: if that re-check also fails, the conflict
                            // has no verification at all — do not learn it (the former
                            // #8595 "using conflict without certificate" arms learned
                            // it unconditionally, laundering unverifiable conflicts
                            // into wrong UNSAT verdicts).
                            if !_itp_farkas_semantically_verified {
                                if let Err(e) = $crate::verification::verify_conflict_semantic_memoized(
                                    &mut $self.conflict_semantic_verify_memo,
                                    &conflict.literals,
                                    &$self.ctx.terms,
                                    &$self.active_support_axioms,
                                ) {
                                    tracing::error!(
                                        error = %e,
                                        conflict_len = conflict.literals.len(),
                                        conflict = ?conflict.literals,
                                        concat!("BUG(#6853): ", $tag, " Farkas conflict semantic verification failed; returning Unknown instead of learning unverified clause")
                                    );
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break Ok(SolveResult::Unknown);
                                }
                            }

                            let _itp_conflict_annotation = if proof_enabled && _itp_farkas_proof_valid {
                                dt_farkas_proof!($self, _itp_negations, &conflict, _itp_dt_registry_data)
                            } else if proof_enabled {
                                dt_conflict_proof!($self, _itp_negations, &conflict.literals, _itp_dt_registry_data)
                            } else { None };

                            if $track_stats {
                                state.theory_conflicts = state.theory_conflicts.saturating_add(1);
                                collect_theory_stats!(incremental: $self, state);
                            }

                            pipeline_add_incremental_conflict_clause!(
                                $self,
                                state: state,
                                solver: solver,
                                term_to_var: term_to_var,
                                conflict_terms: conflict.literals,
                                tag: $tag,
                                set_unknown_on_error: $set_unknown,
                                unmapped_message: "incremental pipeline: Farkas conflict terms all failed to map; returning Unknown",
                                proof_enabled: proof_enabled,
                                theory_proof: _itp_conflict_annotation
                            );
                        }
                        ay_core::TheoryResult::NeedLemmas(lemmas) => {
                            let mut any_new = false;
                            let mut new_lemmas = Vec::new();
                            for lemma in &lemmas {
                                if !state.theory_lemma_keys.insert(lemma.clause.clone()) {
                                    continue;
                                }
                                any_new = true;
                                let (recorded_in_trace, original_id) = $crate::executor::theories::split_incremental::apply_theory_lemma_incremental_persistent(
                                    solver,
                                    &mut term_to_var,
                                    &mut var_to_term,
                                    &mut _itp_negations,
                                    &lemma.clause,
                                );
                                ay_core::TheorySolver::note_applied_theory_lemma(
                                    &mut theory,
                                    &lemma.clause,
                                );
                                new_lemmas.push((lemma.clone(), recorded_in_trace, original_id));
                            }

                            if !any_new {
                                if $set_unknown {
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                }
                                $self.last_result = Some(SolveResult::Unknown);
                                break Ok(SolveResult::Unknown);
                            }

                            let _ = theory;

                            if proof_enabled {
                                _itp_negations.sync_pending(&mut $self.ctx.terms);
                                // #trust->0 C3: DT registries for the funnel,
                                // built once per lemma batch (None when the
                                // problem declares no datatypes).
                                let _c3_dt = $crate::theory_inference::dt_funnel_registry_data(&$self.ctx);
                                for (lemma, recorded_in_trace, original_id) in &new_lemmas {
                                    let terms: Vec<TermId> = lemma
                                        .clause
                                        .iter()
                                        .map(|lit| {
                                            if lit.value {
                                                lit.term
                                            } else {
                                                *_itp_negations
                                                    .as_map()
                                                    .get(&lit.term)
                                                    .expect("persistent theory-lemma negation cache should be synced")
                                            }
                                        })
                                        .collect();
                                    // #8106/#trust->0 C3: the central funnel
                                    // infers the kind (arith/array/string/FP/
                                    // regex/NRA + EUF/DT) and records; the
                                    // returned clause is the validator-accepted
                                    // order and MUST be the one annotated below.
                                    let (kind, terms) =
                                        $crate::theory_inference::record_funnel_classified_lemma(
                                            &mut $self.proof_tracker,
                                            &$self.ctx.terms,
                                            terms,
                                            _c3_dt.as_ref(),
                                        );
                                    if let Some(original_id) = *original_id {
                                        $crate::pipeline_fns::place_original_clause_authority_at_id(
                                            &solver,
                                            original_id,
                                            None,
                                            recorded_in_trace.then_some(ay_core::TheoryLemmaProof {
                                                clause: terms,
                                                kind,
                                                farkas: None,
                                                lia: None,
                                            }),
                                            &mut state.clausification_proofs,
                                            &mut state.original_clause_theory_proofs,
                                        );
                                    }
                                }
                            }
                            // Tag each lemma with the current scope depth so
                            // pop() can discard only lemmas from the popped
                            // scope while retaining lower-scope lemmas (#8157).
                            let lemma_depth = state.scope_depth;
                            // #8304: Also record into the executor's LemmaCache
                            // when lemma persistence is enabled, so lemmas
                            // survive pop and replay on the next path.
                            if $self.lemma_persistence {
                                for (lemma, _, _) in &new_lemmas {
                                    $self.lemma_cache.record_lemma(lemma.clone(), lemma_depth);
                                }
                            }
                            state.theory_lemmas.extend(
                                new_lemmas
                                    .into_iter()
                                    .map(|(lemma, _, _)| (lemma, lemma_depth)),
                            );
                            continue;
                        }
                        ay_core::TheoryResult::NeedModelEquality(eq) => {
                            // Encode the equality atom into the SAT solver so the
                            // next solve round can decide it. Dead-term requests
                            // are already filtered to Sat above (#6726).
                            //
                            // #6851: Use centralized ModelEqualityTracker for round
                            // budgeting. No per-pair abort -- the old `> 2` threshold
                            // caused false-SAT (#6846).
                            if _itp_model_eq_tracker.increment_round() {
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                break Ok(SolveResult::Unknown);
                            }
                            pipeline_encode_model_equality!(
                                $self, solver, term_to_var, var_to_term,
                                _itp_next_var, _itp_negations, eq
                            );
                            continue;
                        }
                        ay_core::TheoryResult::NeedModelEqualities(eqs) => {
                            // Dead-term requests are already filtered to Sat above (#6726).
                            //
                            // #6851: Use centralized ModelEqualityTracker for round
                            // budgeting. No per-pair abort.
                            if _itp_model_eq_tracker.increment_round() {
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                break Ok(SolveResult::Unknown);
                            }
                            for eq in &eqs {
                                pipeline_encode_model_equality!(
                                    $self, solver, term_to_var, var_to_term,
                                    _itp_next_var, _itp_negations, *eq
                                );
                            }
                            continue;
                        }
                        ay_core::TheoryResult::Unknown
                        | ay_core::TheoryResult::NeedSplit(_)
                        | ay_core::TheoryResult::NeedDisequalitySplit(_)
                        | ay_core::TheoryResult::NeedExpressionSplit(_)
                        // Plural variant (Real disequality `a != b` -> a<b | a>b)
                        // emitted on the LRA disequality-saturated lane; the
                        // singular sibling pipelines handle it explicitly, but
                        // this incremental path must at least fail closed to
                        // Unknown instead of hitting the unreachable!() below
                        // (deterministic SIGABRT on sally/oral_messages — see
                        // the development design notes F0).
                        | ay_core::TheoryResult::NeedExpressionSplits(_)
                        | ay_core::TheoryResult::NeedStringLemma(_) => {
                            $self.last_result = Some(SolveResult::Unknown);
                            break Ok(SolveResult::Unknown);
                        }
                            // All current TheoryResult variants are handled above.
                            // This arm is required by #[non_exhaustive] and catches future variants.
                            other => unreachable!("unhandled TheoryResult variant in incremental pipeline: {other:?}"),
                    }
                }
                SatResult::Unsat(_) => {
                    // Stash proof data for post-loop finalization (#6705)
                    if proof_enabled {
                        _itp_negations.sync_pending(&mut $self.ctx.terms);
                        $crate::pipeline_fns::drain_pending_original_clause_authorities(
                            &solver,
                            &mut _itp_negations,
                            &mut state.clausification_proofs,
                            &mut state.original_clause_theory_proofs,
                        );
                        let _itp_clause_trace = solver.snapshot_clause_trace();
                        $crate::pipeline_fns::align_original_clause_authority_ledgers(
                            &solver,
                            &mut state.clausification_proofs,
                            &mut state.original_clause_theory_proofs,
                        );
                        _itp_proof_stash = Some((
                            _itp_clause_trace,
                            {
                                // PROOF-CAPTURE ONLY: real per-round entries win;
                                // backfill (assertion-root var->term from
                                // encoded_assertions) fills the gap when a
                                // re-activated assertion root wasn't re-encoded this
                                // round. Does NOT touch the live solve maps.
                                let mut _itp_m = var_to_term.clone();
                                for &(_itp_bv, _itp_bt) in &_itp_proof_backfill {
                                    _itp_m.entry(_itp_bv).or_insert(_itp_bt);
                                }
                                _itp_m.iter().map(|(&v, &t)| (v, t)).collect()
                            },
                            _itp_negations.as_map().clone(),
                            state.clausification_proofs.clone(),
                            state.original_clause_theory_proofs.clone(),
                        ));
                    }
                    $self.last_model = None;
                    $self.last_result = Some(SolveResult::unsat());
                    break Ok(SolveResult::unsat());
                }
                SatResult::Unknown => {
                    $self.last_model = None;
                    if $self.last_unknown_reason.is_none() {
                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    }
                    $self.last_result = Some(SolveResult::Unknown);
                    break Ok(SolveResult::Unknown);
                }
                #[allow(unreachable_patterns)]
                _ => unreachable!(),
            }
        };

        // Finalize proof after loop exits (borrows on state/solver are released) (#6705)
        if let Some((_itp_ct, _itp_vtm, _itp_neg, _itp_cp, _itp_tp)) = _itp_proof_stash {
            $self.last_clause_trace = _itp_ct;
            $crate::pipeline_fns::record_var_map_provenance_trace(
                "incremental", _itp_vtm.len(), $self.last_clause_trace.as_ref());
            $self.last_var_to_term = Some(_itp_vtm);
            $self.last_negations = Some(_itp_neg);
            $self.last_clausification_proofs = Some(_itp_cp);
            $self.last_original_clause_theory_proofs = Some(_itp_tp);
            $self.build_unsat_proof();
        } else if matches!(_itp_result, Ok(ref r) if r.is_unsat()) && $self.produce_proofs_enabled() {
            // Fallback for trivially-unsat exits (e.g. empty conflict_terms in
            // pipeline_add_incremental_conflict_clause!) that bypass the SAT
            // solver and therefore never populate the proof stash. (#8154)
            $self.build_unsat_proof();
        }

        _itp_result
    }};

    // #2138: Persistent-theory variant. Theory created once before the
    // DPLL(T) loop and reused via soft_reset() across SAT model iterations.
    // Eliminates per-model theory allocation, full reset, and O(n) lemma replay.
    ($self:ident,
        tag: $tag:expr,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        track_theory_stats: $track_stats:expr,
        set_unknown_on_error: $set_unknown:expr,
        persistent_theory: true
        $(, pre_sat_solve: |$sat_solver:ident, $ttv_ref:ident| $pre_sat_solve:expr)?
        $(, extra_active_atoms: $extra_atoms:expr)?
    ) => {{
#[cfg(not(kani))]
        // #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
#[cfg(kani)]
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
        use ay_core::{TermId, Tseitin, TseitinEncodedAssertion, TseitinResult};
        use ay_sat::{Literal as SatLiteral, SatResult, Variable as SatVariable};
        use $crate::executor_types::{SolveResult, UnknownReason};
        use $crate::incremental_state::{collect_active_theory_atoms_cached, IncrementalTheoryState};
        use $crate::verification::{
            log_conflict_debug, verify_theory_conflict, verify_theory_conflict_with_farkas,
            verify_theory_conflict_with_farkas_full,
        };
        use $crate::executor::theories::freeze_var_if_needed;
        use $crate::executor::theories::solve_harness::TheoryModels;

        let proof_enabled = $self.produce_proofs_enabled();
        // #dt-ground-conflict: datatype registries for the conflict-path
        // classifier, built once per pipeline run (None when the problem
        // declares no datatypes — zero cost outside DT logics).
        // Reuse the owned registry data across plain and Farkas conflict arms.
        let _itp_dt_registry_data = if proof_enabled {
            $crate::theory_inference::dt_funnel_registry_data(&$self.ctx)
        } else {
            None
        };
        let _itp_problem_assertions = if proof_enabled {
            $self.proof_problem_assertions()
        } else {
            Vec::new()
        };
        let random_seed = $self.current_random_seed();
        let should_record_random_seed = match $self.incr_theory_state.as_ref() {
            Some(state) => state.persistent_sat.is_none(),
            None => true,
        };
        if should_record_random_seed {
            $self.record_applied_sat_random_seed_for_test(random_seed);
        }

        // #8634: Build should_stop closure before borrowing incr_theory_state
        // so the SAT solver respects caller-set interrupt flags and deadlines.
        let _itp_should_stop = $self.make_should_stop();

        let state = $self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);

        if $track_stats {
            collect_theory_stats!(incremental: $self, state);
        }

        pipeline_incremental_setup!(
            $self, state, proof_enabled, random_seed, $tag,
            sat_field: persistent_sat,
            tseitin_field: tseitin_state,
            encoded_field: encoded_assertions,
            activation_scope_field: assertion_activation_scope,
            solver_init: { state.apply_pending_pushes(); },
            out: (new_assertion_set, solver, tseitin, var_to_term, term_to_var, pending_activations)
        );

        let _itp_tseitin_num_vars = tseitin.num_vars();
        state.tseitin_state = tseitin.into_state();

        pipeline_register_proof_context!(
            $self, proof_enabled, $tag,
            problem_assertions: _itp_problem_assertions
        );
        let mut _itp_negations = $crate::incremental_proof_cache::IncrementalNegationCache::seed(
            &mut $self.ctx.terms,
            var_to_term.values().copied(),
            proof_enabled,
        );

        let mut var_to_term = var_to_term;
        let mut term_to_var = term_to_var;
        // FAIL-CLOSED proof backfill (#verification-route), PROOF-CAPTURE ONLY: mirror of the
        // non-persistent variant above. Read-only list of assertion-root var->term
        // from encoded_assertions, applied ONLY to the captured proof map at the
        // UNSAT stash; never mutates the live solve maps. Genuine encoder binding;
        // fail-closed (a still-unmapped var still drops to Trust).
        let _itp_proof_backfill: Vec<(u32, TermId)> = if proof_enabled {
            state
                .encoded_assertions
                .iter()
                .map(|(&_itp_assn_term, &_itp_root_lit)| {
                    (
                        crate::cnf_lit_to_sat(_itp_root_lit).variable().index() as u32,
                        _itp_assn_term,
                    )
                })
                .collect()
        } else {
            Vec::new()
        };
        // SOUNDNESS (push/pop var-collision): see the matching comment in the
        // non-persistent variant above. Start fresh split/model-eq atom vars
        // past scope-selector vars allocated by `push()` so they never alias a
        // selector and turn triangle/adapter clauses into selector constraints.
        let mut _itp_next_var = _itp_tseitin_num_vars
            .max(u32::try_from(solver.total_num_vars()).expect("SAT solver vars fit u32"));
        let mut _itp_model_eq_tracker = $crate::executor::theories::split_incremental::ModelEqualityTracker::new(
            $crate::executor::theories::split_incremental::model_equality::MODEL_EQ_MAX_ROUNDS_NO_SPLIT,
        );

        state.persistent_sat = Some(solver);
        let solver = state
            .persistent_sat
            .as_mut()
            .expect(concat!("incremental ", $tag, " must store persistent SAT solver before solve"));
        $(
            let $sat_solver = &mut *solver;
            let $ttv_ref = &term_to_var;
            $pre_sat_solve;
        )?

        let active_atoms = collect_active_theory_atoms_cached(
            &$self.ctx.terms,
            &$self.ctx.assertions,
            Some(&mut state.bool_uf_arg_cache),
        );
        $(
            let active_atoms = {
                let mut _aa = active_atoms;
                for _ea_term in $extra_atoms { _aa.insert(_ea_term); }
                _aa
            };
        )?
        for &term in &active_atoms {
            if let Some(&var) = term_to_var.get(&term) {
                freeze_var_if_needed(solver, SatVariable::new(var));
            }
        }
        pipeline_apply_pending_activations_immediate!(
            solver, pending_activations, proof_enabled, state
        );

        let mut _itp_proof_stash: Option<(
            Option<ay_sat::ClauseTrace>,
            HashMap<u32, TermId>,
            HashMap<TermId, TermId>,
            Vec<Option<ay_core::ClausificationProof>>,
            Vec<Option<ay_core::TheoryLemmaProof>>,
        )> = None;

        let mut _itp_refinement_count: u32 = 0;
        const _ITP_MAX_REFINEMENTS: u32 = 1_000_000;
        let mut _itp_saved_phase_hints: Vec<(u32, bool)> = Vec::new();

        let _itp_reachable: Option<HashSet<TermId>> = if $self.incremental_mode {
            Some($crate::executor::theories::reachable_term_set(
                &$self.ctx.terms, &$self.ctx.assertions,
            ))
        } else {
            None
        };

        // #2138: Create the persistent theory ONCE before the loop.
        // #warm-theory: when the warm lane is active (LRA only; false for every
        // other caller, so their path is byte-identical), reuse a theory solver
        // persisted ACROSS check-sats instead of rebuilding from scratch —
        // collapsing the O(accumulated) theory re-processing to O(delta). The
        // persisted solver's raw terms pointer is refreshed via set_terms; a
        // None/type-mismatch falls back to a fresh solver.
        let _itp_warm = $crate::warm_theory_flag::get();
        let (mut theory, _itp_theory_reused) = if _itp_warm {
            match state.persist_theory.take() {
                Some(_itp_boxed) => match _itp_boxed.downcast() {
                    Ok(_itp_t) => (*_itp_t, true),
                    Err(_) => ($create_theory, false),
                },
                None => ($create_theory, false),
            }
        } else {
            ($create_theory, false)
        };
        if _itp_theory_reused {
            // Reused warm solver: refresh the dangling terms pointer; do NOT
            // reset (that would clear the warm tableau/overlay we reuse).
            theory.set_terms(&$self.ctx.terms);
        } else {
            ay_core::TheorySolver::reset(&mut theory);
        }
        if _itp_warm && ay_core::misc_cli_flags().lra_warm_stats {
            eprintln!("c #warm-theory check reused={_itp_theory_reused}");
        }
        let mut _itp_replayed_lemma_count: usize = 0;

        let _itp_result: $crate::executor_types::Result<SolveResult> = loop {
            _itp_refinement_count += 1;
            if _itp_refinement_count > _ITP_MAX_REFINEMENTS {
                tracing::warn!(tag = $tag, refinements = _itp_refinement_count,
                    "incremental pipeline: max theory refinements exceeded; returning Unknown");
                $self.last_result = Some(SolveResult::Unknown);
                break Ok(SolveResult::Unknown);
            }
            // #8634: Check interrupt/deadline at top of each refinement iteration.
            if _itp_should_stop() {
                $self.last_unknown_reason = Some($crate::executor_types::UnknownReason::Interrupted);
                $self.last_result = Some(SolveResult::Unknown);
                break Ok(SolveResult::Unknown);
            }
            if $track_stats { state.round_trips += 1; }

            for &(var_idx, phase) in &_itp_saved_phase_hints {
                solver.set_var_phase(SatVariable::new(var_idx), phase);
            }
            // #array-deadline-forward: see the assume arm.
            solver.set_solve_deadline($self.solve_deadline.get());
            // Deterministic resource budgets (#8749 `:rlimit` +
            // #ground-determinism defaults), incremental arm.
            solver.set_conflict_budget(
                $crate::pipeline_fns::effective_conflict_allowance(
                    $self.resource_limit,
                    $self.ground_budget_enabled,
                )
                .map(|n| solver.num_conflicts().saturating_add(n)),
            );
            solver.set_decision_budget(
                $crate::pipeline_fns::effective_decision_allowance($self.decision_limit, $self.ground_budget_enabled)
                    .map(|n| solver.num_decisions().saturating_add(n)),
            );
            let sat_result = solver.solve_interruptible(&_itp_should_stop).into_inner();
            if let Some(r) = solver.last_unknown_reason() {
                $self.last_unknown_reason = Some($crate::executor::Executor::map_sat_unknown_reason(r));
            }
            collect_sat_stats!($self, solver);
            if $track_stats { collect_theory_stats!(incremental: $self, state); }

                match sat_result {
                    SatResult::Sat(model) => {
                        _itp_negations.sync_pending(&mut $self.ctx.terms);

                        // #2138: Set terms and soft-reset on subsequent iterations.
                        theory.set_terms(&$self.ctx.terms);
                        if _itp_refinement_count > 1 {
                            ay_core::TheorySolver::soft_reset(&mut theory);
                        }

                    // #2138: Incremental lemma replay.
                    for (lemma, _scope) in state.theory_lemmas.iter().skip(_itp_replayed_lemma_count) {
                        ay_core::TheorySolver::note_applied_theory_lemma(&mut theory, &lemma.clause);
                    }
                    _itp_replayed_lemma_count = state.theory_lemmas.len();

                    for (var, term) in $crate::iter_var_to_term_sorted(&var_to_term) {
                        if $crate::is_theory_atom(&$self.ctx.terms, term)
                            && active_atoms.contains(&term)
                        {
                            let value = match model.get(var as usize).copied() {
                                Some(v) => v,
                                None => match solver.value(SatVariable::new(var)) {
                                    Some(v) => v,
                                    None => continue,
                                },
                            };
                            ay_core::TheorySolver::assert_literal(&mut theory, term, value);
                        }
                    }

                    let _itp_theory_result = ay_core::TheorySolver::check(&mut theory);

                    _itp_saved_phase_hints.clear();
                    for (&term, &var_idx) in term_to_var.iter() {
                        if let Some(phase) = ay_core::TheorySolver::suggest_phase(&theory, term) {
                            _itp_saved_phase_hints.push((var_idx, phase));
                        }
                    }

                    let _itp_theory_result = match _itp_theory_result {
                        ay_core::TheoryResult::NeedModelEquality(ref eq)
                            if _itp_reachable.as_ref()
                                .is_some_and(|r| !r.contains(&eq.lhs) || !r.contains(&eq.rhs)) =>
                            { ay_core::TheoryResult::Sat }
                        ay_core::TheoryResult::NeedModelEqualities(ref eqs)
                            if _itp_reachable.as_ref().is_some_and(|r| {
                                eqs.iter().all(|eq| !r.contains(&eq.lhs) || !r.contains(&eq.rhs))
                            }) =>
                            { ay_core::TheoryResult::Sat }
                        // #7966 (persistent no-split arm): when EVERY requested
                        // model equality already has an encoded atom in the SAT
                        // solver (`term_to_var` carries its `(= lhs rhs)` var), the
                        // theory is re-discovering value-equalities that the SAT
                        // solver has already had the chance to decide. Re-encoding
                        // them adds no new clause (the atom var already exists), so
                        // the loop would otherwise spin re-requesting the same set
                        // and burn the model-equality round budget down to a false
                        // Unknown. The SAT model satisfies the boolean skeleton AND
                        // the theory raised no conflict, so the combined model is
                        // consistent — treat as Sat (the produced model is still
                        // independently re-validated by finalize_sat_model_validation
                        // against the ORIGINAL assertions, so a spurious model cannot
                        // escape as a wrong SAT). Mirrors the validated stale-eq
                        // filter in the eager-persistent split-loop arm. (The former
                        // AY_NO_STALE_MODELEQ_SAT kill switch that restored the old
                        // budget-cap path is removed; this filter is permanent.)
                        ay_core::TheoryResult::NeedModelEquality(ref eq)
                            if $self.ctx.terms.find_eq(eq.lhs, eq.rhs)
                                .is_some_and(|ea| term_to_var.contains_key(&ea)) =>
                            { ay_core::TheoryResult::Sat }
                        ay_core::TheoryResult::NeedModelEqualities(ref eqs)
                            if !eqs.is_empty()
                                && eqs.iter().all(|eq| {
                                    $self.ctx.terms.find_eq(eq.lhs, eq.rhs)
                                        .is_some_and(|ea| term_to_var.contains_key(&ea))
                                }) =>
                            { ay_core::TheoryResult::Sat }
                        other => other,
                    };
                    match _itp_theory_result {
                        ay_core::TheoryResult::Sat => {
                            let $theory_var = &mut theory;
                            let _itp_models = $extract;
                            theory.unset_terms();

                            let fake_result = TseitinResult::new(
                                vec![],
                                term_to_var.iter().map(|(&t, &v)| (t, v + 1)).collect(),
                                var_to_term.iter().map(|(&v, &t)| (v + 1, t)).collect(),
                                1, _itp_tseitin_num_vars,
                            );
                            break $self.solve_and_store_model_with_theories(
                                SatResult::Sat(model), &fake_result, _itp_models,
                            );
                        }
                        ay_core::TheoryResult::Unsat(mut conflict_terms) => {
                            theory.unset_terms();
                            // #4666: dedupe exact-duplicate literals (logical
                            // identity) so well-formed conflicts verify and learn.
                            $crate::verification::dedup_conflict_literals(&mut conflict_terms);
                            log_conflict_debug(&conflict_terms, concat!("incremental ", $tag, " UNSAT"));
                            if let Err(e) = verify_theory_conflict(&conflict_terms) {
                                // Structural failure is diagnostic only: the fail-closed
                                // semantic gate below is the authoritative check.
                                tracing::warn!(error = %e, conflict_len = conflict_terms.len(),
                                    concat!("BUG(#4666): ", $tag, " conflict structural verification failed; deferring to fail-closed semantic gate"));
                            }
                            // Fail-closed: a conflict that cannot be semantically
                            // verified must NOT be learned as a global clause (the
                            // former #8595 "using conflict anyway" arm laundered
                            // unverifiable theory conflicts into wrong UNSAT verdicts).
                            // Verifiable-domain skips inside `verify_conflict_semantic`
                            // return Ok, so only genuine verification failures reach
                            // this bail (mirrors the lazy split loop in
                            // pipeline_incremental_split_lazy_shared_macros.rs).
                            if let Err(e) = $crate::verification::verify_conflict_semantic_memoized(
                                &mut $self.conflict_semantic_verify_memo,
                                &conflict_terms,
                                &$self.ctx.terms,
                                &$self.active_support_axioms,
                            ) {
                                tracing::error!(
                                    error = %e,
                                    conflict_len = conflict_terms.len(),
                                    conflict = ?conflict_terms,
                                    concat!("BUG(#6853): ", $tag, " conflict semantic verification failed; returning Unknown instead of learning unverified clause")
                                );
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                break Ok(SolveResult::Unknown);
                            }
                            let _itp_conflict_annotation = if proof_enabled {
                                dt_conflict_proof!($self, _itp_negations, &conflict_terms, _itp_dt_registry_data)
                            } else { None };
                            if $track_stats {
                                state.theory_conflicts = state.theory_conflicts.saturating_add(1);
                                collect_theory_stats!(incremental: $self, state);
                            }
                            pipeline_add_incremental_conflict_clause!(
                                $self, state: state, solver: solver,
                                term_to_var: term_to_var, conflict_terms: conflict_terms,
                                tag: $tag, set_unknown_on_error: $set_unknown,
                                unmapped_message: "incremental pipeline: theory conflict terms all failed to map; returning Unknown",
                                proof_enabled: proof_enabled,
                                theory_proof: _itp_conflict_annotation
                            );
                        }
                        ay_core::TheoryResult::UnsatWithFarkas(mut conflict) => {
                            theory.unset_terms();
                            // #4666: dedupe with Farkas coefficient merge-by-sum
                            // (logical identity; certificate stays aligned).
                            $crate::verification::dedup_conflict_with_farkas(&mut conflict);
                            log_conflict_debug(&conflict.literals, concat!("incremental ", $tag, " UnsatWithFarkas"));
                            let mut _itp_farkas_proof_valid = conflict.farkas.is_some();
                            if let Err(e) = verify_theory_conflict_with_farkas(&conflict) {
                                if e.is_missing_annotation() {
                                    // Missing Farkas annotation (#6535): no certificate to
                                    // check. The conflict itself is still gated by the
                                    // fail-closed semantic backstop below.
                                    _itp_farkas_proof_valid = false;
                                    tracing::debug!(conflict_len = conflict.literals.len(),
                                        concat!($tag, " Farkas annotation missing; skipping proof cert, deferring to semantic backstop"));
                                } else {
                                    // Certificate downgrade: drop the unusable certificate
                                    // and defer to the fail-closed semantic backstop below.
                                    _itp_farkas_proof_valid = false;
                                    tracing::warn!(error = %e, conflict_len = conflict.literals.len(),
                                        concat!("BUG(#4666): ", $tag, " Farkas structural verification failed; dropping certificate, deferring to semantic backstop"));
                                }
                            }
                            // Semantic Farkas verification in ALL builds
                            // (adversarial-review followup on #rank-4 increment 2;
                            // was debug-only per W16-5): a semantically verified
                            // certificate proves the conflict.
                            let mut _itp_farkas_semantically_verified = false;
                            if _itp_farkas_proof_valid && conflict.farkas.is_some() {
                                match verify_theory_conflict_with_farkas_full(&conflict, &$self.ctx.terms) {
                                    Ok(()) => _itp_farkas_semantically_verified = true,
                                    Err(e) => {
                                        // Certificate downgrade: semantically invalid
                                        // certificate. Defer to the fail-closed semantic
                                        // backstop below.
                                        _itp_farkas_proof_valid = false;
                                        tracing::warn!(error = %e, conflict_len = conflict.literals.len(),
                                            concat!("BUG(#4666): ", $tag, " Farkas semantic verification failed; dropping certificate, deferring to semantic backstop"));
                                    }
                                }
                            }
                            // Release backstop (fail-closed): when the UNSAT verdict is
                            // NOT covered by a semantically verified certificate, run the
                            // same domain-aware semantic re-check the Unsat arm runs. If
                            // that also fails, the conflict has no verification at all —
                            // do not learn it (the former #8595 "using conflict without
                            // certificate" arms learned it unconditionally).
                            if !_itp_farkas_semantically_verified {
                                if let Err(e) = $crate::verification::verify_conflict_semantic_memoized(
                                    &mut $self.conflict_semantic_verify_memo,
                                    &conflict.literals,
                                    &$self.ctx.terms,
                                    &$self.active_support_axioms,
                                ) {
                                    tracing::error!(
                                        error = %e,
                                        conflict_len = conflict.literals.len(),
                                        conflict = ?conflict.literals,
                                        concat!("BUG(#6853): ", $tag, " Farkas conflict semantic verification failed; returning Unknown instead of learning unverified clause")
                                    );
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break Ok(SolveResult::Unknown);
                                }
                            }
                            let _itp_conflict_annotation = if proof_enabled && _itp_farkas_proof_valid {
                                dt_farkas_proof!($self, _itp_negations, &conflict, _itp_dt_registry_data)
                            } else if proof_enabled {
                                dt_conflict_proof!($self, _itp_negations, &conflict.literals, _itp_dt_registry_data)
                            } else { None };
                            if $track_stats {
                                state.theory_conflicts = state.theory_conflicts.saturating_add(1);
                                collect_theory_stats!(incremental: $self, state);
                            }
                            pipeline_add_incremental_conflict_clause!(
                                $self, state: state, solver: solver,
                                term_to_var: term_to_var, conflict_terms: conflict.literals,
                                tag: $tag, set_unknown_on_error: $set_unknown,
                                unmapped_message: "incremental pipeline: Farkas conflict terms all failed to map; returning Unknown",
                                proof_enabled: proof_enabled,
                                theory_proof: _itp_conflict_annotation
                            );
                        }
                        ay_core::TheoryResult::NeedLemmas(lemmas) => {
                            let mut any_new = false;
                            let mut new_lemmas = Vec::new();
                            for lemma in &lemmas {
                                if !state.theory_lemma_keys.insert(lemma.clause.clone()) { continue; }
                                any_new = true;
                                let (recorded_in_trace, original_id) = $crate::executor::theories::split_incremental::apply_theory_lemma_incremental_persistent(
                                    solver, &mut term_to_var, &mut var_to_term,
                                    &mut _itp_negations, &lemma.clause,
                                );
                                ay_core::TheorySolver::note_applied_theory_lemma(&mut theory, &lemma.clause);
                                new_lemmas.push((lemma.clone(), recorded_in_trace, original_id));
                            }
                            if !any_new {
                                if $set_unknown { $self.last_unknown_reason = Some(UnknownReason::Incomplete); }
                                $self.last_result = Some(SolveResult::Unknown);
                                break Ok(SolveResult::Unknown);
                            }
                            theory.unset_terms();
                            _itp_replayed_lemma_count = state.theory_lemmas.len() + new_lemmas.len();
                            if proof_enabled {
                                _itp_negations.sync_pending(&mut $self.ctx.terms);
                                // #trust->0 C3: DT registries, once per batch.
                                let _c3_dt = $crate::theory_inference::dt_funnel_registry_data(&$self.ctx);
                                for (lemma, recorded_in_trace, original_id) in &new_lemmas {
                                    let terms: Vec<TermId> = lemma.clause.iter().map(|lit| {
                                        if lit.value { lit.term }
                                        else { *_itp_negations.as_map().get(&lit.term)
                                            .expect("persistent theory-lemma negation cache should be synced") }
                                    }).collect();
                                    // #trust->0 C3: funnel classifies + records;
                                    // adopt its validator-ordered clause.
                                    let (kind, terms) = $crate::theory_inference::record_funnel_classified_lemma(
                                        &mut $self.proof_tracker, &$self.ctx.terms, terms, _c3_dt.as_ref(),
                                    );
                                    if let Some(original_id) = *original_id {
                                        $crate::pipeline_fns::place_original_clause_authority_at_id(
                                            &solver,
                                            original_id,
                                            None,
                                            recorded_in_trace.then_some(ay_core::TheoryLemmaProof {
                                                clause: terms,
                                                kind,
                                                farkas: None,
                                                lia: None,
                                            }),
                                            &mut state.clausification_proofs,
                                            &mut state.original_clause_theory_proofs,
                                        );
                                    }
                                }
                            }
                            let lemma_depth = state.scope_depth;
                            // #8304: Also record into the executor's LemmaCache
                            // when lemma persistence is enabled.
                            if $self.lemma_persistence {
                                for (lemma, _, _) in &new_lemmas {
                                    $self.lemma_cache.record_lemma(lemma.clone(), lemma_depth);
                                }
                            }
                            state.theory_lemmas.extend(
                                new_lemmas.into_iter().map(|(lemma, _, _)| (lemma, lemma_depth)),
                            );
                            continue;
                        }
                        ay_core::TheoryResult::NeedModelEquality(eq) => {
                            theory.unset_terms();
                            if _itp_model_eq_tracker.increment_round() {
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                break Ok(SolveResult::Unknown);
                            }
                            pipeline_encode_model_equality!(
                                $self, solver, term_to_var, var_to_term,
                                _itp_next_var, _itp_negations, eq
                            );
                            continue;
                        }
                        ay_core::TheoryResult::NeedModelEqualities(eqs) => {
                            theory.unset_terms();
                            if _itp_model_eq_tracker.increment_round() {
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                break Ok(SolveResult::Unknown);
                            }
                            for eq in &eqs {
                                pipeline_encode_model_equality!(
                                    $self, solver, term_to_var, var_to_term,
                                    _itp_next_var, _itp_negations, *eq
                                );
                            }
                            continue;
                        }
                        ay_core::TheoryResult::Unknown
                        | ay_core::TheoryResult::NeedSplit(_)
                        | ay_core::TheoryResult::NeedDisequalitySplit(_)
                        | ay_core::TheoryResult::NeedExpressionSplit(_)
                        // Plural variant (Real disequality `a != b` -> a<b | a>b)
                        // emitted on the LRA disequality-saturated lane. The first
                        // match block above already fails closed to Unknown here;
                        // this `persistent_theory: true` block (used by
                        // solve_lra_incremental) was missed by the original F0 fix
                        // and still hit the unreachable!() below — a deterministic
                        // SIGABRT on sally/oral_messages disequalities, which the
                        // F1 Bool-in-IMC unlock now exercises via IMC's check_sat
                        // (see the development design notes F0/F1).
                        | ay_core::TheoryResult::NeedExpressionSplits(_)
                        | ay_core::TheoryResult::NeedStringLemma(_) => {
                            theory.unset_terms();
                            $self.last_result = Some(SolveResult::Unknown);
                            break Ok(SolveResult::Unknown);
                        }
                            other => {
                                theory.unset_terms();
                                unreachable!("unhandled TheoryResult variant in incremental pipeline: {other:?}")
                            },
                    }
                }
                SatResult::Unsat(_) => {
                    if proof_enabled {
                        _itp_negations.sync_pending(&mut $self.ctx.terms);
                        $crate::pipeline_fns::drain_pending_original_clause_authorities(
                            &solver,
                            &mut _itp_negations,
                            &mut state.clausification_proofs,
                            &mut state.original_clause_theory_proofs,
                        );
                        let _itp_clause_trace = solver.snapshot_clause_trace();
                        $crate::pipeline_fns::align_original_clause_authority_ledgers(
                            &solver,
                            &mut state.clausification_proofs,
                            &mut state.original_clause_theory_proofs,
                        );
                        _itp_proof_stash = Some((
                            _itp_clause_trace,
                            {
                                // PROOF-CAPTURE ONLY: real per-round entries win;
                                // backfill (assertion-root var->term from
                                // encoded_assertions) fills the gap when a
                                // re-activated assertion root wasn't re-encoded this
                                // round. Does NOT touch the live solve maps.
                                let mut _itp_m = var_to_term.clone();
                                for &(_itp_bv, _itp_bt) in &_itp_proof_backfill {
                                    _itp_m.entry(_itp_bv).or_insert(_itp_bt);
                                }
                                _itp_m.iter().map(|(&v, &t)| (v, t)).collect()
                            },
                            _itp_negations.as_map().clone(),
                            state.clausification_proofs.clone(),
                            state.original_clause_theory_proofs.clone(),
                        ));
                    }
                    $self.last_model = None;
                    $self.last_result = Some(SolveResult::unsat());
                    break Ok(SolveResult::unsat());
                }
                SatResult::Unknown => {
                    $self.last_model = None;
                    if $self.last_unknown_reason.is_none() {
                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    }
                    $self.last_result = Some(SolveResult::Unknown);
                    break Ok(SolveResult::Unknown);
                }
                #[allow(unreachable_patterns)]
                _ => unreachable!(),
            }
        };

        // #warm-theory: persist the (possibly warm) theory for the next
        // check-sat. `theory` is owned before the loop so it survives every
        // break; its terms pointer was unset at the loop exit and is refreshed
        // via set_terms on reuse. Re-borrow incr_theory_state fresh here (NOT the
        // `state` binding, whose borrow must not extend across the loop body's
        // `&mut self` uses). Stored only in warm mode; in the standalone reverify
        // lane the enclosing IncrementalTheoryState is a throwaway temp_state
        // (discarded), so this never persists there.
        if _itp_warm {
            if let Some(_itp_st) = $self.incr_theory_state.as_mut() {
                _itp_st.persist_theory = Some(Box::new(theory));
            }
        }

        if let Some((_itp_ct, _itp_vtm, _itp_neg, _itp_cp, _itp_tp)) = _itp_proof_stash {
            $self.last_clause_trace = _itp_ct;
            $crate::pipeline_fns::record_var_map_provenance_trace(
                "incremental", _itp_vtm.len(), $self.last_clause_trace.as_ref());
            $self.last_var_to_term = Some(_itp_vtm);
            $self.last_negations = Some(_itp_neg);
            $self.last_clausification_proofs = Some(_itp_cp);
            $self.last_original_clause_theory_proofs = Some(_itp_tp);
            $self.build_unsat_proof();
        } else if matches!(_itp_result, Ok(ref r) if r.is_unsat()) && $self.produce_proofs_enabled() {
            $self.build_unsat_proof();
        }

        _itp_result
    }};
}
