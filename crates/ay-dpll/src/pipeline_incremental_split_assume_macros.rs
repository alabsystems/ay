// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assumption-based arm of the incremental split-loop pipeline.
//!
//! Extracted from `pipeline_incremental_split_macros.rs` (#6680).
//! Contains the assumption-aware counterpart of the lazy arm.
//! Keeps one persistent SAT solver alive across split iterations
//! and uses `solve_with_assumptions` instead of `solve`.

/// Assumption arm implementation for `solve_incremental_assume_split_loop_pipeline!`.
macro_rules! pipeline_incremental_split_assume_arm {
    ($self:ident,
        tag: $tag:expr,
        persistent_sat_field: $sat_field:ident,
        assumptions: $assumptions:expr,
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
        use ay_sat::{AssumeResult, Literal as SatLiteral, Variable as SatVariable};
        use $crate::executor_types::{SolveResult, UnknownReason};
        use $crate::incremental_state::{
            collect_active_theory_atoms_cached, collect_reachable_theory_atoms,
            IncrementalTheoryState,
        };
        use $crate::executor::theories::freeze_var_if_needed;
        use $crate::executor::theories::split_incremental::{
            map_conflict_to_blocking_clause,
            BlockingClauseResult,
        };

        let proof_enabled = $self.produce_proofs_enabled();
        let _iaslp_problem_assertions = if proof_enabled {
            $self.proof_problem_assertions()
        } else {
            Vec::new()
        };
        let _iaslp_assumptions: &[(TermId, TermId)] = $assumptions;
        let random_seed = $self.current_random_seed();
        let should_record_random_seed = match $self.incr_theory_state.as_ref() {
            Some(state) => state.$sat_field.is_none(),
            None => true,
        };
        if should_record_random_seed {
            $self.record_applied_sat_random_seed_for_test(random_seed);
        }

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
            tseitin_field: tseitin_state,
            encoded_field: encoded_assertions,
            activation_scope_field: assertion_activation_scope,
            solver_init: {
                if let Some(ref mut sat) = state.$sat_field {
                    for _ in 0..state.scope_depth {
                        sat.push();
                    }
                }
            },
            out: (_iaslp_new_assertion_set, _iaslp_solver, _iaslp_tseitin, _iaslp_base_vtm_tmp, _iaslp_base_ttv_tmp, _iaslp_pending_activations)
        );

        // Encode assumptions into the live Tseitin BEFORE saving state (#6689).
        // Use encode_assertion() to capture definitional clauses for composite
        // Boolean assumptions (e.g. `(and (= x 0) (= x 1))`). Without this,
        // the SAT solver sees an unconstrained gate variable and the inner
        // equalities are disconnected from the assumption.
        let _iaslp_cnf_to_sat = $crate::cnf_lit_to_sat;
        let mut _iaslp_sat_assumptions: Vec<SatLiteral> = Vec::with_capacity(_iaslp_assumptions.len());
        let mut _iaslp_assumption_to_term: Vec<(SatLiteral, TermId)> =
            Vec::with_capacity(_iaslp_assumptions.len());
        for &(preprocessed_assumption, original_assumption) in _iaslp_assumptions {
            let (base_term, positive) = match $self.ctx.terms.get(preprocessed_assumption) {
                ay_core::term::TermData::Not(inner) => (*inner, false),
                _ => (preprocessed_assumption, true),
            };
            let enc = _iaslp_tseitin.encode_assertion(base_term);

            // Expand SAT solver variable count before adding definitional clauses.
            _iaslp_solver.ensure_num_vars(_iaslp_tseitin.num_vars() as usize);

            // Install assumption-side definitional clauses globally (#6689).
            // Mirrors the assertion-side bookkeeping in pipeline_incremental_setup!.
            if proof_enabled {
                let _iaslp_ann = enc.def_proof_annotations
                    .as_ref()
                    .expect("proof-enabled incremental Tseitin encoding should carry annotations");
                debug_assert_eq!(
                    _iaslp_ann.len(),
                    enc.def_clauses.len(),
                    "assumption-side clause annotations must stay aligned with SAT clause order"
                );
                for (_iaslp_didx, clause) in enc.def_clauses.iter().enumerate() {
                    let lits: Vec<SatLiteral> = clause
                        .literals()
                        .iter()
                        .map(|&lit| _iaslp_cnf_to_sat(lit))
                        .collect();
                    let _iaslp_authority_before =
                        _iaslp_solver.issued_original_clause_id_max();
                    _iaslp_solver.add_clause_global(lits);
                    let _ = $crate::pipeline_fns::place_single_original_clause_authority(
                        &_iaslp_solver,
                        _iaslp_authority_before,
                        _iaslp_ann[_iaslp_didx].clone(),
                        None,
                        &mut state.clausification_proofs,
                        &mut state.original_clause_theory_proofs,
                    );
                }
            } else {
                for clause in &enc.def_clauses {
                    let lits: Vec<SatLiteral> = clause
                        .literals()
                        .iter()
                        .map(|&lit| _iaslp_cnf_to_sat(lit))
                        .collect();
                    _iaslp_solver.add_clause_global(lits);
                }
            }

            let cnf_lit = enc.root_lit;
            let sat_var = SatVariable::new(cnf_lit.unsigned_abs() - 1);
            let sat_lit = if (cnf_lit > 0) == positive {
                SatLiteral::positive(sat_var)
            } else {
                SatLiteral::negative(sat_var)
            };
            _iaslp_sat_assumptions.push(sat_lit);
            _iaslp_assumption_to_term.push((sat_lit, original_assumption));
        }

        // Rebuild var maps after assumption encoding (new atoms may have been added).
        let base_var_to_term: HashMap<u32, TermId> = _iaslp_tseitin
            .var_to_term()
            .iter()
            .map(|(&v, &t)| (v - 1, t))
            .collect();
        let base_term_to_var: HashMap<TermId, u32> = _iaslp_tseitin
            .term_to_var()
            .iter()
            .map(|(&t, &v)| (t, v - 1))
            .collect();
        _iaslp_solver.ensure_num_vars(_iaslp_tseitin.num_vars() as usize);

        state.tseitin_state = _iaslp_tseitin.into_state();
        state.$sat_field = Some(_iaslp_solver);
        // Proof ledger clone + context registration (#5814 Packet A)
        let (mut _iaslp_local_clausification_proofs, mut _iaslp_local_original_clause_theory_proofs) =
            pipeline_clone_local_proof_ledgers!(state, proof_enabled);
        pipeline_register_proof_context!(
            $self,
            proof_enabled,
            $tag,
            problem_assertions: _iaslp_problem_assertions,
            assumptions: _iaslp_assumptions
        );

        // Collect theory atoms from assertions AND assumptions. The
        // (TermStore-global) Bool-UF-arg scan reuses the persistent
        // high-water-mark cache and runs once here (#N); per-assumption
        // sub-collections only need their assertion-reachable atoms, since the
        // global Bool-UF-arg set is identical regardless of the assertion list.
        let mut base_active_atoms = collect_active_theory_atoms_cached(
            &$self.ctx.terms,
            &$self.ctx.assertions,
            Some(&mut state.bool_uf_arg_cache),
        );
        for &(preprocessed, _original) in _iaslp_assumptions {
            let assumption_atoms = collect_reachable_theory_atoms(&$self.ctx.terms, &[preprocessed]);
            for atom in assumption_atoms {
                base_active_atoms.insert(atom);
            }
        }

        // Reuse scratch allocation from previous check-sat call (#8573).
        state.scratch_var_to_term.clone_from(&base_var_to_term);
        let mut local_var_to_term: HashMap<u32, TermId> =
            std::mem::take(&mut state.scratch_var_to_term);

        let solver = state
            .$sat_field
            .as_mut()
            .expect(concat!("incremental ", $tag, " should have persistent SAT solver"));

        solver.push();
        // #6853: Apply deferred activation clauses inside the private push scope.
        pipeline_apply_pending_activations!(
            solver, _iaslp_pending_activations, proof_enabled, state
        );
        // #6853: Re-activate ALL encoded assertions inside the private push.
        pipeline_reactivate_all_in_scope!(
            $self, solver, state, _iaslp_pending_activations,
            proof_enabled, encoded_assertions
        );
        for &term in &base_active_atoms {
            if let Some(&var) = base_term_to_var.get(&term) {
                freeze_var_if_needed(solver, SatVariable::new(var));
            }
        }

        // Bound axiom injection (#6579): shared macro (#5814 Packet 1)
        pipeline_inject_bound_axioms!(
            $self, solver, base_active_atoms, base_term_to_var,
            $create_theory, proof_enabled, $tag,
            _iaslp_local_clausification_proofs, _iaslp_local_original_clause_theory_proofs,
            state
        );

        let mut local_term_to_var: HashMap<TermId, u32> = base_term_to_var;
        let mut local_next_var: u32 = u32::try_from(solver.user_num_vars() + solver.scope_depth())
            .expect("SAT solver variable count does not fit in u32");
        let base_vars: HashSet<u32> = base_var_to_term.keys().copied().collect();
        let mut _iaslp_added_split_clauses: HashSet<
            $crate::executor::theories::split_incremental::SplitClauseKey,
        > = HashSet::default();
        let mut _iaslp_model_eq_tracker = $crate::executor::theories::split_incremental::ModelEqualityTracker::new(
            $crate::executor::theories::split_incremental::model_equality::MODEL_EQ_MAX_ROUNDS_SPLIT,
        );

        let mut _iaslp_learned_cuts: Vec<ay_lia::StoredCut> = Vec::new();
        let mut _iaslp_seen_hnf_cuts: HashSet<ay_lia::HnfCutKey> = HashSet::default();
        let mut _iaslp_dioph_state = ay_lia::DiophState::default();
        let mut _iaslp_theory_lemmas: Vec<ay_core::TheoryLemma> = Vec::new();

        let mut _iaslp_last_split_values: $crate::executor::theories::solve_harness::SplitOscillationMap = HashMap::default();
        let mut _iaslp_last_theory_stats: Vec<(&'static str, u64)> = Vec::new();
        let mut _iaslp_timing = $crate::SplitLoopTimingStats::default();
        let _iaslp_total_start = ay_core::time::Instant::now();
        let mut _iaslp_theory_snapshot: Option<Box<dyn std::any::Any>> = None;

        // Proof tracking setup (#6660, #6689, #6735)
        let mut _iaslp_negations = $crate::incremental_proof_cache::IncrementalNegationCache::seed(
            &mut $self.ctx.terms,
            local_var_to_term.values().copied(),
            proof_enabled,
        );
        let mut _iaslp_theory_lemma_seen =
            $crate::incremental_proof_cache::TheoryLemmaSeenSet::default();
        let _iaslp_result: $crate::executor_types::Result<SolveResult> = 'split_loop: {
            for _iteration in 0..$max_splits {
                $(
                    {
                        let $pic_self = &();
                        if $pic_expr {
                            let _ = solver.pop();
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                    }
                )?

                state.round_trips += 1;
                _iaslp_timing.dpll.round_trips += 1;

                // #array-deadline-forward: forward the executor's live
                // per-solve deadline into the SAT solver so the phases the
                // budgets cannot bound (incremental inprocessing, level-0
                // GC) and this arm's NON-interruptible
                // `solve_with_assumptions` entry honor the caller's wall
                // budget. Refreshed before every solve; `None` clears.
                solver.set_solve_deadline($self.solve_deadline.get());
                // Deterministic resource budgets (#8749 `:rlimit` +
                // #ground-determinism defaults), assume-arm parity with the
                // other split loops.
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

                let _iaslp_sat_start = ay_core::time::Instant::now();
                let assume_result = solver.solve_with_assumptions(&_iaslp_sat_assumptions).into_inner();
                _iaslp_timing.dpll.sat_solve += _iaslp_sat_start.elapsed();
                if let Some(r) = solver.last_unknown_reason() {
                    $self.last_unknown_reason = Some($crate::executor::Executor::map_sat_unknown_reason(r));
                }
                collect_sat_stats!($self, solver);
                collect_theory_stats!(incremental: $self, state);

                match assume_result {
                    AssumeResult::Sat(model) => {
                        _iaslp_negations.sync_pending(&mut $self.ctx.terms);
                        let mut theory = $create_theory;
                        if let Some(snapshot) = _iaslp_theory_snapshot.take() {
                            <_ as ay_core::TheorySolver>::import_structural_snapshot(&mut theory, snapshot);
                        }
                        {
                            let $import_theory = &mut theory;
                            let $import_lc = &mut _iaslp_learned_cuts;
                            let $import_hc = &mut _iaslp_seen_hnf_cuts;
                            let $import_ds = &mut _iaslp_dioph_state;
                            $import_expr;
                        }
                        for &atom in &base_active_atoms {
                            ay_core::TheorySolver::register_atom(&mut theory, atom);
                        }
                        for lemma in &_iaslp_theory_lemmas {
                            ay_core::TheorySolver::note_applied_theory_lemma(&mut theory, &lemma.clause);
                        }
                        for (var, term) in $crate::iter_var_to_term_sorted(&local_var_to_term) {
                            let is_dynamic_split = !base_vars.contains(&var);
                            let is_active = is_dynamic_split || base_active_atoms.contains(&term);
                            if $crate::is_theory_atom(&$self.ctx.terms, term) && is_active {
                                if is_dynamic_split {
                                    ay_core::TheorySolver::register_atom(&mut theory, term);
                                }
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
                        theory.replay_learned_cuts();
                        // #qf-auflia-fc-diseq-sync: see the eager arm — assert
                        // preprocessor-eliminated top-level arithmetic
                        // disequality facts so the theory's diseq check and
                        // repair machinery can see them.
                        let _islp_synced_diseq_facts =
                            $crate::pipeline_fns::assert_top_level_arith_diseq_facts(
                                &$self.ctx.terms,
                                &$self.ctx.assertions,
                                &mut theory,
                            );

                        let _iaslp_theory_start = ay_core::time::Instant::now();
                        let theory_result = ay_core::TheorySolver::check(&mut theory);
                        _iaslp_timing.dpll.theory_check += _iaslp_theory_start.elapsed();
                        _iaslp_last_theory_stats = ay_core::TheorySolver::collect_statistics(&theory);
                        _iaslp_theory_snapshot = <_ as ay_core::TheorySolver>::export_structural_snapshot(&theory);
                        pipeline_incremental_split_lazy_dispatch_theory_result!(
                            'split_loop, $self, solver, state,
                            tag: $tag,
                            theory,
                            theory_result: theory_result,
                            export_theory: |$export_theory| $export_expr,
                            local_term_to_var, local_var_to_term, local_next_var,
                            _iaslp_added_split_clauses, _iaslp_last_split_values, _iaslp_model_eq_tracker,
                            _iaslp_learned_cuts, _iaslp_seen_hnf_cuts, _iaslp_dioph_state, _iaslp_theory_lemmas, _iaslp_theory_lemma_seen,
                            _iaslp_negations, proof_enabled,
                            _iaslp_local_clausification_proofs, _iaslp_local_original_clause_theory_proofs,
                            sat_handler: {
                                pipeline_store_sat_model!(
                                    'split_loop, $self, solver, model,
                                    local_term_to_var, local_var_to_term, local_next_var,
                                    _iaslp_timing, theory, $theory_var, $extract,
                                    pre_store: { let _ = solver.pop(); }
                                );
                            },
                            remaining_arms: {
                                ay_core::TheoryResult::NeedStringLemma(_)
                                | ay_core::TheoryResult::Unknown => {
                                    let _ = solver.pop();
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                                other => unreachable!("unhandled TheoryResult in assumption split loop: {other:?}"),
                            }
                        );
                    }
                    AssumeResult::Unsat(core, _) => {
                        // Map SAT core back to original assumption terms.
                        let unsat_assumptions: Vec<TermId> = core.iter().filter_map(|lit| {
                            _iaslp_assumption_to_term.iter()
                                .find(|(sat_lit, _)| sat_lit == lit)
                                .map(|(_, term)| *term)
                        }).collect();
                        $self.last_assumption_core = Some(unsat_assumptions);
                        $self.last_unknown_reason = None;
                        // UNSAT proof capture + pop: shared macro (#5814 Packet 3)
                        pipeline_build_unsat_proof_with_pop!(
                            'split_loop, $self, solver,
                            local_var_to_term, _iaslp_negations, proof_enabled,
                            _iaslp_local_clausification_proofs, _iaslp_local_original_clause_theory_proofs
                        );
                    }
                    AssumeResult::Unknown => {
                        $self.last_model = None;
                        let _ = solver.pop();
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
            // Too many splits
            let _ = solver.pop();
            if $self.last_unknown_reason.is_none() {
                $self.record_unknown_from_origin($crate::UnknownOrigin::TheorySplitBudget);
            }
            $self.last_result = Some(SolveResult::Unknown);
            Ok(SolveResult::Unknown)
        };

        state.scratch_var_to_term = local_var_to_term;
        pipeline_split_epilogue!(
            $self, _iaslp_timing, _iaslp_total_start,
            _iaslp_last_theory_stats, _iaslp_result,
            eager: {},
            restore: { $self.incr_theory_state = Some(state); }
        )
    }};
}
