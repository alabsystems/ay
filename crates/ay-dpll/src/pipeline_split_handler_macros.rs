// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared split-handler macros for active DPLL(T) pipelines.
//!
//! The remaining macros centralize the incremental conflict and replay helpers
//! that are still shared after the legacy split-loop deletion.

/// Thin control-flow shim over [`crate::pipeline_fns::add_incremental_conflict_clause`].
///
/// The clause-building / level-0-minimization / verdict logic was de-macro'd into
/// that function (#8424); this macro survives only to translate the function's
/// [`crate::pipeline_fns::AddConflictClauseOutcome::Break`] verdict into the
/// caller loop's `break Ok(..)` (a function cannot break the caller's loop) and to
/// capture the private `$self.last_result`/`last_unknown_reason` fields. All call
/// sites are unchanged.
macro_rules! pipeline_add_incremental_conflict_clause {
    (
        $self:ident,
        state: $state:ident,
        solver: $solver:ident,
        term_to_var: $term_to_var:ident,
        conflict_terms: $conflict_terms:expr,
        tag: $tag:expr,
        set_unknown_on_error: $set_unknown:expr,
        unmapped_message: $unmapped_message:literal
    ) => {{
        match $crate::pipeline_fns::add_incremental_conflict_clause(
            &mut $self.last_result,
            &mut $self.last_unknown_reason,
            $solver,
            &$term_to_var,
            &$conflict_terms,
            $tag,
            $set_unknown,
            $unmapped_message,
        ) {
            $crate::pipeline_fns::AddConflictClauseOutcome::Added => {}
            $crate::pipeline_fns::AddConflictClauseOutcome::Break(__acc_result) => {
                break Ok(__acc_result)
            }
        }
    }};
}

/// Persist a verified incremental split-loop conflict as a blocking clause.
///
/// Used by `solve_incremental_split_loop_pipeline!` after the conflict has
/// been verified, regardless of whether it came from a plain theory conflict
/// or a Farkas explanation.
///
/// Proof capture (#6660 Packet 7): when `proof_enabled` is true, the Unsat
/// exit clones proof data from solver/state, pops the SAT frame, then assigns
/// to `$self` and calls `build_unsat_proof()`. The clone-pop-assign ordering
/// avoids double-mutable-borrow of `$self` through the `state -> solver` chain.
macro_rules! pipeline_map_incremental_split_conflict_clause {
    (
        $self:ident,
        label: $label:lifetime,
        state: $state:ident,
        solver: $solver:ident,
        theory: $theory:ident,
        export_theory: |$export_theory:ident| $export_expr:expr,
        learned_cuts: $learned_cuts:ident,
        seen_hnf_cuts: $seen_hnf_cuts:ident,
        dioph_state: $dioph_state:ident,
        local_term_to_var: $local_term_to_var:ident,
        conflict_terms: $conflict_terms:expr,
        proof_enabled: $proof_enabled:expr,
        negations: $negations:expr,
        local_var_to_term: $local_var_to_term:expr,
        local_clausification_proofs: $local_clausification_proofs:ident,
        local_theory_proofs: $local_theory_proofs:ident,
        theory_proof: $theory_proof:expr
    ) => {{
        $state.theory_conflicts = $state.theory_conflicts.saturating_add(1);
        collect_theory_stats!(incremental: $self, $state);

        let extra_conflicts = $theory.lra_solver().collect_all_bound_conflicts(true);
        pipeline_export_theory_state!(
            $theory, $export_theory, $export_expr,
            $learned_cuts, $seen_hnf_cuts, $dioph_state
        );

        match map_conflict_to_blocking_clause(
            $solver,
            &$conflict_terms,
            &extra_conflicts,
            &$local_term_to_var,
        ) {
            BlockingClauseResult::Unmapped => {
                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                break;
            }
            BlockingClauseResult::Unsat => {
                if $proof_enabled {
                    let _pmc_clause_trace = $solver.snapshot_clause_trace();
                    let (_pmc_clausification_proofs, _pmc_theory_proofs) = {
                        if let Some(ref _pmc_trace) = _pmc_clause_trace {
                            let _pmc_count = _pmc_trace.original_clauses().count();
                            if $local_clausification_proofs.len() < _pmc_count {
                                $local_clausification_proofs.resize(_pmc_count, None);
                            }
                            if $local_theory_proofs.len() < _pmc_count {
                                $local_theory_proofs.resize(_pmc_count, None);
                            }
                        }
                        (
                            $local_clausification_proofs.clone(),
                            $local_theory_proofs.clone(),
                        )
                    };
                    let _pmc_vtm = $local_var_to_term.clone();
                    let _pmc_neg = $negations.clone();
                    let _ = $solver.pop();
                    $self.last_clause_trace = _pmc_clause_trace;
                    $self.last_clausification_proofs = Some(_pmc_clausification_proofs);
                    $self.last_original_clause_theory_proofs = Some(_pmc_theory_proofs);
                    $crate::pipeline_fns::record_var_map_provenance("split_handler", &$solver, _pmc_vtm.len());
                    $self.last_var_to_term = Some(_pmc_vtm);
                    $self.last_negations = Some(_pmc_neg);
                    $self.build_unsat_proof();
                } else {
                    let _ = $solver.pop();
                }
                $self.last_result = Some(SolveResult::unsat());
                break $label Ok(SolveResult::unsat());
            }
            BlockingClauseResult::Added => {
                if let Some(_pmc_theory_proof) = $theory_proof {
                    $local_clausification_proofs.push(None);
                    $local_theory_proofs.push(Some(_pmc_theory_proof));
                }
            }
        }
    }};
}

/// Convert a verified model equality into SAT clauses (#5814 Packet 4).
///
/// Thin shim over `pipeline_fns::encode_model_equality`. The eq pieces are
/// passed by Copy value (`lhs`/`rhs`/`implied`) plus a borrowed reason slice,
/// and `&mut $self.ctx.terms` / `&mut $solver` are disjoint borrows at every
/// call site. All existing call signatures are preserved unchanged.
#[allow(unused_macro_rules)]
macro_rules! pipeline_encode_model_equality {
    ($self:expr, $solver:expr, $term_to_var:expr, $var_to_term:expr,
     $next_var:expr, $negations:expr, $eq:expr, added_model_eqs: $added_model_eqs:expr) => {{
        let _pemq_eq = &$eq;
        $crate::pipeline_fns::encode_model_equality(
            &mut $self.ctx.terms,
            $solver,
            &mut $term_to_var,
            &mut $var_to_term,
            &mut $next_var,
            &mut $negations,
            _pemq_eq.lhs,
            _pemq_eq.rhs,
            _pemq_eq.implied,
            &_pemq_eq.reason,
            Some($added_model_eqs),
            None::<&mut dyn ay_core::TheorySolver>,
            true,
        );
    }};
    // Variant with theory reference (#8254) — currently unused by all call sites.
    ($self:expr, $solver:expr, $term_to_var:expr, $var_to_term:expr,
     $next_var:expr, $negations:expr, $eq:expr, added_model_eqs: $added_model_eqs:expr,
     theory: $theory:expr) => {{
        let _pemq_eq = &$eq;
        $crate::pipeline_fns::encode_model_equality(
            &mut $self.ctx.terms,
            $solver,
            &mut $term_to_var,
            &mut $var_to_term,
            &mut $next_var,
            &mut $negations,
            _pemq_eq.lhs,
            _pemq_eq.rhs,
            _pemq_eq.implied,
            &_pemq_eq.reason,
            Some($added_model_eqs),
            Some(&mut $theory),
            true,
        );
    }};
    ($self:expr, $solver:expr, $term_to_var:expr, $var_to_term:expr,
     $next_var:expr, $negations:expr, $eq:expr) => {{
        let _pemq_eq = &$eq;
        $crate::pipeline_fns::encode_model_equality(
            &mut $self.ctx.terms,
            $solver,
            &mut $term_to_var,
            &mut $var_to_term,
            &mut $next_var,
            &mut $negations,
            _pemq_eq.lhs,
            _pemq_eq.rhs,
            _pemq_eq.implied,
            &_pemq_eq.reason,
            None,
            None::<&mut dyn ay_core::TheorySolver>,
            true,
        );
    }};
    // #8596: Variant that skips triangle axioms for pure ArrayEUF (no arithmetic).
    ($self:expr, $solver:expr, $term_to_var:expr, $var_to_term:expr,
     $next_var:expr, $negations:expr, $eq:expr, skip_arith_triangle: true) => {{
        let _pemq_eq = &$eq;
        $crate::pipeline_fns::encode_model_equality(
            &mut $self.ctx.terms,
            $solver,
            &mut $term_to_var,
            &mut $var_to_term,
            &mut $next_var,
            &mut $negations,
            _pemq_eq.lhs,
            _pemq_eq.rhs,
            _pemq_eq.implied,
            &_pemq_eq.reason,
            None,
            None::<&mut dyn ay_core::TheorySolver>,
            false,
        );
    }};
    // Variant without dedup set but with theory reference (#8254) — unused.
    ($self:expr, $solver:expr, $term_to_var:expr, $var_to_term:expr,
     $next_var:expr, $negations:expr, $eq:expr, theory: $theory:expr) => {{
        let _pemq_eq = &$eq;
        $crate::pipeline_fns::encode_model_equality(
            &mut $self.ctx.terms,
            $solver,
            &mut $term_to_var,
            &mut $var_to_term,
            &mut $next_var,
            &mut $negations,
            _pemq_eq.lhs,
            _pemq_eq.rhs,
            _pemq_eq.implied,
            &_pemq_eq.reason,
            None,
            Some(&mut $theory),
            true,
        );
    }};
}

/// Build a `TseitinResult` from local maps, run `solve_and_store_model_with_theories`,
/// and break out of the split loop with the result.
///
/// Shared across all 4 split-loop arms (#5814 Packet B). The `pre_store` block
/// runs between TseitinResult construction and the store call — use it for
/// arm-specific cleanup (`solver.pop()`, `theory.unset_terms()`, or `{}`).
macro_rules! pipeline_store_sat_model {
    ($loop_label:lifetime, $self:expr, $solver:expr, $model:expr,
     $local_term_to_var:expr, $local_var_to_term:expr, $local_next_var:expr,
     $timing:expr, $theory:ident, $theory_var:ident, $extract:expr,
     pre_store: { $($pre_store:tt)* }) => {{
        let _psm_extract_start = ay_core::time::Instant::now();
        let $theory_var = &mut $theory;
        let _psm_models = $extract;
        $timing.model_extract += _psm_extract_start.elapsed();

        let _psm_fake_result = ay_core::TseitinResult::new(
            vec![],
            $local_term_to_var.iter().map(|(&t, &v)| (t, v + 1)).collect(),
            $local_var_to_term.iter().map(|(&v, &t)| (v + 1, t)).collect(),
            1,
            $local_next_var,
        );
        $($pre_store)*
        let _psm_store_start = ay_core::time::Instant::now();
        let _psm_store_result = $self.solve_and_store_model_with_theories(
            ay_sat::SatResult::Sat($model), &_psm_fake_result, _psm_models,
        );
        $timing.store_model += _psm_store_start.elapsed();
        break $loop_label _psm_store_result;
    }};
}

/// Build a `TheoryExtension`, run `solve_with_extension`, collect stats, and
/// return `(sat_result, partial_count, pending_split, pending_refinements)`.
///
/// Shared between the eager and eager-persistent split-loop arms (#5814
/// Packet D). The extension construction, SAT solve, and stats collection
/// are character-identical between the two arms.
macro_rules! pipeline_build_eager_extension {
    // #8064: Interruptible variant — the SAT solver checks `should_stop` every
    // 100 conflicts / 1000 decisions and returns Unknown when it fires.
    // Without this, solve_with_extension uses should_stop=||false and the SAT
    // solver has no way to bail out of a non-converging CDCL search within a
    // single split-loop iteration.
    ($self:ident, $solver:expr, $theory:ident,
     $local_var_to_term:expr, $local_term_to_var:expr,
     $active_theory_atoms:expr, $active_theory_atom_set:expr,
     $proof_enabled:expr, $negations:expr,
     $added_refinement_clauses:expr, $added_axioms:expr,
     $eager_stats:expr, $timing:expr, $state:expr,
     should_stop: $should_stop:expr,
     bound_axioms_pre_injected: $axioms_pre_injected:expr,
     bound_axiom_cache_key: $axiom_cache_key:expr) => {{
        // #8103: Skip bound axiom generation+validation on iterations > 0.
        // #8857: Also skip when the per-Executor cache replayed the axioms
        // up front (bound_axioms_pre_injected — mirrors the eager-persistent
        // arm's pipeline_inject_bound_axioms! hoisting).
        let _pbe_skip_axioms = !$added_axioms.is_empty();
        let _pbe_axioms_pre_injected: bool = $axioms_pre_injected;
        let mut _pbe_ext = if _pbe_skip_axioms || _pbe_axioms_pre_injected {
            $crate::extension::TheoryExtension::new_skip_bound_axioms(
                &mut $theory,
                &$local_var_to_term,
                &$local_term_to_var,
                &$active_theory_atoms,
                &$active_theory_atom_set,
                Some(&$self.ctx.terms),
                None,
            )
        } else {
            $crate::extension::TheoryExtension::new(
                &mut $theory,
                &$local_var_to_term,
                &$local_term_to_var,
                &$active_theory_atoms,
                &$active_theory_atom_set,
                Some(&$self.ctx.terms),
                None,
            )
        }
        .with_inline_bound_refinement_replay(&$added_refinement_clauses)
        // T3: forward the executor's wall-clock deadline so propagate_impl()
        // can terminate a diverging theory churn (see extension/propagate.rs).
        .with_solve_deadline($self.solve_deadline.get())
        // #AUFLIA-support: forward the Executor's accumulated unconditional-
        // Forall ground instances so the eager check()/propagate() conflict
        // verifiers can reprove conflicts that depend on them.
        .with_support_axioms($self.active_support_axioms.clone())
        // #uflia-verify-memo: wire the Executor's #4535 semantic-verification
        // memo into the eager conflict verifiers (trust-true-only; failures
        // always re-verify — see TheoryExtension::verify_conflict_semantic_memo).
        .with_verify_memo(&mut $self.conflict_semantic_verify_memo)
        // #verify-memo (AY_VERIFY_MEMO=1): the sampled propagation-verification
        // memo — Executor-owned so accepts survive per-iteration extension
        // rebuilds; inert unless the env flag is armed.
        .with_verify_prop_memo(&mut $self.prop_semantic_verify_memo);
        if $proof_enabled {
            _pbe_ext = _pbe_ext.with_proof_tracking(
                &mut $self.proof_tracker, $negations.as_map(),
            );
        }
        if !_pbe_skip_axioms && !_pbe_axioms_pre_injected {
            // #8857: Capture the generated-and-validated pairs into the
            // per-Executor bound-axiom cache (iteration 0 only — the cache
            // key was computed over the iteration-0 atom set).
            let _pbe_cache_key: Option<u64> = $axiom_cache_key;
            if let Some(_pbe_key) = _pbe_cache_key {
                let (_pbe_pairs, _pbe_farkas) = _pbe_ext.pending_axiom_snapshot();
                $state.bound_axiom_cache =
                    Some($crate::incremental_state::BoundAxiomCache {
                        atom_set_key: _pbe_key,
                        atom_count: $active_theory_atoms.len(),
                        pairs: _pbe_pairs,
                        farkas: _pbe_farkas,
                        validated: true,
                        proof_validated: true,
                    });
            }
            _pbe_ext.retain_new_axioms(&mut $added_axioms);
        }

        let _pbe_sat_start = ay_core::time::Instant::now();
        let _pbe_sat_result = $solver
            .solve_interruptible_with_extension(&mut _pbe_ext, &$should_stop)
            .into_inner();
        let _pbe_sat_elapsed = _pbe_sat_start.elapsed();
        $timing.dpll.sat_solve += _pbe_sat_elapsed;
        if let Some(_pbe_r) = $solver.last_unknown_reason() {
            $self.last_unknown_reason =
                Some($crate::executor::Executor::map_sat_unknown_reason(_pbe_r));
        }

        let _pbe_ext_conflicts = _pbe_ext.num_theory_conflicts();
        let _pbe_ext_propagations = _pbe_ext.num_theory_propagations();
        let _pbe_ext_partial = _pbe_ext.num_partial_clauses();
        $eager_stats.accumulate_from(_pbe_ext.eager_stats());
        let _pbe_pending_split = _pbe_ext.take_pending_split();
        let _pbe_pending_refinements = _pbe_ext.take_pending_bound_refinements();
        drop(_pbe_ext);

        $state.theory_conflicts =
            $state.theory_conflicts.saturating_add(_pbe_ext_conflicts);
        $state.theory_propagations =
            $state.theory_propagations.saturating_add(_pbe_ext_propagations);
        $state.sat_solve_secs = $timing.dpll.sat_solve.as_secs_f64();
        $state.theory_sync_secs = $timing.dpll.theory_sync.as_secs_f64();
        $state.theory_check_secs = $timing.dpll.theory_check.as_secs_f64();
        collect_sat_stats!($self, $solver);
        collect_theory_stats!(incremental: $self, $state);

        (_pbe_sat_result, _pbe_ext_conflicts, _pbe_ext_propagations,
         _pbe_ext_partial, _pbe_pending_split, _pbe_pending_refinements)
    }};
    // #8256: Cached variant for the eager-persistent arm.
    // Uses CachedExtensionData to skip the expensive O(|terms|) ITE scan
    // and O(|vars|) bitset construction on iterations > 0.
    ($self:ident, $solver:expr, $theory:ident,
     $local_var_to_term:expr, $local_term_to_var:expr,
     $active_theory_atoms:expr, $active_theory_atom_set:expr,
     $proof_enabled:expr, $negations:expr,
     $added_refinement_clauses:expr, $added_axioms:expr,
     $eager_stats:expr, $timing:expr, $state:expr,
     should_stop: $should_stop:expr,
     cached_ext_data: $cached:expr,
     use_continue_solving: $use_continue:expr,
     use_resume_solving: $use_resume:expr,
     bound_axioms_pre_injected: $axioms_pre_injected:expr) => {{
        // #8103/#8256: Three-phase extension construction:
        //   1. Iteration > 0 with cached data: new_with_cached_data() — O(1)
        //   2. Iteration 0 with pre-injected axioms: new_skip_bound_axioms()
        //      — builds bitsets/ITE guards but skips the expensive O(axioms)
        //        per-axiom LraSolver validation. The axioms are already in the
        //        SAT solver from pipeline_inject_bound_axioms!().
        //   3. Iteration 0 without pre-injected axioms: new() — full build.
        //
        // Phase 2 is the key optimization for labyrinth-class benchmarks:
        // 33K axioms * fresh LraSolver each = 60+ seconds of validation that
        // was redundant because the axioms were already injected unvalidated.
        let _pbe_skip_axioms = !$added_axioms.is_empty();
        let _pbe_axioms_pre_injected: bool = $axioms_pre_injected;
        let mut _pbe_ext = if _pbe_skip_axioms {
            // Phase 1: Use cached data when available (iteration > 0).
            $crate::extension::TheoryExtension::new_with_cached_data(
                &mut $theory,
                &$local_var_to_term,
                &$local_term_to_var,
                &$active_theory_atoms,
                &$active_theory_atom_set,
                &mut $cached,
            )
        } else if _pbe_axioms_pre_injected {
            // Phase 2: First iteration, but axioms already injected by
            // pipeline_inject_bound_axioms!(). Build bitsets and register
            // atoms, but skip the expensive per-axiom validation.
            $crate::extension::TheoryExtension::new_skip_bound_axioms(
                &mut $theory,
                &$local_var_to_term,
                &$local_term_to_var,
                &$active_theory_atoms,
                &$active_theory_atom_set,
                Some(&$self.ctx.terms),
                None,
            )
        } else {
            // Phase 3: First iteration without pre-injected axioms — full build.
            $crate::extension::TheoryExtension::new(
                &mut $theory,
                &$local_var_to_term,
                &$local_term_to_var,
                &$active_theory_atoms,
                &$active_theory_atom_set,
                Some(&$self.ctx.terms),
                None,
            )
        }
        .with_inline_bound_refinement_replay(&$added_refinement_clauses)
        // T3: forward the executor's wall-clock deadline so propagate_impl()
        // can terminate a diverging theory churn (see extension/propagate.rs).
        .with_solve_deadline($self.solve_deadline.get())
        // #AUFLIA-support: forward the Executor's accumulated unconditional-
        // Forall ground instances so the eager check()/propagate() conflict
        // verifiers can reprove conflicts that depend on them.
        .with_support_axioms($self.active_support_axioms.clone())
        // #uflia-verify-memo: wire the Executor's #4535 semantic-verification
        // memo into the eager conflict verifiers (trust-true-only; failures
        // always re-verify — see TheoryExtension::verify_conflict_semantic_memo).
        .with_verify_memo(&mut $self.conflict_semantic_verify_memo)
        // #verify-memo (AY_VERIFY_MEMO=1): the sampled propagation-verification
        // memo — Executor-owned so accepts survive per-iteration extension
        // rebuilds; inert unless the env flag is armed.
        .with_verify_prop_memo(&mut $self.prop_semantic_verify_memo);
        // #8256: When continuing after a budget-exhausted iteration, the theory
        // solver already has all assertions from the previous iteration (because
        // soft_reset_warm was skipped). Set the trail position to the current
        // trail length so the extension doesn't replay the entire trail through
        // the theory solver. This eliminates O(trail_length) per-atom assertion
        // overhead per budget-exhausted continuation.
        let _pbe_use_continue: bool = $use_continue;
        if _pbe_use_continue {
            let _pbe_trail_len = $solver.trail_len();
            let _pbe_decision_level = $solver.current_decision_level();
            _pbe_ext = _pbe_ext.with_warm_trail_position(_pbe_trail_len, _pbe_decision_level);
        }
        if $proof_enabled {
            _pbe_ext = _pbe_ext.with_proof_tracking(
                &mut $self.proof_tracker, $negations.as_map(),
            );
        }
        if !_pbe_skip_axioms && !_pbe_axioms_pre_injected {
            _pbe_ext.retain_new_axioms(&mut $added_axioms);
        }

        let _pbe_sat_start = ay_core::time::Instant::now();
        // #8256: Budget-exhausted continuation strategies.
        //
        // Three modes, in order of preference:
        //   1. resume_solving — O(1), re-enters CDCL loop without any state reset.
        //      Used for the first budget-exhausted continuation. Preserves the
        //      entire trail, all learned clauses, VSIDS/CHB state. The theory
        //      extension has warm_trail_position set to skip assertion replay.
        //   2. continue_solving — O(trail + learned), resets trail and flushes
        //      non-core learned clauses. Used as fallback when resume_solving
        //      stalls (3 consecutive budget-exhausted iterations with < 50
        //      conflict progress). This breaks out of stuck search regions.
        //   3. solve_interruptible — full solve. Used for iteration 0 and
        //      after splits/refinements change the clause set.
        let _pbe_use_resume: bool = $use_resume;
        let _pbe_sat_result = if _pbe_use_resume {
            $solver
                .resume_solving_with_extension(&mut _pbe_ext, &$should_stop)
                .into_inner()
        } else if _pbe_use_continue {
            $solver
                .continue_solving_with_extension(&mut _pbe_ext, &$should_stop)
                .into_inner()
        } else {
            $solver
                .solve_interruptible_with_extension(&mut _pbe_ext, &$should_stop)
                .into_inner()
        };
        let _pbe_sat_elapsed = _pbe_sat_start.elapsed();
        $timing.dpll.sat_solve += _pbe_sat_elapsed;
        if let Some(_pbe_r) = $solver.last_unknown_reason() {
            $self.last_unknown_reason =
                Some($crate::executor::Executor::map_sat_unknown_reason(_pbe_r));
        }

        let _pbe_ext_conflicts = _pbe_ext.num_theory_conflicts();
        let _pbe_ext_propagations = _pbe_ext.num_theory_propagations();
        let _pbe_ext_partial = _pbe_ext.num_partial_clauses();
        $eager_stats.accumulate_from(_pbe_ext.eager_stats());
        let _pbe_pending_split = _pbe_ext.take_pending_split();
        let _pbe_pending_refinements = _pbe_ext.take_pending_bound_refinements();
        // #8256: Save cached data back for the next iteration.
        $cached = _pbe_ext.take_cached_data();
        drop(_pbe_ext);

        $state.theory_conflicts =
            $state.theory_conflicts.saturating_add(_pbe_ext_conflicts);
        $state.theory_propagations =
            $state.theory_propagations.saturating_add(_pbe_ext_propagations);
        $state.sat_solve_secs = $timing.dpll.sat_solve.as_secs_f64();
        $state.theory_sync_secs = $timing.dpll.theory_sync.as_secs_f64();
        $state.theory_check_secs = $timing.dpll.theory_check.as_secs_f64();
        collect_sat_stats!($self, $solver);
        collect_theory_stats!(incremental: $self, $state);

        (_pbe_sat_result, _pbe_ext_conflicts, _pbe_ext_propagations,
         _pbe_ext_partial, _pbe_pending_split, _pbe_pending_refinements)
    }};
}
