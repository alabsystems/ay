// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared composable macros for the active DPLL(T) pipelines.
//!
//! After the final `pipeline_macros.rs` retirement (#6688/#6659), this module
//! holds the still-live stats collection, incremental setup, and split-loop
//! timing export macros.
//!
//! These are `macro_rules!` (not functions) for the same borrow-checker reason
//! as the pipeline code they support: theory executors hold `&self.ctx.terms`
//! through `DpllT`, so `&mut self` method calls on `Executor` would conflict.

/// Thin shim over [`crate::pipeline_fns::collect_sat_stats_snapshot`].
///
/// The collection logic was de-macro'd into that function. This macro survives
/// only to capture the private `Executor::last_statistics` /
/// `Executor::pending_sat_unknown_reason` fields and to call the SAT solver's
/// by-value getters here (so a disjoint `&mut` borrow of the solver at the call
/// site is preserved). It must remain a write-only snapshot with NO assertions
/// (guarded by `test_collect_sat_stats_macro_contains_no_assertions`, #4756,
/// #4804): phase-sensitive checks belong in the `stats_contract.rs` finalize
/// helpers.
macro_rules! collect_sat_stats {
    ($self:ident, $sat:expr) => {
        $crate::pipeline_fns::collect_sat_stats_snapshot(
            &mut $self.last_statistics,
            &mut $self.pending_sat_unknown_reason,
            $crate::pipeline_fns::SatStatsSnapshot {
                // #qfuflia-stats: lifetime-inclusive counters — the split
                // loop resets per-solve counters every round, so the plain
                // `num_*` getters report only the LAST round.
                conflicts: ($sat).total_num_conflicts(),
                decisions: ($sat).total_num_decisions(),
                propagations: ($sat).total_num_propagations(),
                restarts: ($sat).total_num_restarts(),
                learned_clauses: ($sat).num_learned_clauses(),
                deleted_clauses: ($sat).num_learned_clauses_deleted(),
                // #stats-cnf: CNF shape of the INPUT problem. Both were declared,
                // exposed and printed but never assigned, so `-st` always said 0
                // and the only way to see the encoding's size was to instrument
                // `add_clause` by hand. `num_original_clauses` (not `num_clauses`)
                // is the right source: the latter is the live database and grows
                // with learned clauses, which is what `:learned-clauses` reports.
                num_vars: ($sat).num_variables() as u64,
                num_clauses: ($sat).num_original_clauses() as u64,
                unknown_reason: ($sat).last_unknown_reason(),
            },
        );
    };
}

/// Thin shim over [`crate::incremental_state::collect_theory_stats_incremental`].
///
/// The collection logic was de-macro'd into that function (#4705); this macro
/// survives only to snapshot the round's `Copy` stat fields (disjoint field
/// reads, so a live `&mut $state` borrow elsewhere is unaffected) and to capture
/// the private `$self.last_statistics` field at the call site.
macro_rules! collect_theory_stats {
    (incremental: $self:ident, $state:expr) => {
        $crate::incremental_state::collect_theory_stats_incremental(
            &mut $self.last_statistics,
            $crate::incremental_state::IncrementalTheoryStats {
                theory_conflicts: $state.theory_conflicts,
                theory_propagations: $state.theory_propagations,
                round_trips: $state.round_trips,
                sat_solve_secs: $state.sat_solve_secs,
                theory_sync_secs: $state.theory_sync_secs,
                theory_check_secs: $state.theory_check_secs,
            },
        )
    };
}

macro_rules! collect_observability_stats_from_dpll {
    ($self:ident, $dpll:expr) => {
        $crate::pipeline_fns::collect_observability_stats_from_dpll(
            &mut $self.last_statistics,
            $crate::pipeline_fns::DpllObservabilityStats {
                theory_unknown_count: ($dpll).num_theory_unknowns(),
                partial_clause_count: ($dpll).num_partial_clauses(),
                conflict_max_literals: ($dpll).conflict_max_literals(),
                conflict_total_literals: ($dpll).conflict_total_literals(),
                theory_minimize_lits_removed: ($dpll).theory_minimize_lits_removed(),
                farkas_certificate_failures: ($dpll).farkas_certificate_failures(),
                farkas_certificate_downgrades: ($dpll).farkas_certificate_downgrades(),
                semantic_verify_budget_skips: ($dpll).semantic_verify_budget_skips(),
                sync_atoms_asserted: ($dpll).sync_atoms_asserted(),
                sync_skipped_identical: ($dpll).sync_skipped_identical(),
                sync_delta_changed: ($dpll).sync_delta_changed(),
                sync_delta_unchanged: ($dpll).sync_delta_unchanged(),
            },
            ay_core::TheorySolver::collect_statistics(($dpll).theory_solver()),
        );
    };
}

macro_rules! collect_observability_stats_from_theory {
    ($self:ident, $theory_stats:expr) => {
        $crate::pipeline_fns::collect_observability_stats_from_theory(
            &mut $self.last_statistics,
            &$theory_stats,
        )
    };
}

/// Common incremental pipeline setup: find new assertions, Tseitin-encode them,
/// initialize or reuse the persistent SAT solver, add assertion clauses, and
/// re-activate roots after pop().
///
/// This is the shared first phase of `solve_incremental_theory_pipeline` and
/// `solve_incremental_split_loop_pipeline`, which was duplicated (~120 lines)
/// with only the SAT solver field and solver-init hook differing.
///
/// After this macro expands, the following output bindings are live in the caller:
/// - `$new_assertion_set`: `HashSet<TermId>` (needed by some callers for dedup)
/// - `$solver_out`: `SatSolver` — the persistent SAT solver, taken out of state
/// - `$tseitin_out`: `Tseitin` — still live, caller must call `.into_state()`
/// - `$var_to_term`: `HashMap<u32, TermId>` — 0-indexed var-to-term map
/// - `$term_to_var`: `HashMap<TermId, u32>` — 0-indexed term-to-var map
///
/// The caller is responsible for:
/// 1. Storing `$solver_out` back into `$state.$sat_field` when done
///
/// All identifiers must be passed as parameters (Rust macro hygiene):
/// - `$self`: the `Executor`
/// - `$state`: the `&mut IncrementalTheoryState`
/// - `$proof_enabled`: the proof flag
/// - `$tag`: string tag for debug messages
/// - `$sat_field`: field on `IncrementalTheoryState` holding the SAT solver
/// - `solver_init`: hook block executed when a fresh solver is created
/// - `out`: tuple of output binding names
macro_rules! pipeline_incremental_setup {
    (
        $self:ident, $state:ident, $proof_enabled:ident, $random_seed:expr, $tag:expr,
        sat_field: $sat_field:ident,
        tseitin_field: $tseitin_field:ident,
        encoded_field: $encoded_field:ident,
        activation_scope_field: $activation_scope_field:ident,
        solver_init: $solver_init:block,
        out: ($new_assertion_set:ident, $solver_out:ident, $tseitin_out:ident,
              $var_to_term:ident, $term_to_var:ident, $pending_out:ident)
    ) => {
        // Find assertions that need to be Tseitin-transformed
        let $new_assertion_set: HashSet<TermId> = {
            let mut _pis_seen = HashSet::default();
            let _pis_new: Vec<TermId> = $self
                .ctx
                .assertions
                .iter()
                .copied()
                .filter(|term| !$state.$encoded_field.contains_key(term))
                .filter(|term| _pis_seen.insert(*term))
                .collect();
            _pis_new.iter().copied().collect()
        };
        let _pis_new_assertions: Vec<TermId> =
            $new_assertion_set.iter().copied().collect();
        let _pis_assertion_depths = $self.ctx.active_assertion_min_scope_depths();

        // Lift arithmetic ITEs from new assertions
        let _pis_lifted = $self.ctx.terms.lift_arithmetic_ite_all(&_pis_new_assertions);

        // Sync per-solver Tseitin state: advance next_var past this solver's
        // total_num_vars to avoid collisions with scope selectors (#6853).
        if let Some(ref sat) = $state.$sat_field {
            let sat_total =
                u32::try_from(sat.total_num_vars()).expect("SAT solver vars fit u32");
            $state.$tseitin_field.next_var = $state.$tseitin_field.next_var.max(sat_total + 1);
        }

        // When the SAT solver for this pipeline doesn't exist yet, its
        // initialization will push `scope_depth` scope selectors at variable
        // indices starting at num_vars. Reserve space for them (#6853).
        if $state.$sat_field.is_none() && $state.scope_depth > 0 {
            let _pis_reserve = $state.scope_depth as u32;
            $state.$tseitin_field.next_var += _pis_reserve;
        }

        let mut $tseitin_out = if $proof_enabled {
            Tseitin::from_state_with_proofs(
                &$self.ctx.terms,
                std::mem::take(&mut $state.$tseitin_field),
            )
        } else {
            Tseitin::from_state(&$self.ctx.terms, std::mem::take(&mut $state.$tseitin_field))
        };

        // Encode new assertions
        let _pis_encoded: Vec<(TermId, TseitinEncodedAssertion)> = _pis_new_assertions
            .iter()
            .zip(_pis_lifted.iter())
            .map(|(&orig, &lifted)| (orig, $tseitin_out.encode_assertion(lifted)))
            .collect();

        let _pis_total_vars = $tseitin_out.num_vars();

        // Initialize or resize persistent SAT solver
        let _pis_solver_is_new;
        let mut $solver_out = if let Some(s) = $state.$sat_field.take() {
            _pis_solver_is_new = false;
            s
        } else {
            _pis_solver_is_new = true;
            let mut sat = SatSolver::new(_pis_total_vars as usize);
            sat.set_random_seed($random_seed);
            // Mirror DpllT::from_tseitin so SMT incremental pipelines honor
            // AY_TRACE_FILE JSONL emission as soon as the persistent SAT solver
            // is created.
            ay_sat::TlaTraceable::maybe_enable_tla_trace_from_env(&mut sat);
            // Part of EXPLAINABILITY_AUDIT.md Finding B: honor the
            // `--decision-trace` / `AY_DECISION_TRACE_FILE` setting so SMT
            // pipelines emit the full SAT decision stream, not just the
            // CLI-level minimal fallback. The CLI still writes a minimal
            // sentinel when the SAT solver never runs (preprocessing-only
            // UNSAT), but when it does run we want the complete event log.
            sat.maybe_enable_decision_trace_from_env();
            if $proof_enabled {
                sat.enable_clause_trace();
                sat.set_proof_bookkeeping_budget(crate::executor::Executor::search_proof_bookkeeping_budget_for(&$self.ctx, $self.proof_reconstruction_step_budget));
            }
            if let Some(seed) = $self.random_seed {
                sat.set_random_seed(seed);
            }
            if $self.progress_enabled {
                sat.set_progress_enabled(true);
            }
            if let Some(path) = &$self.progress_json_path {
                if let Ok(obs) = ay_sat::json_observer::JsonProgressObserver::new_append(path) {
                    sat.set_observer(Some(Box::new(obs)));
                }
            }
            // Adaptive reorder gate for large incremental instances (#8118).
            if _pis_total_vars as usize > 50_000 {
                sat.set_reorder_enabled(false);
            }
            sat
        };
        $solver_out.ensure_num_vars(_pis_total_vars as usize);
        // Rebind the exact public query's cooperative interrupt on every use.
        // The SAT solver is persistent across SMT queries; retaining an older
        // handle would either miss the current timeout or let a later-fired
        // watchdog poison a subsequent query.
        $solver_out.set_interrupt_handle($self.solve_interrupt.clone());

        // If solver was just created, run the init hook for scope synchronization
        if _pis_solver_is_new {
            $state.$sat_field = Some($solver_out);
            $solver_init
            $solver_out = $state
                .$sat_field
                .take()
                .expect(concat!(
                    "incremental ", $tag,
                    " should preserve persistent SAT solver across init"
                ));
        }

        let _pis_cnf_to_sat = $crate::cnf_lit_to_sat;

        // #6853: Collect pending activations instead of adding them directly.
        let mut $pending_out: Vec<(SatLiteral, usize)> = Vec::new();

        // Add encoded assertions: definitions globally, activations deferred
        for (_pis_term, _pis_enc) in _pis_encoded {
            let TseitinEncodedAssertion {
                root_lit: _pis_root_lit,
                def_clauses: _pis_def_clauses,
                def_proof_annotations: _pis_def_proof_annotations,
            } = _pis_enc;

            if $proof_enabled {
                let _pis_annotations = _pis_def_proof_annotations
                    .as_ref()
                    .expect("proof-enabled incremental Tseitin encoding should carry annotations");
                debug_assert_eq!(
                    _pis_annotations.len(),
                    _pis_def_clauses.len(),
                    "incremental clause annotations must stay aligned with SAT clause order"
                );
                for (_pis_idx, clause) in _pis_def_clauses.iter().enumerate() {
                    let lits: Vec<SatLiteral> = clause
                        .literals()
                        .iter()
                        .map(|&lit| _pis_cnf_to_sat(lit))
                        .collect();
                    $solver_out.add_clause_global(lits);
                    $state
                        .clausification_proofs
                        .push(_pis_annotations[_pis_idx].clone());
                    $state.original_clause_theory_proofs.push(None);
                }
            } else {
                for clause in &_pis_def_clauses {
                    let lits: Vec<SatLiteral> = clause
                        .literals()
                        .iter()
                        .map(|&lit| _pis_cnf_to_sat(lit))
                        .collect();
                    $solver_out.add_clause_global(lits);
                }
            }

            let _pis_root = _pis_cnf_to_sat(_pis_root_lit);
            freeze_var_if_needed(&mut $solver_out, _pis_root.variable());
            let _pis_activation_depth =
                $state.desired_activation_depth(_pis_term, &_pis_assertion_depths);
            // Activation clause: force the Tseitin root variable true.
            // Global (depth 0) activations MUST use add_clause_global so they
            // survive SMT-level pop operations. Making them scoped causes model
            // validation failures in LRA/EUF incremental push/pop scenarios.
            if _pis_activation_depth == 0 {
                $solver_out.add_clause_global(vec![_pis_root]);
            } else {
                $solver_out.add_clause_at_scope_depth(vec![_pis_root], _pis_activation_depth);
            }
            if $proof_enabled {
                $state.clausification_proofs.push(None);
                $state.original_clause_theory_proofs.push(None);
            }

            $state.$encoded_field.insert(_pis_term, _pis_root_lit);
            $state
                .$activation_scope_field
                .insert(_pis_term, _pis_activation_depth);
        }

        // Re-activate currently asserted roots only after a pop()
        if $state.needs_activation_reassert {
            let mut _pis_seen_active = HashSet::default();
            for &assertion in &$self.ctx.assertions {
                if !_pis_seen_active.insert(assertion) {
                    continue;
                }
                if $new_assertion_set.contains(&assertion) {
                    continue;
                }
                if $state
                    .$activation_scope_field
                    .get(&assertion)
                    .copied()
                    .is_some_and(|depth| {
                        depth
                            <= $state.desired_activation_depth(assertion, &_pis_assertion_depths)
                    })
                {
                    continue;
                }
                if let Some(&root_lit) = $state.$encoded_field.get(&assertion) {
                    let _pis_root = _pis_cnf_to_sat(root_lit);
                    let _pis_activation_depth =
                        $state.desired_activation_depth(assertion, &_pis_assertion_depths);
                    freeze_var_if_needed(&mut $solver_out, _pis_root.variable());
                    // Defer re-activation to inside the private push scope (#6853)
                    $pending_out.push((_pis_root, _pis_activation_depth));
                    $state
                        .$activation_scope_field
                        .insert(assertion, _pis_activation_depth);
                }
            }
            $state.needs_activation_reassert = false;
        }

        // #3762/#8935: Import SAT warm state only after the fresh solver's
        // original-clause ledger reflects the current formula. The v2
        // fingerprint gate imports learned clauses only for exact replay;
        // mismatches still seed heuristic activity/phase hints.
        if _pis_solver_is_new {
            if let Some(warm) = $state.sat_warm_state.take() {
                if !warm.is_empty() {
                    let _import_report = warm.import_into_with_report(&mut $solver_out);
                    tracing::info!(
                        imported_clauses = _import_report.imported_learned_clauses,
                        activities = _import_report.variable_activity_hints,
                        phase_hints = _import_report.phase_hints,
                        guidance_level = %_import_report.decision.level,
                        guidance_reason = %_import_report.decision.reason,
                        prior_conflicts = warm.prior_conflicts,
                        concat!("Incremental ", $tag, " imported SAT warm state (#3762, #8935)")
                    );
                }
            }
        }

        // Build var_to_term and term_to_var maps (convert 1-indexed to 0-indexed)
        let $var_to_term: HashMap<u32, TermId> = $tseitin_out
            .var_to_term()
            .iter()
            .map(|(&v, &t)| (v - 1, t))
            .collect();
        let $term_to_var: HashMap<TermId, u32> = $tseitin_out
            .term_to_var()
            .iter()
            .map(|(&t, &v)| (t, v - 1))
            .collect();
    };
}

/// Thin shim over [`crate::pipeline_fns::apply_pending_activations`].
///
/// Apply pending activation clauses inside a private push scope (#6853).
/// The call site holds `solver = &mut $state.<sat_field>`; this shim hands that
/// reborrow plus the DISJOINT `$state.clausification_proofs` /
/// `$state.original_clause_theory_proofs` fields to the function as separate
/// `&mut` params, never borrowing the whole `$state`.
macro_rules! pipeline_apply_pending_activations {
    ($solver:expr, $pending:expr, $proof_enabled:expr,
     $state:expr) => {
        $crate::pipeline_fns::apply_pending_activations(
            $solver,
            &$pending,
            $proof_enabled,
            &mut $state.clausification_proofs,
            &mut $state.original_clause_theory_proofs,
        )
    };
}

/// Apply pending activation clauses immediately at their desired depth (#6853).
macro_rules! pipeline_apply_pending_activations_immediate {
    ($solver:expr, $pending:expr, $proof_enabled:expr,
     $state:expr) => {
        $crate::pipeline_fns::apply_pending_activations_immediate(
            $solver,
            &$pending,
            $proof_enabled,
            &mut $state.clausification_proofs,
            &mut $state.original_clause_theory_proofs,
        )
    };
}

macro_rules! pipeline_reactivate_all_in_scope {
    ($self:expr, $solver:expr, $state:expr, $pending:expr,
     $proof_enabled:expr, $encoded_field:ident) => {{
        $crate::pipeline_fns::reactivate_all_in_scope(
            $solver,
            &$self.ctx.assertions,
            &$state.$encoded_field,
            &$pending,
            $proof_enabled,
            &mut $state.clausification_proofs,
            &mut $state.original_clause_theory_proofs,
        )
    }};
}

/// Thin shim over [`crate::pipeline_fns::export_split_loop_timing_stats`].
///
/// Survives only to capture the private `$self.last_statistics` field and to
/// build a `Copy` [`crate::pipeline_fns::SplitLoopTimingStatsSnapshot`] from
/// disjoint Copy field reads of `$stats` (a `SplitLoopTimingStats`, which is
/// only `Clone`). Never passes `&$stats` or `&mut $self` whole.
macro_rules! pipeline_export_split_loop_timing_stats {
    ($self:ident, $stats:expr) => {
        $crate::pipeline_fns::export_split_loop_timing_stats(
            &mut $self.last_statistics,
            $crate::pipeline_fns::SplitLoopTimingStatsSnapshot {
                sat_solve: ($stats).dpll.sat_solve,
                theory_sync: ($stats).dpll.theory_sync,
                theory_check: ($stats).dpll.theory_check,
                round_trips: ($stats).dpll.round_trips,
                model_extract: ($stats).model_extract,
                store_model: ($stats).store_model,
                total: ($stats).total,
            },
        );
    };
}

/// Export theory learned state (cuts, HNF cuts, Dioph state) from a theory
/// instance into local variables. Shared across all split-loop arms.
///
/// Extracted by #5814 Packet 2 to eliminate ~20 duplicate 5-line blocks
/// across eager, eager-persistent, and lazy-shared macro files.
macro_rules! pipeline_export_theory_state {
    ($theory:expr, $export_theory:ident, $export_expr:expr,
     $learned_cuts:expr, $seen_hnf_cuts:expr, $dioph_state:expr) => {{
        let $export_theory = &mut $theory;
        let (_ec, _eh, _ed) = $export_expr;
        $learned_cuts = _ec;
        $seen_hnf_cuts = _eh;
        $dioph_state = _ed;
    }};
}

/// Capture proof state, pop solver, and break with UNSAT for lazy/assume arms.
///
/// Shared between the lazy and assume split-loop arms. These arms use push/pop
/// scoping and must clone proof state before popping. The eager arms use a
/// different macro (`pipeline_incremental_split_eager_build_unsat_proof!`) that
/// skips the pop.
///
/// Extracted by #5814 Packet 3 to eliminate duplicate UNSAT proof capture code.
macro_rules! pipeline_build_unsat_proof_with_pop {
    ($loop_label:lifetime, $self:ident, $solver:ident,
     $local_var_to_term:ident, $negations:ident, $proof_enabled:ident,
     $local_clausification_proofs:ident, $local_theory_proofs:ident
    ) => {
        $self.last_model = None;
        if $proof_enabled {
            $negations.sync_pending(&mut $self.ctx.terms);
            let _bup_clause_trace = $solver.clause_trace().cloned();
            let (_bup_cp, _bup_tp) = {
                if let Some(ref _bup_trace) = _bup_clause_trace {
                    let _bup_oc = _bup_trace.original_clauses().count();
                    if $local_clausification_proofs.len() < _bup_oc {
                        $local_clausification_proofs.resize(_bup_oc, None);
                    }
                    if $local_theory_proofs.len() < _bup_oc {
                        $local_theory_proofs.resize(_bup_oc, None);
                    }
                }
                (
                    $local_clausification_proofs.clone(),
                    $local_theory_proofs.clone(),
                )
            };
            let _bup_vtm = $local_var_to_term.clone();
            let _bup_neg = $negations.as_map().clone();
            let _ = $solver.pop();
            $self.last_clause_trace = _bup_clause_trace;
            $self.last_clausification_proofs = Some(_bup_cp);
            $self.last_original_clause_theory_proofs = Some(_bup_tp);
            $crate::pipeline_fns::record_var_map_provenance("setup", &$solver, _bup_vtm.len());
            $self.last_var_to_term = Some(_bup_vtm);
            $self.last_negations = Some(_bup_neg);
            $self.build_unsat_proof();
        } else {
            let _ = $solver.pop();
        }
        $self.last_result = Some(SolveResult::unsat());
        break $loop_label Ok(SolveResult::unsat());
    };
}

macro_rules! pipeline_add_bound_axiom_clauses {
    ($self:expr, $solver:expr, $term_to_var:expr, $proof_enabled:expr,
     $axiom_pairs:expr, $farkas_store:expr, $from_cache:expr,
     $local_clausification_proofs:expr, $local_original_clause_theory_proofs:expr) => {{
        $crate::pipeline_fns::pipeline_add_bound_axiom_clauses(
            &mut $self.ctx.terms,
            &mut $self.proof_tracker,
            $solver,
            &$term_to_var,
            $proof_enabled,
            &$axiom_pairs,
            &mut $farkas_store,
            $from_cache,
            &mut $local_clausification_proofs,
            &mut $local_original_clause_theory_proofs,
        )
    }};
}

macro_rules! pipeline_inject_bound_axioms {
    ($self:expr, $solver:expr, $base_active_atoms:expr, $base_term_to_var:expr,
     $create_theory:expr, $proof_enabled:expr, $tag:expr,
     $local_clausification_proofs:expr, $local_original_clause_theory_proofs:expr,
     $state:expr) => {{
        let _ba_atom_count = $base_active_atoms.len();
        // Fix 3 Layer A (#8857): per-Executor bound-axiom cache. Generation
        // is a pure function of the active atom set (fresh theory, no
        // assertions), so cached pairs can be replayed for an identical atom
        // set, skipping axiom-theory construction, generation, AND the
        // per-pair tautology validation. The cache therefore stores ONLY the
        // validated subset (`validated: true`); a replay requires both
        // `validated` and (in proof mode) `proof_validated` so an unsound pair
        // can never re-enter the SAT solver via the cache (efccf96/seed-981).
        let _ba_key =
            $crate::incremental_state::bound_axiom_atom_set_key($base_active_atoms.iter().copied());
        let mut _ba_cached: Option<(
            Vec<(ay_core::TermId, bool, ay_core::TermId, bool)>,
            Vec<Option<ay_core::FarkasAnnotation>>,
        )> = None;
        if let Some(_ba_c) = $state.bound_axiom_cache.as_ref() {
            if _ba_c.atom_set_key == _ba_key
                && _ba_c.atom_count == _ba_atom_count
                && _ba_c.validated
                && (!$proof_enabled || _ba_c.proof_validated)
            {
                _ba_cached = Some((_ba_c.pairs.clone(), _ba_c.farkas.clone()));
            }
        }
        let _ba_from_cache = _ba_cached.is_some();
        // `_axiom_rejected` counts non-tautology pairs filtered by the
        // soundness gate below (always 0 on a cache hit — the cache only holds
        // validated pairs).
        let mut _axiom_rejected = 0usize;
        let (axiom_pairs, mut _ba_farkas_store) = match _ba_cached {
            Some((_ba_p, _ba_f)) => {
                tracing::debug!(
                    registered_atoms = _ba_atom_count,
                    axiom_pairs = _ba_p.len(),
                    concat!("Bound axiom cache hit (#8857) for ", $tag)
                );
                (_ba_p, _ba_f)
            }
            None => {
                let mut axiom_theory = $create_theory;
                for &atom in &$base_active_atoms {
                    ay_core::TheorySolver::register_atom(&mut axiom_theory, atom);
                }
                ay_core::TheorySolver::sort_atom_index(&mut axiom_theory);
                let _ba_generated =
                    ay_core::TheorySolver::generate_bound_axiom_terms(&axiom_theory);
                tracing::info!(
                    registered_atoms = _ba_atom_count,
                    axiom_pairs = _ba_generated.len(),
                    term_to_var_size = $base_term_to_var.len(),
                    concat!("Bound axiom injection diagnostic (#8452) for ", $tag)
                );
                // Soundness gate (#6242, #6564; efccf96/seed-981): validate
                // every generated pair before injection. The clause
                // (t1^p1 ∨ t2^p2) must be a tautology, i.e. ¬(t1^p1) ∧ ¬(t2^p2)
                // must be UNSAT in a fresh LRA solver. The single-shot path
                // (extension/construction.rs) has run this gate since #6564;
                // the incremental injection skipped it, so an unsound generated
                // axiom (integer-trichotomy between fractional bounds, seed 981)
                // reached the SAT solver only on the push/pop path and produced
                // a false UNSAT there. We keep only the validated subset, so a
                // later cache replay (which skips validation) stays sound. The
                // check also yields the Farkas certificate reused for proofs.
                let mut _ba_validated_pairs: Vec<(
                    ay_core::TermId,
                    bool,
                    ay_core::TermId,
                    bool,
                )> = Vec::with_capacity(_ba_generated.len());
                let mut _ba_validated_farkas: Vec<Option<ay_core::FarkasAnnotation>> =
                    Vec::with_capacity(_ba_generated.len());
                for (t1, p1, t2, p2) in _ba_generated {
                    let mut check_lra = ay_lra::LraSolver::new(&$self.ctx.terms);
                    // #8373: abstract non-arithmetic operands (e.g. `select(arr,i)`
                    // array reads that appear inside an Int-sorted bound-axiom pair)
                    // as opaque Nelson-Oppen variables instead of marking them
                    // "unsupported" and downgrading Sat->Unknown. Opaque abstraction
                    // is a RELAXATION, so a resulting Unsat still implies real Unsat
                    // (the kept axiom stays a genuine tautology, now WITH a Farkas
                    // certificate); a resulting Sat correctly REJECTS a
                    // non-tautological pair the bare solver previously kept-on-Unknown
                    // (strictly sounder). Without this, UF/array-bearing pairs return
                    // Unknown -> were kept without a certificate, starving downstream
                    // proofs and burning the validation loop (index_range: 260x).
                    check_lra.set_combined_theory_mode(true);
                    ay_core::TheorySolver::assert_literal(&mut check_lra, t1, !p1);
                    ay_core::TheorySolver::assert_literal(&mut check_lra, t2, !p2);
                    let check_result = ay_core::TheorySolver::check(&mut check_lra);
                    drop(check_lra);
                    if matches!(check_result, ay_core::TheoryResult::Sat) {
                        _axiom_rejected += 1;
                        tracing::warn!(
                            term1 = ?t1,
                            pol1 = p1,
                            term2 = ?t2,
                            pol2 = p2,
                            concat!(
                                "Rejected unsound bound axiom at incremental ",
                                "injection (#6242, seed-981) for ",
                                $tag
                            )
                        );
                        continue;
                    }
                    let _ba_pair_farkas = match check_result {
                        ay_core::TheoryResult::UnsatWithFarkas(conflict) => {
                            $crate::pipeline_fns::rebind_bound_axiom_farkas(
                                conflict,
                                &[(t1, !p1), (t2, !p2)],
                            )
                        }
                        _ => None,
                    };
                    _ba_validated_pairs.push((t1, p1, t2, p2));
                    _ba_validated_farkas.push(_ba_pair_farkas);
                }
                (_ba_validated_pairs, _ba_validated_farkas)
            }
        };
        // Pairs are pre-validated here (cache hit, or freshly validated above)
        // and `_ba_farkas_store` is already populated, so pass `from_cache:
        // true` to reuse the certificates instead of re-running the LRA check.
        let (axiom_count, _axiom_dropped) = pipeline_add_bound_axiom_clauses!(
            $self,
            $solver,
            $base_term_to_var,
            $proof_enabled,
            axiom_pairs,
            _ba_farkas_store,
            true,
            $local_clausification_proofs,
            $local_original_clause_theory_proofs
        );
        // #8857: Store the validated generation results in the per-Executor
        // cache. Only tautology pairs survive the soundness gate above, so the
        // cache is `validated: true` and safe for the eager arm and for this
        // macro's own (validation-skipping) replay path.
        if !_ba_from_cache {
            $state.bound_axiom_cache = Some($crate::incremental_state::BoundAxiomCache {
                atom_set_key: _ba_key,
                atom_count: _ba_atom_count,
                pairs: axiom_pairs,
                farkas: _ba_farkas_store,
                validated: true,
                proof_validated: $proof_enabled,
            });
        }
        if axiom_count > 0 || _axiom_dropped > 0 || _axiom_rejected > 0 {
            tracing::info!(
                axiom_count,
                axiom_dropped = _axiom_dropped,
                axiom_rejected = _axiom_rejected,
                theory_atoms = $base_active_atoms.len(),
                concat!("Incremental ", $tag, " bound axiom injection (#6579)")
            );
        }
    }};
}

macro_rules! pipeline_export_split_loop_eager_stats {
    ($self:ident, $stats:expr) => {
        $crate::pipeline_fns::export_split_loop_eager_stats(&mut $self.last_statistics, &($stats));
    };
}

macro_rules! pipeline_register_proof_context {
    ($self:expr, $proof_enabled:expr, $tag:expr) => {{
        let problem_assertions = $self.proof_problem_assertions();
        pipeline_register_proof_context!(
            $self,
            $proof_enabled,
            $tag,
            problem_assertions: problem_assertions
        );
    }};
    ($self:expr, $proof_enabled:expr, $tag:expr, problem_assertions: $problem_assertions:expr) => {{
        pipeline_register_proof_context!(
            $self,
            $proof_enabled,
            $tag,
            problem_assertions: $problem_assertions,
            assumptions: &[]
        );
    }};
    ($self:expr, $proof_enabled:expr, $tag:expr,
     problem_assertions: $problem_assertions:expr, assumptions: $assumptions:expr) => {{
        // Read disjoint immutable self-fields into a Copy bool / owned Vec
        // BEFORE taking the &mut proof_tracker borrow (avoids E0502).
        let __prpc_has_provenance = $self.proof_problem_assertion_provenance.is_some();
        let __prpc_problem_assertions: Vec<ay_core::TermId> = $problem_assertions;
        let __prpc_assumptions: &[(ay_core::TermId, ay_core::TermId)] = $assumptions;
        // &mut $self.proof_tracker and &$self.ctx.assertions are DISJOINT fields,
        // so this simultaneous borrow is accepted by the borrow checker.
        $crate::pipeline_fns::register_proof_context(
            &mut $self.proof_tracker,
            $proof_enabled,
            $tag,
            __prpc_has_provenance,
            &$self.ctx.assertions,
            __prpc_problem_assertions,
            __prpc_assumptions,
        );
    }};
}

/// Clone split-local proof ledgers from incremental state (#5814 Packet A).
///
/// Owns exactly: cloning `state.clausification_proofs` and
/// `state.original_clause_theory_proofs` into split-loop locals.
///
/// Returns `(Vec<Option<ClausificationProof>>, Vec<Option<TheoryLemmaProof>>)`.
/// Export timing stats, theory stats, and optionally eager stats and
/// state restore at the end of a split-loop arm.
///
/// Shared across all 4 split-loop arms (#5814 Packet C). The `eager` block
/// is for `pipeline_export_split_loop_eager_stats!` (eager/eager-persistent only).
/// The `restore` block is for `$self.incr_theory_state = Some(state)` (lazy/eager
/// only, where state was taken via `.take()`).
macro_rules! pipeline_split_epilogue {
    ($self:ident, $timing:expr, $total_start:expr,
     $last_theory_stats:expr, $result:expr,
     eager: { $($eager:tt)* }, restore: { $($restore:tt)* }) => {{
        $timing.total = $total_start.elapsed();
        pipeline_export_split_loop_timing_stats!($self, $timing);
        $($eager)*
        $self.last_statistics.set_int("dpll.rebuilds", 0);
        collect_observability_stats_from_theory!($self, $last_theory_stats);
        for (name, value) in &$last_theory_stats {
            $self.last_statistics.set_int(name, *value);
        }
        $($restore)*
        $result
    }};
}

/// Used only by the four split arms (not the no-split incremental macro).
macro_rules! pipeline_clone_local_proof_ledgers {
    ($state:expr, $proof_enabled:expr) => {{
        $crate::pipeline_fns::clone_local_proof_ledgers(
            $proof_enabled,
            &$state.clausification_proofs,
            &$state.original_clause_theory_proofs,
        )
    }};
}
