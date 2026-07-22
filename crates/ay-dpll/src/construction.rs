// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Construction and reconstruction methods for `DpllT`.
//!
//! Contains `from_tseitin_impl` (the main factory method), `into_sat_state`,
//! and `from_sat_state` for CEGAR-style solver reconstruction.
//! Extracted from `lib.rs` as part of #6860.

use ay_core::term::TermData;
use ay_core::{is_theory_atom, Sort, TermId, TermStore, TheorySolver};

use crate::{DpllConstructionTimings, DpllSatState, DpllT, PhaseTimer};

impl<'a, T: TheorySolver> DpllT<'a, T> {
    /// Create a DPLL(T) solver from a Tseitin transformation result.
    ///
    /// Automatically enables TLA2 JSONL trace emission when `AY_TRACE_FILE` is set.
    pub fn from_tseitin(
        terms: &'a TermStore,
        tseitin_result: &ay_core::TseitinResult,
        theory: T,
    ) -> Self {
        Self::from_tseitin_impl(terms, tseitin_result, theory, false)
    }

    /// Create a DPLL(T) solver from a Tseitin result with clause tracing enabled.
    ///
    /// When `proof_enabled` is true, the clause trace is activated before clauses
    /// are added so that original clauses are recorded for resolution proof
    /// reconstruction (#4176).
    pub fn from_tseitin_with_proof(
        terms: &'a TermStore,
        tseitin_result: &ay_core::TseitinResult,
        theory: T,
    ) -> Self {
        Self::from_tseitin_impl(terms, tseitin_result, theory, true)
    }

    fn from_tseitin_impl(
        terms: &'a TermStore,
        tseitin_result: &ay_core::TseitinResult,
        theory: T,
        proof_enabled: bool,
    ) -> Self {
        let mut construction_timings = DpllConstructionTimings::default();
        let mut solver = {
            let _from_tseitin_timer = PhaseTimer::new(&mut construction_timings.from_tseitin);
            let mut solver = DpllT::new(tseitin_result.num_vars as usize, theory);
            solver.maybe_enable_tla_trace_from_env();
            solver.maybe_enable_diagnostic_trace_from_env();
            solver.maybe_enable_dpll_diagnostic_trace_from_env();
            solver.maybe_enable_decision_trace_from_env();
            solver.maybe_enable_replay_trace_from_env();
            solver.maybe_load_solution_from_env();
            solver.terms = Some(terms);

            // Copy the variable mappings, converting CNF vars (1-indexed) to SAT vars (0-indexed).
            solver.var_to_term = tseitin_result
                .var_to_term
                .iter()
                .map(|(&v, &t)| (v - 1, t))
                .collect();
            solver.term_to_var = tseitin_result
                .term_to_var
                .iter()
                .map(|(&t, &v)| (t, v - 1))
                .collect();

            // Enable clause tracing BEFORE adding clauses so original clauses are
            // recorded in the trace for resolution proof reconstruction (#4176).
            if proof_enabled {
                solver.sat.enable_clause_trace();
            }

            // Add all clauses to the SAT solver.
            let num_original_clauses = tseitin_result.clauses.len();
            {
                let _clause_load_timer = PhaseTimer::new(&mut construction_timings.clause_load);
                for clause in &tseitin_result.clauses {
                    let lits: Vec<ay_sat::Literal> = clause
                        .0
                        .iter()
                        .copied()
                        .map(ay_sat::Literal::from_dimacs)
                        .collect();
                    solver.sat.add_clause(lits);
                }
            }

            // Communicate only theory-relevant *atomic* predicates to the theory solver.
            {
                let _atom_scan_timer = PhaseTimer::new(&mut construction_timings.theory_atom_scan);
                solver.theory_atoms = solver
                    .var_to_term
                    .values()
                    .copied()
                    .filter(|&t| is_theory_atom(terms, t))
                    .collect();
                solver.theory_atoms.sort_unstable_by_key(|t| t.0);
                solver.theory_atoms.dedup();

                tracing::info!(
                    num_vars = tseitin_result.num_vars,
                    num_clauses = num_original_clauses,
                    theory_atoms = solver.theory_atoms.len(),
                    var_to_term_count = solver.var_to_term.len(),
                    "DpllT::from_tseitin stats (#4919)"
                );

                // Additional pass: Bool-sorted terms that appear as arguments to UF
                // applications must be theory atoms so their truth values reach the
                // EUF solver. Without this, congruence closure cannot propagate
                // through Bool-valued UF arguments. (#4610)
                let mut uf_bool_args: Vec<TermId> = Vec::new();
                for idx in 0..terms.len() {
                    let term_id = TermId::new(idx as u32);
                    if let TermData::App(ay_core::term::Symbol::Named(name), args) =
                        terms.get(term_id)
                    {
                        match name.as_str() {
                            "and" | "or" | "xor" | "=>" | "not" | "=" | "distinct" | "ite" => {
                                continue
                            }
                            _ => {}
                        }
                        if args.is_empty() {
                            continue;
                        }
                        for &arg in args {
                            if terms.sort(arg) == &Sort::Bool && solver.var_for_term(arg).is_some()
                            {
                                uf_bool_args.push(arg);
                            }
                        }
                    }
                }
                if !uf_bool_args.is_empty() {
                    solver.theory_atoms.extend(uf_bool_args);
                    solver.theory_atoms.sort_unstable_by_key(|t| t.0);
                    solver.theory_atoms.dedup();
                }
                solver.theory_atom_set = solver.theory_atoms.iter().copied().collect();
            }

            {
                let _freeze_timer = PhaseTimer::new(&mut construction_timings.freeze_internalize);

                // Freeze pass mutates `solver.sat`, so iterate over a snapshot.
                let atoms_to_freeze = solver.theory_atoms.clone();
                for term in atoms_to_freeze {
                    if let Some(var) = solver.var_for_term(term) {
                        solver.freeze_var_if_needed(var);
                    }
                }

                // Disable conditioning (GBCE) for DPLL(T) safety (#4057).
                // Conditioning eliminates globally blocked clauses, which is
                // equisatisfiable for pure SAT but can lose satisfying
                // assignments when theory atoms constrain the solution space.
                // Same rationale as BVE being disabled by default.
                solver.sat.set_condition_enabled(false);
                // Disable SAT preprocessing in DPLL(T) mode.
                // The SAT-side inprocessing pipeline can produce assignments that
                // satisfy the reduced clause DB but violate the original Tseitin CNF,
                // which is unacceptable for theory-model validation and replay.
                solver.sat.set_preprocess_enabled(false);
                // Adaptive reorder gate for large DPLL(T) instances (#8118).
                // Kissat-style clause-weighted VMTF queue reorder is O(n log n)
                // and the constant factor is high. On large bit-blasted or
                // theory-heavy formulas (>50K vars), the overhead exceeds the
                // benefit. This mirrors the adaptive rule in ay-sat's
                // adaptive::REORDER_MAX_VARS without requiring feature extraction.
                if tseitin_result.num_vars as usize > 50_000 {
                    solver.sat.set_reorder_enabled(false);
                }
                solver.internalize_registered_theory_atoms();
            }

            solver
        };
        solver.construction_timings = construction_timings;
        solver
    }

    /// Consume this wrapper and keep SAT-side progress for later reconstruction.
    ///
    /// This intentionally drops the current theory solver, which may hold
    /// immutable borrows into the term store. Callers can then mutate terms
    /// (e.g., create fresh skolem/split atoms) and re-wrap the preserved SAT
    /// state with a fresh theory via [`Self::from_sat_state`].
    pub(crate) fn into_sat_state(mut self) -> DpllSatState {
        // Exit internal model scope before destructuring to maintain
        // theory scope balance (#4520).
        self.exit_model_scope_if_active();
        let DpllT {
            sat,
            theory,
            terms: _,
            var_to_term,
            term_to_var,
            theory_atoms,
            theory_atom_set,
            debug_dpll,
            debug_sync,
            theory_conflict_count,
            theory_propagation_count,
            partial_clause_count,
            theory_unknown_count,
            conflict_max_literals,
            conflict_total_literals,
            theory_minimize_lits_removed,
            farkas_certificate_failures,
            farkas_certificate_downgrades,
            semantic_verify_budget_skips,
            semantic_verify_sample_counter,
            semantic_verify_warned,
            eager_stats,
            timings,
            construction_timings,
            diagnostic_trace,
            dpll_tla_trace,
            model_scope_active: _,
            prev_theory_atom_values: _,
            sync_atoms_asserted: _,
            sync_skipped_identical: _,
            sync_delta_changed: _,
            sync_delta_unchanged: _,
            dt_verification_axioms,
            ematching_support_axioms,
            solve_deadline,
            solve_interrupt,
        } = self;
        drop(theory);
        DpllSatState {
            sat,
            var_to_term,
            term_to_var,
            theory_atoms,
            theory_atom_set,
            debug_dpll,
            debug_sync,
            theory_conflict_count,
            theory_propagation_count,
            partial_clause_count,
            theory_unknown_count,
            conflict_max_literals,
            conflict_total_literals,
            theory_minimize_lits_removed,
            farkas_certificate_failures,
            farkas_certificate_downgrades,
            semantic_verify_budget_skips,
            semantic_verify_sample_counter,
            semantic_verify_warned,
            eager_stats,
            timings,
            construction_timings,
            diagnostic_trace,
            dpll_tla_trace,
            dt_verification_axioms,
            ematching_support_axioms,
            solve_deadline,
            solve_interrupt,
        }
    }

    /// Reconstruct a DPLL(T) wrapper from preserved SAT-side state.
    pub(crate) fn from_sat_state(terms: &'a TermStore, theory: T, state: DpllSatState) -> Self {
        let mut dpll = DpllT {
            sat: state.sat,
            theory,
            terms: Some(terms),
            var_to_term: state.var_to_term,
            term_to_var: state.term_to_var,
            theory_atoms: state.theory_atoms,
            theory_atom_set: state.theory_atom_set,
            debug_dpll: state.debug_dpll,
            debug_sync: state.debug_sync,
            theory_conflict_count: state.theory_conflict_count,
            theory_propagation_count: state.theory_propagation_count,
            partial_clause_count: state.partial_clause_count,
            theory_unknown_count: state.theory_unknown_count,
            conflict_max_literals: state.conflict_max_literals,
            conflict_total_literals: state.conflict_total_literals,
            theory_minimize_lits_removed: state.theory_minimize_lits_removed,
            farkas_certificate_failures: state.farkas_certificate_failures,
            farkas_certificate_downgrades: state.farkas_certificate_downgrades,
            semantic_verify_budget_skips: state.semantic_verify_budget_skips,
            semantic_verify_sample_counter: state.semantic_verify_sample_counter,
            semantic_verify_warned: state.semantic_verify_warned,
            eager_stats: state.eager_stats,
            timings: state.timings,
            construction_timings: state.construction_timings,
            diagnostic_trace: state.diagnostic_trace,
            dpll_tla_trace: state.dpll_tla_trace,
            model_scope_active: false,
            prev_theory_atom_values: None,
            sync_atoms_asserted: 0,
            sync_skipped_identical: 0,
            sync_delta_changed: 0,
            sync_delta_unchanged: 0,
            dt_verification_axioms: state.dt_verification_axioms,
            ematching_support_axioms: state.ematching_support_axioms,
            solve_deadline: state.solve_deadline,
            solve_interrupt: state.solve_interrupt,
        };
        dpll.internalize_registered_theory_atoms();
        dpll
    }
}
