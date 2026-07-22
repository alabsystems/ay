// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{TermId, TermStore, TheoryResult, TheorySolver};
use ay_euf::{EufModel, EufSolver};
use ay_lra::LraModel;
use ay_nra::NraSolver;

use crate::combined_solvers::check_loops::{
    assert_fixpoint_convergence, debug_nelson_oppen, defer_non_local_result,
    discover_model_equality, forward_non_sat, propagate_all_to, propagate_equalities_to,
    triage_lra_result_deferred,
};
use crate::combined_solvers::interface_bridge::{
    evaluate_real_arith_term_with_reasons, lra_get_real_value_with_reasons, InterfaceBridge,
};
use crate::combined_solvers::models::euf_with_int_values;
use crate::term_helpers::{involves_real_arithmetic, is_uf_real_equality};

/// Combined EUF + NRA theory solver
///
/// This solver wraps both EufSolver and NraSolver, delegating to both
/// and combining their results for QF_UFNRA logic.
///
/// Structurally identical to UfLraSolver, substituting NraSolver for LraSolver.
/// NraSolver already wraps LraSolver internally with `set_combined_theory_mode(true)`,
/// so no additional mode configuration is needed.
///
/// # Nelson-Oppen Interface Term Propagation (#4915)
///
/// For correct theory combination, we track "interface terms" — Real arithmetic
/// expressions that appear in equalities with uninterpreted function terms.
/// After NRA solving, we evaluate such terms under the LRA model (accessed via
/// `NraSolver::lra()`) and propagate equalities with constants to EUF.
pub(crate) struct UfNraSolver<'a> {
    /// Reference to term store for inspecting literals
    terms: &'a TermStore,
    /// EUF solver for equality and congruence reasoning
    euf: EufSolver<'a>,
    /// NRA solver for nonlinear real arithmetic
    nra: NraSolver<'a>,
    /// Shared Nelson-Oppen interface term tracking (#4915).
    interface: InterfaceBridge,
    /// Scope depth counter for push/pop symmetry checking (#4714, #4995).
    scope_depth: usize,
}

impl<'a> UfNraSolver<'a> {
    /// Create a new combined EUF+NRA solver
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        // NraSolver::new already calls lra.set_combined_theory_mode(true) internally.
        Self {
            terms,
            euf: EufSolver::new(terms),
            nra: NraSolver::new(terms),
            interface: InterfaceBridge::new(),
            scope_depth: 0,
        }
    }

    /// Extract both EUF and NRA (LRA-compatible) models for model generation
    pub(crate) fn extract_models(&mut self) -> (EufModel, LraModel) {
        (euf_with_int_values(&mut self.euf), self.nra.extract_model())
    }

    pub(crate) fn replay_learned_cuts(&mut self) {
        // NRA's inner LRA has no learned cuts (LRA replay is a no-op).
    }
    /// Evaluate interface terms under NRA's LRA model and propagate results to EUF (#4915).
    /// Returns (proven_eq_count, speculative_pairs). Proven equalities are asserted into
    /// EUF immediately. Speculative pairs (zero-reason equalities) are returned to the
    /// caller for routing through NeedModelEquality/NeedModelEqualities (#7449, #6846).
    fn propagate_interface_bridge(&mut self, debug: bool) -> (usize, Vec<(TermId, TermId)>) {
        let lra = self.nra.lra();
        let (new_eqs, speculative_pairs) = self.interface.evaluate_and_propagate_real(
            self.terms,
            &|t| lra_get_real_value_with_reasons(lra, t),
            debug,
            "UFNRA",
        );
        let proven_count = new_eqs.len();
        for eq in &new_eqs {
            self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
        }
        // #7449: Do NOT assert speculative pairs into EUF with empty reasons.
        // The old code did `self.euf.assert_shared_equality(lhs, rhs, &[])` which
        // is unsound — if EUF has a disequality constraint on these terms, it
        // produces a conflict clause containing only the disequality, with no
        // arithmetic justification. Instead, return them to check() for routing
        // through NeedModelEquality/NeedModelEqualities, matching the #6846 fix
        // applied to the Int path in combiner_check.rs:326-354.
        (proven_count, speculative_pairs)
    }

    /// Self-referential shim for the lazy split-loop conflict macro
    /// which calls `$theory.lra_solver().collect_all_bound_conflicts()`.
    #[expect(dead_code, reason = "used by incremental split-loop conflict macros")]
    pub(crate) fn lra_solver(&self) -> &Self {
        self
    }

    /// Collect bound conflicts from the underlying NRA (LRA) solver.
    #[expect(dead_code, reason = "used by incremental split-loop conflict macros")]
    pub(crate) fn collect_all_bound_conflicts(
        &self,
        skip_first: bool,
    ) -> Vec<ay_core::TheoryConflict> {
        self.nra.lra().collect_all_bound_conflicts(skip_first)
    }
}

impl TheorySolver for UfNraSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        self.nra.register_atom(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        // EUF gets all literals
        self.euf.assert_literal(literal, value);

        // NRA gets literals involving Real-sorted operands (including equalities/disequalities)
        if involves_real_arithmetic(self.terms, literal) {
            self.nra.assert_literal(literal, value);
        } else if let Some((lhs, rhs)) = is_uf_real_equality(self.terms, literal) {
            if value {
                // Forward UF-real equalities to NRA as shared equalities (#5050).
                let reason = ay_core::TheoryLit::new(literal, true);
                self.nra.assert_shared_equality(lhs, rhs, &[reason]);
            } else {
                // Forward negated UF-real equalities to NRA as shared disequalities (#5228).
                let reason = ay_core::TheoryLit::new(literal, false);
                self.nra.assert_shared_disequality(lhs, rhs, &[reason]);
            }
        }

        // Track interface terms from all literals (#4915).
        self.interface.track_interface_term(self.terms, literal);
        self.interface.collect_real_constants(self.terms, literal);
        self.interface.track_uf_arith_args(self.terms, literal);
    }

    fn check(&mut self) -> TheoryResult {
        let debug = debug_nelson_oppen();
        const MAX_ITERATIONS: usize = 100;
        // #8319: AY_MAX_FIXPOINT_ROUNDS caps the N-O loop for debugging.
        let max_iters = crate::theory_debug_flags::max_fixpoint_rounds()
            .unwrap_or(MAX_ITERATIONS)
            .min(MAX_ITERATIONS);
        // #8469: Configure EUF with shared arith terms for unified diseq propagation.
        self.euf
            .set_shared_arith_terms(self.interface.sorted_arith_terms());
        for iteration in 0..max_iters {
            // Check NRA; defer splits so the interface bridge can try first (#6129).
            let nra_result = self.nra.check();
            let nra_is_unknown = matches!(&nra_result, TheoryResult::Unknown);
            let (deferred_nra_result, nra_early) = triage_lra_result_deferred(nra_result);
            if let Some(early) = nra_early {
                return early;
            }
            let nra_eq_count = match propagate_equalities_to(
                &mut self.nra,
                &mut self.euf,
                debug,
                "UFNRA-NRA",
                iteration,
            ) {
                Ok(n) => n,
                Err(conflict) => return conflict,
            };
            let (interface_eq_count, bridge_speculative) = self.propagate_interface_bridge(debug);
            let has_new_equalities = nra_eq_count > 0 || interface_eq_count > 0;
            if let Some(result) = forward_non_sat(self.euf.check()) {
                return result;
            }
            // #8469: Unified equality + disequality propagation from EUF to NRA.
            let euf_counts =
                match propagate_all_to(&mut self.euf, &mut self.nra, debug, "UFNRA-EUF", iteration)
                {
                    Ok(c) => c,
                    Err(conflict) => return conflict,
                };

            if !has_new_equalities && euf_counts.equalities == 0 && euf_counts.disequalities == 0 {
                // Model equality discovery for non-convex theory combination (#4906).
                // Run BEFORE Unknown/deferred-split returns: even when NRA
                // returns Unknown or NeedExpressionSplit, the LRA model may
                // contain equalities (e.g., y=3 from McCormick linearization)
                // that drive EUF congruence conflicts. The split loop encodes
                // these as SAT decisions; on the next round, NRA gets the
                // equality as a Boolean assertion and can produce proper
                // conflict reasons.
                // #7462: Use evaluate_real_arith_term_with_reasons (recursive
                // expression evaluation) instead of direct variable lookup.
                // Without recursive evaluation, compound UF arguments like
                // (+ x 0.5) cannot be evaluated, so two UF args that simplify
                // to the same value are never grouped together.
                {
                    let lra = self.nra.lra();
                    let terms = self.terms;
                    if let Some(model_eq) = discover_model_equality(
                        self.interface.sorted_arith_terms().into_iter(),
                        self.terms,
                        &self.euf,
                        &|t| {
                            let mut reasons = Vec::new();
                            evaluate_real_arith_term_with_reasons(
                                terms,
                                &|var| lra_get_real_value_with_reasons(lra, var),
                                t,
                                &mut reasons,
                            )
                        },
                        &[ay_core::Sort::Real],
                        debug,
                        "UFNRA",
                    ) {
                        return model_eq;
                    }
                }
                // #7449/#6846: Route speculative pairs through NeedModelEquality
                // instead of asserting directly into EUF with empty reasons.
                // Matches the Int path fix in combiner_check.rs:326-354.
                let mut batch = Vec::new();
                for &(lhs, rhs) in &bridge_speculative {
                    if !self.euf.are_equal(lhs, rhs) {
                        if debug {
                            safe_eprintln!(
                                "[N-O UFNRA] Bridge speculative model equality: {:?} = {:?} \
                                 (no arithmetic reasons, not EUF-equal)",
                                lhs,
                                rhs,
                            );
                        }
                        batch.push(ay_core::ModelEqualityRequest {
                            lhs,
                            rhs,
                            reason: Vec::new(),
                            implied: false,
                        });
                    }
                }
                match batch.len() {
                    0 => {}
                    1 => return TheoryResult::NeedModelEquality(batch.pop().unwrap()),
                    _ => return TheoryResult::NeedModelEqualities(batch),
                }
                if nra_is_unknown {
                    return TheoryResult::Unknown; // #4945
                }
                // If NRA deferred a split request, return it now (#6129).
                if let Some(split) = deferred_nra_result {
                    return split;
                }
                assert_fixpoint_convergence("UFNRA", &mut [&mut self.nra, &mut self.euf]);
                return TheoryResult::Sat;
            }
            debug_assert!(
                nra_eq_count
                    + euf_counts.equalities
                    + euf_counts.disequalities
                    + interface_eq_count
                    > 0,
                "BUG: UFNRA N-O iteration {iteration} with 0 new equalities past fixpoint"
            );
            // #anra-select-nra-nonconvergence: the EUF↔NRA interface-equality
            // fixpoint can OSCILLATE when an array-select term feeds a nonlinear
            // NRA atom AND an EUF pin — the same interface equalities are
            // rediscovered every round, so the loop never reaches the
            // `has_new_equalities == false` fixpoint. Hitting the iteration cap is
            // NOT a solver bug in that case; it is genuine non-convergence of a
            // combined NRA+UF problem. Returning Unknown is the only sound verdict
            // (no model produced, no conflict proven). Previously a debug_assert!
            // here PANICKED the debug build (release silently fell through to the
            // Unknown below); we now break gracefully so debug and release agree on
            // a sound Unknown and no panic escapes. Mirrors the UFNIA adapter.
            if iteration >= max_iters - 1 {
                if debug {
                    safe_eprintln!(
                        "[N-O UFNRA] interface-equality fixpoint did not converge in \
                         {max_iters} iterations; returning Unknown (sound)"
                    );
                }
                break;
            }
        }
        TheoryResult::Unknown
    }

    /// BCP-time lightweight check: run each sub-theory's cheap check
    /// individually WITHOUT the Nelson-Oppen fixpoint loop (#8404).
    fn check_during_propagate(&mut self) -> TheoryResult {
        let nra_result = defer_non_local_result(self.nra.check_during_propagate());
        if !matches!(nra_result, TheoryResult::Sat) {
            return nra_result;
        }

        let euf_result = defer_non_local_result(self.euf.check_during_propagate());
        if !matches!(euf_result, TheoryResult::Sat) {
            return euf_result;
        }

        TheoryResult::Sat
    }

    delegate_propagate!(euf, nra);

    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    fn push(&mut self) {
        self.scope_depth += 1;
        self.euf.push();
        self.nra.push();
        self.interface.push();
    }

    fn pop(&mut self) {
        if self.scope_depth == 0 {
            return;
        }
        self.scope_depth -= 1;
        self.euf.pop();
        self.nra.pop();
        self.interface.pop();
    }

    fn reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: UfNraSolver::reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.euf.reset();
        self.nra.reset();
        self.interface.reset();
    }

    fn soft_reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: UfNraSolver::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.euf.soft_reset();
        self.nra.soft_reset();
        self.interface.reset();
    }

    fn supports_farkas_semantic_check(&self) -> bool {
        true
    }

    fn supports_theory_aware_branching(&self) -> bool {
        self.nra.supports_theory_aware_branching()
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        self.nra.suggest_phase(atom)
    }

    fn sort_atom_index(&mut self) {
        self.nra.sort_atom_index();
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        self.nra.generate_bound_axiom_terms()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        self.nra.generate_incremental_bound_axioms(atom)
    }
}
