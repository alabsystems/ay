// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{TermId, TermStore, TheoryResult, TheorySolver};
use ay_euf::{EufModel, EufSolver};
use ay_lia::LiaModel;
use ay_nia::NiaSolver;

use crate::combined_solvers::check_loops::{
    assert_fixpoint_convergence, debug_nelson_oppen, defer_non_local_result,
    discover_model_equality, forward_non_sat, propagate_all_to, propagate_equalities_to,
    triage_lia_result,
};
use crate::combined_solvers::interface_bridge::{
    evaluate_arith_term_with_reasons, lia_get_int_value_with_reasons, InterfaceBridge,
};
use crate::combined_solvers::models::euf_with_int_values;
use crate::term_helpers::{involves_int_arithmetic, is_uf_int_equality};

/// Combined EUF + NIA theory solver for QF_UFNIA / QF_AUFNIRA theory combination.
///
/// Follows the same Nelson-Oppen pattern as `UfNraSolver` (EUF + NRA),
/// but uses `NiaSolver` (which wraps LIA + nonlinear refinement) for
/// integer arithmetic. The interface bridge evaluates Int-sorted terms
/// under the LIA model and propagates equalities to EUF.
///
/// # Theory Combination (#4525)
///
/// AUFNIRA formulas combine arrays, uninterpreted functions, and non-linear
/// integer arithmetic. Arrays are handled by the EUF congruence closure
/// (array axiom injection). UF congruence ensures f(x)=f(y) when x=y.
/// NIA handles nonlinear integer constraints via model-based linearization.
/// The N-O loop propagates equalities between EUF and NIA until fixpoint.
pub(crate) struct UfNiaSolver<'a> {
    /// Reference to term store for inspecting literals
    terms: &'a TermStore,
    /// EUF solver for equality and congruence reasoning
    euf: EufSolver<'a>,
    /// NIA solver for nonlinear integer arithmetic
    nia: NiaSolver<'a>,
    /// Shared Nelson-Oppen interface term tracking (#4915).
    interface: InterfaceBridge,
    /// Scope depth counter for push/pop symmetry checking (#4714, #4995).
    scope_depth: usize,
}

impl<'a> UfNiaSolver<'a> {
    /// Create a new combined EUF+NIA solver
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        let mut nia = NiaSolver::new(terms);
        nia.set_combined_theory_mode(true);
        Self {
            terms,
            euf: EufSolver::new(terms),
            nia,
            interface: InterfaceBridge::new(),
            scope_depth: 0,
        }
    }

    /// Extract both EUF and NIA (LIA-compatible) models for model generation
    pub(crate) fn extract_models(&mut self) -> (EufModel, Option<LiaModel>) {
        let euf_model = euf_with_int_values(&mut self.euf);
        let lia_model = self
            .nia
            .extract_model()
            .map(|m| LiaModel { values: m.values });
        (euf_model, lia_model)
    }

    pub(crate) fn replay_learned_cuts(&mut self) {
        self.nia.replay_learned_cuts();
    }

    /// Forward the solve deadline into the inner NIA solver (#nia-deadline,
    /// mirror of #lia-deadline-forward): the N-O loop above only polls its
    /// own deadline BETWEEN theory checks, so without this a single dense
    /// `nia.check()` refinement escalation could overshoot the caller's wall
    /// budget without bound. NIA forwards it further into its embedded
    /// `LiaSolver`.
    pub(crate) fn set_deadline(&mut self, deadline: ay_core::time::Instant) {
        self.nia.set_deadline(deadline);
    }

    /// Evaluate interface terms under NIA's LIA model and propagate results to EUF (#4915).
    /// Returns (proven_eq_count, speculative_pairs). Proven equalities are asserted into
    /// EUF immediately. Speculative pairs (zero-reason equalities) are returned to the
    /// caller for routing through NeedModelEquality/NeedModelEqualities (#7449, #6846).
    fn propagate_interface_bridge(&mut self, debug: bool) -> (usize, Vec<(TermId, TermId)>) {
        let lia = self.nia.lia();
        let (new_eqs, speculative_pairs) = self.interface.evaluate_and_propagate(
            self.terms,
            &|t| lia_get_int_value_with_reasons(lia, t),
            debug,
            "UFNIA",
        );
        let proven_count = new_eqs.len();
        for eq in &new_eqs {
            self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
        }
        // #7449: Do NOT assert speculative pairs into EUF with empty reasons.
        // Route through NeedModelEquality/NeedModelEqualities instead.
        (proven_count, speculative_pairs)
    }

    /// Self-referential shim for the lazy split-loop conflict macro
    /// which calls `$theory.lra_solver().collect_all_bound_conflicts()`.
    #[expect(dead_code, reason = "used by incremental split-loop conflict macros")]
    pub(crate) fn lra_solver(&self) -> &Self {
        self
    }

    /// Collect bound conflicts from the underlying NIA (LIA -> LRA) solver.
    #[expect(dead_code, reason = "used by incremental split-loop conflict macros")]
    pub(crate) fn collect_all_bound_conflicts(
        &self,
        skip_first: bool,
    ) -> Vec<ay_core::TheoryConflict> {
        self.nia
            .lra_solver()
            .collect_all_bound_conflicts(skip_first)
    }
}

impl TheorySolver for UfNiaSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        self.nia.register_atom(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        // EUF gets all literals
        self.euf.assert_literal(literal, value);

        // NIA gets literals involving Int-sorted operands (including equalities/disequalities)
        if involves_int_arithmetic(self.terms, literal) {
            self.nia.assert_literal(literal, value);
        } else if let Some((lhs, rhs)) = is_uf_int_equality(self.terms, literal) {
            if value {
                // Forward UF-int equalities to NIA as shared equalities (#5050).
                let reason = ay_core::TheoryLit::new(literal, true);
                self.nia.assert_shared_equality(lhs, rhs, &[reason]);
            } else {
                // Forward negated UF-int equalities to NIA as shared disequalities (#5228).
                let reason = ay_core::TheoryLit::new(literal, false);
                self.nia.assert_shared_disequality(lhs, rhs, &[reason]);
            }
        }

        // Track interface terms from all literals (#4915).
        self.interface.track_interface_term(self.terms, literal);
        self.interface.collect_int_constants(self.terms, literal);
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
            // Check NIA; defer splits so the interface bridge can try first (#6129).
            let nia_result = self.nia.check();
            let nia_is_unknown = matches!(&nia_result, TheoryResult::Unknown);
            let (deferred_nia_result, nia_early) = triage_lia_result(nia_result);
            if let Some(early) = nia_early {
                return early;
            }
            let nia_eq_count = match propagate_equalities_to(
                &mut self.nia,
                &mut self.euf,
                debug,
                "UFNIA-NIA",
                iteration,
            ) {
                Ok(n) => n,
                Err(conflict) => return conflict,
            };
            let (interface_eq_count, bridge_speculative) = self.propagate_interface_bridge(debug);
            let has_new_equalities = nia_eq_count > 0 || interface_eq_count > 0;
            if let Some(result) = forward_non_sat(self.euf.check()) {
                return result;
            }
            // #8469: Unified equality + disequality propagation from EUF to NIA.
            let euf_counts =
                match propagate_all_to(&mut self.euf, &mut self.nia, debug, "UFNIA-EUF", iteration)
                {
                    Ok(c) => c,
                    Err(conflict) => return conflict,
                };

            if !has_new_equalities && euf_counts.equalities == 0 && euf_counts.disequalities == 0 {
                // Model equality discovery for non-convex theory combination (#4906).
                {
                    let lia = self.nia.lia();
                    let terms = self.terms;
                    if let Some(model_eq) = discover_model_equality(
                        self.interface.sorted_arith_terms().into_iter(),
                        self.terms,
                        &self.euf,
                        &|t| {
                            let mut reasons = Vec::new();
                            evaluate_arith_term_with_reasons(
                                terms,
                                &|var| lia_get_int_value_with_reasons(lia, var),
                                t,
                                &mut reasons,
                            )
                        },
                        &[ay_core::Sort::Int],
                        debug,
                        "UFNIA",
                    ) {
                        return model_eq;
                    }
                }
                // #7449/#6846: Route speculative pairs through NeedModelEquality
                // instead of asserting directly into EUF with empty reasons.
                let mut batch = Vec::new();
                for &(lhs, rhs) in &bridge_speculative {
                    if !self.euf.are_equal(lhs, rhs) {
                        if debug {
                            safe_eprintln!(
                                "[N-O UFNIA] Bridge speculative model equality: {:?} = {:?} \
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
                if nia_is_unknown {
                    return TheoryResult::Unknown; // #4945
                }
                // If NIA deferred a split request, return it now (#6129).
                if let Some(split) = deferred_nia_result {
                    return split;
                }
                assert_fixpoint_convergence("UFNIA", &mut [&mut self.nia, &mut self.euf]);
                return TheoryResult::Sat;
            }
            debug_assert!(
                nia_eq_count
                    + euf_counts.equalities
                    + euf_counts.disequalities
                    + interface_eq_count
                    > 0,
                "BUG: UFNIA N-O iteration {iteration} with 0 new equalities past fixpoint"
            );
            // #anra-select-nia-nonconvergence: the EUF↔NIA interface-equality
            // fixpoint can OSCILLATE when an array-select term feeds a nonlinear
            // NIA atom (or sits in a `div`/`mod` divisor) AND an EUF pin — the same
            // interface equalities are rediscovered every round, so the loop never
            // reaches the `has_new_equalities == false` fixpoint. Hitting the
            // iteration cap is NOT a solver bug in that case; it is genuine
            // non-convergence of a combined NIA+UF problem (an undecidable
            // fragment). Returning Unknown is the only sound verdict — AY has
            // produced no model and proven no conflict. Previously a debug_assert!
            // here PANICKED the debug build (release silently fell through to the
            // Unknown below); we now break gracefully so debug and release agree on
            // a sound Unknown and no panic escapes. (A debug_assert! would also
            // mask the issue under AY_MAX_FIXPOINT_ROUNDS, which is why this is a
            // hard break rather than an assertion.)
            if iteration >= max_iters - 1 {
                if debug {
                    safe_eprintln!(
                        "[N-O UFNIA] interface-equality fixpoint did not converge in \
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
        let nia_result = defer_non_local_result(self.nia.check_during_propagate());
        if !matches!(nia_result, TheoryResult::Sat) {
            return nia_result;
        }

        let euf_result = defer_non_local_result(self.euf.check_during_propagate());
        if !matches!(euf_result, TheoryResult::Sat) {
            return euf_result;
        }

        TheoryResult::Sat
    }

    delegate_propagate!(euf, nia);

    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    fn push(&mut self) {
        self.scope_depth += 1;
        self.euf.push();
        self.nia.push();
        self.interface.push();
    }

    fn pop(&mut self) {
        if self.scope_depth == 0 {
            return;
        }
        self.scope_depth -= 1;
        self.euf.pop();
        self.nia.pop();
        self.interface.pop();
    }

    fn reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: UfNiaSolver::reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.euf.reset();
        self.nia.reset();
        self.interface.reset();
    }

    fn soft_reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: UfNiaSolver::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.euf.soft_reset();
        self.nia.soft_reset();
        self.interface.reset();
    }

    fn supports_farkas_semantic_check(&self) -> bool {
        true
    }

    fn supports_theory_aware_branching(&self) -> bool {
        self.nia.supports_theory_aware_branching()
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        self.nia.suggest_phase(atom)
    }

    fn sort_atom_index(&mut self) {
        self.nia.sort_atom_index();
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        self.nia.generate_bound_axiom_terms()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        self.nia.generate_incremental_bound_axioms(atom)
    }
}
