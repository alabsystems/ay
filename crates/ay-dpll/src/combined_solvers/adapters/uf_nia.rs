// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{TermId, TermStore, TheoryResult, TheorySolver};
use ay_euf::{EufModel, EufSolver};
use ay_lia::LiaModel;
use ay_nia::NiaSolver;

use crate::combined_solvers::check_loops::{
    assert_fixpoint_convergence, debug_nelson_oppen, defer_non_local_result,
    discover_model_equality, forward_non_sat, propagate_all_to_dedup, triage_lia_result,
    ForwardedPairs,
};
use crate::combined_solvers::interface_bridge::{
    evaluate_arith_term_with_reasons, lia_get_int_value_with_reasons, InterfaceBridge,
};
use crate::combined_solvers::models::{euf_with_int_values, merge_lia_values};
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
    /// Recurrence state for BCP disequality-split surfacing: the last
    /// disequality split the inner NIA requested during
    /// `check_during_propagate` and how many consecutive BCP checks
    /// re-derived it identically. Cleared by any non-split NIA result
    /// and by reset; deliberately kept across push/pop, because the
    /// guarded split clause is valid in every scope and a backtrack
    /// does not make a recurring request fresh guidance.
    bcp_diseq_repeat: Option<(ay_core::DisequalitySplitRequest, u32)>,
}

/// Consecutive identical BCP disequality-split requests after which
/// the request surfaces instead of deferring to `Sat`
/// (DR-AY-NIA-DISEQ-BCP-DEFERRAL-DIAGNOSIS-20261117). Small enough
/// that a genuinely stuck disequality (re-derived at ~99% of BCP
/// checks on Certora `65782_..._8`) surfaces almost immediately;
/// large enough that a split the search resolves within a few
/// quiescences keeps the landed deferred trajectory exactly
/// (unconditioned surfacing was rejected for a stable Zohar loss,
/// DR-AY-UFNIA-BCP-DISEQ-SURFACING-REJECTED-20261117).
const BCP_DISEQ_SURFACE_REPEATS: u32 = 16;

/// Field-wise identity of two disequality split requests (the
/// request type derives no `PartialEq`).
fn same_diseq_request(
    a: &ay_core::DisequalitySplitRequest,
    b: &ay_core::DisequalitySplitRequest,
) -> bool {
    a.variable == b.variable
        && a.excluded_value == b.excluded_value
        && a.disequality_term == b.disequality_term
        && a.is_distinct == b.is_distinct
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
            bcp_diseq_repeat: None,
        }
    }

    /// Genuine Boolean data from the NIA's current verified candidate only.
    pub(crate) fn boolean_witness(&self) -> impl Iterator<Item = (TermId, bool)> + '_ {
        self.nia.boolean_witness()
    }

    /// Extract both EUF and NIA (LIA-compatible) models for model generation.
    ///
    /// The NIA's values are merged into the EUF model's integer views
    /// (`merge_lia_values`), exactly as every other EUF+arithmetic lane does
    /// (`combiner_models.rs`, `auf_lira.rs`). Without it the EUF model kept its
    /// own fabricated per-class integers for terms the NIA owns, and the
    /// function tables keyed and resolved through them: on a QF_UFNIA fuzz
    /// file (`nia_8301_004`) the NIA's point had `f(z) = -4 < f(x*z*w) = -3`
    /// while the EUF lane still said `x = 4, x*z*w = 5, f(z) = 6`; the
    /// model gate read `f(z)` through the table, found the assertion false and
    /// answered `unknown (self-check-rejected)` on a satisfiable problem.
    ///
    /// The EUF model is scoped to `model_roots`, the window this solve
    /// actually decided (#ufnia-model-scope). Unscoped, `EufSolver` models
    /// every application in the whole `TermStore`, and an incremental session
    /// keeps the applications of earlier windows, popped assertions and
    /// `get-value` queries there. The Nelson-Oppen loop never saw those
    /// orphans: no asserted literal mentions them, so their arguments are not
    /// interface terms and `x1 = x2` in the NIA model never reaches EUF. Each
    /// orphan then got its own fabricated class integer and its own table row,
    /// so with `x1 = x2 = 0` the model published `(f x1) = 8`, `(f x2) = 9` —
    /// not a function. Every other EUF+arithmetic lane already scopes
    /// (`scope_euf_model_to_roots`); an application outside the scope is read
    /// through the table at its evaluated arguments, which is a function.
    pub(crate) fn extract_models(
        &mut self,
        model_roots: &[TermId],
    ) -> (EufModel, Option<LiaModel>) {
        self.euf.scope_model_to_roots(model_roots);
        let mut euf_model = euf_with_int_values(&mut self.euf);
        self.euf.clear_model_scope();
        let lia_model = self
            .nia
            .extract_model()
            .map(|m| LiaModel { values: m.values });
        merge_lia_values(&mut euf_model, lia_model.as_ref());
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
        // Pairs already forwarded this check, per direction (see
        // ForwardedPairs: tentative-patch pops re-export the same pairs).
        let mut fwd_nia_to_euf = ForwardedPairs::default();
        let mut fwd_euf_to_nia = ForwardedPairs::default();
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
            let nia_eq_count = match propagate_all_to_dedup(
                &mut self.nia,
                &mut self.euf,
                &mut fwd_nia_to_euf,
                debug,
                "UFNIA-NIA",
                iteration,
            ) {
                Ok(counts) => counts.equalities,
                Err(conflict) => return *conflict,
            };
            let (interface_eq_count, bridge_speculative) = self.propagate_interface_bridge(debug);
            let has_new_equalities = nia_eq_count > 0 || interface_eq_count > 0;
            if let Some(result) = forward_non_sat(self.euf.check()) {
                return result;
            }
            // #8469: Unified equality + disequality propagation from EUF to NIA.
            let euf_counts = match propagate_all_to_dedup(
                &mut self.euf,
                &mut self.nia,
                &mut fwd_euf_to_nia,
                debug,
                "UFNIA-EUF",
                iteration,
            ) {
                Ok(c) => c,
                Err(conflict) => return *conflict,
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
        // Recurrence-gated disequality-split surfacing: the generic
        // deferral maps a disequality split to `Sat` at BCP, so a
        // disequality the search never resolves is re-derived by a
        // full NIA check at every quiescence and only reaches the
        // split loop at candidate granularity
        // (DR-AY-NIA-DISEQ-BCP-DEFERRAL-DIAGNOSIS-20261117). Surface
        // the exact request once it has recurred identically
        // `BCP_DISEQ_SURFACE_REPEATS` times consecutively; below the
        // gate behavior is the landed deferral bit-for-bit.
        let raw_nia = self.nia.check_during_propagate();
        if let TheoryResult::NeedDisequalitySplit(req) = &raw_nia {
            let repeats = match &mut self.bcp_diseq_repeat {
                Some((prev, n)) if same_diseq_request(prev, req) => {
                    *n += 1;
                    *n
                }
                slot => {
                    *slot = Some((req.clone(), 1));
                    1
                }
            };
            if repeats >= BCP_DISEQ_SURFACE_REPEATS {
                return raw_nia;
            }
        } else {
            self.bcp_diseq_repeat = None;
        }
        let nia_result = defer_non_local_result(raw_nia);
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
        self.bcp_diseq_repeat = None;
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
        self.bcp_diseq_repeat = None;
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

    fn phase_hint_epoch(&self) -> Option<u64> {
        // `suggest_phase` above is a pure delegate, so the nonlinear solver's
        // epoch (size-gated there, value-exact by `LraSolver::phase_state_epoch`)
        // covers every suggestion this adapter emits (#nonlinear-phase-hints).
        // Without this forwarding the SAT seeder's epoch skip was dead on the
        // UF+NIA lane.
        self.nia.phase_hint_epoch()
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

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::term::Symbol;
    use ay_core::Sort;
    use num_bigint::BigInt;

    /// After a `Sat`, every term the NIA assigns carries the NIA's value in
    /// BOTH EUF integer views, and none of them is left speculative: the
    /// function tables key and resolve through `int_values`, so a fabricated
    /// class integer there contradicts the arithmetic model the gate checks.
    #[test]
    fn extract_models_merges_the_nia_values_into_the_euf_integer_views() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let fx = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
        let xy = terms.mk_mul(vec![x, y]);
        let three = terms.mk_int(BigInt::from(3));
        let six = terms.mk_int(BigInt::from(6));
        let atoms = [
            terms.mk_eq(x, three),
            terms.mk_eq(xy, six),
            terms.mk_gt(fx, xy),
        ];
        let mut solver = UfNiaSolver::new(&terms);
        for atom in atoms {
            solver.register_atom(atom);
            solver.assert_literal(atom, true);
        }
        let result = solver.check();
        assert!(
            matches!(result, TheoryResult::Sat),
            "x = 3, y = 2, f(3) > 6: {result:?}"
        );
        let (euf, lia) = solver.extract_models(&atoms);
        let lia = lia.expect("an NIA model after Sat");
        assert!(
            lia.values.contains_key(&x),
            "the NIA assigns x: {:?}",
            lia.values
        );
        for (term, value) in &lia.values {
            assert_eq!(
                euf.int_values.get(term),
                Some(value),
                "EUF's integer view of {term:?} disagrees with the NIA's {value}"
            );
            assert!(
                euf.term_values.contains_key(term),
                "EUF's formatted view has no value for {term:?}"
            );
            assert!(
                !euf.speculative_int_terms.contains(term),
                "{term:?} carries the NIA's value but is still marked speculative"
            );
        }
    }

    /// A disequality split the inner NIA keeps re-deriving at BCP must
    /// eventually surface instead of being deferred to `Sat` forever
    /// (DR-AY-NIA-DISEQ-BCP-DEFERRAL-DIAGNOSIS-20261117: on Certora
    /// `65782_..._8` the same request was re-derived at ~99% of BCP
    /// checks and only reached the split loop at candidate
    /// granularity). The first requests keep the landed deferral --
    /// unconditioned surfacing was measured and rejected for a stable
    /// Zohar loss (DR-AY-UFNIA-BCP-DISEQ-SURFACING-REJECTED-20261117)
    /// -- so surfacing is gated on recurrence of the identical
    /// request.
    #[test]
    fn bcp_check_surfaces_repeated_disequality_split() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let x_eq_zero = terms.mk_eq(x, zero);
        let mut solver = UfNiaSolver::new(&terms);
        solver.register_atom(x_eq_zero);
        solver.assert_literal(x_eq_zero, false);

        // The relaxation point x = 0 violates the asserted disequality
        // on every BCP check; the identical request must recur.
        let mut surfaced_at = None;
        for call in 1..=64 {
            match solver.check_during_propagate() {
                TheoryResult::NeedDisequalitySplit(_) => {
                    surfaced_at = Some(call);
                    break;
                }
                other => assert!(
                    matches!(other, TheoryResult::Sat),
                    "BCP call {call} must defer (Sat) before the recurrence gate, got {other:?}"
                ),
            }
        }
        let call = surfaced_at.expect("repeated disequality split must surface at BCP");
        assert!(
            call > 1,
            "the first request must keep the landed deferral, surfaced at call {call}"
        );
    }
}
