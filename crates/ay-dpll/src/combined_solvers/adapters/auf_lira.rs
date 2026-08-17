// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps/sets in all builds.
use ay_arrays::{ArrayModel, ArraySolver};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{TermData, TermId, TermStore, TheoryLit, TheoryResult, TheorySolver};
use ay_euf::{EufModel, EufSolver};
use ay_lia::{LiaModel, LiaSolver};
use ay_lra::{LraModel, LraSolver};
use num_bigint::BigInt;

use crate::combined_solvers::check_loops::{
    debug_nelson_oppen, defer_non_local_result, forward_non_sat, propagate_equalities_to,
};
use crate::combined_solvers::interface_bridge::InterfaceBridge;
use crate::combined_solvers::models::{
    euf_with_int_values, extract_array_model, merge_lia_values, merge_lra_values,
    reconcile_lia_lra_values,
};
use crate::term_helpers::{
    arg_involves_select_or_store, involves_int_arithmetic, involves_real_arithmetic,
    is_select_or_store, is_uf_int_equality, is_uf_real_equality,
};

/// Result of checking all sub-solvers in the N-O fixpoint loop.
/// `(lia_unknown, lra_unknown, deferred_lia, deferred_lra)`.
pub(super) type SubsolverCheckResult =
    Result<(bool, bool, Option<TheoryResult>, Option<TheoryResult>), Box<TheoryResult>>;

/// Trail entry for incremental undo of cross-sort propagations (#5955).
pub(super) enum AufLiraCrossSortTrailEntry {
    ScopeMarker,
    Propagated(TermId, BigInt, Option<PropagationKind>),
    /// Track Int-sorted terms asserted to the Real side (#6198, ported from #6290).
    AssertedRealIntTerm(TermId),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum PropagationKind {
    Bounds,
    Tight,
}

/// Combined Arrays + EUF + LIA + LRA theory solver for QF_AUFLIRA
///
/// This solver supports mixed integer/real arithmetic along with arrays and UF.
///
/// # Nelson-Oppen Interface Term Propagation (#5227)
///
/// Like UfLiaSolver and UfLraSolver, this solver tracks "interface terms" —
/// arithmetic expressions that appear in equalities with uninterpreted function
/// terms. After LIA/LRA solving, we evaluate such terms and propagate equalities
/// with constants to EUF.
///
/// # Cross-Sort Value Propagation (#5955)
///
/// Ported from `LiraSolver` (#4915, #5947). When `to_real(x)` appears in a Real
/// constraint, LIA integer assignments must be forwarded to LRA. Without this,
/// LIRA formulas with arrays can return SAT for UNSAT Big-M patterns.
pub(crate) struct AufLiraSolver<'a> {
    /// Reference to term store for inspecting literal sorts
    pub(super) terms: &'a TermStore,
    /// EUF solver for equality and congruence reasoning
    pub(super) euf: EufSolver<'a>,
    /// Array solver for select/store reasoning
    pub(super) arrays: ArraySolver<'a>,
    /// LIA solver for integer arithmetic
    pub(super) lia: LiaSolver<'a>,
    /// LRA solver for real arithmetic
    pub(super) lra: LraSolver,
    /// Shared Nelson-Oppen interface term tracking (#5227).
    pub(super) interface: InterfaceBridge,
    /// Already-propagated cross-sort (variable, value) pairs for dedup (#5955).
    /// Tracks whether a propagation was bounds-only or tight so a later split
    /// can upgrade bounds to an equality. Uses BigInt keys to avoid i64
    /// truncation collisions on large values (#6150).
    pub(super) propagated_cross_sort: HashMap<(TermId, BigInt), PropagationKind>,
    /// Trail for incremental pop of propagated_cross_sort entries (#5955).
    pub(super) cross_sort_trail: Vec<AufLiraCrossSortTrailEntry>,
    /// Int-sorted terms that occur in literals actually asserted to the Real side.
    /// Ported from LiraSolver (#6290). Prevents registration-artifact Int variables
    /// from participating in cross-sort propagation, which causes spurious conflicts.
    pub(super) asserted_real_int_terms: HashSet<TermId>,
    /// Scope depth counter for push/pop symmetry checking (#4714, #4995).
    pub(super) scope_depth: usize,
}

impl<'a> AufLiraSolver<'a> {
    /// Create a new combined Arrays+EUF+LIA+LRA solver
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        let mut lia = LiaSolver::new(terms);
        lia.set_combined_theory_mode(true);
        let mut lra = LraSolver::new(terms);
        lra.set_combined_theory_mode(true);
        let mut arrays = ArraySolver::new(terms);
        // Defer O(n²) array checks to final_check() at fixpoint (#6282 Packet 2).
        arrays.set_defer_expensive_checks(true);
        arrays.enable_registered_atom_scope(true);
        Self {
            terms,
            euf: EufSolver::new(terms),
            arrays,
            lia,
            lra,
            interface: InterfaceBridge::new(),
            propagated_cross_sort: HashMap::default(),
            cross_sort_trail: Vec::new(),
            asserted_real_int_terms: HashSet::default(),
            scope_depth: 0,
        }
    }

    /// Extract all models for model generation
    pub(crate) fn extract_all_models(
        &mut self,
    ) -> (EufModel, ArrayModel, Option<LiaModel>, LraModel) {
        let mut euf_model = euf_with_int_values(&mut self.euf);
        let mut lia_model = self.lia.extract_model();
        let mut lra_model = self.lra.extract_model();
        let patched_lra_terms = reconcile_lia_lra_values(
            &mut lia_model,
            &mut lra_model,
            &self.lia.shared_equality_terms(),
        );
        if !patched_lra_terms.is_empty() {
            let patched_var_ids: HashSet<u32> = patched_lra_terms
                .iter()
                .filter_map(|term| self.lra.term_to_var().get(term).copied())
                .collect();
            self.lra
                .propagate_model_equalities(&mut lra_model, &patched_var_ids);
        }
        #[cfg(debug_assertions)]
        let lia_value_count = lia_model.as_ref().map_or(0, |m| m.values.len());
        #[cfg(debug_assertions)]
        let lra_value_count = lra_model.values.len();
        merge_lia_values(&mut euf_model, lia_model.as_ref());
        merge_lra_values(&mut euf_model, &lra_model, self.terms);
        // Postcondition: arithmetic values must be subsumed by merged EUF term_values (#4714)
        #[cfg(debug_assertions)]
        {
            debug_assert!(
                euf_model.term_values.len() >= lia_value_count,
                "BUG: AUFLIRA merged EUF model has fewer entries ({}) than LIA values ({})",
                euf_model.term_values.len(),
                lia_value_count,
            );
            debug_assert!(
                euf_model.term_values.len() >= lra_value_count,
                "BUG: AUFLIRA merged EUF model has fewer entries ({}) than LRA values ({})",
                euf_model.term_values.len(),
                lra_value_count,
            );
        }
        let array_model = extract_array_model(&mut self.arrays, &euf_model);
        (euf_model, array_model, lia_model, lra_model)
    }
}

impl TheorySolver for AufLiraSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        self.arrays.register_atom(atom);
        self.lia.register_atom(atom);
        self.lra.register_atom(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        // EUF gets all literals
        self.euf.assert_literal(literal, value);

        // Arrays gets all literals (handles select/store)
        self.arrays.assert_literal(literal, value);

        // Route to LIA if it involves Int arithmetic
        let is_int = involves_int_arithmetic(self.terms, literal);
        let is_real = involves_real_arithmetic(self.terms, literal);
        if is_int {
            self.lia.assert_literal(literal, value);
        } else if let Some((lhs, rhs)) = is_uf_int_equality(self.terms, literal) {
            if value {
                // Forward UF-int equalities to LIA as shared equalities (#4767).
                let reason = TheoryLit::new(literal, true);
                self.lia.assert_shared_equality(lhs, rhs, &[reason]);
            } else {
                // Forward negated UF-int equalities to LIA as shared disequalities (#5228).
                let reason = TheoryLit::new(literal, false);
                self.lia.assert_shared_disequality(lhs, rhs, &[reason]);
            }
        }

        // Route to LRA if it involves Real arithmetic
        if is_real {
            self.track_asserted_real_int_terms(literal); // #6198
            self.lra.assert_literal(literal, value);
        } else if let Some((lhs, rhs)) = is_uf_real_equality(self.terms, literal) {
            self.track_asserted_real_int_terms(literal); // #6198
            if value {
                // Forward UF-real equalities to LRA as shared equalities (#5050).
                let reason = TheoryLit::new(literal, true);
                self.lra.assert_shared_equality(lhs, rhs, &[reason]);
            } else {
                // Forward negated UF-real equalities to LRA as shared disequalities (#5228).
                let reason = TheoryLit::new(literal, false);
                self.lra.assert_shared_disequality(lhs, rhs, &[reason]);
            }
        }

        // Sort routing invariant: a single comparison literal should not be
        // routed to both LIA and LRA (Int and Real operands don't mix in
        // well-sorted SMT-LIB terms). If both fire, the sort predicates
        // may be too permissive.
        debug_assert!(
            !(is_int && is_real),
            "BUG: AUFLIRA assert_literal: literal {literal:?} routed to BOTH LIA and LRA"
        );

        // Track interface terms from all literals (#5227).
        self.interface.track_interface_term(self.terms, literal);
        self.interface.collect_int_constants(self.terms, literal);
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
        let mut pending_cross_sort_split: Option<TheoryResult> = None;

        // #8469: Configure EUF with shared arith terms for unified diseq propagation.
        self.euf
            .set_shared_arith_terms(self.interface.sorted_arith_terms());

        for iteration in 0..max_iters {
            let (lia_is_unknown, lra_is_unknown, deferred_lia_result, deferred_lra_result) =
                match self.check_subsolvers() {
                    Ok(v) => v,
                    Err(result) => return *result,
                };
            let (lia_eq_count, lra_eq_count, euf_to_lia_count, euf_to_lra_count) =
                match self.propagate_theory_equalities(debug, iteration) {
                    Ok(counts) => counts,
                    Err(conflict) => return *conflict,
                };

            if euf_to_lia_count > 0 || euf_to_lra_count > 0 {
                // EUF just injected new arithmetic facts after the LIA/LRA
                // checks for this iteration. Model-dependent bridges must wait
                // until those solvers have rechecked; otherwise AUFLIRA can
                // propagate stale LIA/LRA model values across sorts/scopes.
                continue;
            }

            // Evaluate interface terms under LIA/LRA models and propagate to EUF (#5227).
            let int_bridge_count = self.propagate_int_interface_bridge(debug);
            let real_bridge_count = self.propagate_real_interface_bridge(debug);

            // Cross-sort value/bound propagation LIA → LRA (#5955).
            let (cross_sort_count, cross_sort_split) = self.propagate_cross_sort_values(debug);
            if cross_sort_count > 0 || cross_sort_split.is_some() {
                // A later tight propagation can discharge an earlier bounds-only
                // split request in the same N-O check.
                pending_cross_sort_split = cross_sort_split;
            }

            // Check arrays AFTER equality exchange (#5086).
            let arr_check = self.arrays.check();
            if let Some(result) = forward_non_sat(arr_check) {
                return result;
            }
            // Propagate equalities Arrays → EUF (#6282).
            let arr_eq_count = match propagate_equalities_to(
                &mut self.arrays,
                &mut self.euf,
                debug,
                "AUFLIRA-ARR",
                iteration,
            ) {
                Ok(n) => n,
                Err(conflict) => return conflict,
            };
            let array_progress = match self.propagate_array_index_relations() {
                Ok(progress) => progress,
                Err(result) => return *result,
            };

            let iter_total = lia_eq_count
                + lra_eq_count
                + euf_to_lia_count
                + euf_to_lra_count
                + int_bridge_count
                + real_bridge_count
                + cross_sort_count
                + arr_eq_count;
            if iter_total == 0 && !array_progress {
                match self.handle_fixpoint(
                    debug,
                    lia_is_unknown,
                    lra_is_unknown,
                    deferred_lia_result,
                    deferred_lra_result,
                    pending_cross_sort_split.take(),
                ) {
                    Some(result) => return result,
                    None => continue,
                }
            }

            // Monotonicity: non-fixpoint iterations must make progress
            debug_assert!(
                iter_total > 0 || array_progress,
                "BUG: AUFLIRA N-O iteration {iteration} continued past fixpoint with 0 new equalities and no array progress"
            );

            // Non-convergence is a solver bug — panic in all build modes.
            // Non-convergence within the fixpoint bound is a SOUND fallback, not
            // a crash: the loop ends and returns `TheoryResult::Unknown` below.
            // (Formerly a `did not converge` panic — an abort on a legitimate, if
            // pathological, instance; `unknown` is always sound. #8319: a capped
            // `--max-fixpoint-rounds` reaches the same fallback.)
        }
        TheoryResult::Unknown
    }

    fn check_during_propagate(&mut self) -> TheoryResult {
        let lia_result = defer_non_local_result(self.lia.check_during_propagate());
        if !matches!(lia_result, TheoryResult::Sat) {
            return lia_result;
        }

        let lra_result = defer_non_local_result(self.lra.check_during_propagate());
        if !matches!(lra_result, TheoryResult::Sat) {
            return lra_result;
        }

        let euf_result = defer_non_local_result(self.euf.check_during_propagate());
        if !matches!(euf_result, TheoryResult::Sat) {
            return euf_result;
        }

        let arrays_result = defer_non_local_result(self.arrays.check_during_propagate());
        if !matches!(arrays_result, TheoryResult::Sat) {
            return arrays_result;
        }

        TheoryResult::Sat
    }

    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    delegate_propagate!(euf, arrays, lia, lra);

    fn supports_farkas_semantic_check(&self) -> bool {
        true
    }

    fn note_applied_theory_lemma(&mut self, clause: &[TheoryLit]) {
        self.arrays.note_applied_theory_lemma(clause);
    }

    fn push(&mut self) {
        self.scope_depth += 1;
        self.euf.push();
        self.arrays.push();
        self.lia.push();
        self.lra.push();
        self.interface.push();
        self.cross_sort_trail
            .push(AufLiraCrossSortTrailEntry::ScopeMarker);
    }

    fn pop(&mut self) {
        if self.scope_depth == 0 {
            // Graceful no-op: pop at depth 0 is a caller error but not fatal.
            return;
        }
        self.scope_depth -= 1;
        self.euf.pop();
        self.arrays.pop();
        self.lia.pop();
        self.lra.pop();
        self.interface.pop();

        while let Some(entry) = self.cross_sort_trail.pop() {
            match entry {
                AufLiraCrossSortTrailEntry::ScopeMarker => break,
                AufLiraCrossSortTrailEntry::Propagated(term, key, prev_kind) => {
                    if let Some(prev_kind) = prev_kind {
                        self.propagated_cross_sort.insert((term, key), prev_kind);
                    } else {
                        self.propagated_cross_sort.remove(&(term, key));
                    }
                }
                AufLiraCrossSortTrailEntry::AssertedRealIntTerm(term) => {
                    self.asserted_real_int_terms.remove(&term);
                }
            }
        }
    }

    fn reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: AufLiraSolver::reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.euf.reset();
        self.arrays.reset();
        self.lia.reset();
        self.lra.reset();
        self.interface.reset();
        self.propagated_cross_sort.clear();
        self.cross_sort_trail.clear();
        self.asserted_real_int_terms.clear();
    }

    fn soft_reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: AufLiraSolver::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.euf.soft_reset();
        self.arrays.soft_reset();
        self.lia.soft_reset();
        self.lra.soft_reset();
        self.interface.reset();
        self.propagated_cross_sort.clear();
        self.cross_sort_trail.clear();
        self.asserted_real_int_terms.clear();
    }

    fn supports_theory_aware_branching(&self) -> bool {
        // Array-involving combined theories always benefit from theory-aware
        // branching (#6282). See auf_lia.rs for rationale.
        true
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        // Index equality atoms: suggest false (distinct).
        // See auf_lia.rs for full rationale (#6282).
        if let TermData::App(ref sym, ref args) = self.terms.get(atom) {
            if sym.name() == "=" && args.len() == 2 {
                let lhs_is_simple = !is_select_or_store(self.terms, args[0]);
                let rhs_is_simple = !is_select_or_store(self.terms, args[1]);
                if lhs_is_simple && rhs_is_simple {
                    return Some(false);
                }
            }
        }
        // Suppress LRA phase hints for inequality atoms involving select/store (#6303).
        // See auf_lia.rs suggest_phase for full rationale.
        if let TermData::App(ref sym, ref args) = self.terms.get(atom) {
            let name = sym.name();
            if (name == "<=" || name == ">=" || name == "<" || name == ">")
                && args.len() == 2
                && (arg_involves_select_or_store(self.terms, args[0])
                    || arg_involves_select_or_store(self.terms, args[1]))
            {
                return None;
            }
        }
        self.lra.suggest_phase(atom)
    }

    fn sort_atom_index(&mut self) {
        self.lra.sort_atom_index();
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        self.lra.generate_bound_axiom_terms()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        self.lra.generate_incremental_bound_axioms(atom)
    }
}
