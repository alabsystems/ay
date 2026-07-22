// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Combined EUF + Arrays + Map + LIA theory solver for QF_MAP / QF_MAPLIA.
//!
//! The native map theory ([`ay_map::MapSolver`]) reasons about value/domain
//! reads and subset over the `Map(K, V) = Array(K → V)` value carrier and its
//! parallel `Array(K → Bool)` domain carrier `(map.dom m)`. The array solver
//! decides both carriers (`select`/`store` read-through) and map equality
//! (extensionality); LIA decides any integer arithmetic over Int-valued
//! `map.get` reads / map-size relations, which it treats as opaque Int
//! variables. EUF supplies congruence across all sorts.
//!
//! ## Soundness: the map ↔ LIA bridge (Nelson-Oppen)
//!
//! Int-valued value reads are bridged into LIA as opaque Ints. The combination
//! is sound because:
//!
//! 1. **Ground get/dom equations.** `get(insert(m,k,v),k)=v`,
//!    `dom(insert(m,k,v))[k]=true`, `dom(remove(m,k))[k]=false`, and
//!    `dom(empty)=const-false` are all decided directly by the array solver via
//!    `store`/const-array read-through (the frontend pushes the readers through
//!    the constructors), so no separate axiom is needed for them.
//! 2. **Per-witness subset↔key obligations.** `subset(m,n) ⇒ (dom(m)[k] ⇒
//!    dom(n)[k]) ∧ (dom(m)[k] ⇒ get(m,k)=get(n,k))` over present ground keys are
//!    ground implications injected by the executor and decided by the
//!    array/EUF/LIA combination.
//!
//! The [`MapSolver`] itself only contributes the parts that need theory
//! reasoning beyond the ground array/LIA facts: subset reflexivity refutation.
//! It is **fail-closed**: if a map obligation falls outside the saturatable
//! fragment (polymorphic / higher-order image ops), it returns `Unknown` and
//! this adapter forwards that `Unknown` verdict rather than guessing.

use ay_arrays::{ArrayModel, ArraySolver};
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{TermId, TermStore, TheoryLit, TheoryResult, TheorySolver};
use ay_euf::{EufModel, EufSolver};
use ay_lia::{LiaModel, LiaSolver};
use ay_map::MapSolver;

use crate::combined_solvers::check_loops::{
    debug_nelson_oppen, defer_non_local_result, forward_non_sat, propagate_all_to,
    propagate_equalities_to, triage_lia_result,
};
use crate::combined_solvers::interface_bridge::InterfaceBridge;
use crate::combined_solvers::models::{euf_with_int_values, extract_array_model};
use crate::term_helpers::contains_arithmetic_ops;
use ay_core::term::TermData;

/// Result of a single Nelson-Oppen iteration.
enum IterResult {
    /// Fixpoint or conflict reached — return this result.
    Done(TheoryResult),
    /// New equalities found — continue iterating.
    Continue,
}

/// Combined EUF + Arrays + Map + LIA theory solver.
pub(crate) struct UfMapLiaSolver<'a> {
    /// Reference to term store for inspecting literals.
    terms: &'a TermStore,
    /// EUF solver for equality and congruence reasoning.
    euf: EufSolver<'a>,
    /// Array solver: decides the value/domain carriers (select/store) and map
    /// equality.
    arrays: ArraySolver<'a>,
    /// Native map solver: subset reflexivity, fail-closed.
    map: MapSolver<'a>,
    /// LIA solver: integer arithmetic over Int-valued map reads.
    lia: LiaSolver<'a>,
    /// Shared Nelson-Oppen interface term tracking.
    interface: InterfaceBridge,
    /// Scope depth counter for push/pop symmetry checking.
    scope_depth: usize,
}

impl<'a> UfMapLiaSolver<'a> {
    /// Create a new combined EUF+Arrays+Map+LIA solver.
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        let mut lia = LiaSolver::new(terms);
        lia.set_combined_theory_mode(true);
        let mut arrays = ArraySolver::new(terms);
        arrays.set_defer_expensive_checks(true);
        arrays.enable_registered_atom_scope(true);
        Self {
            terms,
            euf: EufSolver::new(terms),
            arrays,
            map: MapSolver::new(terms),
            lia,
            interface: InterfaceBridge::new(),
            scope_depth: 0,
        }
    }

    /// Extract all models for model generation.
    pub(crate) fn extract_models(&mut self) -> (EufModel, ArrayModel, Option<LiaModel>) {
        let euf_model = euf_with_int_values(&mut self.euf);
        let lia_model = self.lia.extract_model();
        let array_model = extract_array_model(&mut self.arrays, &euf_model);
        (euf_model, array_model, lia_model)
    }

    /// Replay learned LIA cuts into the freshly-created theory.
    pub(crate) fn replay_learned_cuts(&mut self) {
        self.lia.replay_learned_cuts();
    }

    /// Identity accessor for split-loop macro compatibility.
    pub(crate) fn lra_solver(&self) -> &Self {
        self
    }

    /// Collect all bound conflicts from the inner LIA solver.
    pub(crate) fn collect_all_bound_conflicts(
        &self,
        skip_first: bool,
    ) -> Vec<ay_core::TheoryConflict> {
        self.lia.collect_all_bound_conflicts(skip_first)
    }

    /// Export learned LIA state for cross-iteration persistence.
    pub(crate) fn take_learned_state(
        &mut self,
    ) -> (Vec<ay_lia::StoredCut>, HashSet<ay_lia::HnfCutKey>) {
        self.lia.take_learned_state()
    }

    /// Import learned LIA state from a previous iteration.
    pub(crate) fn import_learned_state(
        &mut self,
        cuts: Vec<ay_lia::StoredCut>,
        seen: HashSet<ay_lia::HnfCutKey>,
    ) {
        self.lia.import_learned_state(cuts, seen);
    }

    /// Export Diophantine solver state for cross-iteration persistence.
    pub(crate) fn take_dioph_state(&mut self) -> ay_lia::DiophState {
        self.lia.take_dioph_state()
    }

    /// Import Diophantine solver state from a previous iteration.
    pub(crate) fn import_dioph_state(&mut self, state: ay_lia::DiophState) {
        self.lia.import_dioph_state(state);
    }

    /// Whether a literal references a `map.*` symbol (so LIA must see it for the
    /// map↔LIA bridge when value reads are Int-valued).
    fn references_map(&self, literal: TermId) -> bool {
        let mut stack = vec![literal];
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name().starts_with("map.") {
                        return true;
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, e) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        false
    }

    /// Run one iteration of the Nelson-Oppen fixpoint loop.
    #[allow(clippy::result_large_err)]
    fn check_iteration(&mut self, debug: bool, iteration: usize) -> IterResult {
        // 1. Map: fail-closed Unknown / structural conflicts.
        let map_result = self.map.check();
        if matches!(map_result, TheoryResult::Unknown) {
            // Out-of-fragment: forward Unknown, never guess.
            return IterResult::Done(TheoryResult::Unknown);
        }
        if let Some(r) = forward_non_sat(map_result) {
            return IterResult::Done(r);
        }

        // 2. Propagate Map → EUF equalities (none today, but channel is sound).
        let map_eq = match propagate_equalities_to(
            &mut self.map,
            &mut self.euf,
            debug,
            "UFMAPLIA-MAP",
            iteration,
        ) {
            Ok(n) => n,
            Err(c) => return IterResult::Done(c),
        };

        // 3. Check LIA — Unsat returns immediately; splits deferred.
        let lia_result = self.lia.check();
        let lia_is_unknown = matches!(&lia_result, TheoryResult::Unknown);
        let (deferred_lia, lia_early) = triage_lia_result(lia_result);
        if let Some(early) = lia_early {
            return IterResult::Done(early);
        }

        // 4. Propagate LIA → EUF equalities.
        let lia_eq = match propagate_equalities_to(
            &mut self.lia,
            &mut self.euf,
            debug,
            "UFMAPLIA-LIA",
            iteration,
        ) {
            Ok(n) => n,
            Err(c) => return IterResult::Done(c),
        };

        // 5. Check EUF.
        if let Some(r) = forward_non_sat(self.euf.check()) {
            return IterResult::Done(r);
        }

        // 6. Check Arrays AFTER equality exchange (value/domain carriers).
        if let Some(r) = forward_non_sat(self.arrays.check()) {
            return IterResult::Done(r);
        }
        let arr_eq = match propagate_equalities_to(
            &mut self.arrays,
            &mut self.euf,
            debug,
            "UFMAPLIA-ARR",
            iteration,
        ) {
            Ok(n) => n,
            Err(c) => return IterResult::Done(c),
        };

        // 7. Propagate EUF → LIA equalities + disequalities (unified).
        let euf_lia_counts = match propagate_all_to(
            &mut self.euf,
            &mut self.lia,
            debug,
            "UFMAPLIA-EUF-LIA",
            iteration,
        ) {
            Ok(c) => c,
            Err(c) => return IterResult::Done(c),
        };
        // 8. Propagate EUF → Map equalities.
        let euf_map = match propagate_equalities_to(
            &mut self.euf,
            &mut self.map,
            debug,
            "UFMAPLIA-EUF-MAP",
            iteration,
        ) {
            Ok(n) => n,
            Err(c) => return IterResult::Done(c),
        };

        if map_eq
            + lia_eq
            + arr_eq
            + euf_lia_counts.equalities
            + euf_map
            + euf_lia_counts.disequalities
            == 0
        {
            let _ = (debug, iteration);
            if lia_is_unknown {
                return IterResult::Done(TheoryResult::Unknown);
            }
            if let Some(split) = deferred_lia {
                return IterResult::Done(split);
            }
            return IterResult::Done(TheoryResult::Sat);
        }
        IterResult::Continue
    }
}

impl TheorySolver for UfMapLiaSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        self.arrays.register_atom(atom);
        self.lia.register_atom(atom);
        self.map.register_atom(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.euf.assert_literal(literal, value);
        self.arrays.assert_literal(literal, value);
        self.map.assert_literal(literal, value);
        // LIA must see literals with arithmetic OR any map.* reference so the
        // map↔LIA bridge (Int-valued value reads, subset↔key obligations) is
        // enforced.
        if contains_arithmetic_ops(self.terms, literal) || self.references_map(literal) {
            self.lia.assert_literal(literal, value);
        }
        self.interface.track_interface_term(self.terms, literal);
        self.interface.collect_int_constants(self.terms, literal);
    }

    fn check(&mut self) -> TheoryResult {
        let debug = debug_nelson_oppen();
        const MAX_ITERATIONS: usize = 100;
        let max_iters = crate::theory_debug_flags::max_fixpoint_rounds()
            .unwrap_or(MAX_ITERATIONS)
            .min(MAX_ITERATIONS);

        self.euf
            .set_shared_arith_terms(self.interface.sorted_arith_terms());
        for iteration in 0..max_iters {
            match self.check_iteration(debug, iteration) {
                IterResult::Done(result) => return result,
                IterResult::Continue => {}
            }
            // Non-convergence within the fixpoint bound is a SOUND fallback, not
            // a crash: the loop ends and returns `TheoryResult::Unknown` below.
            // (Formerly a `did not converge` debug panic — `unknown` is always
            // sound. #8319: a capped `--max-fixpoint-rounds` reaches it too.)
        }
        TheoryResult::Unknown
    }

    fn check_during_propagate(&mut self) -> TheoryResult {
        let lia_result = defer_non_local_result(self.lia.check_during_propagate());
        if !matches!(lia_result, TheoryResult::Sat) {
            return lia_result;
        }
        let euf_result = defer_non_local_result(self.euf.check_during_propagate());
        if !matches!(euf_result, TheoryResult::Sat) {
            return euf_result;
        }
        let arrays_result = defer_non_local_result(self.arrays.check_during_propagate());
        if !matches!(arrays_result, TheoryResult::Sat) {
            return arrays_result;
        }
        // Map: fail-closed Unknown is not a BCP-local conflict; only forward
        // genuine Unsat here, defer Unknown to the full check().
        let map_result = self.map.check_during_propagate();
        match map_result {
            TheoryResult::Unsat(_) => map_result,
            _ => TheoryResult::Sat,
        }
    }

    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    delegate_propagate!(euf, arrays, map, lia);

    fn note_applied_theory_lemma(&mut self, clause: &[TheoryLit]) {
        self.arrays.note_applied_theory_lemma(clause);
    }

    fn supports_theory_aware_branching(&self) -> bool {
        self.lia.supports_theory_aware_branching()
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        self.lia.suggest_phase(atom)
    }

    fn sort_atom_index(&mut self) {
        self.lia.sort_atom_index();
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        self.lia.generate_bound_axiom_terms()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        self.lia.generate_incremental_bound_axioms(atom)
    }

    fn push(&mut self) {
        self.scope_depth += 1;
        self.euf.push();
        self.arrays.push();
        self.map.push();
        self.lia.push();
        self.interface.push();
    }

    fn pop(&mut self) {
        if self.scope_depth == 0 {
            return;
        }
        self.scope_depth -= 1;
        self.euf.pop();
        self.arrays.pop();
        self.map.pop();
        self.lia.pop();
        self.interface.pop();
    }

    fn reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: UfMapLiaSolver::reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.euf.reset();
        self.arrays.reset();
        self.map.reset();
        self.lia.reset();
        self.interface.reset();
    }

    fn soft_reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: UfMapLiaSolver::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.euf.soft_reset();
        self.arrays.soft_reset();
        self.map.soft_reset();
        self.lia.soft_reset();
        self.interface.reset();
    }
}
