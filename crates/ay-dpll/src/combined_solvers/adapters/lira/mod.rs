// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Combined LIA + LRA theory solver for QF_LIRA.
//!
//! This solver routes literals to LIA or LRA based on the sorts of their operands:
//! - Int-sorted comparisons/equalities go to LIA
//! - Real-sorted comparisons/equalities go to LRA
//! - The SAT solver handles the Boolean combination
//!
//! # Cross-Sort Value Propagation (#4915)
//!
//! When `to_real(x)` appears in a Real constraint, LRA (after the `to_real`
//! identity fix) shares the same TermId for `x` as LIA. After LIA determines
//! a tight bound (e.g., `x = 1`), this value must be forwarded to LRA so it
//! can detect conflicts with Real constraints on the same variable.
//!
//! Standard N-O propagation only exchanges equalities between variables with
//! the same value (not variable-constant bindings). The `propagate_cross_sort_values`
//! method supplements this with direct tight-bound forwarding.

// #8529: Use deterministic hash maps/sets in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
mod cross_sort;
mod model;

use ay_core::term::{Constant, TermData};
use ay_core::{TermId, TermStore, TheoryResult, TheorySolver};
use ay_lia::LiaSolver;
use ay_lra::LraSolver;
use num_bigint::BigInt;

use crate::combined_solvers::check_loops::{
    assert_fixpoint_convergence, debug_nelson_oppen, defer_non_local_result,
    propagate_equalities_to, triage_lia_result, triage_lra_result_deferred,
};
use crate::term_helpers::{involves_int_arithmetic, involves_real_arithmetic};

/// Combined LIA + LRA theory solver for QF_LIRA.
pub(crate) struct LiraSolver<'a> {
    /// Reference to term store for inspecting literal sorts
    pub(super) terms: &'a TermStore,
    /// LIA solver for integer arithmetic
    pub(super) lia: LiaSolver<'a>,
    /// LRA solver for real arithmetic
    pub(super) lra: LraSolver,
    /// Already-propagated cross-sort (variable, value) pairs for deduplication.
    /// Tracks whether the propagation was bounds-only or a tight value so
    /// bounds-only propagations can be upgraded after a split establishes
    /// equality. Uses BigInt keys to avoid i64 truncation collisions on large
    /// values (#6150).
    pub(super) propagated_cross_sort: HashMap<(TermId, BigInt), PropagationKind>,
    /// Trail for incremental pop of propagated_cross_sort entries.
    pub(super) cross_sort_trail: Vec<CrossSortTrailEntry>,
    /// Int-sorted terms that occur in literals actually asserted to the Real side.
    pub(super) asserted_real_int_terms: HashSet<TermId>,
    /// Trail for incremental pop of asserted_real_int_terms.
    pub(super) asserted_real_int_term_trail: Vec<AssertedRealIntTermTrailEntry>,
    /// Single-variable Int bound literals routed to LIA, recorded as
    /// `(literal, value, subject_term)` so they can be forwarded to LRA at
    /// check time when the subject turns out to be Real-shared
    /// (#to-real-only-int-integrality). See `forward_shared_int_bound_literals`.
    pending_int_bound_literals: Vec<(TermId, bool, TermId)>,
    /// Per-scope lengths of `pending_int_bound_literals` for incremental pop.
    pending_int_bound_scope_lens: Vec<usize>,
    /// Bound literals already forwarded to LRA (deduplication).
    forwarded_int_bound_literals: HashSet<(TermId, bool)>,
    /// Trail for incremental pop of `forwarded_int_bound_literals`. The LRA
    /// assertion itself is popped by `lra.pop()`; this trail keeps the dedup
    /// set symmetric so the literal is re-forwarded after backtracking.
    forwarded_int_bound_trail: Vec<ForwardedIntBoundTrailEntry>,
    /// Scope depth counter for push/pop symmetry checking (#4714, #4995).
    pub(super) scope_depth: usize,
}

#[derive(Clone, PartialEq, Eq)]
pub(super) enum PropagationKind {
    /// Bounds-only forwarding, fingerprinted by the forwarded `(value, strict)`
    /// pairs. The fingerprint lets a later, tighter (but still non-tight) bound
    /// set re-forward instead of being deduplicated away: without it, a split
    /// atom that improves LIA's bounds while leaving LIA's value (the dedup
    /// key) unchanged would never reach LRA, which can then hold a shared Int
    /// variable at a stale non-integral value forever
    /// (#to-real-only-int-integrality).
    Bounds {
        lower: Option<(ay_lra::rational::Rational, bool)>,
        upper: Option<(ay_lra::rational::Rational, bool)>,
    },
    Tight,
}

pub(super) enum CrossSortTrailEntry {
    ScopeMarker,
    Propagated(TermId, BigInt, Option<PropagationKind>),
}

pub(super) enum AssertedRealIntTermTrailEntry {
    ScopeMarker,
    Term(TermId),
}

enum ForwardedIntBoundTrailEntry {
    ScopeMarker,
    Lit(TermId, bool),
}

impl<'a> LiraSolver<'a> {
    /// Create a new combined LIA+LRA solver
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        let mut lia = LiaSolver::new(terms);
        lia.set_combined_theory_mode(true);
        let mut lra = LraSolver::new(terms);
        lra.set_combined_theory_mode(true);
        Self {
            terms,
            lia,
            lra,
            propagated_cross_sort: HashMap::default(),
            cross_sort_trail: Vec::new(),
            asserted_real_int_terms: HashSet::default(),
            asserted_real_int_term_trail: Vec::new(),
            pending_int_bound_literals: Vec::new(),
            pending_int_bound_scope_lens: Vec::new(),
            forwarded_int_bound_literals: HashSet::default(),
            forwarded_int_bound_trail: Vec::new(),
            scope_depth: 0,
        }
    }

    /// If `literal` (possibly negated) is a two-argument comparison or
    /// equality between a non-constant Int-sorted term and an Int constant,
    /// return the non-constant side (#to-real-only-int-integrality).
    fn int_bound_atom_subject(&self, literal: TermId) -> Option<TermId> {
        let atom = match self.terms.get(literal) {
            TermData::Not(inner) => *inner,
            _ => literal,
        };
        let TermData::App(ay_core::term::Symbol::Named(name), args) = self.terms.get(atom) else {
            return None;
        };
        if !matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=") || args.len() != 2 {
            return None;
        }
        let is_int_const =
            |t: TermId| matches!(self.terms.get(t), TermData::Const(Constant::Int(_)));
        let subject = match (is_int_const(args[0]), is_int_const(args[1])) {
            (true, false) => args[1],
            (false, true) => args[0],
            _ => return None,
        };
        matches!(self.terms.sort(subject), ay_core::Sort::Int).then_some(subject)
    }

    /// Forward single-variable Int bound literals over Real-shared Int terms
    /// to LRA (#to-real-only-int-integrality).
    ///
    /// An Int variable that occurs ONLY under `to_real` in Real literals gets
    /// its bound atoms (including branch-and-bound split atoms) routed
    /// exclusively to LIA, while LRA owns the variable's value through the
    /// shared TermId. When LIA solves those bounds without materializing
    /// simplex state for the variable, cross-sort value propagation has
    /// nothing to forward, so LRA can keep a non-integral (or out-of-bounds)
    /// value indefinitely and the integrality split loop livelocks.
    ///
    /// Forwarding the literal itself is sound: the shared TermId denotes the
    /// same value on both sides, so the constraint is identical — LRA merely
    /// interprets it over the rational relaxation. It also keeps conflicts
    /// involving these atoms LRA-internal, with verifiable Farkas
    /// certificates. Only `term <op> constant` shapes over terms recorded in
    /// `asserted_real_int_terms` are forwarded, so pure-Int problem structure
    /// never leaks into LRA.
    fn forward_shared_int_bound_literals(&mut self) {
        for i in 0..self.pending_int_bound_literals.len() {
            let (literal, value, subject) = self.pending_int_bound_literals[i];
            if !self.asserted_real_int_terms.contains(&subject)
                || self
                    .forwarded_int_bound_literals
                    .contains(&(literal, value))
            {
                continue;
            }
            self.lra.assert_literal(literal, value);
            self.forwarded_int_bound_literals.insert((literal, value));
            self.forwarded_int_bound_trail
                .push(ForwardedIntBoundTrailEntry::Lit(literal, value));
        }
    }

    fn record_asserted_real_int_term(&mut self, term: TermId) {
        if self.asserted_real_int_terms.insert(term) {
            self.asserted_real_int_term_trail
                .push(AssertedRealIntTermTrailEntry::Term(term));
        }
    }

    pub(crate) fn take_learned_state(
        &mut self,
    ) -> (Vec<ay_lia::StoredCut>, HashSet<ay_lia::HnfCutKey>) {
        self.lia.take_learned_state()
    }

    pub(crate) fn import_learned_state(
        &mut self,
        cuts: Vec<ay_lia::StoredCut>,
        seen: HashSet<ay_lia::HnfCutKey>,
    ) {
        self.lia.import_learned_state(cuts, seen);
    }

    pub(crate) fn take_dioph_state(&mut self) -> ay_lia::DiophState {
        self.lia.take_dioph_state()
    }

    pub(crate) fn import_dioph_state(&mut self, state: ay_lia::DiophState) {
        self.lia.import_dioph_state(state);
    }

    #[expect(dead_code, reason = "used by incremental split-loop conflict macros")]
    pub(crate) fn collect_all_bound_conflicts(
        &self,
        skip_first: bool,
    ) -> Vec<ay_core::TheoryConflict> {
        let mut lia_conflicts = self.lia.collect_all_bound_conflicts(false);
        let lra_conflicts = self.lra.collect_all_bound_conflicts(false);
        if skip_first && !lia_conflicts.is_empty() {
            lia_conflicts.remove(0);
        }
        if skip_first && lia_conflicts.is_empty() {
            return lra_conflicts.into_iter().skip(1).collect();
        }
        lia_conflicts.into_iter().chain(lra_conflicts).collect()
    }

    /// Track Int-sorted terms that occur in literals routed to the Real solver.
    ///
    /// `register_atom()` intentionally over-registers atoms in LRA so metadata like
    /// `to_int` survives until check-time. Cross-sort propagation cannot treat
    /// registration artifacts as proof that an Int term actually participates in a
    /// Real assertion, so this set is populated only from `assert_literal()`.
    fn track_asserted_real_int_terms(&mut self, literal: TermId) {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![literal];

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }

            if matches!(self.terms.sort(term), ay_core::Sort::Int)
                && !matches!(self.terms.get(term), TermData::Const(Constant::Int(_)))
            {
                self.record_asserted_real_int_term(term);
            }

            stack.extend(self.terms.children(term));
        }
    }

    /// Replay learned cuts into the LRA solver (#6665).
    ///
    /// Forwards to the standalone LRA solver. The LIA solver's internal LRA
    /// state is managed separately by LIA's own replay_learned_cuts.
    pub(crate) fn replay_learned_cuts(&mut self) {
        self.lra.replay_learned_cuts();
        self.lia.replay_learned_cuts();
    }

    /// Get the standalone LRA solver for bound conflict collection (#6665).
    pub(crate) fn lra_solver(&self) -> &LraSolver {
        &self.lra
    }

    /// Clear all Int-bound forwarding state (reset/soft_reset).
    fn clear_int_bound_forwarding(&mut self) {
        self.pending_int_bound_literals.clear();
        self.pending_int_bound_scope_lens.clear();
        self.forwarded_int_bound_literals.clear();
        self.forwarded_int_bound_trail.clear();
    }
}

impl TheorySolver for LiraSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        self.lia.register_atom(atom);
        self.lra.register_atom(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        // Route to LIA if it involves Int arithmetic
        let is_int = involves_int_arithmetic(self.terms, literal);
        let is_real = involves_real_arithmetic(self.terms, literal);
        if is_int {
            self.lia.assert_literal(literal, value);
            // #to-real-only-int-integrality: record single-variable bound
            // literals; check() forwards them to LRA when the subject is
            // Real-shared (which may only become known later).
            if let Some(subject) = self.int_bound_atom_subject(literal) {
                self.pending_int_bound_literals
                    .push((literal, value, subject));
            }
        }

        // Route to LRA if it involves Real arithmetic
        if is_real {
            self.track_asserted_real_int_terms(literal);
            self.lra.assert_literal(literal, value);
        }

        // Sort routing invariant: same as AUFLIRA — a single literal should
        // not match both Int and Real sort predicates.
        debug_assert!(
            !(is_int && is_real),
            "BUG: LIRA assert_literal: literal {literal:?} routed to BOTH LIA and LRA"
        );
    }

    fn check(&mut self) -> TheoryResult {
        let debug = debug_nelson_oppen();
        const MAX_ITERATIONS: usize = 100;
        // #8319: AY_MAX_FIXPOINT_ROUNDS caps the N-O loop for debugging.
        let max_iters = crate::theory_debug_flags::max_fixpoint_rounds()
            .unwrap_or(MAX_ITERATIONS)
            .min(MAX_ITERATIONS);
        let mut pending_cross_sort_split: Option<TheoryResult> = None;

        // #to-real-only-int-integrality: give LRA the Int-side bound atoms of
        // Real-shared Int variables so its model respects them directly (the
        // cross-sort LIA -> LRA bridge cannot forward bounds for variables LIA
        // solves without materializing simplex state).
        self.forward_shared_int_bound_literals();

        // #8747: Register `(to_int x)` TermIds as asserted-real-int terms so
        // that cross-sort propagation forwards the LIA-side value of
        // `(to_int x)` back to LRA. `(to_int x)` is Int-sorted but
        // participates implicitly in the Real tableau through the floor axiom
        // `x - to_int(x) ∈ [0, 1)` injected in `inject_to_int_axioms`. Without
        // this registration, formulas like `(= (to_int x) 3) ∧ (< x 3.0)`
        // return false SAT because the LIA equality never reaches the Real
        // side where the floor axiom would surface the conflict.
        {
            let to_int_terms = self.lra.to_int_terms().to_vec();
            if !to_int_terms.is_empty() {
                let var_to_term: HashMap<u32, TermId> = self
                    .lra
                    .term_to_var()
                    .iter()
                    .map(|(&t, &v)| (v, t))
                    .collect();
                for (to_int_var, _inner_arg) in &to_int_terms {
                    if let Some(&to_int_term) = var_to_term.get(to_int_var) {
                        self.record_asserted_real_int_term(to_int_term);
                    }
                }
            }
        }

        for iteration in 0..max_iters {
            // LIA: splits deferred until cross-sort propagation completes (#4915).
            let lia_result = self.lia.check();
            let lia_is_unknown = matches!(&lia_result, TheoryResult::Unknown);
            let (deferred_lia_result, lia_early) = triage_lia_result(lia_result);
            if let Some(early) = lia_early {
                return early;
            }
            let lia_eq_count = match propagate_equalities_to(
                &mut self.lia,
                &mut self.lra,
                debug,
                "LIRA-LIA",
                iteration,
            ) {
                Ok(n) => n,
                Err(conflict) => return conflict,
            };

            // LRA: check before cross-sort so term_to_var is populated.
            //
            // #7448: Use triage_lra_result_deferred instead of triage_lra_result.
            // triage_lra_result early-returns NeedModelEquality/NeedDisequalitySplit,
            // which skips cross-sort propagation entirely. For Big-M patterns
            // like (* 1000000.0 (to_real phase)), LRA discovers model equalities
            // before cross-sort can bridge LIA's integer bounds to LRA. Without
            // deferral, the loop cycles NeedModelEquality → encode → re-check
            // without ever propagating phase's integrality, producing Unknown.
            let lra_result = self.lra.check();
            let lra_is_unknown = matches!(&lra_result, TheoryResult::Unknown);
            let (deferred_lra_result, lra_early) = triage_lra_result_deferred(lra_result);
            if let Some(early) = lra_early {
                return early;
            }
            let lra_eq_count = match propagate_equalities_to(
                &mut self.lra,
                &mut self.lia,
                debug,
                "LIRA-LRA",
                iteration,
            ) {
                Ok(n) => n,
                Err(conflict) => return conflict,
            };

            // Cross-sort value/bound propagation LIA → LRA (#4915, #5947).
            let (cross_sort_count, cross_sort_split) = self.propagate_cross_sort_values(debug);
            if cross_sort_split.is_some() {
                pending_cross_sort_split = cross_sort_split;
            }

            // Cross-sort propagation for to_int terms: LRA → LIA (#5944).
            // After LRA determines x's value, compute floor(x) and assert
            // to_int(x) = floor(x) as tight bounds in LIA's internal solver.
            let to_int_count = self.propagate_to_int_values(debug);

            if lia_eq_count == 0 && lra_eq_count == 0 && cross_sort_count == 0 && to_int_count == 0
            {
                if lia_is_unknown || lra_is_unknown {
                    return TheoryResult::Unknown;
                }
                if debug && iteration > 0 {
                    safe_eprintln!("[N-O LIRA] Fixpoint after {} iterations", iteration + 1);
                }
                if let Some(split) = deferred_lia_result {
                    return split;
                }
                // #5947: shared Int vars must be case-split before speculative
                // LRA model equalities. Otherwise the equality round-trip can
                // short-circuit the split loop and leave the Real side with
                // only loose cross-sort bounds, producing invalid SAT models.
                if let Some(split) = pending_cross_sort_split {
                    return split;
                }
                // #to-real-only-int-integrality: an Int variable occurring
                // ONLY under `to_real` in Real literals never registers with
                // LIA, so the cross-sort machinery above (keyed on LIA's
                // term_to_var) never sees it and LRA may pin it non-integrally
                // (e.g. `(= (to_real xi) (/ 7 2))` pins xi = 7/2). Request a
                // branch-and-bound split so DPLL either integralizes the
                // variable or flips the offending literal.
                if let Some(split) = self.non_integral_int_value_split(debug) {
                    return split;
                }
                // #7448: return deferred LRA results (NeedModelEquality,
                // NeedDisequalitySplit, NeedExpressionSplit) at fixpoint,
                // after cross-sort propagation has had a chance to run.
                if let Some(lra_deferred) = deferred_lra_result {
                    return lra_deferred;
                }
                assert_fixpoint_convergence("LIRA", &mut [&mut self.lia, &mut self.lra]);
                return TheoryResult::Sat;
            }
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

        TheoryResult::Sat
    }

    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    delegate_propagate!(lia, lra);

    fn supports_farkas_semantic_check(&self) -> bool {
        true
    }

    fn push(&mut self) {
        self.scope_depth += 1;
        self.lia.push();
        self.lra.push();
        self.cross_sort_trail.push(CrossSortTrailEntry::ScopeMarker);
        self.asserted_real_int_term_trail
            .push(AssertedRealIntTermTrailEntry::ScopeMarker);
        self.pending_int_bound_scope_lens
            .push(self.pending_int_bound_literals.len());
        self.forwarded_int_bound_trail
            .push(ForwardedIntBoundTrailEntry::ScopeMarker);
    }

    fn pop(&mut self) {
        if self.scope_depth == 0 {
            // Graceful no-op: pop at depth 0 is a caller error but not fatal.
            return;
        }
        self.scope_depth -= 1;
        self.lia.pop();
        self.lra.pop();
        while let Some(entry) = self.cross_sort_trail.pop() {
            match entry {
                CrossSortTrailEntry::ScopeMarker => break,
                CrossSortTrailEntry::Propagated(term, key, prev_kind) => match prev_kind {
                    None => {
                        self.propagated_cross_sort.remove(&(term, key));
                    }
                    Some(kind) => {
                        self.propagated_cross_sort.insert((term, key), kind);
                    }
                },
            }
        }
        while let Some(entry) = self.asserted_real_int_term_trail.pop() {
            match entry {
                AssertedRealIntTermTrailEntry::ScopeMarker => break,
                AssertedRealIntTermTrailEntry::Term(term) => {
                    self.asserted_real_int_terms.remove(&term);
                }
            }
        }
        if let Some(len) = self.pending_int_bound_scope_lens.pop() {
            self.pending_int_bound_literals.truncate(len);
        }
        while let Some(entry) = self.forwarded_int_bound_trail.pop() {
            match entry {
                ForwardedIntBoundTrailEntry::ScopeMarker => break,
                ForwardedIntBoundTrailEntry::Lit(literal, value) => {
                    self.forwarded_int_bound_literals.remove(&(literal, value));
                }
            }
        }
    }

    fn reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: LiraSolver::reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.lia.reset();
        self.lra.reset();
        self.propagated_cross_sort.clear();
        self.cross_sort_trail.clear();
        self.asserted_real_int_terms.clear();
        self.asserted_real_int_term_trail.clear();
        self.clear_int_bound_forwarding();
    }

    fn soft_reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: LiraSolver::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.lia.soft_reset();
        self.lra.soft_reset();
        self.propagated_cross_sort.clear();
        self.cross_sort_trail.clear();
        self.asserted_real_int_terms.clear();
        self.asserted_real_int_term_trail.clear();
        self.clear_int_bound_forwarding();
    }

    fn supports_theory_aware_branching(&self) -> bool {
        self.lra.supports_theory_aware_branching()
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
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
