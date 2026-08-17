// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-domain equality closure and stamped coverage caching.

use super::*;
use crate::executor::FiniteArrayCachedAxiom;
use ay_core::Sort;

type StampedTermKey = (TermId, ay_core::term::TermEntryStamp);

struct EqualityClosureState<'a> {
    pending: VecDeque<FiniteArrayCandidate>,
    processed_selects: &'a mut HashSet<StampedTermKey>,
    active_assertions: &'a mut HashSet<TermId>,
    report: &'a mut FiniteArrayExtensionalityReport,
    work_since_poll: usize,
}

impl Executor {
    pub(super) fn add_finite_index_array_extensionality_fixed_point(
        &mut self,
        eq_atoms: VecDeque<FiniteArrayCandidate>,
        processed_selects: &mut HashSet<StampedTermKey>,
        active_assertions: &mut HashSet<TermId>,
        report: &mut FiniteArrayExtensionalityReport,
    ) {
        let mut state = EqualityClosureState {
            pending: eq_atoms,
            processed_selects,
            active_assertions,
            report,
            work_since_poll: 0,
        };
        let mut processed = HashSet::default();
        while let Some(candidate) = state.pending.pop_front() {
            if !self.process_finite_array_equality(candidate, &mut processed, &mut state) {
                return;
            }
        }
    }

    fn process_finite_array_equality(
        &mut self,
        (eq_atom, lhs, rhs, domain): FiniteArrayCandidate,
        processed: &mut HashSet<StampedTermKey>,
        state: &mut EqualityClosureState<'_>,
    ) -> bool {
        let Some(candidate_stamp) = self.ctx.terms.entry_stamp(eq_atom) else {
            self.mark_finite_array_scan_truncated(state.report);
            return false;
        };
        if self.ctx.terms.entry_stamp(lhs).is_none() || self.ctx.terms.entry_stamp(rhs).is_none() {
            self.mark_finite_array_scan_truncated(state.report);
            return false;
        }
        let candidate_key = (eq_atom, candidate_stamp);
        if !processed.insert(candidate_key) {
            return true;
        }
        if !self.poll_finite_array_closure(&mut state.work_since_poll) {
            self.mark_finite_array_scan_truncated(state.report);
            return false;
        }

        let index_points = domain.cardinality();
        let value_cells =
            index_points.saturating_mul(self.finite_array_extensionality_value_width(lhs));
        if let Some(cached_axiom) = self.finite_array_equality_already_covered(
            eq_atom,
            candidate_stamp,
            state.active_assertions,
        ) {
            state.report.already_covered_equalities += 1;
            self.queue_nested_finite_array_candidates(cached_axiom, state);
            return true;
        }
        // Telemetry is query-unique. A deferred entry may be revisited by
        // another owning route, but it is neither a newly admitted candidate
        // nor a second unit of deferred work.
        if self
            .finite_array_expansion
            .deferred_equalities
            .contains(&candidate_key)
        {
            return true;
        }
        Self::record_finite_equality_candidate(state.report, index_points, value_cells);
        if self.defer_finite_array_equality(candidate_key, index_points, value_cells, state.report)
        {
            return true;
        }
        self.emit_finite_array_equality(
            eq_atom,
            lhs,
            rhs,
            domain,
            candidate_key,
            index_points,
            value_cells,
            state,
        )
    }

    fn record_finite_equality_candidate(
        report: &mut FiniteArrayExtensionalityReport,
        index_points: usize,
        value_cells: usize,
    ) {
        report.candidate_equalities += 1;
        report.candidate_index_points = report.candidate_index_points.saturating_add(index_points);
        report.candidate_value_cells = report.candidate_value_cells.saturating_add(value_cells);
    }

    fn defer_finite_array_equality(
        &mut self,
        candidate_key: StampedTermKey,
        index_points: usize,
        value_cells: usize,
        report: &mut FiniteArrayExtensionalityReport,
    ) -> bool {
        if self.reserve_finite_array_expansion(index_points, value_cells) {
            return false;
        }
        self.finite_array_expansion
            .deferred_equalities
            .insert(candidate_key);
        report.budget_deferred_equalities += 1;
        report.budget_deferred_index_points = report
            .budget_deferred_index_points
            .saturating_add(index_points);
        report.budget_deferred_value_cells = report
            .budget_deferred_value_cells
            .saturating_add(value_cells);
        true
    }

    fn emit_finite_array_equality(
        &mut self,
        eq_atom: TermId,
        lhs: TermId,
        rhs: TermId,
        domain: FiniteArrayIndexDomain,
        candidate_key: StampedTermKey,
        index_points: usize,
        value_cells: usize,
        state: &mut EqualityClosureState<'_>,
    ) -> bool {
        let mut conjuncts = Vec::with_capacity(index_points);
        for idx in self.finite_index_domain_values(&domain) {
            if !self.poll_finite_array_closure(&mut state.work_since_poll) {
                self.mark_finite_array_scan_truncated(state.report);
                return false;
            }
            let sel_lhs = self.ctx.terms.mk_select(lhs, idx);
            let sel_rhs = self.ctx.terms.mk_select(rhs, idx);
            let sel_eq = if matches!(self.ctx.terms.sort(sel_lhs), Sort::Array(_)) {
                self.ctx.terms.mk_eq_coerce_no_ite_expand(sel_lhs, sel_rhs)
            } else {
                self.ctx.terms.mk_eq(sel_lhs, sel_rhs)
            };
            self.queue_nested_finite_array_candidates(sel_eq, state);
            conjuncts.push(sel_eq);
        }
        self.install_finite_array_equality_axiom(
            eq_atom,
            candidate_key,
            conjuncts,
            index_points,
            value_cells,
            state,
        )
    }

    fn install_finite_array_equality_axiom(
        &mut self,
        eq_atom: TermId,
        candidate_key: StampedTermKey,
        conjuncts: Vec<TermId>,
        index_points: usize,
        value_cells: usize,
        state: &mut EqualityClosureState<'_>,
    ) -> bool {
        let conjunction = self.ctx.terms.mk_and(conjuncts);
        let biconditional = self.ctx.terms.mk_eq(eq_atom, conjunction);
        self.ensure_array_axiom_assertion_site_with_active_set(
            biconditional,
            "finite_index_array_ext",
            state.active_assertions,
        );
        let Some(axiom_stamp) = self.ctx.terms.entry_stamp(biconditional) else {
            self.mark_finite_array_scan_truncated(state.report);
            return false;
        };
        self.finite_array_expansion.equality_axioms.insert(
            eq_atom,
            FiniteArrayCachedAxiom {
                candidate_stamp: candidate_key.1,
                axiom: biconditional,
                axiom_stamp,
            },
        );
        self.finite_array_expansion
            .covered_equalities
            .insert(candidate_key);
        state.report.emitted_equalities += 1;
        state.report.emitted_index_points += index_points;
        state.report.emitted_value_cells += value_cells;
        true
    }

    fn queue_nested_finite_array_candidates(
        &mut self,
        root: TermId,
        state: &mut EqualityClosureState<'_>,
    ) {
        let mut nested = FiniteArrayCandidates::default();
        let discovery_cursor = self.finite_array_expansion.discovered_candidates.len();
        if self.collect_finite_array_candidates_bounded(&[root], &mut nested, discovery_cursor)
            == FiniteArrayScanStatus::Truncated
        {
            self.mark_finite_array_scan_truncated(state.report);
        }
        self.add_finite_index_select_expansion_bounded(
            nested.selects,
            &mut state.pending,
            state.processed_selects,
            state.active_assertions,
            state.report,
        );
        state.pending.extend(nested.equalities);
    }

    pub(super) fn poll_finite_array_closure(&mut self, work_since_poll: &mut usize) -> bool {
        *work_since_poll += 1;
        if *work_since_poll < FINITE_ARRAY_SCAN_RESOURCE_POLL_INTERVAL {
            return true;
        }
        *work_since_poll = 0;
        !self.should_abort_theory_loop()
    }

    pub(super) fn reserve_finite_array_expansion(
        &mut self,
        index_points: usize,
        value_cells: usize,
    ) -> bool {
        if index_points > self.finite_array_expansion.remaining_index_points
            || value_cells > self.finite_array_expansion.remaining_value_cells
        {
            return false;
        }
        self.finite_array_expansion.remaining_index_points -= index_points;
        self.finite_array_expansion.remaining_value_cells -= value_cells;
        true
    }

    fn finite_array_equality_already_covered(
        &mut self,
        equality: TermId,
        candidate_stamp: ay_core::term::TermEntryStamp,
        active_assertions: &mut HashSet<TermId>,
    ) -> Option<TermId> {
        let candidate_key = (equality, candidate_stamp);
        let cached = self
            .finite_array_expansion
            .equality_axioms
            .get(&equality)
            .copied()
            .filter(|cached| {
                cached.candidate_stamp == candidate_stamp
                    && self.ctx.terms.entry_stamp(cached.axiom) == Some(cached.axiom_stamp)
            });
        if let Some(cached) = cached {
            self.ensure_array_axiom_assertion_site_with_active_set(
                cached.axiom,
                "finite_index_array_ext_cached",
                active_assertions,
            );
            self.finite_array_expansion
                .covered_equalities
                .insert(candidate_key);
        } else {
            self.finite_array_expansion
                .equality_axioms
                .remove(&equality);
        }
        cached.map(|cached| cached.axiom)
    }

    /// Whether this exact equality instance is currently backed by an active,
    /// live finite-array axiom. Recursive enumerability alone is not enough:
    /// the exact closure may not have run on this route, or its cumulative
    /// query budget may have deferred this candidate. In either case generic
    /// extensionality must remain available as a conservative fallback.
    pub(in crate::executor) fn finite_array_equality_has_active_exact_coverage(
        &self,
        equality: TermId,
    ) -> bool {
        let Some(candidate_stamp) = self.ctx.terms.entry_stamp(equality) else {
            return false;
        };
        if !self
            .finite_array_expansion
            .covered_equalities
            .contains(&(equality, candidate_stamp))
        {
            return false;
        }
        let Some(cached) = self.finite_array_expansion.equality_axioms.get(&equality) else {
            return false;
        };
        cached.candidate_stamp == candidate_stamp
            && self.ctx.terms.entry_stamp(cached.axiom) == Some(cached.axiom_stamp)
            && self.ctx.assertions.contains(&cached.axiom)
    }

    pub(super) fn finite_array_select_already_covered(
        &mut self,
        select: TermId,
        candidate_stamp: ay_core::term::TermEntryStamp,
        active_assertions: &mut HashSet<TermId>,
    ) -> Option<TermId> {
        let candidate_key = (select, candidate_stamp);
        let cached = self
            .finite_array_expansion
            .select_axioms
            .get(&select)
            .copied()
            .filter(|cached| {
                cached.candidate_stamp == candidate_stamp
                    && self.ctx.terms.entry_stamp(cached.axiom) == Some(cached.axiom_stamp)
            });
        if let Some(cached) = cached {
            self.ensure_array_axiom_assertion_site_with_active_set(
                cached.axiom,
                "finite_index_select_expansion_cached",
                active_assertions,
            );
            self.finite_array_expansion
                .covered_selects
                .insert(candidate_key);
        } else {
            self.finite_array_expansion.select_axioms.remove(&select);
        }
        cached.map(|cached| cached.axiom)
    }

    pub(super) fn finite_array_extensionality_value_width(&self, array: TermId) -> usize {
        let Sort::Array(array_sort) = self.ctx.terms.sort(array) else {
            return 1;
        };
        match &array_sort.element_sort {
            Sort::BitVec(width) => width.width.max(1) as usize,
            Sort::FloatingPoint(exponent, significand) => {
                exponent.saturating_add(*significand).max(1) as usize
            }
            _ => 1,
        }
    }
}
