// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complete symbolic-select expansion over finite carriers.

use super::*;
use crate::executor::FiniteArrayCachedAxiom;
use num_bigint::BigInt;

struct SelectClosureState<'a> {
    pending_selects: VecDeque<FiniteArrayCandidate>,
    pending_equalities: &'a mut VecDeque<FiniteArrayCandidate>,
    processed: &'a mut HashSet<(TermId, ay_core::term::TermEntryStamp)>,
    active_assertions: &'a mut HashSet<TermId>,
    report: &'a mut FiniteArrayExtensionalityReport,
    work_since_poll: usize,
}

impl Executor {
    /// Expand every symbolic select over a complete finite carrier.
    pub(super) fn add_finite_index_select_expansion_bounded(
        &mut self,
        selects: Vec<FiniteArrayCandidate>,
        pending_equalities: &mut VecDeque<FiniteArrayCandidate>,
        processed: &mut HashSet<(TermId, ay_core::term::TermEntryStamp)>,
        active_assertions: &mut HashSet<TermId>,
        report: &mut FiniteArrayExtensionalityReport,
    ) {
        let mut state = SelectClosureState {
            pending_selects: selects.into(),
            pending_equalities,
            processed,
            active_assertions,
            report,
            work_since_poll: 0,
        };
        while let Some(candidate) = state.pending_selects.pop_front() {
            if !self.process_finite_array_select(candidate, &mut state) {
                return;
            }
        }
    }

    fn process_finite_array_select(
        &mut self,
        candidate: FiniteArrayCandidate,
        state: &mut SelectClosureState<'_>,
    ) -> bool {
        let (select, arr, idx) = (candidate.0, candidate.1, candidate.2);
        let Some(candidate_stamp) = self.ctx.terms.entry_stamp(select) else {
            self.mark_finite_array_scan_truncated(state.report);
            return false;
        };
        let candidate_key = (select, candidate_stamp);
        if !state.processed.insert(candidate_key) {
            return true;
        }
        if self.ctx.terms.entry_stamp(arr).is_none()
            || self.ctx.terms.entry_stamp(idx).is_none()
            || !self.poll_finite_array_closure(&mut state.work_since_poll)
        {
            self.mark_finite_array_scan_truncated(state.report);
            return false;
        }

        let index_points = candidate.3.cardinality();
        let value_cells =
            index_points.saturating_mul(self.finite_array_extensionality_value_width(arr));
        if self
            .finite_array_expansion
            .trivially_covered_selects
            .contains(&candidate_key)
        {
            state.report.already_covered_selects += 1;
            return true;
        }
        if let Some(cached_axiom) = self.finite_array_select_already_covered(
            select,
            candidate_stamp,
            state.active_assertions,
        ) {
            state.report.already_covered_selects += 1;
            self.queue_nested_select_candidates(select, cached_axiom, state);
            return true;
        }
        if self
            .finite_array_expansion
            .deferred_selects
            .contains(&candidate_key)
        {
            return true;
        }
        Self::record_finite_select_candidate(state.report, index_points, value_cells);
        if self.defer_finite_array_select(candidate_key, index_points, value_cells, state.report) {
            return true;
        }
        self.emit_finite_array_select(candidate, candidate_key, index_points, value_cells, state)
    }

    fn record_finite_select_candidate(
        report: &mut FiniteArrayExtensionalityReport,
        index_points: usize,
        value_cells: usize,
    ) {
        report.candidate_selects += 1;
        report.candidate_select_index_points = report
            .candidate_select_index_points
            .saturating_add(index_points);
        report.candidate_select_value_cells = report
            .candidate_select_value_cells
            .saturating_add(value_cells);
    }

    fn defer_finite_array_select(
        &mut self,
        candidate_key: (TermId, ay_core::term::TermEntryStamp),
        index_points: usize,
        value_cells: usize,
        report: &mut FiniteArrayExtensionalityReport,
    ) -> bool {
        if self.reserve_finite_array_expansion(index_points, value_cells) {
            return false;
        }
        self.finite_array_expansion
            .deferred_selects
            .insert(candidate_key);
        report.budget_deferred_selects += 1;
        report.budget_deferred_select_index_points = report
            .budget_deferred_select_index_points
            .saturating_add(index_points);
        report.budget_deferred_select_value_cells = report
            .budget_deferred_select_value_cells
            .saturating_add(value_cells);
        true
    }

    fn emit_finite_array_select(
        &mut self,
        (select, arr, idx, domain): FiniteArrayCandidate,
        candidate_key: (TermId, ay_core::term::TermEntryStamp),
        index_points: usize,
        value_cells: usize,
        state: &mut SelectClosureState<'_>,
    ) -> bool {
        let domain_vals = self.finite_index_domain_values(&domain);
        let Some((&last, rest)) = domain_vals.split_last() else {
            self.finite_array_expansion
                .trivially_covered_selects
                .insert(candidate_key);
            return true;
        };
        let mut acc = self.ctx.terms.mk_select(arr, last);
        for &point in rest.iter().rev() {
            let point_equality = self.ctx.terms.mk_eq(idx, point);
            let point_select = self.ctx.terms.mk_select(arr, point);
            acc = self.ctx.terms.mk_ite(point_equality, point_select, acc);
        }
        if select == acc {
            self.finite_array_expansion
                .trivially_covered_selects
                .insert(candidate_key);
            return true;
        }
        self.install_finite_array_select_axiom(
            select,
            acc,
            candidate_key,
            index_points,
            value_cells,
            state,
        )
    }

    fn install_finite_array_select_axiom(
        &mut self,
        select: TermId,
        expansion: TermId,
        candidate_key: (TermId, ay_core::term::TermEntryStamp),
        index_points: usize,
        value_cells: usize,
        state: &mut SelectClosureState<'_>,
    ) -> bool {
        let array_valued = matches!(self.ctx.terms.sort(select), Sort::Array(_));
        let axiom = if array_valued {
            self.ctx.terms.mk_eq_coerce_no_ite_expand(select, expansion)
        } else {
            self.ctx.terms.mk_eq(select, expansion)
        };
        self.ensure_array_axiom_assertion_site_with_active_set(
            axiom,
            "finite_index_select_expansion",
            state.active_assertions,
        );
        let Some(axiom_stamp) = self.ctx.terms.entry_stamp(axiom) else {
            self.mark_finite_array_scan_truncated(state.report);
            return false;
        };
        self.finite_array_expansion.select_axioms.insert(
            select,
            FiniteArrayCachedAxiom {
                candidate_stamp: candidate_key.1,
                axiom,
                axiom_stamp,
            },
        );
        self.finite_array_expansion
            .covered_selects
            .insert(candidate_key);
        state.report.emitted_selects += 1;
        state.report.emitted_select_index_points = state
            .report
            .emitted_select_index_points
            .saturating_add(index_points);
        state.report.emitted_select_value_cells = state
            .report
            .emitted_select_value_cells
            .saturating_add(value_cells);
        if array_valued {
            self.queue_nested_select_candidates(select, axiom, state);
        }
        true
    }

    fn queue_nested_select_candidates(
        &mut self,
        select: TermId,
        axiom: TermId,
        state: &mut SelectClosureState<'_>,
    ) {
        if !matches!(self.ctx.terms.sort(select), Sort::Array(_)) {
            return;
        }
        let mut nested = FiniteArrayCandidates::default();
        let discovery_cursor = self.finite_array_expansion.discovered_candidates.len();
        if self.collect_finite_array_candidates_bounded(&[axiom], &mut nested, discovery_cursor)
            == FiniteArrayScanStatus::Truncated
        {
            self.mark_finite_array_scan_truncated(state.report);
        }
        state.pending_selects.extend(nested.selects);
        state.pending_equalities.extend(nested.equalities);
    }

    /// Enumerate the index constants of a finite array index domain (shared by
    /// the extensionality and select-expansion passes).
    pub(super) fn finite_index_domain_values(
        &mut self,
        domain: &FiniteArrayIndexDomain,
    ) -> Vec<TermId> {
        match domain {
            FiniteArrayIndexDomain::BitVec(width) => (0..(1u64 << width))
                .map(|i| self.ctx.terms.mk_bitvec(BigInt::from(i), *width))
                .collect(),
            FiniteArrayIndexDomain::Bool => {
                vec![self.ctx.terms.mk_bool(false), self.ctx.terms.mk_bool(true)]
            }
            FiniteArrayIndexDomain::EnumDatatype(ctor_names, index_sort) => ctor_names
                .iter()
                .map(|name| self.ctx.terms.mk_var(name.clone(), index_sort.clone()))
                .collect(),
        }
    }
}
