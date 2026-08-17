// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded stamped discovery and recursive-array authorization.

use super::*;
use ay_core::{Sort, Symbol, TermData};

impl Executor {
    /// Return the exact ground children of a term only when every child handle
    /// is live and the structural signatures that matter to finite-array
    /// discovery are well formed. A term that merely *names* `=` or `select`
    /// is not trusted: it must be the non-indexed builtin shape with matching
    /// argument/result sorts. Quantifiers are deliberately opaque because
    /// hoisting their local subterms into ground axioms is not sound; quantified
    /// routes separately present instantiated ground obligations as roots. A
    /// non-empty surviving `let` has no such separate discharge path and is
    /// rejected fail-closed (the SMT-LIB elaborator normally removes it). Future
    /// term variants likewise fail closed until their exact child/scope semantics
    /// are known.
    fn finite_array_scan_children(&self, data: &TermData, term_sort: &Sort) -> Option<Vec<TermId>> {
        let children = match data {
            TermData::App(sym, args) => {
                if args
                    .iter()
                    .any(|&child| self.ctx.terms.entry_stamp(child).is_none())
                {
                    return None;
                }
                if sym.name() == "=" {
                    if !matches!(sym, Symbol::Named(name) if name == "=")
                        || args.len() != 2
                        || term_sort != &Sort::Bool
                        || self.ctx.terms.sort(args[0]) != self.ctx.terms.sort(args[1])
                    {
                        return None;
                    }
                } else if sym.name() == "select" {
                    if !matches!(sym, Symbol::Named(name) if name == "select") || args.len() != 2 {
                        return None;
                    }
                    let Sort::Array(array_sort) = self.ctx.terms.sort(args[0]) else {
                        return None;
                    };
                    if self.ctx.terms.sort(args[1]) != &array_sort.index_sort
                        || term_sort != &array_sort.element_sort
                    {
                        return None;
                    }
                }
                args.clone()
            }
            TermData::Not(inner) => {
                if self.ctx.terms.entry_stamp(*inner).is_none()
                    || term_sort != &Sort::Bool
                    || self.ctx.terms.sort(*inner) != &Sort::Bool
                {
                    return None;
                }
                vec![*inner]
            }
            TermData::Ite(condition, then_term, else_term) => {
                if self.ctx.terms.entry_stamp(*condition).is_none()
                    || self.ctx.terms.entry_stamp(*then_term).is_none()
                    || self.ctx.terms.entry_stamp(*else_term).is_none()
                    || self.ctx.terms.sort(*condition) != &Sort::Bool
                    || self.ctx.terms.sort(*then_term) != self.ctx.terms.sort(*else_term)
                    || term_sort != self.ctx.terms.sort(*then_term)
                {
                    return None;
                }
                vec![*condition, *then_term, *else_term]
            }
            TermData::Let(bindings, body) => {
                if !bindings.is_empty()
                    || self.ctx.terms.entry_stamp(*body).is_none()
                    || term_sort != self.ctx.terms.sort(*body)
                {
                    return None;
                }
                vec![*body]
            }
            TermData::Const(_)
            | TermData::Var(..)
            | TermData::Forall(..)
            | TermData::Exists(..) => Vec::new(),
            _ => return None,
        };
        Some(children)
    }

    /// Replay one authenticated candidate from the query-local discovery index.
    ///
    /// The index deliberately retains only `(TermId, birth stamp)`. Rebuilding
    /// the candidate here revalidates the exact builtin shape, operand liveness,
    /// and finite carrier before the entry gets any semantic authority. A stale
    /// or malformed entry therefore fails closed instead of indexing unchecked
    /// arguments or trusting a recycled term slot.
    fn replay_finite_array_candidate(
        &self,
        candidate_key: (TermId, ay_core::term::TermEntryStamp),
        out: &mut FiniteArrayCandidates,
    ) -> bool {
        let (term, stamp) = candidate_key;
        if self.ctx.terms.entry_stamp(term) != Some(stamp) {
            return false;
        }
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
            return false;
        };
        if name == "=" {
            if !self
                .finite_array_expansion
                .admitted_equalities
                .contains(&candidate_key)
                || args.len() != 2
                || self.ctx.terms.sort(term) != &Sort::Bool
                || self.ctx.terms.entry_stamp(args[0]).is_none()
                || self.ctx.terms.entry_stamp(args[1]).is_none()
                || self.ctx.terms.sort(args[0]) != self.ctx.terms.sort(args[1])
                || args[0] == args[1]
            {
                return false;
            }
            let Sort::Array(array_sort) = self.ctx.terms.sort(args[0]) else {
                return false;
            };
            let Some(domain) = self.finite_array_index_domain_for_sort(&array_sort.index_sort)
            else {
                return false;
            };
            out.equalities.push((term, args[0], args[1], domain));
            return true;
        }
        if name == "select" {
            if !self
                .finite_array_expansion
                .admitted_selects
                .contains(&candidate_key)
                || args.len() != 2
                || self.ctx.terms.entry_stamp(args[0]).is_none()
                || self.ctx.terms.entry_stamp(args[1]).is_none()
            {
                return false;
            }
            let Sort::Array(array_sort) = self.ctx.terms.sort(args[0]) else {
                return false;
            };
            if self.ctx.terms.sort(args[1]) != &array_sort.index_sort
                || self.ctx.terms.sort(term) != &array_sort.element_sort
                || matches!(self.ctx.terms.get(args[1]), TermData::Const(_))
            {
                return false;
            }
            let Some(
                domain @ (FiniteArrayIndexDomain::Bool | FiniteArrayIndexDomain::EnumDatatype(..)),
            ) = self.finite_index_domain_of(args[1])
            else {
                return false;
            };
            out.selects.push((term, args[0], args[1], domain));
            return true;
        }
        false
    }

    /// Discover equality and symbolic-select candidates in one bounded,
    /// query-cumulative iterative walk.
    pub(super) fn collect_finite_array_candidates_bounded(
        &mut self,
        roots: &[TermId],
        out: &mut FiniteArrayCandidates,
        replay_from: usize,
    ) -> FiniteArrayScanStatus {
        if self.finite_array_expansion.candidate_scan_truncated
            || !self.replay_finite_array_candidate_suffix(replay_from, out)
        {
            return FiniteArrayScanStatus::Truncated;
        }

        let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
        let mut work_since_poll = 0usize;
        while let Some(term) = stack.pop() {
            if !self.scan_finite_array_term(term, &mut stack, out, &mut work_since_poll) {
                return FiniteArrayScanStatus::Truncated;
            }
        }
        if self.should_abort_theory_loop() {
            FiniteArrayScanStatus::Truncated
        } else {
            FiniteArrayScanStatus::Complete
        }
    }

    fn replay_finite_array_candidate_suffix(
        &self,
        replay_from: usize,
        out: &mut FiniteArrayCandidates,
    ) -> bool {
        let Some(candidates) = self
            .finite_array_expansion
            .discovered_candidates
            .get(replay_from..)
        else {
            return false;
        };
        candidates
            .iter()
            .copied()
            .all(|candidate| self.replay_finite_array_candidate(candidate, out))
    }

    fn scan_finite_array_term(
        &mut self,
        term: TermId,
        stack: &mut Vec<TermId>,
        out: &mut FiniteArrayCandidates,
        work_since_poll: &mut usize,
    ) -> bool {
        let Some(stamp) = self.ctx.terms.entry_stamp(term) else {
            return false;
        };
        let scan_key = (term, stamp);
        if self
            .finite_array_expansion
            .scanned_nodes
            .contains(&scan_key)
        {
            return true;
        }
        if !self.poll_finite_array_closure(work_since_poll) {
            return false;
        }

        let data = self.ctx.terms.get(term).clone();
        let term_sort = self.ctx.terms.sort(term).clone();
        #[cfg(test)]
        {
            self.finite_array_expansion.discovery_term_inspections = self
                .finite_array_expansion
                .discovery_term_inspections
                .saturating_add(1);
        }
        let Some(children) = self.finite_array_scan_children(&data, &term_sort) else {
            return false;
        };
        if self.finite_array_expansion.remaining_scan_nodes == 0
            || children.len() > self.finite_array_expansion.remaining_scan_edges
        {
            return false;
        }
        self.finite_array_expansion.remaining_scan_nodes -= 1;
        self.finite_array_expansion.remaining_scan_edges -= children.len();
        self.finite_array_expansion.scanned_nodes.insert(scan_key);
        if !self.discover_finite_array_candidates_in_term(term, &data, out) {
            return false;
        }
        stack.extend(children.into_iter().rev());
        true
    }

    fn discover_finite_array_candidates_in_term(
        &mut self,
        term: TermId,
        data: &TermData,
        out: &mut FiniteArrayCandidates,
    ) -> bool {
        let TermData::App(Symbol::Named(name), args) = data else {
            return true;
        };
        if name == "=" {
            return self.discover_finite_array_equality(term, args, out);
        }
        if name == "select" {
            return self.discover_finite_array_select(term, args, out);
        }
        true
    }

    fn discover_finite_array_equality(
        &mut self,
        term: TermId,
        args: &[TermId],
        out: &mut FiniteArrayCandidates,
    ) -> bool {
        let (lhs, rhs) = (args[0], args[1]);
        if lhs == rhs {
            return true;
        }
        let Sort::Array(array_sort) = self.ctx.terms.sort(lhs) else {
            return true;
        };
        let Some(domain) = self.finite_array_index_domain_for_sort(&array_sort.index_sort) else {
            return true;
        };
        if !self.admit_finite_array_candidate(FiniteArrayCandidateKind::Equality, term) {
            return false;
        }
        out.equalities.push((term, lhs, rhs, domain));
        true
    }

    fn discover_finite_array_select(
        &mut self,
        term: TermId,
        args: &[TermId],
        out: &mut FiniteArrayCandidates,
    ) -> bool {
        let (array, index) = (args[0], args[1]);
        if matches!(self.ctx.terms.get(index), TermData::Const(_)) {
            return true;
        }
        let domain = match self.finite_index_domain_of(index) {
            Some(domain @ FiniteArrayIndexDomain::Bool)
            | Some(domain @ FiniteArrayIndexDomain::EnumDatatype(..)) => domain,
            _ => return true,
        };
        if !self.admit_finite_array_candidate(FiniteArrayCandidateKind::Select, term) {
            return false;
        }
        out.selects.push((term, array, index, domain));
        true
    }

    fn admit_finite_array_candidate(
        &mut self,
        kind: FiniteArrayCandidateKind,
        term: TermId,
    ) -> bool {
        let Some(stamp) = self.ctx.terms.entry_stamp(term) else {
            return false;
        };
        let key = (term, stamp);
        let already_admitted = match kind {
            FiniteArrayCandidateKind::Equality => self
                .finite_array_expansion
                .admitted_equalities
                .contains(&key),
            FiniteArrayCandidateKind::Select => {
                self.finite_array_expansion.admitted_selects.contains(&key)
            }
        };
        if already_admitted {
            return true;
        }
        if self.finite_array_expansion.remaining_candidates == 0
            || self.finite_array_expansion.discovered_candidates.len()
                >= crate::executor::FiniteArrayExpansionLedger::MAX_CANDIDATES
        {
            return false;
        }
        self.finite_array_expansion.remaining_candidates -= 1;
        match kind {
            FiniteArrayCandidateKind::Equality => {
                self.finite_array_expansion.admitted_equalities.insert(key);
            }
            FiniteArrayCandidateKind::Select => {
                self.finite_array_expansion.admitted_selects.insert(key);
            }
        }
        // The same candidate charge covers this compact replay entry. The
        // explicit length guard above keeps Vec growth within MAX_CANDIDATES.
        self.finite_array_expansion.discovered_candidates.push(key);
        true
    }

    /// The finite index domain of a term `idx` based on its SORT (Bool, small
    /// BitVec, or enum datatype), or `None` for infinite/large domains.
    pub(super) fn finite_index_domain_of(&self, idx: TermId) -> Option<FiniteArrayIndexDomain> {
        self.finite_array_index_domain_for_sort(self.ctx.terms.sort(idx))
    }

    fn finite_array_index_domain_for_sort(&self, sort: &Sort) -> Option<FiniteArrayIndexDomain> {
        match sort {
            Sort::Bool => Some(FiniteArrayIndexDomain::Bool),
            Sort::BitVec(bv)
                if bv.width >= 1 && bv.width <= Self::FINITE_BV_ARRAY_EXT_MAX_INDEX_WIDTH =>
            {
                Some(FiniteArrayIndexDomain::BitVec(bv.width))
            }
            other => self.finite_enum_datatype_ctors(other).map(|constructors| {
                FiniteArrayIndexDomain::EnumDatatype(constructors, other.clone())
            }),
        }
    }

    /// True only when `sort` is an array and every nested array layer has an
    /// index carrier handled exactly by the finite-array closure.
    #[cfg(test)]
    fn finite_array_sort_is_recursively_enumerable(&self, sort: &Sort) -> bool {
        let mut current = sort;
        let mut saw_array = false;
        while let Sort::Array(layer) = current {
            saw_array = true;
            if self
                .finite_array_index_domain_for_sort(&layer.index_sort)
                .is_none()
            {
                return false;
            }
            current = &layer.element_sort;
        }
        saw_array
    }

    /// Whether every array sort reachable from `roots` has a carrier that the
    /// exact finite-array closure can enumerate, recursively through nested
    /// array elements. Scalar leaves may be arbitrary; an array is accepted
    /// only when every array layer has Bool, BV1..8, or an authenticated small
    /// enum index. The walk is iterative and binder-opaque. Its counters are
    /// wholly local: authorization must not spend or poison the production
    /// closure ledger before the authorized route gets to use it.
    #[cfg(test)]
    pub(in crate::executor) fn roots_have_only_recursively_finite_arrays(
        &self,
        roots: &[TermId],
    ) -> bool {
        let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
        let mut seen: HashSet<(TermId, ay_core::term::TermEntryStamp)> = HashSet::default();
        let mut saw_array = false;
        let mut work_since_poll = 0usize;
        let mut remaining_nodes = crate::executor::FiniteArrayExpansionLedger::MAX_SCAN_NODES;
        let mut remaining_edges = crate::executor::FiniteArrayExpansionLedger::MAX_SCAN_EDGES;
        let should_stop = self.make_should_stop();

        while let Some(term) = stack.pop() {
            let Some(stamp) = self.ctx.terms.entry_stamp(term) else {
                return false;
            };
            if !seen.insert((term, stamp)) {
                continue;
            }
            if remaining_nodes == 0 {
                return false;
            }
            remaining_nodes -= 1;
            work_since_poll += 1;
            if work_since_poll >= FINITE_ARRAY_SCAN_RESOURCE_POLL_INTERVAL {
                work_since_poll = 0;
                if should_stop()
                    || crate::memory::memory_exceeded(self.memory_limit())
                    || ay_sys::process_memory_exceeded()
                {
                    return false;
                }
            }

            let data = self.ctx.terms.get(term).clone();
            if matches!(
                &data,
                TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..)
            ) {
                // Unlike ground candidate discovery, authorization must prove
                // the property for every relevant reachable sort. It cannot
                // certify an opaque binder whose locally scoped body was not
                // inspected.
                return false;
            }
            let term_sort = self.ctx.terms.sort(term);
            if matches!(term_sort, Sort::Array(_)) {
                saw_array = true;
                if !self.finite_array_sort_is_recursively_enumerable(term_sort) {
                    return false;
                }
            }

            let Some(children) = self.finite_array_scan_children(&data, term_sort) else {
                return false;
            };
            if children.len() > remaining_edges {
                return false;
            }
            remaining_edges -= children.len();
            for child in children.into_iter().rev() {
                stack.push(child);
            }
        }

        saw_array
            && !should_stop()
            && !crate::memory::memory_exceeded(self.memory_limit())
            && !ay_sys::process_memory_exceeded()
    }
}
