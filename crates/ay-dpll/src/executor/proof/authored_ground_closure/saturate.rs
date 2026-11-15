// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded saturation of the raw ground closure.
//!
//! Every edge producer here only PROPOSES a merge together with the reason
//! `emit.rs` will prove; none of them is an authority. The recognizer calls
//! below are the checker's own (`recognize_bv_bitblast`), and the emitted
//! candidate is re-validated end to end before anything is committed.

use ay_core::kani_compat::DetHashMap;

use super::*;

impl Executor {
    /// Register the authored equality and disequality roots, merge the
    /// equalities, and return the disequalities as closing targets. `None`
    /// once the node bound is exceeded.
    pub(super) fn seed_ground_closure(
        &mut self,
        closure: &mut GroundClosure,
        roots: &[TermId],
    ) -> Option<Vec<ClosureConflict>> {
        let mut equalities = Vec::new();
        let mut disequalities = Vec::new();
        for &root in roots {
            if let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, root) {
                equalities.push((root, lhs, rhs));
            } else if let TermData::Not(inner) = self.ctx.terms.get(root) {
                let inner = *inner;
                if let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, inner) {
                    disequalities.push(ClosureConflict::Disequality {
                        root,
                        equality: inner,
                        lhs,
                        rhs,
                    });
                }
            }
        }
        for &(_, lhs, rhs) in &equalities {
            self.register_ground_subterms(closure, lhs)?;
            self.register_ground_subterms(closure, rhs)?;
        }
        for conflict in &disequalities {
            if let ClosureConflict::Disequality { lhs, rhs, .. } = *conflict {
                self.register_ground_subterms(closure, lhs)?;
                self.register_ground_subterms(closure, rhs)?;
            }
        }
        for &(root, lhs, rhs) in &equalities {
            if self.ctx.terms.sort(lhs) == self.ctx.terms.sort(rhs) {
                closure.merge(lhs, rhs, EdgeReason::Authored(root));
            }
        }
        Some(disequalities)
    }

    /// One congruence plus read-over-write round. `None` once a bound is
    /// exceeded.
    pub(super) fn ground_closure_round(
        &mut self,
        closure: &mut GroundClosure,
        congruence_budget: &mut SharedGroundWork,
    ) -> Option<()> {
        self.close_ground_congruence(closure, congruence_budget)?;
        self.close_ground_read_over_write(closure)?;
        (closure.edges().len() <= MAX_EDGES).then_some(())
    }

    /// Register `term` and its application, `ite` and `not` subterms. Any
    /// other term shape is an opaque leaf. `None` once the node bound is
    /// exceeded.
    pub(super) fn register_ground_subterms(
        &self,
        closure: &mut GroundClosure,
        term: TermId,
    ) -> Option<()> {
        let mut pending = vec![term];
        while let Some(current) = pending.pop() {
            if !closure.register(current) {
                continue;
            }
            if closure.nodes().len() > MAX_NODES {
                return None;
            }
            match self.ctx.terms.get(current) {
                TermData::App(_, args) => pending.extend(args.iter().copied()),
                TermData::Ite(condition, then_term, else_term) => {
                    pending.extend([*condition, *then_term, *else_term]);
                }
                TermData::Not(inner) => pending.push(*inner),
                _ => {}
            }
        }
        Some(())
    }

    /// Whether `term` is an application of [`EVALUATED_OPERATORS`] over
    /// bit-vector constants only, within [`MAX_CLOSED_TERM_WORK`] nodes.
    pub(super) fn is_closed_evaluable_bv_application(&self, term: TermId) -> bool {
        let TermData::App(symbol, _) = self.ctx.terms.get(term) else {
            return false;
        };
        if !EVALUATED_OPERATORS.contains(&symbol.name()) {
            return false;
        }
        let mut pending = vec![term];
        let mut work = MAX_CLOSED_TERM_WORK;
        while let Some(current) = pending.pop() {
            let Some(remaining) = work.checked_sub(1) else {
                return false;
            };
            work = remaining;
            match self.ctx.terms.get(current) {
                TermData::Const(Constant::BitVec { .. }) => {}
                TermData::App(symbol, args) if EVALUATED_OPERATORS.contains(&symbol.name()) => {
                    pending.extend(args.iter().copied());
                }
                _ => return false,
            }
        }
        true
    }

    /// Select proposals using the existing model evaluator, with an EMPTY
    /// environment and a bounded scalar-width preflight. The hint is never
    /// proof authority: every selected equality still spends a recognizer
    /// probe and must pass strict derivation before installation. Unsupported
    /// hints preserve the existing proposal scan.
    fn ground_evaluation_value_hint(&self, term: TermId) -> Option<num_bigint::BigInt> {
        let mut pending = vec![term];
        let mut work = MAX_CLOSED_TERM_WORK;
        while let Some(current) = pending.pop() {
            work = work.checked_sub(1)?;
            let width = self.ctx.terms.sort(current).bitvec_width()?;
            if width == 0 || width > u64::BITS {
                return None;
            }
            match self.ctx.terms.get(current) {
                TermData::Const(Constant::BitVec {
                    value,
                    width: literal_width,
                }) => {
                    if *literal_width != width
                        || value.sign() == num_bigint::Sign::Minus
                        || value.bits() > u64::from(width)
                    {
                        return None;
                    }
                }
                TermData::App(symbol, args) => {
                    // The model evaluator assumes typed extract indices.
                    // Check them before its mask arithmetic or allocation,
                    // including malformed internal proposal terms.
                    if symbol.name() == "extract" {
                        let Symbol::Indexed(_, indices) = symbol else {
                            return None;
                        };
                        let &[high, low] = indices.as_slice() else {
                            return None;
                        };
                        let &[source] = args.as_slice() else {
                            return None;
                        };
                        let source_width = self.ctx.terms.sort(source).bitvec_width()?;
                        if high < low
                            || high >= source_width
                            || high.checked_sub(low)?.checked_add(1)? != width
                        {
                            return None;
                        }
                    }
                    pending.extend(args.iter().copied());
                }
                _ => return None,
            }
        }
        Self::evaluate_bv_expr(&self.ctx.terms, term, &DetHashMap::default())
    }

    /// Merge each closed evaluable bit-vector application with a registered
    /// constant the checker's recognizer proves it equal to.
    pub(super) fn add_ground_evaluation_edges(
        &mut self,
        closure: &mut GroundClosure,
        candidates: &[TermId],
        budget: &mut usize,
    ) {
        let nodes = closure.nodes().to_vec();
        let constants: Vec<TermId> = nodes
            .iter()
            .copied()
            .filter(|&node| Self::is_bitvec_constant(&self.ctx.terms, node))
            .collect();
        for &term in candidates {
            if *budget == 0 {
                return;
            }
            if !self.is_closed_evaluable_bv_application(term) {
                continue;
            }
            let hint = self.ground_evaluation_value_hint(term);
            for &constant in &constants {
                // Do not burn the finite semantic probes guessing unrelated
                // registered constants. A bad hint can only omit proposals;
                // it cannot merge anything without the unchanged recognizer.
                if hint.as_ref().is_some_and(|expected| {
                    !matches!(self.ctx.terms.get(constant),
                        TermData::Const(Constant::BitVec { value, .. }) if value == expected)
                }) {
                    continue;
                }
                if self.ctx.terms.sort(constant) != self.ctx.terms.sort(term)
                    || closure.same_class(term, constant)
                {
                    continue;
                }
                let Some(remaining) = budget.checked_sub(1) else {
                    return;
                };
                *budget = remaining;
                let equality =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("="), [term, constant], Sort::Bool);
                if self.recognize_bv_bitblast_until_stopped(&[equality]) {
                    closure.merge(term, constant, EdgeReason::Evaluated);
                    break;
                }
            }
        }
    }

    /// One read-over-write pass over every registered `select` of a `store`.
    /// A read of an array merged with a `store` is first restated over that
    /// store (a new node congruence joins to the read), so the axioms below
    /// see through authored array aliases. `None` once introducing a read
    /// would exceed the node bound.
    fn close_ground_read_over_write(&mut self, closure: &mut GroundClosure) -> Option<()> {
        for term in closure.nodes().to_vec() {
            let Some((array, read_index)) = select_parts_local(&self.ctx.terms, term) else {
                continue;
            };
            let Some((base, store_index, value)) = store_parts_local(&self.ctx.terms, array) else {
                self.restate_read_over_aliased_stores(closure, term, array, read_index)?;
                continue;
            };
            if closure.same_class(store_index, read_index) {
                closure.merge(term, value, EdgeReason::ReadHit);
                continue;
            }
            if self.class_constant(closure, store_index).is_none()
                || self.class_constant(closure, read_index).is_none()
            {
                continue;
            }
            let sort = self.ctx.terms.sort(term).clone();
            let base_read =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("select"), [base, read_index], sort);
            if closure.register(base_read) && closure.nodes().len() > MAX_NODES {
                return None;
            }
            closure.merge(term, base_read, EdgeReason::ReadMiss);
        }
        Some(())
    }

    /// Register `(select T index)` for every `store` term `T` merged with
    /// `array`; congruence then joins it to `read`.
    fn restate_read_over_aliased_stores(
        &mut self,
        closure: &mut GroundClosure,
        read: TermId,
        array: TermId,
        read_index: TermId,
    ) -> Option<()> {
        let stores: Vec<TermId> = closure
            .nodes()
            .iter()
            .copied()
            .filter(|&node| {
                node != array
                    && store_parts_local(&self.ctx.terms, node).is_some()
                    && closure.same_class(node, array)
            })
            .collect();
        for store in stores {
            let sort = self.ctx.terms.sort(read).clone();
            let restated =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("select"), [store, read_index], sort);
            if closure.register(restated) && closure.nodes().len() > MAX_NODES {
                return None;
            }
        }
        Some(())
    }

    /// A bit-vector constant in `term`'s class, if any.
    pub(super) fn class_constant(&self, closure: &GroundClosure, term: TermId) -> Option<TermId> {
        let class = closure.class(term)?;
        closure.nodes().iter().copied().find(|&node| {
            Self::is_bitvec_constant(&self.ctx.terms, node) && closure.class(node) == Some(class)
        })
    }

    /// The first conflict the closure currently exhibits.
    pub(super) fn ground_closure_conflict(
        &self,
        closure: &GroundClosure,
        disequalities: &[ClosureConflict],
    ) -> Option<ClosureConflict> {
        for conflict in disequalities {
            if let ClosureConflict::Disequality { lhs, rhs, .. } = *conflict {
                if closure.same_class(lhs, rhs) {
                    return Some(conflict.clone());
                }
            }
        }
        let mut seen: DetHashMap<usize, TermId> = DetHashMap::default();
        for &node in closure.nodes() {
            if !Self::is_bitvec_constant(&self.ctx.terms, node) {
                continue;
            }
            let class = closure.class(node)?;
            match seen.get(&class) {
                Some(&other) if other != node => {
                    return Some(ClosureConflict::ConstantClash(other, node));
                }
                Some(_) => {}
                None => {
                    seen.insert(class, node);
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod evaluation_hint_tests {
    use super::*;

    #[test]
    fn bounded_ground_evaluation_hint_rejects_malformed_extract_indices() {
        for indices in [vec![0, 7], vec![8, 0], vec![u32::MAX, 0], vec![7]] {
            let mut exec = Executor::new();
            let source = exec.ctx.terms.mk_bitvec(255.into(), 8);
            let term = exec.ctx.terms.mk_app(
                Symbol::indexed("extract", indices),
                [source],
                Sort::bitvec(8),
            );
            assert!(exec.ground_evaluation_value_hint(term).is_none());
        }
        let mut exec = Executor::new();
        let source = exec.ctx.terms.mk_bitvec(255.into(), 8);
        let term = exec.ctx.terms.mk_app(
            Symbol::indexed("extract", vec![7, 0]),
            [source],
            Sort::bitvec(8),
        );
        assert_eq!(exec.ground_evaluation_value_hint(term), Some(255.into()));
    }

    #[test]
    fn bounded_ground_evaluation_hint_rejects_noncanonical_literals_and_wide_sources() {
        for (value, literal_width) in [(256, 8), (-1, 8), (0, 16)] {
            let mut exec = Executor::new();
            let source = exec.ctx.terms.mk_bitvec(0.into(), 8);
            let term = exec
                .ctx
                .terms
                .mk_app(Symbol::named("bvneg"), [source], Sort::bitvec(8));
            let mut entries = exec.ctx.terms.entries_snapshot();
            entries[source.index()].0 = TermData::Const(Constant::BitVec {
                value: value.into(),
                width: literal_width,
            });
            exec.ctx.terms = TermStore::from_entries(entries, None, None, 0);
            assert!(exec.ground_evaluation_value_hint(term).is_none());
        }
        let mut exec = Executor::new();
        let source = exec.ctx.terms.mk_bitvec(64.into(), 128);
        let term = exec.ctx.terms.mk_app(
            Symbol::indexed("extract", vec![7, 0]),
            [source],
            Sort::bitvec(8),
        );
        assert!(
            exec.ground_evaluation_value_hint(term).is_none(),
            "wide source keeps the original scan"
        );
    }
}
