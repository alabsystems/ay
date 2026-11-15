// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed arithmetic views that keep LIA's backing-store lifetime intact.

use crate::LiaSolver;
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::{TermId, TermStore};
use ay_core::{TheoryConflict, TheoryLit, TheoryResult, TheorySolver};
use ay_lra::rational::Rational;
use ay_lra::{Bound, GomoryCut, LraSolver};
use num_rational::BigRational;
use std::cmp::Ordering;
use std::marker::PhantomData;

/// Read-only LRA queries borrowed from a live LIA solver.
///
/// The view deliberately does not expose the raw solver or its unconstrained
/// term-store pointer API. References returned here retain the view's borrow.
#[derive(Clone, Copy)]
pub struct LraSolverView<'s> {
    pub(crate) inner: &'s LraSolver,
    pub(crate) terms_borrow: PhantomData<&'s TermStore>,
}

impl<'s> LraSolverView<'s> {
    pub fn terms(self) -> &'s TermStore {
        self.inner.terms()
    }

    pub fn get_value(self, term: TermId) -> Option<BigRational> {
        self.inner.get_value(term)
    }

    pub fn get_value_with_reasons(self, term: TermId) -> Option<(BigRational, Vec<TheoryLit>)> {
        self.inner.get_value_with_reasons(term)
    }

    pub fn get_bounds(self, term: TermId) -> Option<(Option<Bound>, Option<Bound>)> {
        self.inner.get_bounds(term)
    }

    pub fn get_bounds_ref(self, term: TermId) -> Option<(Option<&'s Bound>, Option<&'s Bound>)> {
        self.inner.get_bounds_ref(term)
    }

    pub fn has_value(self, term: TermId) -> bool {
        self.inner.has_value(term)
    }

    pub fn has_implied_bounds(self, term: TermId) -> bool {
        self.inner.has_implied_bounds(term)
    }

    pub fn value_sign(self, term: TermId) -> Option<Ordering> {
        self.inner.value_sign(term)
    }

    pub fn row_count(self) -> usize {
        self.inner.row_count()
    }

    pub fn phase_state_epoch(self) -> u64 {
        self.inner.phase_state_epoch()
    }

    pub fn collect_all_bound_conflicts(self, skip_first: bool) -> Vec<TheoryConflict> {
        self.inner.collect_all_bound_conflicts(skip_first)
    }

    pub fn term_to_var(self) -> &'s DetHashMap<TermId, u32> {
        self.inner.term_to_var()
    }
}

/// Mutable arithmetic operations borrowed from a LIA solver.
///
/// Rebinding retains the owning LIA lifetime. No raw mutable LRA reference,
/// replacement operation, or pointer-bearing owned solver can escape the view.
pub struct LraSolverMut<'s, 'a> {
    // Borrow the real owner: this keeps both its store-lifetime invariance
    // and the shared backing-store's auto-trait requirements.
    pub(crate) owner: &'s mut LiaSolver<'a>,
}

impl<'a> LraSolverMut<'_, 'a> {
    pub fn set_terms(&mut self, terms: &'a TermStore) {
        self.owner.lra.set_terms(terms);
    }

    pub fn unset_terms(&mut self) {
        self.owner.lra.unset_terms();
    }

    pub fn ensure_var_registered(&mut self, term: TermId) -> u32 {
        self.owner.lra.ensure_var_registered(term)
    }

    pub fn add_gomory_cut(&mut self, cut: &GomoryCut, reason: TermId) {
        self.owner.lra.add_gomory_cut(cut, reason);
    }

    pub fn add_cut_rat(
        &mut self,
        coeffs: Vec<(u32, Rational)>,
        bound: Rational,
        is_lower: bool,
        reasons: &[(TermId, bool)],
        reason: TermId,
    ) {
        self.owner
            .lra
            .add_cut_rat(coeffs, bound, is_lower, reasons, reason);
    }

    pub fn check(&mut self) -> TheoryResult {
        self.owner.lra.check()
    }

    pub fn assert_tight_bound(&mut self, term: TermId, value: &BigRational, reasons: &[TheoryLit]) {
        self.owner.lra.assert_tight_bound(term, value, reasons);
    }

    pub fn import_model_equality_proposal_state(
        &mut self,
        equality_pairs: DetHashSet<(TermId, TermId)>,
        disequality_pairs: DetHashSet<(TermId, TermId)>,
    ) {
        self.owner
            .lra
            .import_model_equality_proposal_state(equality_pairs, disequality_pairs);
    }

    pub fn set_no_theory_propagation(&mut self, disabled: bool) {
        self.owner.lra.set_no_theory_propagation(disabled);
    }

    pub fn set_no_bcp_implied_bounds(&mut self, disabled: bool) {
        self.owner.lra.set_no_bcp_implied_bounds(disabled);
    }
}
