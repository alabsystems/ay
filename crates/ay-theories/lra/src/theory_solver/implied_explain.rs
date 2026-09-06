// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact explanations for lazy `ImpliedBound` propagations.
//!
//! The producer (`compute_bound_propagations_for_vars`) decides an atom on
//! variable `var` — an original variable for single-variable atoms, the
//! compound slack for multi-variable atoms (`atom_index[slack]`) — from the
//! row-derived implied bound in `implied_bounds[var]`, which may itself rest
//! on implied bounds through equality chains `x_i = x_j`. The consumer here
//! must hand the SAT core a set of ASSERTED bound literals that entails the
//! propagated literal. Every strategy below returns such a set or `None`:
//!
//! 0. `var`'s own direct bound decides the atom: cite its reason atoms.
//! 1. The current row-derived slot bound decides the atom, and its
//!    derivation chain is grounded — each antecedent's current bound is at
//!    least as tight as the one consumed (`collect_reasons_from_explanation`).
//! 2. Re-derive the bound from the CURRENT row with direct bounds only and
//!    check the value obtained decides the atom.
//! 3. The direct-only interval of the atom's own expression decides the
//!    literal (#8754), citing the direct bounds of its variables.
//!
//! Strategies 1–3 each verify entailment against the current state; the
//! `filter_unsound_propagations` gate is therefore "an exact explanation
//! exists now", replacing the former direct-bounds-only re-derivation that
//! rejected every compound-atom propagation whose entailment needs an implied
//! bound (100% of `ImpliedBound` propagations on sc-*, measured).

use super::*;

/// Which strategy produced an implied-bound explanation (telemetry).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ImpliedReasonBasis {
    /// Strategy 0: the variable's own direct bound.
    DirectBound,
    /// Strategy 1: the value-checked derivation chain.
    Chain,
    /// Strategy 2: direct-only re-derivation from the current row.
    SingleRow,
    /// Strategy 3: direct-only interval of the atom expression.
    Interval,
}

impl LraSolver {
    /// Whether a bound `(value, strict)` on side `is_upper` of the atom's
    /// variable decides the atom literal `(atom, polarity)`.
    ///
    /// Mirrors the producer's comparison exactly: an upper atom `x <= k`
    /// (`x < k` when strict) is proved by an upper bound and refuted by a
    /// lower bound; a lower atom the reverse.
    pub(crate) fn bound_decides_atom(
        value: &Rational,
        strict: bool,
        is_upper: bool,
        atom: &AtomRef,
        polarity: bool,
    ) -> bool {
        use std::cmp::Ordering::{Equal, Greater, Less};
        if is_upper != (atom.is_upper == polarity) {
            return false;
        }
        let cmp = value.cmp(&atom.bound_value);
        match (atom.is_upper, polarity) {
            // ub <= k proves x <= k; ub < k or (ub == k, ub strict) proves x < k.
            (true, true) => cmp == Less || (cmp == Equal && (!atom.strict || strict)),
            // lb > k (or lb == k strict) refutes x <= k; lb >= k refutes x < k.
            (true, false) => cmp == Greater || (cmp == Equal && (atom.strict || strict)),
            // lb >= k proves x >= k; lb > k or (lb == k strict) proves x > k.
            (false, true) => cmp == Greater || (cmp == Equal && (!atom.strict || strict)),
            // ub < k (or ub == k strict) refutes x >= k; ub <= k refutes x > k.
            (false, false) => cmp == Less || (cmp == Equal && (atom.strict || strict)),
        }
    }

    /// Non-sentinel reason literals of a direct bound, provided every one of
    /// them is currently asserted; `None` otherwise or when empty.
    fn asserted_direct_reasons(&self, bound: &Bound) -> Option<Vec<TheoryLit>> {
        let mut reasons = Vec::new();
        for (term, val) in bound.reason_pairs() {
            if term.is_sentinel() {
                continue;
            }
            if self.asserted.get(&term) != Some(&val) {
                return None;
            }
            reasons.push(TheoryLit::new(term, val));
        }
        if reasons.is_empty() {
            return None;
        }
        Some(reasons)
    }

    /// Exact reason for the lazy `ImpliedBound` propagation of
    /// `(atom_term, polarity)` keyed on `var`/`need_upper`.
    ///
    /// Returns asserted literals that entail the propagated literal under
    /// the CURRENT bounds, tagged with the strategy that produced them, or
    /// `None` when no exact explanation exists now (the caller drops the
    /// propagation at the gate, or the SAT core treats the literal as a
    /// decision at conflict analysis — both sound).
    pub(crate) fn explain_implied_bound_propagation(
        &self,
        atom_term: TermId,
        var: u32,
        need_upper: bool,
        polarity: bool,
    ) -> Option<(Vec<TheoryLit>, ImpliedReasonBasis)> {
        let vi = var as usize;
        let atom = self
            .atom_index
            .get(&var)
            .and_then(|atoms| atoms.iter().find(|a| a.term == atom_term));
        if let Some(atom) = atom {
            // Strategy 0: the variable's own direct bound decides the atom.
            if let Some(info) = self.vars.get(vi) {
                let direct = if need_upper {
                    info.upper.as_ref()
                } else {
                    info.lower.as_ref()
                };
                if let Some(b) = direct {
                    if Self::bound_decides_atom(&b.value, b.strict, need_upper, atom, polarity) {
                        if let Some(reasons) = self.asserted_direct_reasons(b) {
                            return Some((reasons, ImpliedReasonBasis::DirectBound));
                        }
                    }
                }
            }
            let slot = self.implied_bounds.get(vi).and_then(|p| {
                if need_upper {
                    p.1.as_ref()
                } else {
                    p.0.as_ref()
                }
            });
            if let Some(ib) = slot.filter(|ib| ib.row_idx != usize::MAX) {
                // Strategy 1: the current row-derived bound decides the atom
                // and its derivation chain is grounded (value-checked, all
                // asserted, acyclic).
                if Self::bound_decides_atom(&ib.value, ib.strict, need_upper, atom, polarity) {
                    if let Some(reasons) =
                        self.make_eager_implied_propagation_reasons(vi, need_upper)
                    {
                        if !reasons.is_empty() {
                            return Some((reasons, ImpliedReasonBasis::Chain));
                        }
                    }
                }
                // Strategy 2: re-derive from the current row with direct
                // bounds only; the derived value must decide the atom.
                if self.max_row_width <= 50 {
                    if let Some((reasons, value, strict)) =
                        self.derive_bound_from_row_direct_only(var, need_upper, ib.row_idx)
                    {
                        if !reasons.is_empty()
                            && Self::bound_decides_atom(&value, strict, need_upper, atom, polarity)
                        {
                            return Some((reasons, ImpliedReasonBasis::SingleRow));
                        }
                    }
                }
            }
        }
        // Strategy 3: the direct-only interval of the atom's own expression.
        self.explain_by_direct_interval(atom_term, polarity)
            .map(|reasons| (reasons, ImpliedReasonBasis::Interval))
    }

    /// Strategy 3: the direct-only interval of the atom's own expression
    /// decides the literal (#8754); reasons are the direct bounds of its
    /// variables (`collect_interval_reasons` is direct-only and complete or
    /// empty), all of which must be asserted.
    fn explain_by_direct_interval(
        &self,
        atom_term: TermId,
        polarity: bool,
    ) -> Option<Vec<TheoryLit>> {
        let Some(Some(info)) = self.atom_cache.get(&atom_term) else {
            return None;
        };
        let is_le = info.is_le;
        let strict = info.strict;
        let (lb, ub) = self.compute_expr_interval_direct_only(&info.expr);
        let implied_true = if polarity {
            if is_le {
                ub.as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_le_zero(ep, strict))
            } else {
                lb.as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_ge_zero(ep, strict))
            }
        } else if is_le {
            lb.as_ref()
                .is_some_and(|ep| Self::endpoint_implies_not_le_zero(ep, strict))
        } else {
            ub.as_ref()
                .is_some_and(|ep| Self::endpoint_implies_not_ge_zero(ep, strict))
        };
        if !implied_true {
            return None;
        }
        let for_upper = if polarity { is_le } else { !is_le };
        let reasons = self.collect_interval_reasons(&info.expr, for_upper);
        if reasons.is_empty()
            || !reasons
                .iter()
                .all(|r| self.asserted.get(&r.term) == Some(&r.value))
        {
            return None;
        }
        Some(reasons)
    }

    /// Telemetry: count which strategy explained a delivered propagation.
    pub(crate) fn note_implied_reason_basis(&mut self, basis: ImpliedReasonBasis) {
        match basis {
            ImpliedReasonBasis::DirectBound => self.stats.implied_reason_direct_count += 1,
            ImpliedReasonBasis::Chain => self.stats.implied_reason_chain_count += 1,
            ImpliedReasonBasis::SingleRow => self.stats.implied_reason_row_count += 1,
            ImpliedReasonBasis::Interval => self.stats.implied_reason_interval_count += 1,
        }
    }
}
