// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    pub(super) fn assert_shared_equality_impl(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        reason: &[TheoryLit],
    ) {
        let debug = self.debug_lra_nelson_oppen;
        if debug {
            safe_eprintln!(
                "[LRA N-O] Receiving shared equality: term {} = term {} (reason: {} lits)",
                lhs.0,
                rhs.0,
                reason.len()
            );
        }
        if self.reject_shared_equality(lhs, rhs, debug) {
            return;
        }

        let diff_expr = self.shared_linear_difference(lhs, rhs);
        if diff_expr.is_constant() {
            self.handle_constant_shared_equality(&diff_expr, lhs, reason, debug);
            return;
        }
        self.assert_shared_linear_equality(diff_expr, lhs, reason);
    }

    // LRA only owns Int/Real terms. Forwarding a Bool equality aliases fresh
    // arithmetic variables to boolean atoms and corrupts the tableau (#8786).
    // ITE values are branch-dependent SAT choices, not stable shared terms;
    // imposing each observed branch value unconditionally is unsound (P1b).
    fn reject_shared_equality(&self, lhs: TermId, rhs: TermId, debug: bool) -> bool {
        let lhs_sort = self.terms().sort(lhs);
        let rhs_sort = self.terms().sort(rhs);
        if *lhs_sort == Sort::Bool || *rhs_sort == Sort::Bool {
            if debug {
                safe_eprintln!(
                    "[LRA N-O]   Rejecting Bool-sorted shared equality (#8786 soundness guard): \
                     lhs sort {:?}, rhs sort {:?}",
                    lhs_sort,
                    rhs_sort,
                );
            }
            return true;
        }

        if matches!(self.terms().get(lhs), TermData::Ite(..))
            || matches!(self.terms().get(rhs), TermData::Ite(..))
        {
            if debug {
                safe_eprintln!(
                    "[LRA N-O]   Rejecting ITE-term shared equality (P1b soundness guard): \
                     lhs {:?}, rhs {:?}",
                    self.terms().get(lhs),
                    self.terms().get(rhs),
                );
            }
            return true;
        }
        false
    }

    fn shared_linear_difference(&mut self, lhs: TermId, rhs: TermId) -> LinearExpr {
        // Shared terms are handled by the other theory's semantics, so parsing
        // here must not mark the current atom as unsupported (#6167, #5511).
        debug_assert!(self.current_parsing_atom.is_none());
        let lhs_expr = self.parse_linear_expr(lhs);
        let rhs_expr = self.parse_linear_expr(rhs);

        let mut diff_expr = lhs_expr;
        for &(var, ref coeff) in &rhs_expr.coeffs {
            diff_expr.add_term_rat(var, -coeff.clone());
        }
        diff_expr.constant = &diff_expr.constant - &rhs_expr.constant;
        diff_expr
    }

    fn handle_constant_shared_equality(
        &mut self,
        diff_expr: &LinearExpr,
        lhs: TermId,
        reason: &[TheoryLit],
        debug: bool,
    ) {
        if diff_expr.constant.is_zero() {
            if debug {
                safe_eprintln!("[LRA N-O]   Equality is trivially true (constant 0)");
            }
            return;
        }

        if debug {
            safe_eprintln!(
                "[LRA N-O]   Equality is impossible! Constant {} != 0 — recording conflict",
                diff_expr.constant
            );
        }
        self.record_shared_trivial_conflict(lhs, reason);
        self.dirty = true;
    }

    fn assert_shared_linear_equality(
        &mut self,
        diff_expr: LinearExpr,
        lhs: TermId,
        reason: &[TheoryLit],
    ) {
        // Both bounds must retain every reason literal so conflict clauses are
        // complete when an EUF equality has a multi-literal explanation.
        let reasons: Vec<(TermId, bool)> = if reason.is_empty() {
            vec![(lhs, true)]
        } else {
            reason.iter().map(|lit| (lit.term, lit.value)).collect()
        };
        self.record_cross_theory_reasons(&reasons);

        // Rational::zero() keeps the common value allocation-free (#8406).
        let zero = Rational::zero();
        self.assert_bound_with_reasons(
            diff_expr.clone(),
            zero.clone(),
            BoundType::Upper,
            false,
            &reasons,
            None,
        );
        self.assert_bound_with_reasons(diff_expr, zero, BoundType::Lower, false, &reasons, None);
        self.dirty = true;
    }

    pub(super) fn assert_shared_disequality_impl(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        reason: &[TheoryLit],
    ) {
        let debug = self.debug_lra_nelson_oppen;
        if debug {
            safe_eprintln!(
                "[LRA N-O] Receiving shared disequality: term {} != term {} (reason: {} lits)",
                lhs.0,
                rhs.0,
                reason.len()
            );
        }

        let diff_expr = self.shared_linear_difference(lhs, rhs);
        if diff_expr.is_constant() {
            self.handle_constant_shared_disequality(&diff_expr, lhs, reason, debug);
            return;
        }

        let eq_term = self.shared_disequality_equality_term(lhs, rhs, reason);
        if eq_term.is_none() && debug {
            safe_eprintln!(
                "[LRA N-O] WARNING: shared disequality has no negated equality in reason ({} lits, all true)",
                reason.len()
            );
        }

        self.shared_disequality_trail
            .push((lhs, rhs, diff_expr, reason.to_vec(), eq_term));
        self.record_cross_theory_reasons_from_lits(reason);
        self.dirty = true;
    }

    fn handle_constant_shared_disequality(
        &mut self,
        diff_expr: &LinearExpr,
        lhs: TermId,
        reason: &[TheoryLit],
        debug: bool,
    ) {
        // A non-zero constant satisfies the disequality and needs no state.
        if !diff_expr.constant.is_zero() {
            return;
        }
        if debug {
            safe_eprintln!(
                "[LRA N-O]   Shared disequality is trivially violated (constant 0 != 0) — recording conflict"
            );
        }
        self.record_shared_trivial_conflict(lhs, reason);
        self.dirty = true;
    }

    // Prefer the explicit negated equality that conditions the split clause.
    // Tight-bound propagation can legitimately provide positive reasons only;
    // in that case find_eq is the existing sound fallback (#6131, #8516).
    fn shared_disequality_equality_term(
        &self,
        lhs: TermId,
        rhs: TermId,
        reason: &[TheoryLit],
    ) -> Option<TermId> {
        reason
            .iter()
            .find(|lit| !lit.value)
            .map(|lit| lit.term)
            .or_else(|| self.terms().find_eq(lhs, rhs))
    }

    // Keep the first conflict, but retain the complete explanation. The lhs
    // literal is the historical fallback for reasonless shared constraints.
    fn record_shared_trivial_conflict(&mut self, lhs: TermId, reason: &[TheoryLit]) {
        if self.trivial_conflict.is_none() {
            let conflict_lits = if reason.is_empty() {
                vec![TheoryLit::new(lhs, true)]
            } else {
                reason.to_vec()
            };
            self.trivial_conflict = Some(conflict_lits);
        }
    }
}
