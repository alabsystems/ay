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

        // A reason may be a negated INDEX equality rather than this numeric
        // equality. Splitting that reason would order unrelated terms (even
        // datatype constructors). Only the actual pair can guard its split;
        // when absent, the existing model-equality handoff creates that atom.
        let eq_term = self.terms().find_eq(lhs, rhs);
        if eq_term.is_none() && debug {
            safe_eprintln!(
                "[LRA N-O] Shared disequality has no equality atom for its actual operands ({} reason lits)",
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

    /// The reason literals of every cross-theory fact this solver currently
    /// holds as a bound or a row — EUF shared equalities and disequalities
    /// (`assert_shared_equality` / `assert_shared_disequality`, directly or
    /// forwarded by an enclosing LIA) and cross-sort bounds
    /// (`assert_tight_bound` / `assert_cross_sort_bounds`) — in the order they
    /// were received, deduplicated, with their current polarity
    /// (#nonlinear-shared-reasons).
    ///
    /// A procedure that refutes this solver's state AS A WHOLE and explains the
    /// refutation with its own asserted atoms must cite these as well: the
    /// state is the asserted atoms PLUS these facts, and a conflict that drops
    /// them is not a theorem (QF_UFNIA `euf_div_010`: the 17-atom set the NIA
    /// returned is satisfiable; the refutation leaned on the EUF equality
    /// `f(a) = f(b)` held as a row). Every literal returned is live: the set is
    /// scoped by `push`/`pop` exactly like the stale-reason guard that reads it.
    ///
    /// Nothing is filtered. A reason that is not a Boolean atom — the
    /// arithmetic `lhs` a reasonless shared equality is installed with, or a
    /// term that reached EUF as the reason of a tight-bound equality — is
    /// returned as recorded: a conflict that names it cannot be mapped to a
    /// clause, and the DPLL layer fails closed on it (`unknown`). Dropping it
    /// instead would publish a conflict that rests on a fact nobody can name.
    pub fn shared_constraint_reasons(&self) -> Vec<TheoryLit> {
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut out = Vec::new();
        for &(term, _) in &self.cross_theory_asserted_trail {
            if !seen.insert(term) {
                continue;
            }
            if let Some(&value) = self.cross_theory_asserted.get(&term) {
                out.push(TheoryLit::new(term, value));
            }
        }
        out
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
            // #lra-scope-trail: the conflict lives in the current scope.
            self.trivial_conflict_scope = self.scopes.len();
        }
    }
}
