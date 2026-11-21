// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression analysis and linear equality assertion.
//!
//! Contains `is_expression_forced_to_value` (check if tableau constraints
//! pin a linear expression to a specific value) and `assert_linear_equality*`
//! (receive equalities from Nelson-Oppen combination).
//!
//! Split from `optimization.rs` for code health (#5970).

// #8529: Use deterministic hash maps in all builds.
use crate::linear_expr::{
    coeffs_are_normalized, proportional_coeff_slice_ratio, same_coeff_slices,
};
use crate::{BoundType, LinearExpr, LraSolver, Rational};
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermId;
use ay_core::DebugChannel;
use ay_core::TheoryLit;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

mod difference_reasons;

// Cached `--debug lra-forced` channel (checked once per process). #8858
cached_debug_channel!(debug_lra_forced, DebugChannel::LraForced);

impl LraSolver {
    /// Check if a linear expression is forced to a specific value by equality constraints.
    ///
    /// When an equality like `A = B` is asserted, we add bounds `A - B <= 0` and `A - B >= 0`,
    /// which forces the expression `A - B` to be exactly 0. This creates slack variables
    /// in the tableau with tight bounds.
    ///
    /// Returns `Some((conflict_reasons, true))` if the expression is forced to `target_value`.
    pub(crate) fn is_expression_forced_to_value(
        &self,
        expr: &LinearExpr,
        target_value: &BigRational,
    ) -> Option<(Vec<TheoryLit>, bool)> {
        let debug = debug_lra_forced();

        // A zero coefficient means the expression does not depend on that
        // variable: drop such entries before the case split, so `0*x + c`
        // is the constant `c` (Case 1) and Case 2 never divides by zero.
        // `LinearExpr::coeffs` is a public field, so the sparse invariant is
        // re-established here rather than assumed.
        let sparse;
        let expr = if expr.coeffs.iter().any(|(_, c)| c.is_zero()) {
            sparse = expr.normalize();
            &sparse
        } else {
            expr
        };

        // Case 1: Expression is constant - it's forced to that constant value
        if expr.coeffs.is_empty() {
            return Some((Vec::new(), expr.constant == *target_value));
        }

        // Case 2: Single variable expression - check if that variable is pinned
        if expr.coeffs.len() == 1 {
            let (var, coeff) = &expr.coeffs[0];
            if let Some(info) = self.vars.get(*var as usize) {
                // Expression value = coeff * var + constant
                // For it to be forced to target_value: coeff * var + constant = target_value
                // So var must be forced to (target_value - constant) / coeff
                let required_var_value = (target_value - expr.constant.to_big()) / coeff.to_big();

                if debug {
                    safe_eprintln!("[LRA_FORCED] Single-var expr: var={}, coeff={}, const={}, target={}, required={}",
                        var, coeff, expr.constant, target_value, required_var_value);
                    safe_eprintln!(
                        "[LRA_FORCED]   var info: lower={:?}, upper={:?}, value={}",
                        info.lower.as_ref().map(|b| (&b.value, b.strict)),
                        info.upper.as_ref().map(|b| (&b.value, b.strict)),
                        info.value
                    );
                }

                // Check if var is pinned to required_var_value
                let is_pinned = info
                    .lower
                    .as_ref()
                    .is_some_and(|lb| lb.value == required_var_value && !lb.strict)
                    && info
                        .upper
                        .as_ref()
                        .is_some_and(|ub| ub.value == required_var_value && !ub.strict);

                if debug {
                    safe_eprintln!("[LRA_FORCED]   is_pinned={}", is_pinned);
                }

                if is_pinned {
                    let mut reasons = Vec::new();
                    if let Some(ref lb) = info.lower {
                        for (r, v) in lb.reasons.iter().zip(&lb.reason_values) {
                            if !r.is_sentinel() {
                                reasons.push(TheoryLit::new(*r, *v));
                            }
                        }
                    }
                    if let Some(ref ub) = info.upper {
                        for (r, v) in ub.reasons.iter().zip(&ub.reason_values) {
                            if !r.is_sentinel() && !reasons.iter().any(|x| x.term == *r) {
                                reasons.push(TheoryLit::new(*r, *v));
                            }
                        }
                    }
                    return Some((reasons, true));
                }
            }
            return None;
        }

        self.multi_var_expression_forced_to_value(expr, target_value)
    }

    /// Collect tableau slack variables whose rows are proportional to `expr`.
    ///
    /// Each match is `(basic_var, required_basic_value, ratio_positive)` where
    /// `expr = k * (basic_var - row_constant) + expr_constant` and
    /// `ratio_positive` is `k > 0`. The SIGN of `k` decides which side of
    /// `expr` a bound on `basic_var` constrains: for `k < 0` a LOWER bound on
    /// the slack is an UPPER bound on `expr` (and vice versa).
    fn matching_slack_vars(
        &self,
        expr: &LinearExpr,
        target_value: &BigRational,
    ) -> Vec<(u32, BigRational, bool)> {
        let mut matching = Vec::new();
        let normalized_expr = expr.normalize();

        for row in &self.rows {
            // Tableau rows are constructed and pivot-maintained
            // normalized, so the common case compares slices in place;
            // the clone+normalize fallback covers any row that is not.
            // (This scan runs per disequality per check: normalizing
            // every row every time was the top profile frame on
            // Certora QF_UFDTNIA 39657...48.)
            let normalized_row;
            let row_coeffs: &[(u32, Rational)] = if coeffs_are_normalized(&row.coeffs) {
                &row.coeffs
            } else {
                normalized_row = LinearExpr {
                    coeffs: row.coeffs.clone(),
                    constant: row.constant.clone(),
                }
                .normalize();
                &normalized_row.coeffs
            };

            // Use semantic coefficient comparison: exact match first,
            // then proportional match (e.g., 4294967296*(A-B) vs (A-B), or
            // -(A-B) vs (A-B) — a NEGATIVE ratio flips bound sides).
            let (required_basic_value, ratio_positive) =
                if same_coeff_slices(&normalized_expr.coeffs, row_coeffs) {
                    // expr = row_expr + (expr_constant - row_constant).
                    // The row constant is widened to a BigRational only for a
                    // MATCHING row: converting it for every row before the
                    // comparison was the allocation hot spot of this scan
                    // (AY-SMT-2 sampling: UFLIA 21ea7d7d spent most of its
                    // samples in `to_big`/drop of this value).
                    (
                        target_value - expr.constant.to_big() + row.constant.to_big(),
                        true,
                    )
                } else if let Some(k) =
                    proportional_coeff_slice_ratio(&normalized_expr.coeffs, row_coeffs)
                {
                    // expr = k * basic_var + (expr_constant - k * row_constant).
                    let positive = k.is_positive();
                    let row_constant_big = row.constant.to_big();
                    (
                        (target_value - expr.constant.to_big() + &k * &row_constant_big) / &k,
                        positive,
                    )
                } else {
                    continue;
                };
            matching.push((row.basic_var, required_basic_value, ratio_positive));
        }

        matching
    }

    /// Check whether matching tableau rows jointly pin a multi-var expression.
    ///
    /// SOUNDNESS: `expr` is pinned only by a bound at the target on EACH side
    /// of `expr`. A slack whose row is a NEGATIVE multiple of `expr` contributes
    /// its lower bound to `expr`'s upper side and its upper bound to `expr`'s
    /// lower side; counting them unflipped "pinned" `y - z` from the one-sided
    /// pair `y - z <= 0`, `z - y >= 0` and refuted a satisfiable `y != z`.
    fn multi_var_expression_forced_to_value(
        &self,
        expr: &LinearExpr,
        target_value: &BigRational,
    ) -> Option<(Vec<TheoryLit>, bool)> {
        let matching_slack_vars = self.matching_slack_vars(expr, target_value);
        if matching_slack_vars.is_empty() {
            return None;
        }

        let mut all_reasons: Vec<TheoryLit> = Vec::new();
        let mut has_lower_bound_at_target = false;
        let mut has_upper_bound_at_target = false;
        let push_reasons = |bound: &crate::Bound, all_reasons: &mut Vec<TheoryLit>| {
            for (r, v) in bound.reasons.iter().zip(&bound.reason_values) {
                if !r.is_sentinel() && !all_reasons.iter().any(|x| x.term == *r) {
                    all_reasons.push(TheoryLit::new(*r, *v));
                }
            }
        };

        for (slack_var, required_value, ratio_positive) in &matching_slack_vars {
            if let Some(info) = self.vars.get(*slack_var as usize) {
                if info.value.rational() != *required_value {
                    continue;
                }

                if let Some(ref lb) = info.lower {
                    if lb.value == *required_value && !lb.strict {
                        if *ratio_positive {
                            has_lower_bound_at_target = true;
                        } else {
                            has_upper_bound_at_target = true;
                        }
                        push_reasons(lb, &mut all_reasons);
                    }
                }
                if let Some(ref ub) = info.upper {
                    if ub.value == *required_value && !ub.strict {
                        if *ratio_positive {
                            has_upper_bound_at_target = true;
                        } else {
                            has_lower_bound_at_target = true;
                        }
                        push_reasons(ub, &mut all_reasons);
                    }
                }
            }
        }

        (has_lower_bound_at_target && has_upper_bound_at_target).then_some((all_reasons, true))
    }

    /// Discover interface equalities `a = b` that are ENTAILED because the
    /// simplex pins the DIFFERENCE `a - b` to exactly `[0,0]` (lower == upper ==
    /// 0, both non-strict), even when neither `a` nor `b` is individually pinned.
    ///
    /// This is the "implied difference equality" completeness step: e.g. from
    /// `x <= y ∧ y <= x` the tableau holds a row representing `x - y` pinned to
    /// 0, but neither `x` nor `y` has a tight individual bound, so the existing
    /// tight-bound grouping (Phase 2) never emits `x = y`. EUF congruence then
    /// never fires on `f(x), f(y)`.
    ///
    /// SOUNDNESS (the Lean (ENT) invariant): we ONLY return a pair when
    /// `is_expression_forced_to_value(a - b, 0)` succeeds AND yields a NON-EMPTY
    /// reason set. That guard reuses the #6282 discipline: a zero-reason "forced"
    /// value is merely a simplex/default-model artifact, not a genuine
    /// entailment, and emitting it would flood EUF with spurious equalities
    /// (false-UNSAT). A non-empty reason set means asserted constraints (the
    /// entailing literals) truly pin `a - b` to 0 — exactly invariant (ENT).
    ///
    /// TRACTABILITY: candidate pairs come from
    /// `difference_pair_reasons` — one bucketing pass over the asserted
    /// atoms — never an O(n^2) pair query over unrelated variables.
    /// The former row-co-occurrence coupling pre-filter rebuilt every
    /// co-occurring pair of every tableau row on every call
    /// (Θ(rows × touched²) hash inserts per Nelson-Oppen round; the
    /// top on-CPU frames on QF_LIRA smtopt, whose rows touch thousands
    /// of candidates). It was purely a work filter from the older
    /// per-pair design: the emitted reasons are entailing asserted
    /// literals by construction, independent of row coupling, so
    /// intersecting with the reason buckets directly is sound and
    /// can only surface entailed pairs the coupling missed.
    /// (#lra-diff-no-couple)
    ///
    /// Returns `(term_a, term_b, reasons)` with `term_a.0 < term_b.0`.
    pub fn find_entailed_difference_equalities(
        &self,
        candidates: &[TermId],
    ) -> Vec<(TermId, TermId, Vec<TheoryLit>)> {
        let mut result: Vec<(TermId, TermId, Vec<TheoryLit>)> = Vec::new();
        if candidates.len() < 2 {
            return result;
        }

        // Map each candidate TermId to its registered internal var id (if any).
        let mut cand_vars: Vec<(TermId, u32)> = Vec::new();
        for &t in candidates {
            if let Some(&v) = self.term_to_var.get(&t) {
                cand_vars.push((t, v));
            }
        }
        if cand_vars.len() < 2 {
            return result;
        }

        let cand_var_set: std::collections::HashSet<u32> =
            cand_vars.iter().map(|(_, v)| *v).collect();

        // #certora-diff-one-pass: the former code ran
        // `entailed_difference_zero_reasons(va, vb)` per coupled pair, and that
        // helper scanned ALL asserted atoms per call — Θ(pairs × asserted) per
        // Nelson-Oppen round (~12% of on-CPU samples on the Certora QF_UFLIA
        // VC family, 2026-07-14 profile). One pass over the SAME `asserted`
        // iteration (DetHashMap — deterministic) now buckets the "difference
        // atoms" by unordered var pair with the identical per-pair resolution
        // rules (first eq atom wins immediately; otherwise the first `<=`/`>=`
        // reasons, frozen the moment both directions are found — mirroring the
        // former early `break`), so each coupled pair resolves by O(1) lookup
        // to the byte-identical reason set.
        let diff_resolved = self.difference_pair_reasons();

        for (&(va, vb), reasons) in diff_resolved.iter() {
            if !cand_var_set.contains(&va) || !cand_var_set.contains(&vb) {
                continue;
            }
            // SOUNDNESS (ENT): only emit `a = b` when asserted literals pin
            // `a - b` to exactly 0 with a NON-EMPTY reason set (see
            // `difference_pair_reasons`) — never a model/default artifact.
            if reasons.is_empty() {
                continue;
            }
            let (ta, tb) = match (self.var_to_term.get(&va), self.var_to_term.get(&vb)) {
                (Some(&ta), Some(&tb)) => (ta, tb),
                _ => continue,
            };
            if ta == tb {
                continue;
            }
            let (lo, hi) = if ta.0 < tb.0 { (ta, tb) } else { (tb, ta) };
            result.push((lo, hi, reasons.clone()));
        }

        result
    }

    /// Assert a linear equality constraint: Σ(coeff * var) = value
    ///
    /// Used by Nelson-Oppen combination to receive equalities from other theories.
    /// The coefficients map term IDs to their coefficients in the linear expression.
    /// The value is the RHS of the equation.
    ///
    /// This adds two bounds: expr <= value AND expr >= value, effectively expr = value.
    pub fn assert_linear_equality(
        &mut self,
        coeffs: &HashMap<TermId, BigRational>,
        value: &BigRational,
        reason_term: TermId,
        reason_value: bool,
    ) {
        let single_reason = [(reason_term, reason_value)];
        self.assert_linear_equality_with_reasons(coeffs, value, &single_reason);
    }

    /// Assert a linear equality constraint with multiple reason literals.
    ///
    /// Passes all reason literals through to the bound assertions so conflict
    /// explanations are complete (#4891).
    pub fn assert_linear_equality_with_reasons(
        &mut self,
        coeffs: &HashMap<TermId, BigRational>,
        value: &BigRational,
        reasons: &[(TermId, bool)],
    ) {
        // Build a linear expression from coefficients
        // Sort by TermId for deterministic variable registration order (#2681)
        let mut sorted_coeffs: Vec<_> = coeffs.iter().collect();
        sorted_coeffs.sort_by_key(|(&term, _)| term);
        let mut expr = LinearExpr::zero();
        for (&term, coeff) in sorted_coeffs {
            let var = self.ensure_var_registered(term);
            expr.add_term(var, coeff.clone());
        }

        // Add dual bounds: expr <= value AND expr >= value
        // These together enforce expr = value
        // #8406: Convert BigRational to Rational at the public API boundary.
        let rat_value = Rational::from_big(value.clone());
        self.assert_bound_with_reasons(
            expr.clone(),
            rat_value.clone(),
            BoundType::Upper,
            false,
            reasons,
            None,
        );
        self.assert_bound_with_reasons(expr, rat_value, BoundType::Lower, false, reasons, None);
        self.dirty = true;
    }
}
