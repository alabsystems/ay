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
use crate::{BoundType, LinearExpr, LraSolver, Rational};
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermId;
use ay_core::DebugChannel;
use ay_core::TheoryLit;
use num_rational::BigRational;

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
    fn matching_slack_vars(
        &self,
        expr: &LinearExpr,
        target_value: &BigRational,
    ) -> Vec<(u32, BigRational)> {
        let mut matching = Vec::new();
        let normalized_expr = expr.normalize();

        for row in &self.rows {
            let row_constant_big = row.constant.to_big();
            let normalized_row = LinearExpr {
                coeffs: row.coeffs.clone(),
                constant: row.constant.clone(),
            }
            .normalize();

            // Use semantic coefficient comparison: exact match first,
            // then proportional match (e.g., 4294967296*(A-B) vs (A-B)).
            let required_basic_value = if normalized_expr.same_coefficients(&normalized_row) {
                // expr = row_expr + (expr_constant - row_constant).
                target_value - expr.constant.to_big() + &row_constant_big
            } else if let Some(k) = normalized_expr.proportional_coefficient_ratio(&normalized_row)
            {
                // expr = k * basic_var + (expr_constant - k * row_constant).
                (target_value - expr.constant.to_big() + &k * &row_constant_big) / &k
            } else {
                continue;
            };
            matching.push((row.basic_var, required_basic_value));
        }

        matching
    }

    /// Check whether matching tableau rows jointly pin a multi-var expression.
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

        for (slack_var, required_value) in &matching_slack_vars {
            if let Some(info) = self.vars.get(*slack_var as usize) {
                if info.value.rational() != *required_value {
                    continue;
                }

                if let Some(ref lb) = info.lower {
                    if lb.value == *required_value && !lb.strict {
                        has_lower_bound_at_target = true;
                        for (r, v) in lb.reasons.iter().zip(&lb.reason_values) {
                            if !r.is_sentinel() && !all_reasons.iter().any(|x| x.term == *r) {
                                all_reasons.push(TheoryLit::new(*r, *v));
                            }
                        }
                    }
                }
                if let Some(ref ub) = info.upper {
                    if ub.value == *required_value && !ub.strict {
                        has_upper_bound_at_target = true;
                        for (r, v) in ub.reasons.iter().zip(&ub.reason_values) {
                            if !r.is_sentinel() && !all_reasons.iter().any(|x| x.term == *r) {
                                all_reasons.push(TheoryLit::new(*r, *v));
                            }
                        }
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
    /// TRACTABILITY: we only consider pairs of candidate interface terms that are
    /// already COUPLED by asserted bounds, i.e. that co-occur in some tableau
    /// row. `is_expression_forced_to_value` for a difference returns `None`
    /// unless a matching tableau row exists, so uncoupled pairs are cheap to
    /// reject; we additionally pre-filter via row co-occurrence so we never run
    /// the full O(n^2) difference query over unrelated variables.
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

        // Determine which candidate-var pairs are COUPLED by asserted bounds: two
        // candidate vars are coupled when, after expressing them in the simplex's
        // nonbasic basis (substituting basic vars via their defining rows), they
        // share a nonbasic variable or are both pinned by a common row. We
        // approximate this cheaply: a pair is a candidate if both vars appear
        // (as basic var or coefficient) in some tableau row, OR if one is the
        // basic var of a row mentioning the other. This restricts work to pairs
        // genuinely connected by the asserted `<=/>=` rows — never the full
        // O(n^2) over unrelated program variables.
        let mut coupled: std::collections::HashSet<(u32, u32)> = std::collections::HashSet::new();
        for row in &self.rows {
            let mut touched: Vec<u32> = Vec::new();
            if cand_var_set.contains(&row.basic_var) {
                touched.push(row.basic_var);
            }
            for &(v, _) in &row.coeffs {
                if cand_var_set.contains(&v) && !touched.contains(&v) {
                    touched.push(v);
                }
            }
            for i in 0..touched.len() {
                for j in (i + 1)..touched.len() {
                    let (va, vb) = (touched[i], touched[j]);
                    let pair = if va < vb { (va, vb) } else { (vb, va) };
                    coupled.insert(pair);
                }
            }
        }

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

        for (va, vb) in coupled {
            // SOUNDNESS (ENT): only emit `a = b` when asserted literals pin
            // `a - b` to exactly 0 with a NON-EMPTY reason set (see
            // `difference_pair_reasons`) — never a model/default artifact.
            if let Some(reasons) = diff_resolved.get(&(va, vb)) {
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
