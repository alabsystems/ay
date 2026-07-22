// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interval computation and endpoint predicates for implied bounds.
//!
//! Extracted from `implied_bounds.rs` to reduce file size.
//! Contains: `compute_expr_interval`, endpoint implication predicates,
//! `collect_interval_reasons`, and `collect_slack_interval_reasons_for_var`.

use super::*;

impl LraSolver {
    /// Compute interval `[lb, ub]` of a linear expression from current bounds.
    ///
    /// Direct bounds are preferred because their witnesses are read directly
    /// from asserted atoms. When a direct bound is absent, the interval falls
    /// back to the current implied bound so compound propagation still has a
    /// finite endpoint to reason about. Endpoint strictness is preserved so
    /// callers can distinguish closed `0` from open `0` (`#6582`).
    ///
    /// #8406: Uses `Rational` accumulators instead of `BigRational` to eliminate
    /// heap allocation in the common case where all bounds and coefficients fit
    /// in i64. The `Rational * &Rational` operator stays inline for Small/Small.
    pub(crate) fn compute_expr_interval(&self, expr: &LinearExpr) -> ExprInterval {
        let mut lb = expr.constant.clone();
        let mut ub = expr.constant.clone();
        let mut lb_finite = true;
        let mut ub_finite = true;
        let mut lb_strict = false;
        let mut ub_strict = false;

        for &(var, ref coeff) in &expr.coeffs {
            let vi = var as usize;
            if vi >= self.vars.len() {
                return (None, None);
            }
            let info = &self.vars[vi];

            // #8511 soundness fix: Only use DIRECT bounds in interval computation.
            //
            // Previously (#8254), implied bounds were used as fallback when direct
            // bounds were absent. But collect_interval_reasons() sometimes fails to
            // collect complete transitive reasons for implied bounds (budget exceeded,
            // explanation chain incomplete, or row-walking produces reasons for a
            // weaker bound than the one used in interval computation). This mismatch
            // between the TIGHTER implied bound used in compute_expr_interval and the
            // WEAKER direct bound reasons collected by collect_interval_reasons
            // produced unsound propagations: the reasons don't actually prove the
            // propagated literal.
            //
            // On rand_70_300_1155482584_4.lp.smt2, this caused 28K+ unsound
            // propagations leading to false-UNSAT.
            //
            // Fix: use only direct bounds here. When a variable lacks a direct
            // bound, the interval dimension becomes infinite (None). This produces
            // fewer propagations but they are all sound. The DeferredReason::ImpliedBound
            // path in propagation.rs handles implied-bound propagations separately
            // with proper reason collection.
            let direct_lb = info.lower.as_ref().map(|b| (&b.value, b.strict));
            let direct_ub = info.upper.as_ref().map(|b| (&b.value, b.strict));

            if coeff.is_positive() {
                // c > 0: ub += c * ub(x), lb += c * lb(x)
                if ub_finite {
                    if let Some((bv, strict)) = direct_ub {
                        ub.mul_add_assign(coeff, bv);
                        ub_strict |= strict;
                    } else {
                        ub_finite = false;
                    }
                }
                if lb_finite {
                    if let Some((bv, strict)) = direct_lb {
                        lb.mul_add_assign(coeff, bv);
                        lb_strict |= strict;
                    } else {
                        lb_finite = false;
                    }
                }
            } else {
                // c < 0: ub += c * lb(x), lb += c * ub(x)
                if ub_finite {
                    if let Some((bv, strict)) = direct_lb {
                        ub.mul_add_assign(coeff, bv);
                        ub_strict |= strict;
                    } else {
                        ub_finite = false;
                    }
                }
                if lb_finite {
                    if let Some((bv, strict)) = direct_ub {
                        lb.mul_add_assign(coeff, bv);
                        lb_strict |= strict;
                    } else {
                        lb_finite = false;
                    }
                }
            }
            // #8800: Early exit when both bounds are infinite — no more arithmetic needed.
            if !lb_finite && !ub_finite {
                return (None, None);
            }
        }

        (
            lb_finite.then(|| IntervalEndpoint::new(lb, lb_strict)),
            ub_finite.then(|| IntervalEndpoint::new(ub, ub_strict)),
        )
    }

    pub(crate) fn endpoint_implies_le_zero(ep: &IntervalEndpoint, strict_atom: bool) -> bool {
        if strict_atom {
            ep.value.is_negative() || (ep.value.is_zero() && ep.strict)
        } else {
            !ep.value.is_positive()
        }
    }

    pub(crate) fn endpoint_implies_ge_zero(ep: &IntervalEndpoint, strict_atom: bool) -> bool {
        if strict_atom {
            ep.value.is_positive() || (ep.value.is_zero() && ep.strict)
        } else {
            !ep.value.is_negative()
        }
    }

    pub(crate) fn endpoint_implies_not_le_zero(ep: &IntervalEndpoint, strict_atom: bool) -> bool {
        if strict_atom {
            !ep.value.is_negative()
        } else {
            ep.value.is_positive() || (ep.value.is_zero() && ep.strict)
        }
    }

    pub(crate) fn endpoint_implies_not_ge_zero(ep: &IntervalEndpoint, strict_atom: bool) -> bool {
        if strict_atom {
            !ep.value.is_positive()
        } else {
            ep.value.is_negative() || (ep.value.is_zero() && ep.strict)
        }
    }

    /// Collect the reason literals for an interval bound on an expression.
    /// `for_upper`: if true, collect reasons for the upper bound (used when
    /// propagating atom=true); if false, for the lower bound (atom=false).
    ///
    /// When a variable lacks a direct bound but has an implied bound from a
    /// tableau row, transitively collects reasons from the nonbasic variables
    /// in that row via `collect_row_reasons_dedup` (#4919, #8254).
    ///
    /// #8254 Soundness fix: compute_expr_interval() uses implied bounds as
    /// fallback. This function must use the same implied-bound pathway with
    /// proper transitive reason collection to ensure soundness. Previously
    /// it only used direct bounds, creating a mismatch that caused 11K+
    /// unsound propagations.
    pub(crate) fn collect_interval_reasons(
        &self,
        expr: &LinearExpr,
        for_upper: bool,
    ) -> Vec<TheoryLit> {
        let mut seen = HashSet::default();
        self.collect_interval_reasons_with_seen(expr, for_upper, &mut seen)
    }

    /// #8599: collect_interval_reasons variant that reuses a caller-provided
    /// seen set to avoid per-call HashSet allocation. The seen set is cleared
    /// before use so it is safe to reuse across calls.
    pub(crate) fn collect_interval_reasons_with_seen(
        &self,
        expr: &LinearExpr,
        for_upper: bool,
        seen: &mut HashSet<(TermId, bool)>,
    ) -> Vec<TheoryLit> {
        seen.clear();
        let mut reasons = Vec::new();
        let mut complete = true;
        for &(var, ref coeff) in &expr.coeffs {
            let vi = var as usize;
            if vi >= self.vars.len() {
                complete = false;
                break;
            }
            // For upper bound: c>0 → use ub(x), c<0 → use lb(x)
            // For lower bound: c>0 → use lb(x), c<0 → use ub(x)
            let need_upper = coeff.is_positive() == for_upper;

            let info = &self.vars[vi];
            let bound = if need_upper { &info.upper } else { &info.lower };
            if let Some(b) = bound {
                for (term, val) in b.reason_pairs() {
                    if !term.is_sentinel() && seen.insert((term, val)) {
                        reasons.push(TheoryLit::new(term, val));
                    }
                }
            } else {
                // #8511: No direct bound — abandon propagation. compute_expr_interval()
                // no longer uses implied bounds, so this variable would have made the
                // interval infinite. If we reach here, something is inconsistent.
                complete = false;
                break;
            }
        }
        if !complete {
            reasons.clear();
        }
        reasons
    }

    /// Compute interval using ONLY direct (asserted) bounds, no implied fallback.
    ///
    /// #8511: Used as a soundness validation gate for interval propagation.
    /// When `compute_expr_interval` uses implied bounds to make a propagation
    /// decision, the reasons are collected from direct bounds via
    /// `collect_interval_reasons`. This creates a gap: the implied bound value
    /// may be tighter than the direct bound value, so the reasons may not
    /// justify the propagation conclusion.
    ///
    /// This function computes the "conservative" interval using only direct
    /// bounds. If the direct-only interval still implies the propagation,
    /// then direct-bound reasons are sufficient and the propagation is sound.
    /// If not, the propagation must be dropped.
    pub(crate) fn compute_expr_interval_direct_only(&self, expr: &LinearExpr) -> ExprInterval {
        let mut lb = expr.constant.clone();
        let mut ub = expr.constant.clone();
        let mut lb_finite = true;
        let mut ub_finite = true;
        let mut lb_strict = false;
        let mut ub_strict = false;

        for &(var, ref coeff) in &expr.coeffs {
            let vi = var as usize;
            if vi >= self.vars.len() {
                return (None, None);
            }
            let info = &self.vars[vi];

            let direct_lb = info.lower.as_ref().map(|b| (&b.value, b.strict));
            let direct_ub = info.upper.as_ref().map(|b| (&b.value, b.strict));

            if coeff.is_positive() {
                if ub_finite {
                    if let Some((bv, strict)) = direct_ub {
                        ub.mul_add_assign(coeff, bv);
                        ub_strict |= strict;
                    } else {
                        ub_finite = false;
                    }
                }
                if lb_finite {
                    if let Some((bv, strict)) = direct_lb {
                        lb.mul_add_assign(coeff, bv);
                        lb_strict |= strict;
                    } else {
                        lb_finite = false;
                    }
                }
            } else {
                if ub_finite {
                    if let Some((bv, strict)) = direct_lb {
                        ub.mul_add_assign(coeff, bv);
                        ub_strict |= strict;
                    } else {
                        ub_finite = false;
                    }
                }
                if lb_finite {
                    if let Some((bv, strict)) = direct_ub {
                        lb.mul_add_assign(coeff, bv);
                        lb_strict |= strict;
                    } else {
                        lb_finite = false;
                    }
                }
            }
            if !lb_finite && !ub_finite {
                return (None, None);
            }
        }

        (
            lb_finite.then(|| IntervalEndpoint::new(lb, lb_strict)),
            ub_finite.then(|| IntervalEndpoint::new(ub, ub_strict)),
        )
    }

    /// For a slack variable, reconstruct sound reasons from the original linear
    /// expression rather than using the slack bound's own witness list (#6564).
    ///
    /// Slack variables represent compound atoms (e.g., `s = x + y` for `x+y<=10`).
    /// Their direct bound `reason_pairs()` only witness the slack bound itself,
    /// not the contributing original-variable bounds. This helper looks up the
    /// atom's original expression via `atom_index`/`atom_cache` and delegates to
    /// `collect_interval_reasons` which walks the original variables.
    ///
    /// Returns `None` if the variable is not a slack, or if the expression lookup
    /// fails. Returns `Some(vec![])` if reconstruction was attempted but produced
    /// no reasons (caller should skip the propagation).
    #[allow(dead_code)]
    pub(crate) fn collect_slack_interval_reasons_for_var(
        &self,
        var: u32,
        for_upper: bool,
    ) -> Option<Vec<TheoryLit>> {
        if !self.slack_var_set.contains(&var) {
            return None;
        }

        let atoms = self.atom_index.get(&var)?;
        let first_atom = atoms.first()?;
        let info = self.atom_cache.get(&first_atom.term)?.as_ref()?;

        Some(self.collect_interval_reasons(&info.expr, for_upper))
    }
}
