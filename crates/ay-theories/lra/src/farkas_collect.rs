// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Farkas conflict collection, per-row conflict building, and deduplication.
//!
//! Complements `farkas` (row-level infeasibility detection) with:
//! - Batch conflict collection across all contradictory variable bounds
//! - Per-row conflict construction with Farkas certificates
//! - Literal deduplication with coefficient combining

use super::*;
use ay_core::term::TermId;
use ay_core::{FarkasAnnotation, TheoryConflict, TheoryLit};

impl LraSolver {
    /// Try to extract reason literals from a bound's provenance chain (#8151).
    ///
    /// When a bound's direct `reasons` field is empty or sentinel-only, the
    /// bound may still have a complete provenance chain (via `BoundProvenance`)
    /// that traces back to the original atom assertions. This is AY's equivalent
    /// of Z3's `set_evidence(u_dependency*)` which linearizes the dependency
    /// tree to collect all contributing constraint indices.
    ///
    /// Returns `Some(literals)` if provenance produced non-empty reasons,
    /// `None` otherwise.
    ///
    /// Reference: Z3 `theory_lra.cpp:3552-3555` (`set_evidence` flattens
    /// `u_dependency*` to literal+eq vectors).
    pub(crate) fn collect_reasons_from_provenance(bound: &Bound) -> Option<Vec<TheoryLit>> {
        let provenance = bound.provenance.as_ref()?;
        let reasons = provenance.collect_reasons_dedup();
        if reasons.is_empty() {
            return None;
        }
        let literals: Vec<TheoryLit> = reasons
            .into_iter()
            .map(|(term, value)| TheoryLit::new(term, value))
            .collect();
        Some(literals)
    }

    /// #8764: Release-mode stale-reason guard for theory conflicts.
    ///
    /// Verifies that every non-sentinel reason literal in the supplied list
    /// is currently asserted in `self.asserted` or `self.cross_theory_asserted`.
    /// If any literal is stale
    /// (e.g., backtracking retracted it between infeasibility detection and
    /// conflict construction), the caller should discard the conflict.
    ///
    /// Mirrors the propagation-layer guard in
    /// theory_solver/propagation.rs:975-986 and 1075-1090 (#8467/#9704).
    /// Parallel to Z3's 'is_bound_required()' check in theory_lra.cpp:3552-3555
    /// which verifies that the u_dependency* justification tree is live
    /// before set_evidence flattens it.
    ///
    /// Exposed as `pub` (#8784) so sibling theories in ay-theories-lia can
    /// delegate their own stale-reason guards to the authoritative trail
    /// maintained by LRA (which owns `cross_theory_asserted` for the
    /// arithmetic half of Nelson-Oppen).
    pub fn conflict_literals_all_asserted(&self, literals: &[TheoryLit]) -> bool {
        for lit in literals {
            if lit.term.is_sentinel() {
                continue;
            }
            let own_ok = self.asserted.get(&lit.term) == Some(&lit.value);
            let cross_ok = self.cross_theory_asserted.get(&lit.term) == Some(&lit.value);
            if !own_ok && !cross_ok {
                return false;
            }
        }
        true
    }

    /// Collect ALL contradictory variable bound conflicts, not just the first.
    ///
    /// The `dual_simplex_with_max_iters` precheck returns on the first bound
    /// contradiction. For problems with many independent bound conflicts in a
    /// single model (e.g., QF_LIA benchmarks with hundreds of equalities and
    /// inequalities), this causes O(N) DPLL(T) round trips where one suffices.
    ///
    /// This method returns ALL bound conflicts (excluding the one already
    /// returned by `dual_simplex`), so the caller can add all blocking clauses
    /// before re-running the SAT solver.
    pub fn collect_all_bound_conflicts(&self, skip_first: bool) -> Vec<TheoryConflict> {
        use num_rational::Rational64;
        let mut conflicts = Vec::new();
        let mut found_first = false;

        for var in 0..self.vars.len() {
            let info = &self.vars[var];
            let (Some(lower), Some(upper)) = (&info.lower, &info.upper) else {
                continue;
            };

            let contradicts = lower.value > upper.value
                || (lower.value == upper.value && (lower.strict || upper.strict));
            if !contradicts {
                continue;
            }

            if skip_first && !found_first {
                found_first = true;
                continue;
            }

            let mut literals = Vec::new();
            let mut coefficients = Vec::new();
            let mut all_fit = true;
            let mut lower_has_real = false;
            let mut upper_has_real = false;
            for ((reason, reason_value), scale) in
                lower.reasons.iter().zip(&lower.reason_values).zip(
                    lower
                        .reason_scales
                        .iter()
                        .chain(std::iter::repeat(types::rational_one())),
                )
            {
                if !reason.is_sentinel() {
                    lower_has_real = true;
                    literals.push(TheoryLit::new(*reason, *reason_value));
                    match Self::rational_to_rational64(scale) {
                        Some(c) => coefficients.push(c),
                        None => {
                            all_fit = false;
                            coefficients.push(Rational64::from(1));
                        }
                    }
                }
            }
            for ((reason, reason_value), scale) in
                upper.reasons.iter().zip(&upper.reason_values).zip(
                    upper
                        .reason_scales
                        .iter()
                        .chain(std::iter::repeat(types::rational_one())),
                )
            {
                if !reason.is_sentinel() {
                    upper_has_real = true;
                    literals.push(TheoryLit::new(*reason, *reason_value));
                    match Self::rational_to_rational64(scale) {
                        Some(c) => coefficients.push(c),
                        None => {
                            all_fit = false;
                            coefficients.push(Rational64::from(1));
                        }
                    }
                }
            }
            // Both sides of the contradiction need real reasons (#4919).
            // #8151: Provenance fallback before skipping.
            if !lower_has_real {
                if let Some(prov_lits) = Self::collect_reasons_from_provenance(lower) {
                    lower_has_real = true;
                    literals.extend(prov_lits);
                    all_fit = false; // No Farkas coefficients for provenance-derived reasons
                }
            }
            if !upper_has_real {
                if let Some(prov_lits) = Self::collect_reasons_from_provenance(upper) {
                    upper_has_real = true;
                    literals.extend(prov_lits);
                    all_fit = false;
                }
            }
            if !lower_has_real || !upper_has_real {
                continue;
            }
            let farkas_opt = if all_fit {
                Some(FarkasAnnotation::new(coefficients))
            } else {
                None
            };
            let (dedup_lits, dedup_coeffs) =
                Self::deduplicate_conflict(literals, farkas_opt.as_ref());
            if dedup_lits.is_empty() {
                continue;
            }
            let farkas = if !dedup_coeffs.is_empty() {
                Some(FarkasAnnotation::new(dedup_coeffs))
            } else if all_fit {
                Some(FarkasAnnotation::new(
                    (0..dedup_lits.len()).map(|_| Rational64::from(1)).collect(),
                ))
            } else {
                None
            };
            conflicts.push(match farkas {
                Some(f) => TheoryConflict::with_farkas(dedup_lits, f),
                None => TheoryConflict::new(dedup_lits),
            });
        }
        conflicts
    }

    /// Build conflict explanation with Farkas coefficients for interpolation
    ///
    /// For infeasible row: basic_var = Σ(coeff * nb_var) + constant
    /// When basic_var violates its bound, the Farkas certificate is:
    /// - Coefficient 1 for the basic variable's violated bound
    /// - Coefficient |coeff| for each non-basic variable's active bound
    pub(crate) fn build_conflict_with_farkas(&mut self, row_idx: usize) -> TheoryConflict {
        use num_rational::Rational64;

        let debug_farkas = ay_core::debug_channel_active(ay_core::DebugChannel::FarkasRow);

        let mut literals = Vec::new();
        let mut coefficients: Option<Vec<Rational64>> = Some(Vec::new());
        let row = &self.rows[row_idx];
        let violated_bound = self.violates_bounds(row.basic_var);

        if debug_farkas {
            let basic_term_dbg = self.var_term_id(row.basic_var);
            safe_eprintln!(
                "[FARKAS-ROW] row_idx={}, basic_var={}, basic_term={:?}, violated={:?}, {} coeffs",
                row_idx,
                row.basic_var,
                basic_term_dbg,
                violated_bound,
                row.coeffs.len()
            );
            let basic_info_dbg = &self.vars[row.basic_var as usize];
            safe_eprintln!(
                "[FARKAS-ROW]   basic lower={} upper={} status={:?}",
                basic_info_dbg
                    .lower
                    .as_ref()
                    .map(|b| format!("val={} reasons={}", b.value, b.reasons.len()))
                    .unwrap_or_else(|| "None".into()),
                basic_info_dbg
                    .upper
                    .as_ref()
                    .map(|b| format!("val={} reasons={}", b.value, b.reasons.len()))
                    .unwrap_or_else(|| "None".into()),
                basic_info_dbg.status,
            );
            for (nb_var, coeff) in &row.coeffs {
                let nb_info_dbg = &self.vars[*nb_var as usize];
                let nb_term_dbg = self.var_term_id(*nb_var);
                safe_eprintln!(
                    "[FARKAS-ROW]   nb_var={}, term={:?}, coeff={}, status={:?}, lower={}, upper={}",
                    nb_var, nb_term_dbg, coeff, nb_info_dbg.status,
                    nb_info_dbg.lower.as_ref().map(|b| format!("val={} reasons={} reason_terms={:?}", b.value, b.reasons.len(), b.reasons.iter().zip(b.reason_values.iter()).map(|(r,v)| format!("({r:?},{v})")).collect::<Vec<_>>())).unwrap_or_else(|| "None".into()),
                    nb_info_dbg.upper.as_ref().map(|b| format!("val={} reasons={} reason_terms={:?}", b.value, b.reasons.len(), b.reasons.iter().zip(b.reason_values.iter()).map(|(r,v)| format!("({r:?},{v})")).collect::<Vec<_>>())).unwrap_or_else(|| "None".into()),
                );
            }
        }

        // Track two distinct forms of incomplete explanations:
        // - sentinel-only reasons from derived cuts, which can drop Farkas
        //   metadata but may still yield a valid blocking clause
        // - reasonless bounds, which are not safe to omit from the returned
        //   conflict because doing so can make the clause semantically SAT (#4919)
        let mut has_sentinel_only_bound = false;
        let mut has_reasonless_bound = false;

        // Basic variable's violated bound gets coefficient scaled by reason_scale.
        // For direct variable bounds, reason_scale=1. For bounds derived from
        // multi-coefficient atoms (fast path), reason_scale=1/|coeff|.
        let basic_info = &self.vars[row.basic_var as usize];
        match violated_bound {
            Some(BoundType::Lower) => {
                if let Some(ref lower) = basic_info.lower {
                    let mut pushed_basic = false;
                    // Add ALL reasons from the violated bound to the conflict clause.
                    for ((reason, reason_value), scale) in
                        lower.reasons.iter().zip(&lower.reason_values).zip(
                            lower
                                .reason_scales
                                .iter()
                                .chain(std::iter::repeat(types::rational_one())),
                        )
                    {
                        if !reason.is_sentinel() {
                            pushed_basic = true;
                            literals.push(TheoryLit::new(*reason, *reason_value));
                            if let Some(coeffs) = coefficients.as_mut() {
                                match Self::rational_to_rational64(scale) {
                                    Some(c) => coeffs.push(c),
                                    None => {
                                        coefficients = None;
                                    }
                                }
                            }
                        }
                    }
                    if !pushed_basic {
                        if lower.reasons.is_empty() {
                            has_reasonless_bound = true;
                        } else {
                            has_sentinel_only_bound = true;
                        }
                    }
                }
            }
            Some(BoundType::Upper) => {
                if let Some(ref upper) = basic_info.upper {
                    let mut pushed_basic = false;
                    for ((reason, reason_value), scale) in
                        upper.reasons.iter().zip(&upper.reason_values).zip(
                            upper
                                .reason_scales
                                .iter()
                                .chain(std::iter::repeat(types::rational_one())),
                        )
                    {
                        if !reason.is_sentinel() {
                            pushed_basic = true;
                            literals.push(TheoryLit::new(*reason, *reason_value));
                            if let Some(coeffs) = coefficients.as_mut() {
                                match Self::rational_to_rational64(scale) {
                                    Some(c) => coeffs.push(c),
                                    None => {
                                        coefficients = None;
                                    }
                                }
                            }
                        }
                    }
                    if !pushed_basic {
                        if upper.reasons.is_empty() {
                            has_reasonless_bound = true;
                        } else {
                            has_sentinel_only_bound = true;
                        }
                    }
                }
            }
            None => {
                // Defensive: shouldn't happen when called from infeasible row handling.
            }
        }

        // Non-basic variables' bounds get their tableau coefficients (absolute value)
        // scaled by the bound's per-reason Farkas scale factor.
        // The sign of the coefficient determines which bound is "active"
        for (nb_var, coeff) in &row.coeffs {
            let nb_info = &self.vars[*nb_var as usize];
            if coeff.is_zero() {
                continue;
            }
            // Skip basic variables (#4919): after pivots, row.coeffs may reference
            // variables that are now basic for other rows. These are not "stuck at
            // bounds" in the Dutertre & de Moura sense — their values are determined
            // by their row equations, not by bounds. Including them produces false
            // missing_active_bound_reasons aborts and spurious Unknown results.
            // This matches the guard in find_beneficial_entering (line 372).
            // #8012: basic vars with tight bounds (lower==upper, non-strict)
            // ARE fixed by their bounds, not row equations. Include their reasons.
            if !matches!(nb_info.status, Some(VarStatus::NonBasic)) {
                let has_tight = match (&nb_info.lower, &nb_info.upper) {
                    (Some(lb), Some(ub)) => lb.value == ub.value && !lb.strict && !ub.strict,
                    _ => false,
                };
                if !has_tight {
                    continue;
                }
            }
            // #8406: Use Rational abs() instead of abs_bigrational() to avoid
            // BigRational heap allocation.
            let abs_coeff = coeff.abs();

            // Choose the *active* bound, per Dutertre & de Moura (CAV'06): when no pivot exists,
            // each non-basic var is stuck at the bound that blocks restoring feasibility.
            let active_bound = match violated_bound {
                Some(BoundType::Lower) => {
                    // Basic var is too small; we needed to move nb_var in the direction that increases it:
                    //   coeff > 0 => increase nb_var => blocked by upper bound
                    //   coeff < 0 => decrease nb_var => blocked by lower bound
                    if coeff.is_positive() {
                        nb_info.upper.as_ref()
                    } else {
                        nb_info.lower.as_ref()
                    }
                }
                Some(BoundType::Upper) => {
                    // Basic var is too large:
                    //   coeff > 0 => decrease nb_var => blocked by lower bound
                    //   coeff < 0 => increase nb_var => blocked by upper bound
                    if coeff.is_positive() {
                        nb_info.lower.as_ref()
                    } else {
                        nb_info.upper.as_ref()
                    }
                }
                None => None,
            };

            let mut pushed_any = false;
            match active_bound {
                Some(bound) => {
                    for ((reason, reason_value), scale) in
                        bound.reasons.iter().zip(&bound.reason_values).zip(
                            bound
                                .reason_scales
                                .iter()
                                .chain(std::iter::repeat(types::rational_one())),
                        )
                    {
                        if !reason.is_sentinel() {
                            pushed_any = true;
                            literals.push(TheoryLit::new(*reason, *reason_value));
                            if let Some(coeffs) = coefficients.as_mut() {
                                let scaled = &abs_coeff * scale;
                                match Self::rational_to_rational64(&scaled) {
                                    Some(c) => coeffs.push(c),
                                    None => {
                                        coefficients = None;
                                    }
                                }
                            }
                        }
                    }

                    if !pushed_any {
                        if bound.reasons.is_empty() {
                            has_reasonless_bound = true;
                        } else {
                            has_sentinel_only_bound = true;
                        }
                        coefficients = None;
                    }
                }
                None => {
                    let has_any_bound = nb_info.lower.is_some() || nb_info.upper.is_some();
                    if has_any_bound {
                        has_reasonless_bound = true;
                        coefficients = None;
                    }
                }
            }
        }

        // Reasonless bounds make the conflict semantically unsound (#4919):
        // the omitted bound is not justified, so the remaining literals alone
        // can be SAT. Before degrading to Unknown, try provenance-based reason
        // extraction (#8151): the bound may have a complete provenance chain
        // (via BoundProvenance) even when direct reasons are empty.
        if has_reasonless_bound {
            // #8151: Provenance fallback — rebuild conflict from provenance chains.
            let mut provenance_literals = Vec::new();
            let mut provenance_ok = true;
            let basic_info = &self.vars[row.basic_var as usize];
            // Collect provenance for the basic variable's violated bound
            match violated_bound {
                Some(BoundType::Lower) => {
                    if let Some(ref lower) = basic_info.lower {
                        if lower.reasons.is_empty() || lower.reasons.iter().all(|r| r.is_sentinel())
                        {
                            match Self::collect_reasons_from_provenance(lower) {
                                Some(prov_lits) => provenance_literals.extend(prov_lits),
                                None => provenance_ok = false,
                            }
                        }
                    }
                }
                Some(BoundType::Upper) => {
                    if let Some(ref upper) = basic_info.upper {
                        if upper.reasons.is_empty() || upper.reasons.iter().all(|r| r.is_sentinel())
                        {
                            match Self::collect_reasons_from_provenance(upper) {
                                Some(prov_lits) => provenance_literals.extend(prov_lits),
                                None => provenance_ok = false,
                            }
                        }
                    }
                }
                None => {}
            }
            // Collect provenance for non-basic variables' active bounds
            if provenance_ok {
                for (nb_var, coeff) in &row.coeffs {
                    let nb_info = &self.vars[*nb_var as usize];
                    if coeff.is_zero() {
                        continue;
                    }
                    let active_bound = match violated_bound {
                        Some(BoundType::Lower) => {
                            if coeff.is_positive() {
                                nb_info.upper.as_ref()
                            } else {
                                nb_info.lower.as_ref()
                            }
                        }
                        Some(BoundType::Upper) => {
                            if coeff.is_positive() {
                                nb_info.lower.as_ref()
                            } else {
                                nb_info.upper.as_ref()
                            }
                        }
                        None => None,
                    };
                    if let Some(bound) = active_bound {
                        if bound.reasons.is_empty() || bound.reasons.iter().all(|r| r.is_sentinel())
                        {
                            match Self::collect_reasons_from_provenance(bound) {
                                Some(prov_lits) => provenance_literals.extend(prov_lits),
                                None => {
                                    provenance_ok = false;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            // Merge provenance-derived literals with existing direct-reason literals
            if provenance_ok && !provenance_literals.is_empty() {
                let lit_count_before = literals.len() + provenance_literals.len();
                literals.extend(provenance_literals);
                // Re-deduplicate after merging provenance literals
                let (dedup_literals, _) = Self::deduplicate_conflict(literals, None);
                if !dedup_literals.is_empty() {
                    if self.debug_lra {
                        safe_eprintln!(
                            "[LRA] simplex conflict recovered via provenance: row={}, basic_var={}, literals={}",
                            row_idx,
                            row.basic_var,
                            dedup_literals.len()
                        );
                    }
                    if !self.conflict_literals_all_asserted(&dedup_literals) {
                        self.stats.stale_conflict_rejected_count += 1;
                        return TheoryConflict::new(vec![]);
                    }
                    return TheoryConflict::new(dedup_literals);
                }
                if self.debug_lra {
                    safe_eprintln!(
                        "[LRA] simplex conflict degraded: row={}, basic_var={}, reasonless=true, sentinel_only={}, pre_dedup_literals={}",
                        row_idx,
                        row.basic_var,
                        has_sentinel_only_bound,
                        lit_count_before
                    );
                }
            } else {
                if self.debug_lra {
                    safe_eprintln!(
                        "[LRA] simplex conflict degraded: row={}, basic_var={}, reasonless=true, sentinel_only={}, provenance_failed=true",
                        row_idx,
                        row.basic_var,
                        has_sentinel_only_bound,
                    );
                }
            }
            return TheoryConflict::new(vec![]);
        }

        // Sentinel-only bounds from axiom/definition sources are safe to omit
        // after fixing #4919: Gomory cuts and Diophantine bounds with empty
        // reasons are now skipped (gomory.rs, lia_support.rs), so remaining
        // sentinel-only bounds come only from initial variable domain setup
        // or theory definitions which hold unconditionally.
        //
        // If we collected no real literals at all, return empty conflict
        // (the entire infeasibility depends on axiom bounds).
        if has_sentinel_only_bound && literals.is_empty() {
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] simplex conflict degraded: row={}, basic_var={}, reasonless=false, sentinel_only=true, literals=0",
                    row_idx,
                    row.basic_var
                );
            }
            return TheoryConflict::new(vec![]);
        }

        // If we have some real literals + sentinel-only bounds, the clause
        // is valid but weaker (blocks a superset of assignments). Return
        // it without Farkas metadata since the certificate is incomplete.
        if has_sentinel_only_bound {
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] simplex conflict partial: row={}, basic_var={}, reasonless=false, sentinel_only=true, literals={}",
                    row_idx,
                    row.basic_var,
                    literals.len()
                );
            }
            let (dedup_literals, _) = Self::deduplicate_conflict(literals, None);
            if !self.conflict_literals_all_asserted(&dedup_literals) {
                self.stats.stale_conflict_rejected_count += 1;
                return TheoryConflict::new(vec![]);
            }
            return TheoryConflict::new(dedup_literals);
        }

        // At this point, all bounds have complete non-sentinel reasons.
        // Attach Farkas coefficients if all fit in Rational64.
        let farkas = coefficients
            .filter(|coeffs| !coeffs.is_empty())
            .map(FarkasAnnotation::new);

        // Deduplicate literals while combining Farkas coefficients (#938).
        // Same literal can appear multiple times if the same constraint is a reason
        // for multiple bounds (e.g., equality x=4 implies both x>=4 and x<=4).
        let (dedup_literals, dedup_coeffs) = Self::deduplicate_conflict(literals, farkas.as_ref());
        let dedup_farkas = if !dedup_coeffs.is_empty() {
            Some(FarkasAnnotation::new(dedup_coeffs))
        } else {
            farkas
        };

        if !self.conflict_literals_all_asserted(&dedup_literals) {
            self.stats.stale_conflict_rejected_count += 1;
            return TheoryConflict::new(vec![]);
        }
        match dedup_farkas {
            Some(f) => TheoryConflict::with_farkas(dedup_literals, f),
            None => TheoryConflict::new(dedup_literals),
        }
    }

    /// Retract active bounds of an infeasible row whose reason atoms are not
    /// currently asserted (own or cross-theory) (#A2 / conflict_without_literals).
    ///
    /// `build_conflict_with_farkas` returns an EMPTY conflict when the
    /// explanation would reference such bounds (the #8764 stale-reason guard
    /// rejects them). Two known producers:
    ///
    /// - NIA model-patch cuts (`ay_nia::patch::apply_patch` →
    ///   `add_gomory_cut`): the `[v, v]` patch bound is justified by the
    ///   monomial term itself (e.g. `(* x x)`, an Int-sorted term that is
    ///   never an asserted Boolean atom), so the conflict literal
    ///   `((* x x), true)` can never pass the asserted-literal guard.
    /// - bounds that survived a scope pop while their reason atoms were
    ///   retracted from `asserted` / `cross_theory_asserted`.
    ///
    /// Returning Unknown in that state livelocks the outer DPLL(T)/PDR loop:
    /// the identical infeasible tableau is re-queried thousands of times per
    /// run ("conflict_without_literals" 6-11k×, #A2). Instead, retract the
    /// unjustified bounds and let the dual simplex continue on the relaxed LP.
    ///
    /// SOUNDNESS: removing a bound only RELAXES the LP. Any later Unsat
    /// verdict is derived from the remaining (justified) bounds only, and any
    /// Sat model is re-validated downstream (NIA monomial consistency, #8373
    /// model validation), so retraction cannot introduce a wrong answer in
    /// either direction. Each retraction permanently removes one bound within
    /// the current scope (recorded on the trail for pop()), so the enclosing
    /// simplex loop terminates.
    ///
    /// Returns the number of bounds retracted.
    pub(crate) fn retract_unjustified_row_bounds(&mut self, row_idx: usize) -> usize {
        let row = &self.rows[row_idx];
        let basic_var = row.basic_var;
        let violated = self.violates_bounds(basic_var);

        // Candidates: the basic variable's violated bound plus each non-basic
        // variable's ACTIVE bound (the one blocking feasibility restoration,
        // same selection as build_conflict_with_farkas).
        let mut candidates: Vec<(u32, BoundType)> = Vec::new();
        match violated {
            Some(bt) => candidates.push((basic_var, bt)),
            None => return 0,
        }
        for (nb_var, coeff) in &row.coeffs {
            if coeff.is_zero() {
                continue;
            }
            let side = match violated {
                Some(BoundType::Lower) => {
                    if coeff.is_positive() {
                        BoundType::Upper
                    } else {
                        BoundType::Lower
                    }
                }
                Some(BoundType::Upper) => {
                    if coeff.is_positive() {
                        BoundType::Lower
                    } else {
                        BoundType::Upper
                    }
                }
                None => continue,
            };
            candidates.push((*nb_var, side));
        }

        let mut retracted = 0usize;
        for (var, side) in candidates {
            let vi = var as usize;
            if vi >= self.vars.len() {
                continue;
            }
            let bound = match side {
                BoundType::Lower => self.vars[vi].lower.as_ref(),
                BoundType::Upper => self.vars[vi].upper.as_ref(),
            };
            let Some(bound) = bound else { continue };

            // Bounds with no non-sentinel reasons are axiom/definition bounds
            // (hold unconditionally) — never retract those.
            let mut has_real_reason = false;
            let mut all_live = true;
            for (term, value) in bound.reason_pairs() {
                if term.is_sentinel() {
                    continue;
                }
                has_real_reason = true;
                let own_ok = self.asserted.get(&term) == Some(&value);
                let cross_ok = self.cross_theory_asserted.get(&term) == Some(&value);
                if !own_ok && !cross_ok {
                    all_live = false;
                    break;
                }
            }
            if !has_real_reason || all_live {
                continue;
            }

            // Retract, recording the old bound on the trail so scope pops
            // restore it exactly as for normal bound assertions.
            let old_bound = match side {
                BoundType::Lower => self.vars[vi].lower.take(),
                BoundType::Upper => self.vars[vi].upper.take(),
            };
            self.trail.push((var, side, old_bound));
            // Bound retracted -> LIA algebraic-detection memo is stale.
            self.bump_bound_revision();
            retracted += 1;
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] retracted unjustified {side:?} bound on var {var} (row {row_idx}): reason atoms not asserted",
                );
            }
        }

        if retracted > 0 {
            self.stats.unjustified_bound_retractions += retracted as u64;
            self.dirty = true;
            // Bound state changed since the implied-bounds overlay was built.
            self.direct_bounds_changed_since_implied = true;
            // The basic variable may have become feasible (its violated bound
            // was retracted) or may now admit a pivot — re-track it so the
            // error heap stays consistent.
            self.track_var_feasibility(basic_var);
        }
        retracted
    }

    /// Variable-level analogue of `retract_unjustified_row_bounds` for the
    /// non-basic repair path (#9061).
    ///
    /// When a non-basic variable's lower and upper bounds are mutually
    /// contradictory (empty feasible interval) but the early contradiction scan
    /// could not emit a sound conflict for it — because at least one offending
    /// bound's reason atoms are no longer asserted — the dual-simplex repair
    /// loop would otherwise oscillate the variable between its two bounds until
    /// `max_iters`, returning a spurious Unknown. Retract every such
    /// *unjustified* bound so the LP is relaxed and the simplex can continue.
    ///
    /// SOUNDNESS: identical to the row variant — retracting a bound only
    /// RELAXES the LP, so it cannot turn a genuinely-Sat state Unsat or vice
    /// versa; later Unsat verdicts rest on the remaining justified bounds and
    /// Sat models are re-validated downstream. Axiom/definition bounds
    /// (sentinel-only reasons) and fully-justified bounds are never touched.
    /// The retraction is recorded on the trail so scope pops restore it.
    ///
    /// Returns the number of bounds retracted.
    pub(crate) fn retract_unjustified_var_bounds(&mut self, var: u32) -> usize {
        let vi = var as usize;
        if vi >= self.vars.len() {
            return 0;
        }
        let mut retracted = 0usize;
        for side in [BoundType::Lower, BoundType::Upper] {
            let bound = match side {
                BoundType::Lower => self.vars[vi].lower.as_ref(),
                BoundType::Upper => self.vars[vi].upper.as_ref(),
            };
            let Some(bound) = bound else { continue };

            // Never retract axiom/definition bounds (no real reasons) or bounds
            // whose reason atoms are all currently asserted (justified).
            let mut has_real_reason = false;
            let mut all_live = true;
            for (term, value) in bound.reason_pairs() {
                if term.is_sentinel() {
                    continue;
                }
                has_real_reason = true;
                let own_ok = self.asserted.get(&term) == Some(&value);
                let cross_ok = self.cross_theory_asserted.get(&term) == Some(&value);
                if !own_ok && !cross_ok {
                    all_live = false;
                    break;
                }
            }
            if !has_real_reason || all_live {
                continue;
            }

            let old_bound = match side {
                BoundType::Lower => self.vars[vi].lower.take(),
                BoundType::Upper => self.vars[vi].upper.take(),
            };
            self.trail.push((var, side, old_bound));
            // Bound retracted -> LIA algebraic-detection memo is stale.
            self.bump_bound_revision();
            retracted += 1;
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] retracted unjustified {side:?} bound on non-basic var {var}: reason atoms not asserted",
                );
            }
        }

        if retracted > 0 {
            self.stats.unjustified_bound_retractions += retracted as u64;
            self.dirty = true;
            self.direct_bounds_changed_since_implied = true;
            self.track_var_feasibility(var);
        }
        retracted
    }

    /// Checked Rational64 addition using i128 intermediates to avoid overflow.
    /// Returns `None` when the result cannot fit in i64 numerator/denominator.
    fn checked_r64_add(
        a: num_rational::Rational64,
        b: num_rational::Rational64,
    ) -> Option<num_rational::Rational64> {
        let an = i128::from(*a.numer());
        let ad = i128::from(*a.denom());
        let bn = i128::from(*b.numer());
        let bd = i128::from(*b.denom());
        let num = an.checked_mul(bd)?.checked_add(bn.checked_mul(ad)?)?;
        let den = ad.checked_mul(bd)?;
        let num_i64 = i64::try_from(num).ok()?;
        let den_i64 = i64::try_from(den).ok()?;
        if den_i64 == 0 {
            return None;
        }
        Some(num_rational::Rational64::new(num_i64, den_i64))
    }

    /// Deduplicate conflict literals, combining Farkas coefficients for duplicates.
    ///
    /// Also removes contradictory pairs: if the same term appears with both
    /// `true` and `false` values, both occurrences are removed. Such pairs
    /// make the clause tautological (useless), and the fresh-solver verifier
    /// cannot handle them (assert_literal overwrites the first polarity with
    /// the second, causing a false SAT verdict). (#4666, #8123)
    pub(crate) fn deduplicate_conflict(
        literals: Vec<TheoryLit>,
        farkas: Option<&FarkasAnnotation>,
    ) -> (Vec<TheoryLit>, Vec<num_rational::Rational64>) {
        use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
        use num_rational::Rational64;

        if literals.is_empty() {
            return (literals, vec![]);
        }

        // First pass: identify terms that appear with both polarities.
        let mut contradictory_terms: HashSet<TermId> = HashSet::default();
        {
            let mut term_values: HashMap<TermId, bool> = HashMap::default();
            for lit in &literals {
                if let Some(&prev) = term_values.get(&lit.term) {
                    if prev != lit.value {
                        contradictory_terms.insert(lit.term);
                    }
                } else {
                    term_values.insert(lit.term, lit.value);
                }
            }
        }

        if farkas.is_none() {
            let mut seen: HashSet<(TermId, bool)> = HashSet::default();
            let mut dedup_literals = Vec::new();
            for lit in literals {
                // Skip contradictory-term literals entirely.
                if contradictory_terms.contains(&lit.term) {
                    continue;
                }
                if seen.insert((lit.term, lit.value)) {
                    dedup_literals.push(lit);
                }
            }
            return (dedup_literals, vec![]);
        }

        // Build map: (term, value) -> accumulated coefficient
        let mut seen: HashMap<(TermId, bool), Rational64> = HashMap::default();
        let mut order: Vec<(TermId, bool)> = Vec::new();
        let mut overflow = false;

        // Borrow coefficients directly — no clone needed (#6221 Finding 2).
        // farkas.is_none() case returns early above.
        let coeffs = match farkas {
            Some(f) => &f.coefficients,
            None => return (literals, vec![]),
        };

        for (lit, coeff) in literals.iter().zip(coeffs.iter()) {
            // Skip contradictory-term literals entirely.
            if contradictory_terms.contains(&lit.term) {
                continue;
            }
            let key = (lit.term, lit.value);
            if let Some(existing) = seen.get_mut(&key) {
                match Self::checked_r64_add(*existing, *coeff) {
                    Some(sum) => *existing = sum,
                    None => {
                        overflow = true;
                        break;
                    }
                }
            } else {
                seen.insert(key, *coeff);
                order.push(key);
            }
        }

        // On overflow, fall back to simple deduplication without Farkas coefficients.
        // The conflict clause is still valid; we just lose the proof annotation.
        if overflow {
            let mut seen_keys: HashSet<(TermId, bool)> = HashSet::default();
            let dedup_literals: Vec<_> = literals
                .into_iter()
                .filter(|lit| {
                    !contradictory_terms.contains(&lit.term)
                        && seen_keys.insert((lit.term, lit.value))
                })
                .collect();
            return (dedup_literals, vec![]);
        }

        let dedup_literals: Vec<_> = order
            .iter()
            .map(|(term, value)| TheoryLit::new(*term, *value))
            .collect();
        let dedup_coeffs: Vec<_> = order.iter().map(|key| seen[key]).collect();

        (dedup_literals, dedup_coeffs)
    }
}
