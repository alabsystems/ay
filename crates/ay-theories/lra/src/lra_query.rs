// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound queries, cross-sort propagation, and tableau row helpers for LRA.
//!
//! Public API for querying variable bounds, asserting cross-sort bounds,
//! propagating model equalities, and extracting tableau row information
//! for use by LIA's GCD and Diophantine tightening passes.
//!
//! Model extraction and value queries live in `lra_model.rs`.
//! Extracted from `lra_model.rs` to keep each file under 500 lines.

use super::*;

impl LraSolver {
    /// Whether an asserted atom semantically enforces equality.
    ///
    /// `=` asserted true means equality, while `distinct` asserted false also
    /// means equality.
    pub(crate) fn asserted_atom_is_equality(info: &ParsedAtomInfo, atom_value: bool) -> bool {
        (info.is_eq && atom_value) || (info.is_distinct && !atom_value)
    }

    /// Monotone revision counter for the variable-bound state.
    ///
    /// Changes whenever any variable bound may have changed (assert, pop,
    /// retraction, reset, snapshot import). Stamped by LIA's
    /// `detect_algebraic_equalities` memo: an equal revision guarantees every
    /// bound readable through [`Self::get_bounds`] is unchanged since the
    /// stamp was taken. See the field documentation for the bump sites.
    pub fn bound_revision(&self) -> u64 {
        self.bound_revision
    }

    /// Record that variable bounds may have changed (see `bound_revision`).
    #[inline]
    pub(crate) fn bump_bound_revision(&mut self) {
        self.bound_revision += 1;
    }

    /// Get the current lower/upper bounds for a variable term, if known.
    ///
    /// This is primarily used by LIA to detect immediate integer infeasibility
    /// from bounds (e.g. `x > 5` and `x < 6` with `x : Int`).
    pub fn get_bounds(&self, term: TermId) -> Option<(Option<Bound>, Option<Bound>)> {
        let &var = self.term_to_var.get(&term)?;
        let info = self.vars.get(var as usize)?;
        Some((info.lower.clone(), info.upper.clone()))
    }

    /// Borrow the current lower/upper bounds for a variable term (#C4).
    ///
    /// Allocation-free variant of [`Self::get_bounds`]: cloning a `Bound`
    /// copies its reason/scale vectors and provenance chain, which dominates
    /// LIA's per-BCP `check_integer_bounds_conflict` scan. The hot path only
    /// needs to *read* `value`/`strict` (and reasons on the rare conflict
    /// path), so it borrows instead.
    pub fn get_bounds_ref(&self, term: TermId) -> Option<(Option<&Bound>, Option<&Bound>)> {
        let &var = self.term_to_var.get(&term)?;
        let info = self.vars.get(var as usize)?;
        Some((info.lower.as_ref(), info.upper.as_ref()))
    }

    /// Check whether a term has implied bounds from the simplex tableau (#6198).
    ///
    /// Returns true if the variable has at least one implied bound (lower or upper)
    /// derived from tableau row analysis in `compute_implied_bounds()`. These bounds
    /// are transitive: if `x = y` and `y >= 0`, then `x` has an implied lower bound
    /// of 0 even though no direct bound on `x` was asserted.
    ///
    /// Used by AUFLIRA cross-sort propagation to detect when a split should be
    /// requested even though direct bounds are absent.
    pub fn has_implied_bounds(&self, term: TermId) -> bool {
        let Some(&var) = self.term_to_var.get(&term) else {
            return false;
        };
        let vi = var as usize;
        if vi >= self.implied_bounds.len() {
            return false;
        }
        let (ref lb, ref ub) = self.implied_bounds[vi];
        lb.is_some() || ub.is_some()
    }

    /// Assert that a variable has a tight (fixed) value (#4915).
    ///
    /// Used by LIRA cross-sort value propagation: when LIA determines x = c,
    /// this asserts both `x <= c` and `x >= c` in LRA so that shared variables
    /// (via `to_real(x)`) pick up the integer constraint.
    ///
    /// SOUNDNESS: only call this when `reasons` actually justify `x = value`
    /// (i.e., tight bounds: lower == upper == value). For non-tight bounds,
    /// use `assert_cross_sort_bounds` instead (#5947 soundness fix).
    pub fn assert_tight_bound(&mut self, term: TermId, value: &BigRational, reasons: &[TheoryLit]) {
        let expr = self.parse_linear_expr(term);
        let reason_pairs: Vec<(TermId, bool)> = reasons.iter().map(|r| (r.term, r.value)).collect();
        self.record_cross_theory_reasons(&reason_pairs);
        // #8406: Convert BigRational to Rational at the public API boundary.
        let rat_value = Rational::from_big(value.clone());
        self.assert_bound_with_reasons(
            expr.clone(),
            rat_value.clone(),
            BoundType::Upper,
            false,
            &reason_pairs,
            None,
        );
        self.assert_bound_with_reasons(
            expr,
            rat_value,
            BoundType::Lower,
            false,
            &reason_pairs,
            None,
        );
        self.dirty = true;
    }

    /// Assert individual lower/upper bounds from LIA to LRA (#5947 soundness fix).
    ///
    /// Unlike `assert_tight_bound` which asserts `x = value`, this propagates
    /// only the bounds that LIA actually has, with each bound's own reasons.
    /// This ensures conflict clauses are sound: the reasons for a lower bound
    /// justify only `x >= l`, not `x = v`.
    pub fn assert_cross_sort_bounds(
        &mut self,
        term: TermId,
        lower: Option<&Bound>,
        upper: Option<&Bound>,
    ) {
        let expr = self.parse_linear_expr(term);
        if let Some(lb) = lower {
            let reason_pairs: Vec<(TermId, bool)> = lb.reason_pairs().collect();
            self.record_cross_theory_reasons(&reason_pairs);
            // #8406: Bound.value is already Rational, clone directly.
            self.assert_bound_with_reasons(
                expr.clone(),
                lb.value.clone(),
                BoundType::Lower,
                lb.strict,
                &reason_pairs,
                None,
            );
        }
        if let Some(ub) = upper {
            let reason_pairs: Vec<(TermId, bool)> = ub.reason_pairs().collect();
            self.record_cross_theory_reasons(&reason_pairs);
            // #8406: Bound.value is already Rational, clone directly.
            self.assert_bound_with_reasons(
                expr,
                ub.value.clone(),
                BoundType::Upper,
                ub.strict,
                &reason_pairs,
                None,
            );
        }
        self.dirty = true;
    }

    /// Get the mapping from term IDs to internal variable IDs
    ///
    /// Used by LIA for HNF cut generation to translate between
    /// term-level and internal variable representations.
    pub fn term_to_var(&self) -> &HashMap<TermId, u32> {
        &self.term_to_var
    }

    /// True iff any variable currently carries a STRICT bound (`<` / `>`).
    ///
    /// Standalone-simplex callers use this to classify an
    /// [`crate::OptimizationResult::Optimal`] outcome (#opt-epsilon): with no
    /// strict bound in the tableau the attained-optimum lane is the long-proven
    /// closed-polyhedron path; with a strict bound present the caller must
    /// additionally prove maximality (verified dual certificate or a full-solver
    /// `obj > v` UNSAT twin) before publishing, because the attainability
    /// confirmation alone is one-sided.
    pub fn has_strict_var_bound(&self) -> bool {
        self.vars.iter().any(|var| {
            var.lower.as_ref().is_some_and(|bound| bound.strict)
                || var.upper.as_ref().is_some_and(|bound| bound.strict)
        })
    }

    /// Returns the registered `to_int(x)` terms: `(to_int_var_id, inner_arg_term)`.
    /// Used by the LIRA adapter to patch model values at extraction time.
    pub fn to_int_terms(&self) -> &[(u32, TermId)] {
        &self.to_int_terms
    }

    /// Propagate patched model values through asserted equality-semantic atoms
    /// (#6227, #7654 follow-up).
    ///
    /// After externally patching some LRA model values (e.g., from LIRA adapter
    /// copying LIA values for shared Int-sorted variables), scan asserted atoms
    /// that semantically enforce equality (`=` asserted true, `distinct`
    /// asserted false) to find Real-sorted variables constrained equal to
    /// patched variables. For each such equality, compute the correct value
    /// from the equality equation.
    ///
    /// This avoids the false-positive risk of value-based matching: only variables
    /// structurally connected through an asserted equality-semantic atom are
    /// updated, and propagation continues transitively through equality chains.
    pub fn propagate_model_equalities(&self, model: &mut LraModel, patched_var_ids: &HashSet<u32>) {
        if patched_var_ids.is_empty() {
            return;
        }

        let mut frontier = patched_var_ids.clone();
        let mut propagated = patched_var_ids.clone();

        while !frontier.is_empty() {
            let mut next_frontier: HashSet<u32> = HashSet::default();

            for (&atom_term, &atom_value) in &self.asserted {
                let Some(Some(info)) = self.atom_cache.get(&atom_term) else {
                    continue;
                };
                if !Self::asserted_atom_is_equality(info, atom_value) {
                    continue;
                }

                let coeffs = &info.expr.coeffs;
                if coeffs.len() != 2 {
                    continue;
                }

                let (v0, c0) = (coeffs[0].0, &coeffs[0].1);
                let (v1, c1) = (coeffs[1].0, &coeffs[1].1);
                let (patched_v, other_v, patched_c, other_c) =
                    if frontier.contains(&v0) && !propagated.contains(&v1) {
                        (v0, v1, c0, c1)
                    } else if frontier.contains(&v1) && !propagated.contains(&v0) {
                        (v1, v0, c1, c0)
                    } else {
                        continue;
                    };

                if other_c.is_zero() {
                    continue;
                }

                // Equality: c_patched * patched_v + c_other * other_v + constant = 0
                // => other_v = -(c_patched * patched_value + constant) / c_other
                let Some(patched_term) = self.var_term_id(patched_v) else {
                    continue;
                };
                let Some(other_term) = self.var_term_id(other_v) else {
                    continue;
                };
                let Some(patched_val) = model.values.get(&patched_term) else {
                    continue;
                };

                let numer = patched_c.mul_bigrational(patched_val) + info.expr.constant.to_big();
                let other_val = -numer / other_c.to_big();
                if self.debug_lra {
                    safe_eprintln!(
                        "[LRA] propagate_model_equalities: term {} (var {}) = {}",
                        other_term.0,
                        other_v,
                        other_val
                    );
                }
                model.values.insert(other_term, other_val);
                propagated.insert(other_v);
                next_frontier.insert(other_v);
            }

            frontier = next_frontier;
        }
    }

    /// Get the status (basic/non-basic) of an internal variable.
    ///
    /// Returns `None` if the variable ID is out of range.
    pub fn get_var_status(&self, var_id: u32) -> Option<VarStatus> {
        self.vars.get(var_id as usize).and_then(|info| info.status)
    }

    /// Get rows with fractional integer basic variables for GCD testing.
    ///
    /// Returns row information for each tableau row where:
    /// 1. The basic variable is an integer variable
    /// 2. The current value of the basic variable is non-integer
    ///
    /// This is used by the LIA solver to perform extended GCD tests that can
    /// detect integer infeasibility before expensive branch-and-bound.
    pub fn get_fractional_int_rows(&self, integer_vars: &HashSet<TermId>) -> Vec<GcdRowInfo> {
        let mut rows = Vec::new();

        for row in &self.rows {
            let basic_var = row.basic_var;

            // Check if this basic variable corresponds to an integer variable
            let basic_term = self.var_to_term.get(&basic_var).copied();
            let is_int_basic = basic_term.is_some_and(|t| integer_vars.contains(&t));

            if !is_int_basic {
                continue;
            }

            let basic_info = &self.vars[basic_var as usize];

            // Check if fractional
            if basic_info.value.rational().denom().is_one() {
                continue; // Already integer
            }

            // Extract bound information
            let lower_bound = basic_info.lower.as_ref().map(Bound::value_big);
            let upper_bound = basic_info.upper.as_ref().map(Bound::value_big);
            let is_fixed =
                lower_bound.is_some() && upper_bound.is_some() && lower_bound == upper_bound;
            let is_bounded = lower_bound.is_some() && upper_bound.is_some();

            rows.push(GcdRowInfo {
                basic_var,
                basic_term,
                coeffs: row.coeffs.iter().map(|(v, c)| (*v, c.to_big())).collect(),
                constant: row.constant.to_big(),
                lower_bound,
                upper_bound,
                is_fixed,
                is_bounded,
            });
        }

        rows
    }

    /// Check if an internal variable is an integer variable
    pub fn is_int_var(&self, var: u32, integer_vars: &HashSet<TermId>) -> bool {
        self.var_to_term
            .get(&var)
            .is_some_and(|t| integer_vars.contains(t))
    }

    /// Get the bounds for an internal variable
    pub fn get_var_bounds(&self, var: u32) -> Option<(Option<BigRational>, Option<BigRational>)> {
        let info = self.vars.get(var as usize)?;
        Some((
            info.lower.as_ref().map(Bound::value_big),
            info.upper.as_ref().map(Bound::value_big),
        ))
    }

    /// Get the full bound objects (with reason atoms) for an internal variable.
    ///
    /// Var-keyed companion to [`Self::get_bounds`]. Slack variables introduced
    /// for compound linear expressions have no `term_to_var` entry, so
    /// term-keyed bound lookups cannot reach them. The LIA tableau GCD
    /// conflict collector must name the reason atoms of FIXED slack variables
    /// (e.g. equality-asserted compound sums folded into the row constant);
    /// dropping them produced an under-sized, theory-invalid conflict clause
    /// and a false UNSAT (fuzzer seed 3167).
    pub fn var_bounds_with_reasons(&self, var: u32) -> Option<(Option<&Bound>, Option<&Bound>)> {
        let info = self.vars.get(var as usize)?;
        Some((info.lower.as_ref(), info.upper.as_ref()))
    }

    /// Ensure a variable is registered with the LRA solver.
    ///
    /// This is called by the LIA solver when propagating Diophantine bounds
    /// for integer variables that may not have been encountered in LRA constraints.
    /// Returns the internal variable ID.
    pub fn ensure_var_registered(&mut self, term: TermId) -> u32 {
        self.intern_var(term)
    }

    /// Map an internal variable ID to its TermId, if known.
    pub fn var_term_id(&self, var: u32) -> Option<TermId> {
        self.var_to_term.get(&var).copied()
    }

    /// Get ALL tableau rows where the basic variable is an integer with at
    /// least one bound.  Used by the LIA Diophantine tightening pass, which
    /// needs rows regardless of whether the current assignment is fractional.
    ///
    /// Reference: Z3 `dioph_eq.cpp` `tighten_terms_with_S()` iterates over
    /// all bounded term columns, not just fractional ones.
    pub fn get_bounded_integer_rows(&self, integer_vars: &HashSet<TermId>) -> Vec<GcdRowInfo> {
        let mut rows = Vec::new();

        for row in &self.rows {
            let basic_var = row.basic_var;

            let basic_term = self.var_to_term.get(&basic_var).copied();
            let is_int_basic = basic_term.is_some_and(|t| integer_vars.contains(&t));

            if !is_int_basic {
                continue;
            }

            let basic_info = &self.vars[basic_var as usize];

            let lower_bound = basic_info.lower.as_ref().map(Bound::value_big);
            let upper_bound = basic_info.upper.as_ref().map(Bound::value_big);

            // Skip unbounded rows — no tightening possible
            if lower_bound.is_none() && upper_bound.is_none() {
                continue;
            }

            let is_fixed =
                lower_bound.is_some() && upper_bound.is_some() && lower_bound == upper_bound;
            let is_bounded = lower_bound.is_some() && upper_bound.is_some();

            rows.push(GcdRowInfo {
                basic_var,
                basic_term,
                coeffs: row.coeffs.iter().map(|(v, c)| (*v, c.to_big())).collect(),
                constant: row.constant.to_big(),
                lower_bound,
                upper_bound,
                is_fixed,
                is_bounded,
            });
        }

        rows
    }

    /// Retention gate for derived bounds entering `implied_bounds`.
    ///
    /// Returns true when a bound should be stored for downstream consumers:
    /// - Boolean atom propagation (same-direction unassigned atom implied)
    /// - Cross-row cascading (enables other rows to derive further bounds)
    /// - Cross-solver queries (`has_implied_bounds()` used by AUFLIRA)
    ///
    /// Returns false only when there IS a same-direction unassigned atom and
    /// the derived bound fails to imply any of them. (#6697)
    ///
    /// Based on Z3's `bound_is_interesting` (theory_lra.cpp:2352-2367), but
    /// broadened because AY's `implied_bounds` serves multiple consumers beyond
    /// SAT-facing propagation. Reference: #6615, #6697.
    pub(crate) fn bound_is_interesting(&self, var: u32, is_upper: bool, value: &Rational) -> bool {
        let Some(atoms) = self.atom_index.get(&var) else {
            return true;
        };
        if atoms.is_empty() {
            return true;
        }
        let mut any_same_direction_unassigned = false;
        for atom in atoms {
            if self.asserted.contains_key(&atom.term) {
                continue;
            }
            if is_upper && atom.is_upper {
                // Same direction: upper bound implies upper atom (true)
                any_same_direction_unassigned = true;
                let cmp = value.cmp(&atom.bound_value);
                let implies = if atom.strict {
                    cmp.is_lt()
                } else {
                    cmp.is_le()
                };
                if implies {
                    return true;
                }
            } else if !is_upper && !atom.is_upper {
                // Same direction: lower bound implies lower atom (true)
                any_same_direction_unassigned = true;
                let cmp = value.cmp(&atom.bound_value);
                let implies = if atom.strict {
                    cmp.is_gt()
                } else {
                    cmp.is_ge()
                };
                if implies {
                    return true;
                }
            } else if is_upper && !atom.is_upper {
                // #8422: Opposite direction: upper bound falsifies lower atom.
                // Upper bound x <= value falsifies x >= k when value < k,
                // or x > k when value <= k.
                // Z3's propagate_lp_solver_bound checks both directions
                // (is_bound_implied handles LE+lower and GE+upper cases).
                // Without this, bound_is_interesting filters bounds that
                // could falsify opposite-direction atoms, blocking those
                // propagations entirely.
                let cmp = value.cmp(&atom.bound_value);
                let falsifies = if atom.strict {
                    // Atom: x > k. False if ub(x) <= k.
                    cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                } else {
                    // Atom: x >= k. False if ub(x) < k, or ub(x) == k and strict.
                    cmp == std::cmp::Ordering::Less
                };
                if falsifies {
                    return true;
                }
            } else if !is_upper && atom.is_upper {
                // #8422: Opposite direction: lower bound falsifies upper atom.
                // Lower bound x >= value falsifies x <= k when value > k,
                // or x < k when value >= k.
                let cmp = value.cmp(&atom.bound_value);
                let falsifies = if atom.strict {
                    // Atom: x < k. False if lb(x) >= k.
                    cmp == std::cmp::Ordering::Greater || cmp == std::cmp::Ordering::Equal
                } else {
                    // Atom: x <= k. False if lb(x) > k, or lb(x) == k and strict.
                    cmp == std::cmp::Ordering::Greater
                };
                if falsifies {
                    return true;
                }
            }
        }
        !any_same_direction_unassigned
    }
}
