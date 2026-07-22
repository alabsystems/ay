// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-sort value and bound propagation between LIA and LRA.
//!
//! When `to_real(x)` appears in a Real constraint, LRA shares the same TermId
//! for `x` as LIA. After LIA determines a tight bound (e.g., `x = 1`), this
//! value must be forwarded to LRA so it can detect conflicts with Real
//! constraints on the same variable.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{SplitRequest, TermId, TheoryLit, TheoryResult};
use ay_lra::Bound;
use num_bigint::BigInt;
use num_rational::BigRational;

use super::{CrossSortTrailEntry, LiraSolver, PropagationKind};

impl LiraSolver<'_> {
    fn integer_lower_bound(bound: &Bound) -> BigInt {
        if bound.strict {
            bound.value.floor() + BigInt::from(1)
        } else {
            bound.value.ceil()
        }
    }

    fn integer_upper_bound(bound: &Bound) -> BigInt {
        if bound.strict {
            bound.value.ceil() - BigInt::from(1)
        } else {
            bound.value.floor()
        }
    }

    fn collect_bound_reasons(lower: &Bound, upper: &Bound) -> Vec<TheoryLit> {
        let mut reasons = Vec::new();
        for (term, val) in lower.reason_pairs() {
            if !term.is_sentinel() {
                reasons.push(TheoryLit::new(term, val));
            }
        }
        for (term, val) in upper.reason_pairs() {
            if !term.is_sentinel() && !reasons.iter().any(|r| r.term == term) {
                reasons.push(TheoryLit::new(term, val));
            }
        }
        reasons
    }

    fn exact_integer_reasons(
        value: &BigInt,
        lower: Option<&Bound>,
        upper: Option<&Bound>,
    ) -> Option<Vec<TheoryLit>> {
        let (lower, upper) = (lower?, upper?);
        let min_value = Self::integer_lower_bound(lower);
        let max_value = Self::integer_upper_bound(upper);
        if min_value != *value || max_value != *value {
            return None;
        }
        let reasons = Self::collect_bound_reasons(lower, upper);
        if reasons.is_empty() {
            None
        } else {
            Some(reasons)
        }
    }

    fn floor_lower_bound(bound: &Bound) -> BigInt {
        bound.value.floor()
    }

    fn floor_upper_bound(bound: &Bound) -> BigInt {
        if bound.strict && bound.value.is_integer() {
            bound.value.floor() - BigInt::from(1)
        } else {
            bound.value.floor()
        }
    }

    fn exact_floor_reasons(
        lower: Option<&Bound>,
        upper: Option<&Bound>,
    ) -> Option<(BigRational, Vec<TheoryLit>)> {
        let (lower, upper) = (lower?, upper?);
        let min_floor = Self::floor_lower_bound(lower);
        let max_floor = Self::floor_upper_bound(upper);
        if min_floor != max_floor {
            return None;
        }
        let reasons = Self::collect_bound_reasons(lower, upper);
        if reasons.is_empty() {
            None
        } else {
            Some((BigRational::from(min_floor), reasons))
        }
    }

    fn choose_cross_sort_split_value(
        lower: Option<&Bound>,
        upper: Option<&Bound>,
        fallback_value: &BigRational,
    ) -> BigRational {
        if let (Some(lower), Some(upper)) = (lower, upper) {
            let lo = Self::integer_lower_bound(lower);
            let hi = Self::integer_upper_bound(upper);
            if lo < hi {
                let midpoint = (BigRational::from(lo) + BigRational::from(hi))
                    / BigRational::from(BigInt::from(2));
                if midpoint.is_integer() {
                    return midpoint + BigRational::new(BigInt::from(1), BigInt::from(2));
                }
                return midpoint;
            }
        }

        fallback_value + BigRational::new(BigInt::from(1), BigInt::from(2))
    }

    /// Propagate LIA integer values to LRA for shared variables (#4915, #5947).
    ///
    /// Returns `(propagation_count, optional_split_request)`.
    ///
    /// For each shared variable:
    /// - **Tight bounds** (lower == upper): propagate `x = value` with bound reasons (sound).
    /// - **Non-tight bounds**: propagate individual bounds to LRA (sound) AND
    ///   request a split so that branch-and-bound establishes tight bounds.
    ///   This avoids asserting `x = v` with reasons that only justify `l <= x <= u`,
    ///   which creates unsound conflict clauses (#5947 soundness fix).
    pub(super) fn propagate_cross_sort_values(
        &mut self,
        debug: bool,
    ) -> (usize, Option<TheoryResult>) {
        let lia_lra = self.lia.lra_solver();
        let lra_vars = self.lra.term_to_var();
        let to_int_term_ids: HashSet<TermId> = self
            .lra
            .to_int_terms()
            .iter()
            .filter_map(|(to_int_var, _)| self.lra.var_term_id(*to_int_var))
            .collect();
        // #6217: When to_int terms exist, their values are propagated by
        // propagate_to_int_values which handles the floor axiom correctly.
        // Cross-sort splits on variables related to to_int equations never
        // converge because the DPLL solver can't find a stable assignment.
        // Suppress cross-sort splits when to_int terms are present.
        let has_to_int = !self.lra.to_int_terms().is_empty();

        let mut to_propagate: Vec<(TermId, BigRational, Vec<TheoryLit>)> = Vec::new();
        let mut to_propagate_bounds: Vec<(TermId, Option<Bound>, Option<Bound>)> = Vec::new();
        let mut need_split: Option<TheoryResult> = None;

        for (&term, _) in lia_lra.term_to_var() {
            // #6217: Only propagate cross-sort values for Int-sorted terms.
            // Real-sorted terms (e.g., the argument x in to_int(x)) appear in
            // both LIA's internal LRA and the main LRA but are not cross-sort
            // variables. Propagating their values and requesting integer-style
            // floor/ceil splits creates artificial gaps (e.g., x<=2 OR x>=3)
            // that exclude valid Real values like 2.5, causing false UNSAT.
            // Matches AUFLIRA adapter behavior (auf_lira.rs:286-288).
            if !matches!(self.terms.sort(term), ay_core::Sort::Int) {
                continue;
            }
            // #8790: `(to_int x)` is represented in LIA's internal LRA with
            // auxiliary floor rows; its simplex value can be a slack value, not
            // the integer term value. The main LRA already owns the floor
            // axiom, so only `propagate_to_int_values` may bridge it.
            if to_int_term_ids.contains(&term) {
                continue;
            }
            // `term_to_var()` is populated during `register_atom()`, so it contains
            // registration artifacts for Int-only literals. Only propagate terms
            // that also appeared in a literal actually asserted to the Real side.
            if !self.asserted_real_int_terms.contains(&term) || !lra_vars.contains_key(&term) {
                continue;
            }
            if let Some((value, reasons)) = lia_lra.get_value_with_reasons(term) {
                if !value.is_integer() {
                    continue;
                }
                let bounds = lia_lra.get_bounds(term);
                let key = value.to_integer();
                let tight_reasons = if reasons.is_empty() {
                    bounds.as_ref().and_then(|(lower, upper)| {
                        Self::exact_integer_reasons(&key, lower.as_ref(), upper.as_ref())
                    })
                } else {
                    Some(reasons.clone())
                };
                let wants_tight = tight_reasons.is_some();
                let new_kind = if wants_tight {
                    PropagationKind::Tight
                } else {
                    // Fingerprint the bounds that would be forwarded so that a
                    // tightened (but still non-tight) bound set is re-forwarded
                    // instead of deduplicated away (#to-real-only-int-integrality).
                    let (lower, upper) = match &bounds {
                        Some((lo, up)) => (
                            lo.as_ref().map(|b| (b.value.clone(), b.strict)),
                            up.as_ref().map(|b| (b.value.clone(), b.strict)),
                        ),
                        None => (None, None),
                    };
                    PropagationKind::Bounds { lower, upper }
                };
                let prev_kind = self
                    .propagated_cross_sort
                    .get(&(term, key.clone()))
                    .cloned();
                match &prev_kind {
                    Some(PropagationKind::Tight) => continue,
                    Some(prev @ PropagationKind::Bounds { .. })
                        if !wants_tight && *prev == new_kind =>
                    {
                        continue;
                    }
                    _ => {}
                }
                self.propagated_cross_sort
                    .insert((term, key.clone()), new_kind);
                self.cross_sort_trail.push(CrossSortTrailEntry::Propagated(
                    term,
                    key.clone(),
                    prev_kind,
                ));
                if let Some(tight_reasons) = tight_reasons {
                    to_propagate.push((term, value, tight_reasons));
                } else {
                    // #5947 soundness fix: bounds not tight from SAT atoms.
                    // Propagate individual bounds and request a split.
                    if let Some((lower, upper)) = bounds {
                        if lower.is_none() && upper.is_none() {
                            // #6198: No direct bounds, but implied bounds through
                            // the simplex tableau may exist. Request a split so
                            // the DPLL solver explores the value.
                            if !has_to_int
                                && lia_lra.has_implied_bounds(term)
                                && need_split.is_none()
                            {
                                need_split = Some(Self::make_cross_sort_split(
                                    term,
                                    Self::choose_cross_sort_split_value(None, None, &value),
                                    debug,
                                ));
                            }
                            continue;
                        }
                        // #8747: When both bounds already pin the integer value
                        // exactly (integer lower == integer upper == key), the
                        // effective interval is a singleton and no further split
                        // can refine it. Requesting a split here produces split
                        // points outside [lower, upper] (e.g., value + 1/2),
                        // which DPLL cannot act on, causing an infinite loop.
                        // The bounds-only forward (assert_cross_sort_bounds)
                        // already propagates the constraint to LRA.
                        let interval_is_singleton = match (lower.as_ref(), upper.as_ref()) {
                            (Some(lo_b), Some(up_b)) => {
                                Self::integer_lower_bound(lo_b) == key
                                    && Self::integer_upper_bound(up_b) == key
                            }
                            _ => false,
                        };
                        let split_value = Self::choose_cross_sort_split_value(
                            lower.as_ref(),
                            upper.as_ref(),
                            &value,
                        );
                        // #to-real-integrality-drift: a shared Int variable bounded
                        // on ONE side only (e.g. `x >= 0`, no upper bound) whose Real
                        // side is unbounded in the open direction (`to_real(x) < y`
                        // with `y` free above) drives an infinite branch-and-bound
                        // drift: the default split always prefers the `ceil` branch
                        // (`make_cross_sort_split` sets `value` so its fractional part
                        // is 1.0), which never conflicts, so `x` climbs 0,1,2,… until
                        // the split cap degrades a genuine SAT to `unknown`. LIA has
                        // already pinned `x` at its bound (`key`), so prefer the branch
                        // that pins `x = key` AGAINST that bound: `x <= key` for a
                        // lower-only bound, `x >= key` for an upper-only bound. Both
                        // arms still exist (sound, terminating); only the exploration
                        // order changes, so bounded problems are unaffected.
                        let one_sided_lower = lower.is_some() && upper.is_none();
                        let one_sided_upper = upper.is_some() && lower.is_none();
                        to_propagate_bounds.push((term, lower, upper));
                        if !has_to_int && !interval_is_singleton && need_split.is_none() {
                            need_split = Some(if one_sided_lower {
                                Self::make_pinning_split(term, key.clone(), false, debug)
                            } else if one_sided_upper {
                                Self::make_pinning_split(term, key.clone(), true, debug)
                            } else {
                                Self::make_cross_sort_split(term, split_value, debug)
                            });
                        }
                    }
                }
            }
        }

        let count = to_propagate.len() + to_propagate_bounds.len();
        self.apply_cross_sort_propagations(to_propagate, to_propagate_bounds, debug);
        (count, need_split)
    }

    /// Apply collected cross-sort propagations to LRA.
    fn apply_cross_sort_propagations(
        &mut self,
        tight: Vec<(TermId, BigRational, Vec<TheoryLit>)>,
        bounds: Vec<(TermId, Option<Bound>, Option<Bound>)>,
        debug: bool,
    ) {
        for (term, value, reasons) in tight {
            if debug {
                safe_eprintln!(
                    "[N-O LIRA] Cross-sort value: term {:?} = {} ({} reasons)",
                    term,
                    value,
                    reasons.len()
                );
            }
            self.lra.assert_tight_bound(term, &value, &reasons);
        }
        for (term, lower, upper) in bounds {
            if debug {
                safe_eprintln!(
                    "[N-O LIRA] Cross-sort bounds: term {:?} lower={} upper={}",
                    term,
                    lower.is_some(),
                    upper.is_some()
                );
            }
            self.lra
                .assert_cross_sort_bounds(term, lower.as_ref(), upper.as_ref());
        }
    }

    /// Build a *pinning* branch-and-bound split for a one-sided-bounded shared
    /// Int variable whose LIA value `v` sits at its only bound
    /// (#to-real-integrality-drift).
    ///
    /// The split partitions the integers at `v` and picks the branch that pins
    /// `x = v` against the existing bound:
    /// - `prefer_ceil == false` (lower-only bound): `x <= v` OR `x >= v+1`,
    ///   preferring `x <= v` — combined with `x >= v` this pins `x = v`.
    /// - `prefer_ceil == true` (upper-only bound): `x <= v-1` OR `x >= v`,
    ///   preferring `x >= v` — combined with `x <= v` this pins `x = v`.
    ///
    /// The `value` field is set so `create_int_split_atoms` derives the intended
    /// `prefer_ceil` (its `frac = value - floor`). Both arms are always present,
    /// so this is a sound, terminating case split; only the exploration order
    /// differs from the default, which averts the unbounded drift that occurs
    /// when the Real side is open in the variable's unbounded direction.
    fn make_pinning_split(term: TermId, v: BigInt, prefer_ceil: bool, debug: bool) -> TheoryResult {
        let (floor, ceil) = if prefer_ceil {
            // Upper-only bound: floor = v-1 makes frac = v-(v-1) = 1 > 1/2.
            (v.clone() - BigInt::from(1), v.clone())
        } else {
            // Lower-only bound: floor = v makes frac = 0 < 1/2.
            (v.clone(), v.clone() + BigInt::from(1))
        };
        if debug {
            safe_eprintln!(
                "[N-O LIRA] Pinning split on shared var {:?} at {} (prefer {})",
                term,
                v,
                if prefer_ceil { "ceil" } else { "floor" }
            );
        }
        TheoryResult::NeedSplit(SplitRequest {
            variable: term,
            value: BigRational::from(v),
            floor,
            ceil,
        })
    }

    /// Request a split for an Int-sorted term that LRA holds at a
    /// non-integral value at fixpoint (#to-real-only-int-integrality).
    ///
    /// An Int variable that occurs ONLY under `to_real` in Real literals
    /// never appears in any Int-side literal, so it never registers with
    /// LIA and `propagate_cross_sort_values` (which iterates LIA's
    /// `term_to_var`) never sees it. LRA is then free to pin the shared
    /// TermId to a non-integral value (e.g. `(= (to_real xi) (/ 7 2))`
    /// pins `xi = 7/2`), and the fixpoint would return an invalid SAT
    /// that the model-validation gate degrades to `unknown`.
    ///
    /// Scanning `asserted_real_int_terms` (Int-sorted terms occurring in
    /// literals actually asserted to the Real side) closes the gap: any
    /// such term with a non-integral LRA value gets a branch-and-bound
    /// split `x <= floor(v) OR x >= ceil(v)`, so DPLL either integralizes
    /// the variable or flips the offending Real literal. The split atoms
    /// are Int-sorted, so they route to LIA and register the variable
    /// there, after which the ordinary cross-sort machinery takes over.
    ///
    /// Suppressed while `to_int` terms exist, matching #6217: splits on
    /// variables related to `to_int` equations do not converge, and
    /// `propagate_to_int_values` owns that bridging.
    pub(super) fn non_integral_int_value_split(&self, debug: bool) -> Option<TheoryResult> {
        // #to-real-bridge soundness: an Int-sorted term reaches a Real literal
        // only through `to_real`, and this integrality split is premised on
        // that coercion pinning the Int variable's Real value. When a user
        // declaration shadows the builtin `to_real`, its applications are
        // uninterpreted (the ay-core rewrites already stand down on the shadow
        // flag), so `(to_real n)` no longer denotes `n` — forcing `n` integral
        // here would fabricate `unsat` for a satisfiable free-function instance.
        // Stand down in lockstep with the constructor rewrites (fail-closed).
        if self.terms.to_real_is_shadowed() {
            return None;
        }
        if !self.lra.to_int_terms().is_empty() {
            return None;
        }
        for &term in self.asserted_real_int_terms.iter() {
            // `asserted_real_int_terms` only holds non-constant Int-sorted
            // terms; `get_value` is None unless LRA actually tracks the term.
            let Some(value) = self.lra.get_value(term) else {
                continue;
            };
            if value.is_integer() {
                continue;
            }
            // Pass floor(v) so the split brackets v itself:
            // floor = floor(v), ceil = floor(v) + 1. (`make_cross_sort_split`
            // truncates toward zero via `to_integer`, which would mis-bracket
            // negative values like -7/2.)
            return Some(Self::make_cross_sort_split(term, value.floor(), debug));
        }
        None
    }

    /// Build a split request for a non-tight shared variable (#5947).
    fn make_cross_sort_split(term: TermId, value: BigRational, debug: bool) -> TheoryResult {
        let int_val = value.to_integer();
        let half = BigRational::new(1.into(), 2.into());
        let split_point = value + &half;
        if debug {
            safe_eprintln!(
                "[N-O LIRA] Requesting split on shared var {:?} at {}",
                term,
                split_point
            );
        }
        TheoryResult::NeedSplit(SplitRequest {
            variable: term,
            value: split_point,
            floor: int_val.clone(),
            ceil: int_val + BigInt::from(1),
        })
    }

    /// Propagate `to_int(x)` values from LRA to LIA (#5944).
    ///
    /// After LRA computes x's value, floor(x) is the correct value for to_int(x).
    /// Assert to_int(x) = floor(x) as tight bounds in LIA's internal LRA solver
    /// so LIA can propagate it through equalities like `y = to_int(x)`.
    pub(super) fn propagate_to_int_values(&mut self, debug: bool) -> usize {
        let to_int_terms = self.lra.to_int_terms().to_vec();
        if to_int_terms.is_empty() {
            return 0;
        }

        let var_to_term: HashMap<u32, TermId> = self
            .lra
            .term_to_var()
            .iter()
            .map(|(&t, &v)| (v, t))
            .collect();

        let lia_lra_vars = self.lia.lra_solver().term_to_var().clone();
        let mut count = 0;

        for (to_int_var, inner_arg_term) in to_int_terms {
            let Some(&to_int_term) = var_to_term.get(&to_int_var) else {
                continue;
            };
            // Only propagate if LIA knows about this to_int variable
            if !lia_lra_vars.contains_key(&to_int_term) {
                continue;
            }
            // #5944/#6217/#8790: Propagate `to_int(x)` only when the main LRA
            // bounds prove a single floor value. The raw LRA model is not a
            // sound witness here: for `3 <= x < 4`, simplex may sit on the
            // strict upper boundary `4`, and `floor(4) = 4` would create a
            // false conflict with the satisfiable floor value `3`.
            let bounds = self.lra.get_bounds(inner_arg_term);
            let Some((floored, arg_reasons)) = bounds.as_ref().and_then(|(lower, upper)| {
                Self::exact_floor_reasons(lower.as_ref(), upper.as_ref())
            }) else {
                continue;
            };
            let key = floored.numer().clone();
            let new_kind = PropagationKind::Tight;
            let prev_kind = self
                .propagated_cross_sort
                .get(&(to_int_term, key.clone()))
                .cloned();
            if prev_kind == Some(PropagationKind::Tight) {
                continue;
            }
            self.propagated_cross_sort
                .insert((to_int_term, key.clone()), new_kind);
            self.cross_sort_trail.push(CrossSortTrailEntry::Propagated(
                to_int_term,
                key.clone(),
                prev_kind,
            ));

            if debug {
                safe_eprintln!(
                    "[N-O LIRA] to_int propagation: to_int(term {:?}) = floor({}) = {} ({} reasons)",
                    inner_arg_term,
                    floored,
                    floored,
                    arg_reasons.len()
                );
            }
            // Assert tight bound: to_int(x) = floor(x) in LIA's internal solver
            // with the reasons from x's bounds in main LRA.
            self.lia
                .lra_solver_mut()
                .assert_tight_bound(to_int_term, &floored, &arg_reasons);
            count += 1;
        }
        count
    }
}
