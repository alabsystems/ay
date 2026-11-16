// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction, value queries, and cross-sort bound propagation.
//!
//! Handles the conversion from InfRational simplex assignments to concrete
//! rational models, and provides the public API for value and bound queries.

use super::*;

impl LraSolver {
    /// Compute a concrete δ > 0 such that materializing all InfRational
    /// assignments as `x + y*δ` preserves every bound constraint.
    ///
    /// After simplex with InfRational values, some assignments may have
    /// infinitesimal components (e.g., `(0, +1)` for strict bound `x > 0`).
    /// To produce a concrete rational model, we choose δ small enough that:
    /// - For each variable with value `(x, y)` and lower bound `lb`:
    ///   if `y < 0`, need `δ ≤ (x - lb) / |y|`
    /// - For each variable with value `(x, y)` and upper bound `ub`:
    ///   if `y > 0`, need `δ ≤ (ub - x) / y`
    ///
    /// Reference: Dutertre & de Moura (CAV 2006), Section 3.
    /// Diagnostic count of materialisation-δ computations (each an
    /// O(#vars) scan). Evaluation passes over one unchanged model are
    /// expected to share one δ via [`Self::get_value_sharing_delta`].
    pub fn materialization_delta_computations(&self) -> u64 {
        self.materialization_delta_computations.get()
    }

    pub(crate) fn compute_materialization_delta(&self) -> BigRational {
        self.materialization_delta_computations
            .set(self.materialization_delta_computations.get() + 1);
        let two = BigRational::from(BigInt::from(2));
        let mut delta = BigRational::one();
        let mut any_epsilon = false;

        for info in &self.vars {
            let y = info.value.epsilon();
            if y.is_zero() {
                continue;
            }
            any_epsilon = true;
            let x = info.value.rational();

            if y.is_negative() {
                // Variable has negative ε: value decreases with δ.
                // Lower bound constraint: x + y*δ ≥ lb  ⇒  δ ≤ (x - lb) / |y|
                if let Some(ref lb) = info.lower {
                    let slack: BigRational = x.clone() - &lb.value_big();
                    if slack.is_positive() {
                        let max_delta = slack / (-y.clone());
                        if max_delta < delta {
                            delta = max_delta;
                        }
                    }
                }
            }

            if y.is_positive() {
                // Variable has positive ε: value increases with δ.
                // Upper bound constraint: x + y*δ ≤ ub  ⇒  δ ≤ (ub - x) / y
                if let Some(ref ub) = info.upper {
                    let slack = &ub.value_big() - &x;
                    if slack.is_positive() {
                        let max_delta: BigRational = slack / &y;
                        if max_delta < delta {
                            delta = max_delta;
                        }
                    }
                }
            }
        }

        // Halve for safety margin
        let mut delta = &delta / &two;
        // Asserted disequalities are not bounds, so the envelope above ignores
        // them: one whose simplex value is x + k·ε (the check accepts it, the
        // value is not zero) materialises to x + k·δ, which is exactly zero at
        // δ = −x/k when x and k have opposite signs. Picking that δ publishes
        // a model that violates the disequality — e.g. `x > 0, x ≤ 1` with
        // `2x ≠ 1` under Boolean structure: x = 0+ε, δ = 1/2, x = 1/2
        // (DPLL_LRA_perf_2026-09-23 §1, the om1 BMC invalid model). Halving
        // keeps every bound constraint (they only cap δ from above) and gives
        // a new value each time, so it clears the finitely many zero points in
        // at most |trail| steps. With no ε component anywhere no disequality
        // value has one either, and the scan is skipped.
        if any_epsilon {
            let zero_points = self.disequality_zero_deltas();
            while zero_points.contains(&delta) {
                delta = &delta / &two;
            }
        }
        // `materialized_sign` relies on exactly this envelope: every candidate
        // above is a positive slack over a non-zero |y| (so δ never reaches
        // 0) and δ only ever decreases from 1 before the halving.
        debug_assert!(
            delta.is_positive() && delta <= BigRational::new(BigInt::one(), BigInt::from(2))
        );

        delta
    }

    /// The δ values at which an asserted disequality (the local
    /// `disequality_trail` and the Nelson-Oppen `shared_disequality_trail`)
    /// materialises to exactly zero: its value `x + k·ε` becomes `x + k·δ`,
    /// zero at `δ = −x/k` when `x` and `k` have opposite signs. Empty when no
    /// disequality carries an ε component.
    fn disequality_zero_deltas(&self) -> Vec<BigRational> {
        let exprs = self
            .disequality_trail
            .iter()
            .map(|(_, expr, _)| expr)
            .chain(
                self.shared_disequality_trail
                    .iter()
                    .map(|(_, _, expr, _, _)| expr),
            );
        let mut zero_points = Vec::new();
        for expr in exprs {
            let mut value = InfRational::from_rat(expr.constant.clone());
            for &(var, ref coeff) in &expr.coeffs {
                if let Some(info) = self.vars.get(var as usize) {
                    value += &info.value.mul_rat(coeff);
                }
            }
            let k = value.epsilon();
            if k.is_zero() {
                continue;
            }
            let x = value.rational();
            if x.is_zero() || x.is_positive() == k.is_positive() {
                continue;
            }
            zero_points.push(-(x / k));
        }
        zero_points
    }

    /// Materialize an InfRational value into a concrete BigRational.
    pub(crate) fn materialize_value(&self, val: &InfRational, delta: &BigRational) -> BigRational {
        val.materialize(delta)
    }

    /// Extract the current model (variable assignments)
    ///
    /// Returns a mapping from term IDs (for variables) to their rational values.
    /// Should only be called after `check()` returns `Sat`.
    pub fn extract_model(&self) -> LraModel {
        let mut values = HashMap::default();
        let delta = self.compute_materialization_delta();

        let debug = self.debug_lra;
        if debug {
            safe_eprintln!(
                "[LRA] extract_model: term_to_var has {} entries, delta={}",
                self.term_to_var.len(),
                delta
            );
        }

        // Extract values for all variables that have associated term IDs
        for (&term, &var) in &self.term_to_var {
            if let Some(info) = self.vars.get(var as usize) {
                let concrete = self.materialize_value(&info.value, &delta);
                if debug {
                    safe_eprintln!(
                        "[LRA] extract_model: term {} -> var {} = {} -> {}",
                        term.0,
                        var,
                        info.value,
                        concrete
                    );
                }
                values.insert(term, concrete);
            }
        }

        let mut model = LraModel { values };

        // #7654: when an asserted equality-semantic atom pins a variable to an
        // exact constant, prefer that exact value over delta-materialized
        // simplex noise.
        let mut equality_patched_var_ids: HashSet<u32> = HashSet::default();
        for (&atom_term, &atom_value) in &self.asserted {
            let Some(Some(info)) = self.atom_cache.get(&atom_term) else {
                continue;
            };
            if !Self::asserted_atom_is_equality(info, atom_value) || info.expr.coeffs.len() != 1 {
                continue;
            }
            let (var, coeff) = &info.expr.coeffs[0];
            if coeff.is_zero() {
                continue;
            }
            let Some(term) = self.var_term_id(*var) else {
                continue;
            };
            let exact = (-info.expr.constant.clone() / coeff.clone()).to_big();
            model.values.insert(term, exact);
            equality_patched_var_ids.insert(*var);
        }
        if !equality_patched_var_ids.is_empty() {
            self.propagate_model_equalities(&mut model, &equality_patched_var_ids);
        }

        // Fix up to_int variables: use floor(arg_value) instead of raw simplex value.
        // The simplex may assign a non-integer value to the to_int variable
        // (it only knows the floor axiom bounds, not integrality). The model
        // evaluator expects to_int(x) = floor(x), so we patch the value here.
        //
        // After patching, propagate to variables constrained equal to each
        // to_int var (#6227). When z = to_real(to_int(x)), the equality is
        // asserted as a 2-variable expression: z - to_int(x) = 0. After simplex
        // pivots, the direct tableau connection is dissolved, so we find equal
        // variables by scanning asserted equality atoms that reference to_int vars.
        let mut patched_var_ids: HashSet<u32> = HashSet::default();
        for &(to_int_var, inner_arg_term) in &self.to_int_terms {
            if let Some(to_int_term) = self.var_term_id(to_int_var) {
                if let Some(arg_val) = model.values.get(&inner_arg_term) {
                    let floored = BigRational::from(arg_val.floor().to_integer());
                    if debug {
                        safe_eprintln!(
                            "[LRA] extract_model: to_int fix: term {} = floor({}) = {}",
                            to_int_term.0,
                            arg_val,
                            floored
                        );
                    }
                    model.values.insert(to_int_term, floored);
                    patched_var_ids.insert(to_int_var);
                }
            }
        }

        // Propagate to_int patches via asserted equality atoms (#6227).
        // Scan asserted atoms for equalities whose parsed expression involves
        // exactly one to_int variable. The other variable in the expression is
        // structurally constrained equal to the to_int var, so copy its value.
        if !patched_var_ids.is_empty() {
            self.propagate_model_equalities(&mut model, &patched_var_ids);
        }

        model
    }

    /// Materialize a single variable's InfRational assignment, computing the
    /// global δ ONLY when the value actually has an infinitesimal component.
    /// `materialize` is the identity on zero-ε values, and ε is zero for
    /// virtually every assignment in the integer (LIA) lane — while
    /// `compute_materialization_delta` is an O(#vars) BigRational scan.
    /// Profiled as the dominant N-O interface-eval cost on the Certora
    /// QF_UFLIA VCs (2^256-scale constants), where the combiner queries one
    /// value per interface-term leaf per fixpoint round
    /// (#certora-materialization-delta). Exact equivalence: when ε = 0 the
    /// returned value is identical to the δ-materialized one for every δ.
    fn materialize_single_value(&self, val: &InfRational) -> BigRational {
        if val.epsilon_is_zero() {
            val.rational()
        } else {
            let delta = self.compute_materialization_delta();
            self.materialize_value(val, &delta)
        }
    }

    /// Get the current value of a variable by term ID
    pub fn get_value(&self, term: TermId) -> Option<BigRational> {
        self.term_to_var
            .get(&term)
            .and_then(|&var| self.vars.get(var as usize))
            .map(|info| self.materialize_single_value(&info.value))
    }

    /// Batch form of [`Self::get_value`]: identical values, but the
    /// O(#vars) materialisation δ is computed at most once for the
    /// whole batch instead of once per ε-carrying term. Exact
    /// equivalence, not an approximation: δ depends only on the
    /// current assignments, bounds and disequality trails, none of
    /// which a `&self` query can change, so the δ one `get_value`
    /// would compute is the δ every other term in the same batch
    /// would compute. Callers that evaluate many leaves against one
    /// model (the NRA monomial-consistency pass asks per factor
    /// occurrence per refinement iteration; sampled at ~40% of the
    /// wall on QF_UFNRA `cas/40f50`, almost all of it repeated δ
    /// scans) should snapshot through here.
    pub fn get_values(&self, terms: &[TermId]) -> Vec<Option<BigRational>> {
        let mut delta: Option<BigRational> = None;
        terms
            .iter()
            .map(|&term| self.get_value_sharing_delta(term, &mut delta))
            .collect()
    }

    /// [`Self::get_value`] with the materialisation δ supplied (and
    /// filled on first need) by the caller, so a read-only evaluation
    /// pass over one unchanged model pays the O(#vars) δ scan at most
    /// once across all its queries instead of once per ε-carrying
    /// term. The caller must not reuse `delta` across any mutation of
    /// assignments, bounds or disequality trails — δ is a function of
    /// exactly those. Values are identical to `get_value`'s: same
    /// materialisation, same δ (see [`Self::get_values`]).
    pub fn get_value_sharing_delta(
        &self,
        term: TermId,
        delta: &mut Option<BigRational>,
    ) -> Option<BigRational> {
        let &var = self.term_to_var.get(&term)?;
        let info = self.vars.get(var as usize)?;
        if info.value.epsilon_is_zero() {
            Some(info.value.rational())
        } else {
            let delta = delta.get_or_insert_with(|| self.compute_materialization_delta());
            Some(self.materialize_value(&info.value, delta))
        }
    }

    /// `get_value(term).is_some()` without materialising the value: the term
    /// has a tableau column. No allocation (#nonlinear-phase-hints — the NRA /
    /// NIA phase look-ahead asks this for every operand of every unassigned
    /// atom after every BCP quiescence and only needs the existence bit).
    #[must_use]
    pub fn has_value(&self, term: TermId) -> bool {
        self.term_to_var
            .get(&term)
            .is_some_and(|&var| (var as usize) < self.vars.len())
    }

    /// The sign of `get_value(term)` — `Some(Equal)` for zero — computed
    /// exactly and, on every path but one, without materialising the value
    /// (#nonlinear-phase-hints). `None` iff `get_value` is `None`.
    #[must_use]
    pub fn value_sign(&self, term: TermId) -> Option<std::cmp::Ordering> {
        let &var = self.term_to_var.get(&term)?;
        let info = self.vars.get(var as usize)?;
        Some(self.materialized_sign(&info.value))
    }

    /// Exact sign of `materialize_single_value(val)` = `x + y·δ`, where δ is
    /// the global materialisation delta, WITHOUT computing δ except in the one
    /// case where the sign genuinely depends on it.
    ///
    /// `compute_materialization_delta` starts at 1, only ever lowers δ, and
    /// halves the result, so `0 < δ ≤ 1/2` (the lower bound because every
    /// candidate is a positive slack over a non-zero |y|; the debug assertion
    /// there pins both). Hence:
    /// - `y = 0`: the value is `x` (materialise is the identity), sign(x);
    /// - `x = 0`: the value is `y·δ` with δ > 0, sign(y);
    /// - `x`, `y` of one sign: both summands share it, sign(x);
    /// - opposite signs with `2|x| > |y|`: `|y·δ| ≤ |y|/2 < |x|`, so the
    ///   rational part dominates, sign(x);
    /// - otherwise (opposite signs, `2|x| ≤ |y|`): materialise exactly.
    ///
    /// Every branch is the sign of the same quantity `materialize` returns,
    /// so this agrees with `get_value(..).cmp(&0)` bit-for-bit; the
    /// `nlsat` debug oracle re-checks that on every call.
    fn materialized_sign(&self, val: &InfRational) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        let (x, y) = val.parts();
        let zero = Rational::zero();
        if y.is_zero() {
            return x.cmp(&zero);
        }
        if x.is_zero() {
            return y.cmp(&zero);
        }
        if x.is_positive() == y.is_positive() {
            return x.cmp(&zero);
        }
        // Opposite signs: compare 2|x| against |y| without allocating (the
        // `Small` arithmetic path stays inline; a `Big` operand promotes).
        let abs = |r: &Rational| {
            if r.is_negative() {
                -r.clone()
            } else {
                r.clone()
            }
        };
        let two_abs_x = &abs(x) + &abs(x);
        if two_abs_x > abs(y) {
            return x.cmp(&zero);
        }
        let delta = self.compute_materialization_delta();
        let materialized = self.materialize_value(val, &delta);
        if materialized.is_zero() {
            Ordering::Equal
        } else if materialized.is_positive() {
            Ordering::Greater
        } else {
            Ordering::Less
        }
    }

    /// Get the current value of a variable term along with the bound reasons
    /// that fix it (#4068). Returns `(value, reasons)` where `reasons` are
    /// the `TheoryLit`s from the tight lower and upper bounds when both exist
    /// and are equal (non-strict). Falls back to an empty reason set when
    /// bounds are not tight (the value is still the simplex assignment).
    pub fn get_value_with_reasons(&self, term: TermId) -> Option<(BigRational, Vec<TheoryLit>)> {
        let &var = self.term_to_var.get(&term)?;
        let info = self.vars.get(var as usize)?;
        // #certora-materialization-delta: δ computed only when ε ≠ 0.
        let value = self.materialize_single_value(&info.value);
        let mut reasons = Vec::new();
        if let (Some(ref lower), Some(ref upper)) = (&info.lower, &info.upper) {
            // Only a JUSTIFIED pin is a fact another theory may learn
            // (#nonlinear-shared-reasons): an NIA/NRA model guess (reason =
            // the variable term) reports no reasons, so the interface bridge
            // treats the value as speculative (a SAT-level model equality)
            // instead of handing EUF an equality whose reason is no atom.
            if lower.value == upper.value
                && !lower.strict
                && !upper.strict
                && self.bound_reasons_all_asserted(lower)
                && self.bound_reasons_all_asserted(upper)
            {
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
            }
        }
        Some((value, reasons))
    }

    /// Get the current simplex assignment along with ALL available bound reasons
    /// (#5947). Unlike `get_value_with_reasons` which only returns reasons when
    /// bounds are tight, this returns reasons from whatever bounds exist (lower,
    /// upper, or both). Used by LIRA cross-sort propagation to forward integer
    /// simplex assignments even when LIA hasn't established a tight bound.
    pub fn get_value_with_all_bound_reasons(
        &self,
        term: TermId,
    ) -> Option<(BigRational, Vec<TheoryLit>)> {
        let &var = self.term_to_var.get(&term)?;
        let info = self.vars.get(var as usize)?;
        // #certora-materialization-delta: δ computed only when ε ≠ 0.
        let value = self.materialize_single_value(&info.value);
        let mut reasons = Vec::new();
        if let Some(ref lower) = &info.lower {
            for (term, val) in lower.reason_pairs() {
                if !term.is_sentinel() {
                    reasons.push(TheoryLit::new(term, val));
                }
            }
        }
        if let Some(ref upper) = &info.upper {
            for (term, val) in upper.reason_pairs() {
                if !term.is_sentinel() && !reasons.iter().any(|r| r.term == term) {
                    reasons.push(TheoryLit::new(term, val));
                }
            }
        }
        Some((value, reasons))
    }
}
