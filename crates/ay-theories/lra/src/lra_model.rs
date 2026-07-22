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
    pub(crate) fn compute_materialization_delta(&self) -> BigRational {
        let two = BigRational::from(BigInt::from(2));
        let mut delta = BigRational::one();

        for info in &self.vars {
            let y = info.value.epsilon();
            if y.is_zero() {
                continue;
            }
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
        &delta / &two
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
            if lower.value == upper.value && !lower.strict && !upper.strict {
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
