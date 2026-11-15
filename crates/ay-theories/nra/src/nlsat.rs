// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NLSAT-style techniques for NRA: feasible-set look-ahead and arithmetic
//! propagation branching.
//!
//! Implements the two key techniques from clauseSMT (Wang, ASE 2025):
//!
//! 1. **Feasible-set look-ahead**: For polynomial constraints with one free
//!    variable, compute the set of values that satisfy the constraint. Guide
//!    literal decisions toward arithmetic feasibility.
//!
//! 2. **Arithmetic propagation branching**: Track blocked (empty feasible set)
//!    and fixed (singleton feasible set) variables. Branch on these first.
//!
//! Reference: "Improving NLSAT for Nonlinear Real Arithmetic" (Wang, ASE 2025),
//! arXiv:2406.02122.

use ay_core::term::{Constant, Symbol, TermData, TermId};
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::cmp::Ordering;

use crate::feasible_set::{FeasibilityClass, FeasibleSet};
use crate::NraSolver;

impl NraSolver<'_> {
    /// The feasible-set look-ahead's phase suggestion for `atom`, or `None`
    /// when it has no opinion (the caller then asks the wrapped linear solver,
    /// exactly as before).
    ///
    /// # Why this exists (#nonlinear-phase-hints)
    ///
    /// The SAT seeder queries `suggest_phase` for EVERY unassigned theory atom
    /// after EVERY BCP quiescence. The previous implementation answered by
    /// building both polarities' feasible sets — two `compute_literal_feasible_set`
    /// calls, each evaluating both operands and every leaf of the
    /// linear-univariate walk through `LraSolver::get_value` (a `BigRational`
    /// per leaf, plus the O(#vars) materialisation delta whenever the value
    /// carries an ε) and allocating the interval sets — and then compared the
    /// two sets. Sampled at 36–72 % of the wall on QF_UFNRA `cas` (`40m10`) and
    /// 62–68 % on QF_UFDTNIA Certora `11775`.
    ///
    /// # What it computes, and why it is value-exact
    ///
    /// For a binary atom `lhs cmp rhs` the two feasible sets differ only in
    /// the polarity they are built for; the free variable, the coefficient
    /// `a` and the target are the same, so the old decision is a function of
    /// `cmp`, of which side carries the free variable, and of `a` alone:
    ///
    /// - `a = 0` (a factor evaluates to zero): the set for polarity `p` is full
    ///   iff `0 cmp target` has truth value `p`, so exactly one polarity is
    ///   empty and the suggestion is that truth value — computed below by the
    ///   reference (it needs the target's exact value; measured rare).
    /// - `a ≠ 0`: both sets are non-empty, and the comparison of their
    ///   interval counts decides. With `cmp'` = `cmp` flipped when `a < 0`:
    ///   `distinct` gives 2 intervals against 1 for its negation → `true`;
    ///   `=` gives 1 against 2 → `false`; the four inequalities give 1 against
    ///   1 → no opinion; an unrecognised comparator gives the full line (1)
    ///   against `distinct` (2) → `false`. (`flip_cmp` maps an unrecognised
    ///   comparator to `=`, which lands on the same `false`.)
    ///
    /// So only the SIGN of `a` is needed, and `a` is a product of leaf values
    /// (`c * inner` at every `*` node, negated by `-`), whose sign is the
    /// product of the leaves' signs and which is zero iff a leaf is zero.
    /// `linear_univariate_coefficient_sign` walks the term exactly as
    /// `extract_linear_univariate` does — the same nodes, the same
    /// "is this operand evaluable" tests (`term_has_value`, the existence bit
    /// of `term_value`), the same first-match order — and folds the leaf
    /// signs (`term_value_sign`, exact without materialising) instead of the
    /// leaf values. Nothing is allocated on this path; the reference is kept
    /// as `feasible_set_phase_reference` and every debug build asserts the two
    /// agree on every call.
    pub(crate) fn feasible_set_phase(&self, atom: TermId) -> Option<bool> {
        let (cmp_name, lhs, rhs) = match self.terms.get(atom) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                (name.as_str(), args[0], args[1])
            }
            _ => return None,
        };
        let lhs_has = self.term_has_value(lhs);
        let rhs_has = self.term_has_value(rhs);
        // Both sides fully evaluated: `compute_literal_feasible_set` returned
        // `None` for both polarities.
        if lhs_has && rhs_has {
            return None;
        }
        // The reference tries `extract_linear_univariate(lhs)` and uses it iff
        // the RHS evaluates; otherwise `extract_linear_univariate(rhs)` iff the
        // LHS evaluates (flipping the comparator). At most one side evaluates
        // here, so the branch is decided by which one does.
        let (side, cmp) = if rhs_has {
            (lhs, cmp_name)
        } else if lhs_has {
            (rhs, flip_cmp(cmp_name))
        } else {
            return None;
        };
        let coeff_sign = self.linear_univariate_coefficient_sign(side)?;
        if coeff_sign == Ordering::Equal {
            // Degenerate `0 cmp target`: the answer is the constant truth
            // value, which needs the target's exact value. Rare; take the
            // reference path, which is exact by definition.
            return self.feasible_set_phase_reference(atom);
        }
        let effective_cmp = if coeff_sign == Ordering::Less {
            flip_cmp(cmp)
        } else {
            cmp
        };
        match effective_cmp {
            "distinct" | "!=" => Some(true),
            "=" => Some(false),
            ">=" | ">" | "<=" | "<" => None,
            _ => Some(false),
        }
    }

    /// The previous `suggest_phase` body, verbatim: both polarities' feasible
    /// sets, then emptiness and interval-count comparison. The debug-build
    /// oracle for `feasible_set_phase`, and its exact fallback for the
    /// degenerate zero-coefficient case.
    pub(crate) fn feasible_set_phase_reference(&self, atom: TermId) -> Option<bool> {
        let mut delta = None;
        if let Some((_free_var, fs_true)) =
            self.compute_literal_feasible_set_with_delta(atom, true, &mut delta)
        {
            if let Some((_free_var, fs_false)) =
                self.compute_literal_feasible_set_with_delta(atom, false, &mut delta)
            {
                // Prefer the phase that produces a non-empty feasible set
                let true_empty = fs_true.is_empty();
                let false_empty = fs_false.is_empty();
                if true_empty && !false_empty {
                    return Some(false);
                }
                if false_empty && !true_empty {
                    return Some(true);
                }
                // If both are non-empty, prefer the one with a wider feasible set
                // (more intervals = more flexibility). Fall through to LRA otherwise.
                if fs_true.num_intervals() > fs_false.num_intervals() {
                    return Some(true);
                }
                if fs_false.num_intervals() > fs_true.num_intervals() {
                    return Some(false);
                }
            }
        }
        None
    }

    /// `term_value(term).is_some()` without computing the value: an LRA
    /// column or a numeric literal.
    #[inline]
    pub(crate) fn term_has_value(&self, term: TermId) -> bool {
        self.lra.has_value(term)
            || matches!(
                self.terms.get(term),
                TermData::Const(Constant::Rational(_)) | TermData::Const(Constant::Int(_))
            )
    }

    /// The exact sign of `term_value(term)` (`Equal` for zero), in the same
    /// precedence order as `term_value`: the LRA column first, then the
    /// literal. `None` iff `term_value` is `None`.
    fn term_value_sign(&self, term: TermId) -> Option<Ordering> {
        if let Some(sign) = self.lra.value_sign(term) {
            return Some(sign);
        }
        match self.terms.get(term) {
            TermData::Const(Constant::Rational(r)) => Some(sign_of(&r.0)),
            TermData::Const(Constant::Int(n)) => Some(n.sign().cmp(&num_bigint::Sign::NoSign)),
            _ => None,
        }
    }

    /// The sign of the coefficient `extract_linear_univariate(term)` would
    /// return (`Equal` when it would be zero), or `None` when that extraction
    /// finds no linear-in-one-free-variable form. Same recursion, same
    /// first-match order, same evaluability tests; the values are replaced by
    /// their signs (a product's sign is the product of signs and is zero iff a
    /// factor is zero; `-` reverses it; `+` leaves it alone).
    fn linear_univariate_coefficient_sign(&self, term: TermId) -> Option<Ordering> {
        match self.terms.get(term) {
            TermData::Var(_, _) => {
                if self.lra.has_value(term) {
                    return None; // Already assigned
                }
                Some(Ordering::Greater) // coefficient 1
            }
            TermData::Const(_) => None,
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "*" if args.len() == 2 => {
                    let (a0, a1) = (args[0], args[1]);
                    if let Some(c) = self.term_value_sign(a0) {
                        if let Some(inner) = self.linear_univariate_coefficient_sign(a1) {
                            return Some(mul_sign(c, inner));
                        }
                    }
                    if let Some(c) = self.term_value_sign(a1) {
                        if let Some(inner) = self.linear_univariate_coefficient_sign(a0) {
                            return Some(mul_sign(c, inner));
                        }
                    }
                    None
                }
                "+" if args.len() == 2 => {
                    let (a0, a1) = (args[0], args[1]);
                    if self.term_has_value(a0) {
                        if let Some(inner) = self.linear_univariate_coefficient_sign(a1) {
                            return Some(inner);
                        }
                    }
                    if self.term_has_value(a1) {
                        if let Some(inner) = self.linear_univariate_coefficient_sign(a0) {
                            return Some(inner);
                        }
                    }
                    None
                }
                "-" if args.len() == 2 => {
                    let (a0, a1) = (args[0], args[1]);
                    if self.term_has_value(a0) {
                        if let Some(inner) = self.linear_univariate_coefficient_sign(a1) {
                            return Some(inner.reverse());
                        }
                    }
                    if self.term_has_value(a1) {
                        if let Some(inner) = self.linear_univariate_coefficient_sign(a0) {
                            return Some(inner);
                        }
                    }
                    None
                }
                "-" if args.len() == 1 => self
                    .linear_univariate_coefficient_sign(args[0])
                    .map(Ordering::reverse),
                _ => None,
            },
            _ => None,
        }
    }

    /// Compute the feasible set for a comparison atom `lhs cmp rhs` where one
    /// side involves a monomial with a single free variable.
    ///
    /// For a constraint like `x * y >= 5` where y is assigned to 3, this becomes
    /// `x >= 5/3`, giving feasible set [5/3, +inf).
    ///
    /// This is a simplified version of full NLSAT root isolation: we handle
    /// the common case of linear-in-one-variable constraints after partial
    /// evaluation. Full CAD root isolation is deferred to #8335.
    /// Compute one literal's feasible set, sharing one materialisation
    /// delta across a read-only pass over many atoms (identical
    /// results; see `term_value_sharing_delta`).
    pub(crate) fn compute_literal_feasible_set_with_delta(
        &self,
        atom: TermId,
        value: bool,
        delta: &mut Option<BigRational>,
    ) -> Option<(TermId, FeasibleSet)> {
        let (cmp_name, lhs, rhs) = match self.terms.get(atom) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                (name.as_str(), args[0], args[1])
            }
            _ => return None,
        };

        // Try to find a monomial factor with exactly one unassigned variable.
        // Evaluate the constraint partially and compute the feasible set for
        // the free variable.

        // Strategy: evaluate both sides, find which has a free variable.
        let lhs_val = self.eval_to_rational_with_delta(lhs, delta);
        let rhs_val = self.eval_to_rational_with_delta(rhs, delta);

        // If both sides are fully evaluated, the feasible set is trivial.
        if lhs_val.is_some() && rhs_val.is_some() {
            return None;
        }

        // Try linear-in-one-variable: a*x + b cmp c
        // where a, b, c are known rational values and x is the free variable.
        if let Some((free_var, coeff, constant)) =
            self.extract_linear_univariate_with_delta(lhs, delta)
        {
            if let Some(rhs_v) = rhs_val {
                // a*x + b cmp rhs_v => a*x cmp (rhs_v - b)
                let target = rhs_v - &constant;
                return Some((
                    free_var,
                    self.feasible_set_from_linear(cmp_name, value, &coeff, &target),
                ));
            }
        }

        if let Some((free_var, coeff, constant)) =
            self.extract_linear_univariate_with_delta(rhs, delta)
        {
            if let Some(lhs_v) = lhs_val {
                // lhs_v cmp a*x + b => (lhs_v - b) cmp a*x
                // Flip the comparison direction
                let target = lhs_v - &constant;
                let flipped = flip_cmp(cmp_name);
                return Some((
                    free_var,
                    self.feasible_set_from_linear(flipped, value, &coeff, &target),
                ));
            }
        }

        None
    }

    /// Evaluate a term to a rational value using the current LRA model.
    /// Returns None if the term has unassigned variables.
    fn eval_to_rational_with_delta(
        &self,
        term: TermId,
        delta: &mut Option<BigRational>,
    ) -> Option<BigRational> {
        self.term_value_sharing_delta(term, delta)
    }

    /// Extract a linear expression in one variable from a term: a*x + b.
    /// Returns (free_var, coefficient a, constant b).
    ///
    /// Handles simple cases:
    /// - Variable x: (x, 1, 0)
    /// - Multiplication: c * x where c is known -> (x, c, 0)
    /// - Addition: expr1 + expr2 where one side has a free variable
    /// - Subtraction: expr1 - expr2
    fn extract_linear_univariate_with_delta(
        &self,
        term: TermId,
        delta: &mut Option<BigRational>,
    ) -> Option<(TermId, BigRational, BigRational)> {
        match self.terms.get(term) {
            TermData::Var(_, _) => {
                // Check if this variable has a value in the model
                if self.var_value_sharing_delta(term, delta).is_some() {
                    return None; // Already assigned
                }
                Some((term, BigRational::one(), BigRational::zero()))
            }
            TermData::Const(Constant::Int(n)) => {
                // Constant: no free variable
                let _ = n;
                None
            }
            TermData::Const(Constant::Rational(_)) => None,
            TermData::App(Symbol::Named(name), args) => {
                match name.as_str() {
                    "*" if args.len() == 2 => {
                        let a0 = args[0];
                        let a1 = args[1];
                        // c * x where c is known
                        if let Some(c) = self.eval_to_rational_with_delta(a0, delta) {
                            if let Some((var, inner_coeff, inner_const)) =
                                self.extract_linear_univariate_with_delta(a1, delta)
                            {
                                return Some((var, &c * &inner_coeff, &c * &inner_const));
                            }
                        }
                        if let Some(c) = self.eval_to_rational_with_delta(a1, delta) {
                            if let Some((var, inner_coeff, inner_const)) =
                                self.extract_linear_univariate_with_delta(a0, delta)
                            {
                                return Some((var, &c * &inner_coeff, &c * &inner_const));
                            }
                        }
                        None
                    }
                    "+" if args.len() == 2 => {
                        let a0 = args[0];
                        let a1 = args[1];
                        // Try: known + linear(x)
                        if let Some(c) = self.eval_to_rational_with_delta(a0, delta) {
                            if let Some((var, coeff, constant)) =
                                self.extract_linear_univariate_with_delta(a1, delta)
                            {
                                return Some((var, coeff, constant + c));
                            }
                        }
                        if let Some(c) = self.eval_to_rational_with_delta(a1, delta) {
                            if let Some((var, coeff, constant)) =
                                self.extract_linear_univariate_with_delta(a0, delta)
                            {
                                return Some((var, coeff, constant + c));
                            }
                        }
                        None
                    }
                    "-" if args.len() == 2 => {
                        let a0 = args[0];
                        let a1 = args[1];
                        if let Some(c) = self.eval_to_rational_with_delta(a0, delta) {
                            if let Some((var, coeff, constant)) =
                                self.extract_linear_univariate_with_delta(a1, delta)
                            {
                                return Some((var, -coeff, c - constant));
                            }
                        }
                        if let Some(c) = self.eval_to_rational_with_delta(a1, delta) {
                            if let Some((var, coeff, constant)) =
                                self.extract_linear_univariate_with_delta(a0, delta)
                            {
                                return Some((var, coeff, constant - c));
                            }
                        }
                        None
                    }
                    "-" if args.len() == 1 => {
                        // Unary negation
                        let a0 = args[0];
                        if let Some((var, coeff, constant)) =
                            self.extract_linear_univariate_with_delta(a0, delta)
                        {
                            return Some((var, -coeff, -constant));
                        }
                        None
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Compute the feasible set for `a*x [cmp] target` where cmp is adjusted
    /// by `value` (negation if value is false).
    fn feasible_set_from_linear(
        &self,
        cmp: &str,
        value: bool,
        coeff: &BigRational,
        target: &BigRational,
    ) -> FeasibleSet {
        if coeff.is_zero() {
            // Degenerate: 0 [cmp] target => constant truth value
            let holds = eval_constant_cmp(cmp, &BigRational::zero(), target);
            if holds == value {
                return FeasibleSet::full();
            } else {
                return FeasibleSet::empty();
            }
        }

        // a*x [cmp] target => x [cmp'] target/a
        // If a < 0, the comparison flips.
        let bound = target / coeff;
        let negative_coeff = coeff < &BigRational::zero();
        let effective_cmp = if negative_coeff { flip_cmp(cmp) } else { cmp };

        // Now compute feasible set for x [effective_cmp] bound
        // If value is false, negate the comparison.
        let (final_cmp, _) = if value {
            (effective_cmp, true)
        } else {
            (negate_cmp(effective_cmp), false)
        };

        match final_cmp {
            ">=" => FeasibleSet::from_interval(Some(bound), false, None, true),
            ">" => FeasibleSet::from_interval(Some(bound), true, None, true),
            "<=" => FeasibleSet::from_interval(None, true, Some(bound), false),
            "<" => FeasibleSet::from_interval(None, true, Some(bound), true),
            "=" => FeasibleSet::singleton(bound),
            "distinct" | "!=" => {
                // Everything except the single point: (-inf, bound) U (bound, +inf)
                let lo = FeasibleSet::from_interval(None, true, Some(bound.clone()), true);
                let hi = FeasibleSet::from_interval(Some(bound), true, None, true);
                lo.union(&hi)
            }
            _ => FeasibleSet::full(), // Unknown comparison: be conservative
        }
    }

    /// Update feasible sets for all variables involved in asserted constraints.
    /// Called during the NRA check loop to maintain arithmetic propagation state.
    ///
    /// clauseSMT Technique 1 (feasible-set look-ahead): For each asserted atom
    /// that involves a polynomial with one free variable, compute the literal's
    /// feasible set and intersect it into the variable's accumulated feasible set.
    ///
    /// clauseSMT Technique 2 (arithmetic propagation branching): Classify the
    /// result as blocked/fixed/narrowed. Blocked and fixed variables are
    /// prioritized for branching via `suggest_decision_atom`.
    ///
    /// Reference: "Improving NLSAT for NRA" (Wang, ASE 2025), arXiv:2406.02122.
    pub(crate) fn update_feasible_sets(&mut self) {
        // Reset classification sets
        self.blocked_vars.clear();
        self.fixed_vars.clear();

        // Recompute feasible sets from scratch. Each call to check() may have
        // different asserted literals due to backtracking, so we cannot
        // incrementally update.
        self.feasible_sets.clear();

        // Compute feasible set for each asserted literal and intersect into
        // the per-variable accumulated feasible set.
        // Iterate by index to avoid cloning self.asserted (#8599).
        // One materialisation delta serves the whole recomputation: the
        // asserted set and LRA state do not change during this pass.
        let mut delta = None;
        for i in 0..self.asserted.len() {
            let (atom, value) = self.asserted[i];
            if let Some((free_var, lit_fs)) =
                self.compute_literal_feasible_set_with_delta(atom, value, &mut delta)
            {
                self.feasible_set_count = self.feasible_set_count.saturating_add(1);
                let var_fs = self
                    .feasible_sets
                    .entry(free_var)
                    .or_insert_with(FeasibleSet::full);
                *var_fs = var_fs.intersection(&lit_fs);
            }
        }

        // Classify all tracked variables
        for (&var, fs) in &self.feasible_sets {
            match fs.classify() {
                FeasibilityClass::Blocked => {
                    self.blocked_vars.push(var);
                }
                FeasibilityClass::Fixed(v) => {
                    self.fixed_vars.push((var, v));
                }
                FeasibilityClass::Narrowed => {
                    // Default VSIDS branching — nothing to do.
                }
            }
        }

        if self.debug && (!self.blocked_vars.is_empty() || !self.fixed_vars.is_empty()) {
            tracing::debug!(
                "[NRA] feasible-set update: {} blocked, {} fixed, {} narrowed (total {} vars tracked)",
                self.blocked_vars.len(),
                self.fixed_vars.len(),
                self.feasible_sets
                    .len()
                    .saturating_sub(self.blocked_vars.len())
                    .saturating_sub(self.fixed_vars.len()),
                self.feasible_sets.len(),
            );
        }
    }

    /// Check if the feasible-set look-ahead indicates a path case (non-empty
    /// intersection) and return a suggested value for the first narrowed variable.
    ///
    /// clauseSMT Technique 1: after conflict analysis, if the intersection of
    /// the current feasible set with the new lemma's feasible set is non-empty,
    /// we have a "path case" — select a value from the intersection to guide
    /// literal decisions.
    pub(crate) fn feasible_set_look_ahead(&self) -> Option<(TermId, BigRational)> {
        for (&var, fs) in &self.feasible_sets {
            if !fs.is_empty() {
                if let Some(val) = fs.pick_value() {
                    // Only suggest for variables that don't already have a model value
                    if self.var_value(var).is_none() {
                        return Some((var, val));
                    }
                }
            }
        }
        None
    }

    /// Reset feasible-set tracking state. Called on push/pop/reset.
    pub(crate) fn reset_feasible_sets(&mut self) {
        self.feasible_sets.clear();
        self.blocked_vars.clear();
        self.fixed_vars.clear();
    }
}

/// Sign of a rational as an ordering against zero.
fn sign_of(r: &BigRational) -> Ordering {
    if r.is_zero() {
        Ordering::Equal
    } else if r.is_positive() {
        Ordering::Greater
    } else {
        Ordering::Less
    }
}

/// Sign of a product from the signs of its factors.
fn mul_sign(a: Ordering, b: Ordering) -> Ordering {
    match (a, b) {
        (Ordering::Equal, _) | (_, Ordering::Equal) => Ordering::Equal,
        (Ordering::Greater, Ordering::Greater) | (Ordering::Less, Ordering::Less) => {
            Ordering::Greater
        }
        _ => Ordering::Less,
    }
}

/// Flip a comparison operator (swap operand sides).
fn flip_cmp(cmp: &str) -> &'static str {
    match cmp {
        ">=" => "<=",
        ">" => "<",
        "<=" => ">=",
        "<" => ">",
        "=" => "=",
        "distinct" | "!=" => "distinct",
        _ => "=", // Unknown comparison: conservative fallback
    }
}

/// Negate a comparison operator.
fn negate_cmp(cmp: &str) -> &'static str {
    match cmp {
        ">=" => "<",
        ">" => "<=",
        "<=" => ">",
        "<" => ">=",
        "=" => "distinct",
        "distinct" | "!=" => "=",
        _ => "distinct", // Unknown comparison: conservative fallback
    }
}

/// Evaluate a constant comparison: value [cmp] target.
fn eval_constant_cmp(cmp: &str, value: &BigRational, target: &BigRational) -> bool {
    match cmp {
        ">=" => value >= target,
        ">" => value > target,
        "<=" => value <= target,
        "<" => value < target,
        "=" => value == target,
        "distinct" | "!=" => value != target,
        _ => false,
    }
}

#[cfg(test)]
#[path = "nlsat/tests.rs"]
mod tests;
