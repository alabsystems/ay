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
use num_traits::{One, Zero};

use crate::feasible_set::{FeasibilityClass, FeasibleSet};
use crate::NraSolver;

impl NraSolver<'_> {
    /// Compute the feasible set for a comparison atom `lhs cmp rhs` where one
    /// side involves a monomial with a single free variable.
    ///
    /// For a constraint like `x * y >= 5` where y is assigned to 3, this becomes
    /// `x >= 5/3`, giving feasible set [5/3, +inf).
    ///
    /// This is a simplified version of full NLSAT root isolation: we handle
    /// the common case of linear-in-one-variable constraints after partial
    /// evaluation. Full CAD root isolation is deferred to #8335.
    pub(crate) fn compute_literal_feasible_set(
        &self,
        atom: TermId,
        value: bool,
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
        let lhs_val = self.eval_to_rational(lhs);
        let rhs_val = self.eval_to_rational(rhs);

        // If both sides are fully evaluated, the feasible set is trivial.
        if lhs_val.is_some() && rhs_val.is_some() {
            return None;
        }

        // Try linear-in-one-variable: a*x + b cmp c
        // where a, b, c are known rational values and x is the free variable.
        if let Some((free_var, coeff, constant)) = self.extract_linear_univariate(lhs) {
            if let Some(rhs_v) = rhs_val {
                // a*x + b cmp rhs_v => a*x cmp (rhs_v - b)
                let target = rhs_v - &constant;
                return Some((
                    free_var,
                    self.feasible_set_from_linear(cmp_name, value, &coeff, &target),
                ));
            }
        }

        if let Some((free_var, coeff, constant)) = self.extract_linear_univariate(rhs) {
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
    fn eval_to_rational(&self, term: TermId) -> Option<BigRational> {
        self.term_value(term)
    }

    /// Extract a linear expression in one variable from a term: a*x + b.
    /// Returns (free_var, coefficient a, constant b).
    ///
    /// Handles simple cases:
    /// - Variable x: (x, 1, 0)
    /// - Multiplication: c * x where c is known -> (x, c, 0)
    /// - Addition: expr1 + expr2 where one side has a free variable
    /// - Subtraction: expr1 - expr2
    fn extract_linear_univariate(
        &self,
        term: TermId,
    ) -> Option<(TermId, BigRational, BigRational)> {
        match self.terms.get(term) {
            TermData::Var(_, _) => {
                // Check if this variable has a value in the model
                if self.var_value(term).is_some() {
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
                        if let Some(c) = self.eval_to_rational(a0) {
                            if let Some((var, inner_coeff, inner_const)) =
                                self.extract_linear_univariate(a1)
                            {
                                return Some((var, &c * &inner_coeff, &c * &inner_const));
                            }
                        }
                        if let Some(c) = self.eval_to_rational(a1) {
                            if let Some((var, inner_coeff, inner_const)) =
                                self.extract_linear_univariate(a0)
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
                        if let Some(c) = self.eval_to_rational(a0) {
                            if let Some((var, coeff, constant)) = self.extract_linear_univariate(a1)
                            {
                                return Some((var, coeff, constant + c));
                            }
                        }
                        if let Some(c) = self.eval_to_rational(a1) {
                            if let Some((var, coeff, constant)) = self.extract_linear_univariate(a0)
                            {
                                return Some((var, coeff, constant + c));
                            }
                        }
                        None
                    }
                    "-" if args.len() == 2 => {
                        let a0 = args[0];
                        let a1 = args[1];
                        if let Some(c) = self.eval_to_rational(a0) {
                            if let Some((var, coeff, constant)) = self.extract_linear_univariate(a1)
                            {
                                return Some((var, -coeff, c - constant));
                            }
                        }
                        if let Some(c) = self.eval_to_rational(a1) {
                            if let Some((var, coeff, constant)) = self.extract_linear_univariate(a0)
                            {
                                return Some((var, coeff, constant - c));
                            }
                        }
                        None
                    }
                    "-" if args.len() == 1 => {
                        // Unary negation
                        let a0 = args[0];
                        if let Some((var, coeff, constant)) = self.extract_linear_univariate(a0) {
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
        for i in 0..self.asserted.len() {
            let (atom, value) = self.asserted[i];
            if let Some((free_var, lit_fs)) = self.compute_literal_feasible_set(atom, value) {
                self.feasible_set_count += 1;
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
                self.feasible_sets.len() - self.blocked_vars.len() - self.fixed_vars.len(),
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
mod tests {
    use super::*;
    use num_rational::BigRational;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(n.into())
    }

    #[test]
    fn test_flip_cmp() {
        assert_eq!(flip_cmp(">="), "<=");
        assert_eq!(flip_cmp(">"), "<");
        assert_eq!(flip_cmp("<="), ">=");
        assert_eq!(flip_cmp("<"), ">");
        assert_eq!(flip_cmp("="), "=");
    }

    #[test]
    fn test_negate_cmp() {
        assert_eq!(negate_cmp(">="), "<");
        assert_eq!(negate_cmp(">"), "<=");
        assert_eq!(negate_cmp("<="), ">");
        assert_eq!(negate_cmp("<"), ">=");
        assert_eq!(negate_cmp("="), "distinct");
        assert_eq!(negate_cmp("distinct"), "=");
    }

    #[test]
    fn test_eval_constant_cmp() {
        assert!(eval_constant_cmp(">=", &rat(5), &rat(3)));
        assert!(eval_constant_cmp(">=", &rat(3), &rat(3)));
        assert!(!eval_constant_cmp(">=", &rat(2), &rat(3)));
        assert!(eval_constant_cmp("=", &rat(3), &rat(3)));
        assert!(!eval_constant_cmp("=", &rat(2), &rat(3)));
    }

    #[test]
    fn test_feasible_set_from_linear_ge() {
        // x >= 5 => [5, +inf)
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear(">=", true, &rat(1), &rat(5));
        assert!(fs.contains_point(&rat(5)));
        assert!(fs.contains_point(&rat(10)));
        assert!(!fs.contains_point(&rat(4)));
    }

    #[test]
    fn test_feasible_set_from_linear_lt() {
        // x < 3 => (-inf, 3)
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear("<", true, &rat(1), &rat(3));
        assert!(fs.contains_point(&rat(2)));
        assert!(!fs.contains_point(&rat(3)));
        assert!(!fs.contains_point(&rat(4)));
    }

    #[test]
    fn test_feasible_set_from_linear_negative_coeff() {
        // -2*x >= 6 => x <= -3 => (-inf, -3]
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear(">=", true, &rat(-2), &rat(6));
        assert!(fs.contains_point(&rat(-3)));
        assert!(fs.contains_point(&rat(-10)));
        assert!(!fs.contains_point(&rat(-2)));
    }

    #[test]
    fn test_feasible_set_from_linear_negated() {
        // NOT(x >= 5) => x < 5 => (-inf, 5)
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear(">=", false, &rat(1), &rat(5));
        assert!(fs.contains_point(&rat(4)));
        assert!(!fs.contains_point(&rat(5)));
    }

    #[test]
    fn test_feasible_set_from_linear_equality() {
        // x = 7 => {7}
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear("=", true, &rat(1), &rat(7));
        assert!(fs.contains_point(&rat(7)));
        assert!(!fs.contains_point(&rat(6)));
        assert_eq!(fs.is_singleton(), Some(rat(7)));
    }

    #[test]
    fn test_feasible_set_from_linear_disequality() {
        // x != 3 => (-inf, 3) U (3, +inf)
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear("distinct", true, &rat(1), &rat(3));
        assert!(!fs.contains_point(&rat(3)));
        assert!(fs.contains_point(&rat(2)));
        assert!(fs.contains_point(&rat(4)));
    }

    // ====== Additional NLSAT tests (#8460) ======

    /// Zero coefficient: 0*x >= 5 => 0 >= 5 is false => empty set.
    #[test]
    fn test_feasible_set_from_linear_zero_coeff_false() {
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear(">=", true, &rat(0), &rat(5));
        assert!(
            fs.is_empty(),
            "0 >= 5 is false, so feasible set should be empty"
        );
    }

    /// Zero coefficient: 0*x >= 0 => 0 >= 0 is true => full set.
    #[test]
    fn test_feasible_set_from_linear_zero_coeff_true() {
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear(">=", true, &rat(0), &rat(0));
        assert!(
            !fs.is_empty(),
            "0 >= 0 is true, so feasible set should be full"
        );
        assert!(fs.contains_point(&rat(42)));
        assert!(fs.contains_point(&rat(-42)));
    }

    /// Zero coefficient: 0*x > 0 => false => empty.
    #[test]
    fn test_feasible_set_from_linear_zero_coeff_strict_gt_false() {
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear(">", true, &rat(0), &rat(0));
        assert!(
            fs.is_empty(),
            "0 > 0 is false, so feasible set should be empty"
        );
    }

    /// Zero coefficient: 0*x = 0 => true => full.
    #[test]
    fn test_feasible_set_from_linear_zero_coeff_eq_true() {
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear("=", true, &rat(0), &rat(0));
        assert!(
            !fs.is_empty(),
            "0 = 0 is true, so feasible set should be full"
        );
    }

    /// Negated equality: NOT(x = 5) => x != 5 => (-inf,5) U (5,+inf).
    #[test]
    fn test_feasible_set_from_linear_negated_equality() {
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear("=", false, &rat(1), &rat(5));
        assert!(!fs.contains_point(&rat(5)));
        assert!(fs.contains_point(&rat(4)));
        assert!(fs.contains_point(&rat(6)));
    }

    /// Negated disequality: NOT(x != 3) => x = 3 => {3}.
    #[test]
    fn test_feasible_set_from_linear_negated_disequality() {
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear("distinct", false, &rat(1), &rat(3));
        assert!(fs.contains_point(&rat(3)));
        assert!(!fs.contains_point(&rat(2)));
        assert!(!fs.contains_point(&rat(4)));
        assert_eq!(fs.is_singleton(), Some(rat(3)));
    }

    /// Unknown comparator should conservatively return full set.
    #[test]
    fn test_feasible_set_from_linear_unknown_cmp() {
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear("???", true, &rat(1), &rat(5));
        assert!(!fs.is_empty(), "unknown comparator should produce full set");
        assert!(fs.contains_point(&rat(0)));
    }

    /// flip_cmp is its own inverse: flip(flip(x)) == x.
    #[test]
    fn test_flip_cmp_involution() {
        for cmp in &[">=", ">", "<=", "<", "=", "distinct"] {
            assert_eq!(
                flip_cmp(flip_cmp(cmp)),
                *cmp,
                "flip_cmp should be an involution for {cmp}"
            );
        }
    }

    /// negate_cmp is its own inverse: negate(negate(x)) == x.
    #[test]
    fn test_negate_cmp_involution() {
        for cmp in &[">=", ">", "<=", "<", "=", "distinct"] {
            assert_eq!(
                negate_cmp(negate_cmp(cmp)),
                *cmp,
                "negate_cmp should be an involution for {cmp}"
            );
        }
    }

    /// eval_constant_cmp covers all six operators.
    #[test]
    fn test_eval_constant_cmp_all_operators() {
        assert!(eval_constant_cmp(">", &rat(5), &rat(3)));
        assert!(!eval_constant_cmp(">", &rat(3), &rat(3)));
        assert!(eval_constant_cmp("<=", &rat(3), &rat(3)));
        assert!(eval_constant_cmp("<=", &rat(2), &rat(3)));
        assert!(!eval_constant_cmp("<=", &rat(4), &rat(3)));
        assert!(eval_constant_cmp("<", &rat(2), &rat(3)));
        assert!(!eval_constant_cmp("<", &rat(3), &rat(3)));
        assert!(eval_constant_cmp("distinct", &rat(1), &rat(2)));
        assert!(!eval_constant_cmp("distinct", &rat(2), &rat(2)));
        assert!(eval_constant_cmp("!=", &rat(1), &rat(2)));
    }

    /// Negative coefficient with negated literal:
    /// NOT(-3*x >= 6) => NOT(x <= -2) => x > -2 => (-2, +inf).
    #[test]
    fn test_feasible_set_from_linear_negative_coeff_negated() {
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear(">=", false, &rat(-3), &rat(6));
        // -3*x >= 6 => x <= -2, negation => x > -2
        assert!(!fs.contains_point(&rat(-2)));
        assert!(fs.contains_point(&rat(-1)));
        assert!(fs.contains_point(&rat(0)));
    }

    /// Fractional coefficient: (1/2)*x >= 3 => x >= 6.
    #[test]
    fn test_feasible_set_from_linear_fractional_coeff() {
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let half = BigRational::new(1.into(), 2.into());
        let fs = solver.feasible_set_from_linear(">=", true, &half, &rat(3));
        assert!(fs.contains_point(&rat(6)));
        assert!(fs.contains_point(&rat(100)));
        assert!(!fs.contains_point(&rat(5)));
    }

    /// x <= -10 => (-inf, -10].
    #[test]
    fn test_feasible_set_from_linear_le_negative() {
        let terms = ay_core::term::TermStore::new();
        let solver = NraSolver::new(&terms);
        let fs = solver.feasible_set_from_linear("<=", true, &rat(1), &rat(-10));
        assert!(fs.contains_point(&rat(-10)));
        assert!(fs.contains_point(&rat(-100)));
        assert!(!fs.contains_point(&rat(-9)));
    }
}
