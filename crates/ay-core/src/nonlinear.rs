// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared nonlinear arithmetic types for NIA and NRA theory solvers.
//!
//! Consolidation rationale: #7947 (simplify arithmetic mode/fallback sprawl).

// #8529: Use deterministic hash maps in all builds.
use crate::kani_compat::DetHashMap as HashMap;
use crate::term::{Constant, Symbol, TermData, TermId, TermStore};
use crate::TheoryLit;
use num_traits::Zero;

/// A tracked monomial representing a nonlinear product.
#[derive(Debug, Clone)]
pub struct Monomial {
    /// Variables in the product (sorted for canonical form).
    pub vars: Vec<TermId>,
    /// Auxiliary variable representing this product's value.
    pub aux_var: TermId,
    /// Degree of the monomial (number of factors).
    pub degree: usize,
}

impl Monomial {
    /// Create a new monomial from variables and auxiliary variable.
    pub fn new(vars: Vec<TermId>, aux_var: TermId) -> Self {
        let degree = vars.len();
        Self {
            vars,
            aux_var,
            degree,
        }
    }

    /// Check if this is a binary product (x*y).
    pub fn is_binary(&self) -> bool {
        self.degree == 2
    }

    /// Check if this is a square (x*x).
    pub fn is_square(&self) -> bool {
        self.degree == 2 && self.vars[0] == self.vars[1]
    }

    /// Get the first factor (for binary products).
    pub fn x(&self) -> Option<TermId> {
        self.vars.first().copied()
    }

    /// Get the second factor (for binary products).
    pub fn y(&self) -> Option<TermId> {
        if self.vars.len() >= 2 {
            Some(self.vars[1])
        } else {
            None
        }
    }
}

/// Sign constraint on a monomial or variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignConstraint {
    /// Must be positive (> 0).
    Positive,
    /// Must be negative (< 0).
    Negative,
    /// Must be zero (= 0).
    Zero,
    /// Must be non-negative (>= 0).
    NonNegative,
    /// Must be non-positive (<= 0).
    NonPositive,
}

/// Compute the sign of a product given factor signs.
pub fn product_sign(factor_signs: &[i32]) -> i32 {
    let mut sign = 1;
    for &s in factor_signs {
        if s == 0 {
            return 0;
        }
        sign *= s;
    }
    sign
}

/// Check if a sign constraint contradicts the expected sign.
pub fn sign_contradicts(constraint: SignConstraint, expected_sign: i32) -> bool {
    match constraint {
        SignConstraint::Positive => expected_sign <= 0,
        SignConstraint::Negative => expected_sign >= 0,
        SignConstraint::Zero => expected_sign != 0,
        SignConstraint::NonNegative => expected_sign < 0,
        SignConstraint::NonPositive => expected_sign > 0,
    }
}

/// Extract a definite sign value from a list of constraints.
pub fn sign_from_constraints(constraints: Option<&Vec<(SignConstraint, TermId)>>) -> Option<i32> {
    let constraints = constraints?;
    for (c, _) in constraints {
        match c {
            SignConstraint::Positive => return Some(1),
            SignConstraint::Negative => return Some(-1),
            SignConstraint::Zero => return Some(0),
            _ => {}
        }
    }
    None
}

/// Like [`sign_from_constraints`] but also returns the assertion TermId.
pub fn sign_from_constraints_with_assertion(
    constraints: Option<&Vec<(SignConstraint, TermId)>>,
) -> Option<(i32, TermId)> {
    let constraints = constraints?;
    for (c, assertion) in constraints {
        match c {
            SignConstraint::Positive => return Some((1, *assertion)),
            SignConstraint::Negative => return Some((-1, *assertion)),
            SignConstraint::Zero => return Some((0, *assertion)),
            _ => {}
        }
    }
    None
}

/// Check if a term is the constant zero (integer or rational).
pub fn is_zero_constant(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => n.is_zero(),
        TermData::Const(Constant::Rational(r)) => r.0.is_zero(),
        _ => false,
    }
}

/// Extract sign constraint from a comparison with zero.
pub fn extract_sign_constraint(
    terms: &TermStore,
    term: TermId,
    value: bool,
) -> Option<(TermId, SignConstraint)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
            let lhs = args[0];
            let rhs = args[1];
            let (subject, is_lhs) = if is_zero_constant(terms, rhs) {
                (lhs, true)
            } else if is_zero_constant(terms, lhs) {
                (rhs, false)
            } else {
                return None;
            };
            let constraint = match (name.as_str(), is_lhs, value) {
                (">", true, true)
                | (">=", false, false)
                | ("<", false, true)
                | ("<=", true, false) => SignConstraint::Positive,
                (">", false, true)
                | (">=", true, false)
                | ("<", true, true)
                | ("<=", false, false) => SignConstraint::Negative,
                (">", true, false)
                | (">=", false, true)
                | ("<", false, false)
                | ("<=", true, true) => SignConstraint::NonPositive,
                (">", false, false)
                | (">=", true, true)
                | ("<", true, false)
                | ("<=", false, true) => SignConstraint::NonNegative,
                ("=", _, true) => SignConstraint::Zero,
                _ => return None,
            };
            Some((subject, constraint))
        }
        _ => None,
    }
}

/// Record a sign constraint for a subject term (variable or monomial).
pub fn record_sign_constraint(
    terms: &TermStore,
    aux_to_monomial: &HashMap<TermId, Vec<TermId>>,
    sign_constraints: &mut HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>>,
    var_sign_constraints: &mut HashMap<TermId, Vec<(SignConstraint, TermId)>>,
    subject: TermId,
    constraint: SignConstraint,
    assertion: TermId,
) {
    if let Some(vars) = aux_to_monomial.get(&subject).cloned() {
        sign_constraints
            .entry(vars)
            .or_default()
            .push((constraint, assertion));
    }
    if matches!(terms.get(subject), TermData::Var(_, _)) {
        var_sign_constraints
            .entry(subject)
            .or_default()
            .push((constraint, assertion));
    }
}

/// Check whether a monomial has all variables appearing an even number of times.
pub fn is_even_degree_monomial(mon: &Monomial) -> bool {
    let mut counts: HashMap<TermId, usize> = Default::default();
    for &v in &mon.vars {
        *counts.entry(v).or_default() += 1;
    }
    counts.values().all(|&c| c % 2 == 0)
}

/// Check sign consistency for all monomials.
pub fn check_sign_consistency(
    monomials: &HashMap<Vec<TermId>, Monomial>,
    sign_constraints: &HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>>,
    var_sign_constraints: &HashMap<TermId, Vec<(SignConstraint, TermId)>>,
    asserted: &[(TermId, bool)],
    debug: bool,
) -> Option<Vec<TheoryLit>> {
    let mut sorted_sign: Vec<_> = sign_constraints.iter().collect();
    sorted_sign.sort_by_key(|(a, _)| *a);
    for (vars, constraints) in sorted_sign {
        let Some(mon) = monomials.get(vars) else {
            continue;
        };
        if is_even_degree_monomial(mon) {
            for (constraint, mon_assertion) in constraints {
                if sign_contradicts(*constraint, 1) && sign_contradicts(*constraint, 0) {
                    if debug {
                        crate::safe_eprintln!(
                            "[NL] Even-degree non-negativity conflict: {:?} constraint {:?}",
                            vars,
                            constraint
                        );
                    }
                    let conflict: Vec<TheoryLit> = asserted
                        .iter()
                        .filter(|&&(t, _)| t == *mon_assertion)
                        .map(|&(t, v)| TheoryLit { term: t, value: v })
                        .collect();
                    if !conflict.is_empty() {
                        return Some(conflict);
                    }
                    return Some(
                        asserted
                            .iter()
                            .map(|&(t, v)| TheoryLit { term: t, value: v })
                            .collect(),
                    );
                }
            }
        }
        let mut factor_signs = Vec::with_capacity(mon.vars.len());
        let mut factor_assertions = Vec::with_capacity(mon.vars.len());
        let mut all_known = true;
        for &var in &mon.vars {
            if let Some((sign, assertion)) =
                sign_from_constraints_with_assertion(var_sign_constraints.get(&var))
            {
                factor_signs.push(sign);
                factor_assertions.push(assertion);
            } else {
                all_known = false;
                break;
            }
        }
        if !all_known {
            continue;
        }
        let expected = product_sign(&factor_signs);
        for (constraint, mon_assertion) in constraints {
            if sign_contradicts(*constraint, expected) {
                if debug {
                    crate::safe_eprintln!(
                        "[NL] Sign conflict: factors={:?} expected={} constraint={:?}",
                        factor_signs,
                        expected,
                        constraint
                    );
                }
                let mut relevant = factor_assertions.clone();
                relevant.push(*mon_assertion);
                let mut conflict = Vec::with_capacity(relevant.len());
                for &(t, v) in asserted {
                    if relevant.contains(&t) {
                        conflict.push(TheoryLit { term: t, value: v });
                    }
                }
                if conflict.is_empty() {
                    return Some(
                        asserted
                            .iter()
                            .map(|&(t, v)| TheoryLit { term: t, value: v })
                            .collect(),
                    );
                }
                return Some(conflict);
            }
        }
    }
    None
}

/// Propagate sign information from factors to monomial auxiliary variables.
pub fn propagate_monomial_signs(
    monomials: &HashMap<Vec<TermId>, Monomial>,
    var_sign_constraints: &mut HashMap<TermId, Vec<(SignConstraint, TermId)>>,
) {
    let mut derived: Vec<(TermId, SignConstraint, TermId)> = Vec::new();
    for mon in monomials.values() {
        if !mon.is_binary() {
            continue;
        }
        if sign_from_constraints(var_sign_constraints.get(&mon.aux_var)).is_some() {
            continue;
        }
        let Some(x) = mon.x() else { continue };
        let Some(y) = mon.y() else { continue };
        let x_sign = sign_from_constraints_with_assertion(var_sign_constraints.get(&x));
        let y_sign = sign_from_constraints_with_assertion(var_sign_constraints.get(&y));
        if let (Some((xs, x_assertion)), Some((ys, _))) = (x_sign, y_sign) {
            let prod = product_sign(&[xs, ys]);
            let constraint = match prod {
                1 => SignConstraint::Positive,
                -1 => SignConstraint::Negative,
                0 => SignConstraint::Zero,
                _ => continue,
            };
            derived.push((mon.aux_var, constraint, x_assertion));
        }
    }
    for (aux_var, constraint, assertion) in derived {
        var_sign_constraints
            .entry(aux_var)
            .or_default()
            .push((constraint, assertion));
    }
}

/// Collect original factor variables from monomials that lack a definite sign.
pub fn vars_needing_model_sign(
    monomials: &HashMap<Vec<TermId>, Monomial>,
    aux_to_monomial: &HashMap<TermId, Vec<TermId>>,
    var_sign_constraints: &HashMap<TermId, Vec<(SignConstraint, TermId)>>,
) -> Vec<TermId> {
    let mut result: Vec<TermId> = Vec::new();
    for mon in monomials.values() {
        for &var in &mon.vars {
            if aux_to_monomial.contains_key(&var) {
                continue;
            }
            let has_definite_sign = var_sign_constraints.get(&var).is_some_and(|cs| {
                cs.iter().any(|(s, _)| {
                    matches!(
                        s,
                        SignConstraint::Positive | SignConstraint::Negative | SignConstraint::Zero
                    )
                })
            });
            if has_definite_sign {
                continue;
            }
            if !result.contains(&var) {
                result.push(var);
            }
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_product_sign_basic() {
        assert_eq!(product_sign(&[1, 1]), 1);
        assert_eq!(product_sign(&[1, -1]), -1);
        assert_eq!(product_sign(&[-1, -1]), 1);
        assert_eq!(product_sign(&[1, 0]), 0);
        assert_eq!(product_sign(&[0, -1]), 0);
    }

    #[test]
    fn test_sign_contradicts() {
        assert!(sign_contradicts(SignConstraint::Positive, 0));
        assert!(sign_contradicts(SignConstraint::Positive, -1));
        assert!(!sign_contradicts(SignConstraint::Positive, 1));
        assert!(sign_contradicts(SignConstraint::Negative, 0));
        assert!(sign_contradicts(SignConstraint::Negative, 1));
        assert!(!sign_contradicts(SignConstraint::Negative, -1));
        assert!(sign_contradicts(SignConstraint::Zero, 1));
        assert!(sign_contradicts(SignConstraint::Zero, -1));
        assert!(!sign_contradicts(SignConstraint::Zero, 0));
        assert!(sign_contradicts(SignConstraint::NonNegative, -1));
        assert!(!sign_contradicts(SignConstraint::NonNegative, 0));
        assert!(sign_contradicts(SignConstraint::NonPositive, 1));
        assert!(!sign_contradicts(SignConstraint::NonPositive, 0));
    }

    #[test]
    fn test_monomial_accessors() {
        let tid = |n: u32| TermId(n);
        let m = Monomial::new(vec![tid(1), tid(2)], tid(10));
        assert!(m.is_binary());
        assert!(!m.is_square());
        assert_eq!(m.x(), Some(tid(1)));
        assert_eq!(m.y(), Some(tid(2)));
        let sq = Monomial::new(vec![tid(3), tid(3)], tid(11));
        assert!(sq.is_binary());
        assert!(sq.is_square());
    }
}
