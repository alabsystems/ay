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
use num_rational::BigRational;
use num_traits::{One, Zero};

/// Capacity-hint clamp for per-monomial scratch vectors: monomial factor
/// counts are small in practice, and larger ones just grow past the hint.
const MAX_PREALLOC_MONOMIAL_FACTORS: usize = 64;

/// A tracked monomial representing a nonlinear product.
///
/// The exact invariant is `value(aux_var) == coeff * product(value(vars))`.
/// Constant factors must remain explicit because the term store flattens
/// products such as `(* x (* y (- 2)))` into one scaled product node.
#[derive(Debug, Clone)]
pub struct Monomial {
    /// Variables in the product (sorted for canonical form).
    pub vars: Vec<TermId>,
    /// Auxiliary variable representing this product's value.
    pub aux_var: TermId,
    /// Degree of the monomial (number of factors).
    pub degree: usize,
    /// Non-zero constant factor relating the auxiliary term to the bare product.
    pub coeff: BigRational,
}

impl Monomial {
    /// Create an unscaled monomial from variables and auxiliary variable.
    pub fn new(vars: Vec<TermId>, aux_var: TermId) -> Self {
        Self::new_scaled(vars, aux_var, BigRational::one())
    }

    /// Create a monomial satisfying `aux_var == coeff * product(vars)`.
    pub fn new_scaled(vars: Vec<TermId>, aux_var: TermId, coeff: BigRational) -> Self {
        debug_assert!(
            !coeff.is_zero(),
            "a zero-scaled product does not constrain its variable product"
        );
        let degree = vars.len();
        Self {
            vars,
            aux_var,
            degree,
            coeff,
        }
    }

    /// Whether the auxiliary term carries a non-unit constant factor.
    pub fn is_scaled(&self) -> bool {
        !self.coeff.is_one()
    }

    /// Sign of the non-zero coefficient.
    pub fn coeff_sign(&self) -> i32 {
        if self.coeff < BigRational::zero() {
            -1
        } else {
            1
        }
    }

    /// Recover the bare product value from an auxiliary-term value.
    pub fn product_from_aux(&self, aux_value: &BigRational) -> BigRational {
        aux_value / &self.coeff
    }

    /// Compute the auxiliary-term value from a bare product value.
    pub fn aux_from_product(&self, product: &BigRational) -> BigRational {
        &self.coeff * product
    }

    /// Check if this is a binary product (x*y).
    pub fn is_binary(&self) -> bool {
        self.degree == 2
    }

    /// Check if this is a square (x*x).
    pub fn is_square(&self) -> bool {
        self.degree == 2 && matches!(self.vars.as_slice(), [x, y, ..] if x == y)
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
    let mut negative = false;
    for &s in factor_signs {
        if s == 0 {
            return 0;
        }
        negative ^= s < 0;
    }
    if negative {
        -1
    } else {
        1
    }
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
        TermData::App(Symbol::Named(name), args) => {
            let &[lhs, rhs] = args.as_slice() else {
                return None;
            };
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

/// The rational value of `term` if it is a numeric literal, else `None`.
///
/// Handles `Int` and `Rational` literals and unary negation of either — SMT-LIB
/// writes a negative literal as `(- 2)`, which is an `App`, not a `Const`.
pub fn constant_value_of(terms: &TermStore, term: TermId) -> Option<BigRational> {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::App(Symbol::Named(name), args) if name == "-" => match args.as_slice() {
            &[arg] => constant_value_of(terms, arg).map(|c| -c),
            _ => None,
        },
        _ => None,
    }
}

/// Product of all literal factors of a multiplication term, or one otherwise.
pub fn constant_factor_of(terms: &TermStore, term: TermId) -> BigRational {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "*" => args
            .iter()
            .filter_map(|&arg| constant_value_of(terms, arg))
            .fold(BigRational::one(), |product, factor| product * factor),
        _ => BigRational::one(),
    }
}

/// Mirror a sign relation after multiplication by a negative coefficient.
pub fn mirror_sign_constraint(constraint: SignConstraint) -> SignConstraint {
    match constraint {
        SignConstraint::Positive => SignConstraint::Negative,
        SignConstraint::Negative => SignConstraint::Positive,
        SignConstraint::Zero => SignConstraint::Zero,
        SignConstraint::NonNegative => SignConstraint::NonPositive,
        SignConstraint::NonPositive => SignConstraint::NonNegative,
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
) -> Option<Vec<TermId>> {
    // The keyed constraint is about the bare product, while `subject` denotes
    // `coeff * product`. A negative coefficient mirrors every order relation.
    let mut recorded_monomial = None;
    if let Some(vars) = aux_to_monomial.get(&subject).cloned() {
        let coeff = constant_factor_of(terms, subject);
        debug_assert!(
            !coeff.is_zero(),
            "zero-scaled terms must never be registered as monomials"
        );
        if !coeff.is_zero() {
            let bare_constraint = if coeff < BigRational::zero() {
                mirror_sign_constraint(constraint)
            } else {
                constraint
            };
            sign_constraints
                .entry(vars.clone())
                .or_default()
                .push((bare_constraint, assertion));
            recorded_monomial = Some(vars);
        }
    }
    if matches!(terms.get(subject), TermData::Var(_, _)) {
        var_sign_constraints
            .entry(subject)
            .or_default()
            .push((constraint, assertion));
    }
    recorded_monomial
}

/// Check whether a monomial has all variables appearing an even number of times.
pub fn is_even_degree_monomial(mon: &Monomial) -> bool {
    let mut odd: HashMap<TermId, bool> = Default::default();
    for &v in &mon.vars {
        let parity = odd.entry(v).or_default();
        *parity = !*parity;
    }
    odd.values().all(|&is_odd| !is_odd)
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
        let mut factor_signs =
            Vec::with_capacity(mon.vars.len().min(MAX_PREALLOC_MONOMIAL_FACTORS));
        let mut factor_assertions =
            Vec::with_capacity(mon.vars.len().min(MAX_PREALLOC_MONOMIAL_FACTORS));
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
                let mut conflict =
                    Vec::with_capacity(relevant.len().min(MAX_PREALLOC_MONOMIAL_FACTORS));
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
pub fn propagate_product_signs<'a>(
    products: impl IntoIterator<Item = &'a Monomial>,
    var_sign_constraints: &mut HashMap<TermId, Vec<(SignConstraint, TermId)>>,
) {
    let mut derived: Vec<(TermId, SignConstraint, TermId)> = Vec::new();
    for mon in products {
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
            let constraint = match (product_sign(&[xs, ys]), mon.coeff_sign() < 0) {
                (0, _) => SignConstraint::Zero,
                (1, false) | (-1, true) => SignConstraint::Positive,
                (1, true) | (-1, false) => SignConstraint::Negative,
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

/// Propagate signs for the ordinary one-representative-per-key map.
pub fn propagate_monomial_signs(
    monomials: &HashMap<Vec<TermId>, Monomial>,
    var_sign_constraints: &mut HashMap<TermId, Vec<(SignConstraint, TermId)>>,
) {
    propagate_product_signs(monomials.values(), var_sign_constraints);
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
#[path = "nonlinear_tests.rs"]
mod tests;
