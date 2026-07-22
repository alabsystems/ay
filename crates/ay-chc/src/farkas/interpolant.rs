// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Craig interpolant computation from Farkas-derived linear constraints.
//!
//! Implements strategies for computing LIA interpolants from transition (A)
//! and bad state (B) constraints: negated B, Fourier-Motzkin elimination,
//! pairwise variable elimination, conjunctive shared constraints, and
//! single-bound conflicts.

use crate::engine_utils::check_sat_with_timeout;
use crate::interpolant_validation::is_valid_interpolant_with_check_sat;
use crate::proof_interpolation::rational64_abs;
use crate::smt::SmtContext;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use num_rational::Rational64;

use super::build_linear_inequality_sorted;
use super::linear::{
    checked_r64_add, checked_r64_mul, linear_constraint_to_int_bound,
    parse_linear_constraints_flat_any, parse_linear_constraints_split_eq_any, IntBound,
    LinearConstraint,
};
use super::normalize::normalize_constraint;

// Deadline-free convenience wrapper consumed only by the `#[cfg(test)]` re-export
// in `farkas/mod.rs` (used across `farkas/tests.rs`); kept as the public test-facing
// validation entry point over `is_valid_interpolant_deadline`.
#[allow(dead_code)]
pub(super) fn is_valid_interpolant(
    a: &ChcExpr,
    b: &ChcExpr,
    interpolant: &ChcExpr,
    shared_vars: &FxHashSet<String>,
    _smt: &mut SmtContext,
) -> bool {
    is_valid_interpolant_deadline(a, b, interpolant, shared_vars, None)
}

/// Candidate validation with the per-check 2s cap additionally clamped to the
/// caller's wall-clock deadline (inc-19): the strategy loops below validate
/// O(|B|) / O(|A|^2) candidates at up to 2 checks x 2s each, which overstayed
/// the IMC cascade budget by minutes on k>=2 unrollings. An expired deadline
/// fails the validation (sound: candidate is dropped, caller falls back).
fn is_valid_interpolant_deadline(
    a: &ChcExpr,
    b: &ChcExpr,
    interpolant: &ChcExpr,
    shared_vars: &FxHashSet<String>,
    deadline: Option<ay_core::time::Instant>,
) -> bool {
    // Use a 2s timeout for validation checks to prevent hangs in reachability
    // loops where interpolation is called repeatedly (#4823).
    let cap = std::time::Duration::from_secs(2);
    is_valid_interpolant_with_check_sat(a, b, interpolant, shared_vars, |query| {
        let timeout = match deadline {
            Some(deadline) => {
                let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
                if remaining.is_zero() {
                    return crate::smt::SmtResult::Unknown;
                }
                remaining.min(cap)
            }
            None => cap,
        };
        check_sat_with_timeout(query, timeout)
    })
}

/// True when the caller's deadline has expired (strategy loops bail).
fn deadline_expired(deadline: Option<ay_core::time::Instant>) -> bool {
    deadline.is_some_and(|d| ay_core::time::Instant::now() >= d)
}

/// Negate a comparison expression: `<=` → `>`, `>=` → `<`, `<` → `>=`, `>` → `<=`.
/// Equalities return None (negation is disequality, not useful as interpolant).
fn negate_comparison(expr: &ChcExpr) -> Option<ChcExpr> {
    match expr {
        ChcExpr::Op(op, args) if args.len() == 2 => {
            let neg_op = op.negate_comparison()?;
            // Skip Eq/Ne negation (disequalities aren't useful as interpolants)
            if matches!(op, ChcOp::Eq | ChcOp::Ne) {
                return None;
            }
            Some(ChcExpr::Op(neg_op, args.clone()))
        }
        _ => None,
    }
}

pub(super) fn try_pairwise_eliminate_non_shared(
    c1: &LinearConstraint,
    c2: &LinearConstraint,
    var_to_eliminate: &str,
    shared_vars: &FxHashSet<String>,
) -> Option<LinearConstraint> {
    let coeff2 = c2.coeffs.get(var_to_eliminate).copied()?;
    let coeff1 = c1.get_coeff(var_to_eliminate);
    if (coeff1 > Rational64::from_integer(0)) == (coeff2 > Rational64::from_integer(0)) {
        return None;
    }

    let w1 = rational64_abs(coeff2);
    let w2 = rational64_abs(coeff1);
    let combined_bound = checked_r64_add(
        checked_r64_mul(c1.bound, w1)?,
        checked_r64_mul(c2.bound, w2)?,
    )?;
    let mut combined = LinearConstraint::new(combined_bound, c1.strict || c2.strict);
    // Preserve the arithmetic domain so the emitted atom is correctly sorted
    // (#chc25-lra-convergence).
    combined.var_sort = LinearConstraint::merged_sort(c1, c2);

    for (v, &c) in &c1.coeffs {
        if v == var_to_eliminate {
            continue;
        }
        combined.set_coeff(v, checked_r64_mul(c, w1)?);
    }
    for (v, &c) in &c2.coeffs {
        if v == var_to_eliminate {
            continue;
        }
        let existing = combined.get_coeff(v);
        let term = checked_r64_mul(c, w2)?;
        combined.set_coeff(v, checked_r64_add(existing, term)?);
    }

    combined
        .coeffs
        .retain(|v, c| shared_vars.contains(v) && *c != Rational64::from_integer(0));

    if combined.coeffs.is_empty() {
        return None;
    }

    Some(combined)
}

/// Compute a LIA interpolant from transition (A) and bad state (B) constraints.
///
/// When A ∧ B is UNSAT, this computes an interpolant I such that:
/// - A ⊨ I (I is implied by A)
/// - I ∧ B is UNSAT (I is inconsistent with B)
/// - I uses only variables shared between A and B
///
/// This implements the Golem/Spacer approach where interpolants are used
/// as blocking lemmas in PDR instead of heuristic generalization.
///
/// # Arguments
/// * `a_constraints` - Constraints from the transition relation
/// * `b_constraints` - Constraints from the bad state (proof obligation)
/// * `shared_vars` - Variables that appear in both A and B (predicate variables)
///
/// # Returns
/// An interpolant expression if successful, None otherwise.
///
/// # Contracts
///
/// REQUIRES: `∧a_constraints ∧ ∧b_constraints` is UNSAT.
///
/// REQUIRES: `shared_vars` contains exactly the variables that appear in both
///           A and B partitions.
///
/// ENSURES: If `Some(I)` is returned:
///          1. A ⊨ I (I is implied by A - verified by SMT check)
///          2. I ∧ B is UNSAT (I blocks B - verified by SMT check)
///          3. vars(I) ⊆ shared_vars (I uses only shared variables)
///
/// ENSURES: `None` is returned if:
///          - No linear constraints can be parsed from A or B
///          - No interpolant strategy succeeds
///          - SMT validation fails for candidate interpolants
///
/// # Known Limitations
///
/// - Variables with rational coefficients in Farkas combination are silently
///   dropped, potentially producing unsound interpolants (#1025)
pub(crate) fn compute_interpolant(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    compute_interpolant_until(a_constraints, b_constraints, shared_vars, None)
}

/// Deadline-aware variant of [`compute_interpolant`] (inc-19): every strategy
/// loop checks the caller's wall-clock deadline and the per-candidate
/// validation timeout is clamped to the remaining window. `None` keeps the
/// legacy unbounded behavior byte-for-byte. Expiry returns `None` (the caller
/// falls back / reports Unknown) — a pure latency lever, never a wrong answer.
pub(crate) fn compute_interpolant_until(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    deadline: Option<ay_core::time::Instant>,
) -> Option<ChcExpr> {
    // Parse A-constraints as linear inequalities.
    // Equalities are split into both directions (a-b<=0 AND b-a<=0) to
    // enable FM elimination and conjunctive interpolants (Part of #966).
    // #chc25-lra-convergence: `_any` admits Real (LRA) constraints in addition
    // to Int, so the Farkas cascade is no longer starved on LRA-Lin queries.
    // Pure-LIA input is parsed byte-identically by the Int-first path.
    let a_linear: Vec<LinearConstraint> = a_constraints
        .iter()
        .flat_map(parse_linear_constraints_split_eq_any)
        .collect();

    // Parse B-constraints as linear inequalities
    let b_linear: Vec<LinearConstraint> = b_constraints
        .iter()
        .flat_map(parse_linear_constraints_flat_any)
        .collect();

    if a_linear.is_empty() || b_linear.is_empty() {
        return None;
    }

    let a = ChcExpr::and_all(a_constraints.iter().cloned());
    let b = ChcExpr::and_all(b_constraints.iter().cloned());

    // Strategy ordering: prefer relational (multi-variable) interpolants over
    // single-variable bounds. Multi-variable interpolants capture relationships
    // like A - 5*C >= -6 which are critical for multi-phase loop invariants.

    // Strategy 0: Negate a B-constraint as interpolant candidate.
    // If A implies NOT(B_i) for some B-constraint B_i, then NOT(B_i) is
    // a valid interpolant (it follows from A and contradicts B). This produces
    // interpolants that match the structure of the property being checked,
    // e.g., producing `x < 5*y` when B requires `x >= 5*y`.
    for b_expr in b_constraints {
        if deadline_expired(deadline) {
            return None;
        }
        let neg_b = negate_comparison(b_expr);
        if let Some(ref candidate) = neg_b {
            // Must only use shared variables
            let cand_vars = candidate
                .vars()
                .into_iter()
                .map(|v| v.name)
                .collect::<FxHashSet<String>>();
            if cand_vars.iter().all(|v| shared_vars.contains(v))
                && is_valid_interpolant_deadline(&a, &b, candidate, shared_vars, deadline)
            {
                return Some(candidate.clone());
            }
        }
    }

    // Strategy 1: Fourier-Motzkin elimination of non-shared variables.
    //
    // Project A's constraints onto the shared variables by iteratively
    // eliminating each non-shared variable. This produces derived bounds
    // on shared variables that may serve as relational interpolants.
    //
    // Critical for multi-phase problems (gj2007_m_1) where A implies
    // equalities on shared vars (a0=4, a2=1) and B requires relational
    // constraints (a0 >= 5*a2).
    if let Some(itp) = fourier_motzkin_interpolant(&a_linear, &a, &b, shared_vars, deadline) {
        return Some(itp);
    }

    // Strategy 2: Combine pairs of A-constraints via variable elimination
    // to derive a constraint that contradicts B
    let shared_a: Vec<&LinearConstraint> = a_linear
        .iter()
        .filter(|c| c.coeffs.keys().any(|v| shared_vars.contains(v)))
        .collect();

    if shared_a.len() >= 2 {
        for i in 0..shared_a.len() {
            if deadline_expired(deadline) {
                return None;
            }
            for j in (i + 1)..shared_a.len() {
                let c1 = shared_a[i];
                let c2 = shared_a[j];

                // Find a variable to eliminate
                // Sort keys for deterministic variable elimination order (#3060)
                let mut sorted_keys: Vec<_> = c1.coeffs.keys().collect();
                sorted_keys.sort_unstable();
                for var in sorted_keys {
                    if !shared_vars.contains(var) {
                        if let Some(coeff2) = c2.coeffs.get(var) {
                            let coeff1 = c1.get_coeff(var);
                            // Opposite signs allow elimination
                            if (coeff1 > Rational64::from_integer(0))
                                != (*coeff2 > Rational64::from_integer(0))
                            {
                                if let Some(combined) =
                                    try_pairwise_eliminate_non_shared(c1, c2, var, shared_vars)
                                {
                                    // i128-lockstep: scaling overflow → skip this
                                    // candidate (abstention, never a clamped expr).
                                    let Some(expr) = build_linear_inequality_sorted(
                                        &combined.coeffs,
                                        combined.bound,
                                        combined.strict,
                                        combined.var_sort.clone(),
                                    ) else {
                                        continue;
                                    };
                                    if is_valid_interpolant_deadline(
                                        &a,
                                        &b,
                                        &expr,
                                        shared_vars,
                                        deadline,
                                    ) {
                                        return Some(expr);
                                    }
                                    if deadline_expired(deadline) {
                                        return None;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Strategy 3: Conjunctive interpolant from shared-only A-constraints.
    // Collect all A-constraints that only involve shared variables and are
    // individually implied by A. Their conjunction may block B even when no
    // single constraint does. This handles cases like A implies x=4 ∧ y=1
    // and B requires x >= 5*y.
    {
        let mut shared_exprs: Vec<ChcExpr> = Vec::new();
        for a_c in &a_linear {
            if a_c.coeffs.keys().all(|v| shared_vars.contains(v)) && !a_c.coeffs.is_empty() {
                // i128-lockstep: scaling overflow → skip candidate (abstention).
                if let Some(expr) = build_linear_inequality_sorted(
                    &a_c.coeffs,
                    a_c.bound,
                    a_c.strict,
                    a_c.var_sort.clone(),
                ) {
                    shared_exprs.push(expr);
                }
            }
        }

        // Try single constraints first (cheapest validation)
        for expr in &shared_exprs {
            if deadline_expired(deadline) {
                return None;
            }
            if is_valid_interpolant_deadline(&a, &b, expr, shared_vars, deadline) {
                return Some(expr.clone());
            }
        }

        // Try conjunction of all shared constraints
        if shared_exprs.len() >= 2 {
            if deadline_expired(deadline) {
                return None;
            }
            let conj = ChcExpr::and_all(shared_exprs.iter().cloned());
            if is_valid_interpolant_deadline(&a, &b, &conj, shared_vars, deadline) {
                return Some(conj);
            }
        }
    }

    // Strategy 4: Single A-constraint that contradicts a single B-constraint
    // (simple bound conflicts). This strategy uses integer floor/ceil rounding
    // (`linear_constraint_to_int_bound`) and emits `Int`-sorted atoms, so it is
    // valid only over the integers. For LRA (Real) constraints it is skipped —
    // integer rounding is unsound over ℝ, and the exact-rational Strategies
    // 0-3 already cover the real domain (#chc25-lra-convergence).
    for a_c in &a_linear {
        if deadline_expired(deadline) {
            return None;
        }
        if matches!(a_c.var_sort, ChcSort::Real) {
            continue;
        }
        let (var_name, a_bound) = match linear_constraint_to_int_bound(a_c) {
            Some((var, bound)) if shared_vars.contains(&var) => (var, bound),
            _ => continue,
        };

        for b_c in &b_linear {
            if matches!(b_c.var_sort, ChcSort::Real) {
                continue;
            }
            let b_bound = match linear_constraint_to_int_bound(b_c) {
                Some((var, bound)) if var == var_name => bound,
                _ => continue,
            };

            match (a_bound, b_bound) {
                (IntBound::Upper(a_ub), IntBound::Lower(b_lb)) if b_lb > a_ub => {
                    let var = ChcVar::new(&var_name, ChcSort::Int);
                    let candidate = ChcExpr::le(ChcExpr::var(var), ChcExpr::Int(i128::from(a_ub)));
                    if is_valid_interpolant_deadline(&a, &b, &candidate, shared_vars, deadline) {
                        return Some(candidate);
                    }
                }
                (IntBound::Lower(a_lb), IntBound::Upper(b_ub)) if a_lb > b_ub => {
                    let var = ChcVar::new(&var_name, ChcSort::Int);
                    let candidate = ChcExpr::ge(ChcExpr::var(var), ChcExpr::Int(i128::from(a_lb)));
                    if is_valid_interpolant_deadline(&a, &b, &candidate, shared_vars, deadline) {
                        return Some(candidate);
                    }
                }
                _ => {}
            }
        }
    }

    None
}

/// Fourier-Motzkin variable elimination to project A's constraints
/// onto the shared variable space.
///
/// Given linear constraints from A, eliminate all non-shared variables
/// one by one. Each elimination step combines pairs of constraints where
/// the eliminated variable has opposite signs, producing a new constraint
/// without that variable. After all non-shared variables are eliminated,
/// the remaining constraints involve only shared variables and are valid
/// interpolants (they follow from A and can contradict B).
fn fourier_motzkin_interpolant(
    a_linear: &[LinearConstraint],
    a_formula: &ChcExpr,
    b_formula: &ChcExpr,
    shared_vars: &FxHashSet<String>,
    deadline: Option<ay_core::time::Instant>,
) -> Option<ChcExpr> {
    // Collect all non-shared variables that appear in A
    let mut non_shared: Vec<String> = Vec::new();
    for c in a_linear {
        for var in c.coeffs.keys() {
            if !shared_vars.contains(var) && !non_shared.contains(var) {
                non_shared.push(var.clone());
            }
        }
    }

    non_shared.sort_unstable(); // Deterministic elimination order (#3060)

    if non_shared.is_empty() {
        return None; // All variables are shared, no elimination needed
    }

    // Start with A's constraints
    let mut constraints: Vec<LinearConstraint> = a_linear.to_vec();

    // Eliminate each non-shared variable
    for var_to_eliminate in &non_shared {
        let mut pos: Vec<LinearConstraint> = Vec::new(); // coeff > 0
        let mut neg: Vec<LinearConstraint> = Vec::new(); // coeff < 0
        let mut neutral: Vec<LinearConstraint> = Vec::new(); // coeff = 0

        for c in &constraints {
            let coeff = c.get_coeff(var_to_eliminate);
            if coeff > Rational64::from_integer(0) {
                pos.push(c.clone());
            } else if coeff < Rational64::from_integer(0) {
                neg.push(c.clone());
            } else {
                neutral.push(c.clone());
            }
        }

        // Combine each (pos, neg) pair to eliminate the variable
        let mut new_constraints = neutral;

        // Limit combinatorial explosion: at most 20 derived constraints per step
        let max_derived = 20;
        let mut derived = 0;

        for p in &pos {
            for n in &neg {
                if derived >= max_derived {
                    break;
                }

                let p_coeff = p.get_coeff(var_to_eliminate); // > 0
                let n_coeff = rational64_abs(n.get_coeff(var_to_eliminate)); // make positive

                // Combine: n_coeff * p + p_coeff * n (eliminates var)
                // Use checked arithmetic to skip pairs that overflow.
                let bound_term1 = match checked_r64_mul(p.bound, n_coeff) {
                    Some(v) => v,
                    None => continue,
                };
                let bound_term2 = match checked_r64_mul(n.bound, p_coeff) {
                    Some(v) => v,
                    None => continue,
                };
                let combined_bound = match checked_r64_add(bound_term1, bound_term2) {
                    Some(v) => v,
                    None => continue,
                };
                let mut combined = LinearConstraint::new(combined_bound, p.strict || n.strict);
                // Preserve the arithmetic domain through elimination
                // (#chc25-lra-convergence).
                combined.var_sort = LinearConstraint::merged_sort(p, n);
                let mut overflow = false;

                for (v, &c) in &p.coeffs {
                    if v == var_to_eliminate {
                        continue;
                    }
                    match checked_r64_mul(c, n_coeff) {
                        Some(val) => combined.set_coeff(v, val),
                        None => {
                            overflow = true;
                            break;
                        }
                    }
                }
                if overflow {
                    continue;
                }
                for (v, &c) in &n.coeffs {
                    if v == var_to_eliminate {
                        continue;
                    }
                    let existing = combined.get_coeff(v);
                    match checked_r64_mul(c, p_coeff).and_then(|t| checked_r64_add(existing, t)) {
                        Some(val) => combined.set_coeff(v, val),
                        None => {
                            overflow = true;
                            break;
                        }
                    }
                }
                if overflow {
                    continue;
                }

                // Normalize: divide by GCD of all coefficients and bound
                let combined = normalize_constraint(combined);

                new_constraints.push(combined);
                derived += 1;
            }
            if derived >= max_derived {
                break;
            }
        }

        constraints = new_constraints;
    }

    // Now `constraints` only involve shared variables.
    // Try each as an interpolant candidate.
    for c in &constraints {
        if deadline_expired(deadline) {
            return None;
        }
        if c.coeffs.is_empty() {
            continue; // Trivial constraint (just a constant bound)
        }

        // All remaining variables should be shared
        if !c.coeffs.keys().all(|v| shared_vars.contains(v)) {
            continue;
        }

        // i128-lockstep: scaling overflow → skip candidate (abstention).
        let Some(expr) =
            build_linear_inequality_sorted(&c.coeffs, c.bound, c.strict, c.var_sort.clone())
        else {
            continue;
        };

        // Validate: A => expr and expr ∧ B is UNSAT
        if is_valid_interpolant_deadline(a_formula, b_formula, &expr, shared_vars, deadline) {
            return Some(expr);
        }
    }

    None
}
