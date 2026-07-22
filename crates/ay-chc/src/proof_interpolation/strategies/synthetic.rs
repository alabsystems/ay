// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

/// Synthetic decomposed Farkas interpolation — heuristic fallback.
///
/// Unlike the proof-derived path in `combine_a_constraints` (which uses real Farkas
/// coefficients from an UNSAT certificate), this function assigns **uniform weights**
/// (all 1) and relies on the decomposition algebra + post-hoc Craig validation to
/// filter out unsound candidates.
///
/// Use only when the SMT solver produces no Farkas certificates (0 Farkas conflicts).
/// The result must be validated against A ⊨ I and I ∧ B UNSAT before use.
pub(crate) fn try_synthetic_decomposed_farkas(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    check_smt: &mut SmtContext,
) -> Option<ChcExpr> {
    // Parse A-side constraints as LinearConstraints, expanding equalities
    let mut linear: Vec<LinearConstraint> = Vec::new();
    for a in a_constraints {
        match a {
            // Equality: expand to <= and >=
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let left = (*args[0]).clone();
                let right = (*args[1]).clone();
                // a = b -> a <= b AND b <= a
                let le_expr = ChcExpr::le(left.clone(), right.clone());
                let ge_expr = ChcExpr::le(right, left);
                if let Some(lc) = parse_linear_constraint(&le_expr) {
                    linear.push(strengthen_strict_lia_constraint(lc));
                }
                if let Some(lc) = parse_linear_constraint(&ge_expr) {
                    linear.push(strengthen_strict_lia_constraint(lc));
                }
            }
            other => {
                if let Some(lc) = parse_linear_constraint(other) {
                    linear.push(strengthen_strict_lia_constraint(lc));
                }
            }
        }
    }

    if linear.is_empty() {
        return None;
    }

    let weights: Vec<Rational64> = vec![Rational64::from_integer(1); linear.len()];
    let interpolant = decomposed_farkas_interpolant(&linear, &weights, shared_vars)?;
    let a_conj = and_slice(a_constraints);
    let b_conj = and_slice(b_constraints);

    if verify_craig_properties(
        &interpolant,
        &a_conj,
        &b_conj,
        shared_vars,
        check_smt,
        "try_synthetic_decomposed_farkas",
    ) {
        Some(interpolant)
    } else {
        None
    }
}
