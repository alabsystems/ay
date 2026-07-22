// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Decomposed Farkas interpolation via null-space matrix decomposition.
//!
//! Ported from OpenSMT's `FarkasInterpolator.cc` (Gaussian elimination, RREF,
//! null-space basis, non-negative decomposition). Given Farkas coefficients that
//! prove `sum(wi * Ci) <= negative`, the decomposition projects away A-local
//! variables by partitioning constraints into shared-only (standalone conjuncts)
//! and mixed (matrix decomposition via null-space basis).
//!
//! Reference: `reference/golem/build/_deps/opensmt-src/src/tsolvers/lasolver/FarkasInterpolator.cc`

mod matrix;

use self::matrix::Matrix;
use self::matrix::{
    ensure_non_negative_decomposition, gaussian_elimination, get_alphas, get_null_basis,
    get_pivot_cols_bitmap, is_decomposition, matrix_nullity, to_reduced_row_echelon_form,
};
use crate::farkas::LinearConstraint;
use crate::proof_interpolation::{build_linear_inequality, iuc_trace_enabled};
use crate::ChcExpr;
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use num_rational::Rational64;
use std::sync::atomic::{AtomicUsize, Ordering};

/// IUC trace for decomposition telemetry (mirrors OpenSMT FarkasInterpolator stats).
macro_rules! decomp_trace {
    ($($arg:tt)*) => {
        if iuc_trace_enabled() {
            safe_eprintln!("[DECOMP] {}", format!($($arg)*));
        }
    };
}

#[derive(Debug, Clone, Copy, Default)]
struct DecompositionStats {
    opportunities: usize,
    decomposed: usize,
    non_trivial_basis: usize,
    fallback_to_standard: usize,
}

static DECOMP_OPPORTUNITIES: AtomicUsize = AtomicUsize::new(0);
static DECOMP_DECOMPOSED: AtomicUsize = AtomicUsize::new(0);
static DECOMP_NON_TRIVIAL_BASIS: AtomicUsize = AtomicUsize::new(0);
static DECOMP_FALLBACK_TO_STANDARD: AtomicUsize = AtomicUsize::new(0);

fn bump_stat(counter: &AtomicUsize) {
    counter.fetch_add(1, Ordering::Relaxed);
}

fn decomp_stats_snapshot() -> DecompositionStats {
    DecompositionStats {
        opportunities: DECOMP_OPPORTUNITIES.load(Ordering::Relaxed),
        decomposed: DECOMP_DECOMPOSED.load(Ordering::Relaxed),
        non_trivial_basis: DECOMP_NON_TRIVIAL_BASIS.load(Ordering::Relaxed),
        fallback_to_standard: DECOMP_FALLBACK_TO_STANDARD.load(Ordering::Relaxed),
    }
}

fn sum_inequalities(constraints: &[LinearConstraint], coeffs: &[Rational64]) -> Option<ChcExpr> {
    if constraints.len() != coeffs.len() || constraints.is_empty() {
        return None;
    }

    let mut sum_coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
    let mut sum_bound = Rational64::from_integer(0);
    let mut sum_strict = false;

    for (constraint, coeff) in constraints.iter().zip(coeffs.iter()) {
        if *coeff == Rational64::from_integer(0) {
            continue;
        }
        sum_strict |= constraint.strict;
        sum_bound += *coeff * constraint.bound;
        for (var, c) in &constraint.coeffs {
            // Avoid String clone when key already exists (#2956 Finding 6).
            if let Some(entry) = sum_coeffs.get_mut(var) {
                *entry += *coeff * *c;
            } else {
                sum_coeffs.insert(var.clone(), *coeff * *c);
            }
        }
    }

    build_linear_inequality(&sum_coeffs, sum_bound, sum_strict)
}

/// Decomposed Farkas interpolation: partition constraints into shared-only
/// (standalone conjuncts) and mixed-variable (null-space basis decomposition).
///
/// Returns `None` if decomposition fails (e.g., non-negative repair impossible).
pub(crate) fn decomposed_farkas_interpolant(
    constraints: &[LinearConstraint],
    weights: &[Rational64],
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    if constraints.len() != weights.len() || constraints.is_empty() {
        return None;
    }

    let mut interpolant_parts: Vec<ChcExpr> = Vec::new();
    let mut with_locals_constraints: Vec<LinearConstraint> = Vec::new();
    let mut with_locals_weights: Vec<Rational64> = Vec::new();
    let mut local_var_set: FxHashSet<String> = FxHashSet::default();

    for (constraint, weight) in constraints.iter().zip(weights.iter()) {
        if *weight == Rational64::from_integer(0) {
            continue;
        }

        let mut has_local = false;
        for var in constraint.coeffs.keys() {
            if !shared_vars.contains(var) {
                has_local = true;
                local_var_set.insert(var.clone());
            }
        }
        if has_local {
            with_locals_constraints.push(constraint.clone());
            with_locals_weights.push(*weight);
        } else {
            let expr =
                build_linear_inequality(&constraint.coeffs, constraint.bound, constraint.strict)?;
            if !matches!(expr, ChcExpr::Bool(true | false)) {
                interpolant_parts.push(expr);
            }
        }
    }

    let standalone_count = interpolant_parts.len();
    decomp_trace!(
        "partition: {} standalone, {} with-locals, {} total constraints",
        standalone_count,
        with_locals_constraints.len(),
        constraints.len()
    );

    if !with_locals_constraints.is_empty() {
        bump_stat(&DECOMP_OPPORTUNITIES);
        let mut recorded_standard_fallback = false;
        let mut push_standard_with_locals = || -> Option<()> {
            if !recorded_standard_fallback {
                bump_stat(&DECOMP_FALLBACK_TO_STANDARD);
                recorded_standard_fallback = true;
            }
            let expr = sum_inequalities(&with_locals_constraints, &with_locals_weights)?;
            if matches!(expr, ChcExpr::Bool(true | false)) {
                return Some(());
            }
            let has_non_shared = expr.vars().iter().any(|v| !shared_vars.contains(&v.name));
            if has_non_shared {
                decomp_trace!(
                    "fallback-to-standard: sum kept local vars, preserving standalone-only parts"
                );
            } else {
                interpolant_parts.push(expr);
            }
            Some(())
        };

        let mut local_vars: Vec<String> = local_var_set.into_iter().collect();
        local_vars.sort();

        let mut local_var_index: FxHashMap<String, usize> = FxHashMap::default();
        for (idx, var) in local_vars.iter().enumerate() {
            local_var_index.insert(var.clone(), idx);
        }

        let rows = local_vars.len();
        let cols = with_locals_constraints.len();
        if rows == 0 || cols == 0 {
            return None;
        }

        let mut matrix: Matrix = vec![vec![Rational64::from_integer(0); cols]; rows];
        for (col, constraint) in with_locals_constraints.iter().enumerate() {
            for (var, coeff) in &constraint.coeffs {
                if let Some(row) = local_var_index.get(var) {
                    matrix[*row][col] = *coeff;
                }
            }
        }

        gaussian_elimination(&mut matrix);
        let nullity = matrix_nullity(&matrix);
        if nullity <= 1 {
            decomp_trace!("fallback-to-standard: nullity={} <= 1", nullity);
            push_standard_with_locals()?;
        } else {
            bump_stat(&DECOMP_NON_TRIVIAL_BASIS);
            decomp_trace!("non-trivial-basis: nullity={}", nullity);
            to_reduced_row_echelon_form(&mut matrix);
            let mut basis = get_null_basis(&matrix);
            let pivot_cols = get_pivot_cols_bitmap(&matrix);
            let mut alphas = get_alphas(&with_locals_weights, &pivot_cols);

            if basis.is_empty() || alphas.len() != basis.len() {
                decomp_trace!(
                    "fallback-to-standard: invalid basis/alpha shape (basis={}, alphas={})",
                    basis.len(),
                    alphas.len()
                );
                push_standard_with_locals()?;
            } else if !is_decomposition(&basis, &alphas, &with_locals_weights) {
                // Some CHC paths feed synthetic/non-null-space weights. In that case,
                // decomposition algebra preconditions do not hold; fall back safely.
                decomp_trace!(
                    "fallback-to-standard: decomposition identity failed at alpha extraction"
                );
                push_standard_with_locals()?;
            } else if !ensure_non_negative_decomposition(
                &mut basis,
                &mut alphas,
                &with_locals_weights,
            ) {
                decomp_trace!("fallback-to-standard: non-negative repair failed");
                push_standard_with_locals()?;
            } else if !is_decomposition(&basis, &alphas, &with_locals_weights) {
                decomp_trace!(
                    "fallback-to-standard: decomposition identity failed after non-negative repair"
                );
                push_standard_with_locals()?;
            } else if basis
                .iter()
                .any(|vec| vec.iter().any(|c| *c < Rational64::from_integer(0)))
            {
                decomp_trace!("fallback-to-standard: basis remained negative after repair");
                push_standard_with_locals()?;
            } else {
                bump_stat(&DECOMP_DECOMPOSED);
                for base in basis {
                    let expr = sum_inequalities(&with_locals_constraints, &base)?;
                    if !matches!(expr, ChcExpr::Bool(true | false)) {
                        interpolant_parts.push(expr);
                    }
                }
            }
        }

        let stats = decomp_stats_snapshot();
        decomp_trace!(
            "stats: opportunities={}, decomposed={}, non-trivial-basis={}, fallback-to-standard={}",
            stats.opportunities,
            stats.decomposed,
            stats.non_trivial_basis,
            stats.fallback_to_standard
        );
    }

    if interpolant_parts.is_empty() {
        return None;
    }

    let interpolant = ChcExpr::and_all(interpolant_parts);
    let vars: FxHashSet<String> = interpolant.vars().into_iter().map(|v| v.name).collect();
    if !vars.iter().all(|v| shared_vars.contains(v)) {
        return None;
    }

    if matches!(interpolant, ChcExpr::Bool(true | false)) {
        return None;
    }

    Some(interpolant)
}

#[cfg(test)]
mod tests;
