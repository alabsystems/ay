// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conditional affine invariant synthesis.
//!
//! Implements Phase 2 of parity-aware affine synthesis:
//! partition sampled models by `(z mod 2)` and compare affine kernels.
//!
//! See:
//! - the development design notes
//! - the development design notes

use crate::convex_closure::ConvexClosure;
use crate::expr::walk_linear_expr;
use crate::{ChcExpr, ChcOp, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ConditionalAffineInvariant {
    /// Coefficients for `vars` (same for both parity partitions).
    pub coefficients: Vec<i128>,
    /// Index of the parity variable `z` in `vars`.
    pub parity_var_idx: usize,
    /// Constant for the even partition (`z mod 2 = 0`).
    pub k_even: i128,
    /// Constant for the odd partition (`z mod 2 = 1`).
    pub k_odd: i128,
}

impl ConditionalAffineInvariant {
    /// Convert to an expression:
    /// `Σ coeff_i*var_i = k_even + (z mod 2) * (k_odd - k_even)`.
    pub(crate) fn to_expr(&self, vars: &[ChcVar]) -> ChcExpr {
        debug_assert_eq!(
            self.coefficients.len(),
            vars.len(),
            "coefficients/vars length mismatch"
        );
        debug_assert!(
            self.parity_var_idx < vars.len(),
            "parity var index out of bounds"
        );

        let Some(lhs) = build_affine_sum(&self.coefficients, vars) else {
            return ChcExpr::Bool(true);
        };

        let parity_var = vars[self.parity_var_idx].clone();
        let parity = ChcExpr::mod_op(ChcExpr::var(parity_var), ChcExpr::int(2));

        let delta = self.k_odd.saturating_sub(self.k_even);
        let delta_term = match delta {
            0 => ChcExpr::int(0),
            1 => parity,
            -1 => ChcExpr::neg(parity),
            d => ChcExpr::mul(ChcExpr::Int(d), parity),
        };

        let rhs = if self.k_even == 0 {
            delta_term
        } else {
            ChcExpr::add(ChcExpr::Int(self.k_even), delta_term)
        };

        ChcExpr::eq(lhs, rhs)
    }
}

/// Discover conditional affine invariants from sampled models.
///
/// For each candidate parity variable `z`, partitions samples by `z mod 2` and computes affine
/// kernels on each partition. If both partitions produce an equality with the same coefficient
/// vector but different constants, returns a conditional affine template.
pub(crate) fn discover_conditional_affine_invariants(
    int_vars: &[ChcVar],
    models: &[FxHashMap<String, i128>],
) -> Vec<ConditionalAffineInvariant> {
    if int_vars.len() < 2 || int_vars.len() > super::MAX_PAIRWISE_DISCOVERY_VARS || models.len() < 4
    {
        return Vec::new();
    }

    let mut name_to_idx: FxHashMap<&str, usize> = FxHashMap::default();
    for (idx, v) in int_vars.iter().enumerate() {
        name_to_idx.insert(v.name.as_str(), idx);
    }

    let mut discovered: FxHashSet<ConditionalAffineInvariant> = FxHashSet::default();

    for parity_var_idx in 0..int_vars.len() {
        let parity_var = &int_vars[parity_var_idx];
        let mut even: Vec<&FxHashMap<String, i128>> = Vec::new();
        let mut odd: Vec<&FxHashMap<String, i128>> = Vec::new();

        for m in models {
            let Some(v) = m.get(&parity_var.name).copied() else {
                continue;
            };
            if v.rem_euclid(2) == 0 {
                even.push(m);
            } else {
                odd.push(m);
            }
        }

        // Need enough samples for each kernel to be non-empty.
        if even.len() < 2 || odd.len() < 2 {
            continue;
        }

        let map_even = compute_affine_kernel_map(int_vars, &name_to_idx, &even);
        let map_odd = compute_affine_kernel_map(int_vars, &name_to_idx, &odd);

        if map_even.is_empty() || map_odd.is_empty() {
            continue;
        }

        for (coeffs, &k_even) in &map_even {
            let Some(&k_odd) = map_odd.get(coeffs) else {
                continue;
            };
            if k_even == k_odd {
                continue;
            }
            discovered.insert(ConditionalAffineInvariant {
                coefficients: coeffs.clone(),
                parity_var_idx,
                k_even,
                k_odd,
            });
        }
    }

    let mut out: Vec<_> = discovered.into_iter().collect();
    out.sort_by(|a, b| {
        a.parity_var_idx
            .cmp(&b.parity_var_idx)
            .then_with(|| a.coefficients.cmp(&b.coefficients))
            .then_with(|| a.k_even.cmp(&b.k_even))
            .then_with(|| a.k_odd.cmp(&b.k_odd))
    });
    out
}

fn compute_affine_kernel_map(
    vars: &[ChcVar],
    name_to_idx: &FxHashMap<&str, usize>,
    models: &[&FxHashMap<String, i128>],
) -> FxHashMap<Vec<i128>, i128> {
    let mut cc = ConvexClosure::new();
    cc.reset(vars.to_vec());

    let mut num_points = 0usize;
    for m in models {
        // i128-lockstep: ConvexClosure is i64-based; skip samples whose
        // values do not fit i64 (kernel output is verified downstream).
        let mut values: Vec<i64> = Vec::with_capacity(vars.len());
        let mut ok = true;
        for v in vars {
            let Some(value) = m.get(&v.name).copied().and_then(|n| i64::try_from(n).ok()) else {
                ok = false;
                break;
            };
            values.push(value);
        }
        if !ok {
            continue;
        }
        cc.add_data_point(&values);
        num_points += 1;
    }
    if num_points < 2 {
        return FxHashMap::default();
    }

    let result = cc.compute();

    let mut out: FxHashMap<Vec<i128>, i128> = FxHashMap::default();
    for eq in result.equalities {
        let Some((coeffs, k)) = parse_affine_equality(&eq, name_to_idx, vars.len()) else {
            continue;
        };

        // Drop inconsistent duplicates (shouldn't happen, but protects against low-diversity samples).
        match out.get(&coeffs) {
            None => {
                out.insert(coeffs, k);
            }
            Some(existing) if *existing == k => {}
            Some(_) => {
                out.remove(&coeffs);
            }
        }
    }

    out
}

fn parse_affine_equality(
    eq: &ChcExpr,
    name_to_idx: &FxHashMap<&str, usize>,
    num_vars: usize,
) -> Option<(Vec<i128>, i128)> {
    let (lhs, rhs) = match eq {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => (args[0].as_ref(), args[1].as_ref()),
        _ => return None,
    };

    if let ChcExpr::Int(k) = rhs {
        return parse_linear_equals_const(lhs, *k, name_to_idx, num_vars);
    }
    if let ChcExpr::Int(k) = lhs {
        return parse_linear_equals_const(rhs, *k, name_to_idx, num_vars);
    }
    None
}

fn parse_linear_equals_const(
    lhs: &ChcExpr,
    rhs_const: i128,
    name_to_idx: &FxHashMap<&str, usize>,
    num_vars: usize,
) -> Option<(Vec<i128>, i128)> {
    let mut coeffs = vec![0i128; num_vars];
    let mut lhs_const = 0i128;
    collect_linear(lhs, 1, name_to_idx, &mut coeffs, &mut lhs_const)?;

    let mut k = rhs_const.checked_sub(lhs_const)?;
    normalize_affine(&mut coeffs, &mut k)?;
    Some((coeffs, k))
}

fn collect_linear(
    expr: &ChcExpr,
    scale: i128,
    name_to_idx: &FxHashMap<&str, usize>,
    coeffs: &mut [i128],
    constant: &mut i128,
) -> Option<()> {
    walk_linear_expr(
        expr,
        scale,
        &mut |mult: i128, n| {
            *constant = (*constant).checked_add(mult.checked_mul(n)?)?;
            Some(())
        },
        &mut |mult: i128, v| {
            let idx = *name_to_idx.get(v.name.as_str())?;
            coeffs[idx] = coeffs[idx].checked_add(mult)?;
            Some(())
        },
    )
}

fn normalize_affine(coeffs: &mut [i128], k: &mut i128) -> Option<()> {
    if coeffs.iter().all(|&c| c == 0) {
        return None;
    }

    fn abs_u128(v: i128) -> u128 {
        v.unsigned_abs()
    }
    let mut g = 0u128;
    for &c in coeffs.iter() {
        g = num_integer::gcd(g, abs_u128(c));
    }
    g = num_integer::gcd(g, abs_u128(*k));
    if g > 1 {
        // Fail closed if the gcd itself does not fit i128 (only possible when
        // every value is i128::MIN).
        let g = i128::try_from(g).ok()?;
        if *k % g == 0 && coeffs.iter().all(|&c| c % g == 0) {
            for c in coeffs.iter_mut() {
                *c /= g;
            }
            *k /= g;
        }
    }

    let &first = coeffs.iter().find(|&&c| c != 0)?;
    if first < 0 {
        let can_negate = coeffs.iter().all(|&c| c != i128::MIN) && *k != i128::MIN;
        if can_negate {
            for c in coeffs.iter_mut() {
                *c = c.checked_neg()?;
            }
            *k = k.checked_neg()?;
        }
    }

    Some(())
}

fn build_affine_sum(coeffs: &[i128], vars: &[ChcVar]) -> Option<ChcExpr> {
    debug_assert_eq!(coeffs.len(), vars.len());

    let mut terms: Vec<ChcExpr> = Vec::new();
    for (&c, v) in coeffs.iter().zip(vars.iter()) {
        if c == 0 {
            continue;
        }
        let var_expr = ChcExpr::var(v.clone());
        let term = match c {
            1 => var_expr,
            -1 => ChcExpr::neg(var_expr),
            _ => ChcExpr::mul(ChcExpr::Int(c), var_expr),
        };
        terms.push(term);
    }

    match terms.len() {
        0 => None,
        1 => Some(terms.pop().expect("len == 1")),
        _ => Some(terms.into_iter().reduce(ChcExpr::add).expect("len > 1")),
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;
