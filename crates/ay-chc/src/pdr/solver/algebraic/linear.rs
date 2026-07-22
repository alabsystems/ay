// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::PdrSolver;
use crate::expr::walk_linear_expr;
use crate::{ChcExpr, ChcOp};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

impl PdrSolver {
    pub(in crate::pdr::solver) fn extract_linear_equalities_alg(
        expr: &ChcExpr,
    ) -> FxHashMap<String, (FxHashMap<String, i128>, i128)> {
        let mut equalities = FxHashMap::default();
        let conjuncts = expr.collect_conjuncts();

        for conjunct in conjuncts {
            if let ChcExpr::Op(ChcOp::Eq, args) = &conjunct {
                if args.len() == 2 {
                    if let Some((var, coeffs, c)) = Self::parse_linear_eq_alg(&args[0], &args[1]) {
                        equalities.insert(var, (coeffs, c));
                    } else if let Some((var, coeffs, c)) =
                        Self::parse_linear_eq_alg(&args[1], &args[0])
                    {
                        equalities.insert(var, (coeffs, c));
                    }
                }
            }
        }

        equalities
    }

    pub(in crate::pdr::solver) fn parse_linear_eq_alg(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
    ) -> Option<(String, FxHashMap<String, i128>, i128)> {
        let var_name = match lhs {
            ChcExpr::Var(v) => v.name.clone(),
            _ => return None,
        };

        let (coeffs, constant) = Self::parse_linear_expr_alg(rhs)?;

        if coeffs.contains_key(&var_name) {
            return None;
        }

        Some((var_name, coeffs, constant))
    }

    pub(in crate::pdr::solver) fn parse_linear_expr_alg(
        expr: &ChcExpr,
    ) -> Option<(FxHashMap<String, i128>, i128)> {
        let mut coeffs = FxHashMap::default();
        let mut constant = 0i128;
        walk_linear_expr(
            expr,
            1i128,
            &mut |mult, n| {
                constant = constant.checked_add(mult.checked_mul(n)?)?;
                Some(())
            },
            &mut |mult, v| {
                let entry = coeffs.entry(v.name.clone()).or_insert(0i128);
                *entry = (*entry).checked_add(mult)?;
                Some(())
            },
        )?;
        Some((coeffs, constant))
    }

    pub(in crate::pdr::solver) fn extract_sum_equalities_alg(
        expr: &ChcExpr,
    ) -> Vec<(
        (FxHashMap<String, i128>, i128),
        (FxHashMap<String, i128>, i128),
    )> {
        let mut equalities = Vec::new();
        let conjuncts = expr.collect_conjuncts();

        for conjunct in conjuncts {
            if let ChcExpr::Op(ChcOp::Eq, args) = &conjunct {
                if args.len() == 2 {
                    if let (Some(l), Some(r)) = (
                        Self::parse_linear_expr_alg(&args[0]),
                        Self::parse_linear_expr_alg(&args[1]),
                    ) {
                        if !l.0.is_empty() || !r.0.is_empty() {
                            equalities.push((l, r));
                        }
                    }
                }
            }
        }

        equalities
    }

    pub(in crate::pdr::solver) fn verify_equality_by_sub_alg(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        body_eq: &FxHashMap<String, (FxHashMap<String, i128>, i128)>,
        sum_eq: &[(
            (FxHashMap<String, i128>, i128),
            (FxHashMap<String, i128>, i128),
        )],
    ) -> bool {
        let (lc, ls) = match Self::parse_linear_expr_alg(lhs) {
            Some(p) => p,
            None => return false,
        };
        let (rc, rs) = match Self::parse_linear_expr_alg(rhs) {
            Some(p) => p,
            None => return false,
        };

        let (ls_c, ls_s) = Self::apply_subs_alg(&lc, ls, body_eq);
        let (rs_c, rs_s) = Self::apply_subs_alg(&rc, rs, body_eq);

        if Self::lin_eq_alg(&ls_c, ls_s, &rs_c, rs_s) {
            return true;
        }

        let (diff_c, diff_s) = Self::sub_lin_alg(&ls_c, ls_s, &rs_c, rs_s);

        if Self::is_zero_alg(&diff_c, diff_s) {
            return true;
        }

        for ((el, els), (er, ers)) in sum_eq {
            let (eq_diff_c, eq_diff_s) = Self::sub_lin_alg(el, *els, er, *ers);
            if Self::lin_eq_alg(&diff_c, diff_s, &eq_diff_c, eq_diff_s) {
                return true;
            }
            let (neg_c, neg_s) = Self::neg_lin_alg(&eq_diff_c, eq_diff_s);
            if Self::lin_eq_alg(&diff_c, diff_s, &neg_c, neg_s) {
                return true;
            }
        }

        false
    }

    /// Single-pass substitution.
    pub(in crate::pdr::solver) fn apply_subs_once(
        coeffs: &FxHashMap<String, i128>,
        constant: i128,
        subs: &FxHashMap<String, (FxHashMap<String, i128>, i128)>,
    ) -> (FxHashMap<String, i128>, i128) {
        let mut nc = FxHashMap::default();
        let mut ns = constant;

        for (var, &coeff) in coeffs {
            if let Some((sc, ss)) = subs.get(var) {
                ns += coeff * ss;
                for (sv, &sco) in sc {
                    *nc.entry(sv.clone()).or_insert(0) += coeff * sco;
                }
            } else {
                *nc.entry(var.clone()).or_insert(0) += coeff;
            }
        }

        nc.retain(|_, v| *v != 0);
        (nc, ns)
    }

    /// Fixed-point substitution - iterate until no changes occur.
    /// This handles chained equalities like F = C - 1, C = B - A, so F becomes B - A - 1.
    pub(in crate::pdr::solver) fn apply_subs_alg(
        coeffs: &FxHashMap<String, i128>,
        constant: i128,
        subs: &FxHashMap<String, (FxHashMap<String, i128>, i128)>,
    ) -> (FxHashMap<String, i128>, i128) {
        let mut current_coeffs = coeffs.clone();
        let mut current_constant = constant;

        const MAX_ITERATIONS: usize = 10;
        for _ in 0..MAX_ITERATIONS {
            let (new_coeffs, new_constant) =
                Self::apply_subs_once(&current_coeffs, current_constant, subs);

            // Check for fixed point
            if new_coeffs == current_coeffs && new_constant == current_constant {
                break;
            }
            current_coeffs = new_coeffs;
            current_constant = new_constant;
        }

        (current_coeffs, current_constant)
    }

    pub(in crate::pdr::solver) fn sub_lin_alg(
        c1: &FxHashMap<String, i128>,
        s1: i128,
        c2: &FxHashMap<String, i128>,
        s2: i128,
    ) -> (FxHashMap<String, i128>, i128) {
        let mut r = c1.clone();
        for (v, &c) in c2 {
            *r.entry(v.clone()).or_insert(0) -= c;
        }
        r.retain(|_, v| *v != 0);
        (r, s1 - s2)
    }

    pub(in crate::pdr::solver) fn neg_lin_alg(
        c: &FxHashMap<String, i128>,
        s: i128,
    ) -> (FxHashMap<String, i128>, i128) {
        let mut r = FxHashMap::default();
        for (v, &co) in c {
            r.insert(v.clone(), -co);
        }
        (r, -s)
    }

    pub(in crate::pdr::solver) fn lin_eq_alg(
        c1: &FxHashMap<String, i128>,
        s1: i128,
        c2: &FxHashMap<String, i128>,
        s2: i128,
    ) -> bool {
        s1 == s2 && c1.len() == c2.len() && c1.iter().all(|(v, &c)| c2.get(v) == Some(&c))
    }

    pub(in crate::pdr::solver) fn is_zero_alg(c: &FxHashMap<String, i128>, s: i128) -> bool {
        s == 0 && c.values().all(|&v| v == 0)
    }

    pub(in crate::pdr::solver) fn verify_ge_from_body_alg(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        body: &ChcExpr,
        body_eq: &FxHashMap<String, (FxHashMap<String, i128>, i128)>,
    ) -> bool {
        let body_conjuncts = body.collect_conjuncts();

        // Check for direct match: lhs >= rhs in body
        for c in &body_conjuncts {
            if let ChcExpr::Op(ChcOp::Ge, args) = c {
                if args.len() == 2 && *args[0] == *lhs && *args[1] == *rhs {
                    return true;
                }
            }
        }

        // Use SINGLE-STEP substitution to transform lhs >= rhs into body variables
        // We avoid fixed-point substitution here because it can introduce unnecessary
        // dependencies. For example, D >= F with D=B, F=C-1, B>=C should be verified
        // as B >= C-1 (which follows from B >= C), not as B >= B-A-1 (after expanding C=B-A).
        let lhs_norm = Self::normalize_with_single_substitution(lhs, body_eq);
        let rhs_norm = Self::normalize_with_single_substitution(rhs, body_eq);

        // Compute diff = lhs_norm - rhs_norm
        // We need to verify diff >= 0
        let (diff_coeffs, diff_constant) =
            Self::sub_lin_alg(&lhs_norm.0, lhs_norm.1, &rhs_norm.0, rhs_norm.1);

        // If constant part is negative, need to compensate with body bounds
        // For each variable term, check if it can offset the constant deficit
        Self::verify_ge_zero_from_body(&diff_coeffs, diff_constant, &body_conjuncts)
    }

    /// Normalize expression using single-step body equalities.
    /// Unlike fixed-point substitution, this only applies substitutions once.
    pub(in crate::pdr::solver) fn normalize_with_single_substitution(
        expr: &ChcExpr,
        body_eq: &FxHashMap<String, (FxHashMap<String, i128>, i128)>,
    ) -> (FxHashMap<String, i128>, i128) {
        let (coeffs, constant) =
            Self::parse_linear_expr_alg(expr).unwrap_or_else(|| (FxHashMap::default(), 0));
        Self::apply_subs_once(&coeffs, constant, body_eq)
    }

    /// Verify that sum of (coeff * var) + constant >= 0 using body bounds.
    pub(in crate::pdr::solver) fn verify_ge_zero_from_body(
        coeffs: &FxHashMap<String, i128>,
        constant: i128,
        body_conjuncts: &[ChcExpr],
    ) -> bool {
        // If constant >= 0 and all positive-coeff vars are >= 0, we're done
        // (negative-coeff vars would make it smaller, so we need them bounded from above)

        // Collect bounds from body
        let mut ge_zero_vars: FxHashSet<String> = FxHashSet::default();
        let mut ge_pairs: Vec<(String, String)> = Vec::new(); // (a, b) means a >= b

        for c in body_conjuncts {
            if let ChcExpr::Op(ChcOp::Ge, args) = c {
                if args.len() == 2 {
                    if let (ChcExpr::Var(v), ChcExpr::Int(0)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        ge_zero_vars.insert(v.name.clone());
                    }
                    if let (ChcExpr::Var(v1), ChcExpr::Var(v2)) =
                        (args[0].as_ref(), args[1].as_ref())
                    {
                        ge_pairs.push((v1.name.clone(), v2.name.clone()));
                    }
                }
            }
        }

        // Case 1: All coefficients are non-negative and constant >= 0
        // Each term with positive coeff needs its var >= 0
        let all_positive_bounded = coeffs.iter().all(|(var, &coeff)| {
            if coeff > 0 {
                ge_zero_vars.contains(var)
            } else {
                true // Negative coeffs don't help but don't hurt if we ignore them
            }
        });

        // For negative coefficients, we'd need upper bounds which we don't track yet
        let has_negative_coeff = coeffs.values().any(|&c| c < 0);

        if constant >= 0 && all_positive_bounded && !has_negative_coeff {
            return true;
        }

        // Case 2: Single positive-coeff var X with X >= 0, and constant + coeff*0 = constant >= 0
        // Already covered by Case 1

        // Case 3: Expression is X - Y + constant where X >= Y in body
        // Then X - Y >= 0, so X - Y + constant >= constant
        if constant >= 0 && coeffs.len() == 2 {
            // Find positive and negative coefficient variables
            let mut pos_var: Option<&String> = None;
            let mut neg_var: Option<&String> = None;
            for (var, &coeff) in coeffs {
                if coeff == 1 {
                    pos_var = Some(var);
                } else if coeff == -1 {
                    neg_var = Some(var);
                }
            }
            if let (Some(pv), Some(nv)) = (pos_var, neg_var) {
                // We have pv - nv + constant >= 0
                // Need pv >= nv in body (since constant >= 0)
                if ge_pairs.iter().any(|(a, b)| a == pv && b == nv) {
                    return true;
                }
            }
        }

        // Case 4: Expression simplifies to just a constant
        if coeffs.is_empty() || coeffs.values().all(|&c| c == 0) {
            return constant >= 0;
        }

        false
    }
}
