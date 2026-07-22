// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

/// Try to extract an interpolant from A-side equalities (Fix #966).
///
/// When direct IUC (negating B-core) fails because the negated B-core is too weak,
/// A-side equalities on shared variables often provide stronger interpolants.
pub(crate) fn try_a_side_equality_interpolant(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    check_smt: &mut SmtContext,
) -> Option<ChcExpr> {
    fn next_combination(indices: &mut [usize], n: usize) -> bool {
        let k = indices.len();
        for i in (0..k).rev() {
            let max_i = n - (k - i);
            if indices[i] < max_i {
                indices[i] += 1;
                for j in (i + 1)..k {
                    indices[j] = indices[j - 1] + 1;
                }
                return true;
            }
        }
        false
    }

    let mut a_equalities: Vec<ChcExpr> = Vec::new();

    for a in a_constraints {
        if is_equality_expr(a) && vars_all_shared(a, shared_vars) {
            a_equalities.push(a.clone());
        }
    }

    if a_equalities.is_empty() {
        iuc_trace!("try_a_side_equality_interpolant: no shared-var equalities in A");
        return None;
    }

    iuc_trace!(
        "try_a_side_equality_interpolant: found {} A-side equalities: {:?}",
        a_equalities.len(),
        a_equalities
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
    );

    let b_conj = and_slice(b_constraints);
    let a_conj = and_slice(a_constraints);

    for candidate in &a_equalities {
        if let ChcExpr::Op(ChcOp::Eq, args) = candidate {
            if args.len() == 2 {
                let a = args[0].as_ref();
                let b = args[1].as_ref();
                let a_sort = a.sort();
                let b_sort = b.sort();
                if a_sort == b_sort && matches!(a_sort, ChcSort::Int | ChcSort::Real) {
                    let (lhs, rhs) = prefer_var_left(a, b);
                    let weakenings = [
                        ChcExpr::le(lhs.clone(), rhs.clone()),
                        ChcExpr::ge(lhs.clone(), rhs.clone()),
                    ];

                    for weakened in weakenings {
                        if verify_craig_properties(
                            &weakened,
                            &a_conj,
                            &b_conj,
                            shared_vars,
                            check_smt,
                            "try_a_side_equality_interpolant",
                        ) {
                            iuc_trace!(
                                "try_a_side_equality_interpolant: weakened {} -> {} passed both checks",
                                candidate,
                                weakened
                            );
                            return Some(weakened);
                        }
                    }
                }
            }
        }

        if verify_craig_properties(
            candidate,
            &a_conj,
            &b_conj,
            shared_vars,
            check_smt,
            "try_a_side_equality_interpolant",
        ) {
            iuc_trace!(
                "try_a_side_equality_interpolant: equality {} passed both checks",
                candidate
            );
            return Some(candidate.clone());
        }
    }

    const MAX_CONJUNCTION_WIDTH: usize = 3;
    const MAX_CONJUNCTIONS_TRIED: usize = 64;
    let max_width = a_equalities.len().min(MAX_CONJUNCTION_WIDTH);
    if max_width >= 2 {
        let mut tried = 0usize;
        'width_loop: for width in 2..=max_width {
            let mut indices: Vec<usize> = (0..width).collect();
            loop {
                let conjuncts: Vec<ChcExpr> = indices
                    .iter()
                    .map(|&idx| a_equalities[idx].clone())
                    .collect();
                let candidate = ChcExpr::and_all(conjuncts);
                if verify_craig_properties(
                    &candidate,
                    &a_conj,
                    &b_conj,
                    shared_vars,
                    check_smt,
                    "try_a_side_equality_interpolant",
                ) {
                    iuc_trace!(
                        "try_a_side_equality_interpolant: conjunction {:?} passed both checks",
                        indices
                    );
                    return Some(candidate);
                }

                tried += 1;
                if tried >= MAX_CONJUNCTIONS_TRIED
                    || !next_combination(&mut indices, a_equalities.len())
                {
                    break;
                }
            }

            if tried >= MAX_CONJUNCTIONS_TRIED {
                break 'width_loop;
            }
        }
    }

    None
}

fn is_equality_expr(expr: &ChcExpr) -> bool {
    matches!(expr, ChcExpr::Op(ChcOp::Eq, _))
}

fn prefer_var_left<'a>(lhs: &'a ChcExpr, rhs: &'a ChcExpr) -> (&'a ChcExpr, &'a ChcExpr) {
    match (lhs, rhs) {
        (ChcExpr::Var(_), _) => (lhs, rhs),
        (_, ChcExpr::Var(_)) => (rhs, lhs),
        _ => (lhs, rhs),
    }
}
