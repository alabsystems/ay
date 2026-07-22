// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Joint case-split helper logic and tests.

use super::*;
use crate::dioph_joint_case_split::{
    FeasibleValueSet, JointCaseSplitBoundPair, JointCaseSplitExpr, SmallRangeTerm, ValueSetEval,
};

pub(crate) fn joint_case_split_proves_infeasible(
    primary_exprs: &[JointCaseSplitExpr],
    alternate_exprs: &HashMap<TermId, Vec<JointCaseSplitExpr>>,
    all_exprs: &[JointCaseSplitExpr],
    bounds: &HashMap<TermId, JointCaseSplitBoundPair>,
    small_range_limit: usize,
    max_assignments: usize,
    debug: bool,
) -> Option<bool> {
    if primary_exprs.is_empty() {
        return None;
    }

    let small_terms = collect_small_range_terms(all_exprs, bounds, small_range_limit);
    if small_terms.is_empty() {
        if debug {
            safe_eprintln!("[DIOPH-JCS] skip: no small-range dependent variables");
        }
        return None;
    }

    let assignment_count = joint_case_split_assignment_count(&small_terms, max_assignments)?;
    if debug {
        let vars: Vec<TermId> = small_terms.iter().map(|term| term.term_id).collect();
        safe_eprintln!(
            "[DIOPH-JCS] exploring {} assignments across {:?}",
            assignment_count,
            vars
        );
    }

    let mut assignment = HashMap::default();
    if has_feasible_joint_assignment(
        0,
        &small_terms,
        &mut assignment,
        primary_exprs,
        alternate_exprs,
        bounds,
        debug,
    ) {
        return Some(false);
    }

    if debug {
        safe_eprintln!(
            "[DIOPH-JCS] all {} assignments violate at least one substitution",
            assignment_count
        );
    }
    Some(true)
}

pub(crate) fn build_joint_case_split_bounds<F>(
    expressions: &[JointCaseSplitExpr],
    mut get_bounds: F,
) -> HashMap<TermId, JointCaseSplitBoundPair>
where
    F: FnMut(TermId) -> JointCaseSplitBoundPair,
{
    let mut bounds = HashMap::default();
    for expr in expressions {
        bounds
            .entry(expr.term_id)
            .or_insert_with(|| get_bounds(expr.term_id));
        for dep_term in expr.coeffs.keys() {
            bounds
                .entry(*dep_term)
                .or_insert_with(|| get_bounds(*dep_term));
        }
    }
    bounds
}

fn joint_case_split_assignment_count(
    small_terms: &[SmallRangeTerm],
    max_assignments: usize,
) -> Option<usize> {
    let mut total = 1usize;
    for term in small_terms {
        total = total.checked_mul(term.values.len())?;
        if total > max_assignments {
            return None;
        }
    }
    Some(total)
}

fn collect_small_range_terms(
    expressions: &[JointCaseSplitExpr],
    bounds: &HashMap<TermId, JointCaseSplitBoundPair>,
    small_range_limit: usize,
) -> Vec<SmallRangeTerm> {
    let mut seen = HashSet::default();
    let max_width = BigInt::from(small_range_limit);
    let mut small_terms = Vec::new();

    for expr in expressions {
        for dep_term in expr.coeffs.keys() {
            if !seen.insert(*dep_term) {
                continue;
            }
            let Some((Some(lower), Some(upper))) = bounds.get(dep_term) else {
                continue;
            };
            if upper < lower || upper - lower > max_width {
                continue;
            }

            let mut values = Vec::new();
            let mut current = lower.clone();
            while current <= *upper {
                values.push(current.clone());
                current += BigInt::one();
            }
            small_terms.push(SmallRangeTerm {
                term_id: *dep_term,
                values,
            });
        }
    }

    small_terms.sort_by_key(|term| term.term_id.0);
    small_terms
}

fn has_feasible_joint_assignment(
    index: usize,
    small_terms: &[SmallRangeTerm],
    assignment: &mut HashMap<TermId, BigInt>,
    primary_exprs: &[JointCaseSplitExpr],
    alternate_exprs: &HashMap<TermId, Vec<JointCaseSplitExpr>>,
    bounds: &HashMap<TermId, JointCaseSplitBoundPair>,
    debug: bool,
) -> bool {
    if index == small_terms.len() {
        let feasible = assignment_is_feasible(assignment, primary_exprs, alternate_exprs, bounds);
        if feasible && debug {
            safe_eprintln!(
                "[DIOPH-JCS] feasible assignment {:?}",
                format_assignment(small_terms, assignment)
            );
        }
        return feasible;
    }

    let small_term = &small_terms[index];
    for value in &small_term.values {
        assignment.insert(small_term.term_id, value.clone());
        if has_feasible_joint_assignment(
            index + 1,
            small_terms,
            assignment,
            primary_exprs,
            alternate_exprs,
            bounds,
            debug,
        ) {
            return true;
        }
    }
    assignment.remove(&small_term.term_id);
    false
}

fn assignment_is_feasible(
    assignment: &HashMap<TermId, BigInt>,
    primary_exprs: &[JointCaseSplitExpr],
    alternate_exprs: &HashMap<TermId, Vec<JointCaseSplitExpr>>,
    bounds: &HashMap<TermId, JointCaseSplitBoundPair>,
) -> bool {
    for primary in primary_exprs {
        let mut term_values = bounds_to_value_set(bounds.get(&primary.term_id).cloned());
        let mut exprs =
            Vec::with_capacity(1 + alternate_exprs.get(&primary.term_id).map_or(0, Vec::len));
        exprs.push(primary);
        if let Some(alternates) = alternate_exprs.get(&primary.term_id) {
            exprs.extend(alternates.iter());
        }

        for expr in exprs {
            match expression_value_set(expr, assignment, bounds) {
                ValueSetEval::Known(expr_values) => {
                    term_values = Some(match term_values.take() {
                        Some(current) => match intersect_value_sets(current, expr_values) {
                            Some(intersection) => intersection,
                            None => return false,
                        },
                        None => expr_values,
                    });
                }
                ValueSetEval::Empty => return false,
                ValueSetEval::Unknown => break,
            }
        }
    }

    true
}

fn expression_value_set(
    expr: &JointCaseSplitExpr,
    assignment: &HashMap<TermId, BigInt>,
    bounds: &HashMap<TermId, JointCaseSplitBoundPair>,
) -> ValueSetEval {
    let mut adjusted_constant = expr.constant.clone();
    let mut implied_lo = adjusted_constant.clone();
    let mut implied_hi = adjusted_constant.clone();
    let mut modulus = BigInt::zero();

    for (dep_term, coeff) in &expr.coeffs {
        if let Some(value) = assignment.get(dep_term) {
            adjusted_constant += coeff * value;
            implied_lo += coeff * value;
            implied_hi += coeff * value;
            continue;
        }

        let Some((Some(dep_lo), Some(dep_hi))) = bounds.get(dep_term) else {
            return ValueSetEval::Unknown;
        };
        if coeff.is_positive() {
            implied_lo += coeff * dep_lo;
            implied_hi += coeff * dep_hi;
        } else {
            implied_lo += coeff * dep_hi;
            implied_hi += coeff * dep_lo;
        }
        let abs_coeff = coeff.abs();
        modulus = if modulus.is_zero() {
            abs_coeff
        } else {
            modulus.gcd(&abs_coeff)
        };
    }

    if implied_lo > implied_hi {
        return ValueSetEval::Empty;
    }

    let (modulus, residue) = if modulus <= BigInt::one() {
        (BigInt::one(), BigInt::zero())
    } else {
        (modulus.clone(), positive_mod(&adjusted_constant, &modulus))
    };
    ValueSetEval::Known(FeasibleValueSet {
        lo: implied_lo,
        hi: implied_hi,
        modulus,
        residue,
    })
}

fn bounds_to_value_set(bounds: Option<JointCaseSplitBoundPair>) -> Option<FeasibleValueSet> {
    let (Some(lo), Some(hi)) = bounds? else {
        return None;
    };
    if lo > hi {
        return None;
    }
    Some(FeasibleValueSet {
        lo,
        hi,
        modulus: BigInt::one(),
        residue: BigInt::zero(),
    })
}

fn intersect_value_sets(
    left: FeasibleValueSet,
    right: FeasibleValueSet,
) -> Option<FeasibleValueSet> {
    let lo = left.lo.max(right.lo);
    let hi = left.hi.min(right.hi);
    if lo > hi {
        return None;
    }

    let (modulus, residue) =
        merge_congruences(&left.modulus, &left.residue, &right.modulus, &right.residue)?;
    let first = if modulus.is_one() {
        lo.clone()
    } else {
        lo.clone() + positive_mod(&(residue.clone() - &lo), &modulus)
    };
    if first > hi {
        return None;
    }

    Some(FeasibleValueSet {
        lo,
        hi,
        modulus,
        residue,
    })
}

fn merge_congruences(
    left_modulus: &BigInt,
    left_residue: &BigInt,
    right_modulus: &BigInt,
    right_residue: &BigInt,
) -> Option<(BigInt, BigInt)> {
    if left_modulus.is_one() {
        return Some((right_modulus.clone(), right_residue.clone()));
    }
    if right_modulus.is_one() {
        return Some((left_modulus.clone(), left_residue.clone()));
    }

    let gcd = left_modulus.gcd(right_modulus);
    if positive_mod(left_residue, &gcd) != positive_mod(right_residue, &gcd) {
        return None;
    }

    let (g_ext, s, _) = ay_core::extended_gcd_bigint(left_modulus, right_modulus);
    let lcm_mod = left_modulus.lcm(right_modulus);
    let diff = right_residue - left_residue;
    let merged = positive_mod(
        &(left_residue + left_modulus * (&diff / &g_ext) * s),
        &lcm_mod,
    );
    Some((lcm_mod, merged))
}

fn format_assignment(
    small_terms: &[SmallRangeTerm],
    assignment: &HashMap<TermId, BigInt>,
) -> Vec<(TermId, BigInt)> {
    small_terms
        .iter()
        .filter_map(|term| {
            assignment
                .get(&term.term_id)
                .cloned()
                .map(|value| (term.term_id, value))
        })
        .collect()
}
