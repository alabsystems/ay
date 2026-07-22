// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Contradiction detection in cube expressions.
//!
//! Contains `is_trivial_contradiction` (A AND NOT(A) detection),
//! `has_relational_contradiction` (contradictory bounds), and
//! `collect_equalities_for_point_check` (union-find-based point cube analysis).

use super::PointCubeUnionFind;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::super::types::RelationType;

/// Returns true when `expr` is variable-free and therefore denotes a ground term.
fn is_var_free(expr: &ChcExpr) -> bool {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Var(_) => false,
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter().all(|arg| is_var_free(arg))
        }
        ChcExpr::ConstArray(_ks, val) => is_var_free(val),
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Real(_, _)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => true,
    })
}

/// Recursively collect equalities and update union-find for point cube detection.
/// - `var = ground_term` marks the var as grounded
/// - `var1 = var2` unions their equivalence classes
pub(in crate::pdr) fn collect_equalities_for_point_check(
    expr: &ChcExpr,
    uf: &mut PointCubeUnionFind,
) {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(ChcOp::And, args) => {
            for arg in args {
                collect_equalities_for_point_check(arg, uf);
            }
        }
        ChcExpr::Var(v) if matches!(v.sort, ChcSort::Bool) => {
            // Bool literals are grounded assignments: `b` means `b = true`.
            uf.mark_grounded(&v.name);
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            // `not b` also grounds bool var `b` to a concrete value.
            if let ChcExpr::Var(v) = args[0].as_ref() {
                if matches!(v.sort, ChcSort::Bool) {
                    uf.mark_grounded(&v.name);
                }
            }
        }
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            let is_var0 = matches!(args[0].as_ref(), ChcExpr::Var(_));
            let is_var1 = matches!(args[1].as_ref(), ChcExpr::Var(_));

            match (is_var0, is_var1) {
                (true, true) => {
                    // var = var: union the equivalence classes
                    if let (ChcExpr::Var(v0), ChcExpr::Var(v1)) =
                        (args[0].as_ref(), args[1].as_ref())
                    {
                        uf.union(&v0.name, &v1.name);
                    }
                }
                (true, false) => {
                    // var = ground_term: mark var as grounded
                    if let ChcExpr::Var(v) = args[0].as_ref() {
                        if is_var_free(args[1].as_ref()) {
                            uf.mark_grounded(&v.name);
                        }
                    }
                }
                (false, true) => {
                    // ground_term = var: mark var as grounded
                    if let ChcExpr::Var(v) = args[1].as_ref() {
                        if is_var_free(args[0].as_ref()) {
                            uf.mark_grounded(&v.name);
                        }
                    }
                }
                (false, false) => {
                    // constant = constant: no variable to track
                }
            }
        }
        _ => {}
    });
}

/// Check if a formula contains a trivial contradiction: A AND NOT(A)
pub(crate) fn is_trivial_contradiction(expr: &ChcExpr) -> bool {
    let conjuncts = expr.collect_conjuncts();
    let mut positive_conjuncts: FxHashSet<&ChcExpr> = FxHashSet::default();
    let mut negated_conjuncts: FxHashSet<&ChcExpr> = FxHashSet::default();

    // Track seen conjuncts and negated forms in O(C) time.
    for conjunct in &conjuncts {
        match conjunct {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                let inner = args[0].as_ref();
                if positive_conjuncts.contains(inner) {
                    return true;
                }
                if let ChcExpr::Op(ChcOp::Or, disjuncts) = inner {
                    if disjuncts
                        .iter()
                        .any(|disjunct| positive_conjuncts.contains(disjunct.as_ref()))
                    {
                        return true;
                    }
                }
                negated_conjuncts.insert(inner);
            }
            _ => {
                if negated_conjuncts.contains(conjunct) {
                    return true;
                }
                if negated_conjuncts.iter().any(|negated| {
                    matches!(
                        negated,
                        ChcExpr::Op(ChcOp::Or, disjuncts)
                            if disjuncts.iter().any(|disjunct| disjunct.as_ref() == conjunct)
                    )
                }) {
                    return true;
                }
                positive_conjuncts.insert(conjunct);
            }
        }
    }

    for negated in &negated_conjuncts {
        match negated {
            ChcExpr::Op(ChcOp::Or, disjuncts)
                if disjuncts
                    .iter()
                    .any(|disjunct| positive_conjuncts.contains(disjunct.as_ref())) =>
            {
                return true;
            }
            ChcExpr::Op(ChcOp::And, inner_conjuncts)
                if inner_conjuncts
                    .iter()
                    .all(|inner| positive_conjuncts.contains(inner.as_ref())) =>
            {
                return true;
            }
            _ => {}
        }
    }

    // Check for relational contradictions: (a <= b) and (a > b), etc.
    // Also handle patterns like (a >= b) and (not (= a b)) and (a <= b) which implies a > b
    if has_relational_contradiction(&conjuncts) {
        return true;
    }

    if has_bv2nat_constant_contradiction(&conjuncts) {
        return true;
    }

    false
}

fn has_bv2nat_constant_contradiction(conjuncts: &[ChcExpr]) -> bool {
    let mut bv_equalities: FxHashMap<ChcVar, u128> = FxHashMap::default();

    for conjunct in conjuncts {
        if let Some((var, bits)) = extract_bv_var_const_equality(conjunct) {
            if let Some(previous) = bv_equalities.insert(var, bits) {
                if previous != bits {
                    return true;
                }
            }
        }
    }

    for conjunct in conjuncts {
        let Some((var, int_value, is_equality)) = extract_bv2nat_int_literal(conjunct) else {
            continue;
        };
        let Some(&bits) = bv_equalities.get(&var) else {
            continue;
        };
        let Some(int_bits) = non_negative_int_to_u128(int_value) else {
            if is_equality {
                return true;
            }
            continue;
        };

        let equal = bits == int_bits;
        if (is_equality && !equal) || (!is_equality && equal) {
            return true;
        }
    }

    false
}

fn extract_bv_var_const_equality(expr: &ChcExpr) -> Option<(ChcVar, u128)> {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    bv_var_const_pair(args[0].as_ref(), args[1].as_ref())
        .or_else(|| bv_var_const_pair(args[1].as_ref(), args[0].as_ref()))
}

fn bv_var_const_pair(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<(ChcVar, u128)> {
    let ChcExpr::Var(var) = lhs else {
        return None;
    };
    let ChcSort::BitVec(var_width) = var.sort else {
        return None;
    };
    let ChcExpr::BitVec(bits, value_width) = rhs else {
        return None;
    };
    if var_width != *value_width {
        return None;
    }
    Some((var.clone(), *bits))
}

fn extract_bv2nat_int_literal(expr: &ChcExpr) -> Option<(ChcVar, i128, bool)> {
    match expr {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            bv2nat_int_pair(args[0].as_ref(), args[1].as_ref(), true)
                .or_else(|| bv2nat_int_pair(args[1].as_ref(), args[0].as_ref(), true))
        }
        ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
            bv2nat_int_pair(args[0].as_ref(), args[1].as_ref(), false)
                .or_else(|| bv2nat_int_pair(args[1].as_ref(), args[0].as_ref(), false))
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
            ChcExpr::Op(ChcOp::Eq, eq_args) if eq_args.len() == 2 => {
                bv2nat_int_pair(eq_args[0].as_ref(), eq_args[1].as_ref(), false)
                    .or_else(|| bv2nat_int_pair(eq_args[1].as_ref(), eq_args[0].as_ref(), false))
            }
            ChcExpr::Op(ChcOp::Ne, ne_args) if ne_args.len() == 2 => {
                bv2nat_int_pair(ne_args[0].as_ref(), ne_args[1].as_ref(), true)
                    .or_else(|| bv2nat_int_pair(ne_args[1].as_ref(), ne_args[0].as_ref(), true))
            }
            _ => None,
        },
        _ => None,
    }
}

fn bv2nat_int_pair(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    is_equality: bool,
) -> Option<(ChcVar, i128, bool)> {
    let ChcExpr::Op(ChcOp::Bv2Nat, args) = lhs else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let ChcExpr::Var(var) = args[0].as_ref() else {
        return None;
    };
    if !matches!(var.sort, ChcSort::BitVec(_)) {
        return None;
    }
    let ChcExpr::Int(value) = rhs else {
        return None;
    };
    Some((var.clone(), *value, is_equality))
}

fn non_negative_int_to_u128(value: i128) -> Option<u128> {
    if value < 0 {
        None
    } else {
        Some(value as u128)
    }
}

/// Check if a list of conjuncts contains contradictory relational constraints.
/// Examples:
/// - (a <= b) and (a > b) → contradiction
/// - (a <= b) and (a >= b) and (a != b) → contradiction (since a <= b && a >= b implies a = b)
pub(in crate::pdr) fn has_relational_contradiction(conjuncts: &[ChcExpr]) -> bool {
    // Extract relational constraints from conjuncts
    let relations = extract_implied_relations_from_conjuncts(conjuncts);

    // O(R) HashMap-based contradiction check (#3036).
    // For each normalized variable pair, accumulate all relations seen so far.
    // When inserting a new relation, check it against all existing relations
    // for the same pair. Since there are at most 4 relation types (Lt, Le, Gt, Ge),
    // the inner check is O(1) per insertion, making the total O(R).
    use ay_core::kani_compat::DetHashMap as FxHashMap;
    let mut seen: FxHashMap<(String, String), Vec<RelationType>> = FxHashMap::default();

    for (v1, v2, rel) in &relations {
        // Normalize to canonical order (v1 <= v2 lexicographically) so
        // (a,b) and (b,a) map to the same bucket.
        let (key, normalized_rel) = if v1 <= v2 {
            ((v1.clone(), v2.clone()), *rel)
        } else {
            ((v2.clone(), v1.clone()), flip_relation(*rel))
        };

        let entry = seen.entry(key).or_default();
        // Check new relation against all previously seen relations for this pair.
        // At most 4 distinct relation types exist, so this is O(1).
        for &existing in entry.iter() {
            if relations_contradict(existing, normalized_rel) {
                return true;
            }
        }
        entry.push(normalized_rel);
    }

    false
}

/// Extract implied relations from a list of conjuncts.
pub(super) fn extract_implied_relations_from_conjuncts(
    conjuncts: &[ChcExpr],
) -> Vec<(String, String, RelationType)> {
    let mut result = Vec::new();
    let mut disequalities: FxHashSet<(String, String)> = FxHashSet::default();

    // Single pass: collect direct relations and disequality pairs.
    for conjunct in conjuncts {
        if let Some(rel) = extract_relational_constraint(conjunct) {
            result.push(rel);
        }
        if let Some((v1, v2)) = extract_disequality_pair(conjunct) {
            disequalities.insert(normalize_var_pair(&v1, &v2));
        }
    }

    // Add strengthened bounds for (a >= b /\ a != b) and (a <= b /\ a != b).
    let direct_len = result.len();
    for idx in 0..direct_len {
        let (v1, v2, rel) = &result[idx];
        if disequalities.contains(&normalize_var_pair(v1, v2)) {
            let strengthened = match rel {
                RelationType::Ge => Some(RelationType::Gt),
                RelationType::Le => Some(RelationType::Lt),
                _ => None,
            };
            if let Some(new_rel) = strengthened {
                result.push((v1.clone(), v2.clone(), new_rel));
            }
        }
    }

    result
}

/// Extract a relational constraint from an expression.
fn extract_relational_constraint(expr: &ChcExpr) -> Option<(String, String, RelationType)> {
    match expr {
        ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
            let v1 = extract_var_name_from_expr(&args[0])?;
            let v2 = extract_var_name_from_expr(&args[1])?;
            Some((v1, v2, RelationType::Lt))
        }
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            let v1 = extract_var_name_from_expr(&args[0])?;
            let v2 = extract_var_name_from_expr(&args[1])?;
            Some((v1, v2, RelationType::Le))
        }
        ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
            let v1 = extract_var_name_from_expr(&args[0])?;
            let v2 = extract_var_name_from_expr(&args[1])?;
            Some((v1, v2, RelationType::Gt))
        }
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            let v1 = extract_var_name_from_expr(&args[0])?;
            let v2 = extract_var_name_from_expr(&args[1])?;
            Some((v1, v2, RelationType::Ge))
        }
        _ => None,
    }
}

/// Extract variable name from an expression if it's a simple variable.
fn extract_var_name_from_expr(expr: &ChcExpr) -> Option<String> {
    match expr {
        ChcExpr::Var(v) => Some(v.name.clone()),
        _ => None,
    }
}

/// Check if an expression is a disequality between two variables.
fn extract_disequality_pair(expr: &ChcExpr) -> Option<(String, String)> {
    match expr {
        ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
            let name1 = extract_var_name_from_expr(&args[0])?;
            let name2 = extract_var_name_from_expr(&args[1])?;
            Some((name1, name2))
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            if let ChcExpr::Op(ChcOp::Eq, eq_args) = args[0].as_ref() {
                if eq_args.len() == 2 {
                    let name1 = extract_var_name_from_expr(&eq_args[0])?;
                    let name2 = extract_var_name_from_expr(&eq_args[1])?;
                    return Some((name1, name2));
                }
            }
            None
        }
        _ => None,
    }
}

fn normalize_var_pair(v1: &str, v2: &str) -> (String, String) {
    if v1 <= v2 {
        (v1.to_string(), v2.to_string())
    } else {
        (v2.to_string(), v1.to_string())
    }
}

/// Check if two relations contradict each other.
fn relations_contradict(r1: RelationType, r2: RelationType) -> bool {
    matches!(
        (r1, r2),
        (RelationType::Lt, RelationType::Ge | RelationType::Gt)
            | (RelationType::Le, RelationType::Gt)
            | (RelationType::Gt, RelationType::Le | RelationType::Lt)
            | (RelationType::Ge, RelationType::Lt)
    )
}

/// Flip a relation (swap operands).
fn flip_relation(r: RelationType) -> RelationType {
    match r {
        RelationType::Lt => RelationType::Gt,
        RelationType::Le => RelationType::Ge,
        RelationType::Gt => RelationType::Lt,
        RelationType::Ge => RelationType::Le,
    }
}
