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

mod scans;
use scans::{
    contains_all_checked, contains_any_checked, has_bv2nat_constant_contradiction_checked,
};

/// Returns true when `expr` is variable-free and therefore denotes a ground term.
fn is_var_free(expr: &ChcExpr) -> bool {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::ArrayLambda(lambda) => lambda.captures().iter().all(|value| is_var_free(value)),
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
    is_trivial_contradiction_checked(expr, || false).unwrap_or(false)
}

/// A cancelled scan returns no mathematical answer, never a partial
/// contradiction result. The ordinary wrapper retains the complete scan.
pub(crate) fn is_trivial_contradiction_checked(
    expr: &ChcExpr,
    mut stop: impl FnMut() -> bool,
) -> Option<bool> {
    let result = trivial_contradiction_inner(expr, &mut stop)?;
    if stop() {
        None
    } else {
        Some(result)
    }
}

fn trivial_contradiction_inner(expr: &ChcExpr, mut stop: &mut dyn FnMut() -> bool) -> Option<bool> {
    let conjuncts = expr.collect_conjuncts_checked(&mut stop)?;
    let mut positive: FxHashSet<&ChcExpr> = FxHashSet::default();
    let mut negated: FxHashSet<&ChcExpr> = FxHashSet::default();
    for conjunct in &conjuncts {
        if stop() {
            return None;
        }
        match conjunct {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                let inner = args[0].as_ref();
                if positive.contains(inner) {
                    return Some(true);
                }
                if let ChcExpr::Op(ChcOp::Or, disjuncts) = inner {
                    if contains_any_checked(&positive, disjuncts, &mut stop)? {
                        return Some(true);
                    }
                }
                negated.insert(inner);
            }
            _ => {
                if negated.contains(conjunct) {
                    return Some(true);
                }
                for prior in &negated {
                    if stop() {
                        return None;
                    }
                    if let ChcExpr::Op(ChcOp::Or, disjuncts) = prior {
                        for disjunct in disjuncts {
                            if stop() {
                                return None;
                            }
                            if disjunct.as_ref() == conjunct {
                                return Some(true);
                            }
                        }
                    }
                }
                positive.insert(conjunct);
            }
        }
    }
    for prior in &negated {
        if stop() {
            return None;
        }
        match prior {
            ChcExpr::Op(ChcOp::Or, disjuncts) => {
                if contains_any_checked(&positive, disjuncts, &mut stop)? {
                    return Some(true);
                }
            }
            ChcExpr::Op(ChcOp::And, inner) => {
                if contains_all_checked(&positive, inner, &mut stop)? {
                    return Some(true);
                }
            }
            _ => {}
        }
    }
    if has_relational_contradiction_checked(&conjuncts, &mut stop)? {
        return Some(true);
    }
    if has_bv2nat_constant_contradiction_checked(&conjuncts, &mut stop)? {
        return Some(true);
    }
    if stop() {
        None
    } else {
        Some(false)
    }
}

/// Check if a list of conjuncts contains contradictory relational constraints.
/// Examples:
/// - (a <= b) and (a > b) → contradiction
/// - (a <= b) and (a >= b) and (a != b) → contradiction (since a <= b && a >= b implies a = b)
pub(in crate::pdr) fn has_relational_contradiction(conjuncts: &[ChcExpr]) -> bool {
    has_relational_contradiction_checked(conjuncts, &mut || false).unwrap_or(false)
}

pub(in crate::pdr) fn has_relational_contradiction_checked(
    conjuncts: &[ChcExpr],
    stop: &mut dyn FnMut() -> bool,
) -> Option<bool> {
    // Extract relational constraints from conjuncts
    let relations = extract_implied_relations_from_conjuncts_checked(conjuncts, stop)?;

    // O(R) HashMap-based contradiction check (#3036).
    // For each normalized variable pair, accumulate all relations seen so far.
    // When inserting a new relation, check it against all existing relations
    // for the same pair. Since there are at most 4 relation types (Lt, Le, Gt, Ge),
    // the inner check is O(1) per insertion, making the total O(R).
    use ay_core::kani_compat::DetHashMap as FxHashMap;
    let mut seen: FxHashMap<(String, String), Vec<RelationType>> = FxHashMap::default();

    for (v1, v2, rel) in &relations {
        if stop() {
            return None;
        }
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
            if stop() {
                return None;
            }
            if relations_contradict(existing, normalized_rel) {
                return Some(true);
            }
        }
        entry.push(normalized_rel);
    }

    Some(false)
}

/// Extract implied relations from a list of conjuncts.
pub(super) fn extract_implied_relations_from_conjuncts(
    conjuncts: &[ChcExpr],
) -> Vec<(String, String, RelationType)> {
    extract_implied_relations_from_conjuncts_checked(conjuncts, &mut || false).unwrap_or_default()
}

pub(super) fn extract_implied_relations_from_conjuncts_checked(
    conjuncts: &[ChcExpr],
    stop: &mut dyn FnMut() -> bool,
) -> Option<Vec<(String, String, RelationType)>> {
    let mut result = Vec::new();
    let mut disequalities: FxHashSet<(String, String)> = FxHashSet::default();

    // Single pass: collect direct relations and disequality pairs.
    for conjunct in conjuncts {
        if stop() {
            return None;
        }
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
        if stop() {
            return None;
        }
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

    Some(result)
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
