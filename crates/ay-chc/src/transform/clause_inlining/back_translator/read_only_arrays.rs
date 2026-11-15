// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact elimination of read-only local arrays before projection.
//!
//! A synthesized interpretation is the defining body of an inlined predicate
//! with every non-formal variable existentially quantified. When such a local
//! is an array that the body only READS, at finitely many index terms that do
//! not mention it, Ackermann's reduction removes it exactly:
//!
//! ```text
//! ∃a. φ[select(a, t₁), …, select(a, tₙ)]
//!   ≡ ∃x₁ … xₙ. φ[x₁, …, xₙ] ∧ ⋀_{i<j} (tᵢ = tⱼ ⇒ xᵢ = xⱼ)
//! ```
//!
//! Left to right, take `xᵢ := a[tᵢ]`. Right to left, the constraints make
//! `tᵢ ↦ xᵢ` a function on the read points, and any total array extending it
//! is a witness for `a` (every sort here is inhabited, and nothing else
//! mentions `a`). Two indices that are distinct literals can never be equal,
//! so their constraint is a tautology and is left out. This is the select-only
//! case of model-based projection for arrays (Komuravelli, Bjørner, Gurfinkel,
//! McMillan, "Compositional Verification of Procedural Programs using Horn
//! Clauses over Integers and Arrays", FMCAD 2015); it is used here as an
//! equivalence, not as a model-guided under-approximation.
//!
//! Without it an inlined definition that reads a seeded memory array (model-checker-consumer
//! `safe_symbolic_from_elem`: `select(mem, v5)` after `mem[k] = …` facts) has
//! no closed interpretation: the scalar projection declines array sorts and
//! model-based projection cannot drop `mem`, so every Safe proof of the
//! inlined problem was discarded at back-translation.
//!
//! The rewrite is all-or-nothing per array: a local array that also occurs
//! anywhere else (a store, an equality, an index of another read, a predicate
//! argument) is left untouched, and any walk or rewrite budget that runs out
//! leaves the whole formula unchanged.

use super::{ChcExpr, ChcOp, ChcSort, ChcVar, FxHashMap, FxHashSet};

/// Nodes one eligibility walk may visit (DAG sharing is walked as a tree).
const MAX_VISITED_NODES: usize = 200_000;
/// Distinct read points of one array.
const MAX_READS_PER_ARRAY: usize = 32;
/// Functional-consistency constraints the whole rewrite may add. Each one is a
/// two-way disjunction the exact projection that follows distributes, within
/// its own budget of 64 branches.
const MAX_CONSISTENCY_CONSTRAINTS: usize = 6;

/// Ackermannize every read-only local array of `formula` (locals are the
/// variables not in `keep`). `None` when there is no such array or a bound was
/// reached; the caller then projects the original formula.
pub(super) fn ackermannize(formula: &ChcExpr, keep: &[ChcVar]) -> Option<ChcExpr> {
    let keep_names: FxHashSet<&str> = keep.iter().map(|var| var.name.as_str()).collect();
    let census = Census::take(formula, &keep_names)?;
    let mut used: FxHashSet<String> = census.names.clone();
    used.extend(keep.iter().map(|var| var.name.clone()));

    let mut pairs: Vec<(ChcExpr, ChcExpr)> = Vec::new();
    let mut constraints: Vec<ChcExpr> = Vec::new();
    let mut eliminated: Vec<&ChcVar> = Vec::new();
    for (array, reads) in &census.reads {
        if census.ineligible.contains(array.name.as_str()) || reads.len() > MAX_READS_PER_ARRAY {
            continue;
        }
        let ChcSort::Array(_, element) = &array.sort else {
            continue;
        };
        let mut points: Vec<(&ChcExpr, ChcVar)> = Vec::with_capacity(reads.len());
        for (position, index) in reads.iter().enumerate() {
            let name = reserve(format!("__ack{position}_{}", array.name), &mut used);
            let point = ChcVar::new(name, element.as_ref().clone());
            pairs.push((
                ChcExpr::select(ChcExpr::var(array.clone()), index.clone()),
                ChcExpr::var(point.clone()),
            ));
            points.push((index, point));
        }
        for (i, (left_index, left)) in points.iter().enumerate() {
            for (right_index, right) in &points[i + 1..] {
                if distinct_literals(left_index, right_index) {
                    continue;
                }
                constraints.push(ChcExpr::or(
                    ChcExpr::not(ChcExpr::eq((*left_index).clone(), (*right_index).clone())),
                    ChcExpr::eq(ChcExpr::var(left.clone()), ChcExpr::var(right.clone())),
                ));
                if constraints.len() > MAX_CONSISTENCY_CONSTRAINTS {
                    return None;
                }
            }
        }
        eliminated.push(array);
    }
    if eliminated.is_empty() {
        return None;
    }

    let rewritten = formula.substitute_expr_pairs(&pairs);
    // `substitute_expr_pairs` returns its input unchanged when it runs out of
    // budget. Only a formula in which no eliminated array survives is exact.
    let gone: FxHashSet<&str> = eliminated.iter().map(|var| var.name.as_str()).collect();
    if mentions_any(&rewritten, &gone)? {
        return None;
    }
    let mut conjuncts = Vec::with_capacity(constraints.len() + 1);
    conjuncts.push(rewritten);
    conjuncts.extend(constraints);
    Some(ChcExpr::and_all(conjuncts))
}

/// One walk over the formula: the read points of every local array, the
/// local arrays that occur other than as a read's base, and every name.
struct Census {
    /// First-occurrence order, deduplicated by structural equality.
    reads: Vec<(ChcVar, Vec<ChcExpr>)>,
    ineligible: FxHashSet<String>,
    names: FxHashSet<String>,
}

impl Census {
    fn take(formula: &ChcExpr, keep: &FxHashSet<&str>) -> Option<Self> {
        let mut census = Self {
            reads: Vec::new(),
            ineligible: FxHashSet::default(),
            names: FxHashSet::default(),
        };
        let mut slot: FxHashMap<String, usize> = FxHashMap::default();
        let mut pending: Vec<&ChcExpr> = vec![formula];
        let mut visited = 0usize;
        while let Some(expr) = pending.pop() {
            visited += 1;
            if visited > MAX_VISITED_NODES {
                return None;
            }
            match expr {
                ChcExpr::ArrayLambda(_) => return None,
                ChcExpr::Var(var) => {
                    census.names.insert(var.name.clone());
                    if is_local_array(var, keep) {
                        census.ineligible.insert(var.name.clone());
                    }
                }
                ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                    match args[0].as_ref() {
                        ChcExpr::Var(array) if is_local_array(array, keep) => {
                            census.names.insert(array.name.clone());
                            let index = args[1].as_ref();
                            let at = *slot.entry(array.name.clone()).or_insert_with(|| {
                                census.reads.push((array.clone(), Vec::new()));
                                census.reads.len() - 1
                            });
                            let reads = &mut census.reads[at].1;
                            if !reads.contains(index) {
                                reads.push(index.clone());
                            }
                        }
                        other => pending.push(other),
                    }
                    pending.push(args[1].as_ref());
                }
                ChcExpr::Op(_, args)
                | ChcExpr::PredicateApp(_, _, args)
                | ChcExpr::FuncApp(_, _, args) => {
                    pending.extend(args.iter().map(AsRef::as_ref));
                }
                ChcExpr::ConstArray(_, value) => pending.push(value.as_ref()),
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => {}
            }
        }
        // A read whose index mentions a local array cannot be replaced
        // independently of that array's own reads.
        let nested = {
            let local_arrays: FxHashSet<&str> = census
                .reads
                .iter()
                .map(|(array, _)| array.name.as_str())
                .chain(census.ineligible.iter().map(String::as_str))
                .collect();
            let mut nested = Vec::new();
            for (array, reads) in &census.reads {
                for index in reads {
                    if mentions_any(index, &local_arrays)? {
                        nested.push(array.name.clone());
                        break;
                    }
                }
            }
            nested
        };
        census.ineligible.extend(nested);
        Some(census)
    }
}

fn is_local_array(var: &ChcVar, keep: &FxHashSet<&str>) -> bool {
    matches!(var.sort, ChcSort::Array(_, _)) && !keep.contains(var.name.as_str())
}

/// Whether `expr` mentions a variable named in `names`; `None` past the walk
/// budget.
fn mentions_any(expr: &ChcExpr, names: &FxHashSet<&str>) -> Option<bool> {
    let mut pending: Vec<&ChcExpr> = vec![expr];
    let mut visited = 0usize;
    while let Some(expr) = pending.pop() {
        visited += 1;
        if visited > MAX_VISITED_NODES {
            return None;
        }
        match expr {
            ChcExpr::Var(var) if names.contains(var.name.as_str()) => return Some(true),
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => pending.extend(args.iter().map(AsRef::as_ref)),
            ChcExpr::ConstArray(_, value) => pending.push(value.as_ref()),
            _ => {}
        }
    }
    Some(false)
}

/// Two literals of one sort with different values: never equal.
fn distinct_literals(left: &ChcExpr, right: &ChcExpr) -> bool {
    match (left, right) {
        (ChcExpr::BitVec(a, aw), ChcExpr::BitVec(b, bw)) => aw == bw && a != b,
        (ChcExpr::Int(a), ChcExpr::Int(b)) => a != b,
        (ChcExpr::Bool(a), ChcExpr::Bool(b)) => a != b,
        _ => false,
    }
}

fn reserve(mut candidate: String, used: &mut FxHashSet<String>) -> String {
    // Each collision strictly lengthens the name; the used set is finite.
    while !used.insert(candidate.clone()) {
        candidate.push('_');
    }
    candidate
}

#[cfg(test)]
mod tests;
