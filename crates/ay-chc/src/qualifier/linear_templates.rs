// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear qualifier-template instantiation.

use super::QualifierSet;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet as FxHashSet;

impl QualifierSet {
    /// Instantiate a set of candidate qualifiers over the given variables.
    ///
    /// This produces a conservative template family over integer variables:
    /// - `v ∘ c`, where ∘ ∈ {=, ≤, ≥}
    /// - `v1 ∘ v2`, where ∘ ∈ {=, ≤, ≥}
    pub(crate) fn instantiate(&self, vars: &[ChcVar]) -> Vec<ChcExpr> {
        let mut candidates: FxHashSet<ChcExpr> = FxHashSet::default();
        let int_vars = sorted_int_vars(vars);
        let constants = sorted_values(&self.constants);

        insert_constant_comparisons(&mut candidates, &int_vars, &constants);
        insert_variable_comparisons(&mut candidates, &int_vars);
        insert_sum_relations(&mut candidates, &int_vars);
        insert_sum_constants(&mut candidates, &int_vars, &constants);
        insert_difference_constants(&mut candidates, &int_vars, &constants);

        let coefficients = sorted_values(&self.coefficients);
        insert_scaled_differences(&mut candidates, &int_vars, &constants, &coefficients);

        // Self-product and cross-product qualifiers are injected separately by
        // CEGAR so they cannot displace linear qualifiers in its template budget.
        let mut out: Vec<ChcExpr> = candidates.into_iter().collect();
        out.sort_by_cached_key(ToString::to_string);
        out
    }
}

fn sorted_int_vars(vars: &[ChcVar]) -> Vec<ChcVar> {
    let mut int_vars: Vec<ChcVar> = vars
        .iter()
        .filter(|var| matches!(var.sort, ChcSort::Int))
        .cloned()
        .collect();
    int_vars.sort_by(|left, right| left.name.cmp(&right.name));
    int_vars
}

fn sorted_values(values: &FxHashSet<i128>) -> Vec<i128> {
    let mut sorted: Vec<i128> = values.iter().copied().collect();
    sorted.sort_unstable();
    sorted
}

fn insert_constant_comparisons(
    candidates: &mut FxHashSet<ChcExpr>,
    int_vars: &[ChcVar],
    constants: &[i128],
) {
    for var in int_vars {
        for &constant in constants {
            candidates.insert(ChcExpr::eq(
                ChcExpr::var(var.clone()),
                ChcExpr::int(constant),
            ));
            candidates.insert(ChcExpr::le(
                ChcExpr::var(var.clone()),
                ChcExpr::int(constant),
            ));
            candidates.insert(ChcExpr::ge(
                ChcExpr::var(var.clone()),
                ChcExpr::int(constant),
            ));
        }
    }
}

fn insert_variable_comparisons(candidates: &mut FxHashSet<ChcExpr>, int_vars: &[ChcVar]) {
    for (index, left) in int_vars.iter().enumerate() {
        for right in int_vars.iter().skip(index + 1) {
            let left = ChcExpr::var(left.clone());
            let right = ChcExpr::var(right.clone());
            candidates.insert(ChcExpr::eq(left.clone(), right.clone()));
            candidates.insert(ChcExpr::le(left.clone(), right.clone()));
            candidates.insert(ChcExpr::ge(left.clone(), right.clone()));
            candidates.insert(ChcExpr::le(right.clone(), left.clone()));
            candidates.insert(ChcExpr::ge(right, left));
        }
    }
}

/// Add `v1 + v2 {=, <=, >=} v3` for each three-variable combination.
fn insert_sum_relations(candidates: &mut FxHashSet<ChcExpr>, int_vars: &[ChcVar]) {
    if int_vars.len() < 3 {
        return;
    }
    for (left_index, left) in int_vars.iter().enumerate() {
        for (right_index, right) in int_vars.iter().enumerate().skip(left_index + 1) {
            let sum = ChcExpr::add(ChcExpr::var(left.clone()), ChcExpr::var(right.clone()));
            for (result_index, result) in int_vars.iter().enumerate() {
                if result_index == left_index || result_index == right_index {
                    continue;
                }
                let result = ChcExpr::var(result.clone());
                candidates.insert(ChcExpr::eq(sum.clone(), result.clone()));
                candidates.insert(ChcExpr::le(sum.clone(), result.clone()));
                candidates.insert(ChcExpr::ge(sum.clone(), result));
            }
        }
    }
}

/// Add `v1 + v2 {=, <=, >=} c` for each variable pair and constant.
fn insert_sum_constants(
    candidates: &mut FxHashSet<ChcExpr>,
    int_vars: &[ChcVar],
    constants: &[i128],
) {
    for (index, left) in int_vars.iter().enumerate() {
        for right in int_vars.iter().skip(index + 1) {
            let sum = ChcExpr::add(ChcExpr::var(left.clone()), ChcExpr::var(right.clone()));
            insert_constant_relations(candidates, &sum, constants);
        }
    }
}

/// Add `v1 - v2 {=, <=, >=} c` for each variable pair and constant.
fn insert_difference_constants(
    candidates: &mut FxHashSet<ChcExpr>,
    int_vars: &[ChcVar],
    constants: &[i128],
) {
    for (index, left) in int_vars.iter().enumerate() {
        for right in int_vars.iter().skip(index + 1) {
            let difference = ChcExpr::sub(ChcExpr::var(left.clone()), ChcExpr::var(right.clone()));
            insert_constant_relations(candidates, &difference, constants);
        }
    }
}

/// Add `v1 - k*v2 {=, <=, >=} c` for each ordered variable pair.
fn insert_scaled_differences(
    candidates: &mut FxHashSet<ChcExpr>,
    int_vars: &[ChcVar],
    constants: &[i128],
    coefficients: &[i128],
) {
    for &coefficient in coefficients {
        for (left_index, left) in int_vars.iter().enumerate() {
            for (right_index, right) in int_vars.iter().enumerate() {
                if left_index == right_index {
                    continue;
                }
                let scaled = ChcExpr::mul(ChcExpr::int(coefficient), ChcExpr::var(right.clone()));
                let difference = ChcExpr::sub(ChcExpr::var(left.clone()), scaled);
                insert_constant_relations(candidates, &difference, constants);
            }
        }
    }
}

fn insert_constant_relations(
    candidates: &mut FxHashSet<ChcExpr>,
    expression: &ChcExpr,
    constants: &[i128],
) {
    for &constant in constants {
        candidates.insert(ChcExpr::eq(expression.clone(), ChcExpr::int(constant)));
        candidates.insert(ChcExpr::le(expression.clone(), ChcExpr::int(constant)));
        candidates.insert(ChcExpr::ge(expression.clone(), ChcExpr::int(constant)));
    }
}
