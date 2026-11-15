// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

//! Frozen orchestration from AY 0883923f8ab49875e84a2fd8100c215ba0fb6a3b,
//! bmc/mod.rs::simplify_exact_acyclic_conjuncts. Shared arithmetic helpers are
//! intentionally current: this is not an oracle for preserving their defects.

use super::*;

mod definitions;
mod intervals;

pub(super) fn simplify(conjuncts: Vec<ChcExpr>) -> ChcExpr {
    let infeasible = |conjuncts: &[ChcExpr], env: &mut FxHashMap<String, IntInterval>| {
        matches!(
            BmcSolver::collect_conjunct_interval_bounds(conjuncts, env, None),
            Ok(false)
        )
    };
    let mut conjuncts = ChcExpr::and_all(conjuncts)
        .propagate_equalities()
        .collect_conjuncts_nontrivial();
    let mut interval_env = FxHashMap::default();
    if infeasible(&conjuncts, &mut interval_env) {
        return ChcExpr::Bool(false);
    }
    let _ = intervals::substitute(&mut conjuncts, &interval_env);
    if infeasible(&conjuncts, &mut interval_env) {
        return ChcExpr::Bool(false);
    }
    let _ = BmcSolver::linearize_bounded_squares_in_conjuncts(&mut conjuncts, &interval_env);
    if infeasible(&conjuncts, &mut interval_env) {
        return ChcExpr::Bool(false);
    }
    let _ = intervals::substitute(&mut conjuncts, &interval_env);
    if infeasible(&conjuncts, &mut interval_env) {
        return ChcExpr::Bool(false);
    }
    let local_bool_vars = conjuncts
        .iter()
        .flat_map(ChcExpr::vars)
        .filter(|var| var.sort == ChcSort::Bool)
        .map(|var| var.name)
        .collect();
    let _ = BmcSolver::simplify_conjuncts_with_intervals_and_bools(
        &mut conjuncts,
        &mut interval_env,
        &local_bool_vars,
        None,
    );
    let _ = intervals::substitute(&mut conjuncts, &interval_env);
    if conjuncts.len() <= 512 {
        let _ = definitions::substitute(&mut conjuncts);
    }
    ChcExpr::and_all(conjuncts).propagate_equalities()
}
