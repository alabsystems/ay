// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{ChcExpr, ChcSort, FxHashMap, InitIntBounds, PdrSolver, PredicateId, SmtResult};

pub(super) fn build_init_constraint_from_bounds(
    solver: &PdrSolver,
    pred: PredicateId,
    bounds: &FxHashMap<String, InitIntBounds>,
) -> Option<ChcExpr> {
    let canonical_vars = solver.canonical_vars(pred)?;
    let mut conjuncts = vec![];

    for var in canonical_vars {
        if !matches!(var.sort, ChcSort::Int) {
            continue;
        }
        if let Some(b) = bounds.get(&var.name) {
            if b.min == b.max {
                conjuncts.push(ChcExpr::eq(ChcExpr::var(var.clone()), ChcExpr::Int(b.min)));
            } else {
                if b.min != i128::MIN {
                    conjuncts.push(ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(b.min)));
                }
                if b.max != i128::MAX {
                    conjuncts.push(ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(b.max)));
                }
            }
        }
    }

    if conjuncts.is_empty() {
        None
    } else {
        Some(ChcExpr::and_all(conjuncts))
    }
}

pub(super) fn blocks_initial_states(
    solver: &mut PdrSolver,
    pred: PredicateId,
    formula: &ChcExpr,
) -> bool {
    let cache_key = (pred, formula.structural_hash());
    if let Some((cached_expr, cached_result)) = solver.caches.blocks_init_cache.get(&cache_key) {
        if cached_expr == formula {
            return *cached_result;
        }
    }

    let result = blocks_initial_states_uncached(solver, pred, formula);
    solver.insert_blocks_init_cache_entry(cache_key, (formula.clone(), result));
    result
}

pub(super) fn blocks_initial_states_uncached(
    solver: &mut PdrSolver,
    pred: PredicateId,
    formula: &ChcExpr,
) -> bool {
    let fact_data: Vec<(usize, ChcExpr, Vec<ChcExpr>)> = solver
        .problem
        .facts()
        .filter(|f| f.head.predicate_id() == Some(pred))
        .enumerate()
        .filter_map(|(fact_idx, fact)| {
            let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            match &fact.head {
                crate::ClauseHead::Predicate(_, args) => Some((fact_idx, constraint, args.clone())),
                crate::ClauseHead::False => None,
            }
        })
        .collect();

    if fact_data.is_empty() {
        return false;
    }

    for (fact_idx, fact_constraint, head_args) in &fact_data {
        if solver.is_cancelled() {
            return false;
        }
        let f_on_head = match solver.apply_to_args(pred, formula, head_args) {
            Some(e) => e,
            None => return false,
        };

        if solver.incremental_pdr_enabled() {
            let check_timeout = solver.smt.current_timeout();
            let seg_key = crate::pdr::solver::prop_solver::SegmentKey::InitBlocking {
                fact_index: *fact_idx,
            };
            let prop = crate::pdr::solver::core::ensure_prop_solver_split(
                &mut solver.prop_solvers,
                &solver.frames,
                pred,
            );
            prop.register_segment(seg_key, fact_constraint);
            let assumptions = [f_on_head.clone()];
            let incr_result = prop.check_init_blocking(
                solver.frames.len(),
                *fact_idx,
                &assumptions,
                check_timeout,
            );
            match incr_result {
                crate::smt::IncrementalCheckResult::Unsat => continue,
                crate::smt::IncrementalCheckResult::Sat(_) => return false,
                crate::smt::IncrementalCheckResult::Unknown => {}
            }
        }

        let query = solver.bound_int_vars(ChcExpr::and(fact_constraint.clone(), f_on_head));
        solver.smt.reset();
        match solver.smt.check_sat(&query) {
            SmtResult::Sat(_) => return false,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                continue
            }
            SmtResult::Unknown => return false,
        }
    }

    true
}
