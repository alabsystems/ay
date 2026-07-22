// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared inductive-blocking checks for lemma admission.
//!
//! This keeps the public `PdrSolver` method surface in `inductiveness/mod.rs`
//! while isolating the cached wrapper, uncached transition checks, and
//! hyperedge incremental helper into one focused module.

use super::super::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

fn array_unsat_is_cross_checked(
    solver: &mut PdrSolver,
    query: &ChcExpr,
    force_array_check: bool,
    context: &str,
) -> bool {
    if !force_array_check && !query.contains_array_ops() {
        return true;
    }

    let propagated = FxHashMap::default();
    let cross_timeout = std::time::Duration::from_millis(500);
    let cross_result = solver
        .smt
        .check_sat_via_executor(query, &propagated, cross_timeout);
    match &cross_result {
        SmtResult::Sat(_) => {
            if solver.config.verbose {
                safe_eprintln!("PDR: {context} array false-UNSAT cross-check hit executor SAT");
            }
            false
        }
        SmtResult::Unsat
        | SmtResult::UnsatWithCore(_)
        | SmtResult::UnsatWithFarkas(_)
        | SmtResult::Unknown => true,
    }
}

pub(super) fn check_hyperedge_inductive_query(
    solver: &mut PdrSolver,
    predicate: PredicateId,
    clause_index: usize,
    hyperedge_query: &super::super::hyperedge::HyperedgeInductiveQuery,
) -> SmtResult {
    if solver.incremental_pdr_enabled() {
        let seg_key = super::super::prop_solver::SegmentKey::Inductiveness { clause_index };
        let prop = super::super::core::ensure_prop_solver_split(
            &mut solver.prop_solvers,
            &solver.frames,
            predicate,
        );
        prop.register_segment(seg_key, &hyperedge_query.clause_constraint);
        let check_timeout = solver
            .smt
            .current_timeout()
            .or(Some(std::time::Duration::from_secs(2)));
        let assumptions = [
            hyperedge_query.candidate_on_body.clone(),
            hyperedge_query.violated_on_head.clone(),
        ];
        match prop.check_inductiveness(
            solver.frames.len(),
            clause_index,
            &assumptions,
            check_timeout,
            None,
        ) {
            crate::smt::IncrementalCheckResult::Unsat => SmtResult::Unsat,
            crate::smt::IncrementalCheckResult::Sat(model) => SmtResult::Sat(model),
            crate::smt::IncrementalCheckResult::Unknown => SmtResult::Unknown,
        }
    } else {
        let result = solver.smt.check_sat(&hyperedge_query.query);
        if matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ) && !array_unsat_is_cross_checked(
            solver,
            &hyperedge_query.query,
            hyperedge_query.query.contains_array_ops(),
            "hyperedge inductive query",
        ) {
            SmtResult::Unknown
        } else {
            result
        }
    }
}

pub(super) fn is_inductive_blocking(
    solver: &mut PdrSolver,
    blocking_formula: &ChcExpr,
    predicate: PredicateId,
    level: usize,
) -> bool {
    // Cache lookup: (predicate, level, formula_hash) -> (frame_epoch, result)
    // `true` results are stable: frames only strengthen, so an inductive
    // blocking formula stays inductive. `false` results are only valid while
    // no frame changed anywhere: the queries use cumulative frame constraints
    // over frames 1..=level-1 (and clause-guarded lemmas even at level 0), so
    // a lemma added at ANY lower frame — not just frames[level-1] — can turn
    // a rejection into an acceptance. The previous fingerprint
    // (frames[level-1].lemmas.len()) missed those and also missed
    // count-preserving add+subsume changes (#pdr-chain).
    let cache_key = (predicate, level, blocking_formula.structural_hash());
    let current_frame_epoch = solver.frames_lemma_epoch();

    if let Some((cached_expr, cached_frame_epoch, cached_result)) =
        solver.caches.inductive_blocking_cache.get(&cache_key)
    {
        // Collision safety (#2860): verify expression matches before using cached result.
        if cached_expr == blocking_formula
            && (*cached_result || *cached_frame_epoch == current_frame_epoch)
        {
            return *cached_result;
        }
        // Expression mismatch (collision) or frames changed with false result - recompute
    }

    let result = is_inductive_blocking_uncached(solver, blocking_formula, predicate, level);

    // Store with expression for collision detection (#2860)
    solver.insert_inductive_blocking_cache_entry(
        cache_key,
        (blocking_formula.clone(), current_frame_epoch, result),
    );
    result
}

pub(super) fn is_inductive_blocking_uncached(
    solver: &mut PdrSolver,
    blocking_formula: &ChcExpr,
    predicate: PredicateId,
    level: usize,
) -> bool {
    // Cached countermodels are only valid relative to the current frame state:
    // frames strengthen over time, so a state that was one-step reachable when
    // recorded may be unreachable now. Publish the epoch so stale models are
    // dropped instead of permanently rejecting now-inductive lemmas (#pdr-chain).
    let frame_epoch = solver.frames_lemma_epoch();
    solver
        .caches
        .implication_cache
        .note_frame_epoch(frame_epoch);
    // Fast path: check if any cached countermodel satisfies blocking_formula (#2126)
    if solver.caches.implication_cache.blocking_rejected_by_cache(
        predicate.index(),
        level,
        blocking_formula,
    ) {
        if solver.config.verbose {
            safe_eprintln!(
                "PDR: is_inductive_blocking fast reject via cached model for pred {} level {}",
                predicate.index(),
                level
            );
        }
        return false;
    }

    // Require that the lemma (NOT of blocking_formula) holds for ALL initial states.
    //
    // Many predicates have multiple initial states (e.g., array-typed init that only
    // constrains a few indices). If we only ensure the lemma is consistent with *some*
    // init state, PDR can learn lemmas that exclude legitimate init states and become
    // unsound (and will later fail model verification).
    let lemma = ChcExpr::not(blocking_formula.clone());
    if solver.predicate_has_facts(predicate) {
        let neg_lemma = ChcExpr::not(lemma);
        if !solver.blocks_initial_states(predicate, &neg_lemma) {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: is_inductive_blocking rejecting at level {}: blocking formula {} is consistent with init (would block init states)",
                    level, blocking_formula
                );
            }
            return false;
        }
    }

    if level == 0 {
        return level_zero_inductive_blocking(solver, blocking_formula, predicate);
    }

    let defining_clauses: Vec<_> = solver
        .problem
        .clauses_defining_with_index(predicate)
        .map(|(index, clause)| (index, clause.clone()))
        .collect();
    for (clause_index, clause) in defining_clauses {
        // #2901: Check cancellation between SMT queries in clause loop.
        if solver.is_cancelled() {
            return false;
        }
        if clause.body.predicates.is_empty() {
            continue;
        }
        let head_args = match &clause.head {
            crate::ClauseHead::Predicate(_, a) => a.as_slice(),
            crate::ClauseHead::False => continue,
        };
        let clause_constraint = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));
        let blocking_on_head = match solver.apply_to_args(predicate, blocking_formula, head_args) {
            Some(e) => e,
            None => return false,
        };
        let guarded = solver.clause_guarded_constraint(predicate, clause_index, head_args, level);
        let incr_clause_bg = clause_constraint.clone();
        let incr_blocking_on_head = blocking_on_head.clone();
        let incr_guarded = guarded.clone();
        let base = ChcExpr::and_all([clause_constraint, blocking_on_head, guarded]);

        if clause.body.predicates.len() > 1 {
            if level - 1 == 0 {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: is_inductive_blocking being conservative for hyperedge at level 1"
                    );
                }
                return false;
            }

            let mut body_constraints = Vec::with_capacity(clause.body.predicates.len());
            for (body_pred, body_args) in &clause.body.predicates {
                let frame_constraint = solver
                    .cumulative_frame_constraint(level - 1, *body_pred)
                    .unwrap_or(ChcExpr::Bool(true));
                match solver.apply_to_args(*body_pred, &frame_constraint, body_args) {
                    Some(e) => body_constraints.push(e),
                    None => return false,
                }
            }
            let all_body_constraints = ChcExpr::and_all(body_constraints);
            let query = solver.bound_int_vars(ChcExpr::and_all([base, all_body_constraints]));

            // #8660 Phase 2b: ROW-expand `select(store(...))` before simplification
            // so symbolic-index array queries reduce to LIA+ITE for the case splitter.
            // Mirrors the Phase 2 rewrite in
            // inductiveness/insertion/retry.rs::is_self_inductive_with_frame_context.
            let query_contains_array_ops = query.contains_array_ops();
            let row_expanded = query.expand_select_store_symbolic();
            let simplified = row_expanded.propagate_equalities();
            if matches!(simplified, ChcExpr::Bool(false)) {
                continue;
            }

            let (result, _) = PdrSolver::check_sat_with_ite_case_split(
                &mut solver.smt,
                solver.config.verbose,
                &simplified,
            );
            match result {
                SmtResult::Sat(ref model) => {
                    let canonical_vars = solver.canonical_vars(predicate).map(|vars| vars.to_vec());
                    super::super::core::record_validated_blocking_countermodel_from_head_args(
                        &mut solver.caches.implication_cache,
                        frame_epoch,
                        canonical_vars.as_deref(),
                        predicate,
                        level,
                        head_args,
                        model,
                        blocking_formula,
                    );
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    if array_unsat_is_cross_checked(
                        solver,
                        &simplified,
                        query_contains_array_ops,
                        "relative hyperedge inductive blocking",
                    ) {
                        continue;
                    }
                    return false;
                }
                SmtResult::Unknown => return false,
            }
        }

        let (body_pred, body_args) = &clause.body.predicates[0];
        if level - 1 == 0 {
            let matching_facts: Vec<_> = solver
                .problem
                .facts()
                .filter(|f| f.head.predicate_id() == Some(*body_pred))
                .cloned()
                .collect();
            for fact in matching_facts {
                let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                let fact_head_args = match &fact.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                if fact_head_args.len() != body_args.len() {
                    continue;
                }

                let (renamed_fact_constraint, renamed_fact_args) =
                    PdrSolver::rename_fact_variables(&fact_constraint, fact_head_args, "__fact_");

                let eqs: Vec<ChcExpr> = body_args
                    .iter()
                    .cloned()
                    .zip(renamed_fact_args.iter().cloned())
                    .map(|(a, b)| ChcExpr::eq(a, b))
                    .collect();
                let init_match = ChcExpr::and_all(eqs);
                let query = solver.bound_int_vars(ChcExpr::and_all([
                    base.clone(),
                    renamed_fact_constraint,
                    init_match,
                ]));

                // #8660 Phase 2b: ROW-expand before simplification so array-typed
                // predicate init queries reduce to LIA+ITE.
                let query_contains_array_ops = query.contains_array_ops();
                let row_expanded = query.expand_select_store_symbolic();
                let simplified = row_expanded.propagate_equalities();
                if matches!(simplified, ChcExpr::Bool(false)) {
                    continue;
                }

                let (result, _) = PdrSolver::check_sat_with_ite_case_split(
                    &mut solver.smt,
                    solver.config.verbose,
                    &simplified,
                );
                match result {
                    SmtResult::Sat(ref model) => {
                        let canonical_vars =
                            solver.canonical_vars(predicate).map(|vars| vars.to_vec());
                        super::super::core::record_validated_blocking_countermodel_from_head_args(
                            &mut solver.caches.implication_cache,
                            frame_epoch,
                            canonical_vars.as_deref(),
                            predicate,
                            level,
                            head_args,
                            model,
                            blocking_formula,
                        );
                        return false;
                    }
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        if array_unsat_is_cross_checked(
                            solver,
                            &simplified,
                            query_contains_array_ops,
                            "relative init-fact inductive blocking",
                        ) {
                            continue;
                        }
                        return false;
                    }
                    SmtResult::Unknown => return false,
                }
            }
        } else {
            let frame_constraint = solver
                .cumulative_frame_constraint(level - 1, *body_pred)
                .unwrap_or(ChcExpr::Bool(true));
            let frame_on_body = match solver.apply_to_args(*body_pred, &frame_constraint, body_args)
            {
                Some(e) => e,
                None => return false,
            };

            if solver.incremental_pdr_enabled() {
                let check_timeout = solver.smt.current_timeout();
                let seg_key = super::super::prop_solver::SegmentKey::Inductiveness { clause_index };
                let prop = super::super::core::ensure_prop_solver_split(
                    &mut solver.prop_solvers,
                    &solver.frames,
                    predicate,
                );
                prop.register_segment(seg_key, &incr_clause_bg);
                let assumptions = [incr_blocking_on_head, incr_guarded, frame_on_body.clone()];
                let incr_result = prop.check_inductiveness(
                    solver.frames.len(),
                    clause_index,
                    &assumptions,
                    check_timeout,
                    None,
                );
                match incr_result {
                    crate::smt::IncrementalCheckResult::Unsat => {
                        continue;
                    }
                    crate::smt::IncrementalCheckResult::Sat(ref model) => {
                        let canonical_vars =
                            solver.canonical_vars(predicate).map(|vars| vars.to_vec());
                        super::super::core::record_validated_blocking_countermodel_from_head_args(
                            &mut solver.caches.implication_cache,
                            frame_epoch,
                            canonical_vars.as_deref(),
                            predicate,
                            level,
                            head_args,
                            model,
                            blocking_formula,
                        );
                        return false;
                    }
                    crate::smt::IncrementalCheckResult::Unknown => {}
                }
            }

            let query = solver.bound_int_vars(ChcExpr::and_all([base, frame_on_body]));

            // #8660 Phase 2b: ROW-expand symbolic select/store chains before
            // simplification so frame-relative inductiveness queries reduce to
            // LIA+ITE.
            let query_contains_array_ops = query.contains_array_ops();
            let row_expanded = query.expand_select_store_symbolic();
            let simplified = row_expanded.propagate_equalities();
            if matches!(simplified, ChcExpr::Bool(false)) {
                continue;
            }

            let (result, _) = PdrSolver::check_sat_with_ite_case_split(
                &mut solver.smt,
                solver.config.verbose,
                &simplified,
            );
            match result {
                SmtResult::Sat(ref model) => {
                    let canonical_vars = solver.canonical_vars(predicate).map(|vars| vars.to_vec());
                    super::super::core::record_validated_blocking_countermodel_from_head_args(
                        &mut solver.caches.implication_cache,
                        frame_epoch,
                        canonical_vars.as_deref(),
                        predicate,
                        level,
                        head_args,
                        model,
                        blocking_formula,
                    );
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    if array_unsat_is_cross_checked(
                        solver,
                        &simplified,
                        query_contains_array_ops,
                        "relative frame inductive blocking",
                    ) {
                        continue;
                    }
                    return false;
                }
                SmtResult::Unknown => return false,
            }
        }
    }

    true
}

fn level_zero_inductive_blocking(
    solver: &mut PdrSolver,
    blocking_formula: &ChcExpr,
    predicate: PredicateId,
) -> bool {
    // Level-zero queries still include clause-guarded frame lemmas, so the
    // recorded countermodels are frame-relative too (#pdr-chain).
    let frame_epoch = solver.frames_lemma_epoch();
    if !solver.predicate_has_facts(predicate) {
        return true;
    }
    if !solver.blocks_initial_states(predicate, blocking_formula) {
        return false;
    }

    let defining_clauses: Vec<_> = solver
        .problem
        .clauses_defining_with_index(predicate)
        .map(|(index, clause)| (index, clause.clone()))
        .collect();
    for (clause_index, clause) in defining_clauses {
        if solver.is_cancelled() {
            return false;
        }
        if clause.body.predicates.is_empty() {
            continue;
        }
        let head_args = match &clause.head {
            crate::ClauseHead::Predicate(_, a) => a.as_slice(),
            crate::ClauseHead::False => continue,
        };
        let clause_constraint = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));
        let blocking_on_head = match solver.apply_to_args(predicate, blocking_formula, head_args) {
            Some(e) => e,
            None => return false,
        };
        let guarded = solver.clause_guarded_constraint(predicate, clause_index, head_args, 1);
        let base = ChcExpr::and_all([
            clause_constraint.clone(),
            blocking_on_head.clone(),
            guarded.clone(),
        ]);

        if clause.body.predicates.len() == 1 {
            let (body_pred, body_args) = &clause.body.predicates[0];
            let matching_facts: Vec<_> = solver
                .problem
                .clauses()
                .iter()
                .enumerate()
                .filter(|(_, f)| f.is_fact() && f.head.predicate_id() == Some(*body_pred))
                .map(|(index, fact)| (index, fact.clone()))
                .collect();
            for (fact_index, fact) in matching_facts {
                let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                let fact_head_args = match &fact.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                if fact_head_args.len() != body_args.len() {
                    continue;
                }

                let (renamed_fact_constraint, renamed_fact_args) =
                    PdrSolver::rename_fact_variables(&fact_constraint, fact_head_args, "__fact_");

                let eqs: Vec<ChcExpr> = body_args
                    .iter()
                    .cloned()
                    .zip(renamed_fact_args.iter().cloned())
                    .map(|(a, b)| ChcExpr::eq(a, b))
                    .collect();
                let init_match = ChcExpr::and_all(eqs);

                if solver.incremental_pdr_enabled()
                    && (!solver.uses_arrays || !blocking_formula.contains_array_ops())
                {
                    let check_timeout = solver.smt.current_timeout();
                    let seg_key = super::super::prop_solver::SegmentKey::InitInductiveness {
                        clause_index,
                        fact_index,
                    };
                    let prop = super::super::core::ensure_prop_solver_split(
                        &mut solver.prop_solvers,
                        &solver.frames,
                        predicate,
                    );
                    prop.register_segment_multi(
                        seg_key,
                        &[
                            clause_constraint.clone(),
                            renamed_fact_constraint.clone(),
                            init_match.clone(),
                        ],
                    );
                    let incr_assumptions = [blocking_on_head.clone(), guarded.clone()];
                    let incr_result = prop.check_init_inductiveness(
                        solver.frames.len(),
                        clause_index,
                        fact_index,
                        &incr_assumptions,
                        check_timeout,
                    );
                    match incr_result {
                        crate::smt::IncrementalCheckResult::Unsat => {
                            continue;
                        }
                        crate::smt::IncrementalCheckResult::Sat(ref model) => {
                            let canonical_vars =
                                solver.canonical_vars(predicate).map(|vars| vars.to_vec());
                            super::super::core::record_validated_blocking_countermodel_from_head_args(
                                &mut solver.caches.implication_cache,
                        frame_epoch,
                                canonical_vars.as_deref(),
                                predicate,
                                0,
                                head_args,
                                model,
                                blocking_formula,
                            );
                            if solver.config.verbose {
                                safe_eprintln!(
                                    "PDR: is_inductive_blocking at level 0: incr SAT — transition from init reaches blocked state"
                                );
                            }
                            return false;
                        }
                        crate::smt::IncrementalCheckResult::Unknown => {}
                    }
                }

                let query = solver.bound_int_vars(ChcExpr::and_all([
                    base.clone(),
                    renamed_fact_constraint,
                    init_match,
                ]));

                // #8660 Phase 2b: ROW-expand before simplification so
                // level-zero init-blocking queries reduce to LIA+ITE.
                let query_contains_array_ops = query.contains_array_ops();
                let row_expanded = query.expand_select_store_symbolic();
                let simplified = row_expanded.propagate_equalities();
                if matches!(simplified, ChcExpr::Bool(false)) {
                    continue;
                }

                let (result, _) = PdrSolver::check_sat_with_ite_case_split(
                    &mut solver.smt,
                    solver.config.verbose,
                    &simplified,
                );
                match result {
                    SmtResult::Sat(ref model) => {
                        let canonical_vars =
                            solver.canonical_vars(predicate).map(|vars| vars.to_vec());
                        super::super::core::record_validated_blocking_countermodel_from_head_args(
                            &mut solver.caches.implication_cache,
                            frame_epoch,
                            canonical_vars.as_deref(),
                            predicate,
                            0,
                            head_args,
                            model,
                            blocking_formula,
                        );
                        if solver.config.verbose {
                            safe_eprintln!(
                                "PDR: is_inductive_blocking at level 0: transition from init reaches blocked state"
                            );
                        }
                        return false;
                    }
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        if array_unsat_is_cross_checked(
                            solver,
                            &simplified,
                            query_contains_array_ops,
                            "level-zero init inductive blocking",
                        ) {
                            continue;
                        }
                        return false;
                    }
                    SmtResult::Unknown => return false,
                }
            }
        }
    }
    true
}
