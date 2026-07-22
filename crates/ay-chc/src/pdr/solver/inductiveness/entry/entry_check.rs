// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::predecessor_context;
use crate::pdr::solver::{EntryInductiveFailureReason, PdrSolver};
use crate::smt::SmtResult;
use crate::{ChcExpr, PredicateId};

pub(super) fn is_entry_inductive(
    solver: &mut PdrSolver,
    invariant: &ChcExpr,
    predicate: PredicateId,
    level: usize,
) -> bool {
    let prev_level = level.saturating_sub(1);

    // Collect entry clauses (inter-predicate transitions into this predicate),
    // retaining clause_index so clause-guarded propagated lemmas can be applied.
    let clauses: Vec<_> = solver
        .problem
        .clauses_defining_with_index(predicate)
        .map(|(clause_index, clause)| (clause_index, clause.clone()))
        .collect();
    'clause_check: for (clause_index, clause) in &clauses {
        // #2887: Check cancellation between SMT queries in clause loop.
        if solver.is_cancelled() {
            return solver.fail_entry_inductive(
                predicate,
                *clause_index,
                EntryInductiveFailureReason::Cancelled,
            );
        }
        if clause.body.predicates.is_empty() {
            continue;
        }

        let is_entry = clause
            .body
            .predicates
            .iter()
            .any(|(body_pred, _)| *body_pred != predicate);

        if !is_entry {
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
        const MAX_ENTRY_CEGAR_REFINEMENTS: usize = 16;
        for refine_iter in 0..MAX_ENTRY_CEGAR_REFINEMENTS {
            if solver.is_cancelled() {
                return solver.fail_entry_inductive(
                    predicate,
                    *clause_index,
                    EntryInductiveFailureReason::Cancelled,
                );
            }
            let neg_inv_on_head = match solver.apply_to_args(predicate, invariant, head_args) {
                Some(e) => ChcExpr::not(e),
                None => {
                    // Can't apply invariant to head args - reject conservatively
                    if solver.config.verbose {
                        safe_eprintln!(
                            "PDR: is_entry_inductive: cannot apply invariant to head args for pred {}",
                            predicate.index()
                        );
                    }
                    return solver.fail_entry_inductive(
                        predicate,
                        *clause_index,
                        EntryInductiveFailureReason::HeadInstantiationFailed,
                    );
                }
            };

            let guarded =
                solver.clause_guarded_constraint(predicate, *clause_index, head_args, level);
            let mut conjuncts = vec![clause_constraint.clone(), guarded, neg_inv_on_head];

            for (body_pred, body_args) in &clause.body.predicates {
                predecessor_context::push_entry_domain_context(
                    solver,
                    &mut conjuncts,
                    *body_pred,
                    body_args,
                    prev_level,
                );

                if prev_level == 0 {
                    predecessor_context::push_prev_level_zero_body_context(
                        solver,
                        &mut conjuncts,
                        *body_pred,
                        body_args,
                    );
                } else {
                    predecessor_context::push_prev_level_frame_context(
                        solver,
                        &mut conjuncts,
                        *body_pred,
                        body_args,
                        prev_level,
                    );
                }
            }

            let incr_query = solver.bound_int_vars(ChcExpr::and_all(
                conjuncts.iter().skip(1).cloned().collect::<Vec<_>>(),
            ));
            let query = solver.bound_int_vars(ChcExpr::and_all(conjuncts));

            let simplified = query.propagate_equalities();
            if matches!(simplified, ChcExpr::Bool(false)) {
                continue 'clause_check;
            }

            // #6358: Per-predicate prop_solver for entry inductiveness.
            // Pure-LIA: one solve via prop_solver, no double-solve fallback.
            let (smt_result, sat_query) = if solver.incremental_pdr_enabled() {
                let seg_key = crate::pdr::solver::prop_solver::SegmentKey::Inductiveness {
                    clause_index: *clause_index,
                };
                let prop = crate::pdr::solver::core::ensure_prop_solver_split(
                    &mut solver.prop_solvers,
                    &solver.frames,
                    predicate,
                );
                prop.register_segment(seg_key, &clause_constraint);
                let check_timeout = solver
                    .smt
                    .current_timeout()
                    .or(Some(std::time::Duration::from_secs(2)));
                let assumptions = [incr_query.clone()];
                let incr_result = prop.check_inductiveness(
                    solver.frames.len(),
                    *clause_index,
                    &assumptions,
                    check_timeout,
                    None,
                );
                match incr_result {
                    crate::smt::IncrementalCheckResult::Unsat => continue 'clause_check,
                    crate::smt::IncrementalCheckResult::Sat(model) => (SmtResult::Sat(model), None),
                    crate::smt::IncrementalCheckResult::Unknown => (SmtResult::Unknown, None),
                }
            } else {
                PdrSolver::check_sat_with_ite_case_split(
                    &mut solver.smt,
                    solver.config.verbose,
                    &query,
                )
            };

            match smt_result {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue 'clause_check;
                }
                SmtResult::Sat(model) => {
                    if solver.config.verbose {
                        safe_eprintln!(
                            "PDR: is_entry_inductive SAT at entry clause {:?} (iter {}/{}) for invariant {}",
                            clause.head,
                            refine_iter + 1,
                            MAX_ENTRY_CEGAR_REFINEMENTS,
                            invariant
                        );
                    }

                    // Entry-CEGAR currently supports single-predecessor clauses.
                    if clause.body.predicates.len() != 1 {
                        if solver.config.verbose {
                            safe_eprintln!(
                                "PDR: is_entry_inductive FAILED: invariant {} not inductive at entry clause {:?} (SAT; hyperedge)",
                                invariant, clause.head
                            );
                        }
                        return solver.fail_entry_inductive(
                            predicate,
                            *clause_index,
                            EntryInductiveFailureReason::SatHyperedge,
                        );
                    }

                    let (body_pred, body_args) = &clause.body.predicates[0];
                    if *body_pred == predicate {
                        return solver.fail_entry_inductive(
                            predicate,
                            *clause_index,
                            EntryInductiveFailureReason::UnexpectedSelfEdge,
                        );
                    }

                    let query_for_cube = sat_query.as_ref().unwrap_or(&query);
                    let Some(body_cube) = solver.cube_from_model_or_constraints(
                        *body_pred,
                        body_args,
                        query_for_cube,
                        &model,
                    ) else {
                        if solver.config.verbose {
                            safe_eprintln!(
                                "PDR: is_entry_inductive FAILED: could not extract predecessor cube for pred {} from entry SAT model",
                                body_pred.index()
                            );
                        }
                        return solver.fail_entry_inductive(
                            predicate,
                            *clause_index,
                            EntryInductiveFailureReason::CubeExtractionFailed,
                        );
                    };

                    if solver.config.verbose {
                        safe_eprintln!(
                            "PDR: is_entry_inductive entry SAT predecessor cube (pred {}, prev_level {}): {}",
                            body_pred.index(),
                            prev_level,
                            body_cube
                        );
                    }

                    // A cube intersecting backed reach facts is definitely reachable.
                    // IMPORTANT: Use is_reachable_backed (not is_reachable) to exclude
                    // filter-only entries that may over-approximate reachable states.
                    // Using is_reachable here would falsely reject valid invariants
                    // when heuristic loop-closure enrichments create spurious intersections.
                    if solver.reachability.reach_solvers.has_facts(*body_pred)
                        && solver.reachability.reach_solvers.is_reachable_backed(
                            &mut solver.smt,
                            *body_pred,
                            &body_cube,
                        )
                    {
                        if solver.config.verbose {
                            safe_eprintln!(
                                "PDR: is_entry_inductive FAILED: predecessor cube for pred {} intersects reach facts",
                                body_pred.index()
                            );
                        }
                        return solver.fail_entry_inductive(
                            predicate,
                            *clause_index,
                            EntryInductiveFailureReason::ReachFactIntersection,
                        );
                    }

                    // Entry-CEGAR discharge toggle (#1615).
                    if !solver.config.use_entry_cegar_discharge {
                        if solver.config.verbose {
                            safe_eprintln!(
                                "PDR: is_entry_inductive FAILED: invariant {} not inductive at entry clause {:?} (Entry-CEGAR disabled)",
                                invariant, clause.head
                            );
                        }
                        return solver.fail_entry_inductive(
                            predicate,
                            *clause_index,
                            EntryInductiveFailureReason::EntryCegarDisabled,
                        );
                    }

                    // Entry-CEGAR budget check (#1615).
                    const ENTRY_CEGAR_BUDGET_PER_PREDICATE: usize = 32;
                    let current_budget = *solver
                        .caches
                        .entry_cegar_budget
                        .entry(predicate)
                        .or_insert(ENTRY_CEGAR_BUDGET_PER_PREDICATE);
                    if current_budget == 0 {
                        if solver.config.verbose {
                            safe_eprintln!(
                                "PDR: is_entry_inductive FAILED: invariant {} not inductive at entry clause {:?} (budget exhausted)",
                                invariant, clause.head
                            );
                        }
                        return solver.fail_entry_inductive(
                            predicate,
                            *clause_index,
                            EntryInductiveFailureReason::EntryCegarBudgetExhausted,
                        );
                    }

                    const DISCHARGE_TIMEOUT_MS: u64 = 500;
                    let discharge_result = solver.entry_cegar_discharge_state(
                        *body_pred,
                        body_cube,
                        prev_level,
                        DISCHARGE_TIMEOUT_MS,
                    );

                    if let Some(budget) = solver.caches.entry_cegar_budget.get_mut(&predicate) {
                        *budget = budget.saturating_sub(1);
                    }

                    match discharge_result {
                        crate::pdr::solver::EntryCegarDischarge::Unreachable => continue,
                        crate::pdr::solver::EntryCegarDischarge::Reachable => {
                            if solver.config.verbose {
                                safe_eprintln!(
                                    "PDR: is_entry_inductive FAILED: invariant {} not inductive at entry clause {:?} (SAT; predecessor reachable/unknown)",
                                    invariant, clause.head
                                );
                            }
                            return solver.fail_entry_inductive(
                                predicate,
                                *clause_index,
                                EntryInductiveFailureReason::DischargeReachable,
                            );
                        }
                        crate::pdr::solver::EntryCegarDischarge::Unknown => {
                            if solver.config.verbose {
                                safe_eprintln!(
                                    "PDR: is_entry_inductive FAILED: invariant {} not inductive at entry clause {:?} (SAT; predecessor reachable/unknown)",
                                    invariant, clause.head
                                );
                            }
                            return solver.fail_entry_inductive(
                                predicate,
                                *clause_index,
                                EntryInductiveFailureReason::DischargeUnknown,
                            );
                        }
                    }
                }
                SmtResult::Unknown => {
                    // #6047: Removed array fallback. Executor adapter
                    // handles array queries natively.

                    if solver.config.verbose {
                        let timeout_note = if solver.smt.has_active_timeout() {
                            " (SMT timeout active)"
                        } else {
                            ""
                        };
                        safe_eprintln!(
                            "PDR: is_entry_inductive UNKNOWN{}: invariant {} at entry clause {:?} (rejecting conservatively)",
                            timeout_note, invariant, clause.head
                        );
                    }
                    return solver.fail_entry_inductive(
                        predicate,
                        *clause_index,
                        EntryInductiveFailureReason::SmtUnknownRejected,
                    );
                }
            }
        }

        if solver.config.verbose {
            safe_eprintln!(
                "PDR: is_entry_inductive FAILED: exceeded Entry-CEGAR refinements for invariant {} at entry clause {:?}",
                invariant, clause.head
            );
        }
        return solver.fail_entry_inductive(
            predicate,
            *clause_index,
            EntryInductiveFailureReason::RefinementLimitExceeded,
        );
    }

    if solver.config.verbose {
        safe_eprintln!(
            "PDR: is_entry_inductive SUCCESS for invariant {} at pred {} (level {})",
            invariant,
            predicate.index(),
            level
        );
    }
    true
}
