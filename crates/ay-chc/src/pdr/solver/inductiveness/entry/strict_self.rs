// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::solver::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

pub(super) fn is_strictly_self_inductive_blocking(
    solver: &mut PdrSolver,
    blocking_formula: &ChcExpr,
    predicate: PredicateId,
) -> bool {
    let lemma = ChcExpr::not(blocking_formula.clone());
    // P0 (model-checker-consumer wishlist 2026-07-17 item 2): strict per-lemma UNSATs are
    // the sole justification for the `individually_inductive` whole-model
    // verification skip on native-BV problems (#5877 via
    // safety_proof_inductive.rs `all_strictly_inductive`). Compute the BV
    // gate once; used below to require dual-solver confirmation.
    let problem_has_bv = solver.problem.has_bv_sorts();
    let mut result = true;
    // #8578: Track whether any self-loop clause was actually checked.
    // If no self-loop clauses exist for this predicate, the inductiveness
    // check is vacuously true — but vacuous truth is NOT sufficient for
    // the `individually_inductive` flag. Acyclic predicates (e.g., in
    // straight-line CFGs) have no self-loops, so any lemma would pass
    // vacuously, even wrong ones like `_main_1 = 0` for an unconstrained
    // variable. Without this guard, PDR accepts wrong invariants and the
    // validation pipeline's `individually_inductive` bypass produces
    // false Safe results.
    let mut checked_any_self_loop = false;

    // Only check clauses defining this predicate (head == predicate),
    // matching is_self_inductive_blocking_uncached. Iterating all clauses
    // would apply the blocking formula to a different predicate's head args.
    // Includes clause index for incremental context keying (#6358).
    let clauses: Vec<_> = solver
        .problem
        .clauses_defining_with_index(predicate)
        .map(|(i, c)| (i, c.clone()))
        .collect();
    for (clause_index, clause) in &clauses {
        // #2887: Check cancellation between SMT queries in clause loop.
        if solver.is_cancelled() {
            return false;
        }
        // Skip fact clauses (no body predicates)
        if clause.body.predicates.is_empty() {
            continue;
        }

        // Handle hyperedge self-loops using the same UNSAT-sufficient query
        // as is_self_inductive_blocking_uncached, but without any frame-based
        // strengthening fallback.
        if clause.body.predicates.len() > 1 {
            let has_self_loop = clause
                .body
                .predicates
                .iter()
                .any(|(bp, _)| *bp == predicate);
            if !has_self_loop {
                continue;
            }

            checked_any_self_loop = true;
            if let Some(hyperedge_query) =
                solver.build_hyperedge_inductive_query(clause, predicate, &lemma)
            {
                match solver.check_hyperedge_inductive_query(
                    predicate,
                    *clause_index,
                    &hyperedge_query,
                ) {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        // Self-inductive for this hyperedge
                        continue;
                    }
                    SmtResult::Sat(_) | SmtResult::Unknown => {
                        // SAT (or Unknown) means we cannot prove strict self-inductiveness.
                        result = false;
                        break;
                    }
                }
            } else {
                result = false;
                break;
            }
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
            None => {
                result = false;
                break;
            }
        };

        let (body_pred, body_args) = &clause.body.predicates[0];
        if *body_pred != predicate {
            continue; // Self-loop only
        }
        checked_any_self_loop = true;
        let lemma_on_body = match solver.apply_to_args(predicate, &lemma, body_args) {
            Some(e) => e,
            None => {
                result = false;
                break;
            }
        };

        // #6358: Per-predicate prop_solver for multi-body inductiveness.
        // Pure-LIA: SAT is trusted (no ITE/mod/div). Unknown falls through to legacy.
        if solver.incremental_pdr_enabled() {
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
            let assumptions = [lemma_on_body.clone(), blocking_on_head.clone()];
            let incr_result = prop.check_inductiveness(
                solver.frames.len(),
                *clause_index,
                &assumptions,
                check_timeout,
                None,
            );

            match incr_result {
                crate::smt::IncrementalCheckResult::Unsat => {
                    continue;
                }
                crate::smt::IncrementalCheckResult::Sat(_) => {
                    // Pure-LIA: SAT is trusted.
                    result = false;
                    break;
                }
                crate::smt::IncrementalCheckResult::Unknown => {
                    // Unknown: fall through to non-incremental.
                }
            }
        }

        // Non-incremental path (incremental_pdr_enabled()=false, non-BV, or Unknown fallthrough).
        let query_parts = vec![lemma_on_body, clause_constraint, blocking_on_head];
        let query = solver.bound_int_vars(ChcExpr::and_all(query_parts));
        let simplified = query.propagate_equalities();
        if matches!(simplified, ChcExpr::Bool(false)) {
            continue;
        }

        let (smt_result, _) = PdrSolver::check_sat_with_ite_case_split(
            &mut solver.smt,
            solver.config.verbose,
            &simplified,
        );
        match smt_result {
            SmtResult::Sat(_) => {
                result = false;
                break;
            }
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                if problem_has_bv {
                    // P0 (model-checker-consumer wishlist item 2): on native-BV problems a
                    // strict per-lemma consecution UNSAT can grant
                    // `individually_inductive`, which SKIPS whole-model
                    // verification (#5877, safety_checks.rs). The internal BV
                    // theory path has produced wrong verdicts before (wishlist
                    // item 1), so a strict claim on a BV query requires DUAL
                    // confirmation: the independent ay-dpll executor pipeline
                    // must also prove Unsat.
                    //   executor Sat     -> false-UNSAT caught, not strict;
                    //   executor Unknown -> unconfirmed, NOT strict (fail-
                    //     closed). The lemma may still be admitted as frame-
                    //     relative self-inductive; the resulting model then
                    //     goes through whole-model verification instead of
                    //     the #5877 skip — a completeness degrade, never a
                    //     verdict flip.
                    let propagated = FxHashMap::default();
                    let cross_timeout = std::time::Duration::from_millis(800);
                    let cross_result =
                        solver
                            .smt
                            .check_sat_via_executor(&simplified, &propagated, cross_timeout);
                    match cross_result {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            // Dual-confirmed strict for this clause.
                        }
                        SmtResult::Sat(_) => {
                            if solver.config.verbose {
                                safe_eprintln!(
                                    "PDR: is_strictly_self_inductive_blocking BV false-UNSAT cross-check hit executor SAT"
                                );
                            }
                            result = false;
                            break;
                        }
                        SmtResult::Unknown => {
                            if solver.config.verbose {
                                safe_eprintln!(
                                    "PDR: is_strictly_self_inductive_blocking BV UNSAT unconfirmed by executor; not strict (fail-closed)"
                                );
                            }
                            result = false;
                            break;
                        }
                    }
                } else if solver.problem_is_integer_arithmetic && !simplified.contains_array_ops() {
                    let propagated = FxHashMap::default();
                    let cross_timeout = std::time::Duration::from_millis(500);
                    let cross_result =
                        solver
                            .smt
                            .check_sat_via_executor(&simplified, &propagated, cross_timeout);
                    if matches!(cross_result, SmtResult::Sat(_)) {
                        if solver.config.verbose {
                            safe_eprintln!(
                                "PDR: is_strictly_self_inductive_blocking false-UNSAT cross-check hit executor SAT"
                            );
                        }
                        result = false;
                        break;
                    }
                }
                // Self-inductive for this clause
            }
            SmtResult::Unknown => {
                result = false;
                break;
            }
        }
    }

    // #8578: Vacuous truth is not sufficient. If no self-loop clause
    // was actually checked, this predicate's lemma has not been proven
    // self-inductive — it just has no self-transitions to violate.
    result && checked_any_self_loop
}
