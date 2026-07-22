// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::pdr::solver::core;
use crate::pdr::solver::prop_solver::SegmentKey;
use crate::HornClause;

impl PdrSolver {
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::result_large_err)]
    pub(super) fn check_prev_level_zero_predecessor(
        &mut self,
        pob: &ProofObligation,
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
        clause_index: usize,
        base: &ChcExpr,
        clause_constraint: &ChcExpr,
        head_args: &[ChcExpr],
        state_on_head: &ChcExpr,
        guarded: &ChcExpr,
        clause: &HornClause,
        transition_constraints: &mut Vec<ChcExpr>,
        clause_interpolation_data: &mut Vec<ClauseInterpolationData>,
        had_sat_no_cube: &mut bool,
    ) -> Result<(), BlockResult> {
        let (body_pred, body_args) = &clause.body.predicates[0];
        for (fact_index, fact) in self
            .problem
            .clauses_defining_with_index(*body_pred)
            .filter(|(_, f)| f.is_fact())
        {
            let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let fact_head_args = match &fact.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };
            if fact_head_args.len() != body_args.len() {
                continue;
            }
            let eqs: Vec<ChcExpr> = body_args
                .iter()
                .cloned()
                .zip(fact_head_args.iter().cloned())
                .map(|(a, b)| ChcExpr::eq(a, b))
                .collect();
            let init_match = ChcExpr::and_all(eqs);

            let exclusion_constraint = self.predecessor_exclusion_constraint(
                "[prev_level=0]",
                pob.level,
                *body_pred,
                body_args,
                unknown_predecessors,
            );

            let query = self.bound_int_vars(ChcExpr::and_all([
                base.clone(),
                fact_constraint.clone(),
                init_match.clone(),
                exclusion_constraint.clone(),
            ]));

            // #8660 Phase 2b: ROW-expand `select(store(...))` (incl. symbolic
            // ITE form) before dispatching to the array or SMT check. This
            // matches the expansion applied in
            // inductiveness/insertion/retry.rs for self-inductiveness queries
            // so blocking/reachability queries along this path no longer
            // return UNKNOWN on symbolic-index array reads.
            let query = query.expand_select_store_symbolic();

            if self.config.verbose {
                safe_eprintln!("PDR: Checking predecessor at prev_level=0:");
                safe_eprintln!("  base={}", base);
                safe_eprintln!("  query={}", query);
            }

            let projection_vars = self.projection_vars_for_args(*body_pred, body_args);
            let verbose = self.config.verbose;
            let (result, sat_query) = if self.uses_arrays && query.contains_array_ops() {
                let query_delta = ChcExpr::and_all([
                    state_on_head.clone(),
                    guarded.clone(),
                    exclusion_constraint.clone(),
                ]);
                (
                    Self::check_array_clause_query(
                        &mut self.smt,
                        &mut self.array_clause_sessions,
                        ArraySessionKey::PrevLevelInit {
                            clause_index,
                            fact_index,
                        },
                        &ChcExpr::and_all([
                            clause_constraint.clone(),
                            fact_constraint.clone(),
                            init_match.clone(),
                        ]),
                        &query_delta,
                        &query,
                        self.max_array_params,
                    ),
                    None,
                )
            } else if self.incremental_pdr_enabled() {
                let check_timeout = self.smt.current_timeout();
                let seg_key = SegmentKey::ClauseFactBlocking {
                    clause_index,
                    fact_index,
                };
                let prop = core::ensure_prop_solver_split(
                    &mut self.prop_solvers,
                    &self.frames,
                    pob.predicate,
                );
                prop.register_segment_multi(
                    seg_key,
                    &[
                        clause_constraint.clone(),
                        fact_constraint.clone(),
                        init_match.clone(),
                    ],
                );
                let incr_result = prop.check_clause_fact_blocking(
                    clause_index,
                    fact_index,
                    &[
                        state_on_head.clone(),
                        guarded.clone(),
                        exclusion_constraint.clone(),
                    ],
                    check_timeout,
                    pob.smt_model.as_ref(),
                );
                match incr_result {
                    IncrementalCheckResult::Unsat => (SmtResult::Unsat, None),
                    IncrementalCheckResult::Sat(model) => (SmtResult::Sat(model), None),
                    IncrementalCheckResult::Unknown => (SmtResult::Unknown, None),
                }
            } else {
                self.smt
                    .with_phase_seed_model(pob.smt_model.as_ref(), |smt| {
                        Self::check_sat_with_ite_case_split(smt, verbose, &query)
                    })
            };
            let farkas_conflicts = if result.is_unsat() {
                extract_farkas_from_result(result.clone())
            } else {
                Vec::new()
            };
            match result {
                SmtResult::Sat(model) => {
                    let query_for_cube = sat_query.as_ref().unwrap_or(&query);
                    let model = Self::minimize_projection_model_with_context(
                        &mut self.smt,
                        &projection_vars,
                        query_for_cube,
                        model,
                    );
                    if self.config.verbose {
                        safe_eprintln!("  Result: SAT with {:?}", model);
                    }
                    // #8660: Prefer scalar-only cubes for array problems, but
                    // keep property-relevant array selects when the property
                    // reads arrays (Mem-track fix).
                    let cube = if self.uses_arrays {
                        self.cube_from_model_array_aware(
                            *body_pred,
                            body_args,
                            query_for_cube,
                            &model,
                        )
                    } else {
                        self.cube_with_mbp(*body_pred, body_args, query_for_cube, &model)
                    };
                    let cube = match cube {
                        Some(c) => c,
                        None => {
                            *had_sat_no_cube = true;
                            self.telemetry.sat_no_cube_events += 1;
                            continue;
                        }
                    };
                    return Err(BlockResult::Reachable(Box::new(PredecessorState {
                        predicate: *body_pred,
                        state: cube,
                        clause_index,
                        smt_model: model,
                        derivation_id: None,
                    })));
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    if self.config.use_interpolation {
                        let transition = ChcExpr::and_all([
                            clause_constraint.clone(),
                            fact_constraint.clone(),
                            init_match.clone(),
                        ]);
                        clause_interpolation_data.push(ClauseInterpolationData {
                            head_args: head_args.to_vec(),
                            constraint: transition.clone(),
                            farkas_conflicts,
                        });
                        let transition_canonical = if let Some(canon_vars) =
                            self.canonical_vars(pob.predicate)
                        {
                            Self::translate_to_canonical_names(&transition, head_args, canon_vars)
                        } else {
                            transition
                        };
                        transition_constraints.push(transition_canonical);
                    }
                    continue;
                }
                SmtResult::Unknown => return Err(BlockResult::Unknown),
            }
        }

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::result_large_err)]
    pub(super) fn check_single_body_predecessor(
        &mut self,
        pob: &ProofObligation,
        prev_level: usize,
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
        clause_index: usize,
        base: &ChcExpr,
        clause_constraint: &ChcExpr,
        head_args: &[ChcExpr],
        state_on_head: &ChcExpr,
        guarded: &ChcExpr,
        clause: &HornClause,
        transition_constraints: &mut Vec<ChcExpr>,
        clause_interpolation_data: &mut Vec<ClauseInterpolationData>,
        had_sat_no_cube: &mut bool,
    ) -> Result<(), BlockResult> {
        let (body_pred, body_args) = &clause.body.predicates[0];
        let frame_constraint = self.frames[prev_level]
            .get_predicate_constraint(*body_pred)
            .unwrap_or(ChcExpr::Bool(true));
        let frame_on_body = match self.apply_to_args(*body_pred, &frame_constraint, body_args) {
            Some(e) => e,
            None => return Err(BlockResult::Unknown),
        };

        let exclusion_constraint = self.predecessor_exclusion_constraint(
            "",
            pob.level,
            *body_pred,
            body_args,
            unknown_predecessors,
        );

        let query = self.bound_int_vars(ChcExpr::and_all([
            base.clone(),
            frame_on_body.clone(),
            exclusion_constraint.clone(),
        ]));

        // #8660 Phase 2b: ROW-expand `select(store(...))` (incl. symbolic
        // ITE form) before simplification/dispatch so predecessor blocking
        // queries with symbolic store indices reduce to LIA+ITE and avoid
        // UNKNOWN from the array theory.
        let query = query.expand_select_store_symbolic();

        if self.config.verbose {
            safe_eprintln!("PDR: Checking predecessor reachability:");
            safe_eprintln!(
                "  prev_level={}, frame_constraint={}",
                prev_level,
                frame_constraint
            );
            safe_eprintln!("  frame_on_body={}", frame_on_body);
            safe_eprintln!("  base={}", base);
            safe_eprintln!("  query={}", query);
        }

        let simplified = query.propagate_equalities();
        if matches!(simplified, ChcExpr::Bool(false)) {
            if self.config.verbose {
                safe_eprintln!("  Result: UNSAT (propagation)");
            }
            return Ok(());
        }

        let projection_vars = self.projection_vars_for_args(*body_pred, body_args);
        let verbose = self.config.verbose;
        let (result, sat_query) = if self.uses_arrays && query.contains_array_ops() {
            let query_delta = ChcExpr::and_all([
                state_on_head.clone(),
                guarded.clone(),
                frame_on_body.clone(),
                exclusion_constraint.clone(),
            ]);
            (
                Self::check_array_clause_query(
                    &mut self.smt,
                    &mut self.array_clause_sessions,
                    ArraySessionKey::SingleBody { clause_index },
                    &clause_constraint.clone(),
                    &query_delta,
                    &query,
                    self.max_array_params,
                ),
                None,
            )
        } else if self.incremental_pdr_enabled() {
            let check_timeout = self.smt.current_timeout();
            let seg_key = SegmentKey::ClauseBlocking { clause_index };
            let prop =
                core::ensure_prop_solver_split(&mut self.prop_solvers, &self.frames, pob.predicate);
            prop.register_segment(seg_key, clause_constraint);
            let incr_result = prop.check_clause_blocking(
                pob.level,
                clause_index,
                &[
                    state_on_head.clone(),
                    guarded.clone(),
                    frame_on_body.clone(),
                    exclusion_constraint.clone(),
                ],
                check_timeout,
                pob.smt_model.as_ref(),
            );
            match incr_result {
                IncrementalCheckResult::Unsat => (SmtResult::Unsat, None),
                IncrementalCheckResult::Sat(model) => (SmtResult::Sat(model), None),
                IncrementalCheckResult::Unknown => (SmtResult::Unknown, None),
            }
        } else {
            self.smt
                .with_phase_seed_model(pob.smt_model.as_ref(), |smt| {
                    Self::check_sat_with_ite_case_split(smt, verbose, &query)
                })
        };
        let farkas_conflicts = if result.is_unsat() {
            extract_farkas_from_result(result.clone())
        } else {
            Vec::new()
        };
        match result {
            SmtResult::Sat(model) => {
                self.record_reachable_pob_countermodel(pob, head_args, &model);
                let query_for_cube = sat_query.as_ref().unwrap_or(&query);
                let model = Self::minimize_projection_model_with_context(
                    &mut self.smt,
                    &projection_vars,
                    query_for_cube,
                    model,
                );
                if self.config.verbose {
                    safe_eprintln!("  Result: SAT with model {:?}", model);
                }
                // #8660: For array-heavy problems, prefer scalar-only cubes.
                // Scalar cubes are cheaper to generalize (no array theory in inductiveness
                // checks) and often sufficient for blocking. Fall back to full cube only
                // if scalar extraction fails. Mem-track fix: keep property-relevant
                // array selects when the property reads arrays.
                let cube = if self.uses_arrays {
                    self.cube_from_model_array_aware(*body_pred, body_args, query_for_cube, &model)
                } else {
                    self.cube_with_mbp(*body_pred, body_args, query_for_cube, &model)
                };
                let cube = match cube {
                    Some(c) => c,
                    None => {
                        *had_sat_no_cube = true;
                        self.telemetry.sat_no_cube_events += 1;
                        return Ok(());
                    }
                };

                Err(BlockResult::Reachable(Box::new(PredecessorState {
                    predicate: *body_pred,
                    state: cube,
                    clause_index,
                    smt_model: model,
                    derivation_id: None,
                })))
            }
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                if self.config.verbose {
                    safe_eprintln!("  Result: UNSAT");
                }
                if self.config.use_interpolation {
                    let transition =
                        ChcExpr::and_all([clause_constraint.clone(), frame_on_body.clone()]);
                    clause_interpolation_data.push(ClauseInterpolationData {
                        head_args: head_args.to_vec(),
                        constraint: transition.clone(),
                        farkas_conflicts,
                    });
                    let transition_canonical =
                        if let Some(canon_vars) = self.canonical_vars(pob.predicate) {
                            Self::translate_to_canonical_names(&transition, head_args, canon_vars)
                        } else {
                            transition
                        };
                    transition_constraints.push(transition_canonical);
                }
                Ok(())
            }
            SmtResult::Unknown => {
                if self.config.verbose {
                    safe_eprintln!("  Result: Unknown");
                }
                Err(BlockResult::Unknown)
            }
        }
    }

    fn predecessor_exclusion_constraint(
        &self,
        scope_label: &str,
        parent_level: usize,
        body_pred: PredicateId,
        body_args: &[ChcExpr],
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
    ) -> ChcExpr {
        let mut exclusions: Vec<ChcExpr> = Vec::new();
        for (unknown_parent_level, pred_id, state_expr) in unknown_predecessors {
            if *unknown_parent_level == parent_level && *pred_id == body_pred {
                if let Some(on_body) = self.apply_to_args(body_pred, state_expr, body_args) {
                    if self.config.verbose {
                        if scope_label.is_empty() {
                            safe_eprintln!(
                                "PDR: Adding exclusion for level={} pred={}: {} -> {}",
                                unknown_parent_level,
                                pred_id.index(),
                                state_expr,
                                on_body
                            );
                        } else {
                            safe_eprintln!(
                                "PDR: {} Adding exclusion for level={} pred={}: {} -> {}",
                                scope_label,
                                unknown_parent_level,
                                pred_id.index(),
                                state_expr,
                                on_body
                            );
                        }
                    }
                    exclusions.push(ChcExpr::not(on_body));
                }
            }
        }

        if exclusions.is_empty() {
            ChcExpr::Bool(true)
        } else {
            if self.config.verbose {
                let joined = ChcExpr::and_all(exclusions.clone());
                if scope_label.is_empty() {
                    safe_eprintln!(
                        "PDR: Exclusion constraint ({} items): {}",
                        exclusions.len(),
                        joined
                    );
                } else {
                    safe_eprintln!(
                        "PDR: {} Exclusion constraint ({} items): {}",
                        scope_label,
                        exclusions.len(),
                        joined
                    );
                }
            }
            ChcExpr::and_all(exclusions)
        }
    }
}
