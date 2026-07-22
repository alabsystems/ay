// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod single_body;

use super::*;
use crate::smt::types::FarkasConflict;

/// Per-clause interpolation data preserved during predecessor reachability checks.
pub(in crate::pdr::solver) struct ClauseInterpolationData {
    pub head_args: Vec<ChcExpr>,
    pub constraint: ChcExpr,
    /// Clause-local Farkas conflicts preserved from the SMT result (#6484).
    pub farkas_conflicts: Vec<FarkasConflict>,
}

/// Data collected during predecessor reachability, passed to lemma construction.
pub(in crate::pdr::solver) struct ReachabilityData {
    pub transition_constraints: Vec<ChcExpr>,
    pub clause_interpolation_data: Vec<ClauseInterpolationData>,
}

impl PdrSolver {
    #[allow(clippy::result_large_err)]
    pub(in crate::pdr::solver) fn check_predecessor_reachability(
        &mut self,
        pob: &mut ProofObligation,
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
    ) -> Result<ReachabilityData, BlockResult> {
        let prev_level = pob.level - 1;
        let mut transition_constraints: Vec<ChcExpr> = Vec::new();
        let mut clause_interpolation_data: Vec<ClauseInterpolationData> = Vec::new();
        // Track whether any clause returned SAT but cube extraction failed.
        // If so, we must NOT create a blocking lemma (the state may be reachable
        // via that clause), but we can try other clauses first in case they produce
        // a complete model (#3121).
        let mut had_sat_no_cube = false;

        // #5877: Collect eligible clause indices and rotate to diversify CTI
        // generation. Without rotation, the first SAT clause always wins,
        // producing CTIs from only one transition branch. Rotation ensures
        // different branches fire across successive blocking calls.
        let eligible_clause_indices: Vec<usize> = self
            .problem
            .clauses_defining_with_index(pob.predicate)
            .map(|(index, _)| index)
            .collect();
        let rotation = self.telemetry.clause_rotation_counter;
        self.telemetry.clause_rotation_counter = rotation.wrapping_add(1);

        for offset in 0..eligible_clause_indices.len() {
            let clause_index =
                eligible_clause_indices[(rotation + offset) % eligible_clause_indices.len()];
            let clause = self.problem.clauses()[clause_index].clone();
            if self.is_cancelled() {
                return Err(BlockResult::Unknown);
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
            let state_on_head = match self.apply_to_args(pob.predicate, &pob.state, head_args) {
                Some(e) => e,
                None => return Err(BlockResult::Unknown),
            };
            let guarded =
                self.clause_guarded_constraint(pob.predicate, clause_index, head_args, pob.level);
            let base = ChcExpr::and_all([
                clause_constraint.clone(),
                state_on_head.clone(),
                guarded.clone(),
            ]);

            if clause.body.predicates.is_empty() {
                let query = self.bound_int_vars(base.clone());
                let projection_vars = self.projection_vars_for_args(pob.predicate, head_args);
                let result = if self.uses_arrays && query.contains_array_ops() {
                    let query_delta = ChcExpr::and(state_on_head.clone(), guarded.clone());
                    Self::check_array_clause_query(
                        &mut self.smt,
                        &mut self.array_clause_sessions,
                        ArraySessionKey::HeadFact { clause_index },
                        &clause_constraint,
                        &query_delta,
                        &query,
                        self.max_array_params,
                    )
                } else if self.incremental_pdr_enabled() {
                    let check_timeout = self.smt.current_timeout();
                    let seg_key =
                        super::super::prop_solver::SegmentKey::ClauseBlocking { clause_index };
                    let prop = super::super::core::ensure_prop_solver_split(
                        &mut self.prop_solvers,
                        &self.frames,
                        pob.predicate,
                    );
                    prop.register_segment(seg_key, &clause_constraint);
                    let incr_result = prop.check_clause_blocking(
                        0,
                        clause_index,
                        &[state_on_head.clone(), guarded.clone()],
                        check_timeout,
                        pob.smt_model.as_ref(),
                    );
                    match incr_result {
                        IncrementalCheckResult::Unsat => SmtResult::Unsat,
                        IncrementalCheckResult::Sat(model) => SmtResult::Sat(model),
                        IncrementalCheckResult::Unknown => SmtResult::Unknown,
                    }
                } else {
                    self.smt.reset();
                    self.smt
                        .with_phase_seed_model(pob.smt_model.as_ref(), |smt| smt.check_sat(&query))
                };
                let farkas_conflicts = if result.is_unsat() {
                    extract_farkas_from_result(result.clone())
                } else {
                    Vec::new()
                };
                match result {
                    SmtResult::Sat(model) => {
                        self.record_reachable_pob_countermodel(pob, head_args, &model);
                        let model = Self::minimize_projection_model_with_context(
                            &mut self.smt,
                            &projection_vars,
                            &query,
                            model,
                        );
                        // #8660: Prefer scalar-only cubes for array problems,
                        // but keep property-relevant array selects when the
                        // property reads arrays (Mem-track fix).
                        let cube = if self.uses_arrays {
                            self.cube_from_model_array_aware(
                                pob.predicate,
                                head_args,
                                &clause_constraint,
                                &model,
                            )
                        } else {
                            self.cube_with_mbp(pob.predicate, head_args, &clause_constraint, &model)
                        };
                        let cube = match cube {
                            Some(c) => c,
                            None => {
                                had_sat_no_cube = true;
                                self.telemetry.sat_no_cube_events += 1;
                                continue;
                            }
                        };
                        return Err(BlockResult::Reachable(Box::new(PredecessorState {
                            predicate: pob.predicate,
                            state: cube,
                            clause_index,
                            smt_model: model,
                            derivation_id: None,
                        })));
                    }
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        if self.config.use_interpolation {
                            let constraint_canonical =
                                if let Some(canon_vars) = self.canonical_vars(pob.predicate) {
                                    Self::translate_to_canonical_names(
                                        &clause_constraint,
                                        head_args,
                                        canon_vars,
                                    )
                                } else {
                                    clause_constraint.clone()
                                };
                            transition_constraints.push(constraint_canonical);
                            clause_interpolation_data.push(ClauseInterpolationData {
                                head_args: head_args.to_vec(),
                                constraint: clause_constraint.clone(),
                                farkas_conflicts,
                            });
                        }
                        continue;
                    }
                    SmtResult::Unknown => return Err(BlockResult::Unknown),
                }
            }

            if clause.body.predicates.len() > 1 {
                if !self.config.use_mixed_summaries {
                    continue;
                }

                let num_body_preds = clause.body.predicates.len();
                for last_may_index in 0..num_body_preds {
                    // Deadline check per hyperedge body: each iteration issues an
                    // SMT query, and the enclosing clause loop only checks the
                    // deadline between clauses (line ~56). Degrade to Unknown
                    // (fail-closed) rather than running these SMT queries past the
                    // solve timeout.
                    if self.is_cancelled() {
                        return Err(BlockResult::Unknown);
                    }
                    if let Some((mixed_summary, refine_pred, refine_args)) =
                        self.get_edge_mixed_summary(&clause, prev_level, last_may_index)
                    {
                        let projection_vars =
                            self.projection_vars_for_args(refine_pred, &refine_args);
                        let query = self.bound_int_vars(ChcExpr::and_all([
                            mixed_summary.clone(),
                            state_on_head.clone(),
                        ]));

                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Checking hyperedge with {} body predicates, last_may_index={}",
                                num_body_preds, last_may_index
                            );
                            safe_eprintln!("  mixed_summary={}", mixed_summary);
                            safe_eprintln!("  state_on_head={}", state_on_head);
                            safe_eprintln!("  query={}", query);
                        }

                        let result = if self.incremental_pdr_enabled() {
                            let bounded_mixed = self.bound_int_vars(mixed_summary.clone());
                            let check_timeout = self.smt.current_timeout();
                            let prop = super::super::core::ensure_prop_solver_split(
                                &mut self.prop_solvers,
                                &self.frames,
                                pob.predicate,
                            );
                            let incr_result = prop.check_hyperedge_blocking(
                                pob.level,
                                &[bounded_mixed, state_on_head.clone()],
                                check_timeout,
                                pob.smt_model.as_ref(),
                            );
                            match incr_result {
                                IncrementalCheckResult::Unsat => SmtResult::Unsat,
                                IncrementalCheckResult::Sat(model) => SmtResult::Sat(model),
                                IncrementalCheckResult::Unknown => SmtResult::Unknown,
                            }
                        } else {
                            self.smt.reset();
                            self.smt
                                .with_phase_seed_model(pob.smt_model.as_ref(), |smt| {
                                    smt.check_sat(&query)
                                })
                        };
                        match result {
                            SmtResult::Sat(model) => {
                                self.record_reachable_pob_countermodel(pob, head_args, &model);
                                let model = Self::minimize_projection_model_with_context(
                                    &mut self.smt,
                                    &projection_vars,
                                    &query,
                                    model,
                                );
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "  Result: SAT -> refining predicate {} at index {}",
                                        refine_pred.index(),
                                        last_may_index
                                    );
                                }
                                let projection_formula = ChcExpr::and_all([
                                    mixed_summary.clone(),
                                    state_on_head.clone(),
                                ]);
                                let cube = self.cube_with_mbp(
                                    refine_pred,
                                    &refine_args,
                                    &projection_formula,
                                    &model,
                                );
                                if let Some(cube) = cube {
                                    let derivation_id = if self.config.use_derivations {
                                        let body_preds: Vec<_> = clause.body.predicates.clone();
                                        Some(self.allocate_hyperedge_derivation_from_preds(
                                            &body_preds,
                                            clause_index,
                                            last_may_index,
                                            pob.predicate,
                                            pob.level,
                                            pob.state.clone(),
                                            pob.query_clause,
                                            prev_level,
                                        ))
                                    } else {
                                        None
                                    };
                                    return Err(BlockResult::Reachable(Box::new(
                                        PredecessorState {
                                            predicate: refine_pred,
                                            state: cube,
                                            clause_index,
                                            smt_model: model,
                                            derivation_id,
                                        },
                                    )));
                                }
                                had_sat_no_cube = true;
                                self.telemetry.sat_no_cube_events += 1;
                            }
                            SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_) => {
                                if self.config.verbose {
                                    safe_eprintln!("  Result: UNSAT, trying next index");
                                }
                                continue;
                            }
                            SmtResult::Unknown => break,
                        }
                    }
                }
                continue;
            }

            let single_body_result = if prev_level == 0 {
                self.check_prev_level_zero_predecessor(
                    pob,
                    unknown_predecessors,
                    clause_index,
                    &base,
                    &clause_constraint,
                    head_args,
                    &state_on_head,
                    &guarded,
                    &clause,
                    &mut transition_constraints,
                    &mut clause_interpolation_data,
                    &mut had_sat_no_cube,
                )
            } else {
                self.check_single_body_predecessor(
                    pob,
                    prev_level,
                    unknown_predecessors,
                    clause_index,
                    &base,
                    &clause_constraint,
                    head_args,
                    &state_on_head,
                    &guarded,
                    &clause,
                    &mut transition_constraints,
                    &mut clause_interpolation_data,
                    &mut had_sat_no_cube,
                )
            };
            match single_body_result {
                Ok(()) => continue,
                Err(result) => return Err(result),
            }
        }

        if had_sat_no_cube {
            return Err(BlockResult::Unknown);
        }

        Ok(ReachabilityData {
            transition_constraints,
            clause_interpolation_data,
        })
    }
}
